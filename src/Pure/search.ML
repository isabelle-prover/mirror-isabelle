(*  Title:      Pure/search.ML
    Author:     Lawrence C Paulson
    Author:     Norbert Voelker, FernUniversitaet Hagen

Search tacticals.
*)

infix 1 THEN_MAYBE THEN_MAYBE';

signature SEARCH =
sig
  val DEPTH_FIRST: (thm -> bool) -> tactic -> tactic
  val has_fewer_prems: int -> thm -> bool
  val IF_UNSOLVED: tactic -> tactic
  val SOLVE: tactic -> tactic
  val THEN_MAYBE: tactic * tactic -> tactic
  val THEN_MAYBE': ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val DEPTH_SOLVE: tactic -> tactic
  val DEPTH_SOLVE_1: tactic -> tactic
  val THEN_ITER_DEEPEN: int -> tactic -> (thm -> bool) -> (int -> tactic) -> tactic
  val ITER_DEEPEN: int -> (thm -> bool) -> (int -> tactic) -> tactic
  val DEEPEN: int * int -> (int -> int -> tactic) -> int -> int -> tactic
  val THEN_BEST_FIRST: tactic -> (thm -> bool) * (thm -> int) -> tactic -> tactic
  val BEST_FIRST: (thm -> bool) * (thm -> int) -> tactic -> tactic
  val BREADTH_FIRST: (thm -> bool) -> tactic -> tactic
  val QUIET_BREADTH_FIRST: (thm -> bool) -> tactic -> tactic
  val THEN_ASTAR: tactic -> (thm -> bool) * (int -> thm -> int) -> tactic -> tactic
  val ASTAR: (thm -> bool) * (int -> thm -> int) -> tactic -> tactic
end;

structure Search: SEARCH =
struct

(**** Depth-first search ****)

(*Searches until "satp" reports proof tree as satisfied.
  Suppresses duplicate solutions to minimize search space.*)
fun DEPTH_FIRST satp tac =
  let
    fun depth used [] = NONE
      | depth used (q :: qs) =
          (case Seq.pull q of
            NONE => depth used qs
          | SOME (st, stq) =>
              if satp st andalso not (member Thm.eq_thm used st) then
                SOME (st, Seq.make (fn() => depth (st :: used) (stq :: qs)))
              else depth used (tac st :: stq :: qs));
  in fn st => Seq.make (fn () => depth [] [Seq.single st]) end;


(*Predicate: Does the rule have fewer than n premises?*)
fun has_fewer_prems n rule = Thm.nprems_of rule < n;

(*Apply a tactic if subgoals remain, else do nothing.*)
val IF_UNSOLVED = COND Thm.no_prems all_tac;

(*Force a tactic to solve its goal completely, otherwise fail *)
fun SOLVE tac = tac THEN COND Thm.no_prems all_tac no_tac;

(*Execute tac1, but only execute tac2 if there are at least as many subgoals
  as before.  This ensures that tac2 is only applied to an outcome of tac1.*)
fun (tac1 THEN_MAYBE tac2) st =
  (tac1 THEN COND (has_fewer_prems (Thm.nprems_of st)) all_tac tac2) st;

fun (tac1 THEN_MAYBE' tac2) x = tac1 x THEN_MAYBE tac2 x;

(*Tactical to reduce the number of premises by 1.
  If no subgoals then it must fail! *)
fun DEPTH_SOLVE_1 tac st = st |>
  (case Thm.nprems_of st of
    0 => no_tac
  | n => DEPTH_FIRST (has_fewer_prems n) tac);

(*Uses depth-first search to solve ALL subgoals*)
val DEPTH_SOLVE = DEPTH_FIRST Thm.no_prems;



(**** Iterative deepening with pruning ****)

fun has_vars (Var _) = true
  | has_vars (Abs (_, _, t)) = has_vars t
  | has_vars (f $ t) = has_vars f orelse has_vars t
  | has_vars _ = false;

(*Counting of primitive inferences is APPROXIMATE, as the step tactic
  may perform >1 inference*)

(*Pruning of rigid ancestor to prevent backtracking*)
fun prune (new as (k', np':int, rgd', stq), qs) =
  let
    fun prune_aux (qs, []) = new :: qs
      | prune_aux (qs, (k, np, rgd, q) :: rqs) =
          if np' + 1 = np andalso rgd then
             (*Use OLD k: zero-cost solution; see Stickel, p 365*)
             (k, np', rgd', stq) :: qs
          else prune_aux ((k, np, rgd, q) :: qs, rqs)
      fun take ([], rqs) = ([], rqs)
        | take (arg as ((k, np, rgd, stq) :: qs, rqs)) =
            if np' < np then take (qs, (k, np, rgd, stq) :: rqs) else arg;
  in prune_aux (take (qs, [])) end;


(*Depth-first iterative deepening search for a state that satisfies satp
  tactic tac0 sets up the initial goal queue, while tac1 searches it.
  The solution sequence is redundant: the cutoff heuristic makes it impossible
  to suppress solutions arising from earlier searches, as the accumulated cost
  (k) can be wrong.*)
fun THEN_ITER_DEEPEN lim tac0 satp tac1 st =
  let
    val counter = Unsynchronized.ref 0
    and tf = tac1 1
    and qs0 = tac0 st
     (*bnd = depth bound; inc = estimate of increment required next*)
    fun depth (bnd, inc) [] =
          if bnd > lim then NONE
          else
            (*larger increments make it run slower for the hard problems*)
            depth (bnd + inc, 10) [(0, 1, false, qs0)]
      | depth (bnd, inc) ((k, np, rgd, q) :: qs) =
          if k >= bnd then depth (bnd, inc) qs
          else
           (case (Unsynchronized.inc counter; Seq.pull q) of
             NONE => depth (bnd, inc) qs
           | SOME (st, stq) =>
              if satp st then (*solution!*)
                SOME(st, Seq.make (fn() => depth (bnd, inc) ((k, np, rgd, stq) :: qs)))
              else
                let
                  val np' = Thm.nprems_of st;
                  (*rgd' calculation assumes tactic operates on subgoal 1*)
                  val rgd' = not (has_vars (hd (Thm.take_prems_of 1 st)));
                  val k' = k + np' - np + 1;  (*difference in # of subgoals, +1*)
                in
                  if k' + np' >= bnd then depth (bnd, Int.min (inc, k' + np' + 1 - bnd)) qs
                  else if np' < np (*solved a subgoal; prune rigid ancestors*)
                  then depth (bnd, inc) (prune ((k', np', rgd', tf st), (k, np, rgd, stq) :: qs))
                  else depth (bnd, inc) ((k', np', rgd', tf st) :: (k, np, rgd, stq) :: qs)
                end)
  in Seq.make (fn () => depth (0, 5) []) end;

fun ITER_DEEPEN lim = THEN_ITER_DEEPEN lim all_tac;


(*Simple iterative deepening tactical.  It merely "deepens" any search tactic
  using increment "inc" up to limit "lim". *)
fun DEEPEN (inc, lim) tacf m i =
  let
    fun dpn m st =
      st |>
       (if has_fewer_prems i st then no_tac
        else if m > lim then no_tac
        else tacf m i  ORELSE  dpn (m+inc))
  in  dpn m  end;


(*** Best-first search ***)

(*total ordering on theorems, allowing duplicates to be found*)
structure Thm_Heap = Heap
(
  type elem = int * thm;
  val ord = prod_ord int_ord (Term_Ord.term_ord o apply2 Thm.prop_of);
);

(*For creating output sequence*)
fun some_of_list [] = NONE
  | some_of_list (x :: l) = SOME (x, Seq.make (fn () => some_of_list l));

(*Check for and delete duplicate proof states*)
fun delete_all_min prf heap =
  if Thm_Heap.is_empty heap then heap
  else if Thm.eq_thm (prf, #2 (Thm_Heap.min heap))
  then delete_all_min prf (Thm_Heap.delete_min heap)
  else heap;

(*Best-first search for a state that satisfies satp (incl initial state)
  Function sizef estimates size of problem remaining (smaller means better).
  tactic tac0 sets up the initial priority queue, while tac1 searches it. *)
fun THEN_BEST_FIRST tac0 (satp, sizef) tac =
  let
    fun pairsize th = (sizef th, th);
    fun bfs (news, nprf_heap) =
      (case List.partition satp news of
        ([], nonsats) => next (fold_rev Thm_Heap.insert (map pairsize nonsats) nprf_heap)
      | (sats, _)  => some_of_list sats)
    and next nprf_heap =
      if Thm_Heap.is_empty nprf_heap then NONE
      else
        let
          val (n, prf) = Thm_Heap.min nprf_heap;
        in
          bfs (Seq.list_of (tac prf), delete_all_min prf (Thm_Heap.delete_min nprf_heap))
        end;
    fun btac st = bfs (Seq.list_of (tac0 st), Thm_Heap.empty)
  in fn st => Seq.make (fn () => btac st) end;

(*Ordinary best-first search, with no initial tactic*)
val BEST_FIRST = THEN_BEST_FIRST all_tac;

(*Breadth-first search to satisfy satpred (including initial state)
  SLOW -- SHOULD NOT USE APPEND!*)
fun gen_BREADTH_FIRST message satpred (tac: tactic) =
  let
    val tacf = Seq.list_of o tac;
    fun bfs prfs =
      (case List.partition satpred prfs of
        ([], []) => []
      | ([], nonsats) =>
          (message ("breadth=" ^ string_of_int (length nonsats));
           bfs (maps tacf nonsats))
      | (sats, _)  => sats);
  in fn st => Seq.of_list (bfs [st]) end;

val BREADTH_FIRST = gen_BREADTH_FIRST tracing;
val QUIET_BREADTH_FIRST = gen_BREADTH_FIRST (K ());


(*
  Implementation of A*-like proof procedure by modification
  of the existing code for BEST_FIRST and best_tac so that the
  current level of search is taken into account.
*)

(*Insertion into priority queue of states, marked with level*)
fun insert_with_level (lnth: int * int * thm) [] = [lnth]
  | insert_with_level (l, m, th) ((l', n, th') :: nths) =
      if  n < m then (l', n, th') :: insert_with_level (l, m, th) nths
      else if n = m andalso Thm.eq_thm (th, th') then (l', n, th') :: nths
      else (l, m, th) :: (l', n, th') :: nths;

(*For creating output sequence*)
fun some_of_list [] = NONE
  | some_of_list (x :: xs) = SOME (x, Seq.make (fn () => some_of_list xs));

fun THEN_ASTAR tac0 (satp, costf) tac =
  let
    fun bfs (news, nprfs, level) =
      let fun cost thm = (level, costf level thm, thm) in
        (case List.partition satp news of
          ([], nonsats) => next (fold_rev (insert_with_level o cost) nonsats nprfs)
        | (sats, _) => some_of_list sats)
      end
    and next [] = NONE
      | next ((level, n, prf) :: nprfs) = bfs (Seq.list_of (tac prf), nprfs, level + 1)
  in fn st => Seq.make (fn () => bfs (Seq.list_of (tac0 st), [], 0)) end;

(*Ordinary ASTAR, with no initial tactic*)
val ASTAR = THEN_ASTAR all_tac;

end;

open Search;
