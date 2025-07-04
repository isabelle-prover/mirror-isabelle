(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of fact list for Metis using external provers.
*)

signature SLEDGEHAMMER_PROVER_MINIMIZE =
sig
  type stature = ATP_Problem_Generate.stature
  type proof_method = Sledgehammer_Proof_Methods.proof_method
  type play_outcome = Sledgehammer_Proof_Methods.play_outcome
  type mode = Sledgehammer_Prover.mode
  type params = Sledgehammer_Prover.params
  type prover = Sledgehammer_Prover.prover
  type prover_slice = Sledgehammer_Prover.prover_slice
  type prover_result = Sledgehammer_Prover.prover_result

  val is_prover_supported : Proof.context -> string -> bool
  val is_prover_installed : Proof.context -> string -> bool
  val get_prover : Proof.context -> mode -> string -> prover
  val get_slices : Proof.context -> string -> prover_slice list

  val binary_min_facts : int Config.T
  val minimize_facts : (thm list -> unit) -> string -> params -> prover_slice -> bool -> int ->
    int -> Proof.state -> thm -> ((string * stature) * thm list) list -> prover_result ->
    ((string * stature) * thm list) list option
    * (((Pretty.T * stature) list * (proof_method * play_outcome)) option -> string)
  val get_minimizing_prover : Proof.context -> mode -> (thm list -> unit) -> string -> prover
end;

structure Sledgehammer_Prover_Minimize : SLEDGEHAMMER_PROVER_MINIMIZE =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_SMT
open Sledgehammer_Prover_Tactic

fun is_prover_supported ctxt =
  is_atp orf is_smt_solver ctxt orf is_tactic_prover

fun is_prover_installed ctxt prover_name =
  if is_atp prover_name then
    let val thy = Proof_Context.theory_of ctxt in
      is_atp_installed thy prover_name
    end
  else if is_smt_solver ctxt prover_name then
    is_smt_solver_installed ctxt prover_name
  else
    true

fun get_prover ctxt mode name =
  if is_atp name then run_atp mode name
  else if is_smt_solver ctxt name then run_smt_solver mode name
  else if is_tactic_prover name then run_tactic_prover mode name
  else error ("No such prover: " ^ name)

fun get_slices ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_atp name then
      map (apsnd ATP_Slice) (#good_slices (get_atp thy name ()) ctxt)
    else if is_smt_solver ctxt name then
      map (apsnd SMT_Slice) (SMT_Solver.good_slices ctxt name)
    else if is_tactic_prover name then
      map (rpair No_Slice) (good_slices_of_tactic_prover name)
    else
      error ("No such prover: " ^ name)
  end

(* wrapper for calling external prover *)

fun n_facts names =
  let val n = length names in
    string_of_int n ^ " fact" ^ plural_s n ^
    (if n > 0 then ": " ^ (names |> map fst |> sort string_ord |> implode_space) else "")
  end

fun print silent f = if silent then () else writeln (f ())

fun test_facts ({debug, verbose, overlord, spy, provers, max_mono_iters, max_new_mono_instances,
      type_enc, strict, lam_trans, uncurried_aliases, isar_proofs, compress, try0, smt_proofs,
      instantiate, minimize, preplay_timeout, induction_rules, cache_dir, ...} : params)
    ((_, _, falsify, _, fact_filter), slice_extra) silent (prover : prover) timeout i n
    state goal facts =
  let
    val _ = print silent (fn () => "Testing " ^ n_facts (map fst facts) ^
      (if verbose then " (timeout: " ^ string_of_time timeout ^ ")" else "") ^ "...")

    val facts = facts |> maps (fn (n, ths) => map (pair n) ths)
    val params =
      {debug = debug, verbose = verbose, overlord = overlord, spy = spy, provers = provers,
       type_enc = type_enc, abduce = SOME 0, falsify = SOME false, strict = strict,
       lam_trans = lam_trans, uncurried_aliases = uncurried_aliases, learn = false,
       fact_filter = NONE, induction_rules = induction_rules, max_facts = SOME (length facts),
       fact_thresholds = (1.01, 1.01), max_mono_iters = max_mono_iters,
       max_new_mono_instances = max_new_mono_instances, max_proofs = 1,
       isar_proofs = isar_proofs, compress = compress, try0 = try0, smt_proofs = smt_proofs,
       instantiate = instantiate, minimize = minimize, slices = 1, timeout = timeout,
       preplay_timeout = preplay_timeout, expect = "", cache_dir = cache_dir}
    val problem =
      {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
       factss = [("", facts)], has_already_found_something = K false, found_something = K (),
       memoize_fun_call = (fn f => f)}
    val result0 as {outcome = outcome0, used_facts, used_from, preferred_methss, run_time,
        message} =
      prover params problem ((1, false, false, length facts, fact_filter), slice_extra)
    val result as {outcome, ...} =
      if is_none outcome0 andalso
         forall (member (fn ((s, _), ((s', _), _)) => s = s') used_from) used_facts then
        result0
      else
        {outcome = SOME MaybeUnprovable, used_facts = [], used_from = used_from,
         preferred_methss = preferred_methss, run_time = run_time, message = message}
  in
    print silent (fn () =>
      (case outcome of
        SOME failure => string_of_atp_failure failure
      | NONE =>
        "Found " ^ (if falsify then "falsification" else "proof") ^
         (if length used_facts = length facts then "" else " with " ^ n_facts used_facts) ^
         " (" ^ string_of_time run_time ^ ")"));
    result
  end

(* Give the external prover some slack. The ATP gets further slack because the
   Sledgehammer preprocessing time is included in the estimate below but isn't
   part of the timeout. *)
val slack_msecs = 200

fun new_timeout timeout run_time =
  Int.min (Time.toMilliseconds timeout, Time.toMilliseconds run_time + slack_msecs)
  |> Time.fromMilliseconds

(* The linear algorithm usually outperforms the binary algorithm when over 60%
   of the facts are actually needed. The binary algorithm is much more
   appropriate for provers that cannot return the list of used facts and hence
   returns all facts as used. Since we cannot know in advance how many facts are
   actually needed, we heuristically set the threshold. *)
val binary_min_facts =
  Attrib.setup_config_int \<^binding>\<open>sledgehammer_minimize_binary_min_facts\<close> (K 20)

fun linear_minimize test timeout result xs =
  let
    fun min _ [] p = p
      | min timeout (x :: xs) (seen, result) =
        (case test timeout (seen @ xs) of
          result as {outcome = NONE, used_facts, run_time, ...} : prover_result =>
          min (new_timeout timeout run_time) (filter_used_facts true used_facts xs)
            (filter_used_facts false used_facts seen, result)
        | _ => min timeout xs (seen @ [x], result))
  in
    min timeout xs ([], result)
  end

fun binary_minimize test timeout result xs =
  let
    fun min depth (result as {run_time, ...} : prover_result) sup (xs as _ :: _ :: _) =
        let
          val (l0, r0) = chop (length xs div 2) xs
(*
          val _ = warning (Symbol.spaces depth ^ "{ " ^ "sup: " ^ n_facts (map fst sup))
          val _ = warning (Symbol.spaces depth ^ " " ^ "xs: " ^ n_facts (map fst xs))
          val _ = warning (Symbol.spaces depth ^ " " ^ "l0: " ^ n_facts (map fst l0))
          val _ = warning (Symbol.spaces depth ^ " " ^ "r0: " ^ n_facts (map fst r0))
*)
          val depth = depth + 1
          val timeout = new_timeout timeout run_time
        in
          (case test timeout (sup @ l0) of
            result as {outcome = NONE, used_facts, ...} =>
            min depth result (filter_used_facts true used_facts sup)
              (filter_used_facts true used_facts l0)
          | _ =>
            (case test timeout (sup @ r0) of
              result as {outcome = NONE, used_facts, ...} =>
              min depth result (filter_used_facts true used_facts sup)
                (filter_used_facts true used_facts r0)
            | _ =>
              let
                val (sup_r0, (l, result)) = min depth result (sup @ r0) l0
                val (sup, r0) = (sup, r0) |> apply2 (filter_used_facts true (map fst sup_r0))
                val (sup_l, (r, result)) = min depth result (sup @ l) r0
                val sup = sup |> filter_used_facts true (map fst sup_l)
              in (sup, (l @ r, result)) end))
        end
(*
        |> tap (fn _ => warning (Symbol.spaces depth ^ "}"))
*)
      | min _ result sup xs = (sup, (xs, result))
  in
    (case snd (min 0 result [] xs) of
      ([x], result as {run_time, ...}) =>
      (case test (new_timeout timeout run_time) [] of
        result as {outcome = NONE, ...} => ([], result)
      | _ => ([x], result))
    | p => p)
  end

fun minimize_facts do_learn prover_name (params as {learn, timeout, ...}) slice silent i n state
    goal facts result =
  let
    val ctxt = Proof.context_of state
    val prover = get_prover ctxt Minimize prover_name
    val (chained, non_chained) = List.partition is_fact_chained facts

    fun test timeout non_chained =
      test_facts params slice silent prover timeout i n state goal (chained @ non_chained)

    fun minimize used_facts (result as {run_time, ...}) =
      let
        val non_chained = filter_used_facts true used_facts non_chained
        val min =
          if length non_chained >= Config.get ctxt binary_min_facts then binary_minimize
          else linear_minimize
        val (min_facts, {message, ...}) =
          min test (new_timeout timeout run_time) result non_chained
        val min_facts_and_chained = chained @ min_facts
      in
        print silent (fn () => cat_lines
          ["Minimized to " ^ n_facts (map fst min_facts)] ^
           (case length chained of
             0 => ""
           | n => " (plus " ^ string_of_int n ^ " chained)"));
        (if learn then do_learn (maps snd min_facts_and_chained) else ());
        (SOME min_facts_and_chained, message)
      end
  in
    (print silent (fn () => "Sledgehammer minimizer: " ^ prover_name);
     if is_tactic_prover prover_name then
       minimize (map fst facts) result
     else
       (case test timeout non_chained of
         result as {outcome = NONE, used_facts, ...} => minimize used_facts result
       | {outcome = SOME TimedOut, ...} =>
         (NONE, fn _ =>
            "Timeout: You can increase the time limit using the \"timeout\" option (e.g., \
            \timeout = " ^ string_of_int (10 + Time.toMilliseconds timeout div 1000) ^ "\")")
       | {message, ...} => (NONE, (prefix "Prover error: " o message))))
    handle ERROR msg => (NONE, fn _ => "Warning: " ^ msg)
  end

fun maybe_minimize mode do_learn name (params as {verbose, minimize, ...})
    ({state, goal, subgoal, subgoal_count, ...} : prover_problem) slice
    (result as {outcome, used_facts, used_from, preferred_methss, run_time, message}
     : prover_result) =
  if is_some outcome then
    result
  else
    let
      val (used_facts, message) =
        if minimize then
          minimize_facts do_learn name params slice
            (not verbose orelse (mode <> Normal andalso mode <> MaSh)) subgoal subgoal_count state
            goal (filter_used_facts true used_facts (map (apsnd single) used_from)) result
          |>> Option.map (map fst)
        else
          (SOME used_facts, message)
    in
      (case used_facts of
        SOME used_facts =>
        {outcome = NONE, used_facts = sort_by fst used_facts, used_from = used_from,
         preferred_methss = preferred_methss, run_time = run_time, message = message}
      | NONE => result)
    end

fun get_minimizing_prover ctxt mode do_learn name params problem slice =
  get_prover ctxt mode name params problem slice
  |> maybe_minimize mode do_learn name params problem slice

end;
