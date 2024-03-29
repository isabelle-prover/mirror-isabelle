(*  Title:      Pure/term_ord.ML
    Author:     Tobias Nipkow, TU Muenchen
    Author:     Makarius

Term orderings.
*)

signature TERM_ORD =
sig
  val fast_indexname_ord: indexname ord
  val sort_ord: sort ord
  val typ_ord: typ ord
  val fast_term_ord: term ord
  val syntax_term_ord: term ord
  val indexname_ord: indexname ord
  val tvar_ord: (indexname * sort) ord
  val var_ord: (indexname * typ) ord
  val term_ord: term ord
  val hd_ord: term ord
  val term_lpo: (term -> int) -> term ord
end;

structure Term_Ord: TERM_ORD =
struct

(* fast syntactic ordering -- tuned for inequalities *)

val fast_indexname_ord =
  pointer_eq_ord (int_ord o apply2 snd ||| fast_string_ord o apply2 fst);

val sort_ord =
  pointer_eq_ord (dict_ord fast_string_ord);

local

fun cons_nr (TVar _) = 0
  | cons_nr (TFree _) = 1
  | cons_nr (Type _) = 2;

in

fun typ_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (Type (a, Ts), Type (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord typ_ord (Ts, Us) | ord => ord)
    | (TFree (a, S), TFree (b, S')) =>
        (case fast_string_ord (a, b) of EQUAL => sort_ord (S, S') | ord => ord)
    | (TVar (xi, S), TVar (yj, S')) =>
        (case fast_indexname_ord (xi, yj) of EQUAL => sort_ord (S, S') | ord => ord)
    | (T, U) => int_ord (cons_nr T, cons_nr U));

end;

local

fun cons_nr (Const _) = 0
  | cons_nr (Free _) = 1
  | cons_nr (Var _) = 2
  | cons_nr (Bound _) = 3
  | cons_nr (Abs _) = 4
  | cons_nr (_ $ _) = 5;

fun struct_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (_, _, t), Abs (_, _, u)) => struct_ord (t, u)
    | (t1 $ t2, u1 $ u2) =>
        (case struct_ord (t1, u1) of EQUAL => struct_ord (t2, u2) | ord => ord)
    | (t, u) => int_ord (cons_nr t, cons_nr u));

fun atoms_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (_, _, t), Abs (_, _, u)) => atoms_ord (t, u)
    | (t1 $ t2, u1 $ u2) =>
        (case atoms_ord (t1, u1) of EQUAL => atoms_ord (t2, u2) | ord => ord)
    | (Const (a, _), Const (b, _)) => fast_string_ord (a, b)
    | (Free (x, _), Free (y, _)) => fast_string_ord (x, y)
    | (Var (xi, _), Var (yj, _)) => fast_indexname_ord (xi, yj)
    | (Bound i, Bound j) => int_ord (i, j)
    | _ => EQUAL);

fun types_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (_, T, t), Abs (_, U, u)) =>
        (case typ_ord (T, U) of EQUAL => types_ord (t, u) | ord => ord)
    | (t1 $ t2, u1 $ u2) =>
        (case types_ord (t1, u1) of EQUAL => types_ord (t2, u2) | ord => ord)
    | (Const (_, T), Const (_, U)) => typ_ord (T, U)
    | (Free (_, T), Free (_, U)) => typ_ord (T, U)
    | (Var (_, T), Var (_, U)) => typ_ord (T, U)
    | _ => EQUAL);

fun comments_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (x, _, t), Abs (y, _, u)) =>
        (case fast_string_ord (x, y) of EQUAL => comments_ord (t, u) | ord => ord)
    | (t1 $ t2, u1 $ u2) =>
        (case comments_ord (t1, u1) of EQUAL => comments_ord (t2, u2) | ord => ord)
    | _ => EQUAL);

in

val fast_term_ord = struct_ord ||| atoms_ord ||| types_ord;

val syntax_term_ord = fast_term_ord ||| comments_ord;

end;


(* term_ord *)

(*a linear well-founded AC-compatible ordering for terms:
  s < t <=> 1. size(s) < size(t) or
            2. size(s) = size(t) and s=f(...) and t=g(...) and f<g or
            3. size(s) = size(t) and s=f(s1..sn) and t=f(t1..tn) and
               (s1..sn) < (t1..tn) (lexicographically)*)

val indexname_ord = int_ord o apply2 #2 ||| string_ord o apply2 #1;
val tvar_ord = prod_ord indexname_ord sort_ord;
val var_ord = prod_ord indexname_ord typ_ord;


local

fun hd_depth (t $ _, n) = hd_depth (t, n + 1)
  | hd_depth p = p;

fun dest_hd (Const (a, T)) = (((a, 0), T), 0)
  | dest_hd (Free (a, T)) = (((a, 0), T), 1)
  | dest_hd (Var v) = (v, 2)
  | dest_hd (Bound i) = ((("", i), dummyT), 3)
  | dest_hd (Abs (_, T, _)) = ((("", 0), T), 4);

in

fun term_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (_, T, t), Abs(_, U, u)) =>
        (case term_ord (t, u) of EQUAL => typ_ord (T, U) | ord => ord)
    | (t, u) =>
        (case int_ord (size_of_term t, size_of_term u) of
          EQUAL =>
            (case prod_ord hd_ord int_ord (hd_depth (t, 0), hd_depth (u, 0)) of
              EQUAL => args_ord (t, u) | ord => ord)
        | ord => ord))
and hd_ord (f, g) =
  prod_ord (prod_ord indexname_ord typ_ord) int_ord (dest_hd f, dest_hd g)
and args_ord (f $ t, g $ u) =
      (case args_ord (f, g) of EQUAL => term_ord (t, u) | ord => ord)
  | args_ord _ = EQUAL;

end;


(* Lexicographic path order on terms *)

(*
  See Baader & Nipkow, Term rewriting, CUP 1998.
  Without variables.  Const, Var, Bound, Free and Abs are treated all as
  constants.

  f_ord maps terms to integers and serves two purposes:
  - Predicate on constant symbols.  Those that are not recognised by f_ord
    must be mapped to ~1.
  - Order on the recognised symbols.  These must be mapped to distinct
    integers >= 0.
  The argument of f_ord is never an application.
*)

local

fun unrecognized (Const (a, T)) = ((1, ((a, 0), T)), 0)
  | unrecognized (Free (a, T)) = ((1, ((a, 0), T)), 0)
  | unrecognized (Var v) = ((1, v), 1)
  | unrecognized (Bound i) = ((1, (("", i), dummyT)), 2)
  | unrecognized (Abs (_, T, _)) = ((1, (("", 0), T)), 3);

fun dest_hd f_ord t =
  let val ord = f_ord t
  in if ord = ~1 then unrecognized t else ((0, (("", ord), fastype_of t)), 0) end;

fun term_lpo f_ord (s, t) =
  let val (f, ss) = strip_comb s and (g, ts) = strip_comb t in
    if forall (fn si => term_lpo f_ord (si, t) = LESS) ss
    then case hd_ord f_ord (f, g) of
        GREATER =>
          if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
          then GREATER else LESS
      | EQUAL =>
          if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
          then list_ord (term_lpo f_ord) (ss, ts)
          else LESS
      | LESS => LESS
    else GREATER
  end
and hd_ord f_ord (f, g) = case (f, g) of
    (Abs (_, T, t), Abs (_, U, u)) =>
      (case term_lpo f_ord (t, u) of EQUAL => typ_ord (T, U) | ord => ord)
  | (_, _) => prod_ord (prod_ord int_ord
                  (prod_ord indexname_ord typ_ord)) int_ord
                (dest_hd f_ord f, dest_hd f_ord g);

in
val term_lpo = term_lpo
end;

end;


(* scalable collections *)

structure Vartab = Table(type key = indexname val ord = Term_Ord.fast_indexname_ord);
structure Sorttab = Table(type key = sort val ord = Term_Ord.sort_ord);
structure Typtab = Table(type key = typ val ord = Term_Ord.typ_ord);

structure Termtab:
sig
  include TABLE
  val term_cache: (term -> 'a) -> term -> 'a
end =
struct

structure Table = Table(type key = term val ord = Term_Ord.fast_term_ord);
open Table;

fun term_cache f = Cache.create empty lookup update f;

end;

structure Typset = Set(Typtab.Key);
structure Termset = Set(Termtab.Key);

structure Var_Graph = Graph(Vartab.Key);
structure Typ_Graph = Graph(Typtab.Key);
structure Term_Graph = Graph(Termtab.Key);
