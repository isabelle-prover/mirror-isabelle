(*  Title:      Pure/term_subst.ML
    Author:     Makarius

Efficient type/term substitution.
*)

signature TERM_SUBST =
sig
  val generalizeT_same: Names.set -> int -> typ Same.operation
  val generalize_same: Names.set * Names.set -> int -> term Same.operation
  val generalizeT: Names.set -> int -> typ -> typ
  val generalize: Names.set * Names.set -> int -> term -> term
  val instantiateT_frees_same: typ TFrees.table -> typ Same.operation
  val instantiate_frees_same: typ TFrees.table * term Frees.table -> term Same.operation
  val instantiateT_frees: typ TFrees.table -> typ -> typ
  val instantiate_frees: typ TFrees.table * term Frees.table -> term -> term
  val instantiateT_maxidx: (typ * int) TVars.table -> typ -> int -> typ * int
  val instantiate_maxidx: (typ * int) TVars.table * (term * int) Vars.table ->
    term -> int -> term * int
  val instantiate_beta_maxidx: (typ * int) TVars.table * (term * int) Vars.table ->
    term -> int -> term * int
  val instantiateT_same: typ TVars.table -> typ Same.operation
  val instantiate_same: typ TVars.table * term Vars.table -> term Same.operation
  val instantiate_beta_same: typ TVars.table * term Vars.table -> term Same.operation
  val instantiateT: typ TVars.table -> typ -> typ
  val instantiate: typ TVars.table * term Vars.table -> term -> term
  val instantiate_beta: typ TVars.table * term Vars.table -> term -> term
  val zero_var_indexes_inst: Name.context -> term list -> typ TVars.table * term Vars.table
  val zero_var_indexes: term -> term
  val zero_var_indexes_list: term list -> term list
end;

structure Term_Subst: TERM_SUBST =
struct

(* generalization of fixed variables *)

fun generalizeT_same tfrees idx ty =
  if Names.is_empty tfrees then raise Same.SAME
  else
    let
      fun gen (Type (a, Ts)) = Type (a, Same.map gen Ts)
        | gen (TFree (a, S)) =
            if Names.defined tfrees a then TVar ((a, idx), S)
            else raise Same.SAME
        | gen _ = raise Same.SAME;
    in gen ty end;

fun generalize_same (tfrees, frees) idx tm =
  if Names.is_empty tfrees andalso Names.is_empty frees then raise Same.SAME
  else
    let
      val genT = generalizeT_same tfrees idx;
      fun gen (Free (x, T)) =
            if Names.defined frees x then
              Var (Name.clean_index (x, idx), Same.commit genT T)
            else Free (x, genT T)
        | gen (Var (xi, T)) = Var (xi, genT T)
        | gen (Const (c, T)) = Const (c, genT T)
        | gen (Bound _) = raise Same.SAME
        | gen (Abs (x, T, t)) =
            (Abs (x, genT T, Same.commit gen t)
              handle Same.SAME => Abs (x, T, gen t))
        | gen (t $ u) = (gen t $ Same.commit gen u handle Same.SAME => t $ gen u);
    in gen tm end;

fun generalizeT names i ty = Same.commit (generalizeT_same names i) ty;
fun generalize names i tm = Same.commit (generalize_same names i) tm;


(* instantiation of free variables (types before terms) *)

fun instantiateT_frees_same instT ty =
  if TFrees.is_empty instT then raise Same.SAME
  else
    let
      fun subst (Type (a, Ts)) = Type (a, Same.map subst Ts)
        | subst (TFree v) =
            (case TFrees.lookup instT v of
              SOME T' => T'
            | NONE => raise Same.SAME)
        | subst _ = raise Same.SAME;
    in subst ty end;

fun instantiate_frees_same (instT, inst) tm =
  if TFrees.is_empty instT andalso Frees.is_empty inst then raise Same.SAME
  else
    let
      val substT = instantiateT_frees_same instT;
      fun subst (Const (c, T)) = Const (c, substT T)
        | subst (Free (x, T)) =
            let val (T', same) = Same.commit_id substT T in
              (case Frees.lookup inst (x, T') of
                 SOME t' => t'
               | NONE => if same then raise Same.SAME else Free (x, T'))
            end
        | subst (Var (xi, T)) = Var (xi, substT T)
        | subst (Bound _) = raise Same.SAME
        | subst (Abs (x, T, t)) =
            (Abs (x, substT T, Same.commit subst t)
              handle Same.SAME => Abs (x, T, subst t))
        | subst (t $ u) = (subst t $ Same.commit subst u handle Same.SAME => t $ subst u);
    in subst tm end;

fun instantiateT_frees instT ty = Same.commit (instantiateT_frees_same instT) ty;
fun instantiate_frees inst tm = Same.commit (instantiate_frees_same inst) tm;


(* instantiation of schematic variables (types before terms) -- recomputes maxidx *)

local

fun no_indexesT instT = TVars.map (fn _ => rpair ~1) instT;
fun no_indexes inst = Vars.map (fn _ => rpair ~1) inst;

fun instT_same maxidx instT ty =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    fun subst_typ (Type (a, Ts)) = Type (a, subst_typs Ts)
      | subst_typ (TVar ((a, i), S)) =
          (case TVars.lookup instT ((a, i), S) of
            SOME (T', j) => (maxify j; T')
          | NONE => (maxify i; raise Same.SAME))
      | subst_typ _ = raise Same.SAME
    and subst_typs (T :: Ts) =
        (subst_typ T :: Same.commit subst_typs Ts
          handle Same.SAME => T :: subst_typs Ts)
      | subst_typs [] = raise Same.SAME;
  in subst_typ ty end;

fun inst_same maxidx (instT, inst) tm =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    val substT = instT_same maxidx instT;
    fun subst (Const (c, T)) = Const (c, substT T)
      | subst (Free (x, T)) = Free (x, substT T)
      | subst (Var ((x, i), T)) =
          let val (T', same) = Same.commit_id substT T in
            (case Vars.lookup inst ((x, i), T') of
               SOME (t', j) => (maxify j; t')
             | NONE => (maxify i; if same then raise Same.SAME else Var ((x, i), T')))
          end
      | subst (Bound _) = raise Same.SAME
      | subst (Abs (x, T, t)) =
          (Abs (x, substT T, subst_commit t)
            handle Same.SAME => Abs (x, T, subst t))
      | subst (t $ u) = (subst t $ subst_commit u handle Same.SAME => t $ subst u)
    and subst_commit t = Same.commit subst t;
  in subst tm end;

(*version with local beta reduction*)
fun inst_beta_same maxidx (instT, inst) tm =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    val substT = instT_same maxidx instT;

    fun expand_head t =
      (case Term.head_of t of
        Var ((x, i), T) =>
          let val (T', same) = Same.commit_id substT T in
            (case Vars.lookup inst ((x, i), T') of
              SOME (t', j) => (maxify j; SOME t')
            | NONE => (maxify i; if same then NONE else SOME (Var ((x, i), T'))))
          end
      | _ => NONE);

    fun subst t =
      (case expand_head t of
        NONE =>
          (case t of
            Const (c, T) => Const (c, substT T)
          | Free (x, T) => Free (x, substT T)
          | Var _ => raise Same.SAME
          | Bound _ => raise Same.SAME
          | Abs (x, T, b) =>
              (Abs (x, substT T, subst_commit b)
                handle Same.SAME => Abs (x, T, subst b))
          | _ $ _ => subst_comb t)
      | SOME (u as Abs _) => Term.betapplys (u, map subst_commit (Term.args_of t))
      | SOME u => subst_head u t)
    and subst_comb (t $ u) = (subst_comb t $ subst_commit u handle Same.SAME => t $ subst u)
      | subst_comb (Var _) = raise Same.SAME
      | subst_comb t = subst t
    and subst_head h (t $ u) = subst_head h t $ subst_commit u
      | subst_head h _ = h
    and subst_commit t = Same.commit subst t;

  in subst tm end;

in

fun instantiateT_maxidx instT ty i =
  let val maxidx = Unsynchronized.ref i
  in (Same.commit (instT_same maxidx instT) ty, ! maxidx) end;

fun instantiate_maxidx insts tm i =
  let val maxidx = Unsynchronized.ref i
  in (Same.commit (inst_same maxidx insts) tm, ! maxidx) end;

fun instantiate_beta_maxidx insts tm i =
  let val maxidx = Unsynchronized.ref i
  in (Same.commit (inst_beta_same maxidx insts) tm, ! maxidx) end;


fun instantiateT_same instT ty =
  if TVars.is_empty instT then raise Same.SAME
  else instT_same (Unsynchronized.ref ~1) (no_indexesT instT) ty;

fun instantiate_same (instT, inst) tm =
  if TVars.is_empty instT andalso Vars.is_empty inst then raise Same.SAME
  else inst_same (Unsynchronized.ref ~1) (no_indexesT instT, no_indexes inst) tm;

fun instantiate_beta_same (instT, inst) tm =
  if TVars.is_empty instT andalso Vars.is_empty inst then raise Same.SAME
  else inst_beta_same (Unsynchronized.ref ~1) (no_indexesT instT, no_indexes inst) tm;


fun instantiateT instT ty = Same.commit (instantiateT_same instT) ty;

fun instantiate inst tm = Same.commit (instantiate_same inst) tm;

fun instantiate_beta inst tm = Same.commit (instantiate_beta_same inst) tm;

end;


(* zero var indexes *)

fun zero_var_inst ins mk (v as ((x, i), X)) (inst, used) =
  let
    val (x', used') = Name.variant_bound x used;
    val inst' = if x = x' andalso i = 0 then inst else ins (v, mk ((x', 0), X)) inst;
  in (inst', used') end;

fun zero_var_indexes_inst used ts =
  let
    val (instT, _) =
      (TVars.empty, used) |> TVars.fold (zero_var_inst TVars.add TVar o #1)
        (TVars.build (ts |> (fold o fold_types o fold_atyps)
          (fn TVar v => TVars.add (v, ()) | _ => I)));
    val (inst, _) =
      (Vars.empty, used) |> Vars.fold (zero_var_inst Vars.add Var o #1)
        (Vars.build (ts |> (fold o fold_aterms)
          (fn Var (xi, T) => Vars.add ((xi, instantiateT instT T), ()) | _ => I)));
  in (instT, inst) end;

fun zero_var_indexes_list ts = map (instantiate (zero_var_indexes_inst Name.context ts)) ts;
val zero_var_indexes = singleton zero_var_indexes_list;

end;
