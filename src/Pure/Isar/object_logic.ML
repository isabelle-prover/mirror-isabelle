(*  Title:      Pure/Isar/object_logic.ML
    Author:     Markus Wenzel, TU Muenchen

Specifics about common object-logics.
*)

signature OBJECT_LOGIC =
sig
  val get_base_sort: Proof.context -> sort option
  val add_base_sort: sort -> theory -> theory
  val add_judgment: binding * typ * mixfix -> theory -> theory
  val add_judgment_cmd: binding * string * mixfix -> theory -> theory
  val judgment_name: Proof.context -> string
  val judgment_const: Proof.context -> string * typ
  val is_judgment: Proof.context -> term -> bool
  val drop_judgment: Proof.context -> term -> term
  val fixed_judgment: Proof.context -> string -> term
  val ensure_propT: Proof.context -> term -> term
  val dest_judgment: Proof.context -> cterm -> cterm
  val judgment_conv: Proof.context -> conv -> conv
  val is_propositional: Proof.context -> typ -> bool
  val elim_concl: Proof.context -> thm -> term option
  val declare_atomize: attribute
  val declare_rulify: attribute
  val atomize_term: Proof.context -> term -> term
  val atomize: Proof.context -> conv
  val atomize_prems: Proof.context -> conv
  val atomize_prems_tac: Proof.context -> int -> tactic
  val full_atomize_tac: Proof.context -> int -> tactic
  val rulify_term: Proof.context -> term -> term
  val rulify_tac: Proof.context -> int -> tactic
  val rulify: Proof.context -> thm -> thm
  val rulify_no_asm: Proof.context -> thm -> thm
  val rule_format: attribute
  val rule_format_no_asm: attribute
end;

structure Object_Logic: OBJECT_LOGIC =
struct

(** context data **)

datatype data = Data of
 {base_sort: sort option,
  judgment: string option,
  atomize_rulify: thm list * thm list};

fun make_data (base_sort, judgment, atomize_rulify) =
  Data {base_sort = base_sort, judgment = judgment, atomize_rulify = atomize_rulify};

structure Data = Generic_Data
(
  type T = data;
  val empty = make_data (NONE, NONE, ([], []));

  fun merge_opt eq (SOME x, SOME y) =
        if eq (x, y) then SOME x else error "Attempt to merge different object-logics"
    | merge_opt _ data = merge_options data;

  fun merge
     (Data {base_sort = base_sort1, judgment = judgment1, atomize_rulify = (atomize1, rulify1)},
      Data {base_sort = base_sort2, judgment = judgment2, atomize_rulify = (atomize2, rulify2)}) =
    make_data (merge_opt (op =) (base_sort1, base_sort2), merge_opt (op =) (judgment1, judgment2),
      (Thm.merge_thms (atomize1, atomize2), Thm.merge_thms (rulify1, rulify2)));
);

fun map_data f = Data.map (fn (Data {base_sort, judgment, atomize_rulify}) =>
  make_data (f (base_sort, judgment, atomize_rulify)));

fun get_data ctxt = Data.get (Context.Proof ctxt) |> (fn Data args => args);



(** generic treatment of judgments -- with a single argument only **)

(* base_sort *)

val get_base_sort = #base_sort o get_data;

fun add_base_sort S =
  (Context.theory_map o map_data) (fn (base_sort, judgment, atomize_rulify) =>
    if is_some base_sort then error "Attempt to redeclare object-logic base sort"
    else (SOME S, judgment, atomize_rulify));


(* add judgment *)

local

fun gen_add_judgment add_consts (b, T, mx) thy =
  let
    val c = Sign.full_name thy b;
    val thy' = thy |> add_consts [(b, T, mx)];
  in
    thy'
    |> Theory.add_deps_const c
    |> (Context.theory_map o map_data) (fn (base_sort, judgment, atomize_rulify) =>
        if is_some judgment then error "Attempt to redeclare object-logic judgment"
        else (base_sort, SOME c, atomize_rulify))
  end;

in

val add_judgment = gen_add_judgment Sign.add_consts;
val add_judgment_cmd = gen_add_judgment Sign.add_consts_cmd;

end;


(* judgments *)

fun judgment_name ctxt =
  (case #judgment (get_data ctxt) of
    SOME name => name
  | _ => raise TERM ("Unknown object-logic judgment", []));

fun judgment_const ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val c = judgment_name ctxt;
    val T = Sign.the_const_type thy c;
  in (c, T) end;

fun is_judgment ctxt =
  let val name = judgment_name ctxt
  in fn Const (c, _) $ _ => c = name | _ => false end;

fun drop_judgment ctxt =
  let
    val name = judgment_name ctxt;
    fun drop (Abs (x, T, t)) = Abs (x, T, drop t)
      | drop (t as Const (c, _) $ u) = if c = name then u else t
      | drop t = t;
  in drop end handle TERM _ => I;

fun fixed_judgment ctxt x =
  let  (*be robust wrt. low-level errors*)
    val c = judgment_name ctxt;
    val aT = Term.aT [];
    val T =
      the_default (aT --> propT) (Sign.const_type (Proof_Context.theory_of ctxt) c)
      |> Term.map_type_tvar (fn ((a, _), S) => TFree (a, S));
    val U = Term.domain_type T handle Match => aT;
  in Const (c, T) $ Free (x, U) end;

fun ensure_propT ctxt t =
  let val T = Term.fastype_of t
  in if T = propT then t else Const (judgment_name ctxt, T --> propT) $ t end;

fun dest_judgment ctxt ct =
  if is_judgment ctxt (Thm.term_of ct)
  then Thm.dest_arg ct
  else raise CTERM ("dest_judgment", [ct]);

fun judgment_conv ctxt cv ct =
  if is_judgment ctxt (Thm.term_of ct)
  then Conv.arg_conv cv ct
  else raise CTERM ("judgment_conv", [ct]);

fun is_propositional ctxt T =
  T = propT orelse
    let val x = Free (singleton (Variable.variant_names ctxt) ("x", T))
    in can (fn () => Syntax.check_term ctxt (ensure_propT ctxt x)) () end;


(* elimination rules *)

fun elim_concl ctxt rule =
  let
    val concl = Thm.concl_of rule;
    val C = drop_judgment ctxt concl;
  in
    if Term.is_Var C andalso
      exists (fn prem => concl aconv Logic.strip_assums_concl prem) (Thm.prems_of rule)
    then SOME C else NONE
  end;



(** treatment of meta-level connectives **)

(* maintain rules *)

fun get_atomize_rulify f ctxt = map (Thm.transfer' ctxt) (f (#atomize_rulify (get_data ctxt)));
val get_atomize = get_atomize_rulify #1;
val get_rulify = get_atomize_rulify #2;

fun add_atomize th = map_data (fn (base_sort, judgment, (atomize, rulify)) =>
  (base_sort, judgment, (Thm.add_thm (Thm.trim_context th) atomize, rulify)));

fun add_rulify th = map_data (fn (base_sort, judgment, (atomize, rulify)) =>
  (base_sort, judgment, (atomize, Thm.add_thm (Thm.trim_context th) rulify)));

val declare_atomize = Thm.declaration_attribute add_atomize;
val declare_rulify = Thm.declaration_attribute add_rulify;

val _ = Theory.setup (fold (Context.theory_map o add_rulify) Drule.norm_hhf_eqs);


(* atomize *)

fun atomize_term ctxt =
  drop_judgment ctxt o
    Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) (get_atomize ctxt) [];

fun atomize ctxt = Raw_Simplifier.rewrite_wrt ctxt true (get_atomize ctxt);

fun atomize_prems ctxt ct =
  if Logic.has_meta_prems (Thm.term_of ct) then
    Conv.params_conv ~1 (Conv.prems_conv ~1 o atomize) ctxt ct
  else Conv.all_conv ct;

val atomize_prems_tac = CONVERSION o atomize_prems;
val full_atomize_tac = CONVERSION o atomize;


(* rulify *)

fun rulify_term ctxt =
  Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) (get_rulify ctxt) [];

fun rulify_tac ctxt = rewrite_goal_tac ctxt (get_rulify ctxt);

fun gen_rulify full ctxt =
  Conv.fconv_rule (Raw_Simplifier.rewrite_wrt ctxt full (get_rulify ctxt))
  #> Variable.gen_all ctxt
  #> Thm.strip_shyps
  #> Drule.zero_var_indexes;

val rulify = gen_rulify true;
val rulify_no_asm = gen_rulify false;

val rule_format = Thm.rule_attribute [] (rulify o Context.proof_of);
val rule_format_no_asm = Thm.rule_attribute [] (rulify_no_asm o Context.proof_of);

end;
