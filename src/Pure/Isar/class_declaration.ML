(*  Title:      Pure/Isar/class_declaration.ML
    Author:     Florian Haftmann, TU Muenchen

Declaring classes and subclass relations.
*)

signature CLASS_DECLARATION =
sig
  val class: binding -> Bundle.name list -> class list ->
    Element.context_i list -> theory -> string * local_theory
  val class_cmd: binding -> Bundle.xname list -> xstring list ->
    Element.context list -> theory -> string * local_theory
  val prove_subclass: tactic -> class ->
    local_theory -> local_theory
  val subclass: class -> local_theory -> Proof.state
  val subclass_cmd: xstring -> local_theory -> Proof.state
end;

structure Class_Declaration: CLASS_DECLARATION =
struct

(** class definitions **)

local

(* calculating class-related rules including canonical interpretation *)

fun calculate thy class sups base_sort param_map assm_axiom =
  let
    val thy_ctxt = Proof_Context.init_global thy;

    val certT = Thm.trim_context_ctyp o Thm.global_ctyp_of thy;
    val cert = Thm.trim_context_cterm o Thm.global_cterm_of thy;
    val conclude_witness = Thm.trim_context o Element.conclude_witness thy_ctxt;

    (* instantiation of canonical interpretation *)
    val a_tfree = (Name.aT, base_sort);
    val a_type = TFree a_tfree;
    val param_map_const = (map o apsnd) Const param_map;
    val param_map_inst =
      Frees.build (param_map |> fold (fn (x, (c, T)) =>
        let val T' = map_atyps (K a_type) T
        in Frees.add ((x, T'), cert (Const (c, T'))) end));
    val const_morph =
      Element.instantiate_normalize_morphism (TFrees.empty, param_map_inst);
    val typ_morph =
      Element.instantiate_normalize_morphism
        (TFrees.make1 (a_tfree, certT (Term.aT [class])), Frees.empty)
    val (([raw_props], _, [(_, raw_inst_morph)], _, export_morph), _) = thy_ctxt
      |> Expression.cert_goal_expression ([(class, (("", false),
           (Expression.Named param_map_const, [])))], []);
    val (props, inst_morph) =
      if null param_map
      then (raw_props |> map (Morphism.term typ_morph),
        raw_inst_morph $> typ_morph)
      else (raw_props, raw_inst_morph); (*FIXME proper handling in
        locale.ML / expression.ML would be desirable*)

    (* witness for canonical interpretation *)
    val some_prop = try the_single props;
    val some_witn = Option.map (fn prop =>
      let
        val sup_axioms = map_filter (fst o Class.rules thy) sups;
        val loc_intro_tac =
          (case Locale.intros_of thy class of
            (_, NONE) => all_tac
          | (_, SOME intro) => ALLGOALS (resolve_tac thy_ctxt [intro]));
        val tac = loc_intro_tac
          THEN ALLGOALS (Proof_Context.fact_tac thy_ctxt (sup_axioms @ the_list assm_axiom));
      in Element.prove_witness thy_ctxt prop tac end) some_prop;
    val some_axiom = Option.map conclude_witness some_witn;

    (* canonical interpretation *)
    val base_morph = inst_morph
      $> Morphism.binding_morphism "class_binding" (Binding.prefix false (Class.class_prefix class))
      $> Element.satisfy_morphism (the_list some_witn);
    val eq_morph =
      Element.eq_morphism thy_ctxt (Class.these_defs thy sups)
      |> Option.map (Morphism.set_context thy);

    (* assm_intro *)
    fun prove_assm_intro thm =
      let
        val ((_, [thm']), _) = Variable.import true [thm] thy_ctxt;
        val const_eq_morph =
          (case eq_morph of
            SOME eq_morph => const_morph $> eq_morph
          | NONE => const_morph);
        val thm'' = Morphism.thm const_eq_morph thm';
      in
        Goal.prove_sorry_global thy [] [] (Thm.prop_of thm'')
          (fn {context = ctxt, ...} => ALLGOALS (Proof_Context.fact_tac ctxt [thm'']))
      end;
    val some_assm_intro = Option.map prove_assm_intro (fst (Locale.intros_of thy class));

    (* of_class *)
    val of_class_prop_concl = Logic.mk_of_class (a_type, class);
    val of_class_prop =
      (case some_prop of
        NONE => of_class_prop_concl
      | SOME prop => Logic.mk_implies (Morphism.term const_morph
          ((map_types o Term.map_atyps_same) (K a_type) prop), of_class_prop_concl));
    val sup_of_classes = map (snd o Class.rules thy) sups;
    val loc_axiom_intros = map Drule.export_without_context_open (Locale.axioms_of thy class);
    val axclass_intro = #intro (Axclass.get_info thy class);
    val base_sort_trivs = Thm.of_sort (Thm.global_ctyp_of thy a_type, base_sort);
    fun tac ctxt =
      REPEAT (SOMEGOAL
        (match_tac ctxt (axclass_intro :: sup_of_classes @ loc_axiom_intros @ base_sort_trivs)
          ORELSE' assume_tac ctxt));
    val of_class = Goal.prove_sorry_global thy [] [] of_class_prop (tac o #context);
  in (base_morph, eq_morph, export_morph, some_axiom, some_assm_intro, of_class) end;


(* reading and processing class specifications *)

fun prep_class_elems prep_decl ctxt sups raw_elems =
  let
    (* user space type system: only permits 'a type variable, improves towards 'a *)
    val thy = Proof_Context.theory_of ctxt;
    val algebra = Sign.classes_of thy;
    val inter_sort = curry (Sorts.inter_sort algebra);
    val proto_base_sort =
      if null sups then Sign.defaultS thy
      else fold inter_sort (map (Class.base_sort thy) sups) [];
    val is_param = member (op =) (map fst (Class.these_params thy sups));
    val base_constraints = (map o apsnd)
      (map_type_tfree (K (TVar ((Name.aT, 0), proto_base_sort))) o fst o fst o snd)
        (Class.these_operations thy sups);
    val singleton_fixate = burrow_types (fn Ts =>
      let
        val tfrees = fold Term.add_tfreesT Ts [];
        val inferred_sort =
          (fold o fold_atyps) (fn TVar (_, S) => inter_sort S | _ => I) Ts [];
        val fixate_sort =
          (case tfrees of
            [] => inferred_sort
          | [(a, S)] =>
              if a <> Name.aT then
                error ("No type variable other than " ^ Name.aT ^ " allowed in class specification")
              else if Sorts.sort_le algebra (S, inferred_sort) then S
              else
                error ("Type inference imposes additional sort constraint " ^
                  Syntax.string_of_sort_global thy inferred_sort ^
                  " of type parameter " ^ Name.aT ^ " of sort " ^
                  Syntax.string_of_sort_global thy S)
          | _ => error "Multiple type variables in class specification");
        val fixateT = Term.aT fixate_sort;
      in
        (Same.commit o Same.map o Term.map_atyps_same)
          (fn TVar (xi, _) => if Type_Infer.is_param xi then fixateT else raise Same.SAME
            | _ => raise Same.SAME) Ts
      end);
    fun unify_params ts =
      let
        val param_Ts = (fold o fold_aterms)
          (fn Free (v, T) => if is_param v then fold_atyps (insert (op =)) T else I | _ => I) ts [];
        val param_namesT = map_filter (try (fst o dest_TVar)) param_Ts;
        val param_T = if null param_namesT then NONE
          else SOME (case get_first (try dest_TFree) param_Ts of
            SOME v_sort => TFree v_sort |
            NONE => TVar (hd param_namesT, proto_base_sort));
      in case param_T of
        NONE => ts |
        SOME T => map (subst_TVars (map (rpair T) param_namesT)) ts
      end;

    (* preprocessing elements, retrieving base sort from type-checked elements *)
    val raw_supexpr =
      (map (fn sup => (sup, (("", false), (Expression.Positional [], [])))) sups, []);
    val init_class_body =
      fold (Proof_Context.add_const_constraint o apsnd SOME) base_constraints
      #> Class.redeclare_operations thy sups
      #> Context.proof_map (Syntax_Phases.term_check 0 "singleton_fixate" (K singleton_fixate));
    val ((raw_supparams, _, raw_inferred_elems, _), _) =
      ctxt
      |> Context.proof_map (Syntax_Phases.term_check 0 "unify_params" (K unify_params))
      |> prep_decl raw_supexpr init_class_body raw_elems;
    fun filter_element (Element.Fixes []) = NONE
      | filter_element (e as Element.Fixes _) = SOME e
      | filter_element (Element.Constrains []) = NONE
      | filter_element (e as Element.Constrains _) = SOME e
      | filter_element (Element.Assumes []) = NONE
      | filter_element (e as Element.Assumes _) = SOME e
      | filter_element (Element.Defines _) =
          error ("\"defines\" element not allowed in class specification.")
      | filter_element (Element.Notes _) =
          error ("\"notes\" element not allowed in class specification.")
      | filter_element (Element.Lazy_Notes _) =
          error ("\"notes\" element not allowed in class specification.");
    val inferred_elems = map_filter filter_element raw_inferred_elems;
    fun fold_element_types f (Element.Fixes fxs) = fold (fn (_, SOME T, _) => f T) fxs
      | fold_element_types f (Element.Constrains cnstrs) = fold (f o snd) cnstrs
      | fold_element_types f (Element.Assumes assms) = fold (fold (fn (t, ts) =>
          fold_types f t #> (fold o fold_types) f ts) o snd) assms;
    val base_sort =
      if null inferred_elems then proto_base_sort
      else
        (case (fold o fold_element_types) Term.add_tfreesT inferred_elems [] of
          [] => error "No type variable in class specification"
        | [(_, sort)] => sort
        | _ => error "Multiple type variables in class specification");
    val supparams = map (fn ((c, T), _) =>
      (c, map_atyps (K (Term.aT base_sort)) T)) raw_supparams;
    val supparam_names = map fst supparams;
    fun mk_param ((c, _), _) = Free (c, (the o AList.lookup (op =) supparams) c);
    val supexpr = (map (fn sup => (sup, (("", false),
      (Expression.Positional (map (SOME o mk_param) (Locale.params_of thy sup)), [])))) sups,
        map (fn (c, T) => (Binding.name c, SOME T, NoSyn)) supparams);

  in (base_sort, supparam_names, supexpr, inferred_elems) end;

val cert_class_elems = prep_class_elems Expression.cert_declaration;
val read_class_elems = prep_class_elems Expression.cert_read_declaration;

fun prep_class_spec prep_class prep_include prep_class_elems ctxt raw_supclasses raw_includes raw_elems =
  let
    val thy = Proof_Context.theory_of ctxt;

    (* prepare import *)
    val inter_sort = curry (Sorts.inter_sort (Sign.classes_of thy));
    val sups = Sign.minimize_sort thy (map (prep_class ctxt) raw_supclasses);
    val _ =
      (case filter_out (Class.is_class thy) sups of
        [] => ()
      | no_classes => error ("No (proper) classes: " ^ commas_quote no_classes));
    val raw_supparams = (map o apsnd) (snd o snd) (Class.these_params thy sups);
    val raw_supparam_names = map fst raw_supparams;
    val _ =
      if has_duplicates (op =) raw_supparam_names then
        error ("Duplicate parameter(s) in superclasses: " ^
          (commas_quote (duplicates (op =) raw_supparam_names)))
      else ();

    (* infer types and base sort *)
    val includes = map (prep_include ctxt) raw_includes;
    val includes_ctxt = Bundle.includes includes ctxt;
    val (base_sort, supparam_names, supexpr, inferred_elems) = prep_class_elems includes_ctxt sups raw_elems;
    val sup_sort = inter_sort base_sort sups;

    (* process elements as class specification *)
    val class_ctxt = Class.begin sups base_sort includes_ctxt;
    val ((_, _, syntax_elems, _), _) = class_ctxt
      |> Expression.cert_declaration supexpr I inferred_elems;
    fun check_vars e vs =
      if null vs then
        error ("No type variable in part of specification element " ^
          Pretty.string_of (Pretty.chunks (Element.pretty_ctxt class_ctxt e)))
      else ();
    fun check_element (e as Element.Fixes fxs) =
          List.app (fn (_, SOME T, _) => check_vars e (Term.add_tfreesT T [])) fxs
      | check_element (e as Element.Assumes assms) =
          List.app (fn (_, ts_pss) =>
            List.app (fn (t, _) => check_vars e (Term.add_tfrees t [])) ts_pss) assms
      | check_element _ = ();
    val _ = List.app check_element syntax_elems;
    fun fork_syn (Element.Fixes xs) =
          fold_map (fn (c, ty, syn) => cons (c, syn) #> pair (c, ty, NoSyn)) xs
          #>> Element.Fixes
      | fork_syn x = pair x;
    val (elems, global_syntax) = fold_map fork_syn syntax_elems [];

  in (((sups, supparam_names), (sup_sort, base_sort, supexpr)), (includes, elems, global_syntax)) end;

val cert_class_spec = prep_class_spec (K I) (K I) cert_class_elems;
val read_class_spec = prep_class_spec Proof_Context.read_class Bundle.check_name read_class_elems;


(* class establishment *)

fun add_consts class base_sort sups supparam_names global_syntax thy =
  let
    (*FIXME simplify*)
    val supconsts = supparam_names
      |> AList.make (snd o the o AList.lookup (op =) (Class.these_params thy sups))
      |> (map o apsnd o apsnd o map_atyps) (K (Term.aT [class]));
    val all_params = Locale.params_of thy class;
    val raw_params = (snd o chop (length supparam_names)) all_params;
    fun add_const ((raw_c, raw_ty), _) thy =
      let
        val b = Binding.name raw_c;
        val c = Sign.full_name thy b;
        val ty = map_atyps (K (Term.aT base_sort)) raw_ty;
        val ty0 = Term.strip_sortsT ty;
        val ty' = map_atyps (K (Term.aT [class])) ty0;
        val syn = (the_default NoSyn o AList.lookup Binding.eq_name global_syntax) b;
      in
        thy
        |> Sign.declare_const_global ((b, ty0), syn)
        |> snd
        |> pair ((Variable.check_name b, ty), (c, ty'))
      end;
  in
    thy
    |> Sign.add_path (Class.class_prefix class)
    |> fold_map add_const raw_params
    ||> Sign.restore_naming thy
    |-> (fn params => pair (supconsts @ (map o apfst) fst params, params))
  end;

fun adjungate_axclass bname class base_sort sups supsort supparam_names global_syntax thy =
  let
    (*FIXME simplify*)
    fun globalize param_map = map_aterms
      (fn Free (v, ty) => Const ((fst o the o AList.lookup (op =) param_map) v, ty)
        | _ => raise Same.SAME);
    val raw_pred = Locale.intros_of thy class
      |> fst
      |> Option.map (Logic.unvarify_global o Logic.strip_imp_concl o Thm.prop_of);
    fun get_axiom thy =
      (case #axioms (Axclass.get_info thy class) of
         [] => NONE
      | [thm] => SOME thm);
  in
    thy
    |> add_consts class base_sort sups supparam_names global_syntax |-> (fn (param_map, params) =>
      Axclass.define_class (bname, supsort)
        (map (fst o snd) params)
          [(Binding.empty_atts, Option.map (globalize param_map) raw_pred |> the_list)]
      #> snd
      #> `get_axiom
      #-> (fn assm_axiom => fold (Sign.add_const_constraint o apsnd SOME o snd) params
      #> pair (param_map, params, assm_axiom)))
  end;

fun gen_class prep_class_spec b raw_includes raw_supclasses raw_elems thy =
  let
    val class = Sign.full_name thy b;
    val ctxt = Proof_Context.init_global thy;
    val (((sups, supparam_names), (supsort, base_sort, supexpr)), (includes, elems, global_syntax)) =
      prep_class_spec ctxt raw_supclasses raw_includes raw_elems;
    val of_class_binding = Binding.qualify_name true b "intro_of_class";
  in
    thy
    |> Expression.add_locale b (Binding.qualify true "class" b) includes supexpr elems
    |> snd |> Local_Theory.exit_global
    |> adjungate_axclass b class base_sort sups supsort supparam_names global_syntax
    |-> (fn (param_map, params, assm_axiom) =>
       `(fn thy => calculate thy class sups base_sort param_map assm_axiom)
    #-> (fn (base_morph, eq_morph, export_morph, some_axiom, some_assm_intro, of_class) =>
       Context.theory_map (Locale.add_registration
         {inst = (class, base_morph),
           mixin = Option.map (rpair true) eq_morph,
           export = export_morph})
    #> Class.register class sups params base_sort base_morph export_morph some_axiom some_assm_intro of_class
    #> Global_Theory.store_thm (of_class_binding, of_class)))
    |> snd
    |> Named_Target.init includes class
    |> pair class
  end;

in

val class = gen_class cert_class_spec;
val class_cmd = gen_class read_class_spec;

end; (*local*)



(** subclass relations **)

local

fun gen_subclass prep_class do_proof raw_sup lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val proto_sup = prep_class thy raw_sup;
    val proto_sub =
      (case Named_Target.class_of lthy of
        SOME class => class
      | NONE => error "Not in a class target");
    val (sub, sup) = Axclass.cert_classrel thy (proto_sub, proto_sup);

    val expr = ([(sup, (("", false), (Expression.Positional [], [])))], []);
    val (([props], _, deps, _, export), goal_ctxt) =
      Expression.cert_goal_expression expr lthy;
    val some_prop = try the_single props;
    val some_dep_morph = try the_single (map snd deps);
    fun after_qed some_wit =
      Class.register_subclass (sub, sup) some_dep_morph some_wit export;
  in do_proof after_qed some_prop goal_ctxt end;

fun user_proof after_qed some_prop =
  Element.witness_proof (after_qed o try the_single o the_single)
    [the_list some_prop];

fun tactic_proof tac after_qed some_prop ctxt =
  after_qed (Option.map
    (fn prop => Element.prove_witness ctxt prop tac) some_prop) ctxt;

in

fun prove_subclass tac = gen_subclass (K I) (tactic_proof tac);

fun subclass x = gen_subclass (K I) user_proof x;
fun subclass_cmd x =
  gen_subclass (Proof_Context.read_class o Proof_Context.init_global) user_proof x;

end; (*local*)

end;
