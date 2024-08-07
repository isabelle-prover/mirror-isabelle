(*  Title:      HOL/Tools/Quickcheck/abstract_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Quickcheck generators for abstract types.
*)

signature ABSTRACT_GENERATORS =
sig
  val quickcheck_generator : string -> term option -> term list -> theory -> theory
end

structure Abstract_Generators : ABSTRACT_GENERATORS =
struct

fun check_constrs ctxt tyco constrs =
  let
    fun check_type c =
      (case try (dest_Type o body_type o fastype_of) c of
        NONE => error (Syntax.string_of_term ctxt c ^ " has mismatching result type.")
      | SOME (tyco', vs) => if not (tyco' = tyco) then
            error (Syntax.string_of_term ctxt c ^ " has mismatching result type. " ^
              "Expected type constructor " ^ quote tyco ^ ", but found " ^ quote tyco' ^ ".")
          else
            (case try (map dest_TFree) vs of
              NONE => error (Syntax.string_of_term ctxt c ^ " has mismatching result type.")
            | SOME _ => ()))
  in map check_type constrs end

fun gen_quickcheck_generator prep_tyco prep_term tyco_raw opt_pred_raw constrs_raw thy =
  let
    val ctxt = Proof_Context.init_global thy
    val tyco = prep_tyco ctxt tyco_raw
    val opt_pred = Option.map (prep_term ctxt) opt_pred_raw
    val constrs = map (prep_term ctxt) constrs_raw
    val _ = check_constrs ctxt tyco constrs
    val vs = map dest_TFree (dest_Type_args (body_type (fastype_of (hd constrs))))
    val name = Long_Name.base_name tyco
    fun mk_dconstrs (Const (s, T)) =
          (s, map (Old_Datatype_Aux.dtyp_of_typ [(tyco, vs)]) (binder_types T))
      | mk_dconstrs t =
          error (Syntax.string_of_term ctxt t ^
            " is not a valid constructor for quickcheck_generator, which expects a constant.")
    fun the_descr _ _ =
      let val descr = [(0, (tyco, map Old_Datatype_Aux.DtTFree vs, map mk_dconstrs constrs))]
      in (descr, vs, [tyco], name, ([name], []), ([Type (tyco, map TFree vs)], [])) end
    fun ensure_sort (sort, instantiate) =
      Quickcheck_Common.ensure_sort
        (((\<^sort>\<open>typerep\<close>, \<^sort>\<open>term_of\<close>), sort), (the_descr, instantiate))
        Old_Datatype_Aux.default_config [tyco]
  in
    thy
    |> ensure_sort
        (\<^sort>\<open>full_exhaustive\<close>, Exhaustive_Generators.instantiate_full_exhaustive_datatype)
    |> ensure_sort (\<^sort>\<open>exhaustive\<close>, Exhaustive_Generators.instantiate_exhaustive_datatype)
    |> ensure_sort (\<^sort>\<open>random\<close>, Random_Generators.instantiate_random_datatype)
    |> (case opt_pred of NONE => I
       | SOME t => Context.theory_map (Quickcheck_Common.register_predicate (t, tyco)))
  end

val quickcheck_generator = gen_quickcheck_generator (K I) (K I)

val quickcheck_generator_cmd =
  gen_quickcheck_generator
    (dest_Type_name oo Proof_Context.read_type_name {proper = true, strict = true})
    Syntax.read_term

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>quickcheck_generator\<close>
    "define quickcheck generators for abstract types"
    ((Parse.type_const --
      Scan.option (Args.$$$ "predicate" |-- \<^keyword>\<open>:\<close> |-- Parse.term)) --
      (Args.$$$ "constructors" |-- \<^keyword>\<open>:\<close> |-- Parse.list1 Parse.term)
      >> (fn ((tyco, opt_pred), constrs) =>
        Toplevel.theory (quickcheck_generator_cmd tyco opt_pred constrs)))

end
