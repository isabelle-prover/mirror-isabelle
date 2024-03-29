(*  Title:      Pure/Isar/named_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Targets for theory, locale, class -- at the bottom of the nested structure.
*)

signature NAMED_TARGET =
sig
  val is_theory: local_theory -> bool
  val locale_of: local_theory -> string option
  val bottom_locale_of: local_theory -> string option
  val class_of: local_theory -> string option
  val init: Bundle.name list -> string -> theory -> local_theory
  val theory_init: theory -> local_theory
  val theory_map: (local_theory -> local_theory) -> theory -> theory
  val theory_map_result: (morphism -> 'a -> 'b) -> (local_theory -> 'a * local_theory) ->
    theory -> 'b * theory
  val setup: (local_theory -> local_theory) -> unit
  val setup_result: (morphism -> 'a -> 'b) -> (local_theory -> 'a * local_theory) -> 'b
  val setup_result0: (local_theory -> 'a * local_theory) -> 'a
  val revoke_reinitializability: local_theory -> local_theory
  val exit_global_reinitialize: local_theory -> (theory -> local_theory) * theory
end;

structure Named_Target: NAMED_TARGET =
struct

(* context data *)

datatype target = Theory | Locale of string | Class of string;

fun target_of_ident _ "" = Theory
  | target_of_ident thy ident =
      if Locale.defined thy ident
      then (if Class.is_class thy ident then Class else Locale) ident
      else error ("No such locale: " ^ quote ident);

fun ident_of_target Theory = ""
  | ident_of_target (Locale locale) = locale
  | ident_of_target (Class class) = class;

fun target_is_theory (SOME Theory) = true
  | target_is_theory _ = false;

fun locale_of_target (SOME (Locale locale)) = SOME locale
  | locale_of_target (SOME (Class locale)) = SOME locale
  | locale_of_target _ = NONE;

fun class_of_target (SOME (Class class)) = SOME class
  | class_of_target _ = NONE;

structure Data = Proof_Data
(
  type T = (target * bool) option;
  fun init _ = NONE;
);

val get_bottom_target = Option.map fst o Data.get;

fun get_target lthy =
  if Local_Theory.level lthy = 1
  then get_bottom_target lthy
  else NONE;

fun ident_of lthy =
  case get_target lthy of
    NONE => error "Not in a named target"
  | SOME target => ident_of_target target;

val is_theory = target_is_theory o get_target;

val locale_of = locale_of_target o get_target;

val bottom_locale_of = locale_of_target o get_bottom_target;

val class_of = class_of_target o get_target;

fun is_reinitializable lthy =
  Local_Theory.level lthy = 1 andalso (the_default false o Option.map snd o Data.get) lthy;


(* operations *)

fun locale_foundation locale (((b, U), mx), (b_def, rhs)) params =
  Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => Generic_Target.locale_const locale Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def));

fun class_foundation class (((b, U), mx), (b_def, rhs)) params =
  Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => Class.const class ((b, mx), lhs) params
    #> pair (lhs, def));

fun operations Theory =
      {define = Generic_Target.define Generic_Target.theory_target_foundation,
       notes = Generic_Target.notes Generic_Target.theory_target_notes,
       abbrev = Generic_Target.theory_abbrev,
       declaration = fn _ => Generic_Target.theory_declaration,
       theory_registration = Generic_Target.theory_registration,
       locale_dependency = fn _ => error "Not possible in theory target",
       pretty = fn ctxt => [Pretty.block [Pretty.keyword1 "theory", Pretty.brk 1,
        Pretty.str (Context.theory_base_name (Proof_Context.theory_of ctxt))]]}
  | operations (Locale locale) =
      {define = Generic_Target.define (locale_foundation locale),
       notes = Generic_Target.notes (Generic_Target.locale_target_notes locale),
       abbrev = Generic_Target.locale_abbrev locale,
       declaration = Generic_Target.locale_declaration locale,
       theory_registration = fn _ => error "Not possible in locale target",
       locale_dependency = Generic_Target.locale_dependency locale,
       pretty = fn ctxt => [Locale.pretty_locale (Proof_Context.theory_of ctxt) false locale]}
  | operations (Class class) =
      {define = Generic_Target.define (class_foundation class),
       notes = Generic_Target.notes (Generic_Target.locale_target_notes class),
       abbrev = Class.abbrev class,
       declaration = Generic_Target.locale_declaration class,
       theory_registration = fn _ => error "Not possible in class target",
       locale_dependency = Generic_Target.locale_dependency class,
       pretty = fn ctxt => Class.pretty_specification (Proof_Context.theory_of ctxt) class};

fun setup_context Theory = Proof_Context.init_global
  | setup_context (Locale locale) = Locale.init locale
  | setup_context (Class class) = Class.init class;

fun setup target includes =
  setup_context target
  #> Data.put (SOME (target, null includes))
  #> Bundle.includes includes;

fun init includes ident thy =
  let
    val target = target_of_ident thy ident;
  in
    thy
    |> Local_Theory.init
       {background_naming = Sign.naming_of thy |> Name_Space.mandatory_path (Long_Name.base_name ident),
        setup = setup target includes,
        conclude = I}
       (operations target)
  end;

val theory_init = init [] "";

fun theory_map g = theory_init #> g #> Local_Theory.exit_global;
fun theory_map_result f g = theory_init #> g #> Local_Theory.exit_result_global f;

fun setup g = Context.>> (Context.mapping (theory_map g) g);
fun setup_result f g =
  Context.>>> (Context.mapping_result (theory_map_result f g) (g #>> f Morphism.identity));
fun setup_result0 g = setup_result (K I) g;

val revoke_reinitializability = (Data.map o Option.map o apsnd) (K false);

fun exit_global_reinitialize lthy =
  if is_reinitializable lthy
  then (init [] (ident_of lthy), Local_Theory.exit_global lthy)
  else error "Non-reinitializable local theory context";

end;
