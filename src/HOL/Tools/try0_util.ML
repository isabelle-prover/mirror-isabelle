(* Title:      HOL/Tools/try0_hol.ML
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen

General-purpose functions used by Try0.
*)

signature TRY0_UTIL =
sig
  val string_of_xref : Try0.xref -> string

  type facts_config =
    {usings_as_params : bool,
     simps_prefix : string option,
     intros_prefix : string option,
     elims_prefix : string option,
     dests_prefix : string option}
  val full_attrs : facts_config
  val clas_attrs : facts_config
  val simp_attrs : facts_config
  val metis_attrs : facts_config
  val no_attrs : facts_config
  val apply_raw_named_method : string -> bool -> facts_config ->
    (Proof.context -> Proof.context) -> Time.time option -> Try0.facts -> Proof.state ->
    Try0.result option
end

structure Try0_Util : TRY0_UTIL = struct

fun string_of_xref ((xref, args) : Try0.xref) =
  (case xref of
    Facts.Fact literal => literal |> Symbol_Pos.explode0 |> Symbol_Pos.implode |> cartouche
  | _ =>
      Facts.string_of_ref xref) ^ implode
        (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args)

type facts_config =
  {usings_as_params : bool,
   simps_prefix : string option,
   intros_prefix : string option,
   elims_prefix : string option,
   dests_prefix : string option}

val no_attrs : facts_config =
  {usings_as_params = false,
   simps_prefix = NONE,
   intros_prefix = NONE,
   elims_prefix = NONE,
   dests_prefix = NONE}
val full_attrs : facts_config =
  {usings_as_params = false,
   simps_prefix = SOME "simp: ",
   intros_prefix = SOME "intro: ",
   elims_prefix = SOME "elim: ",
   dests_prefix = SOME "dest: "}
val clas_attrs : facts_config =
  {usings_as_params = false,
   simps_prefix = NONE,
   intros_prefix = SOME "intro: ",
   elims_prefix = SOME "elim: ",
   dests_prefix = SOME "dest: "}
val simp_attrs : facts_config =
  {usings_as_params = false,
   simps_prefix = SOME "add: ",
   intros_prefix = NONE,
   elims_prefix = NONE,
   dests_prefix = NONE}
val metis_attrs : facts_config =
  {usings_as_params = true,
   simps_prefix = SOME "",
   intros_prefix = SOME "",
   elims_prefix = SOME "",
   dests_prefix = SOME ""}

local

fun parse_method ctxt s =
  enclose "(" ")" s
  |> Token.explode (Thy_Header.get_keywords' ctxt) Position.start
  |> filter Token.is_proper
  |> Scan.read Token.stopper Method.parse
  |> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source")

fun run_tac timeout_opt tac st =
  let val with_timeout =
    (case timeout_opt of SOME timeout => Timeout.apply_physical timeout | NONE => I)
  in with_timeout (Seq.pull o tac) st |> Option.map fst end

val num_goals = Thm.nprems_of o #goal o Proof.goal

fun apply_recursive recurse elapsed0 timeout_opt apply st =
  (case Timing.timing (Option.join o try (run_tac timeout_opt apply)) st of
    ({elapsed, ...}, SOME st') =>
      if recurse andalso num_goals st' > 0 andalso num_goals st' < num_goals st then
        let val timeout_opt1 = (Option.map (fn timeout => timeout - elapsed) timeout_opt)
        in apply_recursive recurse (elapsed0 + elapsed) timeout_opt1 apply st' end
      else (elapsed0 + elapsed, st')
   |_ => (elapsed0, st))

in

fun apply_raw_named_method (name : string) all_goals (facts_config: facts_config)
  (silence_methods : Proof.context -> Proof.context) timeout_opt (facts : Try0.facts)
  (st : Proof.state) : Try0.result option =
  let
    val st = Proof.map_contexts silence_methods st
    val ctxt = Proof.context_of st

    val (unused_simps, simps_attrs) =
       if null (#simps facts) then
        ([], "")
      else
        (case #simps_prefix facts_config of
          NONE =>  (#simps facts, "")
        | SOME prefix => ([], " " ^ prefix ^ implode_space (map string_of_xref (#simps facts))))

    val (unused_intros, intros_attrs) =
      if null (#intros facts) then
        ([], "")
      else
        (case #intros_prefix facts_config of
          NONE =>  (#intros facts, "")
        | SOME prefix => ([], " " ^ prefix ^ implode_space (map string_of_xref (#intros facts))))

    val (unused_elims, elims_attrs) =
      if null (#elims facts) then
        ([], "")
      else
        (case #elims_prefix facts_config of
          NONE =>  (#elims facts, "")
        | SOME prefix => ([], " " ^ prefix ^ implode_space (map string_of_xref (#elims facts))))

    val (unused_dests, dests_attrs) =
      if null (#dests facts) then
        ([], "")
      else
        (case #dests_prefix facts_config of
          NONE =>  (#dests facts, "")
        | SOME prefix => ([], " " ^ prefix ^ implode_space (map string_of_xref (#dests facts))))

    val (unused_usings, using_attrs) =
      if null (#usings facts) then
        ([], "")
      else if #usings_as_params facts_config then
        ([], " " ^ implode_space (map string_of_xref (#usings facts)))
      else
        (#usings facts, "")

    val unused = unused_simps @ unused_intros @ unused_elims @ unused_dests @ unused_usings

    val attrs = simps_attrs ^ intros_attrs ^ elims_attrs ^ dests_attrs ^ using_attrs
    val text =
      name ^ attrs
      |> parse_method ctxt
      |> Method.method_cmd ctxt
      |> Method.Basic
      |> (fn m => Method.Combinator (Method.no_combinator_info, Method.Select_Goals 1, [m]))

    val apply =
        Proof.using [Attrib.eval_thms ctxt unused |> map (rpair [] o single)]
        #> Proof.refine text #> Seq.filter_results
    val num_before = num_goals st
    val multiple_goals = all_goals andalso num_before > 1
    val (time, st') = apply_recursive multiple_goals Time.zeroTime timeout_opt apply st
    val num_after = num_goals st'
    val select = "[" ^ string_of_int (num_before - num_after)  ^ "]"
    val unused = implode_space (unused |> map string_of_xref)
    val command =
      (if unused <> "" then "using " ^ unused ^ " " else "") ^
      (if num_after = 0 then "by " else "apply ") ^
      (name ^ attrs |> attrs <> "" ? enclose "(" ")") ^
      (if multiple_goals andalso num_after > 0 then select else "")
  in
    if num_before > num_after then
      SOME {name = name, command = command, time = time, state = st'}
    else NONE
  end

end

end
