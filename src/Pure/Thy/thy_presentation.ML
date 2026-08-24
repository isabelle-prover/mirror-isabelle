(*  Title:      Pure/Thy/thy_presentation.ML
    Author:     Makarius

Presentation of theory content.
*)

signature THY_PRESENTATION =
sig
  type context =
    {options: Options.T, file_pos: Position.T, adjust_pos: Position.T -> Position.T,
      segments: Document_Output.segment list}
  val adjust_pos_properties: context -> Position.T -> Properties.T
  val apply_hooks: context -> theory -> unit
  val add_hook: (context -> theory -> unit) -> theory -> theory
end;

structure Thy_Presentation: THY_PRESENTATION =
struct

(** theory presentation **)

(* hook for consolidated theory *)

type context =
  {options: Options.T, file_pos: Position.T, adjust_pos: Position.T -> Position.T,
    segments: Document_Output.segment list};

fun adjust_pos_properties (context: context) pos =
  let
    val props = Position.properties_of pos;
    val props' = Position.properties_of (#adjust_pos context pos);
  in
    filter (fn (a, _) => a = Markup.offsetN orelse a = Markup.end_offsetN) props' @
    filter (fn (a, _) => a = Markup.labelN orelse a = Markup.fileN orelse a = Markup.idN) props
  end;

structure Data = Theory_Data
(
  type T = ((context -> theory -> unit) * stamp) list;
  val empty = [];
  fun merge data : T = Library.merge (eq_snd op =) data;
);

fun apply_hooks (context: context) thy =
  ignore (Par_List.map (fn (f, _) => f context thy) (Data.get thy));

fun add_hook f = Data.map (cons (f, stamp ()));

val _ =
  Theory.setup (add_hook (fn {options, segments, ...} => fn thy =>
    let
      val keywords = Thy_Header.get_keywords thy;
      val thy_name = Context.theory_base_name thy;
      val latex = Document_Output.present_thy options keywords thy_name segments;
    in
      if Options.string options "document" = "false" then ()
      else Export.export thy \<^path_binding>\<open>document/latex\<close> latex
    end));

end;
