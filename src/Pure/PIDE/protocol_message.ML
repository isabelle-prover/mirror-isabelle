(*  Title:      Pure/PIDE/protocol_message.ML
    Author:     Makarius

Auxiliary operations on protocol messages.
*)

signature PROTOCOL_MESSAGE =
sig
  val marker_text: string -> string -> unit
  val marker: string -> Properties.T -> unit
  val command_positions: string -> XML.body -> XML.body
  val command_positions_yxml: string -> string -> string
  val clean_output: string -> string
end;

structure Protocol_Message: PROTOCOL_MESSAGE =
struct

(* message markers *)

fun marker_text a text =
  Output.physical_writeln ("\f" ^ a ^ " = " ^ encode_lines text);

fun marker a props =
  marker_text a (YXML.string_of_body (XML.Encode.properties props));


(* inlined messages *)

fun command_positions id =
  let
    fun attribute (a, b) =
      if a = Markup.idN andalso b = Markup.commandN then (a, id) else (a, b);
    fun tree (XML.Elem ((a, atts), ts)) = XML.Elem ((a, map attribute atts), map tree ts)
      | tree text = text;
  in map tree end;

fun command_positions_yxml id =
  YXML.string_of_body o command_positions id o YXML.parse_body;


(* clean output *)

fun clean_output msg =
  (case try YXML.parse_body msg of
    SOME xml =>
      xml |> XML.filter_elements
        {remove = fn a => a = Markup.reportN,
         expose = fn a => a = Markup.no_reportN}
      |> XML.content_of
  | NONE => msg);

end;
