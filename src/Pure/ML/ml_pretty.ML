(*  Title:      Pure/ML/ml_pretty.ML
    Author:     Makarius

Minimal support for raw ML pretty printing, notably for toplevel pp.
*)

signature ML_PRETTY =
sig
  datatype context = datatype PolyML.context
  val markup_get: PolyML.context list -> string * string
  val markup_context: string * string -> PolyML.context list
  val no_markup_context: PolyML.context list -> PolyML.context list
  val open_block_detect: PolyML.context list -> bool
  val open_block_context: bool -> PolyML.context list
  datatype pretty = datatype PolyML.pretty
  val no_markup: pretty -> pretty
  val block: pretty list -> pretty
  val str: string -> pretty
  val brk: FixedInt.int -> pretty
  val dots: pretty
  val pair: ('a * FixedInt.int -> pretty) -> ('b * FixedInt.int -> pretty) ->
    ('a * 'b) * FixedInt.int -> pretty
  val enum: string -> string -> string -> ('a * FixedInt.int -> pretty) ->
    'a list * FixedInt.int -> pretty
  val prune: FixedInt.int -> pretty -> pretty
  val format: int -> pretty -> string
  val default_margin: int
  val get_margin: int option -> int
  val string_of: pretty -> string
  val make_string_fn: string
end;

structure ML_Pretty: ML_PRETTY =
struct

(** context **)

(* properties *)

datatype context = datatype PolyML.context;

fun get_property context name =
  (case List.find (fn ContextProperty (a, _) => name = a | _ => false) context of
    SOME (ContextProperty (_, b)) => b
  | _ => "");


(* markup *)

val markup_bg = "markup_bg";
val markup_en = "markup_en";

fun markup_get context =
  let
    val bg = get_property context markup_bg;
    val en = get_property context markup_en;
  in (bg, en) end;

fun markup_context (bg, en) =
  (if bg = "" then [] else [ContextProperty (markup_bg, bg)]) @
  (if en = "" then [] else [ContextProperty (markup_en, en)]);

val no_markup_context =
  List.filter (fn ContextProperty (a, _) => a <> markup_bg andalso a <> markup_en | _ => true);


(* open_block flag *)

val open_block = ContextProperty ("open_block", "");

val open_block_detect =
  List.exists (fn ContextProperty ("open_block", _) => true | _ => false);

fun open_block_context true = [open_block]
  | open_block_context false = [];



(** pretty printing **)

(* datatype pretty with derived operations *)

datatype pretty = datatype PolyML.pretty;

fun no_markup (PrettyBlock (a, b, c, d)) = PrettyBlock (a, b, no_markup_context c, map no_markup d)
  | no_markup a = a;

fun block prts = PrettyBlock (2, false, [], prts);
val str = PrettyString;
fun brk width = PrettyBreak (width, 0);

val dots = str "...";

fun pair pretty1 pretty2 ((x, y), depth: FixedInt.int) =
  if depth = 0 then dots
  else block [str "(", pretty1 (x, depth), str ",", brk 1, pretty2 (y, depth - 1), str ")"];

fun enum sep lpar rpar pretty (args, depth: FixedInt.int) =
  if depth = 0 then dots
  else
    let
      fun elems _ [] = []
        | elems 0 _ = [dots]
        | elems d [x] = [pretty (x, d)]
        | elems d (x :: xs) = pretty (x, d) :: str sep :: brk 1 :: elems (d - 1) xs;
    in block (str lpar :: (elems (FixedInt.max (depth, 0)) args @ [str rpar])) end;


(* prune *)

fun prune (0: FixedInt.int) (PrettyBlock _) = dots
  | prune depth (PrettyBlock (ind, consistent, context, body)) =
      PrettyBlock (ind, consistent, context, map (prune (depth - 1)) body)
  | prune _ prt = prt;


(* format *)

fun format margin prt =
  let
    val result = Unsynchronized.ref [];
    val () = PolyML.prettyPrint (fn s => result := s :: ! result, margin) prt;
  in implode (rev (! result)) end;

val default_margin = 76;

val get_margin = the_default default_margin;


(* make string *)

val string_of = format default_margin;

val make_string_fn =
  "(fn x => ML_Pretty.string_of (ML_system_pretty \
    \(x, FixedInt.fromInt (ML_Print_Depth.get_print_depth ()))))";

end;
