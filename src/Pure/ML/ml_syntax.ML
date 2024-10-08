(*  Title:      Pure/ML/ml_syntax.ML
    Author:     Makarius

Concrete ML syntax for basic values.
*)

signature ML_SYNTAX =
sig
  val reserved_names: string list
  val reserved: Name.context
  val is_reserved: string -> bool
  val is_identifier: string -> bool
  val atomic: string -> string
  val print_int: int -> string
  val print_pair: ('a -> string) -> ('b -> string) -> 'a * 'b -> string
  val print_list: ('a -> string) -> 'a list -> string
  val print_option: ('a -> string) -> 'a option -> string
  val print_symbol_char: Symbol.symbol -> string
  val print_symbol: Symbol.symbol -> string
  val print_string: string -> string
  val print_strings: string list -> string
  val print_path: Path.T -> string
  val print_platform_path: Path.T -> string
  val print_properties: Properties.T -> string
  val print_position: Position.T -> string
  val print_range: Position.range -> string
  val print_path_binding: Path.binding -> string
  val make_binding: string * Position.T -> string
  val print_indexname: indexname -> string
  val print_class: class -> string
  val print_sort: sort -> string
  val print_typ: typ -> string
  val print_term: term -> string
  val pretty_string: int -> string -> Pretty.T
end;

structure ML_Syntax: ML_SYNTAX =
struct

(* reserved words *)

val reserved_names = filter Symbol.is_ascii_identifier ML_Lex.keywords;
val reserved = Name.make_context reserved_names;
val is_reserved = Name.is_declared reserved;


(* identifiers *)

fun is_identifier name =
  not (is_reserved name) andalso Symbol.is_ascii_identifier name;


(* literal output -- unformatted *)

val atomic = enclose "(" ")";

val print_int = string_of_int;

fun print_pair f1 f2 (x, y) = "(" ^ f1 x ^ ", " ^ f2 y ^ ")";

fun print_list f = enclose "[" "]" o commas o map f;

fun print_option f NONE = "NONE"
  | print_option f (SOME x) = "SOME (" ^ f x ^ ")";

fun print_symbol_char s =
  if Symbol.is_char s then
    (case ord s of
      34 => "\\\""
    | 92 => "\\\\"
    | 7 => "\\a"
    | 8 => "\\b"
    | 9 => "\\t"
    | 10 => "\\n"
    | 11 => "\\v"
    | 12 => "\\f"
    | 13 => "\\r"
    | c =>
        if c < 32 then "\\^" ^ chr (c + 64)
        else if c < 127 then s
        else "\\" ^ string_of_int c)
  else error ("Bad character: " ^ quote s);

fun print_symbol s =
  if Symbol.is_char s then print_symbol_char s
  else if Symbol.is_utf8 s then translate_string print_symbol_char s
  else s;

val print_string = quote o implode o map print_symbol o Symbol.explode;
val print_strings = print_list print_string;

fun print_path path =
  "Path.explode " ^ print_string (Path.implode path);

val print_platform_path = print_string o File.platform_path;

val print_properties = print_list (print_pair print_string print_string);

fun print_position pos =
  let val {line, offset, end_offset, props = {label, file, id}} = Position.dest pos in
    implode_space
      ["Position.make0", print_int line, print_int offset, print_int end_offset,
        print_string label, print_string file, print_string id]
  end;

fun print_range range =
  "Position.range_of_properties " ^ print_properties (Position.properties_of_range range);

fun print_path_binding binding =
  "Path.binding " ^ print_pair print_path print_position (Path.dest_binding binding);

fun make_binding (name, pos) =
  "Binding.make " ^ print_pair print_string print_position (name, pos);

val print_indexname = print_pair print_string print_int;

val print_class = print_string;
val print_sort = print_list print_class;

fun print_typ (Type arg) = "Term.Type " ^ print_pair print_string (print_list print_typ) arg
  | print_typ (TFree arg) = "Term.TFree " ^ print_pair print_string print_sort arg
  | print_typ (TVar arg) = "Term.TVar " ^ print_pair print_indexname print_sort arg;

fun print_term (Const arg) = "Term.Const " ^ print_pair print_string print_typ arg
  | print_term (Free arg) = "Term.Free " ^ print_pair print_string print_typ arg
  | print_term (Var arg) = "Term.Var " ^ print_pair print_indexname print_typ arg
  | print_term (Bound i) = "Term.Bound " ^ print_int i
  | print_term (Abs (s, T, t)) =
      "Term.Abs (" ^ print_string s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
  | print_term (t1 $ t2) = "Term.$ " ^ print_pair print_term print_term (t1, t2);


(* toplevel pretty printing *)

fun pretty_string max_len str =
  let
    val body =
      if YXML.is_wellformed str then
        maps (fn XML.Elem _ => ["<markup>"] | XML.Text s => Symbol.explode s) (YXML.parse_body str)
      else Symbol.explode str;
    val body' =
      if length body <= max_len then body
      else take (Int.max (max_len, 0)) body @ ["..."];
  in Pretty.str (quote (implode (map print_symbol body'))) end;

fun pretty_string' depth = pretty_string (FixedInt.toInt (depth * 100));

val _ =
  ML_system_pp (fn depth => fn _ => fn str =>
    Pretty.to_ML (pretty_string' depth str));

val _ =
  ML_system_pp (fn depth => fn _ => fn chunks =>
    Pretty.to_ML (pretty_string' depth (Long_Name.implode_chunks chunks)));

end;
