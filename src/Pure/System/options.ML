(*  Title:      Pure/System/options.ML
    Author:     Makarius

System options with external string representation.
*)

signature OPTIONS =
sig
  val boolT: string
  val intT: string
  val realT: string
  val stringT: string
  val unknownT: string
  type T
  val empty: T
  val dest: T -> (string * Position.T) list
  val typ: T -> string -> string
  val bool: T -> string -> bool
  val int: T -> string -> int
  val real: T -> string -> real
  val seconds: T -> string -> Time.time
  val string: T -> string -> string
  val put_bool: string -> bool -> T -> T
  val put_int: string -> int -> T -> T
  val put_real: string -> real -> T -> T
  val put_string: string -> string -> T -> T
  type entry = {pos: Position.T, typ: string, value: string, standard_value: string option}
  val declare: string * entry -> T -> T
  type spec = string * string option
  val spec1: string -> spec
  val spec: string -> string -> spec
  type update = spec list
  val update: update -> T -> T
  type spec_pos = (string * Position.T) * (string * Position.T) option
  type update_pos = spec_pos list
  val spec_no_pos: spec_pos -> spec
  val update_no_pos: update_pos -> update
  val spec_pos_none: spec -> spec_pos
  val update_pos_none: update -> update_pos
  val encode: T XML.Encode.T
  val decode: T XML.Decode.T
  val the_process_default: unit -> T
  val set_process_default: T option -> unit
  val load_process_default: unit -> unit
  val inherit_thread_update: unit -> ('a -> 'b) -> 'a -> 'b
  val default: update -> T
  val default_typ: string -> string
  val default_bool: string -> bool
  val default_int: string -> int
  val default_real: string -> real
  val default_seconds: string -> Time.time
  val default_string: string -> string
  val get_default: string -> string
  val with_default_update: update -> ('a -> 'b) -> 'a -> 'b
end;

structure Options: OPTIONS =
struct

(* representation *)

val boolT = "bool";
val intT = "int";
val realT = "real";
val stringT = "string";
val unknownT = "unknown";

type entry = {pos: Position.T, typ: string, value: string, standard_value: string option};
datatype T = Options of entry Symtab.table;

val empty = Options Symtab.empty;

fun dest (Options tab) =
  Symtab.fold (fn (name, {pos, ...}) => cons (name, pos)) tab []
  |> sort_by #1;


(* check *)

fun check_name (Options tab) name =
  let val opt = Symtab.lookup tab name in
    if is_some opt andalso #typ (the opt) <> unknownT then the opt
    else error ("Unknown system option " ^ quote name)
  end;

fun check_type options name typ =
  let val opt = check_name options name in
    if #typ opt = typ then opt
    else error ("Ill-typed system option " ^ quote name ^ " : " ^ #typ opt ^ " vs. " ^ typ)
  end;


(* typ *)

fun typ options name = #typ (check_name options name);


(* basic operations *)

fun put T print name x (options as Options tab) =
  let
    val {pos, typ, standard_value, ...} = check_type options name T;
    val opt' = {pos = pos, typ = typ, value = print x, standard_value = standard_value};
  in Options (Symtab.update (name, opt') tab) end;

fun get T parse options name =
  let val opt = check_type options name T in
    (case parse (#value opt) of
      SOME x => x
    | NONE =>
        error ("Malformed value for system option " ^ quote name ^
          " : " ^ T ^ " =\n" ^ quote (#value opt)))
  end;


(* internal lookup and update *)

val bool = get boolT (try Value.parse_bool);
val int = get intT (try Value.parse_int);
val real = get realT (try Value.parse_real);
val seconds = Time.fromReal oo real;
val string = get stringT SOME;

val put_bool = put boolT Value.print_bool;
val put_int = put intT Value.print_int;
val put_real = put realT Value.print_real;
val put_string = put stringT I;


(* external updates *)

fun check_value options name =
  let val opt = check_name options name in
    if #typ opt = boolT then ignore (bool options name)
    else if #typ opt = intT then ignore (int options name)
    else if #typ opt = realT then ignore (real options name)
    else if #typ opt = stringT then ignore (string options name)
    else ()
  end;

fun declare (name, entry as {pos, typ, ...}: entry) (Options tab) =
  let
    val options' =
      (case Symtab.lookup tab name of
        SOME other =>
          error ("Duplicate declaration of system option " ^ quote name ^ Position.here pos ^
            Position.here (#pos other))
      | NONE => Options (Symtab.update (name, entry) tab));
    val _ =
      typ = boolT orelse typ = intT orelse typ = realT orelse typ = stringT orelse
        error ("Unknown type for system option " ^ quote name ^ " : " ^ quote typ ^
          Position.here pos);
    val _ = check_value options' name;
  in options' end;

type spec = string * string option;
fun spec1 name : spec = (name, NONE);
fun spec name value : spec = (name, SOME value);

type update = spec list;

val update = fold (fn ((name, opt_value): spec) => fn options as Options tab =>
  let
    val {pos, typ, standard_value, ...} = check_name options name;
    val value =
      (case opt_value of
        SOME value => value
      | NONE =>
          (case standard_value of
            SOME value => value
          | NONE =>
              if typ = boolT then "true"
              else error ("Missing value for option " ^ quote name ^ " : " ^ typ)));
    val opt' = {pos = pos, typ = typ, value = value, standard_value = standard_value};
    val options' = Options (Symtab.update (name, opt') tab);
    val _ = check_value options' name;
  in options' end);

type spec_pos = (string * Position.T) * (string * Position.T) option;
type update_pos = spec_pos list;

fun spec_no_pos (opt: spec_pos) : spec = (#1 (#1 opt), Option.map #1 (#2 opt));
val update_no_pos = map spec_no_pos;

fun spec_pos_none (opt: spec) : spec_pos =
  ((#1 opt, Position.none), Option.map (rpair Position.none) (#2 opt));
val update_pos_none = map spec_pos_none;


(* XML data *)

fun encode (Options tab) =
  let
    val opts =
      build (tab |> Symtab.fold (fn (name, {pos, typ, value, standard_value}) =>
        cons (Position.properties_of pos, (name, (typ, (value, standard_value))))));
    open XML.Encode;
  in list (pair properties (pair string (pair string (pair string (option string))))) opts end;

fun decode body =
  let
    open XML.Decode;
    val decode_options =
      list (pair properties (pair string (pair string (pair string (option string)))))
      #> map (fn (props, (name, (typ, (value, standard_value)))) =>
        let
          val entry = {pos = Position.of_properties props, typ = typ, value = value,
            standard_value = standard_value};
        in (name, entry) end);
  in fold declare (decode_options body) empty end;



(** implicit default **)

(* process default *)

val process_default = Synchronized.var "Options.process_default" (NONE: T option);

fun missing_process_default () =
  error "Missing default for system options within Isabelle/ML process";

fun the_process_default () =
  (case Synchronized.value process_default of
    SOME options => options
  | NONE => missing_process_default ());

fun set_process_default opt = Synchronized.change process_default (K opt);

fun load_process_default () =
  (case getenv "ISABELLE_PROCESS_OPTIONS" of
    "" => ()
  | name =>
      try Bytes.read (Path.explode name)
      |> Option.app (set_process_default o SOME o decode o YXML.parse_body_bytes));


(* thread-local update *)

val thread_update = Thread_Data.var () : update Thread_Data.var;

fun get_thread_update () = Thread_Data.get thread_update |> these;

fun setmp_thread_update upd f x =
  if get_thread_update () = upd then f x
  else Thread_Data.setmp thread_update (SOME upd) f x;

fun inherit_thread_update () =
  let val upd = get_thread_update ()
  in setmp_thread_update upd end;


(* generic default *)

fun default upd = the_process_default () |> update (get_thread_update ()) |> update upd;

fun default_typ name = typ (default []) name;
fun default_bool name = bool (default []) name;
fun default_int name = int (default []) name;
fun default_real name = real (default []) name;
fun default_seconds name = seconds (default []) name;
fun default_string name = string (default []) name;

fun get_default name =
  let val options = default [] in get (typ options name) SOME options name end;

fun with_default_update upd f x =
  if null upd then f x
  else setmp_thread_update (get_thread_update () @ upd) f x;


(* Pure bootstrap *)

val _ = load_process_default ();
val _ = ML_Print_Depth.set_print_depth (default_int "ML_print_depth");

end;
