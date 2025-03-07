(*  Title:      Pure/General/path.ML
    Author:     Markus Wenzel, TU Muenchen

Algebra of file-system paths: basic POSIX notation, extended by named
roots (e.g. //foo) and variables (e.g. $BAR).
*)

signature PATH =
sig
  eqtype T
  val is_current: T -> bool
  val current: T
  val root: T
  val named_root: string -> T
  val parent: T
  val make: string list -> T
  val basic: string -> T
  val variable: string -> T
  val has_parent: T -> bool
  val is_absolute: T -> bool
  val is_basic: T -> bool
  val starts_basic: T -> bool
  val append: T -> T -> T
  val appends: T list -> T
  val implode: T -> string
  val explode: string -> T
  val explode_pos: string * Position.T -> T * Position.T
  val split: string -> T list
  val print_markup: T -> Markup.T * string
  val print: T -> string
  val dir: T -> T
  val base: T -> T
  val ext: string -> T -> T
  val platform_exe: T -> T
  val split_ext: T -> T * string
  val drop_ext: T -> T
  val get_ext: T -> string
  val is_xz: T -> bool
  val is_zst: T -> bool
  val expand: T -> T
  val file_name: T -> string
  eqtype binding
  val binding: T * Position.T -> binding
  val binding0: T -> binding
  val map_binding: (T -> T) -> binding -> binding
  val dest_binding: binding -> T * Position.T
  val path_of_binding: binding -> T
  val pos_of_binding: binding -> Position.T
  val proper_binding: binding -> unit
  val implode_binding: binding -> string
  val explode_binding: string * Position.T -> binding
  val explode_binding0: string -> binding
end;

structure Path: PATH =
struct

(* path elements *)

datatype elem =
  Root of string |
  Basic of string |
  Variable of string |
  Parent;

local

fun err_elem msg s = error (msg ^ " path element " ^ quote s);

val illegal_elem = ["", "~", "~~", ".", ".."];
val illegal_char = ["/", "\\", "$", ":", "\"", "'", "<", ">", "|", "?", "*"];

fun check_elem s =
  if member (op =) illegal_elem s then err_elem "Illegal" s
  else
    (s, ()) |-> fold_string (fn c => fn () =>
      if ord c < 32 then
        err_elem ("Illegal control character " ^ string_of_int (ord c) ^ " in") s
      else if member (op =) illegal_char c then
        err_elem ("Illegal character " ^ quote c ^ " in") s
      else ());

in

val root_elem = Root o tap check_elem;
val basic_elem = Basic o tap check_elem;
val variable_elem = Variable o tap check_elem;

end;


(* type path *)

datatype T = Path of elem list;    (*reversed elements*)

fun rep (Path xs) = xs;

fun is_current (Path []) = true
  | is_current _ = false;

val current = Path [];
val root = Path [Root ""];
fun named_root s = Path [root_elem s];
val make = Path o rev o map basic_elem;
fun basic s = Path [basic_elem s];
fun variable s = Path [variable_elem s];
val parent = Path [Parent];

fun has_parent (Path xs) = exists (fn Parent => true | _ => false) xs;

fun is_absolute (Path xs) =
  (case try List.last xs of
    SOME (Root _) => true
  | _ => false);

fun is_basic (Path [Basic _]) = true
  | is_basic _ = false;

fun all_basic (Path elems) =
  forall (fn Basic _ => true | _ => false) elems;

fun starts_basic (Path xs) =
  (case try List.last xs of
    SOME (Basic _) => true
  | _ => false);


(* append and norm *)

fun apply (y as Root _) _ = [y]
  | apply Parent (xs as (Root _ :: _)) = xs
  | apply Parent (Basic _ :: rest) = rest
  | apply y xs = y :: xs;

fun append (Path xs) (Path ys) = Path (fold_rev apply ys xs);
fun appends paths = Library.foldl (uncurry append) (current, paths);

fun norm elems = fold_rev apply elems [];


(* implode *)

local

fun implode_elem (Root "") = ""
  | implode_elem (Root s) = "//" ^ s
  | implode_elem (Basic s) = s
  | implode_elem (Variable s) = "$" ^ s
  | implode_elem Parent = "..";

in

fun implode_path (Path []) = "."
  | implode_path (Path [Root ""]) = "/"
  | implode_path (Path xs) = space_implode "/" (rev (map implode_elem xs));

end;


(* explode *)

fun explode_path str =
  let
    fun explode_elem s =
     (if s = ".." then Parent
      else if s = "~" then Variable "USER_HOME"
      else if s = "~~" then Variable "ISABELLE_HOME"
      else
        (case try (unprefix "$") s of
          SOME s' => variable_elem s'
        | NONE => basic_elem s))
      handle ERROR msg => cat_error msg ("The error(s) above occurred in " ^ quote str);

    val (roots, raw_elems) =
      (case chop_prefix (equal "") (space_explode "/" str) |>> length of
        (0, es) => ([], es)
      | (1, es) => ([Root ""], es)
      | (_, []) => ([Root ""], [])
      | (_, e :: es) => ([root_elem e], es));
    val elems = raw_elems |> filter_out (fn c => c = "" orelse c = ".") |> map explode_elem;

  in Path (norm (rev elems @ roots)) end;

fun explode_pos (s, pos) =
  (explode_path s handle ERROR msg => error (msg ^ Position.here pos), pos);

fun split str =
  space_explode ":" str
  |> map_filter (fn s => if s = "" then NONE else SOME (explode_path s));


(* print *)

fun print_markup path =
  let val s = implode_path path
  in (Markup.path s, quote s) end;

val print = print_markup #-> Markup.markup;


(* base element *)

fun split_path f (Path (Basic s :: xs)) = f (Path xs, s)
  | split_path _ path = error ("Cannot split path into dir/base: " ^ print path);

val dir = split_path #1;
val base = split_path (fn (_, s) => Path [Basic s]);

fun ext "" = I
  | ext e = split_path (fn (prfx, s) => append prfx (basic (s ^ "." ^ e)));

val platform_exe = ML_System.platform_is_windows ? ext "exe";

val split_ext = split_path (fn (prfx, s) => apfst (append prfx)
  (case chop_suffix (fn c => c <> ".") (raw_explode s) of
    ([], _) => (Path [Basic s], "")
  | (cs, e) => (Path [Basic (implode (take (length cs - 1) cs))], implode e)));

val drop_ext = #1 o split_ext;
val get_ext = #2 o split_ext;

fun is_xz path = get_ext path = "xz";
fun is_zst path = get_ext path = "zst";


(* expand variables *)

fun eval (Variable s) =
      let val path = explode_path (getenv_strict s) in
        if exists (fn Variable _ => true | _ => false) (rep path) then
          error ("Illegal path variable nesting: " ^ s ^ "=" ^ print path)
        else rep path
      end
  | eval x = [x];

val expand = rep #> maps eval #> norm #> Path;

val file_name = implode_path o base o expand;


(* binding: strictly monotonic path with position *)

datatype binding = Binding of T * Position.T;

fun binding (path, pos) =
  if all_basic path then Binding (path, pos)
  else error ("Bad path binding: " ^ print path ^ Position.here pos);

fun binding0 path = binding (path, Position.none);

fun map_binding f (Binding (path, pos)) = binding (f path, pos);

fun dest_binding (Binding args) = args;
val path_of_binding = dest_binding #> #1;
val pos_of_binding = dest_binding #> #2;

fun proper_binding binding =
  if is_current (path_of_binding binding)
  then error ("Empty path" ^ Position.here (pos_of_binding binding))
  else ();

val implode_binding = path_of_binding #> implode_path;

val explode_binding = binding o explode_pos;
fun explode_binding0 s = explode_binding (s, Position.none);


(*final declarations of this structure!*)
val implode = implode_path;
val explode = explode_path;

end;

ML_system_overload (uncurry Path.append) "+";
