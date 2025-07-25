(*  Title:      HOL/Tools/Mirabelle/mirabelle.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Makarius
    Author:     Martin Desharnais, UniBw Munich
*)

signature MIRABELLE =
sig
  (*core*)
  type action_context =
    {index: int, label: string, name: string, arguments: Properties.T, timeout: Time.time,
     output_dir: Path.T}
  type command =
    {theory_index: int, name: string, pos: Position.T, pre: Proof.state, post: Toplevel.state}
  type action = {run: command -> string, finalize: unit -> string}
  val register_action: string -> (action_context -> string * action) -> unit

  (*utility functions*)
  val print_exn: exn -> string
  val can_apply : Time.time -> (Proof.context -> int -> tactic) ->
    Proof.state -> bool
  val theorems_in_proof_term : theory -> thm -> thm list
  val theorems_of_sucessful_proof: Toplevel.state -> thm list
  val get_argument : (string * string) list -> string * string -> string
  val get_int_argument : (string * string) list -> string * int -> int
  val get_bool_argument : (string * string) list -> string * bool -> bool
  val cpu_time : ('a -> 'b) -> 'a -> 'b * int
end

structure Mirabelle : MIRABELLE =
struct

(** Mirabelle core **)

(* concrete syntax *)

fun read_actions str =
  let
    val thy = \<^theory>;
    val ctxt = Proof_Context.init_global thy
    val keywords = Keyword.no_major_keywords (Thy_Header.get_keywords thy)

    fun read_actions () = Parse.read_embedded ctxt keywords
      (Parse.enum ";" (Parse.name -- Sledgehammer_Commands.parse_params))
      (Input.string str)
    fun split_name_label (name, args) labels =
        (case String.tokens (fn c => c = #".") name of
          [name] => (("", name, args), labels)
        | [label, name] =>
          (if Symset.member labels label then
             error ("Action label '" ^ label ^ "' already defined.")
           else
             ();
           ((label, name, args), Symset.insert label labels))
        | _ => error "Cannot parse action")
  in
    try read_actions ()
    |> Option.map (fn xs => fst (fold_map split_name_label xs Symset.empty))
  end


(* actions *)

type command =
  {theory_index: int, name: string, pos: Position.T, pre: Proof.state, post: Toplevel.state};
type action_context =
  {index: int, label: string, name: string, arguments: Properties.T, timeout: Time.time,
   output_dir: Path.T};
type action = {run: command -> string, finalize: unit -> string};

val dry_run_action : action = {run = K "", finalize = K ""}

local
  val actions = Synchronized.var "Mirabelle.actions"
    (Symtab.empty : (action_context -> string * action) Symtab.table);
in

fun register_action name make_action =
  (if name = "" then error "Registering unnamed Mirabelle action" else ();
   Synchronized.change actions (Symtab.map_default (name, make_action)
     (fn f => (warning ("Redefining Mirabelle action: " ^ quote name); f))));

fun get_action name = Symtab.lookup (Synchronized.value actions) name;

end


(* apply actions *)

fun print_exn exn =
  (case exn of
    Timeout.TIMEOUT _ => "timeout"
  | ERROR msg => "error: " ^ msg
  | exn => "exception: " ^ General.exnMessage exn);

fun run_action_function f =
  \<^try>\<open>f () catch exn => print_exn exn\<close>;

fun make_action_path ({index, label, name, ...} : action_context) =
  Path.basic (if label = "" then string_of_int index ^ "." ^ name else label);

fun initialize_action (make_action : action_context -> string * action) context =
  let
    val (s, action) = make_action context
    val action_path = make_action_path context;
    val export_name =
      Path.binding0 (Path.basic "mirabelle" + action_path + Path.basic "initialize");
    val () =
      if s <> "" then
        Export.export \<^theory> export_name [XML.Text s]
      else
        ()
  in
    action
  end

fun finalize_action ({finalize, ...} : action) context =
  let
    val s = run_action_function finalize;
    val action_path = make_action_path context;
    val export_name =
      Path.binding0 (Path.basic "mirabelle" + action_path + Path.basic "finalize");
  in
    if s <> "" then
      Export.export \<^theory> export_name [XML.Text s]
    else
      ()
  end

fun apply_action ({run, ...} : action) context (command as {pos, pre, ...} : command) =
  let
    val action_path = make_action_path context
    and goal_name_path = Path.basic (#name command)
    and line_path = Path.basic (string_of_int (the (Position.line_of pos)))
    and offset_path = Path.basic (string_of_int (the (Position.offset_of pos)))
    and ({elapsed, ...}, s) = Timing.timing run_action_function (fn () => run command);
    val export_name =
      Path.binding0 (Path.basic "mirabelle" + action_path + Path.basic "goal" + goal_name_path +
        line_path + offset_path + Path.basic (string_of_int (Time.toMilliseconds elapsed)));
  in
    Export.export (Proof.theory_of pre) export_name [XML.Text s]
  end;


(* theory line range *)

local

val theory_name =
  Scan.many1 (Symbol_Pos.symbol #> (fn s => Symbol.not_eof s andalso s <> "["))
    >> Symbol_Pos.content;

val line = Symbol_Pos.scan_nat >> (Symbol_Pos.content #> Value.parse_nat);
val end_line = Symbol_Pos.$$ ":" |-- line;
val range = Symbol_Pos.$$ "[" |-- line -- Scan.option end_line --| Symbol_Pos.$$ "]";

in

fun read_theory_range str =
  (case Scan.read Symbol_Pos.stopper (theory_name -- Scan.option range) (Symbol_Pos.explode0 str) of
    SOME res => res
  | NONE => error ("Malformed specification of theory line range: " ^ quote str));

end;

fun check_theories strs =
  let
    fun theory_import_name s =
      #theory_name (Resources.import_name (Session.get_name ()) Path.current s);
    val theories = map read_theory_range strs
      |> map (apfst theory_import_name);
    fun get_theory name =
      if null theories then SOME NONE
      else get_first (fn (a, b) => if a = name then SOME b else NONE) theories;
    fun check_line NONE _ = false
      | check_line _ NONE = true
      | check_line (SOME NONE) _ = true
      | check_line (SOME (SOME (line, NONE))) (SOME i) = line <= i
      | check_line (SOME (SOME (line, SOME end_line))) (SOME i) = line <= i andalso i <= end_line;
    fun check_pos range = check_line range o Position.line_of;
  in check_pos o get_theory end;


(* presentation hook *)

val _ =
  Build.add_hook (fn qualifier => fn loaded_theories =>
    let
      val mirabelle_actions = Options.default_string \<^system_option>\<open>mirabelle_actions\<close>;
      val actions =
        (case read_actions mirabelle_actions of
          SOME actions => actions
        | NONE => error ("Failed to parse mirabelle_actions: " ^ quote mirabelle_actions));
    in
      if null actions then
        ()
      else
        let
          val mirabelle_dry_run = Options.default_bool \<^system_option>\<open>mirabelle_dry_run\<close>;
          val mirabelle_timeout = Options.default_seconds \<^system_option>\<open>mirabelle_timeout\<close>;
          val mirabelle_stride = Options.default_int \<^system_option>\<open>mirabelle_stride\<close>;
          val mirabelle_max_calls = Options.default_int \<^system_option>\<open>mirabelle_max_calls\<close>;
          val mirabelle_randomize = Options.default_int \<^system_option>\<open>mirabelle_randomize\<close>;
          val mirabelle_theories = Options.default_string \<^system_option>\<open>mirabelle_theories\<close>;
          val mirabelle_output_dir = Options.default_string \<^system_option>\<open>mirabelle_output_dir\<close>;
          val mirabelle_parallel_group_size = Options.default_int \<^system_option>\<open>mirabelle_parallel_group_size\<close>;
          val check_theory = check_theories (space_explode "," mirabelle_theories);
          val mirabelle_subgoals = Options.default_string \<^system_option>\<open>mirabelle_subgoals\<close>;
          val considered_subgoals = space_explode "," mirabelle_subgoals;

          fun parallel_app (f : 'a -> unit) (xs : 'a list) : unit =
            chop_groups mirabelle_parallel_group_size xs
            |> List.app (ignore o Par_List.map f)

          fun make_commands (thy_index, (thy, segments)) =
            let
              val thy_long_name = Context.theory_long_name thy;
              val check_thy = check_theory thy_long_name;
              fun make_command {command = tr, prev_state = st, state = st', ...} =
                let
                  val name = Toplevel.name_of tr;
                  val pos = Toplevel.pos_of tr;
                in
                  if Context.proper_subthy (\<^theory>, thy) andalso
                    can (Proof.assert_backward o Toplevel.proof_of) st andalso
                    member (op =) considered_subgoals name andalso check_thy pos
                  then SOME {theory_index = thy_index, name = name, pos = pos,
                    pre = Toplevel.proof_of st, post = st'}
                  else NONE
                end;
            in
              if Resources.theory_qualifier thy_long_name = qualifier then
                map_filter make_command segments
              else
                []
            end;

          (* initialize actions *)
          val contexts = actions |> map_index (fn (n, (label, name, args)) =>
            let
              val make_action =
                (case get_action name of
                  SOME f => f
                | NONE => error "Unknown action");
              val action_subdir = if label = "" then string_of_int n ^ "." ^ name else label;
              val output_dir =
                Path.append (Path.explode mirabelle_output_dir) (Path.basic action_subdir);
              val context =
                {index = n, label = label, name = name, arguments = args,
                 timeout = mirabelle_timeout, output_dir = output_dir};
            in
              (initialize_action make_action context, context)
            end);
        in
          (* run actions on all relevant goals *)
          loaded_theories
          |> map_index I
          |> maps make_commands
          |> (if mirabelle_randomize <= 0 then
                I
              else
                fst o MLCG.shuffle (MLCG.initialize mirabelle_randomize))
          |> (fn xs => fold_map (fn x => fn i => ((i, x), i + 1)) xs 0)
          |> (fn (indexed_commands, commands_length) =>
            let
              val stride =
                if mirabelle_stride <= 0 then
                  Integer.max 1 (commands_length div mirabelle_max_calls)
                else
                  mirabelle_stride
            in
              maps (fn (n, command) =>
              let val (m, k) = Integer.div_mod (n + 1) stride in
                if k = 0 andalso (mirabelle_max_calls <= 0 orelse m <= mirabelle_max_calls) then
                  map (fn context => (context, command)) contexts
                else
                  []
              end) indexed_commands
            end)
          (* Don't use multithreading for a dry run because of the high per-thread overhead. *)
          |> (if mirabelle_dry_run then List.app else parallel_app) (fn ((action, context), command) =>
              apply_action (if mirabelle_dry_run then dry_run_action else action) context command);

          (* finalize actions *)
          List.app (uncurry finalize_action) contexts
        end
    end);


(* Mirabelle utility functions *)

fun can_apply time tac st =
  let
    val {context = ctxt, facts, goal} = Proof.goal st;
    val full_tac = HEADGOAL (Method.insert_tac ctxt facts THEN' tac ctxt);
  in
    (case try (Timeout.apply time (Seq.pull o full_tac)) goal of
      SOME (SOME _) => true
    | _ => false)
  end;

local

fun fold_body_thms f =
  let
    fun app n (PBody {thms, ...}) = thms |> fold (fn (i, thm_node) =>
      fn (x, seen) =>
        if Inttab.defined seen i then (x, seen)
        else
          let
            val name = Proofterm.thm_node_name thm_node;
            val prop = Proofterm.thm_node_prop thm_node;
            val body = Future.join (Proofterm.thm_node_body thm_node);
            val (x', seen') =
              app (n + (if Thm_Name.is_empty name then 0 else 1)) body
                (x, Inttab.update (i, ()) seen);
        in (x' |> n = 0 ? f (name, prop, body), seen') end);
  in fn bodies => fn x => #1 (fold (app 0) bodies (x, Inttab.empty)) end;

in

fun theorems_in_proof_term thy thm =
  let
    val all_thms = Global_Theory.all_thms_of thy true;
    fun collect (name, _, _) = if Thm_Name.is_empty name then I else insert (op =) name;
    fun member_of xs (x, y) = if member (op =) xs x then SOME y else NONE;
    fun resolve_thms names = map_filter (member_of names) all_thms;
  in resolve_thms (fold_body_thms collect [Thm.proof_body_of thm] []) end;

end;

fun theorems_of_sucessful_proof st =
  (case try Toplevel.proof_of st of
    NONE => []
  | SOME prf => theorems_in_proof_term (Proof.theory_of prf) (#goal (Proof.goal prf)));

fun get_argument arguments (key, default) =
  the_default default (AList.lookup (op =) arguments key);

fun get_int_argument arguments (key, default) =
  (case Option.map Int.fromString (AList.lookup (op =) arguments key) of
    SOME (SOME i) => i
  | SOME NONE => error ("bad option: " ^ key)
  | NONE => default);

fun get_bool_argument arguments (key, default) =
  (case Option.map Bool.fromString (AList.lookup (op =) arguments key) of
    SOME (SOME i) => i
  | SOME NONE => error ("bad option: " ^ key)
  | NONE => default);

fun cpu_time f x =
  (* CPU time is problematics with multithreading as it refers to the per-process CPU time. *)
  let val ({elapsed, ...}, y) = Timing.timing f x
  in (y, Time.toMilliseconds elapsed) end;

end
