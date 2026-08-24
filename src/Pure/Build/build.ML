(*  Title:      Pure/Build/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

signature BUILD =
sig
  val all_theories: unit -> string list
  val lookup_theory: string -> theory option
  val defined_theory: string -> bool
  val get_theory: string -> theory
  val get_theory_segments: string -> Document_Output.segment list
  val get_theory_elements: string -> Document_Output.segment Thy_Element.element list
  val check_theory: Proof.context -> string * Position.T -> theory
  type hook = string -> (theory * Document_Output.segment list) list -> unit
  val add_hook: hook -> unit
end;

structure Build: BUILD =
struct

(** persistent theories **)

(* messages *)

val show_path = space_implode " via " o map quote;

fun cycle_msg names = "Cyclic dependency of " ^ show_path names;


(* derived graph operations *)

fun add_deps name parents G = String_Graph.add_deps_acyclic (name, parents) G
  handle String_Graph.CYCLES namess => error (cat_lines (map cycle_msg namess));

fun new_entry name parents entry =
  String_Graph.new_node (name, entry) #> add_deps name parents;


(* global thys *)

local
  type thy = theory * Document_Output.segment list;
  val global_thys = Synchronized.var "Build.thys" (String_Graph.empty: thy String_Graph.T);
in
  fun get_thys () = Synchronized.value global_thys;
  fun change_thys f = Synchronized.change global_thys f;
end;

fun all_theories () = String_Graph.topological_order (get_thys ());


(* access thy *)

fun lookup thys name = try (String_Graph.get_node thys) name;
fun lookup_thy name = lookup (get_thys ()) name;

fun get thys name =
  (case lookup thys name of
    SOME thy => thy
  | NONE => error ("Theory loader: nothing known about theory " ^ quote name));

fun check_new thys name =
  if String_Graph.defined thys name
  then error ("Theory loader: cannot change loaded theory " ^ quote name)
  else ();

fun check_old thys (name, thy) =
  let val (thy', _) = get thys name in
    if Context.eq_thy (thy, thy') then ()
    else error ("Theory loader: incoherent theory " ^ quote name)
  end;


(* access theory *)

fun lookup_theory name = lookup_thy name |> Option.map #1;

val defined_theory = is_some o lookup_theory;

fun get_theory name =
  (case lookup_theory name of
    SOME theory => theory
  | _ => error ("Theory loader: undefined entry for theory " ^ quote name));

fun get_theory_segments name =
  let
    val segments =
      (case lookup_thy name of
        SOME (_, segments) => segments
      | _ => []);
  in
    if null segments then
      error ("Theory loader: no theory segments for theory " ^ quote name ^
        "\n Need to build with option " ^ quote \<^system_option>\<open>record_theories\<close>)
    else segments
  end;

fun get_theory_elements name =
  let
    val keywords = Thy_Header.get_keywords (get_theory name);
    val stopper = Document_Output.segment_stopper;
    val segments = get_theory_segments name;
  in Thy_Element.parse_elements_generic keywords #span stopper segments end;


val check_theory = Theory.check_theory {get = get_theory, all = all_theories};



(** thy operations **)

(* commit *)

fun commit_thy (res as (theory, _)) = change_thys (fn thys =>
  let
    val name = Context.theory_long_name theory;
    val _ = check_new thys name;
    val parents = map (`Context.theory_long_name) (Theory.parents_of theory);
    val _ = List.app (check_old thys) parents;
  in new_entry name (map #1 parents) res thys end);


(* scheduling loader tasks *)

datatype result =
  Result of
   {theory: theory,
    exec_id: Document_ID.exec,
    present: unit -> Thy_Presentation.context option,
    commit: Document_Output.segment list -> unit};

fun theory_result theory =
  Result
   {theory = theory,
    exec_id = Document_ID.none,
    present = K NONE,
    commit = K ()};

fun result_theory (Result {theory, ...}) = theory;
fun result_commit (Result {commit, ...}) = commit;

datatype task =
  Task of string list * (theory list -> result) |
  Finished of theory;

local

fun consolidate_theory (Exn.Exn exn) = [Exn.Exn exn]
  | consolidate_theory (Exn.Res (Result {theory, exec_id, ...})) =
      let
        val _ = Execution.join [exec_id];
        val result = Exn.capture Thm.consolidate_theory theory;
        val exns = maps Task_Queue.group_status (Execution.peek exec_id);
      in result :: map Exn.Exn exns end;

fun present_theory (Exn.Exn exn) = SOME (Exn.Exn exn)
  | present_theory (Exn.Res (Result {theory, present, ...})) =
      present () |> Option.map (fn context as {segments, ...} =>
        Exn.capture_body (fn () => (Thy_Presentation.apply_hooks context theory; (theory, segments))));

in

fun schedule_theories tasks =
  let
    fun join_parents deps name parents =
      (case map #1 (filter (not o can Future.join o #2) deps) of
        [] => map (result_theory o Future.join o the o AList.lookup (op =) deps) parents
      | bad =>
          error ("Failed to load theory " ^ quote name ^ " (unresolved " ^ commas_quote bad ^ ")"));

    val futures = tasks
      |> String_Graph.schedule (fn deps => fn (name, task) =>
        (case task of
          Task (parents, body) =>
            if Multithreading.max_threads () > 1 then
              (singleton o Future.forks)
                {name = "theory:" ^ name, group = NONE,
                  deps = map (Future.task_of o #2) deps, pri = 0, interrupts = true}
                (fn () => body (join_parents deps name parents))
            else
              Future.value_result (Exn.capture_body (fn () => body (join_parents deps name parents)))
        | Finished theory => Future.value (theory_result theory)));

    val results1 = futures |> maps (consolidate_theory o Future.join_result);

    val presented_results = futures |> map (present_theory o Future.join_result);
    val present_results = map_filter I presented_results;

    val results2 = (map o Exn.map_res) (K ()) present_results;

    val results3 = (futures, presented_results) |> ListPair.map (fn (future, presented) =>
      let val segments = (case presented of SOME (Exn.Res (_, segments)) => segments | _ => []);
      in Exn.capture_body (fn () => result_commit (Future.join future) segments) end);

    val results4 = map Exn.Exn (maps Task_Queue.group_status (Execution.reset ()));

    val _ = Par_Exn.release_all (results1 @ results2 @ results3 @ results4);
  in Par_Exn.release_all present_results end;

end;


(* eval theory *)

fun eval_thy loading_theory (thy: Resources.thy) text_pos text parents =
  let
    val options = Options.default [];

    val {master_dir, theory = name, ...} = #name thy;
    val keywords =
      fold (curry Keyword.merge_keywords o Thy_Header.get_keywords) parents
        (Keyword.add_keywords (#keywords thy) Keyword.empty_keywords);
    val command_kind = Keyword.command_kind keywords;

    val spans = Outer_Syntax.parse_spans command_kind (Token.explode keywords text_pos text);
    val commands =
      fold (fn span => fn i => if Command_Span.is_ignored span then i else i + 1) spans 0;
    val () = loading_theory commands;

    val elements = Thy_Element.parse_elements keywords spans;
    val command_ranges =
      Command_Span.command_ranges spans |> map (fn (pos, _) => (pos, Markup.command_range));

    val text_id = Position.copy_id text_pos Position.none;

    val bad_conditions = Thy_Header.bad_conditions options;
    fun init () =
     {skipped = not (null bad_conditions),
      theory = Resources.begin_theory thy parents};

    fun excursion () =
      let
        val _ = Thy_Header.skipping_theory Output.system_message name bad_conditions;
        val _ = Position.setmp_thread_data text_id (fn () => Position.reports command_ranges) ();

        fun element_result span_elem (st, _) =
          let
            fun prepare span =
              let
                val tr =
                  Position.setmp_thread_data text_id
                    (fn () => Command.read_span keywords st master_dir init span) ();
              in Toplevel.timing (Resources.last_timing tr) tr end;
            val elem = Thy_Element.map_element prepare span_elem;
            val (results, st') = Toplevel.element_result elem st;
            val pos' = Toplevel.pos_of (Thy_Element.last_element elem);
          in (results, (st', pos')) end;

        val (results, (end_state, end_pos)) =
          fold_map element_result elements (Toplevel.make_state NONE, Position.none);

        val thy = Toplevel.end_theory end_pos end_state;
      in (results, thy) end;

    val (results, thy) = cond_timeit true ("theory " ^ quote name) excursion;

    fun present () : Thy_Presentation.context =
      let
        val segments =
          (spans ~~ maps Toplevel.join_results results) |> map (fn (span, (st, tr, st')) =>
            {span = span, prev_state = st, command = tr, state = st'});
      in {options = options, file_pos = text_pos, adjust_pos = I, segments = segments} end;

  in (thy, present) end;


(* require_thy -- checking database entries wrt. the file-system *)

local

fun required_by _ [] = ""
  | required_by s initiators = s ^ "(required by " ^ show_path (rev initiators) ^ ")";

fun load_thy (thy0: Resources.thy) text parents =
  let
    val exec_id = Document_ID.make ();
    val id = Document_ID.print exec_id;
    val put_id = Position.put_id id;
    val _ =
      Execution.running Document_ID.none exec_id [] orelse
        raise Fail ("Failed to register execution: " ^ id);

    val thy = Resources.map_thy_pos put_id thy0;
    val name = #theory (#name thy);
    val thy_options = Options.update_no_pos (#options thy);

    val text_pos = put_id (Position.file (#node (#name thy)));
    val text_props = Position.properties_of text_pos;

    fun loading_theory commands =
      let
        val _ = writeln ("Loading theory " ^ quote name ^ required_by " " (#initiators thy));
        val _ =
          Output.try_protocol_message
            (Markup.loading_theory {name = name, commands = commands} @ text_props)
            [XML.blob [text]];
        val _ =
          Position.setmp_thread_data (Position.id_only id) (fn () =>
            (parents, map #2 (#imports thy)) |> ListPair.app (fn (thy, pos) =>
              Context_Position.reports_global thy [(pos, Theory.get_markup thy)])) ();
      in () end;

    val (theory, present) =
      Options.strict_thread_update thy_options (fn () =>
        eval_thy loading_theory thy text_pos text
          (if name = Context.PureN then [Context.the_global_context ()] else parents)) ();

    fun commit segments =
      let
        val options = Options.default thy_options;
        val record_theories = Options.bool options \<^system_option>\<open>record_theories\<close>;
      in commit_thy (theory, if record_theories then segments else []) end;
  in Result {theory = theory, exec_id = exec_id, present = SOME o present, commit = commit} end;

in

fun require_thys initiators qualifier dir imports tasks =
      fold (require_thy initiators qualifier dir) imports tasks
and require_thy initiators qualifier dir ((s, require_pos), theory_opts) tasks =
  let
    val {master_dir = theory_dir, theory_name, ...} = Resources.import_name qualifier dir s;
  in
    if String_Graph.defined tasks theory_name then tasks
    else
      (member (op =) initiators theory_name andalso error (cycle_msg initiators);
       case lookup_theory theory_name of
        SOME theory => new_entry theory_name [] (Finished theory) tasks
      | NONE =>
          let
            val {thy_path, text, theory_pos, imports, options = header_options, keywords} =
              Resources.check_thy theory_dir theory_name handle ERROR msg =>
                cat_error msg
                  ("The error(s) above occurred for theory " ^ quote theory_name ^
                    Position.here require_pos ^ required_by "\n" initiators);

            val qualifier' = Resources.theory_qualifier theory_name;
            val dir' = dir + Path.dir thy_path;
            val imports' = map (rpair theory_opts) imports;

            val parents = map (#theory_name o Resources.import_name qualifier' dir' o #1) imports;
            val tasks' = require_thys (theory_name :: initiators) qualifier' dir' imports' tasks;

            val node = File.symbolic_path thy_path;
            val master_dir = Path.dir (Path.explode node);
            val opts = header_options @ Options.update_pos_none theory_opts;
            val thy: Resources.thy =
             {name = {node = node, master_dir = master_dir, theory = theory_name},
              pos = theory_pos, imports = imports, options = opts, keywords = keywords,
              initiators = initiators};
          in new_entry theory_name parents (Task (parents, load_thy thy text)) tasks' end)
  end;

end;


(* use theories *)

fun use_theories qualifier imports =
  schedule_theories (require_thys [] qualifier Path.current imports String_Graph.empty);



(** build **)

(* session timing *)

fun session_timing f x =
  let
    val start = Timing.start ();
    val y = f x;
    val timing = Timing.result start;

    val threads = string_of_int (Multithreading.max_threads ());
    val props = [("threads", threads)] @ Markup.timing_properties timing;
    val _ = Output.protocol_message (Markup.session_timing :: props) [];
  in y end;


(* build theories *)

type hook = string -> (theory * Document_Output.segment list) list -> unit;

local
  val hooks = Synchronized.var "Build.hooks" ([]: hook list);
in

fun add_hook hook = Synchronized.change hooks (cons hook);

fun apply_hooks qualifier loaded_theories =
  Synchronized.value hooks
  |> List.app (fn hook => hook qualifier loaded_theories);

end;


fun build_theories qualifier (options, thys) =
  let
    val _ = ML_Profiling.check_mode (Options.string options "profiling");
    val print_mode = space_explode "," (Options.string options "print_mode") @ print_mode_value ();
    val _ = Options.set_process_default (SOME options);
    val _ = Isabelle_Process.init_options ();
    val _ = Future.fork I;
  in
    (use_theories qualifier
      |> Unsynchronized.setmp Print_Mode.print_mode print_mode) thys
  end;

fun finish_session () =
 (Session.shutdown ();
  Par_List.map (Global_Theory.get_thm_names o get_theory) (all_theories ());
  Session.shutdown ();
  ignore (Context.finish_tracing ()));



(* build session *)

val _ =
  Protocol_Command.define_bytes "build_session"
    (fn session_name_bytes :: resources_yxml :: theories_yxml =>
        let
          val session_name = Bytes.content session_name_bytes;
          val _ = Resources.init_session_yxml resources_yxml;
          val theories = theories_yxml |> map (YXML.parse_body_bytes #>
              let
                open XML.Decode;
                val position = Position.of_properties o properties;
                val theory = pair (pair string position) (list (pair string (option string)));
              in pair Options.decode (list theory) end);

          val _ = Session.init session_name;

          fun build () =
            let
              val res =
                theories |>
                  (maps (build_theories session_name)
                    |> session_timing
                    |> Exn.capture);
              val res1 =
                (case res of
                  Exn.Res loaded_theories =>
                    Exn.capture (apply_hooks session_name) loaded_theories
                | Exn.Exn exn => Exn.Exn exn);
              val res2 = Exn.capture_body finish_session;

              val _ = Resources.finish_session_base ();
              val _ = Par_Exn.release_all [res1, res2];
              val _ =
                if session_name = Context.PureN
                then Theory.install_pure (get_theory Context.PureN) else ();
            in () end;

          fun exec e =
            if can Theory.get_pure () then
              Isabelle_Thread.fork (Isabelle_Thread.params "build_session") e
              |> ignore
            else e ();
        in
          exec (fn () =>
            (case Exn.capture_body (Future.interruptible_task build) of
              Exn.Res () => (0, [])
            | Exn.Exn exn =>
                (case Exn.capture Runtime.exn_message_list exn of
                  Exn.Res errs => (1, errs)
                | Exn.Exn _ (*sic!*) => (2, ["CRASHED"])))
          |> let open XML.Encode in pair int (list string) end
          |> single
          |> Output.protocol_message Markup.build_session_finished)
        end
      | _ => raise Match);

end;
