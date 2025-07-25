(*  Title:      Pure/PIDE/command.ML
    Author:     Makarius

Prover command execution: read -- eval -- print.
*)

signature COMMAND =
sig
  type blob = {file_node: string, src_path: Path.T, content: (SHA1.digest * string list) option}
  val read_thy: Toplevel.state -> theory
  val read: Keyword.keywords -> theory -> Path.T-> (unit -> theory) ->
    blob Exn.result list * int -> Token.T list -> Toplevel.transition
  val read_span: Keyword.keywords -> Toplevel.state -> Path.T -> (unit -> theory) ->
    Command_Span.span -> Toplevel.transition
  type eval
  val eval_command_id: eval -> Document_ID.command
  val eval_exec_id: eval -> Document_ID.exec
  val eval_eq: eval * eval -> bool
  val eval_running: eval -> bool
  val eval_finished: eval -> bool
  val eval_result_command: eval -> Toplevel.transition
  val eval_result_state: eval -> Toplevel.state
  val eval: Keyword.keywords -> Path.T -> (unit -> theory) ->
    blob Exn.result list * int -> Document_ID.command -> Token.T list -> eval -> eval
  type print
  type print_fn = Toplevel.transition -> Toplevel.state -> unit
  val print0: {pri: int, print_fn: print_fn} -> eval -> print
  val print: Keyword.keywords -> bool -> (string * string list) list -> string ->
    eval -> print list -> print list option
  val parallel_print: print -> bool
  type print_function =
    {keywords: Keyword.keywords, command_name: string, args: string list, exec_id: Document_ID.exec} ->
      {delay: Time.time option, pri: int, persistent: bool, strict: bool, print_fn: print_fn} option
  val print_function: string -> print_function -> unit
  val no_print_function: string -> unit
  type exec = eval * print list
  val init_exec: theory option -> exec
  val no_exec: exec
  val exec_ids: exec option -> Document_ID.exec list
  val exec: Document_ID.execution -> exec -> unit
  val exec_parallel_prints: Document_ID.execution -> Future.task list -> exec -> exec option
end;

structure Command: COMMAND =
struct

(** main phases of execution **)

fun task_context group f =
  f
  |> Future.interruptible_task
  |> Future.task_context "Command.run_process" group;


(* read *)

type blob = {file_node: string, src_path: Path.T, content: (SHA1.digest * string list) option};

local

fun blob_file src_path lines digest file_node =
  let
    val file_pos =
      Position.file file_node |>
      (case Position.id_of (Position.thread_data ()) of
        NONE => I
      | SOME exec_id => Position.put_id exec_id);
  in {src_path = src_path, lines = lines, digest = digest, pos = file_pos} end

fun resolve_files master_dir (blobs, blobs_index) toks =
  (case Outer_Syntax.parse_spans toks of
    [Command_Span.Span (Command_Span.Command_Span _, _)] =>
      (case try (nth toks) blobs_index of
        SOME tok =>
          let
            val source = Token.input_of tok;
            val pos = Input.pos_of source;
            val delimited = Input.is_delimited source;

            fun make_file (Exn.Res {file_node, src_path, content}) =
                  let val _ = Position.report pos (Markup.language_path delimited) in
                    case content of
                      NONE =>
                        Exn.result (fn () =>
                          Resources.read_file_node file_node master_dir (src_path, pos)) ()
                    | SOME (digest, lines) => Exn.Res (blob_file src_path lines digest file_node)
                  end
              | make_file (Exn.Exn e) = Exn.Exn e;
            val files = map make_file blobs;
          in
            toks |> map_index (fn (i, tok) =>
              if i = blobs_index then Token.put_files files tok else tok)
          end
      | NONE => toks)
  | _ => toks);

fun reports_of_token keywords tok =
  let
    val malformed_symbols =
      Input.source_explode (Token.input_of tok)
      |> map_filter (fn (sym, pos) =>
          if Symbol.is_malformed sym
          then SOME ((pos, Markup.bad ()), "Malformed symbolic character") else NONE);
    val is_malformed = Token.is_error tok orelse not (null malformed_symbols);
    val reports = Token.reports keywords tok @ Token.completion_report tok @ malformed_symbols;
  in (is_malformed, reports) end;

in

fun read_thy st = Toplevel.theory_of st
  handle Toplevel.UNDEF => Pure_Syn.bootstrap_thy;

fun read keywords thy master_dir init blobs_info span =
  let
    val command_reports = Outer_Syntax.command_reports thy;
    val token_reports = map (reports_of_token keywords) span;
    val _ = Position.reports_text (maps #2 token_reports @ maps command_reports span);

    val core_range = Token.core_range_of span;
    val tr =
      if exists #1 token_reports
      then Toplevel.malformed (#1 core_range) "Malformed command syntax"
      else Outer_Syntax.parse_span thy init (resolve_files master_dir blobs_info span);
    val _ =
      if Toplevel.is_ignored tr orelse Toplevel.is_malformed tr then ()
      else
        let
          val name = Toplevel.name_of tr;
          val kind = the_default "" (Keyword.command_kind (Thy_Header.get_keywords thy) name);
          val markup = Markup.command_span {name = name, kind = kind};
        in Position.report (#1 core_range) markup end;
  in tr end;

end;

fun read_span keywords st master_dir init =
  Command_Span.content #> read keywords (read_thy st) master_dir init ([], ~1);


(* eval *)

type eval_state = {failed: bool, command: Toplevel.transition, state: Toplevel.state};

fun init_eval_state opt_thy =
 {failed = false,
  command = Toplevel.empty,
  state = Toplevel.make_state opt_thy};

datatype eval =
  Eval of
    {command_id: Document_ID.command, exec_id: Document_ID.exec, eval_process: eval_state lazy};

fun eval_command_id (Eval {command_id, ...}) = command_id;

fun eval_exec_id (Eval {exec_id, ...}) = exec_id;
val eval_eq = op = o apply2 eval_exec_id;

val eval_running = Execution.is_running_exec o eval_exec_id;
fun eval_finished (Eval {eval_process, ...}) = Lazy.is_finished eval_process;

fun eval_result (Eval {eval_process, ...}) =
  Exn.release (Lazy.finished_result eval_process);

val eval_result_command = #command o eval_result;
val eval_result_state = #state o eval_result;

local

fun reset_state keywords tr st0 = Toplevel.setmp_thread_position tr (fn () =>
  let
    val name = Toplevel.name_of tr;
    val res =
      if Keyword.is_theory_body keywords name then Toplevel.reset_theory st0
      else if Keyword.is_proof keywords name then Toplevel.reset_proof st0
      else if Keyword.is_theory_end keywords name then
        (case Toplevel.reset_notepad st0 of
          NONE => Toplevel.reset_theory st0
        | some => some)
      else NONE;
  in
    (case res of
      NONE => st0
    | SOME st => (Output.error_message (Toplevel.type_error tr ^ " -- using reset state"); st))
  end) ();

fun run keywords int tr st =
  if Future.proofs_enabled 1 andalso Keyword.is_diag keywords (Toplevel.name_of tr) then
    let
      val (tr1, tr2) = Toplevel.fork_presentation tr;
      val _ =
        Execution.fork {name = "Toplevel.diag", pos = Toplevel.pos_of tr, pri = ~1}
          (fn () => Toplevel.command_exception int tr1 st);
    in Toplevel.command_errors int tr2 st end
  else Toplevel.command_errors int tr st;

fun check_comments ctxt =
  Document_Output.check_comments ctxt o Input.source_explode o Token.input_of;

fun check_token_comments ctxt tok =
  (case Exn.result (fn () => check_comments ctxt tok) () of
    Exn.Res () => []
  | Exn.Exn exn => Runtime.exn_messages exn);

fun check_span_comments ctxt span tr =
  Toplevel.setmp_thread_position tr (fn () => maps (check_token_comments ctxt) span) ();

fun report_indent tr st =
  (case try Toplevel.proof_of st of
    SOME prf =>
      let val keywords = Thy_Header.get_keywords (Proof.theory_of prf) in
        if Keyword.command_kind keywords (Toplevel.name_of tr) = SOME Keyword.prf_script then
          (case try (Thm.nprems_of o #goal o Proof.goal) prf of
            NONE => ()
          | SOME 0 => ()
          | SOME n =>
              let val report = YXML.output_markup_only (Markup.command_indent (n - 1));
              in Toplevel.setmp_thread_position tr (fn () => Output.report [report]) () end)
        else ()
      end
  | NONE => ());

fun status tr m =
  Toplevel.setmp_thread_position tr (fn () => Output.status [YXML.output_markup_only m]) ();

fun eval_state keywords span tr ({state, ...}: eval_state) =
  let
    val _ = Isabelle_Thread.expose_interrupt ();

    val st = reset_state keywords tr state;

    val _ = report_indent tr st;
    val _ = status tr Markup.running;
    val (errs1, result) = run keywords true tr st;
    val errs2 =
      (case result of
        NONE => []
      | SOME st' => check_span_comments (Toplevel.presentation_context st') span tr);
    val errs = errs1 @ errs2;
    val _ = List.app (Future.error_message (Toplevel.pos_of tr)) errs;
  in
    (case result of
      NONE =>
        let
          val _ = status tr Markup.failed;
          val _ = status tr Markup.finished;
          val _ =
            if null errs then (status tr Markup.canceled; Isabelle_Thread.raise_interrupt ())
            else ();
        in {failed = true, command = tr, state = st} end
    | SOME st' =>
        let
          val _ =
            if Keyword.is_theory_end keywords (Toplevel.name_of tr) andalso
              can (Toplevel.end_theory Position.none) st'
            then status tr Markup.finalized else ();
          val _ = status tr Markup.finished;
        in {failed = false, command = tr, state = st'} end)
  end;

in

fun eval keywords master_dir init blobs_info command_id span eval0 =
  let
    val exec_id = Document_ID.make ();
    fun process () =
      let
        val eval_state0 = eval_result eval0;
        val thy = read_thy (#state eval_state0);
        val tr =
          Position.setmp_thread_data (Position.id_only (Document_ID.print exec_id))
            (fn () =>
              read keywords thy master_dir init blobs_info span |> Toplevel.exec_id exec_id) ();
      in eval_state keywords span tr eval_state0 end;
  in
    Eval {command_id = command_id, exec_id = exec_id,
      eval_process = Lazy.lazy_name "Command.eval" process}
  end;

end;


(* print *)

datatype print = Print of
 {name: string, args: string list, delay: Time.time option, pri: int, persistent: bool,
  exec_id: Document_ID.exec, print_process: unit lazy};

fun print_exec_id (Print {exec_id, ...}) = exec_id;
val print_eq = op = o apply2 print_exec_id;
fun print_equiv (name', args') (Print {name, args, ...}) = name' = name andalso args' = args;

type print_fn = Toplevel.transition -> Toplevel.state -> unit;

type print_function =
  {keywords: Keyword.keywords, command_name: string, args: string list, exec_id: Document_ID.exec} ->
    {delay: Time.time option, pri: int, persistent: bool, strict: bool, print_fn: print_fn} option;

local

val print_functions =
  Synchronized.var "Command.print_functions" ([]: (string * print_function) list);

fun print_wrapper tr opt_context =
  Toplevel.setmp_thread_position tr o Runtime.controlled_execution opt_context;

fun print_error tr opt_context e =
  (case Exn.result (fn () => print_wrapper tr opt_context e ()) () of
    Exn.Res res => res
  | Exn.Exn exn => List.app (Future.error_message (Toplevel.pos_of tr)) (Runtime.exn_messages exn));

fun print_finished (Print {print_process, ...}) = Lazy.is_finished print_process;

fun print_persistent (Print {persistent, ...}) = persistent;

val overlay_ord = prod_ord string_ord (list_ord string_ord);

fun make_print (name, args) {delay, pri, persistent, strict, print_fn} eval =
  let
    val exec_id = Document_ID.make ();
    fun process () =
      let
        val {failed, command, state = st', ...} = eval_result eval;
        val tr = Toplevel.exec_id exec_id command;
        val opt_context = try Toplevel.generic_theory_of st';
      in
        if failed andalso strict then ()
        else print_error tr opt_context (fn () => print_fn tr st')
      end;
  in
    Print {
      name = name, args = args, delay = delay, pri = pri, persistent = persistent,
      exec_id = exec_id, print_process = Lazy.lazy_name "Command.print" process}
  end;

fun bad_print name_args exn =
  make_print name_args {delay = NONE, pri = 0, persistent = false,
    strict = false, print_fn = fn _ => fn _ => Exn.reraise exn};

in

fun print0 {pri, print_fn} =
  make_print ("", [serial_string ()])
    {delay = NONE, pri = pri, persistent = true, strict = true, print_fn = print_fn};

fun print keywords visible overlays command_name eval old_prints =
  let
    val print_functions = Synchronized.value print_functions;

    fun new_print (name, args) get_pr =
      let
        val params =
         {keywords = keywords,
          command_name = command_name,
          args = args,
          exec_id = eval_exec_id eval};
      in
        (case Exn.capture (Runtime.controlled_execution NONE get_pr) params of
          Exn.Res NONE => NONE
        | Exn.Res (SOME pr) => SOME (make_print (name, args) pr eval)
        | Exn.Exn exn => SOME (bad_print (name, args) exn eval))
      end;

    fun get_print (name, args) =
      (case find_first (print_equiv (name, args)) old_prints of
        NONE =>
          (case AList.lookup (op =) print_functions name of
            NONE =>
              SOME (bad_print (name, args) (ERROR ("Missing print function " ^ quote name)) eval)
          | SOME get_pr => new_print (name, args) get_pr)
      | some => some);

    val retained_prints =
      filter (fn print => print_finished print andalso print_persistent print) old_prints;
    val visible_prints =
      if visible then
        fold (fn (name, _) => cons (name, [])) print_functions overlays
        |> sort_distinct overlay_ord
        |> map_filter get_print
      else [];
    val new_prints = visible_prints @ retained_prints;
  in
    if eq_list print_eq (old_prints, new_prints) then NONE else SOME new_prints
  end;

fun parallel_print (Print {pri, ...}) =
  pri <= 0 orelse (Future.enabled () andalso Options.default_bool \<^system_option>\<open>parallel_print\<close>);

fun print_function name f =
  Synchronized.change print_functions (fn funs =>
   (if name = "" then error "Unnamed print function"
    else if AList.defined (op =) funs name then
      warning ("Redefining command print function: " ^ quote name)
    else ();
    AList.update (op =) (name, f) funs));

fun no_print_function name =
  Synchronized.change print_functions (filter_out (equal name o #1));

end;


(* combined execution *)

type exec = eval * print list;

fun init_exec opt_thy : exec =
  (Eval
    {command_id = Document_ID.none, exec_id = Document_ID.none,
      eval_process = Lazy.value (init_eval_state opt_thy)}, []);

val no_exec = init_exec NONE;

fun exec_ids NONE = []
  | exec_ids (SOME (eval, prints)) = eval_exec_id eval :: map print_exec_id prints;

local

fun run_process execution_id exec_id process =
  let val group = Future.worker_subgroup () in
    if Execution.running execution_id exec_id [group] then
      ignore (task_context group (fn () => Lazy.force_result {strict = true} process) ())
    else ()
  end;

fun ignore_process process =
  Lazy.is_running process orelse Lazy.is_finished process;

fun run_eval execution_id (Eval {exec_id, eval_process, ...}) =
  if Lazy.is_finished eval_process then ()
  else run_process execution_id exec_id eval_process;

fun fork_print execution_id deps (Print {name, delay, pri, exec_id, print_process, ...}) =
  let
    val group = Future.worker_subgroup ();
    fun fork () =
      ignore ((singleton o Future.forks)
        {name = name, group = SOME group, deps = deps, pri = pri, interrupts = true}
        (fn () =>
          if ignore_process print_process then ()
          else run_process execution_id exec_id print_process));
  in
    (case delay of
      NONE => fork ()
    | SOME d => ignore (Event_Timer.request {physical = true} (Time.now () + d) fork))
  end;

fun run_print execution_id (print as Print {exec_id, print_process, ...}) =
  if ignore_process print_process then ()
  else if parallel_print print then fork_print execution_id [] print
  else run_process execution_id exec_id print_process;

in

fun exec execution_id (eval, prints) =
  (run_eval execution_id eval; List.app (run_print execution_id) prints);

fun exec_parallel_prints execution_id deps (exec as (Eval {eval_process, ...}, prints)) =
  if Lazy.is_finished eval_process
  then (List.app (fork_print execution_id deps) prints; NONE)
  else SOME exec;

end;

end;


(* common print functions *)

val _ =
  Command.print_function "Execution.print"
    (fn {args, exec_id, ...} =>
      if null args then
        SOME {delay = NONE, pri = Task_Queue.urgent_pri + 2, persistent = false, strict = false,
          print_fn = fn _ => fn _ => Execution.fork_prints exec_id}
      else NONE);

val _ =
  Command.print_function "print_state"
    (fn {keywords, command_name, ...} =>
      if Options.default_bool \<^system_option>\<open>editor_output_state\<close>
        andalso Keyword.is_printed keywords command_name
      then
        SOME {delay = NONE, pri = Task_Queue.urgent_pri + 1, persistent = false, strict = false,
          print_fn = fn _ => fn st =>
            if Toplevel.is_proof st
            then Output.state (Pretty.strings_of (Pretty.chunks (Toplevel.pretty_state st)))
            else ()}
      else NONE);
