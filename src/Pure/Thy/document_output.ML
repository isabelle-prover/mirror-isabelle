(*  Title:      Pure/Thy/document_output.ML
    Author:     Makarius

Theory document output.
*)

signature DOCUMENT_OUTPUT =
sig
  val document_reports: Input.source -> Position.report list
  val output_document: Proof.context -> {markdown: bool} -> Input.source -> Latex.text
  val document_output: {markdown: bool, markup: Latex.text -> Latex.text} ->
    (xstring * Position.T) option * Input.source -> Toplevel.transition -> Toplevel.transition
  val check_comments: Proof.context -> Symbol_Pos.T list -> unit
  val output_token: Proof.context -> Token.T -> Latex.text
  val output_source: Proof.context -> string -> Latex.text
  type segment =
    {span: Command_Span.span, command: Toplevel.transition,
     prev_state: Toplevel.state, state: Toplevel.state}
  val segment_eof: segment
  val segment_stopper: segment Scan.stopper
  val present_thy: Options.T -> Keyword.keywords -> string -> segment list -> Latex.text
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val isabelle: Proof.context -> Latex.text -> Latex.text
  val isabelle_typewriter: Proof.context -> Latex.text -> Latex.text
  val typewriter: Proof.context -> string -> Latex.text
  val verbatim: Proof.context -> string -> Latex.text
  val source: Proof.context -> {embedded: bool} -> Token.src -> Latex.text
  val pretty: Proof.context -> Pretty.T -> Latex.text
  val pretty_source: Proof.context -> {embedded: bool} -> Token.src -> Pretty.T -> Latex.text
  val pretty_items: Proof.context -> Pretty.T list -> Latex.text
  val pretty_items_source: Proof.context -> {embedded: bool} -> Token.src ->
    Pretty.T list -> Latex.text
  val antiquotation_pretty:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory
  val antiquotation_pretty_embedded:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory
  val antiquotation_pretty_source:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory
  val antiquotation_pretty_source_embedded:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory
  val antiquotation_raw:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Latex.text) -> theory -> theory
  val antiquotation_raw_embedded:
    binding -> 'a context_parser -> (Proof.context -> 'a -> Latex.text) -> theory -> theory
  val antiquotation_verbatim:
    binding -> 'a context_parser -> (Proof.context -> 'a -> string) -> theory -> theory
  val antiquotation_verbatim_embedded:
    binding -> 'a context_parser -> (Proof.context -> 'a -> string) -> theory -> theory
end;

structure Document_Output: DOCUMENT_OUTPUT =
struct

(* output document source *)

fun document_reports txt =
  let val pos = Input.pos_of txt in
    [(pos, Markup.language_document (Input.is_delimited txt)),
     (pos, Markup.plain_text)]
  end;

fun output_comment ctxt (kind, syms) =
  (case kind of
    Comment.Comment =>
      Input.cartouche_content syms
      |> output_document (ctxt |> Config.put Document_Antiquotation.thy_output_display false)
          {markdown = false}
      |> XML.enclose "%\n\\isamarkupcmt{" "%\n}"
  | Comment.Cancel =>
      Symbol_Pos.cartouche_content syms
      |> Latex.symbols_output
      |> XML.enclose "%\n\\isamarkupcancel{" "}"
  | Comment.Latex => Latex.symbols (Symbol_Pos.cartouche_content syms)
  | Comment.Marker => [])
and output_comment_document ctxt (comment, syms) =
  (case comment of
    SOME kind => output_comment ctxt (kind, syms)
  | NONE => Latex.symbols syms)
and output_document_text ctxt syms =
  Comment.read_body syms |> maps (output_comment_document ctxt)
and output_document ctxt {markdown} source =
  let
    val pos = Input.pos_of source;
    val syms = Input.source_explode source;

    val output_antiquotes =
      maps (Document_Antiquotation.evaluate (output_document_text ctxt) ctxt);

    fun output_line line =
      (if Markdown.line_is_item line then Latex.string "\\item " else []) @
        output_antiquotes (Markdown.line_content line);

    fun output_block (Markdown.Par lines) =
          separate (XML.Text "\n") (map (Latex.block o output_line) lines)
      | output_block (Markdown.List {kind, body, ...}) =
          Latex.environment (Markdown.print_kind kind) (output_blocks body)
    and output_blocks blocks =
      separate (XML.Text "\n\n") (map (Latex.block o output_block) blocks);
  in
    if Toplevel.is_skipped_proof (Toplevel.presentation_state ctxt) then []
    else if markdown andalso exists (Markdown.is_control o Symbol_Pos.symbol) syms
    then
      let
        val ants = Antiquote.parse_comments pos syms;
        val reports = Antiquote.antiq_reports ants;
        val blocks = Markdown.read_antiquotes ants;
        val _ = Context_Position.reports ctxt (reports @ Markdown.reports blocks);
      in output_blocks blocks end
    else
      let
        val ants = Antiquote.parse_comments pos (trim (Symbol.is_blank o Symbol_Pos.symbol) syms);
        val reports = Antiquote.antiq_reports ants;
        val _ = Context_Position.reports ctxt (reports @ Markdown.text_reports ants);
      in output_antiquotes ants end
  end;

fun document_output {markdown, markup} (loc, txt) =
  let
    fun output st =
      let
        val ctxt = Toplevel.presentation_context st;
        val _ = Context_Position.reports ctxt (document_reports txt);
      in txt |> output_document ctxt {markdown = markdown} |> markup end;
  in
    Toplevel.present (fn st =>
      (case loc of
        NONE => output st
      | SOME (_, pos) =>
          error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
    Toplevel.present_local_theory loc output
  end;


(* output tokens with formal comments *)

local

val output_symbols_antiq =
  (fn Antiquote.Text syms => Latex.symbols_output syms
    | Antiquote.Control {name = (name, _), body, ...} =>
        Latex.string (Latex.output_symbols [Symbol.encode (Symbol.Control name)]) @
          Latex.symbols_output body
    | Antiquote.Antiq {body, ...} =>
        XML.enclose "%\n\\isaantiq\n" "{}%\n\\endisaantiq\n" (Latex.symbols_output body));

fun output_comment_symbols ctxt {antiq} (comment, syms) =
  (case (comment, antiq) of
    (NONE, false) => Latex.symbols_output syms
  | (NONE, true) =>
      Antiquote.parse_comments (#1 (Symbol_Pos.range syms)) syms
      |> maps output_symbols_antiq
  | (SOME comment, _) => output_comment ctxt (comment, syms));

fun output_body ctxt antiq bg en syms =
  Comment.read_body syms
  |> maps (output_comment_symbols ctxt {antiq = antiq})
  |> XML.enclose bg en;

in

fun output_token ctxt tok =
  let
    val keywords = Thy_Header.get_keywords' ctxt;

    fun output antiq bg en =
      output_body ctxt antiq bg en (Input.source_explode (Token.input_of tok));
  in
    (case Token.kind_of tok of
      Token.Comment NONE => []
    | Token.Comment (SOME Comment.Marker) => []
    | Token.Command =>
        let
          val name = (Token.content_of tok);
          val bg =
            if Keyword.is_theory_end keywords name then "\\isakeywordTWO{"
            else if Keyword.is_proof_asm keywords name orelse
              Keyword.is_proof_asm_goal keywords name then "\\isakeywordTHREE{"
            else if Keyword.is_proof_asm_goal keywords name then "\\isakeywordTHREE{"
            else "\\isakeywordONE{";
        in output false bg "}" end
    | Token.Keyword =>
        if Symbol.is_ascii_identifier (Token.content_of tok)
        then output false "\\isakeywordTWO{" "}"
        else output false "" ""
    | Token.String => output false "{\\isachardoublequoteopen}" "{\\isachardoublequoteclose}"
    | Token.Alt_String => output false "{\\isacharbackquoteopen}" "{\\isacharbackquoteclose}"
    | Token.Cartouche => output false "{\\isacartoucheopen}" "{\\isacartoucheclose}"
    | Token.Control control => output_body ctxt false "" "" (Antiquote.control_symbols control)
    | _ => output false "" "")
  end handle ERROR msg => error (msg ^ Position.here (Token.pos_of tok));

fun output_source ctxt s =
  output_body ctxt false "" "" (Symbol_Pos.explode (s, Position.none));

fun check_comments ctxt =
  Comment.read_body #> List.app (fn (comment, syms) =>
    let
      val pos = #1 (Symbol_Pos.range syms);
      val _ =
        comment |> Option.app (fn kind =>
          Context_Position.reports ctxt (map (pair pos) (Comment.kind_markups kind)));
      val _ = output_comment_symbols ctxt {antiq = false} (comment, syms);
    in if comment = SOME Comment.Comment then check_comments ctxt syms else () end);

end;



(** present theory source **)

(* presentation tokens *)

datatype token =
    Ignore
  | Token of Token.T
  | Output of Latex.text;

fun token_with pred (Token tok) = pred tok
  | token_with _ _ = false;

val white_token = token_with Document_Source.is_white;
val white_comment_token = token_with Document_Source.is_white_comment;
val blank_token = token_with Token.is_blank;
val newline_token = token_with Token.is_newline;

fun present_token ctxt tok =
  (case tok of
    Ignore => []
  | Token tok => output_token ctxt tok
  | Output output => output);


(* command spans *)

type command = string * Position.T;  (*name, position*)
type source = (token * (string * int)) list;  (*token, markup flag, meta-comment depth*)

datatype span = Span of command * (source * source * source * source) * bool;

fun make_span cmd src =
  let
    fun chop_newline (tok :: toks) =
          if newline_token (fst tok) then ([tok], toks, true)
          else ([], tok :: toks, false)
      | chop_newline [] = ([], [], false);
    val (((src_prefix, src_main), src_suffix1), (src_suffix2, src_appendix, newline)) =
      src
      |> chop_prefix (white_token o fst)
      ||>> chop_suffix (white_token o fst)
      ||>> chop_prefix (white_comment_token o fst)
      ||> chop_newline;
  in Span (cmd, (src_prefix, src_main, src_suffix1 @ src_suffix2, src_appendix), newline) end;


(* present spans *)

local

fun err_bad_nesting here =
  error ("Bad nesting of commands in presentation" ^ here);

fun edge which f (x: string option, y) =
  if x = y then I
  else (case which (x, y) of NONE => I | SOME txt => fold cons (Latex.string (f txt)));

val markup_tag = YXML.output_markup o Markup.latex_tag;
val markup_delim = YXML.output_markup o Markup.latex_delim;
val bg_delim = #1 o markup_delim;
val en_delim = #2 o markup_delim;

val begin_tag = edge #2 (#1 o markup_tag);
val end_tag = edge #1 (#2 o markup_tag);
fun open_delim delim e = edge #2 bg_delim e #> delim #> edge #2 en_delim e;
fun close_delim delim e = edge #1 bg_delim e #> delim #> edge #1 en_delim e;

fun document_tag cmd_pos state state' tagging_stack =
  let
    val ctxt' = Toplevel.presentation_context state';
    val nesting = Toplevel.level state' - Toplevel.level state;

    val (tagging, taggings) = tagging_stack;
    val (tag', tagging') = Document_Source.update_tagging ctxt' tagging;

    val tagging_stack' =
      if nesting = 0 andalso not (Toplevel.is_proof state) then tagging_stack
      else if nesting >= 0 then (tagging', replicate nesting tagging @ taggings)
      else
        (case drop (~ nesting - 1) taggings of
          tg :: tgs => (tg, tgs)
        | [] => err_bad_nesting (Position.here cmd_pos));
  in (tag', tagging_stack') end;

fun read_tag s =
  (case space_explode "%" s of
    ["", b] => (SOME b, NONE)
  | [a, b] => (NONE, SOME (a, b))
  | _ => error ("Bad document_tags specification: " ^ quote s));

in

fun make_command_tag options keywords =
  let
    val document_tags =
      map read_tag (space_explode "," (Options.string options \<^system_option>\<open>document_tags\<close>));
    val document_tags_default = map_filter #1 document_tags;
    val document_tags_command = map_filter #2 document_tags;
  in
    fn name => fn st => fn st' => fn active_tag =>
      let
        val keyword_tags =
          if Keyword.is_theory_end keywords name andalso Toplevel.is_end_theory st' then ["theory"]
          else Keyword.command_tags keywords name;
        val command_tags =
          the_list (AList.lookup (op =) document_tags_command name) @
          keyword_tags @ document_tags_default;
        val active_tag' =
          (case command_tags of
            default_tag :: _ => SOME default_tag
          | [] =>
              if Keyword.is_vacuous keywords name andalso Toplevel.is_proof st
              then active_tag else NONE);
      in active_tag' end
  end;

fun present_span command_tag span state state'
    (tagging_stack, active_tag, newline, latex, present_cont) =
  let
    val ctxt' = Toplevel.presentation_context state';
    val present = fold (fn (tok, (flag, 0)) =>
        fold cons (present_token ctxt' tok)
        #> fold cons (Latex.string flag)
      | _ => I);

    val Span ((cmd_name, cmd_pos), srcs, span_newline) = span;

    val (tag', tagging_stack') = document_tag cmd_pos state state' tagging_stack;
    val active_tag' =
      if is_some tag' then Option.map #1 tag'
      else command_tag cmd_name state state' active_tag;
    val edge = (active_tag, active_tag');

    val newline' =
      if is_none active_tag' then span_newline else newline;

    val latex' =
      latex
      |> end_tag edge
      |> close_delim (fst present_cont) edge
      |> snd present_cont
      |> open_delim (present (#1 srcs)) edge
      |> begin_tag edge
      |> present (#2 srcs);
    val present_cont' =
      if newline then (present (#3 srcs), present (#4 srcs))
      else (I, present (#3 srcs) #> present (#4 srcs));
  in (tagging_stack', active_tag', newline', latex', present_cont') end;

fun present_trailer ((_, tags), active_tag, _, latex, present_cont) =
  if not (null tags) then err_bad_nesting " at end of theory"
  else
    latex
    |> end_tag (active_tag, NONE)
    |> close_delim (fst present_cont) (active_tag, NONE)
    |> snd present_cont;

end;


(* present_thy *)

type segment =
  {span: Command_Span.span, command: Toplevel.transition,
   prev_state: Toplevel.state, state: Toplevel.state};

val segment_eof: segment =
  {span = Command_Span.eof, command = Toplevel.empty,
   prev_state = Toplevel.make_state NONE, state = Toplevel.make_state NONE};

val segment_stopper =
  Scan.stopper (K segment_eof) (Command_Span.is_eof o #span);


local

val markup_true = "\\isamarkuptrue%\n";
val markup_false = "\\isamarkupfalse%\n";

fun command_output output tok =
  if Token.is_command tok then SOME (Token.put_output output tok) else NONE;

fun segment_content (segment: segment) =
  let val toks = Command_Span.content (#span segment) in
    (case Toplevel.output_of (#state segment) of
      NONE => toks
    | SOME output => map_filter (command_output output) toks)
  end;

fun output_command keywords = Scan.some (fn tok =>
  if Token.is_command tok then
    let
      val name = Token.content_of tok;
      val is_document = Keyword.is_document keywords name;
      val is_document_raw = Keyword.is_document_raw keywords name;
      val flag = if is_document andalso not is_document_raw then markup_true else "";
    in
      if is_document andalso is_some (Token.get_output tok)
      then SOME ((name, Token.pos_of tok), the (Token.get_output tok), flag)
      else NONE
    end
  else NONE);

val opt_newline = Scan.option (Scan.one Token.is_newline);

val ignore =
  Scan.depend (fn d => opt_newline |-- Scan.one Token.is_begin_ignore
    >> pair (d + 1)) ||
  Scan.depend (fn d => Scan.one Token.is_end_ignore --|
    (if d = 0 then Scan.fail_with (K (fn () => "Bad nesting of meta-comments")) else opt_newline)
    >> pair (d - 1));

in

fun present_thy options keywords thy_name (segments: segment list) =
  let
    (* tokens *)

    val ignored = Scan.state --| ignore
      >> (fn d => [(NONE, (Ignore, ("", d)))]);

    val output = Scan.peek (fn d =>
      Document_Source.improper |-- output_command keywords --| Document_Source.improper_end
        >> (fn (kind, body, flag) => [(SOME kind, (Output body, (flag, d)))]));

    val command = Scan.peek (fn d =>
      Scan.optional (Scan.one Token.is_command_modifier ::: Document_Source.improper) [] --
      Scan.one Token.is_command --| Document_Source.annotation
      >> (fn (cmd_mod, cmd) =>
        map (fn tok => (NONE, (Token tok, ("", d)))) cmd_mod @
          [(SOME (Token.content_of cmd, Token.pos_of cmd),
            (Token cmd, (markup_false, d)))]));

    val cmt = Scan.peek (fn d =>
      Scan.one Document_Source.is_black_comment >> (fn tok => [(NONE, (Token tok, ("", d)))]));

    val other = Scan.peek (fn d =>
       Parse.not_eof >> (fn tok => [(NONE, (Token tok, ("", d)))]));

    val tokens = ignored || output || command || cmt || other;


    (* spans *)

    val is_eof = fn (_, (Token x, _)) => Token.is_eof x | _ => false;
    val stopper = Scan.stopper (K (NONE, (Token Token.eof, ("", 0)))) is_eof;

    val cmd = Scan.one (is_some o fst);
    val non_cmd = Scan.one (is_none o fst andf not o is_eof) >> #2;

    val white_comments = Scan.many (white_comment_token o fst o snd);
    val blank = Scan.one (blank_token o fst o snd);
    val newline = Scan.one (newline_token o fst o snd);
    val before_cmd =
      Scan.option (newline -- white_comments) --
      Scan.option (newline -- white_comments) --
      Scan.option (blank -- white_comments) -- cmd;

    val span =
      Scan.repeat non_cmd -- cmd --
        Scan.repeat (Scan.unless before_cmd non_cmd) --
        Scan.option (newline >> (single o snd))
      >> (fn (((toks1, (cmd, tok2)), toks3), tok4) =>
          make_span (the cmd) (toks1 @ (tok2 :: (toks3 @ the_default [] tok4))));

    val spans = segments
      |> maps segment_content
      |> drop_suffix Token.is_space
      |> Source.of_list
      |> Source.source' 0 Token.stopper (Scan.error (Scan.bulk tokens >> flat))
      |> Source.source stopper (Scan.error (Scan.bulk span))
      |> Source.exhaust;

    val command_results =
      segments |> map_filter (fn {command, state, ...} =>
        if Toplevel.is_ignored command then NONE else SOME (command, state));


    (* present commands *)

    val command_tag = make_command_tag options keywords;

    fun present_command tr span st st' =
      Toplevel.setmp_thread_position tr (present_span command_tag span st st');

    fun present _ [] = I
      | present st ((span, (tr, st')) :: rest) = present_command tr span st st' #> present st' rest;
  in
    if length command_results = length spans then
      (([], []), NONE, true, [], (I, I))
      |> present (Toplevel.make_state NONE) (spans ~~ command_results)
      |> present_trailer
      |> rev
      |> Latex.isabelle_body thy_name
    else error "Messed-up outer syntax for presentation"
  end;

end;



(** standard output operations **)

(* pretty printing *)

fun pretty_term ctxt t =
  Syntax.pretty_term (Proof_Context.augment t ctxt) t;

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;


(* default output *)

fun isabelle ctxt body =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then Latex.environment "isabelle" body
  else Latex.macro "isa" body;

fun isabelle_typewriter ctxt body =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then Latex.environment "isabellett" body
  else Latex.macro "isatt" body;

fun typewriter ctxt s =
  isabelle_typewriter ctxt (Latex.string (Latex.output_ascii s));

fun verbatim ctxt =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then Document_Antiquotation.indent_lines ctxt #> typewriter ctxt
  else split_lines #> map (typewriter ctxt #> Latex.block) #> separate (XML.Text "\\isanewline%\n");

fun token_source ctxt {embedded} tok =
  if Token.is_kind Token.Cartouche tok andalso embedded andalso
    not (Config.get ctxt Document_Antiquotation.thy_output_source_cartouche)
  then Token.content_of tok
  else Token.unparse tok;

fun is_source ctxt =
  Config.get ctxt Document_Antiquotation.thy_output_source orelse
  Config.get ctxt Document_Antiquotation.thy_output_source_cartouche;

fun source ctxt embedded =
  Token.args_of_src
  #> map (token_source ctxt embedded #> Document_Antiquotation.prepare_lines ctxt)
  #> implode_space
  #> output_source ctxt
  #> isabelle ctxt;

fun pretty ctxt =
  Document_Antiquotation.output ctxt #> Latex.string #> isabelle ctxt;

fun pretty_source ctxt embedded src prt =
  if is_source ctxt then source ctxt embedded src else pretty ctxt prt;

fun pretty_items ctxt =
  map (Document_Antiquotation.output ctxt #> XML.Text) #>
  separate (XML.Text "\\isasep\\isanewline%\n") #> isabelle ctxt;

fun pretty_items_source ctxt embedded src prts =
  if is_source ctxt then source ctxt embedded src else pretty_items ctxt prts;


(* antiquotation variants *)

local

fun gen_setup name embedded =
  if embedded
  then Document_Antiquotation.setup_embedded name
  else Document_Antiquotation.setup name;

fun gen_antiquotation_pretty name embedded scan f =
  gen_setup name embedded scan (fn {context = ctxt, argument = x, ...} => pretty ctxt (f ctxt x));

fun gen_antiquotation_pretty_source name embedded scan f =
  gen_setup name embedded scan
    (fn {context = ctxt, source = src, argument = x} =>
      pretty_source ctxt {embedded = embedded} src (f ctxt x));

fun gen_antiquotation_raw name embedded scan f =
  gen_setup name embedded scan (fn {context = ctxt, argument = x, ...} => f ctxt x);

fun gen_antiquotation_verbatim name embedded scan f =
  gen_antiquotation_raw name embedded scan (fn ctxt => verbatim ctxt o f ctxt);

in

fun antiquotation_pretty name = gen_antiquotation_pretty name false;
fun antiquotation_pretty_embedded name = gen_antiquotation_pretty name true;

fun antiquotation_pretty_source name = gen_antiquotation_pretty_source name false;
fun antiquotation_pretty_source_embedded name = gen_antiquotation_pretty_source name true;

fun antiquotation_raw name = gen_antiquotation_raw name false;
fun antiquotation_raw_embedded name = gen_antiquotation_raw name true;

fun antiquotation_verbatim name = gen_antiquotation_verbatim name false;
fun antiquotation_verbatim_embedded name = gen_antiquotation_verbatim name true;

end;

end;
