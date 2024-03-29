(*  Title:      Pure/ML/ml_lex.ML
    Author:     Makarius

Lexical syntax for Isabelle/ML and Standard ML.
*)

signature ML_LEX =
sig
  val keywords: string list
  datatype token_kind =
    Keyword | Ident | Long_Ident | Type_Var | Word | Int | Real | Char | String |
    Space | Comment of Comment.kind option | Error of string | EOF
  eqtype token
  val stopper: token Scan.stopper
  val is_ident_with: (string -> bool) -> token -> bool
  val is_regular: token -> bool
  val is_improper: token -> bool
  val is_comment: token -> bool
  val set_range: Position.range -> token -> token
  val range_of: token -> Position.range
  val pos_of: token -> Position.T
  val end_pos_of: token -> Position.T
  val kind_of: token -> token_kind
  val content_of: token -> string
  val check_content_of: token -> string
  val flatten: token list -> string
  val source: (Symbol.symbol, 'a) Source.source ->
    (token, (Symbol_Pos.T, Position.T * (Symbol.symbol, 'a) Source.source)
      Source.source) Source.source
  val tokenize: string -> token list
  val tokenize_range: Position.range -> string -> token list
  val tokenize_no_range: string -> token list
  val read_text: Symbol_Pos.text * Position.T -> token Antiquote.antiquote list
  val read: Symbol_Pos.text -> token Antiquote.antiquote list
  val read_range: Position.range -> Symbol_Pos.text -> token Antiquote.antiquote list
  val read_source': {language: bool -> Markup.T, opaque_warning: bool, symbols: bool} ->
    token Antiquote.antiquote Symbol_Pos.scanner -> Input.source -> token Antiquote.antiquote list
  val read_source: Input.source -> token Antiquote.antiquote list
  val read_source_sml: Input.source -> token Antiquote.antiquote list
  val read_symbols: Symbol_Pos.T list -> token Antiquote.antiquote list
  val read_symbols_sml: Symbol_Pos.T list -> token Antiquote.antiquote list
end;

structure ML_Lex: ML_LEX =
struct

(** keywords **)

val keywords =
 ["#", "(", ")", ",", "->", "...", ":", ":>", ";", "=", "=>", "[",
  "]", "_", "{", "|", "}", "abstype", "and", "andalso", "as", "case",
  "datatype", "do", "else", "end", "eqtype", "exception", "fn", "fun",
  "functor", "handle", "if", "in", "include", "infix", "infixr",
  "let", "local", "nonfix", "of", "op", "open", "orelse", "raise",
  "rec", "sharing", "sig", "signature", "struct", "structure", "then",
  "type", "val", "where", "while", "with", "withtype"];

val keywords2 =
 Symset.make ["and", "case", "do", "else", "end", "if", "in", "let", "local", "of",
  "sig", "struct", "then", "while", "with"];

val keywords3 =
 Symset.make ["handle", "open", "raise"];

val lexicon = Scan.make_lexicon (map raw_explode keywords);



(** tokens **)

(* datatype token *)

datatype token_kind =
  Keyword | Ident | Long_Ident | Type_Var | Word | Int | Real | Char | String |
  Space | Comment of Comment.kind option | Error of string | EOF;

datatype token = Token of Position.range * (token_kind * string);


(* position *)

fun set_range range (Token (_, x)) = Token (range, x);
fun range_of (Token (range, _)) = range;

val pos_of = #1 o range_of;
val end_pos_of = #2 o range_of;


(* stopper *)

fun mk_eof pos = Token ((pos, Position.none), (EOF, ""));
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;


(* token content *)

fun kind_of (Token (_, (k, _))) = k;

fun content_of (Token (_, (_, x))) = x;
fun token_leq (tok, tok') = content_of tok <= content_of tok';

fun is_keyword (Token (_, (Keyword, _))) = true
  | is_keyword _ = false;

fun is_delimiter (Token (_, (Keyword, x))) = not (Symbol.is_ascii_identifier x)
  | is_delimiter _ = false;

fun is_ident_with pred (Token (_, (Ident, x))) = pred x
  | is_ident_with _ _ = false;

fun is_regular (Token (_, (Error _, _))) = false
  | is_regular (Token (_, (EOF, _))) = false
  | is_regular _ = true;

fun is_improper (Token (_, (Space, _))) = true
  | is_improper (Token (_, (Comment _, _))) = true
  | is_improper _ = false;

fun is_comment (Token (_, (Comment _, _))) = true
  | is_comment _ = false;

fun warning_opaque tok =
  (case tok of
    Token (_, (Keyword, ":>")) =>
      warning ("Opaque signature matching (:>) fails to work with ML pretty printing --\n\
        \prefer non-opaque matching (:) possibly with abstype" ^
        Position.here (pos_of tok))
  | _ => ());

fun check_content_of tok =
  (case kind_of tok of
    Error msg => error msg
  | _ => content_of tok);


(* flatten *)

fun flatten_content (tok :: (toks as tok' :: _)) =
      Symbol.escape (check_content_of tok) ::
        (if is_improper tok orelse is_improper tok' then flatten_content toks
         else Symbol.space :: flatten_content toks)
  | flatten_content toks = map (Symbol.escape o check_content_of) toks;

val flatten = implode o flatten_content;


(* markup *)

local

val token_kind_markup =
 fn Type_Var => (Markup.ML_tvar, "")
  | Word => (Markup.ML_numeral, "")
  | Int => (Markup.ML_numeral, "")
  | Real => (Markup.ML_numeral, "")
  | Char => (Markup.ML_char, "")
  | String => (Markup.ML_string, "")
  | Comment _ => (Markup.ML_comment, "")
  | Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

in

fun token_report (tok as Token ((pos, _), (kind, x))) =
  let
    val (markup, txt) =
      if not (is_keyword tok) then token_kind_markup kind
      else if is_delimiter tok then (Markup.ML_delimiter, "")
      else if Symset.member keywords2 x then (Markup.ML_keyword2 |> Markup.keyword_properties, "")
      else if Symset.member keywords3 x then (Markup.ML_keyword3 |> Markup.keyword_properties, "")
      else (Markup.ML_keyword1 |> Markup.keyword_properties, "");
  in ((pos, markup), txt) end;

end;



(** scanners **)

open Basic_Symbol_Pos;

val err_prefix = "SML lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);


(* identifiers *)

local

val scan_letdigs =
  Scan.many (Symbol.is_ascii_letdig o Symbol_Pos.symbol);

val scan_alphanumeric =
  Scan.one (Symbol.is_ascii_letter o Symbol_Pos.symbol) ::: scan_letdigs;

val symbolic = Symset.make (raw_explode "!#$%&*+-/:<=>?@\\^`|~");

val scan_symbolic = Scan.many1 (Symset.member symbolic o Symbol_Pos.symbol);

in

val scan_ident = scan_alphanumeric || scan_symbolic;

val scan_long_ident =
  Scan.repeats1 (scan_alphanumeric @@@ $$$ ".") @@@ (scan_ident || $$$ "=");

val scan_type_var = $$$ "'" @@@ scan_letdigs;

end;


(* numerals *)

local

val scan_dec = Scan.many1 (Symbol.is_ascii_digit o Symbol_Pos.symbol);
val scan_hex = Scan.many1 (Symbol.is_ascii_hex o Symbol_Pos.symbol);
val scan_sign = Scan.optional ($$$ "~") [];
val scan_decint = scan_sign @@@ scan_dec;
val scan_exp = ($$$ "E" || $$$ "e") @@@ scan_decint;

in

val scan_word =
  $$$ "0" @@@ $$$ "w" @@@ $$$ "x" @@@ scan_hex ||
  $$$ "0" @@@ $$$ "w" @@@ scan_dec;

val scan_int = scan_sign @@@ ($$$ "0" @@@ $$$ "x" @@@ scan_hex || scan_dec);

val scan_rat = scan_decint @@@ Scan.optional ($$$ "/" @@@ scan_dec) [];

val scan_real =
  scan_decint @@@ $$$ "." @@@ scan_dec @@@ Scan.optional scan_exp [] ||
  scan_decint @@@ scan_exp;

end;


(* chars and strings *)

val scan_blanks1 = Scan.many1 (Symbol.is_ascii_blank o Symbol_Pos.symbol);

local

val escape = Symset.make (raw_explode "\"\\abtnvfr");

val scan_escape =
  Scan.one (Symset.member escape o Symbol_Pos.symbol) >> single ||
  $$$ "^" @@@
    (Scan.one (fn (s, _) => Char.ord #"@" <= ord s andalso ord s <= Char.ord #"_") >> single) ||
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
    Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
    Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) >> (fn ((a, b), c) => [a, b, c]);

val scan_str =
  Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> "\"" andalso s <> "\\" andalso
    (not (Symbol.is_char s) orelse Symbol.is_printable s)) >> single ||
  $$$ "\\" @@@ !!! "bad escape character in string" scan_escape;

val scan_gap = $$$ "\\" @@@ scan_blanks1 @@@ $$$ "\\";
val scan_gaps = Scan.repeats scan_gap;

in

val scan_char =
  $$$ "#" @@@ $$$ "\"" @@@ scan_gaps @@@ scan_str @@@ scan_gaps @@@ $$$ "\"";

val recover_char =
  $$$ "#" @@@ $$$ "\"" @@@ scan_gaps @@@ Scan.optional (Scan.permissive scan_str @@@ scan_gaps) [];

val scan_string =
  Scan.ahead ($$ "\"") |--
    !!! "unclosed string literal"
      ($$$ "\"" @@@ Scan.repeats (scan_gap || scan_str) @@@ $$$ "\"");

val recover_string =
  $$$ "\"" @@@ Scan.repeats (scan_gap || Scan.permissive scan_str);

end;


(* rat antiquotation *)

val rat_name = Symbol_Pos.explode ("Pure.rat ", Position.none);

val scan_rat_antiq =
  Symbol_Pos.scan_pos -- ($$ "@" |-- Symbol_Pos.scan_pos -- scan_rat) -- Symbol_Pos.scan_pos
    >> (fn ((pos1, (pos2, body)), pos3) =>
      {start = Position.range_position (pos1, pos2),
       stop = Position.none,
       range = Position.range (pos1, pos3),
       body = rat_name @ body});


(* scan tokens *)

local

fun token k ss = Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss));

val scan_sml =
  scan_char >> token Char ||
  scan_string >> token String ||
  scan_blanks1 >> token Space ||
  Symbol_Pos.scan_comment err_prefix >> token (Comment NONE) ||
  Scan.max token_leq
   (Scan.literal lexicon >> token Keyword)
   (scan_word >> token Word ||
    scan_real >> token Real ||
    scan_int >> token Int ||
    scan_long_ident >> token Long_Ident ||
    scan_ident >> token Ident ||
    scan_type_var >> token Type_Var);

val scan_sml_antiq = scan_sml >> Antiquote.Text;

val scan_ml_antiq =
  Comment.scan_inner >> (fn (kind, ss) => Antiquote.Text (token (Comment (SOME kind)) ss)) ||
  Antiquote.scan_control Antiquote.err_prefix >> Antiquote.Control ||
  Antiquote.scan_antiq >> Antiquote.Antiq ||
  scan_rat_antiq >> Antiquote.Antiq ||
  scan_sml_antiq;

fun recover msg =
 (recover_char ||
  recover_string ||
  Symbol_Pos.recover_cartouche ||
  Symbol_Pos.recover_comment ||
  Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> single)
  >> (single o token (Error msg));

fun reader {opaque_warning} scan syms =
  let
    val termination =
      if null syms then []
      else
        let
          val pos1 = List.last syms |-> Position.symbol;
          val pos2 = Position.symbol Symbol.space pos1;
        in [Antiquote.Text (Token (Position.range (pos1, pos2), (Space, Symbol.space)))] end;

    fun check (Antiquote.Text tok) =
          (check_content_of tok; if opaque_warning then warning_opaque tok else ())
      | check _ = ();
    val input =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper
        (Scan.recover (Scan.bulk (!!! "bad input" scan))
          (fn msg => recover msg >> map Antiquote.Text))
      |> Source.exhaust;
    val _ = Position.reports (Antiquote.antiq_reports input);
    val _ = Position.reports_text (maps (fn Antiquote.Text t => [token_report t] | _ => []) input);
    val _ = List.app check input;
  in input @ termination end;

in

fun source src =
  Symbol_Pos.source (Position.line 1) src
  |> Source.source Symbol_Pos.stopper (Scan.recover (Scan.bulk (!!! "bad input" scan_sml)) recover);

val tokenize = Symbol.explode #> Source.of_list #> source #> Source.exhaust;
fun tokenize_range range = tokenize #> map (set_range range);
val tokenize_no_range = tokenize_range Position.no_range;

val read_text = reader {opaque_warning = true} scan_ml_antiq o Symbol_Pos.explode;
fun read text = read_text (text, Position.none);

fun read_range range =
  read #> map (fn Antiquote.Text tok => Antiquote.Text (set_range range tok) | antiq => antiq);

fun read_source' {language, symbols, opaque_warning} scan source =
  let
    val pos = Input.pos_of source;
    val _ =
      if Position.is_reported_range pos
      then Position.report pos (language (Input.is_delimited source))
      else ();
  in
    Input.source_explode source
    |> not symbols ? maps (fn (s, p) => raw_explode s |> map (rpair p))
    |> reader {opaque_warning = opaque_warning} scan
  end;

val read_source =
  read_source' {language = Markup.language_ML, symbols = true, opaque_warning = true}
    scan_ml_antiq;

val read_source_sml =
  read_source' {language = Markup.language_SML, symbols = false, opaque_warning = false}
    scan_sml_antiq;

val read_symbols = reader {opaque_warning = true} scan_ml_antiq;
val read_symbols_sml = reader {opaque_warning = false} scan_sml_antiq;

end;

end;
