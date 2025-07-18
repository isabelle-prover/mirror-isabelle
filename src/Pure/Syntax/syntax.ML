(*  Title:      Pure/Syntax/syntax.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Standard Isabelle syntax, based on arbitrary context-free grammars
(specified by mixfix declarations).
*)

signature SYNTAX =
sig
  datatype 'a trrule =
    Parse_Rule of 'a * 'a |
    Print_Rule of 'a * 'a |
    Parse_Print_Rule of 'a * 'a
  type operations
  val install_operations: operations -> theory -> theory
  val root: string Config.T
  val ambiguity_warning: bool Config.T
  val ambiguity_limit: int Config.T
  val encode_input: Input.source -> XML.tree
  val implode_input: Input.source -> string
  val read_input_pos: string -> Position.T
  val read_input: string -> Input.source
  val parse_input: Proof.context -> (XML.tree list -> 'a) ->
    (bool -> Markup.T) -> (Symbol_Pos.T list * Position.T -> 'a) -> string -> 'a
  val parse_trrule: Proof.context -> (string * string) trrule -> Ast.ast trrule
  val parse_sort: Proof.context -> string -> sort
  val parse_typ: Proof.context -> string -> typ
  val parse_term: Proof.context -> string -> term
  val parse_prop: Proof.context -> string -> term
  val unparse_sort: Proof.context -> sort -> Pretty.T
  val unparse_classrel: Proof.context -> class list -> Pretty.T
  val unparse_arity: Proof.context -> arity -> Pretty.T
  val unparse_typ: Proof.context -> typ -> Pretty.T
  val unparse_term: Proof.context -> term -> Pretty.T
  val check_sort: Proof.context -> sort -> sort
  val check_typ: Proof.context -> typ -> typ
  val check_term: Proof.context -> term -> term
  val check_prop: Proof.context -> term -> term
  val check_typs: Proof.context -> typ list -> typ list
  val check_terms: Proof.context -> term list -> term list
  val check_props: Proof.context -> term list -> term list
  val uncheck_sort: Proof.context -> sort -> sort
  val uncheck_arity: Proof.context -> arity -> arity
  val uncheck_classrel: Proof.context -> class list -> class list
  val uncheck_typs: Proof.context -> typ list -> typ list
  val uncheck_terms: Proof.context -> term list -> term list
  val read_sort: Proof.context -> string -> sort
  val read_typ: Proof.context -> string -> typ
  val read_term: Proof.context -> string -> term
  val read_prop: Proof.context -> string -> term
  val read_typs: Proof.context -> string list -> typ list
  val read_terms: Proof.context -> string list -> term list
  val read_props: Proof.context -> string list -> term list
  val read_sort_global: theory -> string -> sort
  val read_typ_global: theory -> string -> typ
  val read_term_global: theory -> string -> term
  val read_prop_global: theory -> string -> term
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_typ: Proof.context -> typ -> Pretty.T
  val pretty_sort: Proof.context -> sort -> Pretty.T
  val pretty_classrel: Proof.context -> class list -> Pretty.T
  val pretty_arity: Proof.context -> arity -> Pretty.T
  val string_of_term: Proof.context -> term -> string
  val string_of_typ: Proof.context -> typ -> string
  val string_of_sort: Proof.context -> sort -> string
  val string_of_classrel: Proof.context -> class list -> string
  val string_of_arity: Proof.context -> arity -> string
  val is_pretty_global: Proof.context -> bool
  val set_pretty_global: bool -> Proof.context -> Proof.context
  val init_pretty_global: theory -> Proof.context
  val init_pretty: Context.generic -> Proof.context
  val pretty_term_global: theory -> term -> Pretty.T
  val pretty_typ_global: theory -> typ -> Pretty.T
  val pretty_sort_global: theory -> sort -> Pretty.T
  val string_of_term_global: theory -> term -> string
  val string_of_typ_global: theory -> typ -> string
  val string_of_sort_global: theory -> sort -> string
  val pretty_flexpair: Proof.context -> term * term -> Pretty.T list
  type syntax
  val cache_persistent: bool Unsynchronized.ref
  val cache_syntax: syntax -> unit
  val eq_syntax: syntax * syntax -> bool
  datatype approx = Prefix of string | Infix of {assoc: Printer.assoc, delim: string, pri: int}
  val get_approx: syntax -> string -> approx option
  val get_consts: syntax -> string -> string list
  val is_const: syntax -> string -> bool
  val is_keyword: syntax -> string -> bool
  val tokenize: syntax -> {raw: bool} -> Symbol_Pos.T list -> Lexicon.token list
  val parse: syntax -> string -> Lexicon.token list -> Parser.tree list
  val parse_ast_translation: syntax -> string -> (Proof.context -> Ast.ast list -> Ast.ast) option
  val parse_rules: syntax -> string -> (Ast.ast * Ast.ast) list
  val parse_translation: syntax -> string -> (Proof.context -> term list -> term) option
  val print_translation: syntax -> string ->
    Proof.context -> typ -> term list -> term  (*exception Match*)
  val print_rules: syntax -> string -> (Ast.ast * Ast.ast) list
  val print_ast_translation: syntax -> string ->
    Proof.context -> Ast.ast list -> Ast.ast  (*exception Match*)
  val prtabs: syntax -> Printer.prtabs
  val print_mode_tabs: syntax -> Printer.prtab list
  type mode
  val mode_default: mode
  val mode_input: mode
  val empty_syntax: syntax
  val merge_syntax: syntax * syntax -> syntax
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val map_trrule: ('a -> 'b) -> 'a trrule -> 'b trrule
  val update_trfuns: Proof.context ->
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list -> syntax -> syntax
  val update_type_gram: Proof.context -> bool -> mode -> (string * typ * mixfix) list ->
    syntax -> syntax
  val update_const_gram: Proof.context -> bool -> string list ->
    mode -> (string * typ * mixfix) list -> syntax -> syntax
  val update_consts: Proof.context -> (string * string list) list -> syntax -> syntax
  val update_trrules: Proof.context -> bool -> Ast.ast trrule list -> syntax -> syntax
  val get_polarity: Proof.context -> bool
  val set_polarity: bool -> Proof.context -> Proof.context
  val set_polarity_generic: bool -> Context.generic -> Context.generic
  val effective_polarity: Proof.context -> bool -> bool
  val effective_polarity_global: theory -> bool -> bool
  val effective_polarity_generic: Context.generic -> bool -> bool
  val const: string -> term
  val free: string -> term
  val var: indexname -> term
end;

structure Syntax: SYNTAX =
struct


(** inner syntax operations **)

(* operations *)

datatype 'a trrule =
  Parse_Rule of 'a * 'a |
  Print_Rule of 'a * 'a |
  Parse_Print_Rule of 'a * 'a;

type operations =
 {parse_trrule: Proof.context -> (string * string) trrule -> Ast.ast trrule,
  parse_sort: Proof.context -> string -> sort,
  parse_typ: Proof.context -> string -> typ,
  parse_term: Proof.context -> string -> term,
  parse_prop: Proof.context -> string -> term,
  unparse_sort: Proof.context -> sort -> Pretty.T,
  unparse_typ: Proof.context -> typ -> Pretty.T,
  unparse_term: Proof.context -> term -> Pretty.T,
  check_typs: Proof.context -> typ list -> typ list,
  check_terms: Proof.context -> term list -> term list,
  check_props: Proof.context -> term list -> term list,
  uncheck_typs: Proof.context -> typ list -> typ list,
  uncheck_terms: Proof.context -> term list -> term list};

structure Operations = Theory_Data
(
  type T = operations option;
  val empty = NONE;
  val merge = merge_options;
);

fun install_operations ops =
  Operations.map
    (fn NONE => SOME ops
      | SOME _ => raise Fail "Inner syntax operations already installed");

fun operation which ctxt x =
  (case Operations.get (Proof_Context.theory_of ctxt) of
    NONE => raise Fail "Inner syntax operations not installed"
  | SOME ops => which ops ctxt x);


(* configuration options *)

val root = Config.declare_string ("syntax_root", \<^here>) (K "any");
val ambiguity_warning = Config.declare_bool ("syntax_ambiguity_warning", \<^here>) (K true);
val ambiguity_limit = Config.declare_int ("syntax_ambiguity_limit", \<^here>) (K 10);


(* formal input *)

fun encode_input source =
  let
    val delimited = Input.is_delimited source;
    val pos = Input.pos_of source;
    val text = Input.text_of source;
  in XML.Elem (Markup.input delimited (Position.properties_of pos), [XML.Text text]) end;

val implode_input = encode_input #> YXML.string_of;

local

fun input_range (XML.Elem ((name, props), _)) =
      if name = Markup.inputN
      then (Markup.is_delimited props, Position.range_of_properties props)
      else (false, Position.no_range)
  | input_range (XML.Text _) = (false, Position.no_range);

fun input_source tree =
  let
    val text = XML.content_of [tree];
    val (delimited, range) = input_range tree;
  in Input.source delimited text range end;

in

fun read_input_pos str = #1 (#2 (input_range (YXML.parse str handle Fail msg => error msg)));

fun read_input str = input_source (YXML.parse str handle Fail msg => error msg);

fun parse_input ctxt decode markup parse str =
  let
    fun parse_tree tree =
      let
        val source = input_source tree;
        val syms = Input.source_explode source;
        val pos = Input.pos_of source;
        val _ =
          Context_Position.reports ctxt
            [(pos, Markup.cartouche), (pos, markup (Input.is_delimited source))];
        val _ =
          if Options.default_bool "update_inner_syntax_cartouches" then
            Context_Position.report_text ctxt
              pos Markup.update (cartouche (Symbol_Pos.content syms))
          else ();
      in parse (syms, pos) end;
  in
    (case YXML.parse_body str handle Fail msg => error msg of
      body as [tree as XML.Elem ((name, _), _)] =>
        if name = Markup.inputN then parse_tree tree else decode body
    | [tree as XML.Text _] => parse_tree tree
    | body => decode body)
  end;

end;


(* (un)parsing *)

val parse_trrule = operation #parse_trrule;
val parse_sort = operation #parse_sort;
val parse_typ = operation #parse_typ;
val parse_term = operation #parse_term;
val parse_prop = operation #parse_prop;
val unparse_sort = operation #unparse_sort;
val unparse_typ = operation #unparse_typ;
val unparse_term = operation #unparse_term;


(* (un)checking *)

val check_typs = operation #check_typs;
val check_terms = operation #check_terms;
val check_props = operation #check_props;

val check_typ = singleton o check_typs;
val check_term = singleton o check_terms;
val check_prop = singleton o check_props;

val uncheck_typs = operation #uncheck_typs;
val uncheck_terms = operation #uncheck_terms;


(* derived operations for algebra of sorts *)

local

fun map_sort f S =
  (case f (TFree ("", S)) of
    TFree ("", S') => S'
  | _ => raise TYPE ("map_sort", [TFree ("", S)], []));

in

val check_sort = map_sort o check_typ;
val uncheck_sort = map_sort o singleton o uncheck_typs;

end;


val uncheck_classrel = map o singleton o uncheck_sort;

fun unparse_classrel ctxt cs = Pretty.block (flat
  (separate [Pretty.str " <", Pretty.brk 1] (map (single o unparse_sort ctxt o single) cs)));

fun uncheck_arity ctxt (a, Ss, S) =
  let
    val T = Type (a, replicate (length Ss) dummyT);
    val a' =
      (case singleton (uncheck_typs ctxt) T of
        Type (a', _) => a'
      | T => raise TYPE ("uncheck_arity", [T], []));
    val Ss' = map (uncheck_sort ctxt) Ss;
    val S' = uncheck_sort ctxt S;
  in (a', Ss', S') end;

fun unparse_arity ctxt (a, Ss, S) =
  let
    val prtT = unparse_typ ctxt (Type (a, []));
    val dom =
      if null Ss then []
      else [Pretty.list "(" ")" (map (unparse_sort ctxt) Ss), Pretty.brk 1];
  in Pretty.block ([prtT, Pretty.str " ::", Pretty.brk 1] @ dom @ [unparse_sort ctxt S]) end;


(* read = parse + check *)

fun read_sort ctxt = parse_sort ctxt #> check_sort ctxt;

fun read_typs ctxt =
  grouped 10 Par_List.map_independent (parse_typ ctxt) #> check_typs ctxt;

fun read_terms ctxt =
  grouped 10 Par_List.map_independent (parse_term ctxt) #> check_terms ctxt;

fun read_props ctxt =
  grouped 10 Par_List.map_independent (parse_prop ctxt) #> check_props ctxt;

val read_typ = singleton o read_typs;
val read_term = singleton o read_terms;
val read_prop = singleton o read_props;

val read_sort_global = read_sort o Proof_Context.init_global;
val read_typ_global = read_typ o Proof_Context.init_global;
val read_term_global = read_term o Proof_Context.init_global;
val read_prop_global = read_prop o Proof_Context.init_global;


(* pretty = uncheck + unparse *)

fun pretty_term ctxt = singleton (uncheck_terms ctxt) #> unparse_term ctxt;
fun pretty_typ ctxt = singleton (uncheck_typs ctxt) #> unparse_typ ctxt;
fun pretty_sort ctxt = uncheck_sort ctxt #> unparse_sort ctxt;
fun pretty_classrel ctxt = uncheck_classrel ctxt #> unparse_classrel ctxt;
fun pretty_arity ctxt = uncheck_arity ctxt #> unparse_arity ctxt;

val string_of_term = Pretty.string_of oo pretty_term;
val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_sort = Pretty.string_of oo pretty_sort;
val string_of_classrel = Pretty.string_of oo pretty_classrel;
val string_of_arity = Pretty.string_of oo pretty_arity;


(* global pretty printing *)

val pretty_global = Config.declare_bool ("Syntax.pretty_global", \<^here>) (K false);
val is_pretty_global = Config.apply pretty_global;
val set_pretty_global = Config.put pretty_global;
val init_pretty_global = set_pretty_global true o Proof_Context.init_global;
val init_pretty = Context.cases init_pretty_global I;

val pretty_term_global = pretty_term o init_pretty_global;
val pretty_typ_global = pretty_typ o init_pretty_global;
val pretty_sort_global = pretty_sort o init_pretty_global;

val string_of_term_global = string_of_term o init_pretty_global;
val string_of_typ_global = string_of_typ o init_pretty_global;
val string_of_sort_global = string_of_sort o init_pretty_global;


(* derived operations *)

fun pretty_flexpair ctxt (t, u) =
  [pretty_term ctxt t, Pretty.str " \<equiv>\<^sup>?", Pretty.brk 1, pretty_term ctxt u];



(** keywords **)

abstype keywords = Keywords of Symset.T * Scan.lexicon lazy
with

val empty_keywords =
  Keywords (Symset.empty, Lazy.value Scan.empty_lexicon);

fun make_keywords set =
  let fun lex () = Scan.build_lexicon (set |> Symset.fold (Scan.extend_lexicon o Symbol.explode))
  in Keywords (set, Lazy.lazy lex) end;

fun add_keywords s (keywords as Keywords (set, lex)) =
  if Symset.member set s then keywords
  else
    let
      val set' = Symset.insert s set;
      val lex' = Lazy.map_finished (fn x => Scan.extend_lexicon (Symbol.explode s) x) lex;
    in Keywords (set', lex') end;

fun merge_keywords (keywords1 as Keywords (set1, lex1), keywords2 as Keywords (set2, lex2)) =
  if pointer_eq (keywords1, keywords2) then keywords1
  else if Symset.is_empty set1 then keywords2
  else if Symset.is_empty set2 then keywords1
  else if Symset.subset (set1, set2) then keywords2
  else if Symset.subset (set2, set1) then keywords1
  else
    let
      val set' = Symset.merge (set1, set2);
      val lex' = Lazy.value (Scan.merge_lexicons (apply2 Lazy.force (lex1, lex2)));
    in Keywords (set', lex') end;

fun member_keywords (Keywords (set, _)) = Symset.member set;

fun dest_keywords (Keywords (set, _)) = sort_strings (Symset.dest set);

fun tokenize_keywords (Keywords (_, lex)) = Lexicon.tokenize (Lazy.force lex);

end;



(** tables of translation functions **)

(* parse (ast) translations *)

fun err_dup_trfun name c =
  error ("More than one " ^ name ^ " for " ^ quote c);

fun lookup_tr tab c = Option.map fst (Symtab.lookup tab c);

fun remove_trtab trfuns = fold (Symtab.remove Syntax_Ext.eq_trfun) trfuns;

fun update_trtab name trfuns tab = fold Symtab.update_new trfuns (remove_trtab trfuns tab)
  handle Symtab.DUP c => err_dup_trfun name c;

fun merge_trtabs name tab1 tab2 = Symtab.merge Syntax_Ext.eq_trfun (tab1, tab2)
  handle Symtab.DUP c => err_dup_trfun name c;


(* print (ast) translations *)

fun apply_tr' tab c ctxt T args =
  let
    val fns = map fst (Symtab.lookup_list tab c);
    fun app_first [] = raise Match
      | app_first (f :: fs) = f ctxt T args handle Match => app_first fs;
  in app_first fns end;

fun apply_ast_tr' tab c ctxt args =
  let
    val fns = map fst (Symtab.lookup_list tab c);
    fun app_first [] = raise Match
      | app_first (f :: fs) = f ctxt args handle Match => app_first fs;
  in app_first fns end;

fun update_tr'tab trfuns = fold_rev (Symtab.update_list Syntax_Ext.eq_trfun) trfuns;
fun remove_tr'tab trfuns = fold (Symtab.remove_list Syntax_Ext.eq_trfun) trfuns;
fun merge_tr'tabs tab1 tab2 = Symtab.merge_list Syntax_Ext.eq_trfun (tab1, tab2);



(** tables of translation rules **)

type ruletab = (Ast.ast * Ast.ast) list Symtab.table;

fun dest_ruletab tab = Symtab.dest tab |> sort_by #1 |> maps #2;

val update_ruletab = fold_rev (fn r => Symtab.update_list (op =) (Ast.rule_index r, r));
val remove_ruletab = fold (fn r => Symtab.remove_list (op =) (Ast.rule_index r, r));
fun merge_ruletabs tab1 tab2 = Symtab.merge_list (op =) (tab1, tab2);



(** datatype syntax **)

datatype syntax =
  Syntax of {
    input: Syntax_Ext.xprod list,
    keywords: keywords,
    gram: Parser.gram Synchronized.cache,
    consts: unit Graph.T,
    prmodes: string list,
    parse_ast_trtab: ((Proof.context -> Ast.ast list -> Ast.ast) * stamp) Symtab.table,
    parse_ruletab: ruletab,
    parse_trtab: ((Proof.context -> term list -> term) * stamp) Symtab.table,
    print_trtab: ((Proof.context -> typ -> term list -> term) * stamp) list Symtab.table,
    print_ruletab: ruletab,
    print_ast_trtab: ((Proof.context -> Ast.ast list -> Ast.ast) * stamp) list Symtab.table,
    prtabs: Printer.prtabs} * stamp;

val cache_persistent = Unsynchronized.ref false;

fun cache_eval (gram: Parser.gram Synchronized.cache) =
  Synchronized.cache_eval {persistent = ! cache_persistent} gram;

fun cache_syntax (Syntax ({gram, ...}, _)) = ignore (cache_eval gram);

fun eq_syntax (Syntax (_, s1), Syntax (_, s2)) = s1 = s2;

datatype approx = Prefix of string | Infix of {assoc: Printer.assoc, delim: string, pri: int};
fun get_approx (Syntax ({prtabs, ...}, _)) c =
  (case Printer.get_infix prtabs c of
    SOME infx => SOME (Infix infx)
  | NONE =>
      (case Printer.get_prefix prtabs c of
        SOME prfx => SOME prfx
      | NONE => Printer.get_binder prtabs c)
      |> Option.map Prefix);

fun is_const (Syntax ({consts, ...}, _)) c =
  Graph.defined consts c andalso not (Lexicon.is_marked_entity c);

fun is_keyword (Syntax ({keywords, ...}, _)) = member_keywords keywords;
fun tokenize (Syntax ({keywords, ...}, _)) = tokenize_keywords keywords;
fun parse (Syntax ({gram, ...}, _)) = Parser.parse (cache_eval gram);

fun parse_ast_translation (Syntax ({parse_ast_trtab, ...}, _)) = lookup_tr parse_ast_trtab;
fun parse_translation (Syntax ({parse_trtab, ...}, _)) = lookup_tr parse_trtab;
fun parse_rules (Syntax ({parse_ruletab, ...}, _)) = Symtab.lookup_list parse_ruletab;
fun print_translation (Syntax ({print_trtab, ...}, _)) = apply_tr' print_trtab;
fun print_rules (Syntax ({print_ruletab, ...}, _)) = Symtab.lookup_list print_ruletab;
fun print_ast_translation (Syntax ({print_ast_trtab, ...}, _)) = apply_ast_tr' print_ast_trtab;

fun prtabs (Syntax ({prtabs, ...}, _)) = prtabs;
val print_mode_tabs = Printer.print_mode_tabs o prtabs;

type mode = string * bool;
val mode_default = ("", true);
val mode_input = (Print_Mode.input, true);

fun extend_gram new_xprods old_xprods gram =
  Synchronized.cache (fn () =>
    Parser.make_gram new_xprods old_xprods (Synchronized.cache_peek gram));

fun new_gram new_xprods =
  Synchronized.cache (fn () => Parser.make_gram new_xprods [] NONE);


(* syntax consts *)

fun err_cyclic_consts css =
  error (cat_lines (map (fn cs =>
    "Cycle in syntax consts: " ^ (space_implode " \<leadsto> " (map quote cs))) css));

fun get_consts (Syntax ({consts, ...}, _)) c =
  if Graph.defined consts c
  then filter (Graph.is_minimal consts) (Graph.all_preds consts [c])
  else [c];

fun add_consts (c, bs) consts =
  if c = "" orelse (null bs andalso (Lexicon.is_marked_entity c orelse Graph.defined consts c))
  then consts
  else
    consts
    |> fold (fn a => Graph.default_node (a, ())) (c :: bs)
    |> Graph.add_deps_acyclic (c, bs)
    handle Graph.CYCLES css => err_cyclic_consts css;


(* empty_syntax *)

val empty_syntax = Syntax
  ({input = [],
    keywords = empty_keywords,
    gram = Synchronized.cache (fn () => Parser.empty_gram),
    consts = Graph.empty,
    prmodes = [],
    parse_ast_trtab = Symtab.empty,
    parse_ruletab = Symtab.empty,
    parse_trtab = Symtab.empty,
    print_trtab = Symtab.empty,
    print_ruletab = Symtab.empty,
    print_ast_trtab = Symtab.empty,
    prtabs = Printer.empty_prtabs}, stamp ());


(* update_syntax *)

fun update_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val {input, keywords, gram, consts = consts1, prmodes, parse_ast_trtab, parse_ruletab,
      parse_trtab, print_trtab, print_ruletab, print_ast_trtab, prtabs} = tabs;
    val Syntax_Ext.Syn_Ext {xprods, consts = consts2, parse_ast_translation,
      parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation} = syn_ext;
    val new_xprods =
      if inout then distinct (op =) (filter_out (member (op =) input) xprods) else [];
    fun if_inout xs = if inout then xs else [];
  in
    Syntax
    ({input = new_xprods @ input,
      keywords = (fold o Syntax_Ext.fold_delims) add_keywords new_xprods keywords,
      gram = if null new_xprods then gram else extend_gram new_xprods input gram,
      consts = fold add_consts consts2 consts1,
      prmodes = insert (op =) mode prmodes,
      parse_ast_trtab =
        update_trtab "parse ast translation" (if_inout parse_ast_translation) parse_ast_trtab,
      parse_ruletab = update_ruletab (if_inout parse_rules) parse_ruletab,
      parse_trtab = update_trtab "parse translation" (if_inout parse_translation) parse_trtab,
      print_trtab = update_tr'tab print_translation print_trtab,
      print_ruletab = update_ruletab print_rules print_ruletab,
      print_ast_trtab = update_tr'tab print_ast_translation print_ast_trtab,
      prtabs = Printer.update_prtabs mode xprods prtabs}, stamp ())
  end;


(* remove_syntax *)

fun remove_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val Syntax_Ext.Syn_Ext {xprods, consts = _, parse_ast_translation, parse_rules,
      parse_translation, print_translation, print_rules, print_ast_translation} = syn_ext;
    val {input, keywords, gram, consts, prmodes, parse_ast_trtab, parse_ruletab,
      parse_trtab, print_trtab, print_ruletab, print_ast_trtab, prtabs} = tabs;
    val input' = if inout then subtract (op =) xprods input else input;
    val changed = length input <> length input';
    fun if_inout xs = if inout then xs else [];
  in
    Syntax
    ({input = input',
      keywords =
        if changed
        then make_keywords (Symset.build (input' |> (fold o Syntax_Ext.fold_delims) Symset.insert))
        else keywords,
      gram = if changed then new_gram input' else gram,
      consts = consts,
      prmodes = prmodes,
      parse_ast_trtab = remove_trtab (if_inout parse_ast_translation) parse_ast_trtab,
      parse_ruletab = remove_ruletab (if_inout parse_rules) parse_ruletab,
      parse_trtab = remove_trtab (if_inout parse_translation) parse_trtab,
      print_trtab = remove_tr'tab print_translation print_trtab,
      print_ruletab = remove_ruletab print_rules print_ruletab,
      print_ast_trtab = remove_tr'tab print_ast_translation print_ast_trtab,
      prtabs = Printer.remove_prtabs mode xprods prtabs}, stamp ())
  end;


(* merge_syntax *)

fun merge_syntax (Syntax (tabs1, _), Syntax (tabs2, _)) =
  let
    val {input = input1, keywords = keywords1, gram = gram1, consts = consts1,
      prmodes = prmodes1, parse_ast_trtab = parse_ast_trtab1, parse_ruletab = parse_ruletab1,
      parse_trtab = parse_trtab1, print_trtab = print_trtab1, print_ruletab = print_ruletab1,
      print_ast_trtab = print_ast_trtab1, prtabs = prtabs1} = tabs1;

    val {input = input2, keywords = keywords2, gram = gram2, consts = consts2,
      prmodes = prmodes2, parse_ast_trtab = parse_ast_trtab2, parse_ruletab = parse_ruletab2,
      parse_trtab = parse_trtab2, print_trtab = print_trtab2, print_ruletab = print_ruletab2,
      print_ast_trtab = print_ast_trtab2, prtabs = prtabs2} = tabs2;

    val (input', gram') =
      if pointer_eq (input1, input2) then (input1, gram1)
      else
        (case subtract (op =) input1 input2 of
          [] => (input1, gram1)
        | new_xprods2 =>
            if subset (op =) (input1, input2) then (input2, gram2)
            else
              let
                val input' = new_xprods2 @ input1;
                val gram' = new_gram input';
              in (input', gram') end);
  in
    Syntax
    ({input = input',
      keywords = merge_keywords (keywords1, keywords2),
      gram = gram',
      consts =
        Graph.merge_acyclic (op =) (consts1, consts2)
          handle Graph.CYCLES css => err_cyclic_consts css,
      prmodes = Library.merge (op =) (prmodes1, prmodes2),
      parse_ast_trtab =
        merge_trtabs "parse ast translation" parse_ast_trtab1 parse_ast_trtab2,
      parse_ruletab = merge_ruletabs parse_ruletab1 parse_ruletab2,
      parse_trtab = merge_trtabs "parse translation" parse_trtab1 parse_trtab2,
      print_trtab = merge_tr'tabs print_trtab1 print_trtab2,
      print_ruletab = merge_ruletabs print_ruletab1 print_ruletab2,
      print_ast_trtab = merge_tr'tabs print_ast_trtab1 print_ast_trtab2,
      prtabs = Printer.merge_prtabs (prtabs1, prtabs2)}, stamp ())
  end;



(** print syntax **)

local

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map quote (sort_strings strs));

fun pretty_gram (Syntax (tabs, _)) =
  let
    val {keywords, prmodes, gram, ...} = tabs;
    val prmodes' = sort_strings (filter_out (fn s => s = "") prmodes);
  in
    [Pretty.block (Pretty.breaks
      (Pretty.str "lexicon:" :: map (Pretty.quote o Pretty.keyword1) (dest_keywords keywords))),
      Pretty.big_list "productions:" (Parser.pretty_gram (cache_eval gram)),
      pretty_strs_qs "print modes:" prmodes']
  end;

fun pretty_trans (Syntax (tabs, _)) =
  let
    fun pretty_tab name tab =
      pretty_strs_qs name (sort_strings (Symtab.keys tab));

    fun pretty_ruletab name tab =
      Pretty.big_list name (map (Pretty.item o single o Ast.pretty_rule) (dest_ruletab tab));

    val {consts, parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab,
      print_ruletab, print_ast_trtab, ...} = tabs;
  in
   [pretty_strs_qs "consts:" (sort_strings (Graph.keys consts)),
    pretty_tab "parse_ast_translation:" parse_ast_trtab,
    pretty_ruletab "parse_rules:" parse_ruletab,
    pretty_tab "parse_translation:" parse_trtab,
    pretty_tab "print_translation:" print_trtab,
    pretty_ruletab "print_rules:" print_ruletab,
    pretty_tab "print_ast_translation:" print_ast_trtab]
  end;

in

fun print_gram syn = Pretty.writeln (Pretty.chunks (pretty_gram syn));
fun print_trans syn = Pretty.writeln (Pretty.chunks (pretty_trans syn));
fun print_syntax syn = Pretty.writeln (Pretty.chunks (pretty_gram syn @ pretty_trans syn));

end;



(** prepare translation rules **)

(* rules *)

fun map_trrule f (Parse_Rule (x, y)) = Parse_Rule (f x, f y)
  | map_trrule f (Print_Rule (x, y)) = Print_Rule (f x, f y)
  | map_trrule f (Parse_Print_Rule (x, y)) = Parse_Print_Rule (f x, f y);

fun parse_rule (Parse_Rule pats) = SOME pats
  | parse_rule (Print_Rule _) = NONE
  | parse_rule (Parse_Print_Rule pats) = SOME pats;

fun print_rule (Parse_Rule _) = NONE
  | print_rule (Print_Rule pats) = SOME (swap pats)
  | print_rule (Parse_Print_Rule pats) = SOME (swap pats);


(* check_rules *)

local

fun check_rule rule =
  (case Ast.rule_error rule of
    SOME msg =>
      error ("Error in syntax translation rule: " ^ msg ^ "\n" ^
        Pretty.string_of (Ast.pretty_rule rule))
  | NONE => rule);

in

fun check_rules rules =
 (map check_rule (map_filter parse_rule rules),
  map check_rule (map_filter print_rule rules));

end;



(** modify syntax **)

(* updates *)

fun update_trfuns ctxt = update_syntax mode_default o Syntax_Ext.syn_ext_trfuns ctxt;

fun update_type_gram ctxt add prmode decls =
  (if add then update_syntax else remove_syntax) prmode (Mixfix.syn_ext_types ctxt decls);

fun update_const_gram ctxt add logical_types prmode decls =
  (if add then update_syntax else remove_syntax) prmode
    (Mixfix.syn_ext_consts ctxt logical_types decls);

val update_consts = update_syntax mode_default oo Syntax_Ext.syn_ext_consts;

fun update_trrules ctxt add =
  (if add then update_syntax else remove_syntax) mode_default o
    Syntax_Ext.syn_ext_rules ctxt o check_rules;


(* polarity of declarations: true = add, false = del *)

val polarity = Config.declare_bool ("polarity", Position.none) (K true);

fun get_polarity ctxt = Config.get ctxt polarity;
val set_polarity = Config.put polarity;
val set_polarity_generic = Config.put_generic polarity;

fun effective_polarity ctxt add = get_polarity ctxt = add;
fun effective_polarity_global thy add = Config.get_global thy polarity = add;
val effective_polarity_generic = Context.cases effective_polarity_global effective_polarity;


open Lexicon.Syntax;

end;
