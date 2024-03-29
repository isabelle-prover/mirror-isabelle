(*  Title:      Pure/Syntax/parser.ML
    Author:     Carsten Clasohm, Sonia Mahjoub
    Author:     Makarius

General context-free parser for the inner syntax of terms and types.
*)

signature PARSER =
sig
  type gram
  val empty_gram: gram
  val make_gram: Syntax_Ext.xprod list -> Syntax_Ext.xprod list -> gram option -> gram
  val pretty_gram: gram -> Pretty.T list
  datatype parsetree =
    Node of string * parsetree list |
    Tip of Lexicon.token
  exception PARSETREE of parsetree
  val pretty_parsetree: parsetree -> Pretty.T
  val parse: gram -> string -> Lexicon.token list -> parsetree list
  val branching_level: int Config.T
end;

structure Parser: PARSER =
struct

(** datatype gram **)

(* nonterminals *)

(*production for the NTs are stored in a vector, indexed by the NT tag*)
type nt = int;

type tags = nt Symtab.table;
val tags_empty: tags = Symtab.empty;
fun tags_content (tags: tags) = sort_by #1 (Symtab.dest tags);
fun tags_lookup (tags: tags) = Symtab.lookup tags;
fun tags_insert tag (tags: tags) = Symtab.update_new tag tags;
fun tags_name (tags: tags) =
  the o Inttab.lookup (Inttab.build (Symtab.fold (Inttab.update_new o swap) tags));

type nts = Bitset.T;
val nts_empty: nts = Bitset.empty;
val nts_merge: nts * nts -> nts = Bitset.merge;
fun nts_insert nt : nts -> nts = Bitset.insert nt;
fun nts_member (nts: nts) = Bitset.member nts;
fun nts_fold f (nts: nts) = Bitset.fold f nts;
fun nts_subset (nts1: nts, nts2: nts) = Bitset.forall (nts_member nts2) nts1;
fun nts_is_empty (nts: nts) = Bitset.is_empty nts;
fun nts_is_unique (nts: nts) = Bitset.is_unique nts;


(* tokens *)

structure Tokens = Set(type key = Lexicon.token val ord = Lexicon.tokens_match_ord);

fun tokens_find P tokens = Tokens.get_first (fn tok => if P tok then SOME tok else NONE) tokens;
fun tokens_add (nt: nt, tokens) = if Tokens.is_empty tokens then I else cons (nt, tokens);


(* productions *)

datatype symb =
  Terminal of Lexicon.token |
  Nonterminal of nt * int;  (*(tag, prio)*)

structure Prods = Table(Tokens.Key);
type prods = (symb list * string * int) list Prods.table;  (*start_token ~> [(rhs, name, prio)]*)

val prods_empty: prods = Prods.empty;
fun prods_lookup (prods: prods) = Prods.lookup_list prods;
fun prods_update entry : prods -> prods = Prods.update entry;
fun prods_content (prods: prods) = distinct (op =) (maps #2 (Prods.dest prods));

type nt_gram = (nts * Tokens.T) * prods; (*dependent_nts, start_tokens, prods*)
  (*depent_nts is a set of all NTs whose lookahead depends on this NT's lookahead*)

val nt_gram_empty: nt_gram = ((nts_empty, Tokens.empty), prods_empty);

type chains = unit Int_Graph.T;
fun chains_preds (chains: chains) = Int_Graph.immediate_preds chains;
fun chains_all_preds (chains: chains) = Int_Graph.all_preds chains;
fun chains_all_succs (chains: chains) = Int_Graph.all_succs chains;
val chains_empty: chains = Int_Graph.empty;
fun chains_member (chains: chains) = Int_Graph.is_edge chains;
fun chains_declare nt : chains -> chains = Int_Graph.default_node (nt, ());
fun chains_insert (from, to) =
  chains_declare from #> chains_declare to #> Int_Graph.add_edge (from, to);

datatype gram =
  Gram of
   {nt_count: int,
    prod_count: int,
    tags: tags,
    chains: chains,
    lambdas: nts,
    prods: nt_gram Vector.vector};
    (*"tags" is used to map NT names (i.e. strings) to tags;
     chain productions are not stored as normal productions
     but instead as an entry in "chains": from -> to;
     lambda productions are stored as normal productions
     and also as an entry in "lambdas"*)

(*productions for which no starting token is
  known yet are associated with this token*)
val unknown_start = Lexicon.eof;

fun get_start tks =
  (case Tokens.min tks of
    SOME tk => tk
  | NONE => unknown_start);

fun add_production array_prods (lhs, new_prod as (rhs, _, pri)) (chains, lambdas) =
  let
    (*store chain if it does not already exist*)
    val (chain, new_chain, chains') =
      (case (pri, rhs) of
        (~1, [Nonterminal (from, ~1)]) =>
          if chains_member chains (from, lhs)
          then (SOME from, false, chains)
          else (SOME from, true, chains_insert (from, lhs) chains)
      | _ =>
        let
          val chains' = chains
            |> chains_declare lhs
            |> fold (fn Nonterminal (nt, _) => chains_declare nt | _ => I) rhs;
        in (NONE, false, chains') end);

    (*propagate new chain in lookahead and lambdas;
      added_starts is used later to associate existing
      productions with new starting tokens*)
    val (added_starts, lambdas') =
      if not new_chain then ([], lambdas)
      else
        let (*lookahead of chain's source*)
          val ((_, from_tks), _) = Array.nth array_prods (the chain);

          (*copy from's lookahead to chain's destinations*)
          fun copy_lookahead to =
            let
              val ((to_nts, to_tks), ps) = Array.nth array_prods to;

              val new_tks = Tokens.subtract to_tks from_tks;  (*added lookahead tokens*)
              val to_tks' = Tokens.merge (to_tks, new_tks);
              val _ = Array.upd array_prods to ((to_nts, to_tks'), ps);
            in tokens_add (to, new_tks) end;

          val tos = chains_all_succs chains' [lhs];
        in
          (fold copy_lookahead tos [],
            lambdas |> nts_member lambdas lhs ? fold nts_insert tos)
        end;

    (*test if new production can produce lambda
      (rhs must either be empty or only consist of lambda NTs)*)
    val new_lambdas =
      if forall
        (fn Nonterminal (id, _) => nts_member lambdas' id
          | Terminal _ => false) rhs
      then SOME (filter_out (nts_member lambdas') (chains_all_succs chains' [lhs]))
      else NONE;
    val lambdas'' = fold nts_insert (these new_lambdas) lambdas';

    (*list optional terminal and all nonterminals on which the lookahead
      of a production depends*)
    fun lookahead_dependency _ [] nts = (NONE, nts)
      | lookahead_dependency _ (Terminal tk :: _) nts = (SOME tk, nts)
      | lookahead_dependency lambdas (Nonterminal (nt, _) :: symbs) nts =
          if nts_member lambdas nt then
            lookahead_dependency lambdas symbs (nts_insert nt nts)
          else (NONE, nts_insert nt nts);

    (*get all known starting tokens for a nonterminal*)
    fun starts_for_nt nt = snd (fst (Array.nth array_prods nt));

    (*update prods, lookaheads, and lambdas according to new lambda NTs*)
    val (added_starts', lambdas') =
      let
        (*propagate added lambda NT*)
        fun propagate_lambda [] added_starts lambdas = (added_starts, lambdas)
          | propagate_lambda (l :: ls) added_starts lambdas =
              let
                (*get lookahead for lambda NT*)
                val ((dependent, l_starts), _) = Array.nth array_prods l;

                (*check productions whose lookahead may depend on lambda NT*)
                fun examine_prods [] add_lambda nt_dependencies added_tks nt_prods =
                      (add_lambda, nt_dependencies, added_tks, nt_prods)
                  | examine_prods ((p as (rhs, _, _)) :: ps) add_lambda
                        nt_dependencies added_tks nt_prods =
                      let val (tk, nts) = lookahead_dependency lambdas rhs nts_empty in
                        if nts_member nts l then       (*update production's lookahead*)
                          let
                            val new_lambda =
                              is_none tk andalso nts_subset (nts, lambdas);

                            val new_tks =
                              Tokens.empty
                              |> fold Tokens.insert (the_list tk)
                              |> nts_fold (curry Tokens.merge o starts_for_nt) nts
                              |> Tokens.subtract l_starts;

                            val added_tks' = Tokens.merge (added_tks, new_tks);

                            val nt_dependencies' = nts_merge (nt_dependencies, nts);

                            (*associate production with new starting tokens*)
                            fun copy tk nt_prods =
                              prods_update (tk, p :: prods_lookup nt_prods tk) nt_prods;

                            val nt_prods' = nt_prods
                              |> Tokens.fold copy new_tks
                              |> new_lambda ? copy Lexicon.dummy;
                          in
                            examine_prods ps (add_lambda orelse new_lambda)
                              nt_dependencies' added_tks' nt_prods'
                          end
                        else (*skip production*)
                          examine_prods ps add_lambda nt_dependencies added_tks nt_prods
                      end;

                (*check each NT whose lookahead depends on new lambda NT*)
                fun process_nts nt (added_lambdas, added_starts) =
                  let
                    val ((old_nts, old_tks), nt_prods) = Array.nth array_prods nt;

                    (*existing productions whose lookahead may depend on l*)
                    val tk_prods = prods_lookup nt_prods (get_start l_starts);

                    (*add_lambda is true if an existing production of the nt
                      produces lambda due to the new lambda NT l*)
                    val (add_lambda, nt_dependencies, added_tks, nt_prods') =
                      examine_prods tk_prods false nts_empty Tokens.empty nt_prods;

                    val new_nts = nts_merge (old_nts, nt_dependencies);
                    val new_tks = Tokens.merge (old_tks, added_tks);

                    val added_lambdas' = added_lambdas |> add_lambda ? cons nt;
                    val _ = Array.upd array_prods nt ((new_nts, new_tks), nt_prods');
                      (*N.B. that because the tks component
                        is used to access existing
                        productions we have to add new
                        tokens at the _end_ of the list*)
                    val added_starts' = tokens_add (nt, added_tks) added_starts;
                  in (added_lambdas', added_starts') end;

                val (added_lambdas, added_starts') =
                  nts_fold process_nts dependent ([], added_starts);
                val added_lambdas' = filter_out (nts_member lambdas) added_lambdas;
              in
                propagate_lambda (ls @ added_lambdas') added_starts'
                  (fold nts_insert added_lambdas' lambdas)
              end;
      in
        propagate_lambda
          (nts_fold (fn l => not (nts_member lambdas l) ? cons l) lambdas'' [])
          added_starts lambdas''
      end;

    (*insert production into grammar*)
    val added_starts' =
      if is_some chain then added_starts'  (*don't store chain production*)
      else
        let
          (*lookahead tokens of new production and on which
            NTs lookahead depends*)
          val (start_tk, start_nts) = lookahead_dependency lambdas' rhs nts_empty;

          val start_tks =
            Tokens.empty
            |> fold Tokens.insert (the_list start_tk)
            |> nts_fold (curry Tokens.merge o starts_for_nt) start_nts;

          val start_tks' =
            start_tks
            |> (if is_some new_lambdas then Tokens.insert Lexicon.dummy
                else if Tokens.is_empty start_tks then Tokens.insert unknown_start
                else I);

          (*add lhs NT to list of dependent NTs in lookahead*)
          fun add_nts nt initial =
            (if initial then
              let val ((old_nts, old_tks), ps) = Array.nth array_prods nt in
                if nts_member old_nts lhs then ()
                else Array.upd array_prods nt ((nts_insert lhs old_nts, old_tks), ps)
              end
             else (); false);

          (*add new start tokens to chained NTs' lookahead list;
            also store new production for lhs NT*)
          fun add_tks [] added = added
            | add_tks (nt :: nts) added =
                let
                  val ((old_nts, old_tks), nt_prods) = Array.nth array_prods nt;

                  val new_tks = Tokens.subtract old_tks start_tks;

                  (*store new production*)
                  fun store tk (prods, _) =
                    let
                      val tk_prods = prods_lookup prods tk;
                      val tk_prods' = new_prod :: tk_prods;
                      val prods' = prods_update (tk, tk_prods') prods;
                    in (prods', true) end;

                  val (nt_prods', changed) = (nt_prods, false)
                    |> nt = lhs ? Tokens.fold store start_tks';
                  val _ =
                    if not changed andalso Tokens.is_empty new_tks then ()
                    else Array.upd array_prods nt ((old_nts, Tokens.merge (old_tks, new_tks)), nt_prods');
                in add_tks nts (tokens_add (nt, new_tks) added) end;
          val _ = nts_fold add_nts start_nts true;
        in add_tks (chains_all_succs chains' [lhs]) [] end;

    (*associate productions with new lookaheads*)
    val _ =
      let
        (*propagate added start tokens*)
        fun add_starts [] = ()
          | add_starts ((changed_nt, new_tks) :: starts) =
              let
                (*token under which old productions which
                  depend on changed_nt could be stored*)
                val key =
                  tokens_find (not o Tokens.member new_tks) (starts_for_nt changed_nt)
                  |> the_default unknown_start;

                (*copy productions whose lookahead depends on changed_nt;
                  if key = SOME unknown_start then tk_prods is used to hold
                  the productions not copied*)
                fun update_prods [] result = result
                  | update_prods ((p as (rhs, _: string, _: nt)) :: ps)
                        (tk_prods, nt_prods) =
                      let
                        (*lookahead dependency for production*)
                        val (tk, depends) = lookahead_dependency lambdas' rhs nts_empty;

                        (*test if this production has to be copied*)
                        val update = nts_member depends changed_nt;

                        (*test if production could already be associated with
                          a member of new_tks*)
                        val lambda =
                          not (nts_is_unique depends) orelse
                          not (nts_is_empty depends) andalso is_some tk
                          andalso Tokens.member new_tks (the tk);

                        (*associate production with new starting tokens*)
                        fun copy tk nt_prods =
                          let
                            val tk_prods = prods_lookup nt_prods tk;
                            val tk_prods' =
                              if not lambda then p :: tk_prods
                              else insert (op =) p tk_prods;
                               (*if production depends on lambda NT we
                                 have to look for duplicates*)
                          in prods_update (tk, tk_prods') nt_prods end;
                        val result =
                          if update then (tk_prods, Tokens.fold copy new_tks nt_prods)
                          else if key = unknown_start then (p :: tk_prods, nt_prods)
                          else (tk_prods, nt_prods);
                      in update_prods ps result end;

                (*copy existing productions for new starting tokens*)
                fun process_nts nt =
                  let
                    val ((nts, tks), nt_prods) = Array.nth array_prods nt;

                    val tk_prods = prods_lookup nt_prods key;

                    (*associate productions with new lookahead tokens*)
                    val (tk_prods', nt_prods') = update_prods tk_prods ([], nt_prods);

                    val nt_prods'' =
                      if key = unknown_start then
                        prods_update (key, tk_prods') nt_prods'
                      else nt_prods';

                    val added_tks = Tokens.subtract tks new_tks;
                    val tks' = Tokens.merge (tks, added_tks);
                    val _ = Array.upd array_prods nt ((nts, tks'), nt_prods'');
                  in tokens_add (nt, added_tks) end;

                val ((dependent, _), _) = Array.nth array_prods changed_nt;
              in add_starts (starts @ nts_fold process_nts dependent []) end;
      in add_starts added_starts' end;
  in (chains', lambdas') end;


(* pretty_gram *)

fun pretty_gram (Gram {tags, prods, chains, ...}) =
  let
    val print_nt = tags_name tags;
    fun print_pri p = if p < 0 then "" else Symbol.make_sup ("(" ^ string_of_int p ^ ")");

    fun pretty_symb (Terminal tok) =
          if Lexicon.is_literal tok
          then Pretty.quote (Pretty.keyword1 (Lexicon.str_of_token tok))
          else Pretty.str (Lexicon.str_of_token tok)
      | pretty_symb (Nonterminal (tag, p)) = Pretty.str (print_nt tag ^ print_pri p);

    fun pretty_const "" = []
      | pretty_const c = [Pretty.str ("\<^bold>\<Rightarrow> " ^ quote c)];

    fun prod_of_chain from = ([Nonterminal (from, ~1)], "", ~1);

    fun pretty_prod (name, tag) =
      (prods_content (#2 (Vector.nth prods tag)) @ map prod_of_chain (chains_preds chains tag))
      |> map (fn (symbs, const, p) =>
          Pretty.block (Pretty.breaks
            (Pretty.str (name ^ print_pri p ^ " =") :: map pretty_symb symbs @ pretty_const const)));
  in maps pretty_prod (tags_content tags) end;



(** operations on grammars **)

val empty_gram =
  Gram
   {nt_count = 0,
    prod_count = 0,
    tags = tags_empty,
    chains = chains_empty,
    lambdas = nts_empty,
    prods = Vector.fromList [nt_gram_empty]};

fun extend_gram xprods (Gram {nt_count, prod_count, tags, chains, lambdas, prods}) =
  let
    (*Get tag for existing nonterminal or create a new one*)
    fun get_tag nt_count tags nt =
      (case tags_lookup tags nt of
        SOME tag => (nt_count, tags, tag)
      | NONE => (nt_count + 1, tags_insert (nt, nt_count) tags, nt_count));

    (*Convert symbols to the form used by the parser;
      delimiters and predefined terms are stored as terminals,
      nonterminals are converted to integer tags*)
    fun symb_of [] nt_count tags result = (nt_count, tags, rev result)
      | symb_of (Syntax_Ext.Delim s :: ss) nt_count tags result =
          symb_of ss nt_count tags (Terminal (Lexicon.literal s) :: result)
      | symb_of (Syntax_Ext.Argument (s, p) :: ss) nt_count tags result =
          let
            val (nt_count', tags', new_symb) =
              (case Lexicon.get_terminal s of
                NONE =>
                  let val (nt_count', tags', s_tag) = get_tag nt_count tags s;
                  in (nt_count', tags', Nonterminal (s_tag, p)) end
              | SOME tk => (nt_count, tags, Terminal tk));
          in symb_of ss nt_count' tags' (new_symb :: result) end
      | symb_of (_ :: ss) nt_count tags result = symb_of ss nt_count tags result;

    (*Convert list of productions by invoking symb_of for each of them*)
    fun prod_of [] nt_count prod_count tags result =
          (nt_count, prod_count, tags, result)
      | prod_of (Syntax_Ext.XProd (lhs, xsymbs, const, pri) :: ps)
            nt_count prod_count tags result =
          let
            val (nt_count', tags', lhs_tag) = get_tag nt_count tags lhs;
            val (nt_count'', tags'', prods) = symb_of xsymbs nt_count' tags' [];
          in
            prod_of ps nt_count'' (prod_count + 1) tags''
              ((lhs_tag, (prods, const, pri)) :: result)
          end;

    val (nt_count', prod_count', tags', xprods') =
      prod_of xprods nt_count prod_count tags [];

    val array_prods' =
      Array.tabulate (nt_count', fn i =>
        if i < nt_count then Vector.nth prods i
        else nt_gram_empty);

    val (chains', lambdas') =
      (chains, lambdas) |> fold (add_production array_prods') xprods';
  in
    Gram
     {nt_count = nt_count',
      prod_count = prod_count',
      tags = tags',
      chains = chains',
      lambdas = lambdas',
      prods = Array.vector array_prods'}
  end;

fun make_gram [] _ (SOME gram) = gram
  | make_gram new_xprods _ (SOME gram) = extend_gram new_xprods gram
  | make_gram [] [] NONE = empty_gram
  | make_gram new_xprods old_xprods NONE = extend_gram (new_xprods @ old_xprods) empty_gram;



(** parser **)

(* parsetree *)

datatype parsetree =
  Node of string * parsetree list |
  Tip of Lexicon.token;

exception PARSETREE of parsetree;

fun pretty_parsetree parsetree =
  let
    fun pretty (Node (c, pts)) =
          [Pretty.enclose "(" ")" (Pretty.breaks (Pretty.quote (Pretty.str c) :: maps pretty pts))]
      | pretty (Tip tok) =
          if Lexicon.valued_token tok then [Pretty.str (Lexicon.str_of_token tok)] else [];
  in (case pretty parsetree of [prt] => prt | _ => raise PARSETREE parsetree) end;


(* parser state *)

type state =
  nt * int *    (*identification and production precedence*)
  parsetree list *  (*already parsed nonterminals on rhs*)
  symb list *       (*rest of rhs*)
  string *          (*name of production*)
  int;              (*index for previous state list*)


(*Get all rhss with precedence >= min_prec*)
fun get_RHS min_prec = filter (fn (_, _, prec: int) => prec >= min_prec);

(*Get all rhss with precedence >= min_prec and < max_prec*)
fun get_RHS' min_prec max_prec =
  filter (fn (_, _, prec: int) => prec >= min_prec andalso prec < max_prec);

(*Make states using a list of rhss*)
fun mk_states i lhs_ID rhss =
  let fun mk_state (rhs, id, prod_prec) = (lhs_ID, prod_prec, [], rhs, id, i);
  in map mk_state rhss end;

(*Add parse tree to list and eliminate duplicates
  saving the maximum precedence*)
fun conc (t: parsetree list, prec: int) [] = (NONE, [(t, prec)])
  | conc (t, prec) ((t', prec') :: ts) =
      if t = t' then
        (SOME prec',
          if prec' >= prec then (t', prec') :: ts
          else (t, prec) :: ts)
      else
        let val (n, ts') = conc (t, prec) ts
        in (n, (t', prec') :: ts') end;

(*Update entry in used*)
fun update_trees (A, t) used =
  let
    val (i, ts) = the (Inttab.lookup used A);
    val (n, ts') = conc t ts;
  in (n, Inttab.update (A, (i, ts')) used) end;

(*Replace entry in used*)
fun update_prec (A, prec) =
  Inttab.map_entry A (fn (_, ts) => (prec, ts));

fun getS A max_prec NONE Si =
      filter
        (fn (_, _, _, Nonterminal (B, prec) :: _, _, _) => A = B andalso prec <= max_prec
          | _ => false) Si
  | getS A max_prec (SOME min_prec) Si =
      filter
        (fn (_, _, _, Nonterminal (B, prec) :: _, _, _) =>
            A = B andalso prec > min_prec andalso prec <= max_prec
          | _ => false) Si;

fun get_states Estate j A max_prec =
  filter
    (fn (_, _, _, Nonterminal (B, prec) :: _, _, _) => A = B andalso prec <= max_prec
      | _ => false)
    (Array.nth Estate j);


fun movedot_term c (A, j, ts, Terminal a :: sa, id, i) =
  if Lexicon.valued_token c orelse id <> ""
  then (A, j, Tip c :: ts, sa, id, i)
  else (A, j, ts, sa, id, i);

fun movedot_nonterm tt (A, j, ts, Nonterminal _ :: sa, id, i) =
  (A, j, tt @ ts, sa, id, i);

fun movedot_lambda [] _ = []
  | movedot_lambda ((t, ki) :: ts) (state as (B, j, tss, Nonterminal (A, k) :: sa, id, i)) =
      if k <= ki then (B, j, t @ tss, sa, id, i) :: movedot_lambda ts state
      else movedot_lambda ts state;


(*trigger value for warnings*)
val branching_level = Config.declare_int ("syntax_branching_level", \<^here>) (K 600);

(*get all productions of a NT and NTs chained to it which can
  be started by specified token*)
fun prods_for (Gram {prods, chains, ...}) tk nt =
  let
    fun token_prods prods =
      fold cons (prods_lookup prods tk) #>
      fold cons (prods_lookup prods Lexicon.dummy);
    fun nt_prods nt = #2 (Vector.nth prods nt);
  in fold (token_prods o nt_prods) (chains_all_preds chains [nt]) [] end;


fun PROCESSS gram Estate i c states =
  let
    fun processS _ [] (Si, Sii) = (Si, Sii)
      | processS used (S :: States) (Si, Sii) =
          (case S of
            (_, _, _, Nonterminal (nt, min_prec) :: _, _, _) =>
              let (*predictor operation*)
                val (used', new_states) =
                  (case Inttab.lookup used nt of
                    SOME (used_prec, l) => (*nonterminal has been processed*)
                      if used_prec <= min_prec then
                        (*wanted precedence has been processed*)
                        (used, movedot_lambda l S)
                      else (*wanted precedence hasn't been parsed yet*)
                        let
                          val tk_prods = prods_for gram c nt;
                          val States' =
                            mk_states i nt (get_RHS' min_prec used_prec tk_prods);
                        in (update_prec (nt, min_prec) used, movedot_lambda l S @ States') end
                  | NONE => (*nonterminal is parsed for the first time*)
                      let
                        val tk_prods = prods_for gram c nt;
                        val States' = mk_states i nt (get_RHS min_prec tk_prods);
                      in (Inttab.update (nt, (min_prec, [])) used, States') end);
              in
                processS used' (new_states @ States) (S :: Si, Sii)
              end
          | (_, _, _, Terminal a :: _, _, _) => (*scanner operation*)
              processS used States
                (S :: Si,
                  if Lexicon.tokens_match_ord (a, c) = EQUAL then movedot_term c S :: Sii else Sii)
          | (A, prec, ts, [], id, j) => (*completer operation*)
              let val tt = if id = "" then ts else [Node (id, rev ts)] in
                if j = i then (*lambda production?*)
                  let
                    val (prec', used') = update_trees (A, (tt, prec)) used;
                    val Slist = getS A prec prec' Si;
                    val States' = map (movedot_nonterm tt) Slist;
                  in processS used' (States' @ States) (S :: Si, Sii) end
                else
                  let val Slist = get_states Estate j A prec
                  in processS used (map (movedot_nonterm tt) Slist @ States) (S :: Si, Sii) end
              end)
  in processS Inttab.empty states ([], []) end;


fun produce gram stateset i indata prev_token =
  (case Array.nth stateset i of
    [] =>
      let
        val toks = if Lexicon.is_eof prev_token then indata else prev_token :: indata;
        val pos = Position.here (Lexicon.pos_of_token prev_token);
      in
        if null toks then
          error ("Inner syntax error: unexpected end of input" ^ pos)
        else
          error ("Inner syntax error" ^ pos ^
            Markup.markup Markup.no_report
              ("\n" ^ Pretty.string_of
                (Pretty.block [
                  Pretty.str "at", Pretty.brk 1,
                  Pretty.block
                   (Pretty.str "\"" ::
                    Pretty.breaks (map (Pretty.str o Lexicon.str_of_token) (#1 (split_last toks))) @
                    [Pretty.str "\""])])))
      end
  | s =>
      (case indata of
        [] => s
      | c :: cs =>
          let
            val (si, sii) = PROCESSS gram stateset i c s;
            val _ = Array.upd stateset i si;
            val _ = Array.upd stateset (i + 1) sii;
          in produce gram stateset (i + 1) cs c end));


fun get_trees states = map_filter (fn (_, _, [pt], _, _, _) => SOME pt | _ => NONE) states;

fun earley (gram as Gram {tags, ...}) startsymbol indata =
  let
    val start_tag =
      (case tags_lookup tags startsymbol of
        SOME tag => tag
      | NONE => error ("Inner syntax: bad grammar root symbol " ^ quote startsymbol));
    val S0 = [(~1, 0, [], [Nonterminal (start_tag, 0), Terminal Lexicon.eof], "", 0)];
    val s = length indata + 1;
    val Estate = Array.array (s, []);
    val _ = Array.upd Estate 0 S0;
  in
    get_trees (produce gram Estate 0 indata Lexicon.eof)
  end;


fun parse gram start toks =
  let
    val end_pos =
      (case try List.last toks of
        NONE => Position.none
      | SOME tok => Lexicon.end_pos_of_token tok);
    val r =
      (case earley gram start (toks @ [Lexicon.mk_eof end_pos]) of
        [] => raise Fail "Inner syntax: no parse trees"
      | pts => pts);
  in r end;

end;
