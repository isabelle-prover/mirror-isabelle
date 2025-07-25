(*  Title:      Pure/Isar/context_rules.ML
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Makarius

Declarations of intro/elim/dest rules in Pure (see also
Provers/classical.ML for a more specialized version of the same idea).
*)

signature CONTEXT_RULES =
sig
  val netpair_bang: Proof.context -> Bires.netpair
  val netpair: Proof.context -> Bires.netpair
  val find_rules_netpair: Proof.context -> bool -> thm list -> term -> Bires.netpair -> thm list
  val find_rules: Proof.context -> bool -> thm list -> term -> thm list list
  val declared_rule: Context.generic -> thm -> bool
  val print_rules: Proof.context -> unit
  val addSWrapper: (Proof.context -> (int -> tactic) -> int -> tactic) -> theory -> theory
  val addWrapper: (Proof.context -> (int -> tactic) -> int -> tactic) -> theory -> theory
  val Swrap: Proof.context -> (int -> tactic) -> int -> tactic
  val wrap: Proof.context -> (int -> tactic) -> int -> tactic
  val intro_bang: int option -> attribute
  val elim_bang: int option -> attribute
  val dest_bang: int option -> attribute
  val intro: int option -> attribute
  val elim: int option -> attribute
  val dest: int option -> attribute
  val intro_query: int option -> attribute
  val elim_query: int option -> attribute
  val dest_query: int option -> attribute
  val rule_del: attribute
  val add: (int option -> attribute) -> (int option -> attribute) -> (int option -> attribute) ->
    attribute context_parser
end;

structure Context_Rules: CONTEXT_RULES =
struct


(** rule declaration contexts **)

(* rule declarations *)

type decl = thm Bires.decl;
type decls = thm Bires.decls;

fun init_decl kind opt_weight th : decl =
  let val weight = opt_weight |> \<^if_none>\<open>Bires.subgoals_of (Bires.kind_rule kind th)\<close>;
  in {kind = kind, tag = Bires.weight_tag weight, info = th} end;

fun insert_decl ({kind, tag, info = th}: decl) =
  Bires.insert_tagged_rule (tag, Bires.kind_rule kind th);

fun remove_decl ({tag = {index, ...}, info = th, ...}: decl) =
  Bires.delete_tagged_rule (index, th);


(* context data *)

datatype rules = Rules of
 {decls: decls,
  netpairs: Bires.netpair list,
  wrappers:
    ((Proof.context -> (int -> tactic) -> int -> tactic) * stamp) list *
    ((Proof.context -> (int -> tactic) -> int -> tactic) * stamp) list};

fun make_rules decls netpairs wrappers =
  Rules {decls = decls, netpairs = netpairs, wrappers = wrappers};

fun add_rule kind opt_weight th (rules as Rules {decls, netpairs, wrappers}) =
  let
    val th' = Thm.trim_context th;
    val th'' = Thm.trim_context (Bires.kind_make_elim kind th);
    val decl' = init_decl kind opt_weight th'';
  in
    (case Bires.extend_decls (th', decl') decls of
      (NONE, _) => rules
    | (SOME new_decl, decls') =>
        let val netpairs' = Bires.kind_map kind (insert_decl new_decl) netpairs
        in make_rules decls' netpairs' wrappers end)
  end;

fun del_rule th (rules as Rules {decls, netpairs, wrappers}) =
  (case Bires.remove_decls th decls of
    ([], _) => rules
  | (old_decls, decls') =>
      let
        val netpairs' =
          fold (fn decl as {kind, ...} => Bires.kind_map kind (remove_decl decl))
            old_decls netpairs;
      in make_rules decls' netpairs' wrappers end);


structure Data = Generic_Data
(
  type T = rules;
  val empty = make_rules Bires.empty_decls (Bires.kind_values Bires.empty_netpair) ([], []);
  fun merge (rules1, rules2) =
    if pointer_eq (rules1, rules2) then rules1
    else
    let
      val Rules {decls = decls1, netpairs = netpairs1, wrappers = (ws1, ws1')} = rules1;
      val Rules {decls = decls2, netpairs = _, wrappers = (ws2, ws2')} = rules2;
      val (new_rules, decls) = Bires.merge_decls (decls1, decls2);
      val netpairs =
        netpairs1 |> map_index (uncurry (fn i =>
          new_rules |> fold (fn decl =>
            if Bires.kind_index (#kind decl) = i then insert_decl decl else I)))
      val wrappers =
       (Library.merge (eq_snd (op =)) (ws1, ws2),
        Library.merge (eq_snd (op =)) (ws1', ws2'));
    in make_rules decls netpairs wrappers end;
);

fun declared_rule context =
  let val Rules {decls, ...} =  Data.get context
  in Bires.has_decls decls end;

fun print_rules ctxt =
  let val Rules {decls, ...} = Data.get (Context.Proof ctxt)
  in Pretty.writeln (Pretty.chunks (Bires.pretty_decls ctxt decls)) end;


(* access data *)

fun netpairs ctxt = let val Rules {netpairs, ...} = Data.get (Context.Proof ctxt) in netpairs end;
val netpair_bang = hd o netpairs;
val netpair = hd o tl o netpairs;


(* retrieving rules *)

local

fun order weighted =
  make_order_list (Bires.weighted_tag_ord weighted) NONE;

fun may_unify weighted t net =
  map snd (order weighted (Net.unify_term net t));

fun find_erules _ [] = K []
  | find_erules w (fact :: _) = may_unify w (Logic.strip_assums_concl (Thm.prop_of fact));

fun find_irules w goal = may_unify w (Logic.strip_assums_concl goal);

in

fun find_rules_netpair ctxt weighted facts goal (inet, enet) =
  find_erules weighted facts enet @ find_irules weighted goal inet
  |> map (Thm.transfer' ctxt);

fun find_rules ctxt weighted facts goal =
  map (find_rules_netpair ctxt weighted facts goal) (netpairs ctxt);

end;


(* wrappers *)

fun gen_add_wrapper upd w =
  Context.theory_map (Data.map (fn Rules {decls, netpairs, wrappers} =>
    make_rules decls netpairs (upd (fn ws => (w, stamp ()) :: ws) wrappers)));

val addSWrapper = gen_add_wrapper Library.apfst;
val addWrapper = gen_add_wrapper Library.apsnd;


fun gen_wrap which ctxt =
  let val Rules {wrappers, ...} = Data.get (Context.Proof ctxt)
  in fold_rev (fn (w, _) => w ctxt) (which wrappers) end;

val Swrap = gen_wrap #1;
val wrap = gen_wrap #2;



(** attributes **)

(* add and del rules *)

val rule_del = Thm.declaration_attribute (Data.map o del_rule);

fun rule_add k opt_w =
  Thm.declaration_attribute (fn th => Data.map (add_rule k opt_w th o del_rule th));

val intro_bang  = rule_add Bires.intro_bang_kind;
val elim_bang   = rule_add Bires.elim_bang_kind;
val dest_bang   = rule_add Bires.dest_bang_kind;
val intro       = rule_add Bires.intro_kind;
val elim        = rule_add Bires.elim_kind;
val dest        = rule_add Bires.dest_kind;
val intro_query = rule_add Bires.intro_query_kind;
val elim_query  = rule_add Bires.elim_query_kind;
val dest_query  = rule_add Bires.dest_query_kind;

val _ = Theory.setup
  (snd o Global_Theory.add_thms [((Binding.empty, Drule.equal_intr_rule), [intro_query NONE])]);


(* concrete syntax *)

fun add a b c x =
  (Scan.lift ((Args.bang >> K a || Args.query >> K c || Scan.succeed b) --
    Scan.option Parse.nat) >> (fn (f, n) => f n)) x;

val _ = Theory.setup
 (Attrib.setup \<^binding>\<open>intro\<close> (add intro_bang intro intro_query)
    "declaration of Pure introduction rule" #>
  Attrib.setup \<^binding>\<open>elim\<close> (add elim_bang elim elim_query)
    "declaration of Pure elimination rule" #>
  Attrib.setup \<^binding>\<open>dest\<close> (add dest_bang dest dest_query)
    "declaration of Pure destruction rule" #>
  Attrib.setup \<^binding>\<open>rule\<close> (Scan.lift Args.del >> K rule_del)
    "remove declaration of Pure intro/elim/dest rule");

end;
