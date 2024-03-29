(*  Title:      Pure/General/graph.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Directed graphs.
*)

signature GRAPH =
sig
  structure Key: KEY
  type key
  structure Keys:
  sig
    type T
    val is_empty: T -> bool
    val fold: (key -> 'a -> 'a) -> T -> 'a -> 'a
    val fold_rev: (key -> 'a -> 'a) -> T -> 'a -> 'a
    val dest: T -> key list
  end
  type 'a T
  exception DUP of key
  exception SAME
  exception UNDEF of key
  val empty: 'a T
  val is_empty: 'a T -> bool
  val keys: 'a T -> key list
  val get_first: (key * ('a * (Keys.T * Keys.T)) -> 'b option) -> 'a T -> 'b option
  val fold: (key * ('a * (Keys.T * Keys.T)) -> 'b -> 'b) -> 'a T -> 'b -> 'b
  val defined: 'a T -> key -> bool
  val get_entry: 'a T -> key -> key * ('a * (Keys.T * Keys.T))        (*exception UNDEF*)
  val get_node: 'a T -> key -> 'a                                     (*exception UNDEF*)
  val map_node: key -> ('a -> 'a) -> 'a T -> 'a T
  val map: (key -> 'a -> 'b) -> 'a T -> 'b T
  val imm_preds: 'a T -> key -> Keys.T
  val imm_succs: 'a T -> key -> Keys.T
  val immediate_preds: 'a T -> key -> key list
  val immediate_succs: 'a T -> key -> key list
  val all_preds: 'a T -> key list -> key list
  val all_succs: 'a T -> key list -> key list
  val strong_conn: 'a T -> key list list
  val map_strong_conn: ((key * 'a) list -> 'b list) -> 'a T -> 'b T
  val minimals: 'a T -> key list
  val maximals: 'a T -> key list
  val is_minimal: 'a T -> key -> bool
  val is_maximal: 'a T -> key -> bool
  val is_isolated: 'a T -> key -> bool
  val new_node: key * 'a -> 'a T -> 'a T                              (*exception DUP*)
  val default_node: key * 'a -> 'a T -> 'a T
  val del_node: key -> 'a T -> 'a T                                   (*exception UNDEF*)
  val is_edge: 'a T -> key * key -> bool
  val add_edge: key * key -> 'a T -> 'a T                             (*exception UNDEF*)
  val del_edge: key * key -> 'a T -> 'a T                             (*exception UNDEF*)
  val restrict: (key -> bool) -> 'a T -> 'a T
  val dest: 'a T -> ((key * 'a) * key list) list
  val make: ((key * 'a) * key list) list -> 'a T                      (*exception DUP | UNDEF*)
  val merge: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T                 (*exception DUP*)
  val join: (key -> 'a * 'a -> 'a) (*exception DUP/SAME*) ->
    'a T * 'a T -> 'a T                                               (*exception DUP*)
  val irreducible_paths: 'a T -> key * key -> key list list
  exception CYCLES of key list list
  val add_edge_acyclic: key * key -> 'a T -> 'a T                     (*exception UNDEF | CYCLES*)
  val add_deps_acyclic: key * key list -> 'a T -> 'a T                (*exception UNDEF | CYCLES*)
  val merge_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T         (*exception CYCLES*)
  val topological_order: 'a T -> key list
  val add_edge_trans_acyclic: key * key -> 'a T -> 'a T               (*exception UNDEF | CYCLES*)
  val merge_trans_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T   (*exception CYCLES*)
  exception DEP of key * key
  val schedule: ((key * 'b) list -> key * 'a -> 'b) -> 'a T -> 'b list  (*exception DEP*)
  val encode: key XML.Encode.T -> 'a XML.Encode.T -> 'a T XML.Encode.T
  val decode: key XML.Decode.T -> 'a XML.Decode.T -> 'a T XML.Decode.T
end;

functor Graph(Key: KEY): GRAPH =
struct

(* keys *)

structure Key = Key;
type key = Key.key;

val eq_key = is_equal o Key.ord;

structure Table = Table(Key);
structure Set = Set(Key);

structure Keys =
struct

abstype T = Keys of Set.T
with

val empty = Keys Set.empty;
fun is_empty (Keys set) = Set.is_empty set;

fun member (Keys set) = Set.member set;
fun insert x (Keys set) = Keys (Set.insert x set);
fun remove x (Keys set) = Keys (Set.remove x set);

fun fold f (Keys set) = Set.fold f set;
fun fold_rev f (Keys set) = Set.fold_rev f set;

fun dest keys = fold_rev cons keys [];

fun filter P keys = fold (fn x => P x ? insert x) keys empty;

end;
end;


(* graphs *)

datatype 'a T = Graph of ('a * (Keys.T * Keys.T)) Table.table;

exception DUP = Table.DUP;
exception UNDEF = Table.UNDEF;
exception SAME = Table.SAME;

val empty = Graph Table.empty;
fun is_empty (Graph tab) = Table.is_empty tab;
fun keys (Graph tab) = Table.keys tab;

fun get_first f (Graph tab) = Table.get_first f tab;
fun fold_graph f (Graph tab) = Table.fold f tab;

fun defined (Graph tab) = Table.defined tab;

fun get_entry (Graph tab) x =
  (case Table.lookup_key tab x of
    SOME entry => entry
  | NONE => raise UNDEF x);

fun map_entry x f (G as Graph tab) = Graph (Table.update (x, f (#2 (get_entry G x))) tab);


(* nodes *)

fun get_node G = #1 o #2 o get_entry G;

fun map_node x f = map_entry x (fn (i, ps) => (f i, ps));

fun map_nodes f (Graph tab) = Graph (Table.map (apfst o f) tab);


(* reachability *)

(*nodes reachable from xs -- topologically sorted for acyclic graphs*)
fun reachable next xs =
  let
    fun reach x (rs, R) =
      if Keys.member R x then (rs, R)
      else Keys.fold_rev reach (next x) (rs, Keys.insert x R) |>> cons x;
    fun reachs x (rss, R) =
      reach x ([], R) |>> (fn rs => rs :: rss);
  in fold reachs xs ([], Keys.empty) end;

(*immediate*)
fun imm_preds G = #1 o #2 o #2 o get_entry G;
fun imm_succs G = #2 o #2 o #2 o get_entry G;

fun immediate_preds G = Keys.dest o imm_preds G;
fun immediate_succs G = Keys.dest o imm_succs G;

(*transitive*)
fun all_preds G = flat o #1 o reachable (imm_preds G);
fun all_succs G = flat o #1 o reachable (imm_succs G);

(*strongly connected components; see: David King and John Launchbury,
  "Structuring Depth First Search Algorithms in Haskell"*)
fun strong_conn G =
  rev (filter_out null (#1 (reachable (imm_preds G) (all_succs G (keys G)))));

fun map_strong_conn f G =
  let
    val xss = strong_conn G;
    fun map' xs =
      fold2 (curry Table.update) xs (f (AList.make (get_node G) xs));
    val tab' = Table.empty
      |> fold map' xss;
  in map_nodes (fn x => fn _ => the (Table.lookup tab' x)) G end;


(* minimal and maximal elements *)

fun minimals G = fold_graph (fn (m, (_, (preds, _))) => Keys.is_empty preds ? cons m) G [];
fun maximals G = fold_graph (fn (m, (_, (_, succs))) => Keys.is_empty succs ? cons m) G [];
fun is_minimal G x = Keys.is_empty (imm_preds G x);
fun is_maximal G x = Keys.is_empty (imm_succs G x);

fun is_isolated G x = is_minimal G x andalso is_maximal G x;


(* node operations *)

fun new_node (x, info) (Graph tab) =
  Graph (Table.update_new (x, (info, (Keys.empty, Keys.empty))) tab);

fun default_node (x, info) (Graph tab) =
  Graph (Table.default (x, (info, (Keys.empty, Keys.empty))) tab);

fun del_node x (G as Graph tab) =
  let
    fun del_adjacent which y =
      Table.map_entry y (fn (i, ps) => (i, (which (Keys.remove x) ps)));
    val (preds, succs) = #2 (#2 (get_entry G x));
  in
    Graph (tab
      |> Table.delete x
      |> Keys.fold (del_adjacent apsnd) preds
      |> Keys.fold (del_adjacent apfst) succs)
  end;

fun restrict pred G =
  fold_graph (fn (x, _) => not (pred x) ? del_node x) G G;


(* edge operations *)

fun is_edge (Graph tab) (x, y) =
  (case Table.lookup tab x of
    SOME (_, (_, succs)) => Keys.member succs y
  | NONE => false);

fun add_edge (x, y) G =
  if is_edge G (x, y) then G
  else
    G |> map_entry y (fn (i, (preds, succs)) => (i, (Keys.insert x preds, succs)))
      |> map_entry x (fn (i, (preds, succs)) => (i, (preds, Keys.insert y succs)));

fun del_edge (x, y) G =
  if is_edge G (x, y) then
    G |> map_entry y (fn (i, (preds, succs)) => (i, (Keys.remove x preds, succs)))
      |> map_entry x (fn (i, (preds, succs)) => (i, (preds, Keys.remove y succs)))
  else G;

fun diff_edges G1 G2 =
  fold_graph (fn (x, (_, (_, succs))) =>
    Keys.fold (fn y => not (is_edge G2 (x, y)) ? cons (x, y)) succs) G1 [];

fun edges G = diff_edges G empty;


(* dest and make *)

fun dest G = fold_graph (fn (x, (i, (_, succs))) => cons ((x, i), Keys.dest succs)) G [];

fun make entries =
  empty
  |> fold (new_node o fst) entries
  |> fold (fn ((x, _), ys) => fold (fn y => add_edge (x, y)) ys) entries;


(* join and merge *)

fun no_edges (i, _) = (i, (Keys.empty, Keys.empty));

fun join f (G1 as Graph tab1, G2 as Graph tab2) =
  let fun join_node key ((i1, edges1), (i2, _)) = (f key (i1, i2), edges1) in
    if pointer_eq (G1, G2) then G1
    else fold add_edge (edges G2) (Graph (Table.join join_node (tab1, Table.map (K no_edges) tab2)))
  end;

fun gen_merge add eq (G1 as Graph tab1, G2 as Graph tab2) =
  let fun eq_node ((i1, _), (i2, _)) = eq (i1, i2) in
    if pointer_eq (G1, G2) then G1
    else fold add (edges G2) (Graph (Table.merge eq_node (tab1, Table.map (K no_edges) tab2)))
  end;

fun merge eq GG = gen_merge add_edge eq GG;


(* irreducible paths -- Hasse diagram *)

fun irreducible_preds G X path z =
  let
    fun red x x' = is_edge G (x, x') andalso not (eq_key (x', z));
    fun irreds [] xs' = xs'
      | irreds (x :: xs) xs' =
          if not (Keys.member X x) orelse eq_key (x, z) orelse member eq_key path x orelse
            exists (red x) xs orelse exists (red x) xs'
          then irreds xs xs'
          else irreds xs (x :: xs');
  in irreds (immediate_preds G z) [] end;

fun irreducible_paths G (x, y) =
  let
    val (_, X) = reachable (imm_succs G) [x];
    fun paths path z =
      if eq_key (x, z) then cons (z :: path)
      else fold (paths (z :: path)) (irreducible_preds G X path z);
  in if eq_key (x, y) andalso not (is_edge G (x, x)) then [[]] else paths [] y [] end;


(* maintain acyclic graphs *)

exception CYCLES of key list list;

fun add_edge_acyclic (x, y) G =
  if is_edge G (x, y) then G
  else
    (case irreducible_paths G (y, x) of
      [] => add_edge (x, y) G
    | cycles => raise CYCLES (map (cons x) cycles));

fun add_deps_acyclic (y, xs) = fold (fn x => add_edge_acyclic (x, y)) xs;

fun merge_acyclic eq GG = gen_merge add_edge_acyclic eq GG;

fun topological_order G = minimals G |> all_succs G;


(* maintain transitive acyclic graphs *)

fun add_edge_trans_acyclic (x, y) G =
  add_edge_acyclic (x, y) G
  |> fold_product (curry add_edge) (all_preds G [x]) (all_succs G [y]);

fun merge_trans_acyclic eq (G1, G2) =
  if pointer_eq (G1, G2) then G1
  else
    merge_acyclic eq (G1, G2)
    |> fold add_edge_trans_acyclic (diff_edges G1 G2)
    |> fold add_edge_trans_acyclic (diff_edges G2 G1);


(* schedule acyclic graph *)

exception DEP of key * key;

fun schedule f G =
  let
    val xs = topological_order G;
    val results = (xs, Table.empty) |-> fold (fn x => fn tab =>
      let
        val a = get_node G x;
        val deps = immediate_preds G x |> map (fn y =>
          (case Table.lookup tab y of
            SOME b => (y, b)
          | NONE => raise DEP (x, y)));
      in Table.update (x, f deps (x, a)) tab end);
  in map (the o Table.lookup results) xs end;


(* XML data representation *)

fun encode key info G =
  dest G |>
    let open XML.Encode
    in list (pair (pair key info) (list key)) end;

fun decode key info body =
  body |>
    let open XML.Decode
    in list (pair (pair key info) (list key)) end |> make;


(*final declarations of this structure!*)
val map = map_nodes;
val fold = fold_graph;

end;

structure Graph = Graph(Symtab.Key);
structure String_Graph = Graph(type key = string val ord = string_ord);
structure Int_Graph = Graph(Inttab.Key);
