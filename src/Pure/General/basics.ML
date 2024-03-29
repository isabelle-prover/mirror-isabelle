(*  Title:      Pure/General/basics.ML
    Author:     Florian Haftmann and Makarius, TU Muenchen

Fundamental concepts.
*)

infix 1 |> |-> |>> ||> ||>>
infix 1 #> #-> #>> ##> ##>>

signature BASICS =
sig
  (*functions*)
  val |> : 'a * ('a -> 'b) -> 'b
  val |-> : ('c * 'a) * ('c -> 'a -> 'b) -> 'b
  val |>> : ('a * 'c) * ('a -> 'b) -> 'b * 'c
  val ||> : ('c * 'a) * ('a -> 'b) -> 'c * 'b
  val ||>> : ('c * 'a) * ('a -> 'd * 'b) -> ('c * 'd) * 'b
  val #> : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
  val #-> : ('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd
  val #>> : ('a -> 'c * 'b) * ('c -> 'd) -> 'a -> 'd * 'b
  val ##> : ('a -> 'c * 'b) * ('b -> 'd) -> 'a -> 'c * 'd
  val ##>> : ('a -> 'c * 'b) * ('b -> 'e * 'd) -> 'a -> ('c * 'e) * 'd
  val ` : ('b -> 'a) -> 'b -> 'a * 'b
  val tap: ('b -> 'a) -> 'b -> 'b

  (*options*)
  val is_some: 'a option -> bool
  val is_none: 'a option -> bool
  val the: 'a option -> 'a
  val these: 'a list option -> 'a list
  val the_list: 'a option -> 'a list
  val the_default: 'a -> 'a option -> 'a
  val perhaps: ('a -> 'a option) -> 'a -> 'a
  val merge_options: 'a option * 'a option -> 'a option
  val join_options: ('a * 'a -> 'a) -> 'a option * 'a option -> 'a option
  val eq_option: ('a * 'b -> bool) -> 'a option * 'b option -> bool

  (*partiality*)
  val try: ('a -> 'b) -> 'a -> 'b option
  val can: ('a -> 'b) -> 'a -> bool

  (*lists*)
  val cons: 'a -> 'a list -> 'a list
  val append: 'a list -> 'a list -> 'a list
  val fold: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_rev: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_map: ('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b
  val fold_maps: ('a -> 'b -> 'c list * 'b) -> 'a list -> 'b -> 'c list * 'b
end;

structure Basics: BASICS =
struct

(* functions *)

(*application and structured results*)
fun x |> f = f x;
fun (x, y) |-> f = f x y;
fun (x, y) |>> f = (f x, y);
fun (x, y) ||> f = (x, f y);
fun (x, y) ||>> f = let val (z, y') = f y in ((x, z), y') end;

(*composition and structured results*)
fun (f #> g) x   = x |> f |> g;
fun (f #-> g) x  = x |> f |-> g;
fun (f #>> g) x  = x |> f |>> g;
fun (f ##> g) x  = x |> f ||> g;
fun (f ##>> g) x = x |> f ||>> g;

(*result views*)
fun `f = fn x => (f x, x);
fun tap f = fn x => (f x; x);


(* options *)

fun is_some (SOME _) = true
  | is_some NONE = false;

fun is_none (SOME _) = false
  | is_none NONE = true;

fun the (SOME x) = x
  | the NONE = raise Option.Option;

fun these (SOME x) = x
  | these NONE = [];

fun the_list (SOME x) = [x]
  | the_list NONE = []

fun the_default x (SOME y) = y
  | the_default x NONE = x;

fun perhaps f x = the_default x (f x);

fun merge_options (x, y) = if is_some x then x else y;

fun join_options f (SOME x, SOME y) = SOME (f (x, y))
  | join_options _ args = merge_options args;

fun eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option _ (NONE, NONE) = true
  | eq_option _ _ = false;


(* partiality *)

fun try f x = SOME (f x)
  handle exn => if Exn.is_interrupt exn then Exn.reraise exn else NONE;

fun can f x = is_some (try f x);


(* lists *)

fun cons x xs = x :: xs;

fun append xs ys = xs @ ys;

fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);

fun fold_rev _ [] y = y
  | fold_rev f (x :: xs) y = f x (fold_rev f xs y);

fun fold_map _ [] y = ([], y)
  | fold_map f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_map f xs y';
      in (x' :: xs', y'') end;

fun fold_maps _ [] y = ([], y)
  | fold_maps f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_maps f xs y';
      in (x' @ xs', y'') end;

end;

open Basics;
