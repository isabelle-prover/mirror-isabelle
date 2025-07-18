(*  Title:      Pure/cterm_items.ML
    Author:     Makarius

Scalable collections of term items: for type thm and cterm.
See also Pure/term_items.ML.
*)

structure Ctermtab:
sig
  include TABLE
  val cterm_cache: (cterm -> 'a) -> cterm -> 'a
end =
struct

structure Table = Table(type key = cterm val ord = Thm.fast_term_ord);
open Table;

fun cterm_cache f = Cache.create empty lookup update f;

end;

structure Ctermset = Set(Ctermtab.Key);


structure Cterms:
sig
  include TERM_ITEMS
  val add_vars: thm -> set -> set
  val add_frees: thm -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = cterm;
  val ord = Thm.fast_term_ord;
);
open Term_Items;

val add_vars = Thm.fold_atomic_cterms {hyps = false} (K Term.is_Var) add_set;
val add_frees = Thm.fold_atomic_cterms {hyps = true} (K Term.is_Free) add_set;

end;


structure Proptab = Table
(
  type key = thm
  val ord = pointer_eq_ord (Term_Ord.fast_term_ord o apply2 Thm.full_prop_of)
);

structure Thmtab:
sig
  include TABLE
  val thm_cache: (thm -> 'a) -> thm -> 'a
end =
struct

structure Table = Table(type key = thm val ord = Thm.thm_ord);
open Table;

fun thm_cache f = Cache.create empty lookup update f;

end;

structure Thmset = Set(Thmtab.Key);
