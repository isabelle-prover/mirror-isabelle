(*  Title:      HOL/Library/DAList.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>Abstract type of association lists with unique keys\<close>

theory DAList
imports AList
begin

text \<open>This was based on some existing fragments in the AFP-Collection framework.\<close>

subsection \<open>Preliminaries\<close>

lemma distinct_map_fst_filter:
  "distinct (map fst xs) \<Longrightarrow> distinct (map fst (List.filter P xs))"
  by (induct xs) auto


subsection \<open>Type \<open>('key, 'value) alist\<close>\<close>

typedef ('key, 'value) alist = "{xs :: ('key \<times> 'value) list. (distinct \<circ> map fst) xs}"
  morphisms impl_of Alist
proof
  show "[] \<in> {xs. (distinct \<circ> map fst) xs}"
    by simp
qed

setup_lifting type_definition_alist

lemma alist_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
  by (simp add: impl_of_inject)

lemma alist_eq_iff: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
  by (simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of xs))"
  using impl_of[of xs] by simp

lemma Alist_impl_of [code abstype]: "Alist (impl_of xs) = xs"
  by (rule impl_of_inverse)


subsection \<open>Primitive operations\<close>

lift_definition lookup :: "('key, 'value) alist \<Rightarrow> 'key \<Rightarrow> 'value option" is map_of  .

lift_definition empty :: "('key, 'value) alist" is "[]"
  by simp

lift_definition update :: "'key \<Rightarrow> 'value \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.update
  by (simp add: distinct_update)

(* FIXME: we use an unoptimised delete operation. *)
lift_definition delete :: "'key \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.delete
  by (simp add: distinct_delete)

lift_definition map_entry ::
    "'key \<Rightarrow> ('value \<Rightarrow> 'value) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.map_entry
  by (simp add: distinct_map_entry)

lift_definition filter :: "('key \<times> 'value \<Rightarrow> bool) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is List.filter
  by (simp add: distinct_map_fst_filter)

lift_definition map_default ::
    "'key \<Rightarrow> 'value \<Rightarrow> ('value \<Rightarrow> 'value) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.map_default
  by (simp add: distinct_map_default)


subsection \<open>Abstract operation properties\<close>

(* FIXME: to be completed *)

lemma lookup_empty [simp]: "lookup empty k = None"
by (simp add: empty_def lookup_def Alist_inverse)

lemma lookup_update:
  "lookup (update k1 v xs) k2 = (if k1 = k2 then Some v else lookup xs k2)"
by(transfer)(simp add: update_conv')

lemma lookup_update_eq [simp]:
  "k1 = k2 \<Longrightarrow> lookup (update k1 v xs) k2 = Some v"
by(simp add: lookup_update)

lemma lookup_update_neq [simp]:
  "k1 \<noteq> k2 \<Longrightarrow> lookup (update k1 v xs) k2 = lookup xs k2"
by(simp add: lookup_update)

lemma update_update_eq [simp]:
  "k1 = k2 \<Longrightarrow> update k2 v2 (update k1 v1 xs) = update k2 v2 xs"
by(transfer)(simp add: update_conv')

lemma lookup_delete [simp]: "lookup (delete k al) = (lookup al)(k := None)"
  by (simp add: lookup_def delete_def Alist_inverse distinct_delete delete_conv')


subsection \<open>Further operations\<close>

subsubsection \<open>Equality\<close>

instantiation alist :: (equal, equal) equal
begin

definition "HOL.equal (xs :: ('a, 'b) alist) ys == impl_of xs = impl_of ys"

instance
  by standard (simp add: equal_alist_def impl_of_inject)

end


subsubsection \<open>Size\<close>

instantiation alist :: (type, type) size
begin

definition "size (al :: ('a, 'b) alist) = length (impl_of al)"

instance ..

end


subsection \<open>Quickcheck generators\<close>

context
  includes state_combinator_syntax and term_syntax
begin

definition
  valterm_empty :: "('key :: typerep, 'value :: typerep) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)"
  where "valterm_empty = Code_Evaluation.valtermify empty"

definition
  valterm_update :: "'key :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  'value :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  ('key, 'value) alist \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  ('key, 'value) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "valterm_update k v a = Code_Evaluation.valtermify update {\<cdot>} k {\<cdot>} v {\<cdot>}a"

fun random_aux_alist
where
  "random_aux_alist i j =
    (if i = 0 then Pair valterm_empty
     else Quickcheck_Random.collapse
       (Random.select_weight
         [(i, Quickcheck_Random.random j \<circ>\<rightarrow> (\<lambda>k. Quickcheck_Random.random j \<circ>\<rightarrow>
           (\<lambda>v. random_aux_alist (i - 1) j \<circ>\<rightarrow> (\<lambda>a. Pair (valterm_update k v a))))),
          (1, Pair valterm_empty)]))"

end

instantiation alist :: (random, random) random
begin

definition random_alist
where
  "random_alist i = random_aux_alist i i"

instance ..

end

instantiation alist :: (exhaustive, exhaustive) exhaustive
begin

fun exhaustive_alist ::
  "(('a, 'b) alist \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "exhaustive_alist f i =
    (if i = 0 then None
     else
      case f empty of
        Some ts \<Rightarrow> Some ts
      | None \<Rightarrow>
          exhaustive_alist
            (\<lambda>a. Quickcheck_Exhaustive.exhaustive
              (\<lambda>k. Quickcheck_Exhaustive.exhaustive (\<lambda>v. f (update k v a)) (i - 1)) (i - 1))
            (i - 1))"

instance ..

end

instantiation alist :: (full_exhaustive, full_exhaustive) full_exhaustive
begin

fun full_exhaustive_alist ::
  "(('a, 'b) alist \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow>
    (bool \<times> term list) option"
where
  "full_exhaustive_alist f i =
    (if i = 0 then None
     else
      case f valterm_empty of
        Some ts \<Rightarrow> Some ts
      | None \<Rightarrow>
          full_exhaustive_alist
            (\<lambda>a.
              Quickcheck_Exhaustive.full_exhaustive
                (\<lambda>k. Quickcheck_Exhaustive.full_exhaustive (\<lambda>v. f (valterm_update k v a)) (i - 1))
              (i - 1))
            (i - 1))"

instance ..

end


section \<open>alist is a BNF\<close>

lift_bnf (dead 'k, set: 'v) alist [wits: "[] :: ('k \<times> 'v) list"] for map: map rel: rel
  by auto

hide_const valterm_empty valterm_update random_aux_alist

hide_fact (open) lookup_def empty_def update_def delete_def map_entry_def filter_def map_default_def
hide_const (open) impl_of lookup empty update delete map_entry filter map_default map set rel

end
