(*  Title:      HOL/Library/RBT.thy
    Author:     Lukas Bulwahn and Ondrej Kuncar
*)

section \<open>Abstract type of RBT trees\<close>

theory RBT 
imports Main RBT_Impl
begin

subsection \<open>Type definition\<close>

typedef (overloaded) ('a, 'b) rbt = "{t :: ('a::linorder, 'b) RBT_Impl.rbt. is_rbt t}"
  morphisms impl_of RBT
proof -
  have "RBT_Impl.Empty \<in> ?rbt" by simp
  then show ?thesis ..
qed

lemma rbt_eq_iff:
  "t1 = t2 \<longleftrightarrow> impl_of t1 = impl_of t2"
  by (simp add: impl_of_inject)

lemma rbt_eqI:
  "impl_of t1 = impl_of t2 \<Longrightarrow> t1 = t2"
  by (simp add: rbt_eq_iff)

lemma is_rbt_impl_of [simp, intro]:
  "is_rbt (impl_of t)"
  using impl_of [of t] by simp

lemma RBT_impl_of [simp, code abstype]:
  "RBT (impl_of t) = t"
  by (simp add: impl_of_inverse)

subsection \<open>Primitive operations\<close>

setup_lifting type_definition_rbt

lift_definition lookup :: "('a::linorder, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b" is "rbt_lookup" .

lift_definition empty :: "('a::linorder, 'b) rbt" is RBT_Impl.Empty 
by (simp add: empty_def)

lift_definition insert :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" is "rbt_insert" 
by simp

lift_definition delete :: "'a::linorder \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" is "rbt_delete" 
by simp

lift_definition entries :: "('a::linorder, 'b) rbt \<Rightarrow> ('a \<times> 'b) list" is RBT_Impl.entries .

lift_definition keys :: "('a::linorder, 'b) rbt \<Rightarrow> 'a list" is RBT_Impl.keys .

lift_definition bulkload :: "('a::linorder \<times> 'b) list \<Rightarrow> ('a, 'b) rbt" is "rbt_bulkload" ..

lift_definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt" is rbt_map_entry
by simp

lift_definition map :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> ('a, 'c) rbt" is RBT_Impl.map
by simp

lift_definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c"  is RBT_Impl.fold .

lift_definition union :: "('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" is "rbt_union"
by (simp add: rbt_union_is_rbt)

lift_definition foldi :: "('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a :: linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c"
  is RBT_Impl.foldi .
  
lift_definition combine_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
  is RBT_Impl.rbt_union_with_key by (rule is_rbt_rbt_unionwk)

lift_definition combine :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
  is RBT_Impl.rbt_union_with by (rule rbt_unionw_is_rbt)

subsection \<open>Derived operations\<close>

definition is_empty :: "('a::linorder, 'b) rbt \<Rightarrow> bool" where
  [code]: "is_empty t = (case impl_of t of RBT_Impl.Empty \<Rightarrow> True | _ \<Rightarrow> False)"

(* TODO: Is deleting more efficient than re-building the tree? 
   (Probably more difficult to prove though *)
definition filter :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  [code]: "filter P t = fold (\<lambda>k v t. if P k v then insert k v t else t) t empty" 

subsection \<open>Abstract lookup properties\<close>

lemma lookup_RBT:
  "is_rbt t \<Longrightarrow> lookup (RBT t) = rbt_lookup t"
  by (simp add: lookup_def RBT_inverse)

lemma lookup_impl_of:
  "rbt_lookup (impl_of t) = lookup t"
  by transfer (rule refl)

lemma entries_impl_of:
  "RBT_Impl.entries (impl_of t) = entries t"
  by transfer (rule refl)

lemma keys_impl_of:
  "RBT_Impl.keys (impl_of t) = keys t"
  by transfer (rule refl)

lemma lookup_keys: 
  "dom (lookup t) = set (keys t)" 
  by transfer (simp add: rbt_lookup_keys)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def lookup_RBT fun_eq_iff)

lemma lookup_insert [simp]:
  "lookup (insert k v t) = (lookup t)(k \<mapsto> v)"
  by transfer (rule rbt_lookup_rbt_insert)

lemma lookup_delete [simp]:
  "lookup (delete k t) = (lookup t)(k := None)"
  by transfer (simp add: rbt_lookup_rbt_delete restrict_complement_singleton_eq)

lemma map_of_entries [simp]:
  "map_of (entries t) = lookup t"
  by transfer (simp add: map_of_entries)

lemma entries_lookup:
  "entries t1 = entries t2 \<longleftrightarrow> lookup t1 = lookup t2"
  by transfer (simp add: entries_rbt_lookup)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = map_of xs"
  by transfer (rule rbt_lookup_rbt_bulkload)

lemma lookup_map_entry [simp]:
  "lookup (map_entry k f t) = (lookup t)(k := map_option f (lookup t k))"
  by transfer (rule rbt_lookup_rbt_map_entry)

lemma lookup_map [simp]:
  "lookup (map f t) k = map_option (f k) (lookup t k)"
  by transfer (rule rbt_lookup_map)

lemma lookup_combine_with_key [simp]:
  "lookup (combine_with_key f t1 t2) k = combine_options (f k) (lookup t1 k) (lookup t2 k)"
  by transfer (simp_all add: combine_options_def rbt_lookup_rbt_unionwk)

lemma combine_altdef: "combine f t1 t2 = combine_with_key (\<lambda>_. f) t1 t2"
  by transfer (simp add: rbt_union_with_def)

lemma lookup_combine [simp]:
  "lookup (combine f t1 t2) k = combine_options f (lookup t1 k) (lookup t2 k)"
  by (simp add: combine_altdef)

lemma fold_fold:
  "fold f t = List.fold (case_prod f) (entries t)"
  by transfer (rule RBT_Impl.fold_def)

lemma impl_of_empty:
  "impl_of empty = RBT_Impl.Empty"
  by transfer (rule refl)

lemma is_empty_empty [simp]:
  "is_empty t \<longleftrightarrow> t = empty"
  unfolding is_empty_def by transfer (simp split: rbt.split)

lemma RBT_lookup_empty [simp]: (*FIXME*)
  "rbt_lookup t = Map.empty \<longleftrightarrow> t = RBT_Impl.Empty"
  by (cases t) (auto simp add: fun_eq_iff)

lemma lookup_empty_empty [simp]:
  "lookup t = Map.empty \<longleftrightarrow> t = empty"
  by transfer (rule RBT_lookup_empty)

lemma keys_empty_eq [simp]:
  \<open>keys empty = []\<close>
  by transfer simp

lemma sorted_keys [iff]:
  "sorted (keys t)"
  by transfer (simp add: RBT_Impl.keys_def rbt_sorted_entries)

lemma distinct_keys [iff]:
  "distinct (keys t)"
  by transfer (simp add: RBT_Impl.keys_def distinct_entries)

lemma finite_dom_lookup [simp, intro!]: "finite (dom (lookup t))"
  by transfer simp

lemma lookup_union: "lookup (union s t) = lookup s ++ lookup t"
  by transfer (simp add: rbt_lookup_rbt_union)

lemma lookup_in_tree: "(lookup t k = Some v) = ((k, v) \<in> set (entries t))"
  by transfer (simp add: rbt_lookup_in_tree)

lemma keys_entries: "(k \<in> set (keys t)) = (\<exists>v. (k, v) \<in> set (entries t))"
  by transfer (simp add: keys_entries)

lemma fold_def_alt:
  "fold f t = List.fold (case_prod f) (entries t)"
  by transfer (auto simp: RBT_Impl.fold_def)

lemma distinct_entries: "distinct (List.map fst (entries t))"
  by transfer (simp add: distinct_entries)

lemma sorted_entries: "sorted (List.map fst (entries t))"
  by (transfer) (simp add: rbt_sorted_entries)

lemma non_empty_keys: "t \<noteq> empty \<Longrightarrow> keys t \<noteq> []"
  by transfer (simp add: non_empty_rbt_keys)

lemma keys_def_alt:
  "keys t = List.map fst (entries t)"
  by transfer (simp add: RBT_Impl.keys_def)

context
begin

private lemma lookup_filter_aux:
  assumes "distinct (List.map fst xs)"
  shows   "lookup (List.fold (\<lambda>(k, v) t. if P k v then insert k v t else t) xs t) k =
             (case map_of xs k of 
                None \<Rightarrow> lookup t k
              | Some v \<Rightarrow> if P k v then Some v else lookup t k)"
  using assms by (induction xs arbitrary: t) (force split: option.splits)+

lemma lookup_filter: 
  "lookup (filter P t) k = 
     (case lookup t k of None \<Rightarrow> None | Some v \<Rightarrow> if P k v then Some v else None)"
  unfolding filter_def using lookup_filter_aux[of "entries t" P empty k]
  by (simp add: fold_fold distinct_entries split: option.splits)
  
end


subsection \<open>Quickcheck generators\<close>

quickcheck_generator rbt predicate: is_rbt constructors: empty, insert

subsection \<open>Hide implementation details\<close>

lifting_update rbt.lifting
lifting_forget rbt.lifting

hide_const (open) impl_of empty lookup keys entries bulkload delete map fold union insert map_entry foldi 
  is_empty filter
hide_fact (open) empty_def lookup_def keys_def entries_def bulkload_def delete_def map_def fold_def 
  union_def insert_def map_entry_def foldi_def is_empty_def filter_def

end
