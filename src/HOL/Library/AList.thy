(*  Title:      HOL/Library/AList.thy
    Author:     Norbert Schirmer, Tobias Nipkow, Martin Wildmoser, TU Muenchen
*)

section \<open>Implementation of Association Lists\<close>

theory AList
  imports Main
begin

context
begin

text \<open>
  The operations preserve distinctness of keys and
  function \<^term>\<open>clearjunk\<close> distributes over them. Since
  \<^term>\<open>clearjunk\<close> enforces distinctness of keys it can be used
  to establish the invariant, e.g. for inductive proofs.
\<close>

subsection \<open>\<open>update\<close> and \<open>updates\<close>\<close>

qualified primrec update :: "'key \<Rightarrow> 'val \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where
    "update k v [] = [(k, v)]"
  | "update k v (p # ps) = (if fst p = k then (k, v) # ps else p # update k v ps)"

lemma update_conv': "map_of (update k v al) = (map_of al)(k\<mapsto>v)"
  by (induct al) (auto simp add: fun_eq_iff)

corollary update_conv: "map_of (update k v al) k' = ((map_of al)(k\<mapsto>v)) k'"
  by (simp add: update_conv')

lemma dom_update: "fst ` set (update k v al) = {k} \<union> fst ` set al"
  by (induct al) auto

lemma update_keys:
  "map fst (update k v al) =
    (if k \<in> set (map fst al) then map fst al else map fst al @ [k])"
  by (induct al) simp_all

lemma distinct_update:
  assumes "distinct (map fst al)"
  shows "distinct (map fst (update k v al))"
  using assms by (simp add: update_keys)

lemma update_filter:
  "a \<noteq> k \<Longrightarrow> update k v [q\<leftarrow>ps. fst q \<noteq> a] = [q\<leftarrow>update k v ps. fst q \<noteq> a]"
  by (induct ps) auto

lemma update_triv: "map_of al k = Some v \<Longrightarrow> update k v al = al"
  by (induct al) auto

lemma update_nonempty [simp]: "update k v al \<noteq> []"
  by (induct al) auto

lemma update_eqD: "update k v al = update k v' al' \<Longrightarrow> v = v'"
proof (induct al arbitrary: al')
  case Nil
  then show ?case
    by (cases al') (auto split: if_split_asm)
next
  case Cons
  then show ?case
    by (cases al') (auto split: if_split_asm)
qed

lemma update_last [simp]: "update k v (update k v' al) = update k v al"
  by (induct al) auto

text \<open>Note that the lists are not necessarily the same:
        \<^term>\<open>update k v (update k' v' []) = [(k', v'), (k, v)]\<close> and
        \<^term>\<open>update k' v' (update k v []) = [(k, v), (k', v')]\<close>.\<close>

lemma update_swap:
  "k \<noteq> k' \<Longrightarrow> map_of (update k v (update k' v' al)) = map_of (update k' v' (update k v al))"
  by (simp add: update_conv' fun_eq_iff)

lemma update_Some_unfold:
  "map_of (update k v al) x = Some y \<longleftrightarrow>
    x = k \<and> v = y \<or> x \<noteq> k \<and> map_of al x = Some y"
  by (simp add: update_conv' map_upd_Some_unfold)

lemma image_update [simp]: "x \<notin> A \<Longrightarrow> map_of (update x y al) ` A = map_of al ` A"
  by (auto simp add: update_conv')

qualified definition updates ::
    "'key list \<Rightarrow> 'val list \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where "updates ks vs = fold (case_prod update) (zip ks vs)"

lemma updates_simps [simp]:
  "updates [] vs ps = ps"
  "updates ks [] ps = ps"
  "updates (k#ks) (v#vs) ps = updates ks vs (update k v ps)"
  by (simp_all add: updates_def)

lemma updates_key_simp [simp]:
  "updates (k # ks) vs ps =
    (case vs of [] \<Rightarrow> ps | v # vs \<Rightarrow> updates ks vs (update k v ps))"
  by (cases vs) simp_all

lemma updates_conv': "map_of (updates ks vs al) = (map_of al)(ks[\<mapsto>]vs)"
proof -
  have "map_of \<circ> fold (case_prod update) (zip ks vs) =
      fold (\<lambda>(k, v) f. f(k \<mapsto> v)) (zip ks vs) \<circ> map_of"
    by (rule fold_commute) (auto simp add: fun_eq_iff update_conv')
  then show ?thesis
    by (auto simp add: updates_def fun_eq_iff map_upds_fold_map_upd foldl_conv_fold split_def)
qed

lemma updates_conv: "map_of (updates ks vs al) k = ((map_of al)(ks[\<mapsto>]vs)) k"
  by (simp add: updates_conv')

lemma distinct_updates:
  assumes "distinct (map fst al)"
  shows "distinct (map fst (updates ks vs al))"
proof -
  have "distinct (fold
       (\<lambda>(k, v) al. if k \<in> set al then al else al @ [k])
       (zip ks vs) (map fst al))"
    by (rule fold_invariant [of "zip ks vs" "\<lambda>_. True"]) (auto intro: assms)
  moreover have "map fst \<circ> fold (case_prod update) (zip ks vs) =
      fold (\<lambda>(k, v) al. if k \<in> set al then al else al @ [k]) (zip ks vs) \<circ> map fst"
    by (rule fold_commute) (simp add: update_keys split_def case_prod_beta comp_def)
  ultimately show ?thesis
    by (simp add: updates_def fun_eq_iff)
qed

lemma updates_append1[simp]: "size ks < size vs \<Longrightarrow>
    updates (ks@[k]) vs al = update k (vs!size ks) (updates ks vs al)"
  by (induct ks arbitrary: vs al) (auto split: list.splits)

lemma updates_list_update_drop[simp]:
  "size ks \<le> i \<Longrightarrow> i < size vs \<Longrightarrow>
    updates ks (vs[i:=v]) al = updates ks vs al"
  by (induct ks arbitrary: al vs i) (auto split: list.splits nat.splits)

lemma update_updates_conv_if:
  "map_of (updates xs ys (update x y al)) =
    map_of
     (if x \<in> set (take (length ys) xs)
      then updates xs ys al
      else (update x y (updates xs ys al)))"
  by (simp add: updates_conv' update_conv' map_upd_upds_conv_if)

lemma updates_twist [simp]:
  "k \<notin> set ks \<Longrightarrow>
    map_of (updates ks vs (update k v al)) = map_of (update k v (updates ks vs al))"
  by (simp add: updates_conv' update_conv')

lemma updates_apply_notin [simp]:
  "k \<notin> set ks \<Longrightarrow> map_of (updates ks vs al) k = map_of al k"
  by (simp add: updates_conv)

lemma updates_append_drop [simp]:
  "size xs = size ys \<Longrightarrow> updates (xs @ zs) ys al = updates xs ys al"
  by (induct xs arbitrary: ys al) (auto split: list.splits)

lemma updates_append2_drop [simp]:
  "size xs = size ys \<Longrightarrow> updates xs (ys @ zs) al = updates xs ys al"
  by (induct xs arbitrary: ys al) (auto split: list.splits)


subsection \<open>\<open>delete\<close>\<close>

qualified definition delete :: "'key \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where delete_eq: "delete k = filter (\<lambda>(k', _). k \<noteq> k')"

lemma delete_simps [simp]:
  "delete k [] = []"
  "delete k (p # ps) = (if fst p = k then delete k ps else p # delete k ps)"
  by (auto simp add: delete_eq)

lemma delete_conv': "map_of (delete k al) = (map_of al)(k := None)"
  by (induct al) (auto simp add: fun_eq_iff)

corollary delete_conv: "map_of (delete k al) k' = ((map_of al)(k := None)) k'"
  by (simp add: delete_conv')

lemma delete_keys: "map fst (delete k al) = removeAll k (map fst al)"
  by (simp add: delete_eq removeAll_filter_not_eq filter_map split_def comp_def)

lemma distinct_delete:
  assumes "distinct (map fst al)"
  shows "distinct (map fst (delete k al))"
  using assms by (simp add: delete_keys distinct_removeAll)

lemma delete_id [simp]: "k \<notin> fst ` set al \<Longrightarrow> delete k al = al"
  by (auto simp add: image_iff delete_eq filter_id_conv)

lemma delete_idem: "delete k (delete k al) = delete k al"
  by (simp add: delete_eq)

lemma map_of_delete [simp]: "k' \<noteq> k \<Longrightarrow> map_of (delete k al) k' = map_of al k'"
  by (simp add: delete_conv')

lemma delete_notin_dom: "k \<notin> fst ` set (delete k al)"
  by (auto simp add: delete_eq)

lemma dom_delete_subset: "fst ` set (delete k al) \<subseteq> fst ` set al"
  by (auto simp add: delete_eq)

lemma delete_update_same: "delete k (update k v al) = delete k al"
  by (induct al) simp_all

lemma delete_update: "k \<noteq> l \<Longrightarrow> delete l (update k v al) = update k v (delete l al)"
  by (induct al) simp_all

lemma delete_twist: "delete x (delete y al) = delete y (delete x al)"
  by (simp add: delete_eq conj_commute)

lemma length_delete_le: "length (delete k al) \<le> length al"
  by (simp add: delete_eq)


subsection \<open>\<open>update_with_aux\<close> and \<open>delete_aux\<close>\<close>

qualified primrec update_with_aux ::
    "'val \<Rightarrow> 'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where
    "update_with_aux v k f [] = [(k, f v)]"
  | "update_with_aux v k f (p # ps) =
      (if (fst p = k) then (k, f (snd p)) # ps else p # update_with_aux v k f ps)"

text \<open>
  The above \<^term>\<open>delete\<close> traverses all the list even if it has found the key.
  This one does not have to keep going because is assumes the invariant that keys are distinct.
\<close>
qualified fun delete_aux :: "'key \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where
    "delete_aux k [] = []"
  | "delete_aux k ((k', v) # xs) = (if k = k' then xs else (k', v) # delete_aux k xs)"

lemma map_of_update_with_aux':
  "map_of (update_with_aux v k f ps) k' =
    ((map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))) k'"
  by (induct ps) auto

lemma map_of_update_with_aux:
  "map_of (update_with_aux v k f ps) =
    (map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))"
  by (simp add: fun_eq_iff map_of_update_with_aux')

lemma dom_update_with_aux: "fst ` set (update_with_aux v k f ps) = {k} \<union> fst ` set ps"
  by (induct ps) auto

lemma distinct_update_with_aux [simp]:
  "distinct (map fst (update_with_aux v k f ps)) = distinct (map fst ps)"
  by (induct ps) (auto simp add: dom_update_with_aux)

lemma set_update_with_aux:
  "distinct (map fst xs) \<Longrightarrow>
    set (update_with_aux v k f xs) =
      (set xs - {k} \<times> UNIV \<union> {(k, f (case map_of xs k of None \<Rightarrow> v | Some v \<Rightarrow> v))})"
  by (induct xs) (auto intro: rev_image_eqI)

lemma set_delete_aux: "distinct (map fst xs) \<Longrightarrow> set (delete_aux k xs) = set xs - {k} \<times> UNIV"
  apply (induct xs)
   apply simp_all
  apply clarsimp
  apply (fastforce intro: rev_image_eqI)
  done

lemma dom_delete_aux: "distinct (map fst ps) \<Longrightarrow> fst ` set (delete_aux k ps) = fst ` set ps - {k}"
  by (auto simp add: set_delete_aux)

lemma distinct_delete_aux [simp]: "distinct (map fst ps) \<Longrightarrow> distinct (map fst (delete_aux k ps))"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain k' v where a: "a = (k', v)"
    by (cases a)
  show ?case
  proof (cases "k' = k")
    case True
    with Cons a show ?thesis by simp
  next
    case False
    with Cons a have "k' \<notin> fst ` set ps" "distinct (map fst ps)"
      by simp_all
    with False a have "k' \<notin> fst ` set (delete_aux k ps)"
      by (auto dest!: dom_delete_aux[where k=k])
    with Cons a show ?thesis
      by simp
  qed
qed

lemma map_of_delete_aux':
  "distinct (map fst xs) \<Longrightarrow> map_of (delete_aux k xs) = (map_of xs)(k := None)"
  apply (induct xs)
   apply (fastforce simp add: map_of_eq_None_iff fun_upd_twist)
  apply (auto intro!: ext)
  apply (simp add: map_of_eq_None_iff)
  done

lemma map_of_delete_aux:
  "distinct (map fst xs) \<Longrightarrow> map_of (delete_aux k xs) k' = ((map_of xs)(k := None)) k'"
  by (simp add: map_of_delete_aux')

lemma delete_aux_eq_Nil_conv: "delete_aux k ts = [] \<longleftrightarrow> ts = [] \<or> (\<exists>v. ts = [(k, v)])"
  by (cases ts) (auto split: if_split_asm)


subsection \<open>\<open>restrict\<close>\<close>

qualified definition restrict :: "'key set \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where restrict_eq: "restrict A = filter (\<lambda>(k, v). k \<in> A)"

lemma restr_simps [simp]:
  "restrict A [] = []"
  "restrict A (p#ps) = (if fst p \<in> A then p # restrict A ps else restrict A ps)"
  by (auto simp add: restrict_eq)

lemma restr_conv': "map_of (restrict A al) = ((map_of al)|` A)"
proof
  show "map_of (restrict A al) k = ((map_of al)|` A) k" for k
    apply (induct al)
     apply simp
    apply (cases "k \<in> A")
     apply auto
    done
qed

corollary restr_conv: "map_of (restrict A al) k = ((map_of al)|` A) k"
  by (simp add: restr_conv')

lemma distinct_restr: "distinct (map fst al) \<Longrightarrow> distinct (map fst (restrict A al))"
  by (induct al) (auto simp add: restrict_eq)

lemma restr_empty [simp]:
  "restrict {} al = []"
  "restrict A [] = []"
  by (induct al) (auto simp add: restrict_eq)

lemma restr_in [simp]: "x \<in> A \<Longrightarrow> map_of (restrict A al) x = map_of al x"
  by (simp add: restr_conv')

lemma restr_out [simp]: "x \<notin> A \<Longrightarrow> map_of (restrict A al) x = None"
  by (simp add: restr_conv')

lemma dom_restr [simp]: "fst ` set (restrict A al) = fst ` set al \<inter> A"
  by (induct al) (auto simp add: restrict_eq)

lemma restr_upd_same [simp]: "restrict (-{x}) (update x y al) = restrict (-{x}) al"
  by (induct al) (auto simp add: restrict_eq)

lemma restr_restr [simp]: "restrict A (restrict B al) = restrict (A\<inter>B) al"
  by (induct al) (auto simp add: restrict_eq)

lemma restr_update[simp]:
  "map_of (restrict D (update x y al)) =
    map_of ((if x \<in> D then (update x y (restrict (D-{x}) al)) else restrict D al))"
  by (simp add: restr_conv' update_conv')

lemma restr_delete [simp]:
  "delete x (restrict D al) = (if x \<in> D then restrict (D - {x}) al else restrict D al)"
  apply (simp add: delete_eq restrict_eq)
  apply (auto simp add: split_def)
proof -
  have "y \<noteq> x \<longleftrightarrow> x \<noteq> y" for y
    by auto
  then show "[p \<leftarrow> al. fst p \<in> D \<and> x \<noteq> fst p] = [p \<leftarrow> al. fst p \<in> D \<and> fst p \<noteq> x]"
    by simp
  assume "x \<notin> D"
  then have "y \<in> D \<longleftrightarrow> y \<in> D \<and> x \<noteq> y" for y
    by auto
  then show "[p \<leftarrow> al . fst p \<in> D \<and> x \<noteq> fst p] = [p \<leftarrow> al . fst p \<in> D]"
    by simp
qed

lemma update_restr:
  "map_of (update x y (restrict D al)) = map_of (update x y (restrict (D - {x}) al))"
  by (simp add: update_conv' restr_conv') (rule fun_upd_restrict)

lemma update_restr_conv [simp]:
  "x \<in> D \<Longrightarrow>
    map_of (update x y (restrict D al)) = map_of (update x y (restrict (D - {x}) al))"
  by (simp add: update_conv' restr_conv')

lemma restr_updates [simp]:
  "length xs = length ys \<Longrightarrow> set xs \<subseteq> D \<Longrightarrow>
    map_of (restrict D (updates xs ys al)) =
      map_of (updates xs ys (restrict (D - set xs) al))"
  by (simp add: updates_conv' restr_conv')

lemma restr_delete_twist: "(restrict A (delete a ps)) = delete a (restrict A ps)"
  by (induct ps) auto


subsection \<open>\<open>clearjunk\<close>\<close>

qualified function clearjunk  :: "('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where
    "clearjunk [] = []"
  | "clearjunk (p#ps) = p # clearjunk (delete (fst p) ps)"
  by pat_completeness auto
termination
  by (relation "measure length") (simp_all add: less_Suc_eq_le length_delete_le)

lemma map_of_clearjunk: "map_of (clearjunk al) = map_of al"
  by (induct al rule: clearjunk.induct) (simp_all add: fun_eq_iff)

lemma clearjunk_keys_set: "set (map fst (clearjunk al)) = set (map fst al)"
  by (induct al rule: clearjunk.induct) (simp_all add: delete_keys)

lemma dom_clearjunk: "fst ` set (clearjunk al) = fst ` set al"
  using clearjunk_keys_set by simp

lemma distinct_clearjunk [simp]: "distinct (map fst (clearjunk al))"
  by (induct al rule: clearjunk.induct) (simp_all del: set_map add: clearjunk_keys_set delete_keys)

lemma ran_clearjunk: "ran (map_of (clearjunk al)) = ran (map_of al)"
  by (simp add: map_of_clearjunk)

lemma ran_map_of: "ran (map_of al) = snd ` set (clearjunk al)"
proof -
  have "ran (map_of al) = ran (map_of (clearjunk al))"
    by (simp add: ran_clearjunk)
  also have "\<dots> = snd ` set (clearjunk al)"
    by (simp add: ran_distinct)
  finally show ?thesis .
qed

lemma graph_map_of: "Map.graph (map_of al) = set (clearjunk al)"
  by (metis distinct_clearjunk graph_map_of_if_distinct_dom map_of_clearjunk)

lemma clearjunk_update: "clearjunk (update k v al) = update k v (clearjunk al)"
  by (induct al rule: clearjunk.induct) (simp_all add: delete_update)

lemma clearjunk_updates: "clearjunk (updates ks vs al) = updates ks vs (clearjunk al)"
proof -
  have "clearjunk \<circ> fold (case_prod update) (zip ks vs) =
      fold (case_prod update) (zip ks vs) \<circ> clearjunk"
    by (rule fold_commute) (simp add: clearjunk_update case_prod_beta o_def)
  then show ?thesis
    by (simp add: updates_def fun_eq_iff)
qed

lemma clearjunk_delete: "clearjunk (delete x al) = delete x (clearjunk al)"
  by (induct al rule: clearjunk.induct) (auto simp add: delete_idem delete_twist)

lemma clearjunk_restrict: "clearjunk (restrict A al) = restrict A (clearjunk al)"
  by (induct al rule: clearjunk.induct) (auto simp add: restr_delete_twist)

lemma distinct_clearjunk_id [simp]: "distinct (map fst al) \<Longrightarrow> clearjunk al = al"
  by (induct al rule: clearjunk.induct) auto

lemma clearjunk_idem: "clearjunk (clearjunk al) = clearjunk al"
  by simp

lemma length_clearjunk: "length (clearjunk al) \<le> length al"
proof (induct al rule: clearjunk.induct [case_names Nil Cons])
  case Nil
  then show ?case by simp
next
  case (Cons kv al)
  moreover have "length (delete (fst kv) al) \<le> length al"
    by (fact length_delete_le)
  ultimately have "length (clearjunk (delete (fst kv) al)) \<le> length al"
    by (rule order_trans)
  then show ?case
    by simp
qed

lemma delete_map:
  assumes "\<And>kv. fst (f kv) = fst kv"
  shows "delete k (map f ps) = map f (delete k ps)"
  by (simp add: delete_eq filter_map comp_def split_def assms)

lemma clearjunk_map:
  assumes "\<And>kv. fst (f kv) = fst kv"
  shows "clearjunk (map f ps) = map f (clearjunk ps)"
  by (induct ps rule: clearjunk.induct [case_names Nil Cons])
    (simp_all add: clearjunk_delete delete_map assms)


subsection \<open>\<open>map_ran\<close>\<close>

definition map_ran :: "('key \<Rightarrow> 'val1 \<Rightarrow> 'val2) \<Rightarrow> ('key \<times> 'val1) list \<Rightarrow> ('key \<times> 'val2) list"
  where "map_ran f = map (\<lambda>(k, v). (k, f k v))"

lemma map_ran_simps [simp]:
  "map_ran f [] = []"
  "map_ran f ((k, v) # ps) = (k, f k v) # map_ran f ps"
  by (simp_all add: map_ran_def)

lemma map_ran_Cons_sel: "map_ran f (p # ps) = (fst p, f (fst p) (snd p)) # map_ran f ps"
  by (simp add: map_ran_def case_prod_beta)

lemma length_map_ran[simp]: "length (map_ran f al) = length al"
  by (simp add: map_ran_def)

lemma map_fst_map_ran[simp]: "map fst (map_ran f al) = map fst al"
  by (simp add: map_ran_def case_prod_beta)

lemma dom_map_ran: "fst ` set (map_ran f al) = fst ` set al"
  by (simp add: map_ran_def image_image split_def)

lemma map_ran_conv: "map_of (map_ran f al) k = map_option (f k) (map_of al k)"
  by (induct al) auto

lemma distinct_map_ran: "distinct (map fst al) \<Longrightarrow> distinct (map fst (map_ran f al))"
  by simp

lemma map_ran_filter: "map_ran f [p\<leftarrow>ps. fst p \<noteq> a] = [p\<leftarrow>map_ran f ps. fst p \<noteq> a]"
  by (simp add: map_ran_def filter_map split_def comp_def)

lemma clearjunk_map_ran: "clearjunk (map_ran f al) = map_ran f (clearjunk al)"
  by (simp add: map_ran_def split_def clearjunk_map)


subsection \<open>\<open>merge\<close>\<close>

qualified definition merge :: "('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where "merge qs ps = foldr (\<lambda>(k, v). update k v) ps qs"

lemma merge_simps [simp]:
  "merge qs [] = qs"
  "merge qs (p#ps) = update (fst p) (snd p) (merge qs ps)"
  by (simp_all add: merge_def split_def)

lemma merge_updates: "merge qs ps = updates (rev (map fst ps)) (rev (map snd ps)) qs"
  by (simp add: merge_def updates_def foldr_conv_fold zip_rev zip_map_fst_snd)

lemma dom_merge: "fst ` set (merge xs ys) = fst ` set xs \<union> fst ` set ys"
  by (induct ys arbitrary: xs) (auto simp add: dom_update)

lemma distinct_merge: "distinct (map fst xs) \<Longrightarrow> distinct (map fst (merge xs ys))"
  by (simp add: merge_updates distinct_updates)

lemma clearjunk_merge: "clearjunk (merge xs ys) = merge (clearjunk xs) ys"
  by (simp add: merge_updates clearjunk_updates)

lemma merge_conv': "map_of (merge xs ys) = map_of xs ++ map_of ys"
proof -
  have "map_of \<circ> fold (case_prod update) (rev ys) =
      fold (\<lambda>(k, v) m. m(k \<mapsto> v)) (rev ys) \<circ> map_of"
    by (rule fold_commute) (simp add: update_conv' case_prod_beta split_def fun_eq_iff)
  then show ?thesis
    by (simp add: merge_def map_add_map_of_foldr foldr_conv_fold fun_eq_iff)
qed

corollary merge_conv: "map_of (merge xs ys) k = (map_of xs ++ map_of ys) k"
  by (simp add: merge_conv')

lemma merge_empty: "map_of (merge [] ys) = map_of ys"
  by (simp add: merge_conv')

lemma merge_assoc [simp]: "map_of (merge m1 (merge m2 m3)) = map_of (merge (merge m1 m2) m3)"
  by (simp add: merge_conv')

lemma merge_Some_iff:
  "map_of (merge m n) k = Some x \<longleftrightarrow>
    map_of n k = Some x \<or> map_of n k = None \<and> map_of m k = Some x"
  by (simp add: merge_conv' map_add_Some_iff)

lemmas merge_SomeD [dest!] = merge_Some_iff [THEN iffD1]

lemma merge_find_right [simp]: "map_of n k = Some v \<Longrightarrow> map_of (merge m n) k = Some v"
  by (simp add: merge_conv')

lemma merge_None [iff]: "(map_of (merge m n) k = None) = (map_of n k = None \<and> map_of m k = None)"
  by (simp add: merge_conv')

lemma merge_upd [simp]: "map_of (merge m (update k v n)) = map_of (update k v (merge m n))"
  by (simp add: update_conv' merge_conv')

lemma merge_updatess [simp]:
  "map_of (merge m (updates xs ys n)) = map_of (updates xs ys (merge m n))"
  by (simp add: updates_conv' merge_conv')

lemma merge_append: "map_of (xs @ ys) = map_of (merge ys xs)"
  by (simp add: merge_conv')


subsection \<open>\<open>compose\<close>\<close>

qualified function compose :: "('key \<times> 'a) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('key \<times> 'b) list"
  where
    "compose [] ys = []"
  | "compose (x # xs) ys =
      (case map_of ys (snd x) of
        None \<Rightarrow> compose (delete (fst x) xs) ys
      | Some v \<Rightarrow> (fst x, v) # compose xs ys)"
  by pat_completeness auto
termination
  by (relation "measure (length \<circ> fst)") (simp_all add: less_Suc_eq_le length_delete_le)

lemma compose_first_None [simp]: "map_of xs k = None \<Longrightarrow> map_of (compose xs ys) k = None"
  by (induct xs ys rule: compose.induct) (auto split: option.splits if_split_asm)

lemma compose_conv: "map_of (compose xs ys) k = (map_of ys \<circ>\<^sub>m map_of xs) k"
proof (induct xs ys rule: compose.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs ys)
  show ?case
  proof (cases "map_of ys (snd x)")
    case None
    with 2 have hyp: "map_of (compose (delete (fst x) xs) ys) k =
        (map_of ys \<circ>\<^sub>m map_of (delete (fst x) xs)) k"
      by simp
    show ?thesis
    proof (cases "fst x = k")
      case True
      from True delete_notin_dom [of k xs]
      have "map_of (delete (fst x) xs) k = None"
        by (simp add: map_of_eq_None_iff)
      with hyp show ?thesis
        using True None
        by simp
    next
      case False
      from False have "map_of (delete (fst x) xs) k = map_of xs k"
        by simp
      with hyp show ?thesis
        using False None by (simp add: map_comp_def)
    qed
  next
    case (Some v)
    with 2
    have "map_of (compose xs ys) k = (map_of ys \<circ>\<^sub>m map_of xs) k"
      by simp
    with Some show ?thesis
      by (auto simp add: map_comp_def)
  qed
qed

lemma compose_conv': "map_of (compose xs ys) = (map_of ys \<circ>\<^sub>m map_of xs)"
  by (rule ext) (rule compose_conv)

lemma compose_first_Some [simp]: "map_of xs k = Some v \<Longrightarrow> map_of (compose xs ys) k = map_of ys v"
  by (simp add: compose_conv)

lemma dom_compose: "fst ` set (compose xs ys) \<subseteq> fst ` set xs"
proof (induct xs ys rule: compose.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs ys)
  show ?case
  proof (cases "map_of ys (snd x)")
    case None
    with "2.hyps" have "fst ` set (compose (delete (fst x) xs) ys) \<subseteq> fst ` set (delete (fst x) xs)"
      by simp
    also have "\<dots> \<subseteq> fst ` set xs"
      by (rule dom_delete_subset)
    finally show ?thesis
      using None by auto
  next
    case (Some v)
    with "2.hyps" have "fst ` set (compose xs ys) \<subseteq> fst ` set xs"
      by simp
    with Some show ?thesis
      by auto
  qed
qed

lemma distinct_compose:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (compose xs ys))"
  using assms
proof (induct xs ys rule: compose.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs ys)
  show ?case
  proof (cases "map_of ys (snd x)")
    case None
    with 2 show ?thesis by simp
  next
    case (Some v)
    with 2 dom_compose [of xs ys] show ?thesis
      by auto
  qed
qed

lemma compose_delete_twist: "compose (delete k xs) ys = delete k (compose xs ys)"
proof (induct xs ys rule: compose.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs ys)
  show ?case
  proof (cases "map_of ys (snd x)")
    case None
    with 2 have hyp: "compose (delete k (delete (fst x) xs)) ys =
        delete k (compose (delete (fst x) xs) ys)"
      by simp
    show ?thesis
    proof (cases "fst x = k")
      case True
      with None hyp show ?thesis
        by (simp add: delete_idem)
    next
      case False
      from None False hyp show ?thesis
        by (simp add: delete_twist)
    qed
  next
    case (Some v)
    with 2 have hyp: "compose (delete k xs) ys = delete k (compose xs ys)"
      by simp
    with Some show ?thesis
      by simp
  qed
qed

lemma compose_clearjunk: "compose xs (clearjunk ys) = compose xs ys"
  by (induct xs ys rule: compose.induct)
    (auto simp add: map_of_clearjunk split: option.splits)

lemma clearjunk_compose: "clearjunk (compose xs ys) = compose (clearjunk xs) ys"
  by (induct xs rule: clearjunk.induct)
    (auto split: option.splits simp add: clearjunk_delete delete_idem compose_delete_twist)

lemma compose_empty [simp]: "compose xs [] = []"
  by (induct xs) (auto simp add: compose_delete_twist)

lemma compose_Some_iff:
  "(map_of (compose xs ys) k = Some v) \<longleftrightarrow>
    (\<exists>k'. map_of xs k = Some k' \<and> map_of ys k' = Some v)"
  by (simp add: compose_conv map_comp_Some_iff)

lemma map_comp_None_iff:
  "map_of (compose xs ys) k = None \<longleftrightarrow>
    (map_of xs k = None \<or> (\<exists>k'. map_of xs k = Some k' \<and> map_of ys k' = None))"
  by (simp add: compose_conv map_comp_None_iff)


subsection \<open>\<open>map_entry\<close>\<close>

qualified fun map_entry :: "'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where
    "map_entry k f [] = []"
  | "map_entry k f (p # ps) =
      (if fst p = k then (k, f (snd p)) # ps else p # map_entry k f ps)"

lemma map_of_map_entry:
  "map_of (map_entry k f xs) =
    (map_of xs)(k := case map_of xs k of None \<Rightarrow> None | Some v' \<Rightarrow> Some (f v'))"
  by (induct xs) auto

lemma dom_map_entry: "fst ` set (map_entry k f xs) = fst ` set xs"
  by (induct xs) auto

lemma distinct_map_entry:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (map_entry k f xs))"
  using assms by (induct xs) (auto simp add: dom_map_entry)


subsection \<open>\<open>map_default\<close>\<close>

fun map_default :: "'key \<Rightarrow> 'val \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
  where
    "map_default k v f [] = [(k, v)]"
  | "map_default k v f (p # ps) =
      (if fst p = k then (k, f (snd p)) # ps else p # map_default k v f ps)"

lemma map_of_map_default:
  "map_of (map_default k v f xs) =
    (map_of xs)(k := case map_of xs k of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (f v'))"
  by (induct xs) auto

lemma dom_map_default: "fst ` set (map_default k v f xs) = insert k (fst ` set xs)"
  by (induct xs) auto

lemma distinct_map_default:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (map_default k v f xs))"
  using assms by (induct xs) (auto simp add: dom_map_default)

end

end
