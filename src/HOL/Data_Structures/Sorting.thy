(* Author: Tobias Nipkow *)

section "Sorting"

theory Sorting
  imports
    Complex_Main
    "HOL-Library.Multiset"
    Define_Time_Function
begin

hide_const List.insort

declare Let_def [simp]


subsection "Insertion Sort"

fun insort1 :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort1 x [] = [x]" |
  "insort1 x (y#ys) =
  (if x \<le> y then x#y#ys else y#(insort1 x ys))"

fun insort :: "'a::linorder list \<Rightarrow> 'a list" where
  "insort [] = []" |
  "insort (x#xs) = insort1 x (insort xs)"


subsubsection "Functional Correctness"

lemma mset_insort1: "mset (insort1 x xs) = {#x#} + mset xs"
  by (induction xs) auto

lemma mset_insort: "mset (insort xs) = mset xs"
  by (induction xs) (auto simp: mset_insort1)

lemma set_insort1: "set (insort1 x xs) = {x} \<union> set xs"
  by(simp add: mset_insort1 flip: set_mset_mset)

lemma sorted_insort1: "sorted (insort1 a xs) = sorted xs"
  by (induction xs) (auto simp: set_insort1)

lemma sorted_insort: "sorted (insort xs)"
  by (induction xs) (auto simp: sorted_insort1)


subsubsection "Time Complexity"

time_fun insort1
time_fun insort

lemma T_insort1_length: "T_insort1 x xs \<le> length xs + 1"
  by (induction xs) auto

lemma length_insort1: "length (insort1 x xs) = length xs + 1"
  by (induction xs) auto

lemma length_insort: "length (insort xs) = length xs"
  by (metis Sorting.mset_insort size_mset)

lemma T_insort_length: "T_insort xs \<le> (length xs + 1) ^ 2"
proof(induction xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have "T_insort (x#xs) = T_insort xs + T_insort1 x (insort xs) + 1" by simp
  also have "\<dots> \<le> (length xs + 1) ^ 2 + T_insort1 x (insort xs) + 1"
    using Cons.IH by simp
  also have "\<dots> \<le> (length xs + 1) ^ 2 + length xs + 1 + 1"
    using T_insort1_length[of x "insort xs"] by (simp add: length_insort)
  also have "\<dots> \<le> (length(x#xs) + 1) ^ 2"
    by (simp add: power2_eq_square)
  finally show ?case .
qed


subsection "Merge Sort"

fun merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge [] ys = ys" |
  "merge xs [] = xs" |
  "merge (x#xs) (y#ys) = (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"

fun msort :: "'a::linorder list \<Rightarrow> 'a list" where
  "msort xs = (let n = length xs in
  if n \<le> 1 then xs
  else merge (msort (take (n div 2) xs)) (msort (drop (n div 2) xs)))"

declare msort.simps [simp del]


subsubsection "Functional Correctness"

lemma mset_merge: "mset(merge xs ys) = mset xs + mset ys"
  by(induction xs ys rule: merge.induct) auto

lemma mset_msort: "mset (msort xs) = mset xs"
proof(induction xs rule: msort.induct)
  case (1 xs)
  let ?n = "length xs"
  let ?ys = "take (?n div 2) xs"
  let ?zs = "drop (?n div 2) xs"
  show ?case
  proof cases
    assume "?n \<le> 1"
    thus ?thesis by(simp add: msort.simps[of xs])
  next
    assume "\<not> ?n \<le> 1"
    hence "mset (msort xs) = mset (msort ?ys) + mset (msort ?zs)"
      by(simp add: msort.simps[of xs] mset_merge)
    also have "\<dots> = mset ?ys + mset ?zs"
      using \<open>\<not> ?n \<le> 1\<close> by(simp add: "1.IH")
    also have "\<dots> = mset (?ys @ ?zs)" by (simp del: append_take_drop_id)
    also have "\<dots> = mset xs" by simp
    finally show ?thesis .
  qed
qed

text \<open>Via the previous lemma or directly:\<close>

lemma set_merge: "set(merge xs ys) = set xs \<union> set ys"
  by (metis mset_merge set_mset_mset set_mset_union)

lemma "set(merge xs ys) = set xs \<union> set ys"
  by(induction xs ys rule: merge.induct) (auto)

lemma sorted_merge: "sorted (merge xs ys) \<longleftrightarrow> (sorted xs \<and> sorted ys)"
  by(induction xs ys rule: merge.induct) (auto simp: set_merge)

lemma sorted_msort: "sorted (msort xs)"
proof(induction xs rule: msort.induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof cases
    assume "?n \<le> 1"
    thus ?thesis by(simp add: msort.simps[of xs] sorted01)
  next
    assume "\<not> ?n \<le> 1"
    thus ?thesis using "1.IH"
      by(simp add: sorted_merge msort.simps[of xs])
  qed
qed


subsubsection "Time Complexity"

text \<open>We only count the number of comparisons between list elements.\<close>

fun C_merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "C_merge [] ys = 0" |
  "C_merge xs [] = 0" |
  "C_merge (x#xs) (y#ys) = 1 + (if x \<le> y then C_merge xs (y#ys) else C_merge (x#xs) ys)"

lemma C_merge_ub: "C_merge xs ys \<le> length xs + length ys"
  by (induction xs ys rule: C_merge.induct) auto

fun C_msort :: "'a::linorder list \<Rightarrow> nat" where
  "C_msort xs =
  (let n = length xs;
       ys = take (n div 2) xs;
       zs = drop (n div 2) xs
   in if n \<le> 1 then 0
      else C_msort ys + C_msort zs + C_merge (msort ys) (msort zs))"

declare C_msort.simps [simp del]

lemma length_merge: "length(merge xs ys) = length xs + length ys"
  by (induction xs ys rule: merge.induct) auto

lemma length_msort: "length(msort xs) = length xs"
proof (induction xs rule: msort.induct)
  case (1 xs)
  show ?case
    by (auto simp: msort.simps [of xs] 1 length_merge)
qed
text \<open>Why structured proof?
   To have the name "xs" to specialize msort.simps with xs
   to ensure that msort.simps cannot be used recursively.
Also works without this precaution, but that is just luck.\<close>

lemma C_msort_le: "length xs = 2^k \<Longrightarrow> C_msort xs \<le> k * 2^k"
proof(induction k arbitrary: xs)
  case 0 thus ?case by (simp add: C_msort.simps)
next
  case (Suc k)
  let ?n = "length xs"
  let ?ys = "take (?n div 2) xs"
  let ?zs = "drop (?n div 2) xs"
  show ?case
  proof (cases "?n \<le> 1")
    case True
    thus ?thesis by(simp add: C_msort.simps)
  next
    case False
    have "C_msort(xs) =
      C_msort ?ys + C_msort ?zs + C_merge (msort ?ys) (msort ?zs)"
      by (simp add: C_msort.simps msort.simps)
    also have "\<dots> \<le> C_msort ?ys + C_msort ?zs + length ?ys + length ?zs"
      using C_merge_ub[of "msort ?ys" "msort ?zs"] length_msort[of ?ys] length_msort[of ?zs]
      by arith
    also have "\<dots> \<le> k * 2^k + C_msort ?zs + length ?ys + length ?zs"
      using Suc.IH[of ?ys] Suc.prems by simp
    also have "\<dots> \<le> k * 2^k + k * 2^k + length ?ys + length ?zs"
      using Suc.IH[of ?zs] Suc.prems by simp
    also have "\<dots> = 2 * k * 2^k + 2 * 2 ^ k"
      using Suc.prems by simp
    finally show ?thesis by simp
  qed
qed

(* Beware of implicit conversions: *)
lemma C_msort_log: "length xs = 2^k \<Longrightarrow> C_msort xs \<le> length xs * log 2 (length xs)"
  using C_msort_le[of xs k]
  by (metis log2_of_power_eq mult.commute of_nat_mono of_nat_mult) 


subsection "Bottom-Up Merge Sort"

fun merge_adj :: "('a::linorder) list list \<Rightarrow> 'a list list" where
  "merge_adj [] = []" |
  "merge_adj [xs] = [xs]" |
  "merge_adj (xs # ys # zss) = merge xs ys # merge_adj zss"

text \<open>For the termination proof of \<open>merge_all\<close> below.\<close>
lemma length_merge_adjacent[simp]: "length (merge_adj xs) = (length xs + 1) div 2"
  by (induction xs rule: merge_adj.induct) auto

fun merge_all :: "('a::linorder) list list \<Rightarrow> 'a list" where
  "merge_all [] = []" |
  "merge_all [xs] = xs" |
  "merge_all xss = merge_all (merge_adj xss)"

definition msort_bu :: "('a::linorder) list \<Rightarrow> 'a list" where
  "msort_bu xs = merge_all (map (\<lambda>x. [x]) xs)"


subsubsection "Functional Correctness"

abbreviation mset_mset :: "'a list list \<Rightarrow> 'a multiset" where
  "mset_mset xss \<equiv> \<Sum>\<^sub># (image_mset mset (mset xss))"

lemma mset_merge_adj:
  "mset_mset (merge_adj xss) = mset_mset xss"
  by(induction xss rule: merge_adj.induct) (auto simp: mset_merge)

lemma mset_merge_all:
  "mset (merge_all xss) = mset_mset xss"
  by(induction xss rule: merge_all.induct) (auto simp: mset_merge mset_merge_adj)

lemma mset_msort_bu: "mset (msort_bu xs) = mset xs"
  by(simp add: msort_bu_def mset_merge_all multiset.map_comp comp_def)

lemma sorted_merge_adj:
  "\<forall>xs \<in> set xss. sorted xs \<Longrightarrow> \<forall>xs \<in> set (merge_adj xss). sorted xs"
  by(induction xss rule: merge_adj.induct) (auto simp: sorted_merge)

lemma sorted_merge_all:
  "\<forall>xs \<in> set xss. sorted xs \<Longrightarrow> sorted (merge_all xss)"
  by (induction xss rule: merge_all.induct) (auto simp add: sorted_merge_adj)

lemma sorted_msort_bu: "sorted (msort_bu xs)"
  by(simp add: msort_bu_def sorted_merge_all)


subsubsection "Time Complexity"

fun C_merge_adj :: "('a::linorder) list list \<Rightarrow> nat" where
  "C_merge_adj [] = 0" |
  "C_merge_adj [xs] = 0" |
  "C_merge_adj (xs # ys # zss) = C_merge xs ys + C_merge_adj zss"

fun C_merge_all :: "('a::linorder) list list \<Rightarrow> nat" where
  "C_merge_all [] = 0" |
  "C_merge_all [xs] = 0" |
  "C_merge_all xss = C_merge_adj xss + C_merge_all (merge_adj xss)"

definition C_msort_bu :: "('a::linorder) list \<Rightarrow> nat" where
  "C_msort_bu xs = C_merge_all (map (\<lambda>x. [x]) xs)"

lemma length_merge_adj:
  "\<lbrakk> even(length xss); \<forall>xs \<in> set xss. length xs = m \<rbrakk>
  \<Longrightarrow> \<forall>xs \<in> set (merge_adj xss). length xs = 2*m"
  by(induction xss rule: merge_adj.induct) (auto simp: length_merge)

lemma C_merge_adj: "\<forall>xs \<in> set xss. length xs = m \<Longrightarrow> C_merge_adj xss \<le> m * length xss"
proof(induction xss rule: C_merge_adj.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 x y) thus ?case using C_merge_ub[of x y] by (simp add: algebra_simps)
qed

lemma C_merge_all: "\<lbrakk> \<forall>xs \<in> set xss. length xs = m; length xss = 2^k \<rbrakk>
  \<Longrightarrow> C_merge_all xss \<le> m * k * 2^k"
proof (induction xss arbitrary: k m rule: C_merge_all.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 xs ys xss)
  let ?xss = "xs # ys # xss"
  let ?xss2 = "merge_adj ?xss"
  obtain k' where k': "k = Suc k'" using "3.prems"(2)
    by (metis length_Cons nat.inject nat_power_eq_Suc_0_iff nat.exhaust)
  have "even (length ?xss)" using "3.prems"(2) k' by auto
  from length_merge_adj[OF this "3.prems"(1)]
  have *: "\<forall>x \<in> set(merge_adj ?xss). length x = 2*m" .
  have **: "length ?xss2 = 2 ^ k'" using "3.prems"(2) k' by auto
  have "C_merge_all ?xss = C_merge_adj ?xss + C_merge_all ?xss2" by simp
  also have "\<dots> \<le> m * 2^k + C_merge_all ?xss2"
    using "3.prems"(2) C_merge_adj[OF "3.prems"(1)] by (auto simp: algebra_simps)
  also have "\<dots> \<le> m * 2^k + (2*m) * k' * 2^k'"
    using "3.IH"[OF * **] by simp
  also have "\<dots> = m * k * 2^k"
    using k' by (simp add: algebra_simps)
  finally show ?case .
qed

corollary C_msort_bu: "length xs = 2 ^ k \<Longrightarrow> C_msort_bu xs \<le> k * 2 ^ k"
  using C_merge_all[of "map (\<lambda>x. [x]) xs" 1] by (simp add: C_msort_bu_def)


subsection "Quicksort"

fun quicksort :: "('a::linorder) list \<Rightarrow> 'a list" where
  "quicksort []     = []" |
  "quicksort (x#xs) = quicksort (filter (\<lambda>y. y < x) xs) @ [x] @ quicksort (filter (\<lambda>y. x \<le> y) xs)"

lemma mset_quicksort: "mset (quicksort xs) = mset xs"
  by (induction xs rule: quicksort.induct) (auto simp: not_le)

lemma set_quicksort: "set (quicksort xs) = set xs"
  by(rule mset_eq_setD[OF mset_quicksort])

lemma sorted_quicksort: "sorted (quicksort xs)"
proof (induction xs rule: quicksort.induct)
qed (auto simp: sorted_append set_quicksort)


subsection "Insertion Sort w.r.t. Keys and Stability"

hide_const List.insort_key

fun insort1_key :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort1_key f x [] = [x]" |
  "insort1_key f x (y # ys) = (if f x \<le> f y then x # y # ys else y # insort1_key f x ys)"

fun insort_key :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort_key f [] = []" |
  "insort_key f (x # xs) = insort1_key f x (insort_key f xs)"


subsubsection "Standard functional correctness"

lemma mset_insort1_key: "mset (insort1_key f x xs) = {#x#} + mset xs"
  by(induction xs) simp_all

lemma mset_insort_key: "mset (insort_key f xs) = mset xs"
  by(induction xs) (simp_all add: mset_insort1_key)

(* Inductive proof simpler than derivation from mset lemma: *)
lemma set_insort1_key: "set (insort1_key f x xs) = {x} \<union> set xs"
  by (induction xs) auto

lemma sorted_insort1_key: "sorted (map f (insort1_key f a xs)) = sorted (map f xs)"
  by(induction xs)(auto simp: set_insort1_key)

lemma sorted_insort_key: "sorted (map f (insort_key f xs))"
  by(induction xs)(simp_all add: sorted_insort1_key)


subsubsection "Stability"

lemma insort1_is_Cons: "\<forall>x\<in>set xs. f a \<le> f x \<Longrightarrow> insort1_key f a xs = a # xs"
  by (cases xs) auto

lemma filter_insort1_key_neg:
  "\<not> P x \<Longrightarrow> filter P (insort1_key f x xs) = filter P xs"
  by (induction xs) simp_all

lemma filter_insort1_key_pos:
  "sorted (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort1_key f x xs) = insort1_key f x (filter P xs)"
  by (induction xs) (auto, subst insort1_is_Cons, auto)

lemma sort_key_stable: "filter (\<lambda>y. f y = k) (insort_key f xs) = filter (\<lambda>y. f y = k) xs"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  thus ?case
  proof (cases "f a = k")
    case False thus ?thesis  by (simp add: Cons.IH filter_insort1_key_neg)
  next
    case True
    have "filter (\<lambda>y. f y = k) (insort_key f (a # xs))
      = filter (\<lambda>y. f y = k) (insort1_key f a (insort_key f xs))"  by simp
    also have "\<dots> = insort1_key f a (filter (\<lambda>y. f y = k) (insort_key f xs))"
      by (simp add: True filter_insort1_key_pos sorted_insort_key)
    also have "\<dots> = insort1_key f a (filter (\<lambda>y. f y = k) xs)"  by (simp add: Cons.IH)
    also have "\<dots> = a # (filter (\<lambda>y. f y = k) xs)"  by(simp add: True insort1_is_Cons)
    also have "\<dots> = filter (\<lambda>y. f y = k) (a # xs)" by (simp add: True)
    finally show ?thesis .
  qed
qed


subsection \<open>Uniqueness of Sorting\<close>

lemma sorting_unique:
  assumes "mset ys = mset xs" "sorted xs" "sorted ys"
  shows "xs = ys"
  using assms
proof (induction xs arbitrary: ys)
  case (Cons x xs ys')
  obtain y ys where ys': "ys' = y # ys"
    using Cons.prems by (cases ys') auto
  have "x = y"
    using Cons.prems unfolding ys'
  proof (induction x y arbitrary: xs ys rule: linorder_wlog)
    case (le x y xs ys)
    have "x \<in># mset (x # xs)"
      by simp
    also have "mset (x # xs) = mset (y # ys)"
      using le by simp
    finally show "x = y"
      using le by auto
  qed (simp_all add: eq_commute)
  thus ?case
    using Cons.prems Cons.IH[of ys] by (auto simp: ys')
qed auto


end
