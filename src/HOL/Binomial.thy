(*  Title:      HOL/Binomial.thy
    Author:     Jacques D. Fleuriot
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
    Author:     Chaitanya Mangla
    Author:     Manuel Eberl
*)

section \<open>Binomial Coefficients, Binomial Theorem, Inclusion-exclusion Principle\<close>

theory Binomial
  imports Presburger Factorial
begin

subsection \<open>Binomial coefficients\<close>

text \<open>This development is based on the work of Andy Gordon and Florian Kammueller.\<close>

text \<open>Combinatorial definition\<close>

definition binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "binomial n k = card {K\<in>Pow {0..<n}. card K = k}"

open_bundle binomial_syntax
begin
notation binomial  (infix \<open>choose\<close> 64)
end

lemma binomial_right_mono:
  assumes "m \<le> n" shows "m choose k \<le> n choose k"
proof -
  have "{K. K \<subseteq> {0..<m} \<and> card K = k} \<subseteq> {K. K \<subseteq> {0..<n} \<and> card K = k}"
    using assms by auto
  then show ?thesis
    by (simp add: binomial_def card_mono)
qed

theorem n_subsets:
  assumes "finite A"
  shows "card {B. B \<subseteq> A \<and> card B = k} = card A choose k"
proof -
  from assms obtain f where bij: "bij_betw f {0..<card A} A"
    by (blast dest: ex_bij_betw_nat_finite)
  then have [simp]: "card (f ` C) = card C" if "C \<subseteq> {0..<card A}" for C
    by (meson bij_betw_imp_inj_on bij_betw_subset card_image that)
  from bij have "bij_betw (image f) (Pow {0..<card A}) (Pow A)"
    by (rule bij_betw_Pow)
  then have "inj_on (image f) (Pow {0..<card A})"
    by (rule bij_betw_imp_inj_on)
  moreover have "{K. K \<subseteq> {0..<card A} \<and> card K = k} \<subseteq> Pow {0..<card A}"
    by auto
  ultimately have "inj_on (image f) {K. K \<subseteq> {0..<card A} \<and> card K = k}"
    by (rule inj_on_subset)
  then have "card {K. K \<subseteq> {0..<card A} \<and> card K = k} =
      card (image f ` {K. K \<subseteq> {0..<card A} \<and> card K = k})" (is "_ = card ?C")
    by (simp add: card_image)
  also have "?C = {K. K \<subseteq> f ` {0..<card A} \<and> card K = k}"
    by (auto elim!: subset_imageE)
  also have "f ` {0..<card A} = A"
    by (meson bij bij_betw_def)
  finally show ?thesis
    by (simp add: binomial_def)
qed

text \<open>Recursive characterization\<close>

lemma binomial_n_0 [simp]: "n choose 0 = 1"
proof -
  have "{K \<in> Pow {0..<n}. card K = 0} = {{}}"
    by (auto dest: finite_subset)
  then show ?thesis
    by (simp add: binomial_def)
qed

lemma binomial_0_Suc [simp]: "0 choose Suc k = 0"
  by (simp add: binomial_def)

lemma binomial_Suc_Suc [simp]: "Suc n choose Suc k = (n choose k) + (n choose Suc k)"
proof -
  let ?P = "\<lambda>n k. {K. K \<subseteq> {0..<n} \<and> card K = k}"
  let ?Q = "?P (Suc n) (Suc k)"
  have inj: "inj_on (insert n) (?P n k)"
    by rule (auto; metis atLeastLessThan_iff insert_iff less_irrefl subsetCE)
  have disjoint: "insert n ` ?P n k \<inter> ?P n (Suc k) = {}"
    by auto
  have "?Q = {K\<in>?Q. n \<in> K} \<union> {K\<in>?Q. n \<notin> K}"
    by auto
  also have "{K\<in>?Q. n \<in> K} = insert n ` ?P n k" (is "?A = ?B")
  proof (rule set_eqI)
    fix K
    have K_finite: "finite K" if "K \<subseteq> insert n {0..<n}"
      using that by (rule finite_subset) simp_all
    have Suc_card_K: "Suc (card K - Suc 0) = card K" if "n \<in> K"
      and "finite K"
    proof -
      from \<open>n \<in> K\<close> obtain L where "K = insert n L" and "n \<notin> L"
        by (blast elim: Set.set_insert)
      with that show ?thesis by (simp add: card.insert_remove)
    qed
    show "K \<in> ?A \<longleftrightarrow> K \<in> ?B"
      by (subst in_image_insert_iff)
        (auto simp add: card.insert_remove subset_eq_atLeast0_lessThan_finite
          Diff_subset_conv K_finite Suc_card_K)
  qed
  also have "{K\<in>?Q. n \<notin> K} = ?P n (Suc k)"
    by (auto simp add: atLeast0_lessThan_Suc)
  finally show ?thesis using inj disjoint
    by (simp add: binomial_def card_Un_disjoint card_image)
qed

lemma binomial_eq_0: "n < k \<Longrightarrow> n choose k = 0"
  by (auto simp add: binomial_def dest: subset_eq_atLeast0_lessThan_card)

lemma zero_less_binomial: "k \<le> n \<Longrightarrow> n choose k > 0"
  by (induct n k rule: diff_induct) simp_all

lemma binomial_eq_0_iff [simp]: "n choose k = 0 \<longleftrightarrow> n < k"
  by (metis binomial_eq_0 less_numeral_extra(3) not_less zero_less_binomial)

lemma zero_less_binomial_iff [simp]: "n choose k > 0 \<longleftrightarrow> k \<le> n"
  by (metis binomial_eq_0_iff not_less0 not_less zero_less_binomial)

lemma binomial_n_n [simp]: "n choose n = 1"
  by (induct n) (simp_all add: binomial_eq_0)

lemma binomial_Suc_n [simp]: "Suc n choose n = Suc n"
  by (induct n) simp_all

lemma binomial_1 [simp]: "n choose Suc 0 = n"
  by (induct n) simp_all

lemma choose_one: "n choose 1 = n" for n :: nat
  by simp

lemma choose_reduce_nat:
  "0 < n \<Longrightarrow> 0 < k \<Longrightarrow>
    n choose k = ((n - 1) choose (k - 1)) + ((n - 1) choose k)"
  using binomial_Suc_Suc [of "n - 1" "k - 1"] by simp

lemma Suc_times_binomial_eq: "Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
proof (induction n arbitrary: k)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  show ?case 
  proof (cases k)
    case (Suc k')
    then show ?thesis
      using Suc.IH
      by (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq binomial_eq_0)
  qed auto
qed

lemma binomial_le_pow2: "n choose k \<le> 2^n"
proof (induction n arbitrary: k)
  case 0
  then show ?case
    using le_less less_le_trans by fastforce
next
  case (Suc n)
  show ?case
  proof (cases k)
    case (Suc k')
    then show ?thesis
      using Suc.IH by (simp add: add_le_mono mult_2)
  qed auto
qed

text \<open>The absorption property.\<close>
lemma Suc_times_binomial: "Suc k * (Suc n choose Suc k) = Suc n * (n choose k)"
  using Suc_times_binomial_eq by auto

text \<open>This is the well-known version of absorption, but it's harder to use
  because of the need to reason about division.\<close>
lemma binomial_Suc_Suc_eq_times: "(Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
  by (simp add: Suc_times_binomial_eq del: mult_Suc mult_Suc_right)

text \<open>Another version of absorption, with \<open>-1\<close> instead of \<open>Suc\<close>.\<close>
lemma times_binomial_minus1_eq: "0 < k \<Longrightarrow> k * (n choose k) = n * ((n - 1) choose (k - 1))"
  using Suc_times_binomial_eq [where n = "n - 1" and k = "k - 1"]
  by (auto split: nat_diff_split)


subsection \<open>The binomial theorem (courtesy of Tobias Nipkow):\<close>

text \<open>Avigad's version, generalized to any commutative ring\<close>
theorem (in comm_semiring_1) binomial_ring:
  "(a + b :: 'a)^n = (\<Sum>k\<le>n. (of_nat (n choose k)) * a^k * b^(n-k))"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have decomp: "{0..n+1} = {0} \<union> {n + 1} \<union> {1..n}" and decomp2: "{0..n} = {0} \<union> {1..n}"
    by auto
  have "(a + b)^(n+1) = (a + b) * (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n - k))"
    using Suc.hyps by simp
  also have "\<dots> = a * (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n-k)) +
      b * (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n-k))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * a^(k+1) * b^(n-k)) +
      (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n - k + 1))"
    by (auto simp add: sum_distrib_left ac_simps)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * a^k * b^(n + 1 - k)) +
      (\<Sum>k=1..n+1. of_nat (n choose (k - 1)) * a^k * b^(n + 1 - k))"
    by (simp add: atMost_atLeast0 sum.shift_bounds_cl_Suc_ivl Suc_diff_le field_simps del: sum.cl_ivl_Suc)
  also have "\<dots> = b^(n + 1) +
      (\<Sum>k=1..n. of_nat (n choose k) * a^k * b^(n + 1 - k)) + (a^(n + 1) +
      (\<Sum>k=1..n. of_nat (n choose (k - 1)) * a^k * b^(n + 1 - k)))"
      using sum.nat_ivl_Suc' [of 1 n "\<lambda>k. of_nat (n choose (k-1)) * a ^ k * b ^ (n + 1 - k)"]
    by (simp add: sum.atLeast_Suc_atMost atMost_atLeast0)
  also have "\<dots> = a^(n + 1) + b^(n + 1) +
      (\<Sum>k=1..n. of_nat (n + 1 choose k) * a^k * b^(n + 1 - k))"
    by (auto simp add: field_simps sum.distrib [symmetric] choose_reduce_nat)
  also have "\<dots> = (\<Sum>k\<le>n+1. of_nat (n + 1 choose k) * a^k * b^(n + 1 - k))"
    using decomp by (simp add: atMost_atLeast0 field_simps)
  finally show ?case
    by simp
qed


text \<open>Original version for the naturals.\<close>
corollary binomial: "(a + b :: nat)^n = (\<Sum>k\<le>n. (of_nat (n choose k)) * a^k * b^(n - k))"
  using binomial_ring [of "int a" "int b" n]
  by (simp only: of_nat_add [symmetric] of_nat_mult [symmetric] of_nat_power [symmetric]
      of_nat_sum [symmetric] of_nat_eq_iff of_nat_id)

lemma binomial_fact_lemma: "k \<le> n \<Longrightarrow> fact k * fact (n - k) * (n choose k) = fact n"
proof (induct n arbitrary: k rule: nat_less_induct)
  fix n k
  assume H: "\<forall>m<n. \<forall>x\<le>m. fact x * fact (m - x) * (m choose x) = fact m"
  assume kn: "k \<le> n"
  let ?ths = "fact k * fact (n - k) * (n choose k) = fact n"
  consider "n = 0 \<or> k = 0 \<or> n = k" | m h where "n = Suc m" "k = Suc h" "h < m"
    using kn by atomize_elim presburger
  then show "fact k * fact (n - k) * (n choose k) = fact n"
  proof cases
    case 1
    with kn show ?thesis by auto
  next
    case 2
    note n = \<open>n = Suc m\<close>
    note k = \<open>k = Suc h\<close>
    note hm = \<open>h < m\<close>
    have mn: "m < n"
      using n by arith
    have hm': "h \<le> m"
      using hm by arith
    have km: "k \<le> m"
      using hm k n kn by arith
    have "m - h = Suc (m - Suc h)"
      using  k km hm by arith
    with km k have "fact (m - h) = (m - h) * fact (m - k)"
      by simp
    with n k have "fact k * fact (n - k) * (n choose k) =
        k * (fact h * fact (m - h) * (m choose h)) +
        (m - h) * (fact k * fact (m - k) * (m choose k))"
      by (simp add: field_simps)
    also have "\<dots> = (k + (m - h)) * fact m"
      using H[rule_format, OF mn hm'] H[rule_format, OF mn km]
      by (simp add: field_simps)
    finally show ?thesis
      using k n km by simp
  qed
qed

lemma binomial_fact':
  assumes "k \<le> n"
  shows "n choose k = fact n div (fact k * fact (n - k))"
  using binomial_fact_lemma [OF assms]
  by (metis fact_nonzero mult_eq_0_iff nonzero_mult_div_cancel_left)

lemma binomial_fact:
  assumes kn: "k \<le> n"
  shows "(of_nat (n choose k) :: 'a::field_char_0) = fact n / (fact k * fact (n - k))"
  using binomial_fact_lemma[OF kn]
  by (metis (mono_tags, lifting) fact_nonzero mult_eq_0_iff nonzero_mult_div_cancel_left of_nat_fact of_nat_mult)

lemma fact_binomial:
  assumes "k \<le> n"
  shows "fact k * of_nat (n choose k) = (fact n / fact (n - k) :: 'a::field_char_0)"
  unfolding binomial_fact [OF assms] by (simp add: field_simps)

lemma binomial_fact_pow: "(n choose s) * fact s \<le> n^s"
proof (cases "s \<le> n")
  case True
  then show ?thesis
    by (smt (verit) binomial_fact_lemma mult.assoc mult.commute fact_div_fact_le_pow fact_nonzero nonzero_mult_div_cancel_right) 
qed (simp add: binomial_eq_0)

lemma choose_two: "n choose 2 = n * (n - 1) div 2"
proof (cases "n \<ge> 2")
  case False
  then have "n = 0 \<or> n = 1"
    by auto
  then show ?thesis by auto
next
  case True
  define m where "m = n - 2"
  with True have "n = m + 2"
    by simp
  then have "fact n = n * (n - 1) * fact (n - 2)"
    by (simp add: fact_prod_Suc atLeast0_lessThan_Suc algebra_simps)
  with True show ?thesis
    by (simp add: binomial_fact')
qed

lemma choose_row_sum: "(\<Sum>k\<le>n. n choose k) = 2^n"
  using binomial [of 1 "1" n] by (simp add: numeral_2_eq_2)

lemma sum_choose_lower: "(\<Sum>k\<le>n. (r+k) choose k) = Suc (r+n) choose n"
  by (induct n) auto

lemma sum_choose_upper: "(\<Sum>k\<le>n. k choose m) = Suc n choose Suc m"
  by (induct n) auto

lemma choose_alternating_sum:
  "n > 0 \<Longrightarrow> (\<Sum>i\<le>n. (-1)^i * of_nat (n choose i)) = (0 :: 'a::comm_ring_1)"
  using binomial_ring[of "-1 :: 'a" 1 n]
  by (simp add: atLeast0AtMost mult_of_nat_commute zero_power)

lemma choose_even_sum:
  assumes "n > 0"
  shows "2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0) = (2 ^ n :: 'a::comm_ring_1)"
proof -
  have "2 ^ n = (\<Sum>i\<le>n. of_nat (n choose i)) + (\<Sum>i\<le>n. (-1) ^ i * of_nat (n choose i) :: 'a)"
    using choose_row_sum[of n]
    by (simp add: choose_alternating_sum assms atLeast0AtMost of_nat_sum[symmetric])
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) + (-1) ^ i * of_nat (n choose i))"
    by (simp add: sum.distrib)
  also have "\<dots> = 2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0)"
    by (subst sum_distrib_left, intro sum.cong) simp_all
  finally show ?thesis ..
qed

lemma choose_odd_sum:
  assumes "n > 0"
  shows "2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0) = (2 ^ n :: 'a::comm_ring_1)"
proof -
  have "2 ^ n = (\<Sum>i\<le>n. of_nat (n choose i)) - (\<Sum>i\<le>n. (-1) ^ i * of_nat (n choose i) :: 'a)"
    using choose_row_sum[of n]
    by (simp add: choose_alternating_sum assms atLeast0AtMost of_nat_sum[symmetric])
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) - (-1) ^ i * of_nat (n choose i))"
    by (simp add: sum_subtractf)
  also have "\<dots> = 2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0)"
    by (subst sum_distrib_left, intro sum.cong) simp_all
  finally show ?thesis ..
qed

text\<open>NW diagonal sum property\<close>
lemma sum_choose_diagonal:
  assumes "m \<le> n"
  shows "(\<Sum>k\<le>m. (n - k) choose (m - k)) = Suc n choose m"
proof -
  have "(\<Sum>k\<le>m. (n-k) choose (m - k)) = (\<Sum>k\<le>m. (n - m + k) choose k)"
    using sum.atLeastAtMost_rev [of "\<lambda>k. (n - k) choose (m - k)" 0 m] assms
    by (simp add: atMost_atLeast0)
  also have "\<dots> = Suc (n - m + m) choose m"
    by (rule sum_choose_lower)
  also have "\<dots> = Suc n choose m"
    using assms by simp
  finally show ?thesis .
qed


subsection \<open>Generalized binomial coefficients\<close>

definition gbinomial :: "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"  (infix \<open>gchoose\<close> 64)
  where gbinomial_prod_rev: "a gchoose k = (\<Prod>i=0..<k. a - of_nat i) div fact k"

lemma gbinomial_0 [simp]:
  "a gchoose 0 = 1"
  "0 gchoose (Suc k) = 0"
  by (simp_all add: gbinomial_prod_rev prod.atLeast0_lessThan_Suc_shift del: prod.op_ivl_Suc)

lemma gbinomial_Suc: "a gchoose (Suc k) = prod (\<lambda>i. a - of_nat i) {0..k} div fact (Suc k)"
  by (simp add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)

lemma gbinomial_1 [simp]: "a gchoose 1 = a"
  by (simp add: gbinomial_prod_rev lessThan_Suc)

lemma gbinomial_Suc0 [simp]: "a gchoose Suc 0 = a"
  by (simp add: gbinomial_prod_rev lessThan_Suc)

lemma gbinomial_0_left: "0 gchoose k = (if k = 0 then 1 else 0)"
  by (cases k) simp_all

lemma gbinomial_mult_fact: "fact k * (a gchoose k) = (\<Prod>i = 0..<k. a - of_nat i)"
  for a :: "'a::field_char_0"
  by (simp_all add: gbinomial_prod_rev field_simps)

lemma gbinomial_mult_fact': "(a gchoose k) * fact k = (\<Prod>i = 0..<k. a - of_nat i)"
  for a :: "'a::field_char_0"
  using gbinomial_mult_fact [of k a] by (simp add: ac_simps)

lemma gbinomial_pochhammer: "a gchoose k = (- 1) ^ k * pochhammer (- a) k / fact k"
  for a :: "'a::field_char_0"
proof (cases k)
  case (Suc k')
  then have "a gchoose k = pochhammer (a - of_nat k') (Suc k') / ((1 + of_nat k') * fact k')"
    by (simp add: gbinomial_prod_rev pochhammer_prod_rev atLeastLessThanSuc_atLeastAtMost
        prod.atLeast_Suc_atMost_Suc_shift of_nat_diff flip: power_mult_distrib prod.cl_ivl_Suc)
  then show ?thesis
    by (simp add: pochhammer_minus Suc)
qed auto

lemma gbinomial_pochhammer': "a gchoose k = pochhammer (a - of_nat k + 1) k / fact k"
  for a :: "'a::field_char_0"
proof -
  have "a gchoose k = ((-1)^k * (-1)^k) * pochhammer (a - of_nat k + 1) k / fact k"
    by (simp add: gbinomial_pochhammer pochhammer_minus mult_ac)
  also have "(-1 :: 'a)^k * (-1)^k = 1"
    by (subst power_add [symmetric]) simp
  finally show ?thesis
    by simp
qed

lemma gbinomial_binomial: "n gchoose k = n choose k"
proof (cases "k \<le> n")
  case False
  then have "n < k"
    by (simp add: not_le)
  then have "0 \<in> ((-) n) ` {0..<k}"
    by auto
  then have "prod ((-) n) {0..<k} = 0"
    by (auto intro: prod_zero)
  with \<open>n < k\<close> show ?thesis
    by (simp add: binomial_eq_0 gbinomial_prod_rev prod_zero)
next
  case True
  from True have *: "prod ((-) n) {0..<k} = \<Prod>{Suc (n - k)..n}"
    by (intro prod.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"]) auto
  from True have "n choose k = fact n div (fact k * fact (n - k))"
    by (rule binomial_fact')
  with * show ?thesis
    by (simp add: gbinomial_prod_rev mult.commute [of "fact k"] div_mult2_eq fact_div_fact)
qed

lemma of_nat_gbinomial: "of_nat (n gchoose k) = (of_nat n gchoose k :: 'a::field_char_0)"
proof (cases "k \<le> n")
  case False
  then show ?thesis
    by (simp add: not_le gbinomial_binomial binomial_eq_0 gbinomial_prod_rev)
next
  case True
  define m where "m = n - k"
  with True have n: "n = m + k"
    by arith
  from n have "fact n = ((\<Prod>i = 0..<m + k. of_nat (m + k - i) ):: 'a)"
    by (simp add: fact_prod_rev)
  also have "\<dots> = ((\<Prod>i\<in>{0..<k} \<union> {k..<m + k}. of_nat (m + k - i)) :: 'a)"
    by (simp add: ivl_disj_un)
  finally have "fact n = (fact m * (\<Prod>i = 0..<k. of_nat m + of_nat k - of_nat i) :: 'a)"
    using prod.shift_bounds_nat_ivl [of "\<lambda>i. of_nat (m + k - i) :: 'a" 0 k m]
    by (simp add: fact_prod_rev [of m] prod.union_disjoint of_nat_diff)
  then have "fact n / fact (n - k) = ((\<Prod>i = 0..<k. of_nat n - of_nat i) :: 'a)"
    by (simp add: n)
  with True have "fact k * of_nat (n gchoose k) = (fact k * (of_nat n gchoose k) :: 'a)"
    by (simp only: gbinomial_mult_fact [of k "of_nat n"] gbinomial_binomial [of n k] fact_binomial)
  then show ?thesis
    by simp
qed

lemma binomial_gbinomial: "of_nat (n choose k) = (of_nat n gchoose k :: 'a::field_char_0)"
  using gbinomial_binomial of_nat_gbinomial by auto

setup
  \<open>Sign.add_const_constraint (\<^const_name>\<open>gbinomial\<close>, SOME \<^typ>\<open>'a::field_char_0 \<Rightarrow> nat \<Rightarrow> 'a\<close>)\<close>

lemma gbinomial_mult_1:
  fixes a :: "'a::field_char_0"
  shows "a * (a gchoose k) = of_nat k * (a gchoose k) + of_nat (Suc k) * (a gchoose (Suc k))"
  (is "?l = ?r")
proof -
  have "?r = ((- 1) ^k * pochhammer (- a) k / fact k) * (of_nat k - (- a + of_nat k))"
    unfolding gbinomial_pochhammer pochhammer_Suc right_diff_distrib power_Suc
    by (auto simp add: field_simps simp del: of_nat_Suc)
  also have "\<dots> = ?l"
    by (simp add: field_simps gbinomial_pochhammer)
  finally show ?thesis ..
qed

lemma gbinomial_mult_1':
  "(a gchoose k) * a = of_nat k * (a gchoose k) + of_nat (Suc k) * (a gchoose (Suc k))"
  for a :: "'a::field_char_0"
  by (simp add: mult.commute gbinomial_mult_1)

lemma gbinomial_Suc_Suc: "(a + 1) gchoose (Suc k) = (a gchoose k) + (a gchoose (Suc k))"
  for a :: "'a::field_char_0"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq0: "(\<Prod>i\<in>{1..k}. (a + 1) - of_nat i) = (\<Prod>i\<in>{0..h}. a - of_nat i)"
  proof (rule prod.reindex_cong)
    show "{1..k} = Suc ` {0..h}"
      using Suc by (auto simp add: image_Suc_atMost)
  qed auto
  have "fact (Suc k) * ((a gchoose k) + (a gchoose (Suc k))) =
      (a gchoose Suc h) * (fact (Suc (Suc h))) +
      (a gchoose Suc (Suc h)) * (fact (Suc (Suc h)))"
    by (simp add: Suc field_simps del: fact_Suc)
  also have "\<dots> =
    (a gchoose Suc h) * of_nat (Suc (Suc h) * fact (Suc h)) + (\<Prod>i=0..Suc h. a - of_nat i)"
    by (metis atLeastLessThanSuc_atLeastAtMost fact_Suc gbinomial_mult_fact mult.commute of_nat_fact of_nat_mult)
  also have "\<dots> =
    (fact (Suc h) * (a gchoose Suc h)) * of_nat (Suc (Suc h)) + (\<Prod>i=0..Suc h. a - of_nat i)"
    by (simp only: fact_Suc mult.commute mult.left_commute of_nat_fact of_nat_id of_nat_mult)
  also have "\<dots> =
    of_nat (Suc (Suc h)) * (\<Prod>i=0..h. a - of_nat i) + (\<Prod>i=0..Suc h. a - of_nat i)"
    unfolding gbinomial_mult_fact atLeastLessThanSuc_atLeastAtMost by auto
  also have "\<dots> =
    (\<Prod>i=0..Suc h. a - of_nat i) + (of_nat h * (\<Prod>i=0..h. a - of_nat i) + 2 * (\<Prod>i=0..h. a - of_nat i))"
    by (simp add: field_simps)
  also have "\<dots> =
    ((a gchoose Suc h) * (fact (Suc h)) * of_nat (Suc k)) + (\<Prod>i\<in>{0..Suc h}. a - of_nat i)"
    unfolding gbinomial_mult_fact'
    by (simp add: comm_semiring_class.distrib field_simps Suc atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = (\<Prod>i\<in>{0..h}. a - of_nat i) * (a + 1)"
    unfolding gbinomial_mult_fact' atLeast0_atMost_Suc
    by (simp add: field_simps Suc atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = (\<Prod>i\<in>{0..k}. (a + 1) - of_nat i)"
    using eq0
    by (simp add: Suc prod.atLeast0_atMost_Suc_shift del: prod.cl_ivl_Suc)
  also have "\<dots> = (fact (Suc k)) * ((a + 1) gchoose (Suc k))"
    by (simp only: gbinomial_mult_fact atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis
    using fact_nonzero [of "Suc k"] by auto
qed

lemma gbinomial_reduce_nat: "0 < k \<Longrightarrow> a gchoose k = (a-1 gchoose k-1) + (a-1 gchoose k)"
  for a :: "'a::field_char_0"
  by (metis Suc_pred' diff_add_cancel gbinomial_Suc_Suc)

lemma gchoose_row_sum_weighted:
  "(\<Sum>k = 0..m. (r gchoose k) * (r/2 - of_nat k)) = of_nat(Suc m) / 2 * (r gchoose (Suc m))"
  for r :: "'a::field_char_0"
  by (induct m) (simp_all add: field_simps distrib gbinomial_mult_1)

lemma binomial_symmetric:
  assumes kn: "k \<le> n"
  shows "n choose k = n choose (n - k)"
proof -
  have kn': "n - k \<le> n"
    using kn by arith
  from binomial_fact_lemma[OF kn] binomial_fact_lemma[OF kn']
  have "fact k * fact (n - k) * (n choose k) = fact (n - k) * fact (n - (n - k)) * (n choose (n - k))"
    by simp
  then show ?thesis
    using kn by simp
qed

lemma choose_rising_sum:
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))"
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose m)"
proof -
  show "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))"
    by (induct m) simp_all
  also have "\<dots> = (n + m + 1) choose m"
    by (subst binomial_symmetric) simp_all
  finally show "(\<Sum>j\<le>m. ((n + j) choose n)) = (n + m + 1) choose m" .
qed

lemma choose_linear_sum: "(\<Sum>i\<le>n. i * (n choose i)) = n * 2 ^ (n - 1)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  have "(\<Sum>i\<le>n. i * (n choose i)) = (\<Sum>i\<le>Suc m. i * (Suc m choose i))"
    by (simp add: Suc)
  also have "\<dots> = Suc m * 2 ^ m"
    unfolding sum.atMost_Suc_shift Suc_times_binomial sum_distrib_left[symmetric]
    by (simp add: choose_row_sum)
  finally show ?thesis
    using Suc by simp
qed

lemma choose_alternating_linear_sum:
  assumes "n \<noteq> 1"
  shows "(\<Sum>i\<le>n. (-1)^i * of_nat i * of_nat (n choose i) :: 'a::comm_ring_1) = 0"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  with assms have "m > 0"
    by simp
  have "(\<Sum>i\<le>n. (-1) ^ i * of_nat i * of_nat (n choose i) :: 'a) =
      (\<Sum>i\<le>Suc m. (-1) ^ i * of_nat i * of_nat (Suc m choose i))"
    by (simp add: Suc)
  also have "\<dots> = (\<Sum>i\<le>m. (-1) ^ (Suc i) * of_nat (Suc i * (Suc m choose Suc i)))"
    by (simp only: sum.atMost_Suc_shift sum_distrib_left[symmetric] mult_ac of_nat_mult) simp
  also have "\<dots> = - of_nat (Suc m) * (\<Sum>i\<le>m. (-1) ^ i * of_nat (m choose i))"
    proof (subst sum_distrib_left, rule sum.cong[OF refl], subst Suc_times_binomial)
    qed (simp add: algebra_simps)
  also have "(\<Sum>i\<le>m. (-1 :: 'a) ^ i * of_nat ((m choose i))) = 0"
    using choose_alternating_sum[OF \<open>m > 0\<close>] by simp
  finally show ?thesis
    by simp
qed

lemma vandermonde: "(\<Sum>k\<le>r. (m choose k) * (n choose (r - k))) = (m + n) choose r"
proof (induct n arbitrary: r)
  case 0
  have "(\<Sum>k\<le>r. (m choose k) * (0 choose (r - k))) = (\<Sum>k\<le>r. if k = r then (m choose k) else 0)"
    by (intro sum.cong) simp_all
  also have "\<dots> = m choose r"
    by simp
  finally show ?case
    by simp
next
  case (Suc n r)
  show ?case
    by (cases r) (simp_all add: Suc [symmetric] algebra_simps sum.distrib Suc_diff_le)
qed

lemma choose_square_sum: "(\<Sum>k\<le>n. (n choose k)^2) = ((2*n) choose n)"
  using vandermonde[of n n n]
  by (simp add: power2_eq_square mult_2 binomial_symmetric [symmetric])

lemma pochhammer_binomial_sum:
  fixes a b :: "'a::comm_ring_1"
  shows "pochhammer (a + b) n = (\<Sum>k\<le>n. of_nat (n choose k) * pochhammer a k * pochhammer b (n - k))"
proof (induction n arbitrary: a b)
  case 0
  then show ?case by simp
next
  case (Suc n a b)
  have "(\<Sum>k\<le>Suc n. of_nat (Suc n choose k) * pochhammer a k * pochhammer b (Suc n - k)) =
      (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
      ((\<Sum>i\<le>n. of_nat (n choose Suc i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
      pochhammer b (Suc n))"
    by (subst sum.atMost_Suc_shift) (simp add: ring_distribs sum.distrib)
  also have "(\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a (Suc i) * pochhammer b (n - i)) =
      a * pochhammer ((a + 1) + b) n"
    by (subst Suc) (simp add: sum_distrib_left pochhammer_rec mult_ac)
  also have "(\<Sum>i\<le>n. of_nat(n choose Suc i) * pochhammer a (Suc i) * pochhammer b (n-i)) + pochhammer b (Suc n)
           = of_nat (n choose 0) * pochhammer a 0 * pochhammer b (Suc n - 0) 
           + (\<Sum>i = Suc 0..Suc n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    unfolding sum.shift_bounds_cl_Suc_ivl by (simp add: atLeast0AtMost)
  also have "\<dots> = (\<Sum>i=0..Suc n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    by (simp add: sum.atLeast_Suc_atMost)
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    using Suc by (intro sum.mono_neutral_right) (auto simp: not_le binomial_eq_0)
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc (n - i)))"
    by (simp add: Suc_diff_le)
  also have "\<dots> = b * pochhammer (a + (b + 1)) n"
    by (subst Suc) (simp add: sum_distrib_left mult_ac pochhammer_rec)
  also have "a * pochhammer ((a + 1) + b) n + b * pochhammer (a + (b + 1)) n =
      pochhammer (a + b) (Suc n)"
    by (simp add: pochhammer_rec algebra_simps)
  finally show ?case ..
qed

text \<open>Contributed by Manuel Eberl, generalised by LCP.
  Alternative definition of the binomial coefficient as \<^term>\<open>\<Prod>i<k. (n - i) / (k - i)\<close>.\<close>
lemma gbinomial_altdef_of_nat: "a gchoose k = (\<Prod>i = 0..<k. (a - of_nat i) / of_nat (k - i) :: 'a)"
  for k :: nat and a :: "'a::field_char_0"
  by (simp add: prod_dividef gbinomial_prod_rev fact_prod_rev)

lemma gbinomial_ge_n_over_k_pow_k:
  fixes k :: nat
    and a :: "'a::linordered_field"
  assumes "of_nat k \<le> a"
  shows "(a / of_nat k :: 'a) ^ k \<le> a gchoose k"
proof -
  have x: "0 \<le> a"
    using assms of_nat_0_le_iff order_trans by blast
  have "(a / of_nat k :: 'a) ^ k = (\<Prod>i = 0..<k. a / of_nat k :: 'a)"
    by simp
  also have "\<dots> \<le> a gchoose k"
  proof -
    have "\<And>i. i < k \<Longrightarrow> 0 \<le> a / of_nat k"
      by (simp add: x zero_le_divide_iff)
    moreover have "a / of_nat k \<le> (a - of_nat i) / of_nat (k - i)" if "i < k" for i
    proof -
      from assms have "a * of_nat i \<ge> of_nat (i * k)"
        by (metis mult.commute mult_le_cancel_right of_nat_less_0_iff of_nat_mult)
      then have "a * of_nat k - a * of_nat i \<le> a * of_nat k - of_nat (i * k)"
        by arith
      then have "a * of_nat (k - i) \<le> (a - of_nat i) * of_nat k"
        using \<open>i < k\<close> by (simp add: algebra_simps zero_less_mult_iff of_nat_diff)
      then have "a * of_nat (k - i) \<le> (a - of_nat i) * (of_nat k :: 'a)"
        by blast
      with assms show ?thesis
        using \<open>i < k\<close> by (simp add: field_simps)
    qed
    ultimately show ?thesis
      unfolding gbinomial_altdef_of_nat
      by (intro prod_mono) auto
  qed
  finally show ?thesis .
qed

lemma gbinomial_negated_upper: "(a gchoose k) = (-1) ^ k * ((of_nat k - a - 1) gchoose k)"
  by (simp add: gbinomial_pochhammer pochhammer_minus algebra_simps)

lemma gbinomial_minus: "((-a) gchoose k) = (-1) ^ k * ((a + of_nat k - 1) gchoose k)"
  by (metis add.commute diff_minus_eq_add gbinomial_negated_upper)

lemma Suc_times_gbinomial: "of_nat (Suc k) * ((a + 1) gchoose (Suc k)) = (a + 1) * (a gchoose k)"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case Suc
  have "((a + 1) gchoose (Suc k)) = (\<Prod>i = 0..k. a + (1 - of_nat i)) / fact (Suc k)"
    by (simp add: add_diff_eq gbinomial_Suc)
  also have "(\<Prod>i = 0..k. a + (1 - of_nat i)) = (a + 1) * (\<Prod>i = 0..k-1. a - of_nat i)"
    by (simp add: Suc prod.atLeast0_atMost_Suc_shift del: prod.cl_ivl_Suc)
  also have "\<dots> / fact (Suc k) = (a + 1) / of_nat (Suc k) * (a gchoose k)"
    by (simp_all add: Suc gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis
    using of_nat_neq_0 by auto
qed

lemma gbinomial_factors: "((a + 1) gchoose (Suc k)) = (a + 1) / of_nat (Suc k) * (a gchoose k)"
  by (metis Suc_times_gbinomial nonzero_mult_div_cancel_left of_nat_neq_0 times_divide_eq_left)

lemma gbinomial_rec: "((a + 1) gchoose (Suc k)) = (a gchoose k) * ((a + 1) / of_nat (Suc k))"
  by (simp add: gbinomial_factors mult.commute plus_1_eq_Suc)

lemma gbinomial_of_nat_symmetric: "k \<le> n \<Longrightarrow> (of_nat n) gchoose k = (of_nat n) gchoose (n - k)"
  using binomial_symmetric[of k n] by (simp add: binomial_gbinomial [symmetric])


text \<open>The absorption identity (equation 5.5 \<^cite>\<open>\<open>p.~157\<close> in GKP_CM\<close>):
\[
{r \choose k} = \frac{r}{k}{r - 1 \choose k - 1},\quad \textnormal{integer } k \neq 0.
\]\<close>
lemma gbinomial_absorption': "k > 0 \<Longrightarrow> a gchoose k = (a / of_nat k) * (a - 1 gchoose (k - 1))"
  using gbinomial_rec[of "a - 1" "k - 1"]
  by (simp_all add: gbinomial_rec field_simps del: of_nat_Suc)

text \<open>The absorption identity is written in the following form to avoid
division by $k$ (the lower index) and therefore remove the $k \neq 0$
restriction \<^cite>\<open>\<open>p.~157\<close> in GKP_CM\<close>:
\[
k{r \choose k} = r{r - 1 \choose k - 1}, \quad \textnormal{integer } k.
\]\<close>
lemma gbinomial_absorption: "of_nat (Suc k) * (a gchoose Suc k) = a * ((a - 1) gchoose k)"
  by (metis Suc_times_gbinomial diff_eq_eq)

text \<open>The absorption identity for natural number binomial coefficients:\<close>
lemma binomial_absorption: "Suc k * (n choose Suc k) = n * ((n - 1) choose k)"
  using times_binomial_minus1_eq by fastforce

text \<open>The absorption companion identity for natural number coefficients,
  following the proof by GKP \<^cite>\<open>\<open>p.~157\<close> in GKP_CM\<close>:\<close>
lemma binomial_absorb_comp: "(n - k) * (n choose k) = n * ((n - 1) choose k)"
  (is "?lhs = ?rhs")
proof (cases "n \<le> k")
  case True
  then show ?thesis by auto
next
  case False
  then have "?rhs = Suc ((n - 1) - k) * (n choose Suc ((n - 1) - k))"
    using binomial_symmetric[of k "n - 1"] binomial_absorption[of "(n - 1) - k" n]
    by simp
  also have "Suc ((n - 1) - k) = n - k"
    using False by simp
  also have "n choose \<dots> = n choose k"
    using False by (intro binomial_symmetric [symmetric]) simp_all
  finally show ?thesis ..
qed

text \<open>The generalised absorption companion identity:\<close>
lemma gbinomial_absorb_comp: "(a - of_nat k) * (a gchoose k) = a * ((a - 1) gchoose k)"
  using pochhammer_absorb_comp[of a k] by (simp add: gbinomial_pochhammer)

lemma gbinomial_addition_formula:
  "a gchoose (Suc k) = ((a - 1) gchoose (Suc k)) + ((a - 1) gchoose k)"
  using gbinomial_Suc_Suc[of "a - 1" k] by (simp add: algebra_simps)

lemma binomial_addition_formula:
  "0 < n \<Longrightarrow> n choose (Suc k) = ((n - 1) choose (Suc k)) + ((n - 1) choose k)"
  by (metis Suc_diff_1 add.commute binomial_Suc_Suc)

text \<open>
  Equation 5.9 of the reference material \<^cite>\<open>\<open>p.~159\<close> in GKP_CM\<close> is a useful
  summation formula, operating on both indices:
  \[
   \sum\limits_{k \leq n}{r + k \choose k} = {r + n + 1 \choose n},
   \quad \textnormal{integer } n.
  \]
\<close>
lemma gbinomial_parallel_sum: "(\<Sum>k\<le>n. (a + of_nat k) gchoose k) = (a + of_nat n + 1) gchoose n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case
    using gbinomial_Suc_Suc[of "(a + of_nat m + 1)" m]
    by (simp add: add_ac)
qed


subsection \<open>Summation on the upper index\<close>

text \<open>
  Another summation formula is equation 5.10 of the reference material \<^cite>\<open>\<open>p.~160\<close> in GKP_CM\<close>,
  aptly named \emph{summation on the upper index}:\[\sum_{0 \leq k \leq n} {k \choose m} =
  {n + 1 \choose m + 1}, \quad \textnormal{integers } m, n \geq 0.\]
\<close>
lemma gbinomial_sum_up_index:
  "(\<Sum>j = 0..n. (of_nat j gchoose k) :: 'a::field_char_0) = (of_nat n + 1) gchoose (k + 1)"
proof (induct n)
  case 0
  show ?case
    using gbinomial_Suc_Suc[of 0 k]
    by (cases k) auto
next
  case (Suc n)
  then show ?case
    using gbinomial_Suc_Suc[of "of_nat (Suc n) :: 'a" k]
    by (simp add: add_ac)
qed

lemma gbinomial_index_swap:
  "((-1) ^ k) * ((- (of_nat n) - 1) gchoose k) = ((-1) ^ n) * ((- (of_nat k) - 1) gchoose n)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (of_nat (k + n) gchoose k)"
    by (simp add: gbinomial_negated_upper [of "- of_nat n - 1"])
  also have "\<dots> = (of_nat (k + n) gchoose n)"
    by (subst gbinomial_of_nat_symmetric; simp) 
  also have "\<dots> = ?rhs"
    by (subst gbinomial_negated_upper; simp) 
  finally show ?thesis .
qed

lemma gbinomial_sum_lower_neg: "(\<Sum>k\<le>m. (a gchoose k) * (- 1) ^ k) = (- 1) ^ m * (a - 1 gchoose m)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>k\<le>m. -(a + 1) + of_nat k gchoose k)"
    by (simp add: gbinomial_negated_upper [of a] power_mult_distrib diff_add_eq mult.commute)
  also have "\<dots>  = - a + of_nat m gchoose m"
    by (simp add: gbinomial_parallel_sum)
  also have "\<dots> = ?rhs"
    by (simp add: gbinomial_negated_upper [of "a-1"] power_mult_distrib)
  finally show ?thesis .
qed

lemma gbinomial_partial_row_sum:
  "(\<Sum>k\<le>m. (a gchoose k) * ((a / 2) - of_nat k)) = ((of_nat m + 1)/2) * (a gchoose (m + 1))"
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc mm)
  then have "(\<Sum>k\<le>Suc mm. (a gchoose k) * (a / 2 - of_nat k)) =
      (a - of_nat (Suc mm)) * (a gchoose Suc mm) / 2"
    by (simp add: field_simps)
  also have "\<dots> = a * (a - 1 gchoose Suc mm) / 2"
    by (subst gbinomial_absorb_comp) (rule refl)
  also have "\<dots> = (of_nat (Suc mm) + 1) / 2 * (a gchoose (Suc mm + 1))"
    by (subst gbinomial_absorption [symmetric]) simp
  finally show ?case .
qed

lemma sum_bounds_lt_plus1: "(\<Sum>k<mm. f (Suc k)) = (\<Sum>k=1..mm. f k)"
  by (induct mm) simp_all

lemma gbinomial_partial_sum_poly:
  "(\<Sum>k\<le>m. (of_nat m + a gchoose k) * x^k * y^(m-k)) =
    (\<Sum>k\<le>m. (-a gchoose k) * (-x)^k * (x + y)^(m-k))"
  (is "?lhs m = ?rhs m")
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  define G where "G i k = (of_nat i + a gchoose k) * x^k * y^(i - k)" for i k
  define S where "S = ?lhs"
  have SG_def: "S = (\<lambda>i. (\<Sum>k\<le>i. (G i k)))"
    unfolding S_def G_def ..

  have "S (Suc m) = G (Suc m) 0 + (\<Sum>k=Suc 0..Suc m. G (Suc m) k)"
    using SG_def by (simp add: sum.atLeast_Suc_atMost atLeast0AtMost [symmetric])
  also have "(\<Sum>k=Suc 0..Suc m. G (Suc m) k) = (\<Sum>k=0..m. G (Suc m) (Suc k))"
    by (subst sum.shift_bounds_cl_Suc_ivl) simp
  also have "\<dots> = (\<Sum>k=0..m. ((of_nat m + a gchoose (Suc k)) +
      (of_nat m + a gchoose k)) * x^(Suc k) * y^(m - k))"
    unfolding G_def by (subst gbinomial_addition_formula) simp
  also have "\<dots> = (\<Sum>k=0..m. (of_nat m + a gchoose (Suc k)) * x^(Suc k) * y^(m - k)) +
      (\<Sum>k=0..m. (of_nat m + a gchoose k) * x^(Suc k) * y^(m - k))"
    by (subst sum.distrib [symmetric]) (simp add: algebra_simps)
  also have "(\<Sum>k=0..m. (of_nat m + a gchoose (Suc k)) * x^(Suc k) * y^(m - k)) =
      (\<Sum>k<Suc m. (of_nat m + a gchoose (Suc k)) * x^(Suc k) * y^(m - k))"
    by (simp only: atLeast0AtMost lessThan_Suc_atMost)
  also have "\<dots> = (\<Sum>k<m. (of_nat m + a gchoose Suc k) * x^(Suc k) * y^(m-k)) +
      (of_nat m + a gchoose (Suc m)) * x^(Suc m)"
    (is "_ = ?A + ?B")
    by (subst sum.lessThan_Suc) simp
  also have "?A = (\<Sum>k=1..m. (of_nat m + a gchoose k) * x^k * y^(m - k + 1))"
  proof (subst sum_bounds_lt_plus1 [symmetric], intro sum.cong[OF refl], clarify)
    fix k
    assume "k < m"
    then have "m - k = m - Suc k + 1"
      by linarith
    then show "(of_nat m + a gchoose Suc k) * x ^ Suc k * y ^ (m - k) =
        (of_nat m + a gchoose Suc k) * x ^ Suc k * y ^ (m - Suc k + 1)"
      by (simp only:)
  qed
  also have "\<dots> + ?B = y * (\<Sum>k=1..m. (G m k)) + (of_nat m + a gchoose (Suc m)) * x^(Suc m)"
    unfolding G_def by (simp add: sum_distrib_left algebra_simps)
  also have "(\<Sum>k=0..m. (of_nat m + a gchoose k) * x^(Suc k) * y^(m - k)) = x * (S m)"
    unfolding S_def by (simp add: sum_distrib_left atLeast0AtMost algebra_simps)
  also have "(G (Suc m) 0) = y * (G m 0)"
    by (simp add: G_def)
  finally have "S (Suc m) =
      y * (G m 0 + (\<Sum>k=1..m. (G m k))) + (of_nat m + a gchoose (Suc m)) * x^(Suc m) + x * (S m)"
    by (simp add: ring_distribs)
  also have "G m 0 + (\<Sum>k=1..m. (G m k)) = S m"
    by (simp add: SG_def atLeast0AtMost flip: sum.atLeast_Suc_atMost)
  finally have "S (Suc m) = (x + y) * (S m) + (of_nat m + a gchoose (Suc m)) * x^(Suc m)"
    by (simp add: algebra_simps)
  also have "(of_nat m + a gchoose (Suc m)) = (-1) ^ (Suc m) * (- a gchoose (Suc m))"
    by (subst gbinomial_negated_upper) simp
  also have "(-1) ^ Suc m * (- a gchoose Suc m) * x ^ Suc m = (- a gchoose (Suc m)) * (-x) ^ Suc m"
    by (simp add: power_minus[of x])
  also have "(x + y) * S m + \<dots> = (x + y) * ?rhs m + (- a gchoose (Suc m)) * (- x)^Suc m"
    unfolding S_def by (simp add: Suc.IH)
  also have "(x + y) * ?rhs m = (\<Sum>n\<le>m. ((- a gchoose n) * (- x) ^ n * (x + y) ^ (Suc m - n)))"
    by (auto simp: Suc_diff_le sum_distrib_left intro!: sum.cong)
  also have "\<dots> + (-a gchoose (Suc m)) * (-x)^Suc m =
      (\<Sum>n\<le>Suc m. (- a gchoose n) * (- x) ^ n * (x + y) ^ (Suc m - n))"
    by simp
  finally show ?case
    by (simp only: S_def)
qed

lemma gbinomial_partial_sum_poly_xpos:
    "(\<Sum>k\<le>m. (of_nat m + a gchoose k) * x^k * y^(m-k)) =
     (\<Sum>k\<le>m. (of_nat k + a - 1 gchoose k) * x^k * (x + y)^(m-k))" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>k\<le>m. (- a gchoose k) * (- x) ^ k * (x + y) ^ (m - k))"
    by (simp add: gbinomial_partial_sum_poly)
  also have "\<dots> = (\<Sum>k\<le>m. (-1) ^ k * (of_nat k - - a - 1 gchoose k) * (- x) ^ k * (x + y) ^ (m - k))"
    by (metis (no_types, opaque_lifting) gbinomial_negated_upper)
  also have "\<dots> = ?rhs"
    by (auto simp flip: power_mult_distrib intro: sum.cong)
  finally show ?thesis .
qed

lemma binomial_r_part_sum: "(\<Sum>k\<le>m. (2 * m + 1 choose k)) = 2 ^ (2 * m)"
proof -
  have "2 * 2^(2*m) = (\<Sum>k = 0..(2 * m + 1). (2 * m + 1 choose k))"
    using choose_row_sum[where n="2 * m + 1"]  by (simp add: atMost_atLeast0)
  also have "(\<Sum>k = 0..(2 * m + 1). (2 * m + 1 choose k)) =
      (\<Sum>k = 0..m. (2 * m + 1 choose k)) +
      (\<Sum>k = m+1..2*m+1. (2 * m + 1 choose k))"
    using sum.ub_add_nat[of 0 m "\<lambda>k. 2 * m + 1 choose k" "m+1"]
    by (simp add: mult_2)
  also have "(\<Sum>k = m+1..2*m+1. (2 * m + 1 choose k)) =
      (\<Sum>k = 0..m. (2 * m + 1 choose (k + (m + 1))))"
    by (subst sum.shift_bounds_cl_nat_ivl [symmetric]) (simp add: mult_2)
  also have "\<dots> = (\<Sum>k = 0..m. (2 * m + 1 choose (m - k)))"
    by (intro sum.cong[OF refl], subst binomial_symmetric) simp_all
  also have "\<dots> = (\<Sum>k = 0..m. (2 * m + 1 choose k))"
    using sum.atLeastAtMost_rev [of "\<lambda>k. 2 * m + 1 choose (m - k)" 0 m]
    by simp
  also have "\<dots> + \<dots> = 2 * \<dots>"
    by simp
  finally show ?thesis
    by (simp add: atLeast0AtMost)
qed

lemma gbinomial_r_part_sum: "(\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k)) = 2 ^ (2 * m)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = of_nat (\<Sum>k\<le>m. (2 * m + 1) choose k)"
    by (simp add: binomial_gbinomial add_ac)
  also have "\<dots> = of_nat (2 ^ (2 * m))"
    using binomial_r_part_sum by presburger
  finally show ?thesis by simp
qed

lemma gbinomial_sum_nat_pow2:
  "(\<Sum>k\<le>m. (of_nat (m + k) gchoose k :: 'a::field_char_0) / 2 ^ k) = 2 ^ m"
  (is "?lhs = ?rhs")
proof -
  have "2 ^ m * 2 ^ m = (2 ^ (2*m) :: 'a)"
    by (induct m) simp_all
  also have "\<dots> = (\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k))"
    using gbinomial_r_part_sum ..
  also have "\<dots> = (\<Sum>k\<le>m. (of_nat (m + k) gchoose k) * 2 ^ (m - k))"
    using gbinomial_partial_sum_poly_xpos[where x="1" and y="1" and a="of_nat m + 1" and m="m"]
    by (simp add: add_ac)
  also have "\<dots> = 2 ^ m * (\<Sum>k\<le>m. (of_nat (m + k) gchoose k) / 2 ^ k)"
    by (simp add: sum_distrib_left algebra_simps power_diff)
  finally show ?thesis
    by (subst (asm) mult_left_cancel) simp_all
qed

lemma gbinomial_trinomial_revision:
  assumes "k \<le> m"
  shows "(a gchoose m) * (of_nat m gchoose k) = (a gchoose k) * (a - of_nat k gchoose (m - k))"
proof -
  have "(a gchoose m) * (of_nat m gchoose k) = (a gchoose m) * fact m / (fact k * fact (m - k))"
    using assms by (simp add: binomial_gbinomial [symmetric] binomial_fact)
  also have "\<dots> = (a gchoose k) * (a - of_nat k gchoose (m - k))"
    using assms by (simp add: gbinomial_pochhammer power_diff pochhammer_product)
  finally show ?thesis .
qed

text \<open>Versions of the theorems above for the natural-number version of "choose"\<close>
lemma binomial_altdef_of_nat:
  "k \<le> n \<Longrightarrow> of_nat (n choose k) = (\<Prod>i = 0..<k. of_nat (n - i) / of_nat (k - i) :: 'a)"
  for n k :: nat and x :: "'a::field_char_0"
  by (simp add: gbinomial_altdef_of_nat binomial_gbinomial of_nat_diff)

lemma binomial_ge_n_over_k_pow_k: "k \<le> n \<Longrightarrow> (of_nat n / of_nat k :: 'a) ^ k \<le> of_nat (n choose k)"
  for k n :: nat and x :: "'a::linordered_field"
  by (simp add: binomial_gbinomial gbinomial_ge_n_over_k_pow_k)

lemma binomial_le_pow:
  assumes "r \<le> n"
  shows "n choose r \<le> n ^ r"
proof -
  have "n choose r \<le> fact n div fact (n - r)"
    using assms by (subst binomial_fact_lemma[symmetric]) auto
  with fact_div_fact_le_pow [OF assms] show ?thesis
    by auto
qed

lemma choose_dvd:
  assumes "k \<le> n" shows "fact k * fact (n - k) dvd (fact n)"
  by (metis assms binomial_fact_lemma dvd_def of_nat_fact of_nat_mult)

lemma fact_fact_dvd_fact:
  "fact k * fact n dvd (fact (k + n))"
  by (metis add.commute add_diff_cancel_left' choose_dvd le_add2)

lemma choose_mult_lemma:
  "((m + r + k) choose (m + k)) * ((m + k) choose k) = ((m + r + k) choose k) * ((m + r) choose m)"
  (is "?lhs = _")
proof -
  have "?lhs =
      fact (m + r + k) div (fact (m + k) * fact (m + r - m)) * (fact (m + k) div (fact k * fact m))"
    by (simp add: binomial_fact')
  also have "\<dots> = fact (m + r + k) * fact (m + k) div
                 (fact (m + k) * fact (m + r - m) * (fact k * fact m))"
    by (metis add_implies_diff add_le_mono1 choose_dvd diff_cancel2 div_mult_div_if_dvd le_add1 le_add2)
  also have "\<dots> = fact (m + r + k) div (fact r * (fact k * fact m))"
    by (auto simp: algebra_simps fact_fact_dvd_fact)
  also have "\<dots> = (fact (m + r + k) * fact (m + r)) div (fact r * (fact k * fact m) * fact (m + r))"
    by simp
  also have "\<dots> =
      (fact (m + r + k) div (fact k * fact (m + r)) * (fact (m + r) div (fact r * fact m)))"
    by (auto simp: div_mult_div_if_dvd fact_fact_dvd_fact algebra_simps)
  finally show ?thesis
    by (simp add: binomial_fact' mult.commute)
qed

text \<open>The "Subset of a Subset" identity.\<close>
lemma choose_mult:
  "k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (n choose m) * (m choose k) = (n choose k) * ((n - k) choose (m - k))"
  using choose_mult_lemma [of "m-k" "n-m" k] by simp

lemma of_nat_binomial_eq_mult_binomial_Suc:
  assumes "k \<le> n"
  shows "(of_nat :: (nat \<Rightarrow> ('a :: field_char_0))) (n choose k) = of_nat (n + 1 - k) / of_nat (n + 1) * of_nat (Suc n choose k)"
proof (cases k)
  case 0 then show ?thesis
    using of_nat_neq_0 by auto
next
  case (Suc l)
  have "of_nat (n + 1) * (\<Prod>i=0..<k. of_nat (n - i)) = (of_nat :: (nat \<Rightarrow> 'a)) (n + 1 - k) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    using prod.atLeast0_lessThan_Suc [where ?'a = 'a, symmetric, of "\<lambda>i. of_nat (Suc n - i)" k]
    by (simp add: ac_simps prod.atLeast0_lessThan_Suc_shift del: prod.op_ivl_Suc)
  also have "\<dots> = (of_nat :: (nat \<Rightarrow> 'a)) (Suc n - k) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    by (simp add: Suc atLeast0_atMost_Suc atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = (of_nat :: (nat \<Rightarrow> 'a)) (n + 1 - k) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    by (simp only: Suc_eq_plus1)
  finally have "(\<Prod>i=0..<k. of_nat (n - i)) = (of_nat :: (nat \<Rightarrow> 'a)) (n + 1 - k) / of_nat (n + 1) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    using of_nat_neq_0 by (auto simp: mult.commute divide_simps)
  with assms show ?thesis
    by (simp add: binomial_altdef_of_nat prod_dividef)
qed


subsection \<open>More on Binomial Coefficients\<close>

text \<open>The number of nat lists of length \<open>m\<close> summing to \<open>N\<close> is \<^term>\<open>(N + m - 1) choose N\<close>:\<close>
lemma card_length_sum_list_rec:
  assumes "m \<ge> 1"
  shows "card {l::nat list. length l = m \<and> sum_list l = N} =
      card {l. length l = (m - 1) \<and> sum_list l = N} +
      card {l. length l = m \<and> sum_list l + 1 = N}"
    (is "card ?C = card ?A + card ?B")
proof -
  let ?A' = "{l. length l = m \<and> sum_list l = N \<and> hd l = 0}"
  let ?B' = "{l. length l = m \<and> sum_list l = N \<and> hd l \<noteq> 0}"
  let ?f = "\<lambda>l. 0 # l"
  let ?g = "\<lambda>l. (hd l + 1) # tl l"
  have 1: "xs \<noteq> [] \<Longrightarrow> x = hd xs \<Longrightarrow> x # tl xs = xs" for x :: nat and xs
    by simp
  have 2: "xs \<noteq> [] \<Longrightarrow> sum_list(tl xs) = sum_list xs - hd xs" for xs :: "nat list"
    by (auto simp add: neq_Nil_conv)
  have f: "bij_betw ?f ?A ?A'"
    by (rule bij_betw_byWitness[where f' = tl]) (use assms in \<open>auto simp: 2 1 simp flip: length_0_conv\<close>)
  have 3: "xs \<noteq> [] \<Longrightarrow> hd xs + (sum_list xs - hd xs) = sum_list xs" for xs :: "nat list"
    by (metis 1 sum_list_simps(2) 2)
  have g: "bij_betw ?g ?B ?B'"
    apply (rule bij_betw_byWitness[where f' = "\<lambda>l. (hd l - 1) # tl l"])
    using assms
    by (auto simp: 2 simp flip: length_0_conv intro!: 3)
  have fin: "finite {xs. size xs = M \<and> set xs \<subseteq> {0..<N}}" for M N :: nat
    using finite_lists_length_eq[OF finite_atLeastLessThan] conj_commute by auto
  have fin_A: "finite ?A" using fin[of _ "N+1"]
    by (intro finite_subset[where ?A = "?A" and ?B = "{xs. size xs = m - 1 \<and> set xs \<subseteq> {0..<N+1}}"])
      (auto simp: member_le_sum_list less_Suc_eq_le)
  have fin_B: "finite ?B"
    by (intro finite_subset[where ?A = "?B" and ?B = "{xs. size xs = m \<and> set xs \<subseteq> {0..<N}}"])
      (auto simp: member_le_sum_list less_Suc_eq_le fin)
  have disj: "?A' \<inter> ?B' = {}" by blast
  have "?C = ?A' \<union> ?B'"
    by auto
  then have "card ?C = card(?A' \<union> ?B')"
    by simp
  also have "\<dots> = card ?A + card ?B"
    using card_Un_disjoint[OF _ _ disj] bij_betw_finite[OF f] bij_betw_finite[OF g]
      bij_betw_same_card[OF f] bij_betw_same_card[OF g] fin_A fin_B
    by presburger
  finally show ?thesis .
qed

lemma card_length_sum_list: "card {l::nat list. size l = m \<and> sum_list l = N} = (N + m - 1) choose N"
  \<comment> \<open>by Holden Lee, tidied by Tobias Nipkow\<close>
proof (cases m)
  case 0
  then show ?thesis
    by (cases N) (auto cong: conj_cong)
next
  case (Suc m')
  have m: "m \<ge> 1"
    by (simp add: Suc)
  then show ?thesis
  proof (induct "N + m - 1" arbitrary: N m)
    case 0  \<comment> \<open>In the base case, the only solution is [0].\<close>
    have [simp]: "{l::nat list. length l = Suc 0 \<and> (\<forall>n\<in>set l. n = 0)} = {[0]}"
      by (auto simp: length_Suc_conv)
    have "m = 1 \<and> N = 0"
      using 0 by linarith
    then show ?case
      by simp
  next
    case (Suc k)
    have c1: "card {l::nat list. size l = (m - 1) \<and> sum_list l =  N} = (N + (m - 1) - 1) choose N"
    proof (cases "m = 1")
      case True
      with Suc.hyps have "N \<ge> 1"
        by auto
      with True show ?thesis
        by (simp add: binomial_eq_0)
    next
      case False
      then show ?thesis
        using Suc by fastforce
    qed
    from Suc have c2: "card {l::nat list. size l = m \<and> sum_list l + 1 = N} =
      (if N > 0 then ((N - 1) + m - 1) choose (N - 1) else 0)"
    proof -
      have *: "n > 0 \<Longrightarrow> Suc m = n \<longleftrightarrow> m = n - 1" for m n
        by arith
      from Suc have "N > 0 \<Longrightarrow>
        card {l::nat list. size l = m \<and> sum_list l + 1 = N} =
          ((N - 1) + m - 1) choose (N - 1)"
        by (simp add: *)
      then show ?thesis
        by auto
    qed
    from Suc.prems have "(card {l::nat list. size l = (m - 1) \<and> sum_list l = N} +
          card {l::nat list. size l = m \<and> sum_list l + 1 = N}) = (N + m - 1) choose N"
      by (auto simp: c1 c2 choose_reduce_nat[of "N + m - 1" N] simp del: One_nat_def)
    then show ?case
      using card_length_sum_list_rec[OF Suc.prems] by auto
  qed
qed

lemma card_disjoint_shuffles:
  assumes "set xs \<inter> set ys = {}"
  shows   "card (shuffles xs ys) = (length xs + length ys) choose length xs"
using assms
proof (induction xs ys rule: shuffles.induct)
  case (3 x xs y ys)
  have "shuffles (x # xs) (y # ys) = (#) x ` shuffles xs (y # ys) \<union> (#) y ` shuffles (x # xs) ys"
    by (rule shuffles.simps)
  also have "card \<dots> = card ((#) x ` shuffles xs (y # ys)) + card ((#) y ` shuffles (x # xs) ys)"
    by (rule card_Un_disjoint) (use 3 in auto)
  also have "card ((#) x ` shuffles xs (y # ys)) = card (shuffles xs (y # ys))"
    by (rule card_image) auto
  also have "\<dots> = (length xs + length (y # ys)) choose length xs"
    using "3.prems" by (intro "3.IH") auto
  also have "card ((#) y ` shuffles (x # xs) ys) = card (shuffles (x # xs) ys)"
    by (rule card_image) auto
  also have "\<dots> = (length (x # xs) + length ys) choose length (x # xs)"
    using "3.prems" by (intro "3.IH") auto
  also have "(length xs + length (y # ys) choose length xs) + \<dots> =
               (length (x # xs) + length (y # ys)) choose length (x # xs)" by simp
  finally show ?case .
qed auto

lemma Suc_times_binomial_add: "Suc a * (Suc (a + b) choose Suc a) = Suc b * (Suc (a + b) choose a)"
  \<comment> \<open>by Lukas Bulwahn\<close>
proof -
  have dvd: "Suc a * (fact a * fact b) dvd fact (Suc (a + b))" for a b
    using fact_fact_dvd_fact[of "Suc a" "b"]
    by (metis add.commute add_Suc_right fact_Suc id_apply mult.assoc of_nat_eq_id)
  have "Suc a * (fact (Suc (a + b)) div (Suc a * fact a * fact b)) =
      Suc a * fact (Suc (a + b)) div (Suc a * (fact a * fact b))"
    by (metis mult.assoc div_mult_swap dvd)
  also have "\<dots> = Suc b * fact (Suc (a + b)) div (Suc b * (fact a * fact b))"
    by (simp only: div_mult_mult1)
  also have "\<dots> = Suc b * (fact (Suc (a + b)) div (Suc b * (fact a * fact b)))"
    by (metis add.commute div_mult_swap dvd mult.commute)
  finally show ?thesis
    by (metis Suc_diff_le Suc_eq_plus1 Suc_times_binomial add.commute binomial_absorb_comp diff_add_inverse le_add1)
qed

subsection \<open>Inclusion-exclusion principle\<close>

text \<open>Ported from HOL Light by lcp\<close>

lemma Inter_over_Union:
  "\<Inter> {\<Union> (\<F> x) |x. x \<in> S} = \<Union> {\<Inter> (G ` S) |G. \<forall>x\<in>S. G x \<in> \<F> x}" 
proof -
  have "\<And>x. \<forall>s\<in>S. \<exists>X \<in> \<F> s. x \<in> X \<Longrightarrow> \<exists>G. (\<forall>x\<in>S. G x \<in> \<F> x) \<and> (\<forall>s\<in>S. x \<in> G s)"
    by metis
  then show ?thesis
    by (auto simp flip: all_simps ex_simps)
qed

lemma subset_insert_lemma:
  "{T. T \<subseteq> (insert a S) \<and> P T} = {T. T \<subseteq> S \<and> P T} \<union> {insert a T |T. T \<subseteq> S \<and> P(insert a T)}" (is "?L=?R")
proof
  show "?L \<subseteq> ?R"
    by (smt (verit) UnI1 UnI2 insert_Diff mem_Collect_eq subsetI subset_insert_iff)
qed blast


text\<open>Versions for additive real functions, where the additivity applies only to some
 specific subsets (e.g. cardinality of finite sets, measurable sets with bounded measure.
 (From HOL Light)\<close>

locale Incl_Excl =
  fixes P :: "'a set \<Rightarrow> bool" and f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes disj_add: "\<lbrakk>P S; P T; disjnt S T\<rbrakk> \<Longrightarrow> f(S \<union> T) = f S + f T"
    and empty: "P{}"
    and Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<inter> T)"
    and Un: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<union> T)"
    and Diff: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S - T)"

begin

lemma f_empty [simp]: "f{} = 0"
  using disj_add empty by fastforce

lemma f_Un_Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> f(S \<union> T) + f(S \<inter> T) = f S + f T"
  by (smt (verit, ccfv_threshold) Groups.add_ac(2) Incl_Excl.Diff Incl_Excl.Int Incl_Excl_axioms Int_Diff_Un Int_Diff_disjoint Int_absorb Un_Diff Un_Int_eq(2) disj_add disjnt_def group_cancel.add2 sup_bot.right_neutral)

lemma restricted_indexed:
  assumes "finite A" and X: "\<And>a. a \<in> A \<Longrightarrow> P(X a)"
  shows "f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
proof -
  have "\<lbrakk>finite A; card A = n; \<forall>a \<in> A. P (X a)\<rbrakk>
              \<Longrightarrow> f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))" for n X and A :: "'c set"
  proof (induction n arbitrary: A X rule: less_induct)
    case (less n0 A0 X)
    show ?case
    proof (cases "n0=0")
      case True
      with less show ?thesis
       by fastforce
    next
      case False
      with less.prems obtain A n a where *: "n0 = Suc n" "A0 = insert a A" "a \<notin> A" "card A = n" "finite A"
        by (metis card_Suc_eq_finite not0_implies_Suc)
      with less have "P (X a)" by blast
      have APX: "\<forall>a \<in> A. P (X a)"
        by (simp add: "*" less.prems)
      have PUXA: "P (\<Union> (X ` A))"
        using \<open>finite A\<close> APX
        by (induction) (auto simp: empty Un)
      have "f (\<Union> (X ` A0)) = f (X a \<union> \<Union> (X ` A))"
        by (simp add: *)
      also have "\<dots> = f (X a) + f (\<Union> (X ` A)) - f (X a \<inter> \<Union> (X ` A))"
        using f_Un_Int add_diff_cancel PUXA \<open>P (X a)\<close> by metis
      also have "\<dots> = f (X a) - (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ card B * f (\<Inter> (X ` B))) +
                       (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B)))"
      proof -
        have 1: "f (\<Union>i\<in>A. X a \<inter> X i) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter>b\<in>B. X a \<inter> X b))"
          using less.IH [of n A "\<lambda>i. X a \<inter> X i"] APX Int \<open>P (X a)\<close>  by (simp add: *)
        have 2: "X a \<inter> \<Union> (X ` A) = (\<Union>i\<in>A. X a \<inter> X i)"
          by auto
        have 3: "f (\<Union> (X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
          using less.IH [of n A X] APX Int \<open>P (X a)\<close>  by (simp add: *)
        show ?thesis
          unfolding 3 2 1
          by (simp add: sum_negf)
      qed
      also have "\<dots> = (\<Sum>B | B \<subseteq> A0 \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
      proof -
         have F: "{insert a B |B. B \<subseteq> A} = insert a ` Pow A \<and> {B. B \<subseteq> A \<and> B \<noteq> {}} = Pow A - {{}}"
          by auto
        have G: "(\<Sum>B\<in>Pow A. (- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B))) = (\<Sum>B\<in>Pow A. - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B))))"
        proof (rule sum.cong [OF refl])
          fix B
          assume B: "B \<in> Pow A"
          then have "finite B"
            using \<open>finite A\<close> finite_subset by auto
          show "(- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B)) = - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B)))"
            using B * by (auto simp add: card_insert_if \<open>finite B\<close>)
        qed
        have disj: "{B. B \<subseteq> A \<and> B \<noteq> {}} \<inter> {insert a B |B. B \<subseteq> A} = {}"
          using * by blast
        have inj: "inj_on (insert a) (Pow A)"
          using "*" inj_on_def by fastforce
        show ?thesis
          apply (simp add: * subset_insert_lemma sum.union_disjoint disj sum_negf)
          apply (simp add: F G sum_negf sum.reindex [OF inj] o_def sum_diff *)
          done
      qed
      finally show ?thesis .
    qed   
  qed
  then show ?thesis
    by (meson assms)
qed

lemma restricted:
  assumes "finite A" "\<And>a. a \<in> A \<Longrightarrow> P a"
  shows  "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  using restricted_indexed [of A "\<lambda>x. x"] assms by auto

end

subsection\<open>Versions for unrestrictedly additive functions\<close>

lemma Incl_Excl_UN:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union>(G ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (-1) ^ (card B + 1) * f (\<Inter> (G ` B)))"
proof -
  interpret Incl_Excl "\<lambda>x. True" f
    by (simp add: Incl_Excl.intro assms(1))
  show ?thesis
    using restricted_indexed assms by blast
qed

lemma Incl_Excl_Union:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  using Incl_Excl_UN[of f A "\<lambda>X. X"] assms by simp

text \<open>The famous inclusion-exclusion formula for the cardinality of a union\<close>
lemma int_card_UNION:
  assumes "finite A" "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "int (card (\<Union>A)) = (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
proof -
  interpret Incl_Excl finite "int o card"
  proof qed (auto simp add: card_Un_disjnt)
  show ?thesis
    using restricted assms by auto
qed

text\<open>A more conventional form\<close>
lemma inclusion_exclusion:
  assumes "finite A" "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "int(card(\<Union> A)) =
         (\<Sum>n=1..card A. (-1) ^ (Suc n) * (\<Sum>B | B \<subseteq> A \<and> card B = n. int (card (\<Inter> B))))" (is "_=?R")
proof -
  have fin: "finite {I. I \<subseteq> A \<and> I \<noteq> {}}"
    by (simp add: assms)
  have "\<And>k. \<lbrakk>Suc 0 \<le> k; k \<le> card A\<rbrakk> \<Longrightarrow> \<exists>B\<subseteq>A. B \<noteq> {} \<and> k = card B"
    by (metis (mono_tags, lifting) Suc_le_D Zero_neq_Suc card_eq_0_iff obtain_subset_with_card_n)
  with \<open>finite A\<close> finite_subset
  have card_eq: "card ` {I. I \<subseteq> A \<and> I \<noteq> {}} = {1..card A}"
    using not_less_eq_eq card_mono by (fastforce simp: image_iff)
  have "int(card(\<Union> A)) 
      = (\<Sum>y = 1..card A. \<Sum>I\<in>{x. x \<subseteq> A \<and> x \<noteq> {} \<and> card x = y}. - ((- 1) ^ y * int (card (\<Inter> I))))"
    by (simp add: int_card_UNION assms sum.image_gen [OF fin, where g=card] card_eq)
  also have "\<dots> = ?R"
  proof -
    have "{B. B \<subseteq> A \<and> B \<noteq> {} \<and> card B = k} = {B. B \<subseteq> A \<and> card B = k}"
      if "Suc 0 \<le> k" and "k \<le> card A" for k
      using that by auto
    then show ?thesis
      by (clarsimp simp add: sum_negf simp flip: sum_distrib_left)
  qed
  finally show ?thesis .
qed

lemma card_UNION:
  assumes "finite A" and "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  by (simp only: flip: int_card_UNION [OF assms])

lemma card_UNION_nonneg:
  assumes "finite A" and "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "(\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I))) \<ge> 0"
  using int_card_UNION [OF assms] by presburger


subsection \<open>General "Moebius inversion" inclusion-exclusion principle\<close>

text \<open>This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" \<close>

lemma sum_Un_eq:
   "\<lbrakk>S \<inter> T = {}; S \<union> T = U; finite U\<rbrakk>
           \<Longrightarrow> (sum f S + sum f T = sum f U)"
  by (metis finite_Un sum.union_disjoint)

lemma card_adjust_lemma: "\<lbrakk>inj_on f S; x = y + card (f ` S)\<rbrakk> \<Longrightarrow> x = y + card S"
  by (simp add: card_image)

lemma card_subsets_step:
  assumes "finite S" "x \<notin> S" "U \<subseteq> S"
  shows "card {T. T \<subseteq> (insert x S) \<and> U \<subseteq> T \<and> odd(card T)} 
       = card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)} + card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} \<and>
         card {T. T \<subseteq> (insert x S) \<and> U \<subseteq> T \<and> even(card T)} 
       = card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} + card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)}"
proof -
  have inj: "inj_on (insert x) {T. T \<subseteq> S \<and> P T}" for P
    using assms by (auto simp: inj_on_def)
  have [simp]: "finite {T. T \<subseteq> S \<and> P T}"  "finite (insert x ` {T. T \<subseteq> S \<and> P T})" for P
    using \<open>finite S\<close> by auto
  have [simp]: "disjnt {T. T \<subseteq> S \<and> P T} (insert x ` {T. T \<subseteq> S \<and> Q T})" for P Q
    using assms by (auto simp: disjnt_iff)
  have eq: "{T. T \<subseteq> S \<and> U \<subseteq> T \<and> P T} \<union> insert x ` {T. T \<subseteq> S \<and> U \<subseteq> T \<and> Q T}
          = {T. T \<subseteq> insert x S \<and> U \<subseteq> T \<and> P T}"  (is "?L = ?R")
    if "\<And>A. A \<subseteq> S \<Longrightarrow> Q (insert x A) \<longleftrightarrow> P A" "\<And>A. \<not> Q A \<longleftrightarrow> P A" for P Q
  proof
    show "?L \<subseteq> ?R"
      by (clarsimp simp: image_iff subset_iff) (meson subsetI that)
    show "?R \<subseteq> ?L"
      using \<open>U \<subseteq> S\<close>
      by (clarsimp simp: image_iff) (smt (verit) insert_iff mk_disjoint_insert subset_iff that)
  qed
  have [simp]: "\<And>A. A \<subseteq> S \<Longrightarrow> even (card (insert x A)) \<longleftrightarrow> odd (card A)"
    by (metis \<open>finite S\<close> \<open>x \<notin> S\<close> card_insert_disjoint even_Suc finite_subset subsetD)
  show ?thesis
    by (intro conjI card_adjust_lemma [OF inj]; simp add: eq flip: card_Un_disjnt)
qed

lemma card_subsupersets_even_odd:
  assumes "finite S" "U \<subset> S"
  shows "card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} 
       = card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)}"
  using assms
proof (induction "card S" arbitrary: S rule: less_induct)
  case (less S)
  then obtain x where "x \<notin> U" "x \<in> S"
    by blast
  then have U: "U \<subseteq> S - {x}"
    using less.prems(2) by blast
  let ?V = "S - {x}"
  show ?case
    using card_subsets_step [of ?V x U] less.prems U
    by (simp add: insert_absorb \<open>x \<in> S\<close>)
qed

lemma sum_alternating_cancels:
  assumes "finite S" "card {x. x \<in> S \<and> even(f x)} = card {x. x \<in> S \<and> odd(f x)}"
  shows "(\<Sum>x\<in>S. (-1) ^ f x) = (0::'b::ring_1)"
proof -
  have "(\<Sum>x\<in>S. (-1) ^ f x)
      = (\<Sum>x | x \<in> S \<and> even (f x). (-1) ^ f x) + (\<Sum>x | x \<in> S \<and> odd (f x). (-1) ^ f x)"
    by (rule sum_Un_eq [symmetric]; force simp: \<open>finite S\<close>)
  also have "\<dots> = (0::'b::ring_1)"
    by (simp add: minus_one_power_iff assms cong: conj_cong)
  finally show ?thesis .
qed

lemma inclusion_exclusion_symmetric:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes \<section>: "\<And>S. finite S \<Longrightarrow> g S = (\<Sum>T \<in> Pow S. (-1) ^ card T * f T)"
    and "finite S"
  shows "f S = (\<Sum>T \<in> Pow S. (-1) ^ card T * g T)"
proof -
  have "(-1) ^ card T * g T = (-1) ^ card T * (\<Sum>U | U \<subseteq> S \<and> U \<subseteq> T. (-1) ^ card U * f U)" 
    if "T \<subseteq> S" for T
  proof -
    have [simp]: "{U. U \<subseteq> S \<and> U \<subseteq> T} = Pow T"
      using that by auto
    show ?thesis
      using that by (simp add: \<open>finite S\<close> finite_subset \<section>)
  qed
  then have "(\<Sum>T \<in> Pow S. (-1) ^ card T * g T)
      = (\<Sum>T\<in>Pow S. (-1) ^ card T * (\<Sum>U | U \<in> {U. U \<subseteq> S} \<and> U \<subseteq> T. (-1) ^ card U * f U))"
    by simp
  also have "\<dots> = (\<Sum>U\<in>Pow S. (\<Sum>T | T \<subseteq> S \<and> U \<subseteq> T. (-1) ^ card T) * (-1) ^ card U * f U)"
    unfolding sum_distrib_left
    by (subst sum.swap_restrict; simp add: \<open>finite S\<close> algebra_simps sum_distrib_right Pow_def)
  also have "\<dots> = (\<Sum>U\<in>Pow S. if U=S then f S else 0)"
  proof -
    have [simp]: "{T. T \<subseteq> S \<and> S \<subseteq> T} = {S}"
      by auto
    show ?thesis
      apply (rule sum.cong [OF refl])
      by (simp add: sum_alternating_cancels card_subsupersets_even_odd \<open>finite S\<close> flip: power_add)
  qed
  also have "\<dots> = f S"
    by (simp add: \<open>finite S\<close>)
  finally show ?thesis
    by presburger
qed

text\<open> The more typical non-symmetric version.                                   \<close>
lemma inclusion_exclusion_mobius:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes \<section>: "\<And>S. finite S \<Longrightarrow> g S = sum f (Pow S)" and "finite S"
  shows "f S = (\<Sum>T \<in> Pow S. (-1) ^ (card S - card T) * g T)" (is "_ = ?rhs")
proof -
  have "(- 1) ^ card S * f S = (\<Sum>T\<in>Pow S. (- 1) ^ card T * g T)"
    by (rule inclusion_exclusion_symmetric; simp add: assms flip: power_add mult.assoc)
  then have "((- 1) ^ card S * (- 1) ^ card S) * f S = ((- 1) ^ card S) * (\<Sum>T\<in>Pow S. (- 1) ^ card T * g T)"
    by (simp add: mult_ac)
  then have "f S = (\<Sum>T\<in>Pow S. (- 1) ^ (card S + card T) * g T)"
    by (simp add: sum_distrib_left flip: power_add mult.assoc)
  also have "\<dots> = ?rhs"
    by (simp add: \<open>finite S\<close> card_mono neg_one_power_add_eq_neg_one_power_diff)
  finally show ?thesis .
qed


subsection \<open>Executable code\<close>

lemma gbinomial_code [code]:
  "a gchoose k =
    (if k = 0 then 1
     else fold_atLeastAtMost_nat (\<lambda>k acc. (a - of_nat k) * acc) 0 (k - 1) 1 / fact k)"
  by (cases k) (simp_all add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost flip: prod_atLeastAtMost_code)

lemma binomial_code [code]:
  "n choose k =
      (if k > n then 0
       else if 2 * k > n then n choose (n - k)
       else (fold_atLeastAtMost_nat (*) (n - k + 1) n 1 div fact k))"
proof -
  {
    assume "k \<le> n"
    then have "(fact n :: nat) = fact (n-k) * \<Prod>{n-k+1..n}"
      by (metis Suc_eq_plus1 diff_le_self fact_eq_fact_times)
  }
  then show ?thesis by (auto simp: binomial_fact' mult_ac prod_atLeastAtMost_code)
qed

end
