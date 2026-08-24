theory Infinite_Product_Examples
  imports "HOL-Analysis.Infinite_Product"
begin

text \<open>
  Four small examples.  They are here to exercise the interface rather than for their own sake: a
  product whose value comes for free from the sum theory, one computed by telescoping, one showing
  why \<open>strongly_multipliable_on\<close> exists at all, and one uniform convergence statement obtained
  from the \<open>M\<close>-test.
\<close>

text \<open>A product read off from a sum\<close>

text \<open>
  \<open>has_sum_imp_has_setprod_exp\<close> turns any convergent sum into a convergent product; with the
  geometric series that gives an exact value in one step, over the index set \<^term>\<open>{1..}\<close> rather
  than all of \<^typ>\<open>nat\<close>.
\<close>
lemma has_setprod_exp_geometric:
  fixes z :: complex
  assumes "norm z < 1"
  shows "((\<lambda>n. exp (z ^ n)) has_setprod exp (z / (1 - z))) {1..}"
  using has_sum_geometric_from_1[OF assms] by (rule has_sum_imp_has_setprod_exp)


text \<open>A product computed by telescoping\<close>

text \<open>
  \<^term>\<open>\<Prod>\<^sub>\<infinity>n. 1 - 1 / (real n + 2) ^ 2\<close> is \<open>1/2\<close>.  Convergence is absolute, because the
  deviations from \<open>1\<close> are the terms of a \<open>p\<close>-series; the value then follows from the initial
  segments alone, since \<open>filterlim_lessThan_at_top\<close> makes them cofinal in
  \<^term>\<open>finite_subsets_at_top UNIV\<close>.  That is the standard division of labour for an unordered
  product: convergence unordered, value ordered.
\<close>
lemma quotient_cancel_aux:
  fixes a b c :: real
  assumes "a \<noteq> 0" "b \<noteq> 0"
  shows "(a / (2 * b)) * ((b * c) / a ^ 2) = c / (2 * a)"
  using assms by (simp add: power2_eq_square field_simps)

lemma prod_lessThan_telescope:
  "(\<Prod>k<n. 1 - 1 / (real k + 2) ^ 2) = (real n + 2) / (2 * (real n + 1))"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have pos: "real n + 1 \<noteq> 0" "real n + 2 \<noteq> 0" "(real n + 2) ^ 2 \<noteq> 0"
    by auto
  then have factor: "1 - 1 / (real n + 2) ^ 2 = ((real n + 1) * (real n + 3)) / (real n + 2) ^ 2"
    by (simp add: power2_eq_square field_simps)
  have "(\<Prod>k<Suc n. 1 - 1 / (real k + 2) ^ 2)
          = ((real n + 2) / (2 * (real n + 1))) * (1 - 1 / (real n + 2) ^ 2)"
    using Suc by simp
  also have "\<dots> = ((real n + 2) / (2 * (real n + 1)))
                    * (((real n + 1) * (real n + 3)) / (real n + 2) ^ 2)"
    by (simp only: factor)
  also have "\<dots> = (real n + 3) / (2 * (real n + 2))"
    by (rule quotient_cancel_aux[OF pos(2) pos(1)])
  also have "\<dots> = (real (Suc n) + 2) / (2 * (real (Suc n) + 1))"
    by (simp add: field_simps)
  finally show ?case .
qed

lemma telescope_limit:
  "(\<lambda>n. (real n + 2) / (2 * (real n + 1))) \<longlonglongrightarrow> 1/2"
proof -
  have "(\<lambda>n. 1/2 + inverse (real (Suc n)) * (1/2)) \<longlonglongrightarrow> 1/2 + 0 * (1/2)"
    by (intro tendsto_intros LIMSEQ_inverse_real_of_nat)
  moreover have "1/2 + inverse (real (Suc n)) * (1/2) = (real n + 2) / (2 * (real n + 1))" for n
    by (simp add: field_simps)
  ultimately show ?thesis
    by simp
qed

lemma summable_on_inverse_squares_shifted:
  "(\<lambda>n. 1 / (real n + 2) ^ 2) summable_on UNIV"
proof (rule summable_nonneg_imp_summable_on)
  have "summable (\<lambda>n. inverse (real n ^ 2))"
    by (rule inverse_power_summable) simp
  hence "summable (\<lambda>n. inverse (real (n + 2) ^ 2))"
    by (rule summable_ignore_initial_segment)
  thus "summable (\<lambda>n. 1 / (real n + 2) ^ 2)"
    by (simp add: inverse_eq_divide add.commute)
qed auto

lemma has_setprod_telescope:
  "((\<lambda>n. 1 - 1 / (real n + 2) ^ 2) has_setprod 1/2) UNIV"
proof -
  define f where "f = (\<lambda>n. 1 - 1 / (real n + 2) ^ 2)"
  have pf: "prod f {..<n} = (real n + 2) / (2 * (real n + 1))" for n
    unfolding f_def by (rule prod_lessThan_telescope)
  \<comment> \<open>convergence: the deviations from \<open>1\<close> are summable\<close>
  have "(\<lambda>n. norm (f n - 1)) summable_on UNIV"
    by (simp add: f_def summable_on_inverse_squares_shifted)
  hence "f abs_multipliable_on UNIV"
    by (subst abs_multipliable_on_iff_summable_on) auto
  hence "f multipliable_on UNIV"
    by (blast intro: strongly_multipliable_imp_multipliable
                     abs_multipliable_on_imp_strongly_multipliable_on)
  then obtain P where P: "(f has_setprod P) UNIV"
    by (auto simp: multipliable_on_def)
  \<comment> \<open>the value: the initial segments are cofinal, so they already determine the limit\<close>
  have "(prod f \<longlongrightarrow> P) (finite_subsets_at_top UNIV)"
    using P by (simp add: has_setprod_def)
  from filterlim_compose[OF this filterlim_lessThan_at_top]
  have seq: "(\<lambda>n. prod f {..<n}) \<longlonglongrightarrow> P"
    by simp
  have "(\<lambda>n. prod f {..<n}) \<longlonglongrightarrow> 1/2"
    using telescope_limit by (simp add: pf)
  with seq have "P = 1/2"
    by (rule LIMSEQ_unique)
  with P show ?thesis
    by (simp add: f_def)
qed

corollary infprod_telescope: "(\<Prod>\<^sub>\<infinity>n. 1 - 1 / (real n + 2) ^ 2) = 1/2"
  by (rule infprodI[OF has_setprod_telescope])


text \<open>Why strong multipliability is a different notion\<close>

text \<open>
  A constant family below \<open>1\<close>: the partial products shrink to \<open>0\<close>, so the product converges
  \<^emph>\<open>unordered\<close> with value \<open>0\<close> although no factor vanishes.  By \<open>infprod_eq_0_iff\<close> it is therefore
  not strongly multipliable.  This is the counterexample behind several hypotheses in this theory.
\<close>
lemma pow_half_small: "e > 0 \<Longrightarrow> \<exists>N. (1/2::real) ^ N < e"
  using arch_pow_inv[of e "1/2"] by auto

lemma has_setprod_const_half: "((\<lambda>_::nat. 1/2::real) has_setprod 0) UNIV"
  unfolding has_setprod_def
proof (rule tendstoI)
  fix e :: real assume e: "e > 0"
  obtain N where N: "(1/2::real) ^ N < e"
    using pow_half_small[OF e] by blast
  show "\<forall>\<^sub>F X in finite_subsets_at_top UNIV. dist (prod (\<lambda>_::nat. 1/2::real) X) 0 < e"
    unfolding eventually_finite_subsets_at_top
  proof (intro exI conjI allI impI)
    show "finite {..<N}" "{..<N} \<subseteq> UNIV"
      by auto
    fix Y assume Y: "finite Y \<and> {..<N} \<subseteq> Y \<and> Y \<subseteq> UNIV"
    hence card: "card Y \<ge> N"
      by (metis card_lessThan card_mono)
    have "prod (\<lambda>_::nat. 1/2::real) Y = (1/2) ^ card Y"
      by simp
    also have "\<dots> \<le> (1/2) ^ N"
      using card by (intro power_decreasing) auto
    also have "\<dots> < e"
      by (rule N)
    finally show "dist (prod (\<lambda>_::nat. 1/2::real) Y) 0 < e"
      by (simp add: dist_real_def)
  qed
qed

corollary not_strongly_multipliable_const_half:
  "\<not> (\<lambda>_::nat. 1/2::real) strongly_multipliable_on UNIV"
  using has_setprod_const_half has_setprod_eq_0_iff by fastforce


text \<open>Uniform convergence from the \<open>M\<close>-test\<close>

text \<open>
  The shape a Weierstrass product comes in: on a bounded set the deviations from \<open>1\<close> are dominated
  by a summable sequence and \<open>uniform_limit_infprod_M_test\<close> does the rest.  Nothing about the
  factors beyond that bound is needed -- no continuity, no compactness.
\<close>
lemma uniform_limit_prod_one_plus_halves:
  fixes r :: real
  shows "uniform_limit (cball (0::complex) r) (\<lambda>X z. \<Prod>k\<in>X. 1 + z / 2 ^ k)
                       (\<lambda>z. \<Prod>\<^sub>\<infinity>k. 1 + z / 2 ^ k) (finite_subsets_at_top UNIV)"
proof (rule uniform_limit_infprod_M_test[where M = "\<lambda>k. r / 2 ^ k"])
  show "norm ((1 + z / 2 ^ k) - 1) \<le> r / 2 ^ k" if "z \<in> cball (0::complex) r" for k z
  proof -
    have "norm ((1 + z / 2 ^ k) - 1) = norm z / 2 ^ k"
      by (simp add: norm_divide norm_power)
    also have "\<dots> \<le> r / 2 ^ k"
      using that by (intro divide_right_mono) auto
    finally show ?thesis .
  qed
  show "(\<lambda>k. r / 2 ^ k) summable_on UNIV"
  proof (rule norm_summable_imp_summable_on)
    have "summable (\<lambda>k. \<bar>r\<bar> * (1/2::real) ^ k)"
      by (intro summable_mult summable_geometric) auto
    thus "summable (\<lambda>k. norm (r / 2 ^ k))"
      by (simp add: power_one_over abs_divide)
  qed
qed

end
