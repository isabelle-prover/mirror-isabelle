(*
  File:     HOL/Analysis/Log_Derivative.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Logarithmic derivatives\<close>
theory Log_Derivative
  imports Elementary_Topology "HOL-Library.Multiset"
begin

definition has_log_derivative :: "('a::real_normed_field \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a filter \<Rightarrow> bool"
    (infix \<open>(has'_log'_derivative)\<close> 50)
    where "(f has_log_derivative D) F \<longleftrightarrow> 
             (F = bot \<or> f (netlimit F) \<noteq> 0) \<and> (f has_field_derivative (D * f (netlimit F))) F"

lemma has_log_derivative_imp_has_field_derivative_ln_real:
  assumes "f x > (0::real)" "(f has_log_derivative D) (at x within A)"
  shows   "((\<lambda>x. ln (f x)) has_field_derivative D) (at x within A)"
proof (cases "at x within A = bot")
  case [simp]: False
  have [simp]: "netlimit (at x within A) = x"
    by (simp add: Lim_ident_at)
  show ?thesis using assms
    by (auto intro!: derivative_eq_intros simp: has_log_derivative_def)
qed auto

lemma has_log_derivative_bot [simp, intro]: "(f has_log_derivative f') bot"
  by (auto simp: has_log_derivative_def)

lemma has_log_derivative_unique:
  assumes "(f has_log_derivative D1) (at x within A)" "(f has_log_derivative D2) (at x within A)"
  assumes "at x within A \<noteq> bot"
  shows   "D1 = D2"
proof -
  from assms have "D1 * f (netlimit (at x within A)) = D2 * f (netlimit (at x within A))"
    using assms has_field_derivative_unique unfolding has_log_derivative_def by blast
  with assms show "D1 = D2"
    by (auto simp: has_log_derivative_def)
qed

lemma has_log_derivative_cong_ev':
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)"
  shows   "(f has_log_derivative f') (at x) \<longleftrightarrow>
           (g has_log_derivative f') (at x)"
proof -
  from assms(1) have [simp]: "f x = g x"
    using eventually_nhds_x_imp_x by blast
  show ?thesis
    unfolding has_log_derivative_def
    apply (intro conj_cong)
    using DERIV_cong_ev[OF refl assms refl] assms
    apply simp_all
    done
qed

lemma has_log_derivative_cong_ev:
  assumes "eventually (\<lambda>x. f x = g x) (at x within A)" "f x = g x"
  shows   "(f has_log_derivative f') (at x within A) \<longleftrightarrow>
           (g has_log_derivative f') (at x within A)"
  unfolding has_log_derivative_def
  apply (cases "at x within A = bot"; intro conj_cong)
  using has_field_derivative_cong_eventually[OF assms] assms
     apply (simp_all add: Lim_ident_at)
  done  

lemma has_log_derivative_cong:
  "(f has_log_derivative X) F \<Longrightarrow> X = Y \<Longrightarrow> (f has_log_derivative Y) F"
  by simp

named_theorems derivative_congs

lemmas [derivative_congs] =
  has_derivative_eq_rhs DERIV_cong has_vector_derivative_eq_rhs has_log_derivative_cong

(* TODO: make version in distribution similarly extensible and then drop this *)
setup \<open>
  let
    fun eq_thms ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>derivative_congs\<close>
    fun eq_rule ctxt thm = get_first (try (fn eq_thm => eq_thm OF [thm])) (eq_thms ctxt)
  in
    Global_Theory.add_thms_dynamic
      (\<^binding>\<open>derivative_eq_intros\<close>,
        fn context =>
          Named_Theorems.get (Context.proof_of context) \<^named_theorems>\<open>derivative_intros\<close>
          |> map_filter (eq_rule (Context.proof_of context)))
  end
\<close>

lemma has_log_derivative_imp_has_field_derivative:
  assumes "(f has_log_derivative (f' / f x)) (at x within A)"
  shows   "(f has_field_derivative f') (at x within A)"
  using assms by (cases "at x within A = bot") (auto simp: has_log_derivative_def Lim_ident_at)

lemma has_log_derivative_imp_has_field_derivative':
  assumes "(f has_log_derivative f') (at x within A)"
  shows   "(f has_field_derivative (f' * f x)) (at x within A)"
  using assms by (cases "at x within A = bot") (auto simp: has_log_derivative_def Lim_ident_at)

lemma has_log_derivative_imp_nonzero:
  assumes "(f has_log_derivative f') (at x within A)" "at x within A \<noteq> bot"
  shows   "f x \<noteq> 0"
  using assms unfolding has_log_derivative_def by (auto simp: Lim_ident_at)

lemma has_field_derivative_imp_has_log_derivative:
  assumes "(f has_field_derivative (f' * f x)) (at x within A)" "f x \<noteq> 0"
  shows   "(f has_log_derivative f') (at x within A)"
  using assms by (cases "at x within A = bot") (auto simp: has_log_derivative_def Lim_ident_at)

lemma has_field_derivative_imp_has_log_derivative':
  assumes "(f has_field_derivative f') (at x within A)" "f x \<noteq> 0"
  shows   "(f has_log_derivative (f' / f x)) (at x within A)"
  using assms by (cases "at x within A = bot") (auto simp: has_log_derivative_def Lim_ident_at)

lemma has_log_derivative_chain:
  assumes "(f has_log_derivative f') (at (g x))"
  assumes "(g has_field_derivative g') (at x within A)"
  shows "((f \<circ> g) has_log_derivative (f' * g')) (at x within A)"
proof (cases "at x within A = bot")
  case False
  hence [simp]: "netlimit (at x within A) = x"
    by (simp add: Lim_ident_at)
  show ?thesis
    unfolding has_log_derivative_def
  proof
    have "((f \<circ> g) has_field_derivative f' * f (g x) * g') (at x within A)"
      by (rule DERIV_chain) (use assms False in \<open>auto simp: has_log_derivative_def\<close>)
    thus "(f \<circ> g has_field_derivative (f' * g') * (f \<circ> g) (netlimit (at x within A))) (at x within A)"
      by (simp add: mult_ac)
  qed (use assms in \<open>auto simp: has_log_derivative_def\<close>)
qed auto

lemma has_log_derivative_const [intro, derivative_intros]:
  "c \<noteq> 0 \<Longrightarrow> ((\<lambda>_. c) has_log_derivative 0) (at x within A)"
  by (auto simp: has_log_derivative_def intro!: derivative_eq_intros)

lemma has_log_derivative_uminus [derivative_intros]:
  assumes "((\<lambda>x. f x) has_log_derivative f') (at x within A)"
  shows   "((\<lambda>x. -f x) has_log_derivative f') (at x within A)"
  using assms
  by (cases "at x within A = bot")
     (auto simp: has_log_derivative_def algebra_simps Lim_ident_at intro!: derivative_eq_intros)

lemma has_log_derivative_exp [derivative_intros]:
  assumes "((\<lambda>x. f x) has_field_derivative f') (at x within A)"
  shows   "((\<lambda>x. exp (f x)) has_log_derivative f') (at x within A)"
  using assms
  by (cases "at x within A = bot")
     (auto simp: has_log_derivative_def Lim_ident_at intro!: derivative_eq_intros)

lemma has_log_derivative_mult [derivative_intros]:
  assumes "((\<lambda>x. f x) has_log_derivative f') (at x within A)"
  assumes "((\<lambda>x. g x) has_log_derivative g') (at x within A)"
  shows   "((\<lambda>x. f x * g x) has_log_derivative (f' + g')) (at x within A)"
  using assms
  by (cases "at x within A = bot")
     (auto simp: has_log_derivative_def algebra_simps Lim_ident_at intro!: derivative_eq_intros)

lemma has_log_derivative_inverse [derivative_intros]:
  assumes "((\<lambda>x. f x) has_log_derivative f') (at x within A)"
  shows   "((\<lambda>x. inverse (f x)) has_log_derivative (-f')) (at x within A)"
  using assms
  by (cases "at x within A = bot")
     (auto simp: has_log_derivative_def algebra_simps Lim_ident_at intro!: derivative_eq_intros)

lemma has_log_derivative_divide [derivative_intros]:
  assumes "((\<lambda>x. f x) has_log_derivative f') (at x within A)"
  assumes "((\<lambda>x. g x) has_log_derivative g') (at x within A)"
  shows   "((\<lambda>x. f x / g x) has_log_derivative (f' - g')) (at x within A)"
  using assms
  by (cases "at x within A = bot")
     (auto simp: has_log_derivative_def field_simps Lim_ident_at intro!: derivative_eq_intros)

lemma has_log_derivative_power [derivative_intros]:
  assumes "((\<lambda>x. f x) has_log_derivative f') (at x within A)"
  shows   "((\<lambda>x. f x ^ n) has_log_derivative (of_nat n * f')) (at x within A)"
  using assms by (induction n) (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma has_log_derivative_power_int [derivative_intros]:
  assumes [derivative_intros]: "((\<lambda>x. f x) has_log_derivative f') (at x within A)"
  shows   "((\<lambda>x. f x powi n) has_log_derivative (of_int n * f')) (at x within A)"
  by (cases "n \<ge> 0") (auto simp: power_int_def intro!: derivative_eq_intros)

lemma has_log_derivative_prod [derivative_intros]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> (f i has_log_derivative f' i) (at x within A)"
  shows "((\<lambda>x. \<Prod>i\<in>I. f i x) has_log_derivative (\<Sum>i\<in>I. f' i)) (at x within A)"
  using assms by (induction I rule: infinite_finite_induct) (auto intro!: derivative_eq_intros)

lemma has_log_derivative_prod_list [derivative_intros]:
  assumes "\<And>i. i \<in> set is \<Longrightarrow> (f i has_log_derivative f' i) (at x within A)"
  shows "((\<lambda>x. \<Prod>i\<leftarrow>is. f i x) has_log_derivative (\<Sum>i\<leftarrow>is. f' i)) (at x within A)"
  using assms by (induction "is") (auto intro!: derivative_eq_intros)

lemma has_log_derivative_prod_mset [derivative_intros]:
  assumes "\<And>i. i \<in># I \<Longrightarrow> (f i has_log_derivative f' i) (at x within A)"
  shows "((\<lambda>x. \<Prod>i\<in>#I. f i x) has_log_derivative (\<Sum>i\<in>#I. f' i)) (at x within A)"
  using assms by (induction I) (auto intro!: derivative_eq_intros)

end