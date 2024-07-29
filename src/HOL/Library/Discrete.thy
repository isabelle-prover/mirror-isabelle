(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Common discrete functions\<close>

theory Discrete
imports Complex_Main
begin

subsection \<open>Discrete logarithm\<close>

context
begin

qualified fun log :: "nat \<Rightarrow> nat"
  where [simp del]: "log n = (if n < 2 then 0 else Suc (log (n div 2)))"

lemma log_induct [consumes 1, case_names one double]:
  fixes n :: nat
  assumes "n > 0"
  assumes one: "P 1"
  assumes double: "\<And>n. n \<ge> 2 \<Longrightarrow> P (n div 2) \<Longrightarrow> P n"
  shows "P n"
using \<open>n > 0\<close> proof (induct n rule: log.induct)
  fix n
  assume "\<not> n < 2 \<Longrightarrow>
          0 < n div 2 \<Longrightarrow> P (n div 2)"
  then have *: "n \<ge> 2 \<Longrightarrow> P (n div 2)" by simp
  assume "n > 0"
  show "P n"
  proof (cases "n = 1")
    case True
    with one show ?thesis by simp
  next
    case False
    with \<open>n > 0\<close> have "n \<ge> 2" by auto
    with * have "P (n div 2)" .
    with \<open>n \<ge> 2\<close> show ?thesis by (rule double)
  qed
qed
  
lemma log_zero [simp]: "log 0 = 0"
  by (simp add: log.simps)

lemma log_one [simp]: "log 1 = 0"
  by (simp add: log.simps)

lemma log_Suc_zero [simp]: "log (Suc 0) = 0"
  using log_one by simp

lemma log_rec: "n \<ge> 2 \<Longrightarrow> log n = Suc (log (n div 2))"
  by (simp add: log.simps)

lemma log_twice [simp]: "n \<noteq> 0 \<Longrightarrow> log (2 * n) = Suc (log n)"
  by (simp add: log_rec)

lemma log_half [simp]: "log (n div 2) = log n - 1"
proof (cases "n < 2")
  case True
  then have "n = 0 \<or> n = 1" by arith
  then show ?thesis by (auto simp del: One_nat_def)
next
  case False
  then show ?thesis by (simp add: log_rec)
qed

lemma log_power [simp]: "log (2 ^ n) = n"
  by (induct n) simp_all

lemma log_mono: "mono log"
proof
  fix m n :: nat
  assume "m \<le> n"
  then show "log m \<le> log n"
  proof (induct m arbitrary: n rule: log.induct)
    case (1 m)
    then have mn2: "m div 2 \<le> n div 2" by arith
    show "log m \<le> log n"
    proof (cases "m \<ge> 2")
      case False
      then have "m = 0 \<or> m = 1" by arith
      then show ?thesis by (auto simp del: One_nat_def)
    next
      case True then have "\<not> m < 2" by simp
      with mn2 have "n \<ge> 2" by arith
      from True have m2_0: "m div 2 \<noteq> 0" by arith
      with mn2 have n2_0: "n div 2 \<noteq> 0" by arith
      from \<open>\<not> m < 2\<close> "1.hyps" mn2 have "log (m div 2) \<le> log (n div 2)" by blast
      with m2_0 n2_0 have "log (2 * (m div 2)) \<le> log (2 * (n div 2))" by simp
      with m2_0 n2_0 \<open>m \<ge> 2\<close> \<open>n \<ge> 2\<close> show ?thesis by (simp only: log_rec [of m] log_rec [of n]) simp
    qed
  qed
qed

lemma log_exp2_le:
  assumes "n > 0"
  shows "2 ^ log n \<le> n"
  using assms
proof (induct n rule: log_induct)
  case one
  then show ?case by simp
next
  case (double n)
  with log_mono have "log n \<ge> Suc 0"
    by (simp add: log.simps)
  assume "2 ^ log (n div 2) \<le> n div 2"
  with \<open>n \<ge> 2\<close> have "2 ^ (log n - Suc 0) \<le> n div 2" by simp
  then have "2 ^ (log n - Suc 0) * 2 ^ 1 \<le> n div 2 * 2" by simp
  with \<open>log n \<ge> Suc 0\<close> have "2 ^ log n \<le> n div 2 * 2"
    unfolding power_add [symmetric] by simp
  also have "n div 2 * 2 \<le> n" by (cases "even n") simp_all
  finally show ?case .
qed

lemma log_exp2_gt: "2 * 2 ^ log n > n"
proof (cases "n > 0")
  case True
  thus ?thesis
  proof (induct n rule: log_induct)
    case (double n)
    thus ?case
      by (cases "even n") (auto elim!: evenE oddE simp: field_simps log.simps)
  qed simp_all
qed simp_all

lemma log_exp2_ge: "2 * 2 ^ log n \<ge> n"
  using log_exp2_gt[of n] by simp

lemma log_le_iff: "m \<le> n \<Longrightarrow> log m \<le> log n"
  by (rule monoD [OF log_mono])

lemma log_eqI:
  assumes "n > 0" "2^k \<le> n" "n < 2 * 2^k"
  shows   "log n = k"
proof (rule antisym)
  from \<open>n > 0\<close> have "2 ^ log n \<le> n" by (rule log_exp2_le)
  also have "\<dots> < 2 ^ Suc k" using assms by simp
  finally have "log n < Suc k" by (subst (asm) power_strict_increasing_iff) simp_all
  thus "log n \<le> k" by simp
next
  have "2^k \<le> n" by fact
  also have "\<dots> < 2^(Suc (log n))" by (simp add: log_exp2_gt)
  finally have "k < Suc (log n)" by (subst (asm) power_strict_increasing_iff) simp_all
  thus "k \<le> log n" by simp
qed

lemma log_altdef: "log n = (if n = 0 then 0 else nat \<lfloor>Transcendental.log 2 (real_of_nat n)\<rfloor>)"
proof (cases "n = 0")
  case False
  have "\<lfloor>Transcendental.log 2 (real_of_nat n)\<rfloor> = int (log n)"
  proof (rule floor_unique)
    from False have "2 powr (real (log n)) \<le> real n"
      by (simp add: powr_realpow log_exp2_le)
    hence "Transcendental.log 2 (2 powr (real (log n))) \<le> Transcendental.log 2 (real n)"
      using False by (subst Transcendental.log_le_cancel_iff) simp_all
    also have "Transcendental.log 2 (2 powr (real (log n))) = real (log n)" by simp
    finally show "real_of_int (int (log n)) \<le> Transcendental.log 2 (real n)" by simp
  next
    have "real n < real (2 * 2 ^ log n)"
      by (subst of_nat_less_iff) (rule log_exp2_gt)
    also have "\<dots> = 2 powr (real (log n) + 1)"
      by (simp add: powr_add powr_realpow)
    finally have "Transcendental.log 2 (real n) < Transcendental.log 2 \<dots>"
      using False by (subst Transcendental.log_less_cancel_iff) simp_all
    also have "\<dots> = real (log n) + 1" by simp
    finally show "Transcendental.log 2 (real n) < real_of_int (int (log n)) + 1" by simp
  qed
  thus ?thesis by simp
qed simp_all


subsection \<open>Discrete square root\<close>

qualified definition sqrt :: "nat \<Rightarrow> nat"
  where "sqrt n = Max {m. m\<^sup>2 \<le> n}"

lemma sqrt_aux:
  fixes n :: nat
  shows "finite {m. m\<^sup>2 \<le> n}" and "{m. m\<^sup>2 \<le> n} \<noteq> {}"
proof -
  { fix m
    assume "m\<^sup>2 \<le> n"
    then have "m \<le> n"
      by (cases m) (simp_all add: power2_eq_square)
  } note ** = this
  then have "{m. m\<^sup>2 \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then show "finite {m. m\<^sup>2 \<le> n}" by (rule finite_subset) rule
  have "0\<^sup>2 \<le> n" by simp
  then show *: "{m. m\<^sup>2 \<le> n} \<noteq> {}" by blast
qed

lemma sqrt_unique:
  assumes "m^2 \<le> n" "n < (Suc m)^2"
  shows   "Discrete.sqrt n = m"
proof -
  have "m' \<le> m" if "m'^2 \<le> n" for m'
  proof -
    note that
    also note assms(2)
    finally have "m' < Suc m" by (rule power_less_imp_less_base) simp_all
    thus "m' \<le> m" by simp
  qed
  with \<open>m^2 \<le> n\<close> sqrt_aux[of n] show ?thesis unfolding Discrete.sqrt_def
    by (intro antisym Max.boundedI Max.coboundedI) simp_all
qed


lemma sqrt_code[code]: "sqrt n = Max (Set.filter (\<lambda>m. m\<^sup>2 \<le> n) {0..n})"
proof -
  from power2_nat_le_imp_le [of _ n] have "{m. m \<le> n \<and> m\<^sup>2 \<le> n} = {m. m\<^sup>2 \<le> n}" by auto
  then show ?thesis by (simp add: sqrt_def Set.filter_def)
qed

lemma sqrt_inverse_power2 [simp]: "sqrt (n\<^sup>2) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: sqrt_def power2_nat_le_eq_le intro: antisym)
qed

lemma sqrt_zero [simp]: "sqrt 0 = 0"
  using sqrt_inverse_power2 [of 0] by simp

lemma sqrt_one [simp]: "sqrt 1 = 1"
  using sqrt_inverse_power2 [of 1] by simp

lemma mono_sqrt: "mono sqrt"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "sqrt m \<le> sqrt n"
    by (auto intro!: Max_mono \<open>0 * 0 \<le> m\<close> finite_less_ub simp add: power2_eq_square sqrt_def)
qed

lemma mono_sqrt': "m \<le> n \<Longrightarrow> Discrete.sqrt m \<le> Discrete.sqrt n"
  using mono_sqrt unfolding mono_def by auto

lemma sqrt_greater_zero_iff [simp]: "sqrt n > 0 \<longleftrightarrow> n > 0"
proof -
  have *: "0 < Max {m. m\<^sup>2 \<le> n} \<longleftrightarrow> (\<exists>a\<in>{m. m\<^sup>2 \<le> n}. 0 < a)"
    by (rule Max_gr_iff) (fact sqrt_aux)+
  show ?thesis
  proof
    assume "0 < sqrt n"
    then have "0 < Max {m. m\<^sup>2 \<le> n}" by (simp add: sqrt_def)
    with * show "0 < n" by (auto dest: power2_nat_le_imp_le)
  next
    assume "0 < n"
    then have "1\<^sup>2 \<le> n \<and> 0 < (1::nat)" by simp
    then have "\<exists>q. q\<^sup>2 \<le> n \<and> 0 < q" ..
    with * have "0 < Max {m. m\<^sup>2 \<le> n}" by blast
    then show "0 < sqrt n" by  (simp add: sqrt_def)
  qed
qed

lemma sqrt_power2_le [simp]: "(sqrt n)\<^sup>2 \<le> n" (* FIXME tune proof *)
proof (cases "n > 0")
  case False then show ?thesis by simp
next
  case True then have "sqrt n > 0" by simp
  then have "mono (times (Max {m. m\<^sup>2 \<le> n}))" by (auto intro: mono_times_nat simp add: sqrt_def)
  then have *: "Max {m. m\<^sup>2 \<le> n} * Max {m. m\<^sup>2 \<le> n} = Max (times (Max {m. m\<^sup>2 \<le> n}) ` {m. m\<^sup>2 \<le> n})"
    using sqrt_aux [of n] by (rule mono_Max_commute)
  have "\<And>a. a * a \<le> n \<Longrightarrow> Max {m. m * m \<le> n} * a \<le> n"
  proof -
    fix q
    assume "q * q \<le> n"
    show "Max {m. m * m \<le> n} * q \<le> n"
    proof (cases "q > 0")
      case False then show ?thesis by simp
    next
      case True then have "mono (times q)" by (rule mono_times_nat)
      then have "q * Max {m. m * m \<le> n} = Max (times q ` {m. m * m \<le> n})"
        using sqrt_aux [of n] by (auto simp add: power2_eq_square intro: mono_Max_commute)
      then have "Max {m. m * m \<le> n} * q = Max (times q ` {m. m * m \<le> n})" by (simp add: ac_simps)
      moreover have "finite ((*) q ` {m. m * m \<le> n})"
        by (metis (mono_tags) finite_imageI finite_less_ub le_square)
      moreover have "\<exists>x. x * x \<le> n"
        by (metis \<open>q * q \<le> n\<close>)
      ultimately show ?thesis
        by simp (metis \<open>q * q \<le> n\<close> le_cases mult_le_mono1 mult_le_mono2 order_trans)
    qed
  qed
  then have "Max ((*) (Max {m. m * m \<le> n}) ` {m. m * m \<le> n}) \<le> n"
    apply (subst Max_le_iff)
      apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
     apply auto
    apply (metis le0 mult_0_right)
    done
  with * show ?thesis by (simp add: sqrt_def power2_eq_square)
qed

lemma sqrt_le: "sqrt n \<le> n"
  using sqrt_aux [of n] by (auto simp add: sqrt_def intro: power2_nat_le_imp_le)

text \<open>Additional facts about the discrete square root, thanks to Julian Biendarra, Manuel Eberl\<close>
  
lemma Suc_sqrt_power2_gt: "n < (Suc (Discrete.sqrt n))^2"
  using Max_ge[OF Discrete.sqrt_aux(1), of "Discrete.sqrt n + 1" n]
  by (cases "n < (Suc (Discrete.sqrt n))^2") (simp_all add: Discrete.sqrt_def)

lemma le_sqrt_iff: "x \<le> Discrete.sqrt y \<longleftrightarrow> x^2 \<le> y"
proof -
  have "x \<le> Discrete.sqrt y \<longleftrightarrow> (\<exists>z. z\<^sup>2 \<le> y \<and> x \<le> z)"    
    using Max_ge_iff[OF Discrete.sqrt_aux, of x y] by (simp add: Discrete.sqrt_def)
  also have "\<dots> \<longleftrightarrow> x^2 \<le> y"
  proof safe
    fix z assume "x \<le> z" "z ^ 2 \<le> y"
    thus "x^2 \<le> y" by (intro le_trans[of "x^2" "z^2" y]) (simp_all add: power2_nat_le_eq_le)
  qed auto
  finally show ?thesis .
qed
  
lemma le_sqrtI: "x^2 \<le> y \<Longrightarrow> x \<le> Discrete.sqrt y"
  by (simp add: le_sqrt_iff)

lemma sqrt_le_iff: "Discrete.sqrt y \<le> x \<longleftrightarrow> (\<forall>z. z^2 \<le> y \<longrightarrow> z \<le> x)"
  using Max.bounded_iff[OF Discrete.sqrt_aux] by (simp add: Discrete.sqrt_def)

lemma sqrt_leI:
  "(\<And>z. z^2 \<le> y \<Longrightarrow> z \<le> x) \<Longrightarrow> Discrete.sqrt y \<le> x"
  by (simp add: sqrt_le_iff)
    
lemma sqrt_Suc:
  "Discrete.sqrt (Suc n) = (if \<exists>m. Suc n = m^2 then Suc (Discrete.sqrt n) else Discrete.sqrt n)"
proof cases
  assume "\<exists> m. Suc n = m^2"
  then obtain m where m_def: "Suc n = m^2" by blast
  then have lhs: "Discrete.sqrt (Suc n) = m" by simp
  from m_def sqrt_power2_le[of n] 
    have "(Discrete.sqrt n)^2 < m^2" by linarith
  with power2_less_imp_less have lt_m: "Discrete.sqrt n < m" by blast
  from m_def Suc_sqrt_power2_gt[of "n"]
    have "m^2 \<le> (Suc(Discrete.sqrt n))^2"
      by linarith
  with power2_nat_le_eq_le have "m \<le> Suc (Discrete.sqrt n)" by blast
  with lt_m have "m = Suc (Discrete.sqrt n)" by simp
  with lhs m_def show ?thesis by fastforce
next
  assume asm: "\<not> (\<exists> m. Suc n = m^2)"
  hence "Suc n \<noteq> (Discrete.sqrt (Suc n))^2" by simp
  with sqrt_power2_le[of "Suc n"] 
    have "Discrete.sqrt (Suc n) \<le> Discrete.sqrt n" by (intro le_sqrtI) linarith
  moreover have "Discrete.sqrt (Suc n) \<ge> Discrete.sqrt n"
    by (intro monoD[OF mono_sqrt]) simp_all
  ultimately show ?thesis using asm by simp
qed

end

end
