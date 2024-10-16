(* Author: Johannes Hölzl, TU München *)

section \<open>Formalization of a Countermeasure by Koepf \& Duermuth 2009\<close>

theory Koepf_Duermuth_Countermeasure
  imports "HOL-Probability.Information"
begin

lemma SIGMA_image_vimage:
  "snd ` (SIGMA x:f`X. f -` {x} \<inter> X) = X"
  by (auto simp: image_iff)

declare inj_split_Cons[simp]

definition extensionalD :: "'b \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "extensionalD d A = {f. \<forall>x. x \<notin> A \<longrightarrow> f x = d}"

lemma extensionalD_empty[simp]: "extensionalD d {} = {\<lambda>x. d}"
  unfolding extensionalD_def by (simp add: set_eq_iff fun_eq_iff)

lemma funset_eq_UN_fun_upd_I:
  assumes *: "\<And>f. f \<in> F (insert a A) \<Longrightarrow> f(a := d) \<in> F A"
  and **: "\<And>f. f \<in> F (insert a A) \<Longrightarrow> f a \<in> G (f(a:=d))"
  and ***: "\<And>f x. \<lbrakk> f \<in> F A ; x \<in> G f \<rbrakk> \<Longrightarrow> f(a:=x) \<in> F (insert a A)"
  shows "F (insert a A) = (\<Union>f\<in>F A. fun_upd f a ` (G f))"
proof safe
  fix f assume f: "f \<in> F (insert a A)"
  show "f \<in> (\<Union>f\<in>F A. fun_upd f a ` G f)"
  proof (rule UN_I[of "f(a := d)"])
    show "f(a := d) \<in> F A" using *[OF f] .
    show "f \<in> fun_upd (f(a:=d)) a ` G (f(a:=d))"
    proof (rule image_eqI[of _ _ "f a"])
      show "f a \<in> G (f(a := d))" using **[OF f] .
    qed simp
  qed
next
  fix f x assume "f \<in> F A" "x \<in> G f"
  from ***[OF this] show "f(a := x) \<in> F (insert a A)" .
qed

lemma extensionalD_insert[simp]:
  assumes "a \<notin> A"
  shows "extensionalD d (insert a A) \<inter> (insert a A \<rightarrow> B) = (\<Union>f \<in> extensionalD d A \<inter> (A \<rightarrow> B). (\<lambda>b. f(a := b)) ` B)"
  apply (rule funset_eq_UN_fun_upd_I)
  using assms
  by (auto intro!: inj_onI dest: inj_onD split: if_split_asm simp: extensionalD_def)

lemma finite_extensionalD_funcset[simp, intro]:
  assumes "finite A" "finite B"
  shows "finite (extensionalD d A \<inter> (A \<rightarrow> B))"
  using assms by induct auto

lemma fun_upd_eq_iff: "f(a := b) = g(a := b') \<longleftrightarrow> b = b' \<and> f(a := d) = g(a := d)"
  by (auto simp: fun_eq_iff)

lemma card_funcset:
  assumes "finite A" "finite B"
  shows "card (extensionalD d A \<inter> (A \<rightarrow> B)) = card B ^ card A"
using \<open>finite A\<close> proof induct
  case (insert a A) thus ?case unfolding extensionalD_insert[OF \<open>a \<notin> A\<close>]
  proof (subst card_UN_disjoint, safe, simp_all)
    show "finite (extensionalD d A \<inter> (A \<rightarrow> B))" "\<And>f. finite (fun_upd f a ` B)"
      using \<open>finite B\<close> \<open>finite A\<close> by simp_all
  next
    fix f g b b' assume "f \<noteq> g" and eq: "f(a := b) = g(a := b')" and
      ext: "f \<in> extensionalD d A" "g \<in> extensionalD d A"
    have "f a = d" "g a = d"
      using ext \<open>a \<notin> A\<close> by (auto simp add: extensionalD_def)
    with \<open>f \<noteq> g\<close> eq show False unfolding fun_upd_eq_iff[of _ _ b _ _ d]
      by (auto simp: fun_upd_idem fun_upd_eq_iff)
  next
    have "card (fun_upd f a ` B) = card B"
      if "f \<in> extensionalD d A \<inter> (A \<rightarrow> B)" for f
    proof (auto intro!: card_image inj_onI)
      fix b b' assume "f(a := b) = f(a := b')"
      from fun_upd_eq_iff[THEN iffD1, OF this] show "b = b'" by simp
    qed
    then show "(\<Sum>i\<in>extensionalD d A \<inter> (A \<rightarrow> B). card (fun_upd i a ` B)) = card B * card B ^ card A"
      using insert by simp
  qed
qed simp

lemma prod_sum_distrib_lists:
  fixes P and S :: "'a set" and f :: "'a \<Rightarrow> _::semiring_0" assumes "finite S"
  shows "(\<Sum>ms\<in>{ms. set ms \<subseteq> S \<and> length ms = n \<and> (\<forall>i<n. P i (ms!i))}. \<Prod>x<n. f (ms ! x)) =
         (\<Prod>i<n. \<Sum>m\<in>{m\<in>S. P i m}. f m)"
proof (induct n arbitrary: P)
  case 0 then show ?case by (simp cong: conj_cong)
next
  case (Suc n)
  have *: "{ms. set ms \<subseteq> S \<and> length ms = Suc n \<and> (\<forall>i<Suc n. P i (ms ! i))} =
    (\<lambda>(xs, x). x#xs) ` ({ms. set ms \<subseteq> S \<and> length ms = n \<and> (\<forall>i<n. P (Suc i) (ms ! i))} \<times> {m\<in>S. P 0 m})"
    apply (auto simp: image_iff length_Suc_conv)
    apply force+
    apply (case_tac i)
    by force+
  show ?case unfolding *
    using Suc[of "\<lambda>i. P (Suc i)"]
    by (simp add: sum.reindex sum.cartesian_product'
      lessThan_Suc_eq_insert_0 prod.reindex sum_distrib_right[symmetric] sum_distrib_left[symmetric])
qed

declare space_point_measure[simp]

declare sets_point_measure[simp]

lemma measure_point_measure:
  "finite \<Omega> \<Longrightarrow> A \<subseteq> \<Omega> \<Longrightarrow> (\<And>x. x \<in> \<Omega> \<Longrightarrow> 0 \<le> p x) \<Longrightarrow>
    measure (point_measure \<Omega> (\<lambda>x. ennreal (p x))) A = (\<Sum>i\<in>A. p i)"
  unfolding measure_def
  by (subst emeasure_point_measure_finite) (auto simp: subset_eq sum_nonneg)

locale finite_information =
  fixes \<Omega> :: "'a set"
    and p :: "'a \<Rightarrow> real"
    and b :: real
  assumes finite_space[simp, intro]: "finite \<Omega>"
  and p_sums_1[simp]: "(\<Sum>\<omega>\<in>\<Omega>. p \<omega>) = 1"
  and positive_p[simp, intro]: "\<And>x. 0 \<le> p x"
  and b_gt_1[simp, intro]: "1 < b"

lemma (in finite_information) positive_p_sum[simp]: "0 \<le> sum p X"
   by (auto intro!: sum_nonneg)

sublocale finite_information \<subseteq> prob_space "point_measure \<Omega> p"
  by standard (simp add: one_ereal_def emeasure_point_measure_finite)

sublocale finite_information \<subseteq> information_space "point_measure \<Omega> p" b
  by standard simp

lemma (in finite_information) \<mu>'_eq: "A \<subseteq> \<Omega> \<Longrightarrow> prob A = sum p A"
  by (auto simp: measure_point_measure)

locale koepf_duermuth = K: finite_information keys K b + M: finite_information messages M b
    for b :: real
    and keys :: "'key set" and K :: "'key \<Rightarrow> real"
    and messages :: "'message set" and M :: "'message \<Rightarrow> real" +
  fixes observe :: "'key \<Rightarrow> 'message \<Rightarrow> 'observation"
    and n :: nat
begin

definition msgs :: "('key \<times> 'message list) set" where
  "msgs = keys \<times> {ms. set ms \<subseteq> messages \<and> length ms = n}"

definition P :: "('key \<times> 'message list) \<Rightarrow> real" where
  "P = (\<lambda>(k, ms). K k * (\<Prod>i<n. M (ms ! i)))"

end

sublocale koepf_duermuth \<subseteq> finite_information msgs P b
proof
  show "finite msgs" unfolding msgs_def
    using finite_lists_length_eq[OF M.finite_space, of n]
    by auto

  have [simp]: "\<And>A. inj_on (\<lambda>(xs, n). n # xs) A" by (force intro!: inj_onI)

  note sum_distrib_left[symmetric, simp]
  note sum_distrib_right[symmetric, simp]
  note sum.cartesian_product'[simp]

  have "(\<Sum>ms | set ms \<subseteq> messages \<and> length ms = n. \<Prod>x<length ms. M (ms ! x)) = 1"
  proof (induct n)
    case 0 then show ?case by (simp cong: conj_cong)
  next
    case (Suc n)
    then show ?case
      by (simp add: lists_length_Suc_eq lessThan_Suc_eq_insert_0
                    sum.reindex prod.reindex)
  qed
  then show "sum P msgs = 1"
    unfolding msgs_def P_def by simp
  have "0 \<le> (\<Prod>x\<in>A. M (f x))" for A f
    by (auto simp: prod_nonneg)
  then show "0 \<le> P x" for x
    unfolding P_def by (auto split: prod.split simp: zero_le_mult_iff)
qed auto

context koepf_duermuth
begin

definition observations :: "'observation set" where
  "observations = (\<Union>f\<in>observe ` keys. f ` messages)"

lemma finite_observations[simp, intro]: "finite observations"
  unfolding observations_def by auto

definition OB :: "'key \<times> 'message list \<Rightarrow> 'observation list" where
  "OB = (\<lambda>(k, ms). map (observe k) ms)"

definition t :: "'observation list \<Rightarrow> 'observation \<Rightarrow> nat" where
  t_def2: "t seq obs = card { i. i < length seq \<and> seq ! i = obs}"

lemma t_def: "t seq obs = length (filter ((=) obs) seq)"
  unfolding t_def2 length_filter_conv_card by (subst eq_commute) simp

lemma card_T_bound: "card ((t\<circ>OB)`msgs) \<le> (n+1)^card observations"
proof -
  have "(t\<circ>OB)`msgs \<subseteq> extensionalD 0 observations \<inter> (observations \<rightarrow> {.. n})"
    unfolding observations_def extensionalD_def OB_def msgs_def
    by (auto simp add: t_def comp_def image_iff subset_eq)
  with finite_extensionalD_funcset
  have "card ((t\<circ>OB)`msgs) \<le> card (extensionalD 0 observations \<inter> (observations \<rightarrow> {.. n}))"
    by (rule card_mono) auto
  also have "\<dots> = (n + 1) ^ card observations"
    by (subst card_funcset) auto
  finally show ?thesis .
qed

abbreviation
 "p A \<equiv> sum P A"

abbreviation
  "\<mu> \<equiv> point_measure msgs P"

abbreviation probability (\<open>\<P>'(_') _\<close>) where
  "\<P>(X) x \<equiv> measure \<mu> (X -` x \<inter> msgs)"

abbreviation joint_probability (\<open>\<P>'(_ ; _') _\<close>) where
  "\<P>(X ; Y) x \<equiv> \<P>(\<lambda>x. (X x, Y x)) x"

no_notation disj  (infixr \<open>|\<close> 30)

abbreviation conditional_probability (\<open>\<P>'(_ | _') _\<close>) where
  "\<P>(X | Y) x \<equiv> (\<P>(X ; Y) x) / \<P>(Y) (snd`x)"

notation
  entropy_Pow (\<open>\<H>'( _ ')\<close>)

notation
  conditional_entropy_Pow (\<open>\<H>'( _ | _ ')\<close>)

notation
  mutual_information_Pow (\<open>\<I>'( _ ; _ ')\<close>)

lemma t_eq_imp_bij_func:
  assumes "t xs = t ys"
  shows "\<exists>f. bij_betw f {..<length xs} {..<length ys} \<and> (\<forall>i<length xs. xs ! i = ys ! (f i))"
proof -
  from assms have \<open>mset xs = mset ys\<close>
    using assms by (simp add: fun_eq_iff t_def multiset_eq_iff flip: count_mset)
  then obtain p where \<open>p permutes {..<length ys}\<close> \<open>permute_list p ys = xs\<close>
    by (rule mset_eq_permutation)
  then have \<open>bij_betw p {..<length xs} {..<length ys}\<close> \<open>\<forall>i<length xs. xs ! i = ys ! p i\<close>
    by (auto dest: permutes_imp_bij simp add: permute_list_nth)
  then show ?thesis
    by blast
qed

lemma \<P>_k: assumes "k \<in> keys" shows "\<P>(fst) {k} = K k"
proof -
  from assms have *:
      "fst -` {k} \<inter> msgs = {k}\<times>{ms. set ms \<subseteq> messages \<and> length ms = n}"
    unfolding msgs_def by auto
  show "(\<P>(fst) {k}) = K k"
    apply (simp add: \<mu>'_eq)
    apply (simp add: * P_def)
    apply (simp add: sum.cartesian_product')
    using prod_sum_distrib_lists[OF M.finite_space, of M n "\<lambda>x x. True"] \<open>k \<in> keys\<close>
    by (auto simp add: sum_distrib_left[symmetric] subset_eq prod.neutral_const)
qed

lemma fst_image_msgs[simp]: "fst`msgs = keys"
proof -
  from M.not_empty obtain m where "m \<in> messages" by auto
  then have *: "{m. set m \<subseteq> messages \<and> length m = n} \<noteq> {}"
    by (auto intro!: exI[of _ "replicate n m"])
  then show ?thesis
    unfolding msgs_def fst_image_times if_not_P[OF *] by simp
qed

lemma sum_distribution_cut:
  "\<P>(X) {x} = (\<Sum>y \<in> Y`space \<mu>. \<P>(X ; Y) {(x, y)})"
  by (subst finite_measure_finite_Union[symmetric])
     (auto simp add: disjoint_family_on_def inj_on_def
           intro!: arg_cong[where f=prob])

lemma prob_conj_imp1:
  "prob ({x. Q x} \<inter> msgs) = 0 \<Longrightarrow> prob ({x. Pr x \<and> Q x} \<inter> msgs) = 0"
  using finite_measure_mono[of "{x. Pr x \<and> Q x} \<inter> msgs" "{x. Q x} \<inter> msgs"]
  using measure_nonneg[of \<mu> "{x. Pr x \<and> Q x} \<inter> msgs"]
  by (simp add: subset_eq)

lemma prob_conj_imp2:
  "prob ({x. Pr x} \<inter> msgs) = 0 \<Longrightarrow> prob ({x. Pr x \<and> Q x} \<inter> msgs) = 0"
  using finite_measure_mono[of "{x. Pr x \<and> Q x} \<inter> msgs" "{x. Pr x} \<inter> msgs"]
  using measure_nonneg[of \<mu> "{x. Pr x \<and> Q x} \<inter> msgs"]
  by (simp add: subset_eq)

lemma simple_function_finite: "simple_function \<mu> f"
  by (simp add: simple_function_def)

lemma entropy_commute: "\<H>(\<lambda>x. (X x, Y x)) = \<H>(\<lambda>x. (Y x, X x))"
  apply (subst (1 2) entropy_simple_distributed[OF simple_distributedI[OF simple_function_finite _ refl]])
  unfolding space_point_measure
proof -
  have eq: "(\<lambda>x. (X x, Y x)) ` msgs = (\<lambda>(x, y). (y, x)) ` (\<lambda>x. (Y x, X x)) ` msgs"
    by auto
  show "- (\<Sum>x\<in>(\<lambda>x. (X x, Y x)) ` msgs. (\<P>(X ; Y) {x}) * log b (\<P>(X ; Y) {x})) =
    - (\<Sum>x\<in>(\<lambda>x. (Y x, X x)) ` msgs. (\<P>(Y ; X) {x}) * log b (\<P>(Y ; X) {x}))"
    unfolding eq
    apply (subst sum.reindex)
    apply (auto simp: vimage_def inj_on_def intro!: sum.cong arg_cong[where f="\<lambda>x. prob x * log b (prob x)"])
    done
qed simp_all

lemma (in -) measure_eq_0I: "A = {} \<Longrightarrow> measure M A = 0" by simp

lemma conditional_entropy_eq_ce_with_hypothesis:
  "\<H>(X | Y) = -(\<Sum>y\<in>Y`msgs. (\<P>(Y) {y}) * (\<Sum>x\<in>X`msgs. (\<P>(X ; Y) {(x,y)}) / (\<P>(Y) {y}) *
     log b ((\<P>(X ; Y) {(x,y)}) / (\<P>(Y) {y}))))"
  apply (subst conditional_entropy_eq[OF
    simple_distributedI[OF simple_function_finite _ refl]
    simple_distributedI[OF simple_function_finite _ refl]])
  unfolding space_point_measure
proof -
  have "- (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` msgs. (\<P>(X ; Y) {(x, y)}) * log b ((\<P>(X ; Y) {(x, y)}) / (\<P>(Y) {y}))) =
    - (\<Sum>x\<in>X`msgs. (\<Sum>y\<in>Y`msgs. (\<P>(X ; Y) {(x, y)}) * log b ((\<P>(X ; Y) {(x, y)}) / (\<P>(Y) {y}))))"
    unfolding sum.cartesian_product
    apply (intro arg_cong[where f=uminus] sum.mono_neutral_left)
    apply (auto simp: vimage_def image_iff intro!: measure_eq_0I)
    apply metis
    done
  also have "\<dots> = - (\<Sum>y\<in>Y`msgs. (\<Sum>x\<in>X`msgs. (\<P>(X ; Y) {(x, y)}) * log b ((\<P>(X ; Y) {(x, y)}) / (\<P>(Y) {y}))))"
    by (subst sum.swap) rule
  also have "\<dots> = -(\<Sum>y\<in>Y`msgs. (\<P>(Y) {y}) * (\<Sum>x\<in>X`msgs. (\<P>(X ; Y) {(x,y)}) / (\<P>(Y) {y}) * log b ((\<P>(X ; Y) {(x,y)}) / (\<P>(Y) {y}))))"
    by (auto simp add: sum_distrib_left vimage_def intro!: sum.cong prob_conj_imp1)
  finally show "- (\<Sum>(x, y)\<in>(\<lambda>x. (X x, Y x)) ` msgs. (\<P>(X ; Y) {(x, y)}) * log b ((\<P>(X ; Y) {(x, y)}) / (\<P>(Y) {y}))) =
    -(\<Sum>y\<in>Y`msgs. (\<P>(Y) {y}) * (\<Sum>x\<in>X`msgs. (\<P>(X ; Y) {(x,y)}) / (\<P>(Y) {y}) * log b ((\<P>(X ; Y) {(x,y)}) / (\<P>(Y) {y}))))" .
qed simp_all

lemma ce_OB_eq_ce_t: "\<I>(fst ; OB) = \<I>(fst ; t\<circ>OB)"
proof -
  txt \<open>Lemma 2\<close>

  have t_eq_imp: "(\<P>(OB ; fst) {(obs, k)}) = (\<P>(OB ; fst) {(obs', k)})"
    if "k \<in> keys" "K k \<noteq> 0" and obs': "obs' \<in> OB ` msgs" and obs: "obs \<in> OB ` msgs"
      and eq: "t obs = t obs'"
    for k obs obs'
  proof -
    from t_eq_imp_bij_func[OF eq]
    obtain t_f where "bij_betw t_f {..<n} {..<n}" and
      obs_t_f: "\<And>i. i<n \<Longrightarrow> obs!i = obs' ! t_f i"
      using obs obs' unfolding OB_def msgs_def by auto
    then have t_f: "inj_on t_f {..<n}" "{..<n} = t_f`{..<n}" unfolding bij_betw_def by auto

    have *: "(\<P>(OB ; fst) {(obs, k)}) / K k =
            (\<Prod>i<n. \<Sum>m\<in>{m\<in>messages. observe k m = obs ! i}. M m)"
      if "obs \<in> OB`msgs" for obs
    proof -
      from that have **: "length ms = n \<Longrightarrow> OB (k, ms) = obs \<longleftrightarrow> (\<forall>i<n. observe k (ms!i) = obs ! i)"
        for ms
        unfolding OB_def msgs_def by (simp add: image_iff list_eq_iff_nth_eq)
      have "(\<P>(OB ; fst) {(obs, k)}) / K k =
          p ({k}\<times>{ms. (k,ms) \<in> msgs \<and> OB (k,ms) = obs}) / K k"
        by (simp add: \<mu>'_eq) (auto intro!: arg_cong[where f=p])
      also have "\<dots> = (\<Prod>i<n. \<Sum>m\<in>{m\<in>messages. observe k m = obs ! i}. M m)"
        unfolding P_def using \<open>K k \<noteq> 0\<close> \<open>k \<in> keys\<close>
        apply (simp add: sum.cartesian_product' sum_divide_distrib msgs_def ** cong: conj_cong)
        apply (subst prod_sum_distrib_lists[OF M.finite_space]) ..
      finally show ?thesis .
    qed

    have "(\<P>(OB ; fst) {(obs, k)}) / K k = (\<P>(OB ; fst) {(obs', k)}) / K k"
      unfolding *[OF obs] *[OF obs']
      using t_f(1) obs_t_f by (subst (2) t_f(2)) (simp add: prod.reindex)
    then show ?thesis using \<open>K k \<noteq> 0\<close> by auto
  qed

  let ?S = "\<lambda>obs. t -`{t obs} \<inter> OB`msgs"
  have P_t_eq_P_OB: "\<P>(t\<circ>OB ; fst) {(t obs, k)} = real (card (?S obs)) * \<P>(OB ; fst) {(obs, k)}"
    if "k \<in> keys" "K k \<noteq> 0" and obs: "obs \<in> OB`msgs"
    for k obs
  proof -
    have *: "((\<lambda>x. (t (OB x), fst x)) -` {(t obs, k)} \<inter> msgs) =
      (\<Union>obs'\<in>?S obs. ((\<lambda>x. (OB x, fst x)) -` {(obs', k)} \<inter> msgs))" by auto
    have df: "disjoint_family_on (\<lambda>obs'. (\<lambda>x. (OB x, fst x)) -` {(obs', k)} \<inter> msgs) (?S obs)"
      unfolding disjoint_family_on_def by auto
    have "\<P>(t\<circ>OB ; fst) {(t obs, k)} = (\<Sum>obs'\<in>?S obs. \<P>(OB ; fst) {(obs', k)})"
      unfolding comp_def
      using finite_measure_finite_Union[OF _ _ df]
      by (auto simp add: * intro!: sum_nonneg)
    also have "(\<Sum>obs'\<in>?S obs. \<P>(OB ; fst) {(obs', k)}) = real (card (?S obs)) * \<P>(OB ; fst) {(obs, k)}"
      by (simp add: t_eq_imp[OF \<open>k \<in> keys\<close> \<open>K k \<noteq> 0\<close> obs])
    finally show ?thesis .
  qed

  have CP_t_K: "\<P>(t\<circ>OB | fst) {(t obs, k)} =
    real (card (t -` {t obs} \<inter> OB ` msgs)) * \<P>(OB | fst) {(obs, k)}"
    if k: "k \<in> keys" and obs: "obs \<in> OB`msgs" for k obs
    using \<P>_k[OF k] P_t_eq_P_OB[OF k _ obs] by auto

  have CP_T_eq_CP_O: "\<P>(fst | t\<circ>OB) {(k, t obs)} = \<P>(fst | OB) {(k, obs)}"
    if "k \<in> keys" and obs: "obs \<in> OB`msgs" for k obs
  proof -
    from that have "t -`{t obs} \<inter> OB`msgs \<noteq> {}" (is "?S \<noteq> {}") by auto
    then have "real (card ?S) \<noteq> 0" by auto

    have "\<P>(fst | t\<circ>OB) {(k, t obs)} = \<P>(t\<circ>OB | fst) {(t obs, k)} * \<P>(fst) {k} / \<P>(t\<circ>OB) {t obs}"
      using finite_measure_mono[of "{x. fst x = k \<and> t (OB x) = t obs} \<inter> msgs" "{x. fst x = k} \<inter> msgs"]
      using measure_nonneg[of \<mu> "{x. fst x = k \<and> t (OB x) = t obs} \<inter> msgs"]
      by (auto simp add: vimage_def conj_commute subset_eq simp del: measure_nonneg)
    also have "(\<P>(t\<circ>OB) {t obs}) = (\<Sum>k'\<in>keys. (\<P>(t\<circ>OB|fst) {(t obs, k')}) * (\<P>(fst) {k'}))"
      using finite_measure_mono[of "{x. t (OB x) = t obs \<and> fst x = k} \<inter> msgs" "{x. fst x = k} \<inter> msgs"]
      using measure_nonneg[of \<mu> "{x. fst x = k \<and> t (OB x) = t obs} \<inter> msgs"]
      apply (simp add: sum_distribution_cut[of "t\<circ>OB" "t obs" fst])
      apply (auto intro!: sum.cong simp: subset_eq vimage_def prob_conj_imp1)
      done
    also have "\<P>(t\<circ>OB | fst) {(t obs, k)} * \<P>(fst) {k} / (\<Sum>k'\<in>keys. \<P>(t\<circ>OB|fst) {(t obs, k')} * \<P>(fst) {k'}) =
      \<P>(OB | fst) {(obs, k)} * \<P>(fst) {k} / (\<Sum>k'\<in>keys. \<P>(OB|fst) {(obs, k')} * \<P>(fst) {k'})"
      using CP_t_K[OF \<open>k\<in>keys\<close> obs] CP_t_K[OF _ obs] \<open>real (card ?S) \<noteq> 0\<close>
      by (simp only: sum_distrib_left[symmetric] ac_simps
          mult_divide_mult_cancel_left[OF \<open>real (card ?S) \<noteq> 0\<close>]
        cong: sum.cong)
    also have "(\<Sum>k'\<in>keys. \<P>(OB|fst) {(obs, k')} * \<P>(fst) {k'}) = \<P>(OB) {obs}"
      using sum_distribution_cut[of OB obs fst]
      by (auto intro!: sum.cong simp: prob_conj_imp1 vimage_def)
    also have "\<P>(OB | fst) {(obs, k)} * \<P>(fst) {k} / \<P>(OB) {obs} = \<P>(fst | OB) {(k, obs)}"
      by (auto simp: vimage_def conj_commute prob_conj_imp2)
    finally show ?thesis .
  qed

  let ?H = "\<lambda>obs. (\<Sum>k\<in>keys. \<P>(fst|OB) {(k, obs)} * log b (\<P>(fst|OB) {(k, obs)})) :: real"
  let ?Ht = "\<lambda>obs. (\<Sum>k\<in>keys. \<P>(fst|t\<circ>OB) {(k, obs)} * log b (\<P>(fst|t\<circ>OB) {(k, obs)})) :: real"

  have *: "?H obs = ?Ht (t obs)" if obs: "obs \<in> OB`msgs" for obs
  proof -
    have "?H obs = (\<Sum>k\<in>keys. \<P>(fst|t\<circ>OB) {(k, t obs)} * log b (\<P>(fst|t\<circ>OB) {(k, t obs)}))"
      using CP_T_eq_CP_O[OF _ obs]
      by simp
    then show ?thesis .
  qed

  have **: "\<And>x f A. (\<Sum>y\<in>t-`{x}\<inter>A. f y (t y)) = (\<Sum>y\<in>t-`{x}\<inter>A. f y x)" by auto

  have P_t_sum_P_O: "\<P>(t\<circ>OB) {t (OB x)} = (\<Sum>obs\<in>?S (OB x). \<P>(OB) {obs})" for x
  proof -
    have *: "(\<lambda>x. t (OB x)) -` {t (OB x)} \<inter> msgs =
      (\<Union>obs\<in>?S (OB x). OB -` {obs} \<inter> msgs)" by auto
    have df: "disjoint_family_on (\<lambda>obs. OB -` {obs} \<inter> msgs) (?S (OB x))"
      unfolding disjoint_family_on_def by auto
    show ?thesis
      unfolding comp_def
      using finite_measure_finite_Union[OF _ _ df]
      by (force simp add: * intro!: sum_nonneg)
  qed

  txt \<open>Lemma 3\<close>
  have "\<H>(fst | OB) = -(\<Sum>obs\<in>OB`msgs. \<P>(OB) {obs} * ?Ht (t obs))"
    unfolding conditional_entropy_eq_ce_with_hypothesis using * by simp
  also have "\<dots> = -(\<Sum>obs\<in>t`OB`msgs. \<P>(t\<circ>OB) {obs} * ?Ht obs)"
    apply (subst SIGMA_image_vimage[symmetric, of "OB`msgs" t])
    apply (subst sum.reindex)
    apply (fastforce intro!: inj_onI)
    apply simp
    apply (subst sum.Sigma[symmetric, unfolded split_def])
    using finite_space apply fastforce
    using finite_space apply fastforce
    apply (safe intro!: sum.cong)
    using P_t_sum_P_O
    by (simp add: sum_divide_distrib[symmetric] field_simps **
                  sum_distrib_left[symmetric] sum_distrib_right[symmetric])
  also have "\<dots> = \<H>(fst | t\<circ>OB)"
    unfolding conditional_entropy_eq_ce_with_hypothesis
    by (simp add: comp_def image_image[symmetric])
  finally show ?thesis
    by (subst (1 2) mutual_information_eq_entropy_conditional_entropy) simp_all
qed

theorem "\<I>(fst ; OB) \<le> real (card observations) * log b (real n + 1)"
proof -
  have "\<I>(fst ; OB) = \<H>(fst) - \<H>(fst | t\<circ>OB)"
    unfolding ce_OB_eq_ce_t
    by (rule mutual_information_eq_entropy_conditional_entropy simple_function_finite)+
  also have "\<dots> = \<H>(t\<circ>OB) - \<H>(t\<circ>OB | fst)"
    unfolding entropy_chain_rule[symmetric, OF simple_function_finite simple_function_finite] algebra_simps
    by (subst entropy_commute) simp
  also have "\<dots> \<le> \<H>(t\<circ>OB)"
    using conditional_entropy_nonneg[of "t\<circ>OB" fst] by simp
  also have "\<dots> \<le> log b (real (card ((t\<circ>OB)`msgs)))"
    using entropy_le_card[of "t\<circ>OB", OF simple_distributedI[OF simple_function_finite _ refl]] by simp
  also have "\<dots> \<le> log b (real (n + 1)^card observations)"
    using card_T_bound not_empty
    by (auto intro!: log_mono simp: card_gt_0_iff of_nat_power [symmetric] simp del: of_nat_power of_nat_Suc)
  also have "\<dots> = real (card observations) * log b (real n + 1)"
    by (simp add: log_nat_power add.commute)
  finally show ?thesis  .
qed

end

end
