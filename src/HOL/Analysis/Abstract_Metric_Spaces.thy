section \<open>Abstract Metric Spaces\<close>

theory Abstract_Metric_Spaces
  imports Elementary_Metric_Spaces Abstract_Limits Abstract_Topological_Spaces
begin

(*Avoid a clash with the existing metric_space locale (from the type class)*)
locale Metric_space =
  fixes M :: "'a set" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes nonneg [simp]: "\<And>x y. 0 \<le> d x y"
  assumes commute: "\<And>x y. d x y = d y x"
  assumes zero [simp]: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d x y = 0 \<longleftrightarrow> x=y"
  assumes triangle: "\<And>x y z. \<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d x y + d y z"

text \<open>Link with the type class version\<close>
interpretation Met_TC: Metric_space UNIV dist
  by (simp add: dist_commute dist_triangle Metric_space.intro)

context Metric_space
begin

lemma subspace: "M' \<subseteq> M \<Longrightarrow> Metric_space M' d"
  by (simp add: commute in_mono Metric_space.intro triangle)

lemma abs_mdist [simp] : "\<bar>d x y\<bar> = d x y"
  by simp

lemma mdist_pos_less: "\<lbrakk>x \<noteq> y; x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> 0 < d x y"
  by (metis less_eq_real_def nonneg zero)

lemma mdist_zero [simp]: "x \<in> M \<Longrightarrow> d x x = 0"
  by simp

lemma mdist_pos_eq [simp]: "\<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> 0 < d x y \<longleftrightarrow> x \<noteq> y"
  using mdist_pos_less zero by fastforce

lemma triangle': "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d x y + d z y"
  by (simp add: commute triangle)

lemma triangle'': "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d y x + d y z"
  by (simp add: commute triangle)

lemma mdist_reverse_triangle: "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> \<bar>d x y - d y z\<bar> \<le> d x z"
  by (smt (verit) commute triangle)

text\<open> Open and closed balls                                                                \<close>

definition mball where "mball x r \<equiv> {y. x \<in> M \<and> y \<in> M \<and> d x y < r}"
definition mcball where "mcball x r \<equiv> {y. x \<in> M \<and> y \<in> M \<and> d x y \<le> r}"

lemma in_mball [simp]: "y \<in> mball x r \<longleftrightarrow> x \<in> M \<and> y \<in> M \<and> d x y < r"
  by (simp add: local.Metric_space_axioms Metric_space.mball_def)

lemma centre_in_mball_iff [iff]: "x \<in> mball x r \<longleftrightarrow> x \<in> M \<and> 0 < r"
  using in_mball mdist_zero by force

lemma mball_subset_mspace: "mball x r \<subseteq> M"
  by auto

lemma mball_eq_empty: "mball x r = {} \<longleftrightarrow> (x \<notin> M) \<or> r \<le> 0"
  by (smt (verit, best) Collect_empty_eq centre_in_mball_iff mball_def nonneg)

lemma mball_subset: "\<lbrakk>d x y + a \<le> b; y \<in> M\<rbrakk> \<Longrightarrow> mball x a \<subseteq> mball y b"
  by (smt (verit) commute in_mball subsetI triangle)

lemma disjoint_mball: "r + r' \<le> d x x' \<Longrightarrow> disjnt (mball x r) (mball x' r')"
  by (smt (verit) commute disjnt_iff in_mball triangle)

lemma mball_subset_concentric: "r \<le> s \<Longrightarrow> mball x r \<subseteq> mball x s"
  by auto

lemma in_mcball [simp]: "y \<in> mcball x r \<longleftrightarrow> x \<in> M \<and> y \<in> M \<and> d x y \<le> r"
  by (simp add: local.Metric_space_axioms Metric_space.mcball_def)

lemma centre_in_mcball_iff [iff]: "x \<in> mcball x r \<longleftrightarrow> x \<in> M \<and> 0 \<le> r"
  using mdist_zero by force

lemma mcball_eq_empty: "mcball x r = {} \<longleftrightarrow> (x \<notin> M) \<or> r < 0"
  by (smt (verit, best) Collect_empty_eq centre_in_mcball_iff empty_iff mcball_def nonneg)

lemma mcball_subset_mspace: "mcball x r \<subseteq> M"
  by auto

lemma mball_subset_mcball: "mball x r \<subseteq> mcball x r"
  by auto

lemma mcball_subset: "\<lbrakk>d x y + a \<le> b; y \<in> M\<rbrakk> \<Longrightarrow> mcball x a \<subseteq> mcball y b"
  by (smt (verit) in_mcball mdist_reverse_triangle subsetI)

lemma mcball_subset_concentric: "r \<le> s \<Longrightarrow> mcball x r \<subseteq> mcball x s"
  by force

lemma mcball_subset_mball: "\<lbrakk>d x y + a < b; y \<in> M\<rbrakk> \<Longrightarrow> mcball x a \<subseteq> mball y b"
  by (smt (verit) commute in_mball in_mcball subsetI triangle)

lemma mcball_subset_mball_concentric: "a < b \<Longrightarrow> mcball x a \<subseteq> mball x b"
  by force

end



subsection \<open>Metric topology                                                           \<close>

context Metric_space
begin

definition mopen where 
  "mopen U \<equiv> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U))"

definition mtopology :: "'a topology" where 
  "mtopology \<equiv> topology mopen"

lemma is_topology_metric_topology [iff]: "istopology mopen"
proof -
  have "\<And>S T. \<lbrakk>mopen S; mopen T\<rbrakk> \<Longrightarrow> mopen (S \<inter> T)"
    by (smt (verit, del_insts) Int_iff in_mball mopen_def subset_eq)
  moreover have "\<And>\<K>. (\<forall>K\<in>\<K>. mopen K) \<longrightarrow> mopen (\<Union>\<K>)"
    using mopen_def by fastforce
  ultimately show ?thesis
    by (simp add: istopology_def)
qed

lemma openin_mtopology: "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U))"
  by (simp add: mopen_def mtopology_def)

lemma topspace_mtopology [simp]: "topspace mtopology = M"
  by (meson order.refl mball_subset_mspace openin_mtopology openin_subset openin_topspace subset_antisym zero_less_one)

lemma subtopology_mspace [simp]: "subtopology mtopology M = mtopology"
  by (metis subtopology_topspace topspace_mtopology)

lemma open_in_mspace [iff]: "openin mtopology M"
  by (metis openin_topspace topspace_mtopology)

lemma closedin_mspace [iff]: "closedin mtopology M"
  by (metis closedin_topspace topspace_mtopology)

lemma openin_mball [iff]: "openin mtopology (mball x r)"
proof -
  have "\<And>y. \<lbrakk>x \<in> M; d x y < r\<rbrakk> \<Longrightarrow> \<exists>s>0. mball y s \<subseteq> mball x r"
    by (metis add_diff_cancel_left' add_diff_eq commute less_add_same_cancel1 mball_subset order_refl)
  then show ?thesis
    by (auto simp: openin_mtopology)
qed

lemma mcball_eq_cball [simp]: "Met_TC.mcball = cball"
  by force

lemma mball_eq_ball [simp]: "Met_TC.mball = ball"
  by force

lemma mopen_eq_open [simp]: "Met_TC.mopen = open"
  by (force simp: open_contains_ball Met_TC.mopen_def)

lemma limitin_iff_tendsto [iff]: "limitin Met_TC.mtopology \<sigma> x F = tendsto \<sigma> x F"
  by (simp add: Met_TC.mtopology_def)

lemma mtopology_is_euclideanreal [simp]: "Met_TC.mtopology = euclideanreal"
  by (simp add: Met_TC.mtopology_def)

(*
lemma metric_injective_image:
   "\<And>f m s.
        f ` s \<subseteq> M \<and>
        (\<forall>x y. x \<in> s \<and> y \<in> s \<and> f x = f y \<Longrightarrow> x = y)
        \<Longrightarrow> (mspace(metric(s,\<lambda>(x,y). d (f x) (f y))) = s) \<and>
            (d(metric(s,\<lambda>(x,y). d (f x) (f y))) =
             \<lambda>(x,y). d (f x) (f y))"
oops
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; INJECTIVE_ON_ALT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mspace; d; GSYM PAIR_EQ] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 metric_tybij); is_metric_space] THEN
  REWRITE_TAC[GSYM mspace; GSYM d] THEN
  ASM_SIMP_TAC[MDIST_POS_LE; MDIST_TRIANGLE; MDIST_0] THEN
  ASM_MESON_TAC[MDIST_SYM]);;
*)

lemma mtopology_base:
   "mtopology = topology(arbitrary union_of (\<lambda>U. \<exists>x \<in> M. \<exists>r>0. U = mball x r))"
proof -
  have "\<And>S. \<exists>x r. x \<in> M \<and> 0 < r \<and> S = mball x r \<Longrightarrow> openin mtopology S"
    using openin_mball by blast
  moreover have "\<And>U x. \<lbrakk>openin mtopology U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>B. (\<exists>x r. x \<in> M \<and> 0 < r \<and> B = mball x r) \<and> x \<in> B \<and> B \<subseteq> U"
    by (metis centre_in_mball_iff in_mono openin_mtopology)
  ultimately show ?thesis
    by (smt (verit) topology_base_unique)
qed

lemma closedin_metric:
   "closedin mtopology C \<longleftrightarrow> C \<subseteq> M \<and> (\<forall>x. x \<in> M - C \<longrightarrow> (\<exists>r>0. disjnt C (mball x r)))"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding closedin_def openin_mtopology
    by (metis Diff_disjoint disjnt_def disjnt_subset2 topspace_mtopology)
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding closedin_def openin_mtopology disjnt_def
    by (metis Diff_subset Diff_triv Int_Diff Int_commute inf.absorb_iff2 mball_subset_mspace topspace_mtopology)
qed

lemma closedin_mcball [iff]: "closedin mtopology (mcball x r)"
proof -
  have "\<exists>ra>0. disjnt (mcball x r) (mball y ra)" if "x \<notin> M" for y
    by (metis disjnt_empty1 gt_ex mcball_eq_empty that)
  moreover have "disjnt (mcball x r) (mball y (d x y - r))" if "y \<in> M" "d x y > r" for y
    using that disjnt_iff in_mball in_mcball mdist_reverse_triangle by force
  ultimately show ?thesis
    using closedin_metric mcball_subset_mspace by fastforce
qed

lemma mball_iff_mcball: "(\<exists>r>0. mball x r \<subseteq> U) = (\<exists>r>0. mcball x r \<subseteq> U)"
  by (meson dense mball_subset_mcball mcball_subset_mball_concentric order_trans)

lemma openin_mtopology_mcball:
  "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r. 0 < r \<and> mcball x r \<subseteq> U))"
  using mball_iff_mcball openin_mtopology by presburger

lemma metric_derived_set_of:
  "mtopology derived_set_of S = {x \<in> M. \<forall>r>0. \<exists>y\<in>S. y\<noteq>x \<and> y \<in> mball x r}" (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    unfolding openin_mtopology derived_set_of_def 
    by clarsimp (metis in_mball openin_mball openin_mtopology zero)
  show "?rhs \<subseteq> ?lhs"
    unfolding openin_mtopology derived_set_of_def 
    by clarify (metis subsetD topspace_mtopology)
qed

lemma metric_closure_of:
   "mtopology closure_of S = {x \<in> M. \<forall>r>0. \<exists>y \<in> S. y \<in> mball x r}"
proof -
  have "\<And>x r. \<lbrakk>0 < r; x \<in> mtopology closure_of S\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. y \<in> mball x r"
    by (metis centre_in_mball_iff in_closure_of openin_mball topspace_mtopology)
  moreover have "\<And>x T. \<lbrakk>x \<in> M; \<forall>r>0. \<exists>y\<in>S. y \<in> mball x r\<rbrakk> \<Longrightarrow> x \<in> mtopology closure_of S"
    by (smt (verit) in_closure_of in_mball openin_mtopology subsetD topspace_mtopology)
  ultimately show ?thesis
    by (auto simp: in_closure_of)
qed

lemma metric_closure_of_alt:
  "mtopology closure_of S = {x \<in> M. \<forall>r>0. \<exists>y \<in> S. y \<in> mcball x r}"
proof -
  have "\<And>x r. \<lbrakk>\<forall>r>0. x \<in> M \<and> (\<exists>y\<in>S. y \<in> mcball x r); 0 < r\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. y \<in> M \<and> d x y < r"
    by (meson dense in_mcball le_less_trans)
  then show ?thesis
    by (fastforce simp: metric_closure_of in_closure_of)
qed

lemma metric_interior_of:
   "mtopology interior_of S = {x \<in> M. \<exists>\<epsilon>>0. mball x \<epsilon> \<subseteq> S}" (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using interior_of_maximal_eq openin_mtopology by fastforce
  show "?rhs \<subseteq> ?lhs"
    using interior_of_def openin_mball by fastforce
qed

lemma metric_interior_of_alt:
   "mtopology interior_of S = {x \<in> M. \<exists>\<epsilon>>0. mcball x \<epsilon> \<subseteq> S}"
  by (fastforce simp: mball_iff_mcball metric_interior_of)

lemma in_interior_of_mball:
   "x \<in> mtopology interior_of S \<longleftrightarrow> x \<in> M \<and> (\<exists>\<epsilon>>0. mball x \<epsilon> \<subseteq> S)"
  using metric_interior_of by force

lemma in_interior_of_mcball:
   "x \<in> mtopology interior_of S \<longleftrightarrow> x \<in> M \<and> (\<exists>\<epsilon>>0. mcball x \<epsilon> \<subseteq> S)"
  using metric_interior_of_alt by force

lemma Hausdorff_space_mtopology: "Hausdorff_space mtopology"
  unfolding Hausdorff_space_def
proof clarify
  fix x y
  assume x: "x \<in> topspace mtopology" and y: "y \<in> topspace mtopology" and "x \<noteq> y"
  then have gt0: "d x y / 2 > 0"
    by auto
  have "disjnt (mball x (d x y / 2)) (mball y (d x y / 2))"
    by (simp add: disjoint_mball)
  then show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
    by (metis centre_in_mball_iff gt0 openin_mball topspace_mtopology x y)
qed



subsection\<open>Bounded sets\<close>

definition mbounded where "mbounded S \<longleftrightarrow> (\<exists>x B. S \<subseteq> mcball x B)"

lemma mbounded_pos: "mbounded S \<longleftrightarrow> (\<exists>x B. 0 < B \<and> S \<subseteq> mcball x B)"
proof -
  have "\<exists>x' r'. 0 < r' \<and> S \<subseteq> mcball x' r'" if "S \<subseteq> mcball x r" for x r
    by (metis gt_ex less_eq_real_def linorder_not_le mcball_subset_concentric order_trans that)
  then show ?thesis
    by (auto simp: mbounded_def)
qed

lemma mbounded_alt:
  "mbounded S \<longleftrightarrow> S \<subseteq> M \<and> (\<exists>B. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> B)"
proof -
  have "\<And>x B. S \<subseteq> mcball x B \<Longrightarrow> \<forall>x\<in>S. \<forall>y\<in>S. d x y \<le> 2 * B"
    by (smt (verit, best) commute in_mcball subsetD triangle)
  then show ?thesis
    apply (auto simp: mbounded_def subset_iff)
     apply blast+
    done
qed


lemma mbounded_alt_pos:
  "mbounded S \<longleftrightarrow> S \<subseteq> M \<and> (\<exists>B>0. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> B)"
  by (smt (verit, del_insts) gt_ex mbounded_alt)

lemma mbounded_subset: "\<lbrakk>mbounded T; S \<subseteq> T\<rbrakk> \<Longrightarrow> mbounded S"
  by (meson mbounded_def order_trans)

lemma mbounded_subset_mspace: "mbounded S \<Longrightarrow> S \<subseteq> M"
  by (simp add: mbounded_alt)

lemma mbounded:
   "mbounded S \<longleftrightarrow> S = {} \<or> (\<forall>x \<in> S. x \<in> M) \<and> (\<exists>y B. y \<in> M \<and> (\<forall>x \<in> S. d y x \<le> B))"
  by (meson all_not_in_conv in_mcball mbounded_def subset_iff)

lemma mbounded_empty [iff]: "mbounded {}"
  by (simp add: mbounded)

lemma mbounded_mcball: "mbounded (mcball x r)"
  using mbounded_def by auto

lemma mbounded_mball [iff]: "mbounded (mball x r)"
  by (meson mball_subset_mcball mbounded_def)

lemma mbounded_insert: "mbounded (insert a S) \<longleftrightarrow> a \<in> M \<and> mbounded S"
proof -
  have "\<And>y B. \<lbrakk>y \<in> M; \<forall>x\<in>S. d y x \<le> B\<rbrakk>
           \<Longrightarrow> \<exists>y. y \<in> M \<and> (\<exists>B \<ge> d y a. \<forall>x\<in>S. d y x \<le> B)"
    by (metis order.trans nle_le)
  then show ?thesis
    by (auto simp: mbounded)
qed

lemma mbounded_Int: "mbounded S \<Longrightarrow> mbounded (S \<inter> T)"
  by (meson inf_le1 mbounded_subset)

lemma mbounded_Un: "mbounded (S \<union> T) \<longleftrightarrow> mbounded S \<and> mbounded T" (is "?lhs=?rhs")
proof
  assume R: ?rhs
  show ?lhs
  proof (cases "S={} \<or> T={}")
    case True then show ?thesis
      using R by auto
  next
    case False
    obtain x y B C where "S \<subseteq> mcball x B" "T \<subseteq> mcball y C" "B > 0" "C > 0" "x \<in> M" "y \<in> M"
      using R mbounded_pos
      by (metis False mcball_eq_empty subset_empty)
    then have "S \<union> T \<subseteq> mcball x (B + C + d x y)"
      by (smt (verit) commute dual_order.trans le_supI mcball_subset mdist_pos_eq)
    then show ?thesis
      using mbounded_def by blast
  qed
next
  show "?lhs \<Longrightarrow> ?rhs"
    using mbounded_def by auto
qed

lemma mbounded_Union:
  "\<lbrakk>finite \<F>; \<And>X. X \<in> \<F> \<Longrightarrow> mbounded X\<rbrakk> \<Longrightarrow> mbounded (\<Union>\<F>)"
  by (induction \<F> rule: finite_induct) (auto simp: mbounded_Un)

lemma mbounded_closure_of:
   "mbounded S \<Longrightarrow> mbounded (mtopology closure_of S)"
  by (meson closedin_mcball closure_of_minimal mbounded_def)

lemma mbounded_closure_of_eq:
   "S \<subseteq> M \<Longrightarrow> (mbounded (mtopology closure_of S) \<longleftrightarrow> mbounded S)"
  by (metis closure_of_subset mbounded_closure_of mbounded_subset topspace_mtopology)


lemma maxdist_thm:
  assumes "mbounded S"
      and "x \<in> S"
      and "y \<in> S"
    shows  "d x y = (SUP z\<in>S. \<bar>d x z - d z y\<bar>)"
proof -
  have "\<bar>d x z - d z y\<bar> \<le> d x y" if "z \<in> S" for z
    by (metis all_not_in_conv assms mbounded mdist_reverse_triangle that) 
  moreover have "d x y \<le> r"
    if "\<And>z. z \<in> S \<Longrightarrow> \<bar>d x z - d z y\<bar> \<le> r" for r :: real
    using that assms mbounded_subset_mspace mdist_zero by fastforce
  ultimately show ?thesis
    by (intro cSup_eq [symmetric]) auto
qed


lemma metric_eq_thm: "\<lbrakk>S \<subseteq> M; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> (x = y) = (\<forall>z\<in>S. d x z = d y z)"
  by (metis commute  subset_iff zero)

lemma compactin_imp_mbounded:
  assumes "compactin mtopology S"
  shows "mbounded S"
proof -
  have "S \<subseteq> M"
    and com: "\<And>\<U>. \<lbrakk>\<forall>U\<in>\<U>. openin mtopology U; S \<subseteq> \<Union>\<U>\<rbrakk> \<Longrightarrow> \<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>"
    using assms by (auto simp: compactin_def mbounded_def)
  show ?thesis
  proof (cases "S = {}")
    case False
    with \<open>S \<subseteq> M\<close> obtain a where "a \<in> S" "a \<in> M"
      by blast
    with \<open>S \<subseteq> M\<close> gt_ex have "S \<subseteq> \<Union>(range (mball a))"
      by force
    moreover have "\<forall>U \<in> range (mball a). openin mtopology U"
      by (simp add: openin_mball)
    ultimately obtain \<F> where "finite \<F>" "\<F> \<subseteq> range (mball a)" "S \<subseteq> \<Union>\<F>"
      by (meson com)
  then show ?thesis
      using mbounded_Union mbounded_subset by fastforce
  qed auto
qed

end


subsection\<open>Subspace of a metric space\<close>

locale submetric = Metric_space + 
  fixes A
  assumes subset: "A \<subseteq> M"

sublocale submetric \<subseteq> sub: Metric_space A d
  by (simp add: subset subspace)

context submetric
begin 

lemma mball_submetric_eq: "sub.mball a r = (if a \<in> A then A \<inter> mball a r else {})"
and mcball_submetric_eq: "sub.mcball a r = (if a \<in> A then A \<inter> mcball a r else {})"
  using subset by force+

lemma mtopology_submetric: "sub.mtopology = subtopology mtopology A"
  unfolding topology_eq
proof (intro allI iffI)
  fix S
  assume "openin sub.mtopology S"
  then have "\<exists>T. openin (subtopology mtopology A) T \<and> x \<in> T \<and> T \<subseteq> S" if "x \<in> S" for x
    by (metis mball_submetric_eq openin_mball openin_subtopology_Int2 sub.centre_in_mball_iff sub.openin_mtopology subsetD that)
  then show "openin (subtopology mtopology A) S"
    by (meson openin_subopen)
next
  fix S
  assume "openin (subtopology mtopology A) S"
  then obtain T where "openin mtopology T" "S = T \<inter> A"
    by (meson openin_subtopology)
  then have "mopen T"
    by (simp add: mopen_def openin_mtopology)
  then have "sub.mopen (T \<inter> A)"
    unfolding sub.mopen_def mopen_def
    by (metis inf.coboundedI2 mball_submetric_eq Int_iff \<open>S = T \<inter> A\<close> inf.bounded_iff subsetI)
  then show "openin sub.mtopology S"
    using \<open>S = T \<inter> A\<close> sub.mopen_def sub.openin_mtopology by force
qed

lemma mbounded_submetric: "sub.mbounded T \<longleftrightarrow> mbounded T \<and> T \<subseteq> A"
  by (meson mbounded_alt sub.mbounded_alt subset subset_trans)

end

lemma (in Metric_space) submetric_empty [iff]: "submetric M d {}"
  by (simp add: Metric_space_axioms submetric.intro submetric_axioms_def)


subsection\<open>The discrete metric\<close>

locale discrete_metric =
  fixes M :: "'a set"

definition (in discrete_metric) dd :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  where "dd \<equiv> \<lambda>x y::'a. if x=y then 0 else 1"

lemma metric_M_dd: "Metric_space M discrete_metric.dd"
  by (simp add: discrete_metric.dd_def Metric_space.intro)

sublocale discrete_metric \<subseteq> disc: Metric_space M dd
  by (simp add: metric_M_dd)


lemma (in discrete_metric) mopen_singleton:
  assumes "x \<in> M" shows "disc.mopen {x}"
proof -
  have "disc.mball x (1/2) \<subseteq> {x}"
    by (smt (verit) dd_def disc.in_mball less_divide_eq_1_pos singleton_iff subsetI)
  with assms show ?thesis
    using disc.mopen_def half_gt_zero_iff zero_less_one by blast
qed

lemma (in discrete_metric) mtopology_discrete_metric:
   "disc.mtopology = discrete_topology M"
proof -
  have "\<And>x. x \<in> M \<Longrightarrow> openin disc.mtopology {x}"
    by (simp add: disc.mtopology_def mopen_singleton)
  then show ?thesis
    by (metis disc.topspace_mtopology discrete_topology_unique)
qed

lemma (in discrete_metric) discrete_ultrametric:
   "dd x z \<le> max (dd x y) (dd y z)"
  by (simp add: dd_def)


lemma (in discrete_metric) dd_le1: "dd x y \<le> 1"
  by (simp add: dd_def)

lemma (in discrete_metric) mbounded_discrete_metric: "disc.mbounded S \<longleftrightarrow> S \<subseteq> M"
  by (meson dd_le1 disc.mbounded_alt)



subsection\<open>Metrizable spaces\<close>

definition metrizable_space where
  "metrizable_space X \<equiv> \<exists>M d. Metric_space M d \<and> X = Metric_space.mtopology M d"

lemma (in Metric_space) metrizable_space_mtopology: "metrizable_space mtopology"
  using local.Metric_space_axioms metrizable_space_def by blast

lemma openin_mtopology_eq_open [simp]: "openin Met_TC.mtopology = open"
  by (simp add: Met_TC.mtopology_def)

lemma closedin_mtopology_eq_closed [simp]: "closedin Met_TC.mtopology = closed"
proof -
  have "(euclidean::'a topology) = Met_TC.mtopology"
    by (simp add: Met_TC.mtopology_def)
  then show ?thesis
    using closed_closedin by fastforce
qed

lemma compactin_mtopology_eq_compact [simp]: "compactin Met_TC.mtopology = compact"
  by (simp add: compactin_def compact_eq_Heine_Borel fun_eq_iff) meson

lemma metrizable_space_discrete_topology:
   "metrizable_space(discrete_topology U)"
  by (metis discrete_metric.mtopology_discrete_metric metric_M_dd metrizable_space_def)

lemma metrizable_space_subtopology:
  assumes "metrizable_space X"
  shows "metrizable_space(subtopology X S)"
proof -
  obtain M d where "Metric_space M d" and X: "X = Metric_space.mtopology M d"
    using assms metrizable_space_def by blast
  then interpret submetric M d "M \<inter> S"
    by (simp add: submetric.intro submetric_axioms_def)
  show ?thesis
    unfolding metrizable_space_def
    by (metis X mtopology_submetric sub.Metric_space_axioms subtopology_restrict topspace_mtopology)
qed

lemma homeomorphic_metrizable_space_aux:
  assumes "X homeomorphic_space Y" "metrizable_space X"
  shows "metrizable_space Y"
proof -
  obtain M d where "Metric_space M d" and X: "X = Metric_space.mtopology M d"
    using assms by (auto simp: metrizable_space_def)
  then interpret m: Metric_space M d 
    by simp
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> M. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms X homeomorphic_maps_map homeomorphic_space_def by fastforce
  define d' where "d' x y \<equiv> d (g x) (g y)" for x y
  interpret m': Metric_space "topspace Y" "d'"
    unfolding d'_def
  proof
    show "(d (g x) (g y) = 0) = (x = y)" if "x \<in> topspace Y" "y \<in> topspace Y" for x y
      by (metis fg X hmg homeomorphic_imp_surjective_map imageI m.topspace_mtopology m.zero that)
    show "d (g x) (g z) \<le> d (g x) (g y) + d (g y) (g z)"
      if "x \<in> topspace Y" and "y \<in> topspace Y" and "z \<in> topspace Y" for x y z
      by (metis X that hmg homeomorphic_eq_everything_map imageI m.topspace_mtopology m.triangle)
  qed (auto simp: m.nonneg m.commute)
  have "Y = Metric_space.mtopology (topspace Y) d'"
    unfolding topology_eq
  proof (intro allI)
    fix S
    have "openin m'.mtopology S" if S: "S \<subseteq> topspace Y" and "openin X (g ` S)"
      unfolding m'.openin_mtopology
    proof (intro conjI that strip)
      fix y
      assume "y \<in> S"
      then obtain r where "r>0" and r: "m.mball (g y) r \<subseteq> g ` S" 
        using X \<open>openin X (g ` S)\<close> m.openin_mtopology using \<open>y \<in> S\<close> by auto
      then have "g ` m'.mball y r \<subseteq> m.mball (g y) r"
        using X d'_def hmg homeomorphic_imp_surjective_map by fastforce
      with S fg have "m'.mball y r \<subseteq> S"
        by (smt (verit, del_insts) image_iff m'.in_mball r subset_iff)
      then show "\<exists>r>0. m'.mball y r \<subseteq> S"
        using \<open>0 < r\<close> by blast 
    qed
    moreover have "openin X (g ` S)" if ope': "openin m'.mtopology S"
    proof -
      have "\<exists>r>0. m.mball (g y) r \<subseteq> g ` S" if "y \<in> S" for y
      proof -
        have y: "y \<in> topspace Y"
          using m'.openin_mtopology ope' that by blast
        obtain r where "r > 0" and r: "m'.mball y r \<subseteq> S"
          using ope' by (meson \<open>y \<in> S\<close> m'.openin_mtopology)
        moreover have "\<And>x. \<lbrakk>x \<in> M; d (g y) x < r\<rbrakk> \<Longrightarrow> \<exists>u. u \<in> topspace Y \<and> d' y u < r \<and> x = g u"
          using fg X d'_def hmf homeomorphic_imp_surjective_map by fastforce
        ultimately have "m.mball (g y) r \<subseteq> g ` m'.mball y r"
          using y by (force simp: m'.openin_mtopology)
        then show ?thesis
          using \<open>0 < r\<close> r by blast
      qed
      then show ?thesis
        using X hmg homeomorphic_imp_surjective_map m.openin_mtopology ope' openin_subset by fastforce
    qed
    ultimately have "(S \<subseteq> topspace Y \<and> openin X (g ` S)) = openin m'.mtopology S"
      using m'.topspace_mtopology openin_subset by blast
    then show "openin Y S = openin m'.mtopology S"
      by (simp add: m'.mopen_def homeomorphic_map_openness_eq [OF hmg])
  qed
  then show ?thesis
    using m'.metrizable_space_mtopology by force
qed

lemma homeomorphic_metrizable_space:
  assumes "X homeomorphic_space Y"
  shows "metrizable_space X \<longleftrightarrow> metrizable_space Y"
  using assms homeomorphic_metrizable_space_aux homeomorphic_space_sym by metis

lemma metrizable_space_retraction_map_image:
   "retraction_map X Y r \<and> metrizable_space X
        \<Longrightarrow> metrizable_space Y"
  using hereditary_imp_retractive_property metrizable_space_subtopology homeomorphic_metrizable_space
  by blast


lemma metrizable_imp_Hausdorff_space:
   "metrizable_space X \<Longrightarrow> Hausdorff_space X"
  by (metis Metric_space.Hausdorff_space_mtopology metrizable_space_def)

(**
lemma metrizable_imp_kc_space:
   "metrizable_space X \<Longrightarrow> kc_space X"
oops
  MESON_TAC[METRIZABLE_IMP_HAUSDORFF_SPACE; HAUSDORFF_IMP_KC_SPACE]);;

lemma kc_space_mtopology:
   "kc_space mtopology"
oops
  REWRITE_TAC[GSYM FORALL_METRIZABLE_SPACE; METRIZABLE_IMP_KC_SPACE]);;
**)

lemma metrizable_imp_t1_space:
   "metrizable_space X \<Longrightarrow> t1_space X"
  by (simp add: Hausdorff_imp_t1_space metrizable_imp_Hausdorff_space)

lemma closed_imp_gdelta_in:
  assumes X: "metrizable_space X" and S: "closedin X S"
  shows "gdelta_in X S"
proof -
  obtain M d where "Metric_space M d" and Xeq: "X = Metric_space.mtopology M d"
    using X metrizable_space_def by blast
  then interpret M: Metric_space M d
    by blast
  have "S \<subseteq> M"
    using M.closedin_metric \<open>X = M.mtopology\<close> S by blast
  show ?thesis
  proof (cases "S = {}")
    case True
    then show ?thesis
      by simp
  next
    case False
    have "\<exists>y\<in>S. d x y < inverse (1 + real n)" if "x \<in> S" for x n
      using \<open>S \<subseteq> M\<close> M.mdist_zero [of x] that by force
    moreover
    have "x \<in> S" if "x \<in> M" and \<section>: "\<And>n. \<exists>y\<in>S. d x y < inverse(Suc n)" for x
    proof -
      have *: "\<exists>y\<in>S. d x y < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
        by (metis \<section> that not0_implies_Suc order_less_le order_less_le_trans real_arch_inverse)
      have "closedin M.mtopology S"
        using S by (simp add: Xeq)
      then show ?thesis
        apply (simp add: M.closedin_metric)
        by (metis * \<open>x \<in> M\<close> M.in_mball disjnt_insert1 insert_absorb subsetD)
    qed
    ultimately have Seq: "S = \<Inter>(range (\<lambda>n. {x\<in>M. \<exists>y\<in>S. d x y < inverse(Suc n)}))"
      using \<open>S \<subseteq> M\<close> by force
    have "openin M.mtopology {xa \<in> M. \<exists>y\<in>S. d xa y < inverse (1 + real n)}" for n
    proof (clarsimp simp: M.openin_mtopology)
      fix x y
      assume "x \<in> M" "y \<in> S" and dxy: "d x y < inverse (1 + real n)"
      then have "\<And>z. \<lbrakk>z \<in> M; d x z < inverse (1 + real n) - d x y\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. d z y < inverse (1 + real n)"
        by (smt (verit) M.commute M.triangle \<open>S \<subseteq> M\<close> in_mono)
      with dxy show "\<exists>r>0. M.mball x r \<subseteq> {z \<in> M. \<exists>y\<in>S. d z y < inverse (1 + real n)}"
        by (rule_tac x="inverse(Suc n) - d x y" in exI) auto
    qed
    then show ?thesis
      apply (subst Seq)
      apply (force simp: Xeq intro: gdelta_in_Inter open_imp_gdelta_in)
      done
  qed
qed

lemma open_imp_fsigma_in:
   "\<lbrakk>metrizable_space X; openin X S\<rbrakk> \<Longrightarrow> fsigma_in X S"
  by (meson closed_imp_gdelta_in fsigma_in_gdelta_in openin_closedin openin_subset)

(*NEEDS first_countable
lemma first_countable_mtopology:
   "first_countable mtopology"
oops
  GEN_TAC THEN REWRITE_TAC[first_countable; TOPSPACE_MTOPOLOGY] THEN
  X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  EXISTS_TAC `{ mball m (x::A,r) | rational r \<and> 0 < r}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; OPEN_IN_MBALL; EXISTS_IN_GSPEC] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{f x | S x \<and> Q x} = f ` {x \<in> S. Q x}`] THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_RATIONAL; COUNTABLE_RESTRICT] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
  X_GEN_TAC `U::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::A`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r::real` THEN STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC \<circ> SPEC `r::real` \<circ> MATCH_MP RATIONAL_APPROXIMATION_BELOW) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q::real` THEN
  REWRITE_TAC[REAL_SUB_REFL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CENTRE_IN_MBALL] THEN
  TRANS_TAC SUBSET_TRANS `mball m (x::A,r)` THEN
  ASM_SIMP_TAC[MBALL_SUBSET_CONCENTRIC; REAL_LT_IMP_LE]);;

lemma metrizable_imp_first_countable:
   "metrizable_space X \<Longrightarrow> first_countable X"
oops
  REWRITE_TAC[FORALL_METRIZABLE_SPACE; FIRST_COUNTABLE_MTOPOLOGY]);;
*)

lemma mball_eq_ball [simp]: "Met_TC.mball = ball"
  by force

lemma mopen_eq_open [simp]: "Met_TC.mopen = open"
  by (force simp: open_contains_ball Met_TC.mopen_def)

lemma metrizable_space_euclidean:
  "metrizable_space (euclidean :: 'a::metric_space topology)"
  unfolding metrizable_space_def
  by (metis Met_TC.Metric_space_axioms Met_TC.mtopology_def mopen_eq_open)

lemma (in Metric_space) regular_space_mtopology:
   "regular_space mtopology"
unfolding regular_space_def
proof clarify
  fix C a
  assume C: "closedin mtopology C" and a: "a \<in> topspace mtopology" and "a \<notin> C"
  have "openin mtopology (topspace mtopology - C)"
    by (simp add: C openin_diff)
  then obtain r where "r>0" and r: "mball a r \<subseteq> topspace mtopology - C"
    unfolding openin_mtopology using \<open>a \<notin> C\<close> a by auto
  show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
  proof (intro exI conjI)
    show "a \<in> mball a (r/2)"
      using \<open>0 < r\<close> a by force
    show "C \<subseteq> topspace mtopology - mcball a (r/2)"
      using C \<open>0 < r\<close> r by (fastforce simp: closedin_metric)
  qed (auto simp: openin_mball closedin_mcball openin_diff disjnt_iff)
qed

lemma metrizable_imp_regular_space:
   "metrizable_space X \<Longrightarrow> regular_space X"
  by (metis Metric_space.regular_space_mtopology metrizable_space_def)

lemma regular_space_euclidean:
 "regular_space (euclidean :: 'a::metric_space topology)"
  by (simp add: metrizable_imp_regular_space metrizable_space_euclidean)


subsection\<open>Limits at a point in a topological space\<close>

lemma (in Metric_space) eventually_atin_metric:
   "eventually P (atin mtopology a) \<longleftrightarrow>
        (a \<in> M \<longrightarrow> (\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x))"  (is "?lhs=?rhs")
proof (cases "a \<in> M")
  case True
  show ?thesis
  proof
    assume L: ?lhs 
    with True obtain U where "openin mtopology U" "a \<in> U" and U: "\<forall>x\<in>U - {a}. P x"
      by (auto simp: eventually_atin)
    then obtain r where "r>0" and "mball a r \<subseteq> U"
      by (meson openin_mtopology)
    with U show ?rhs
      by (smt (verit, ccfv_SIG) commute in_mball insert_Diff_single insert_iff subset_iff)
  next
    assume ?rhs 
    then obtain \<delta> where "\<delta>>0" and \<delta>: "\<forall>x. x \<in> M \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x"
      using True by blast
    then have "\<forall>x \<in> mball a \<delta> - {a}. P x"
      by (simp add: commute)
    then show ?lhs
      unfolding eventually_atin openin_mtopology
      by (metis True \<open>0 < \<delta>\<close> centre_in_mball_iff openin_mball openin_mtopology) 
  qed
qed auto

subsection \<open>Normal spaces and metric spaces\<close>

lemma (in Metric_space) normal_space_mtopology:
   "normal_space mtopology"
  unfolding normal_space_def
proof clarify
  fix S T
  assume "closedin mtopology S"
  then have "\<And>x. x \<in> M - S \<Longrightarrow> (\<exists>r>0. mball x r \<subseteq> M - S)"
    by (simp add: closedin_def openin_mtopology)
  then obtain \<delta> where d0: "\<And>x. x \<in> M - S \<Longrightarrow> \<delta> x > 0 \<and> mball x (\<delta> x) \<subseteq> M - S"
    by metis
  assume "closedin mtopology T"
  then have "\<And>x. x \<in> M - T \<Longrightarrow> (\<exists>r>0. mball x r \<subseteq> M - T)"
    by (simp add: closedin_def openin_mtopology)
  then obtain \<epsilon> where e: "\<And>x. x \<in> M - T \<Longrightarrow> \<epsilon> x > 0 \<and> mball x (\<epsilon> x) \<subseteq> M - T"
    by metis
  assume "disjnt S T"
  have "S \<subseteq> M" "T \<subseteq> M"
    using \<open>closedin mtopology S\<close> \<open>closedin mtopology T\<close> closedin_metric by blast+
  have \<delta>: "\<And>x. x \<in> T \<Longrightarrow> \<delta> x > 0 \<and> mball x (\<delta> x) \<subseteq> M - S"
    by (meson DiffI \<open>T \<subseteq> M\<close> \<open>disjnt S T\<close> d0 disjnt_iff subsetD)
  have \<epsilon>: "\<And>x. x \<in> S \<Longrightarrow> \<epsilon> x > 0 \<and> mball x (\<epsilon> x) \<subseteq> M - T"
    by (meson Diff_iff \<open>S \<subseteq> M\<close> \<open>disjnt S T\<close> disjnt_iff e subsetD)
  show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  proof (intro exI conjI)
    show "openin mtopology (\<Union>x\<in>S. mball x (\<epsilon> x / 2))" "openin mtopology (\<Union>x\<in>T. mball x (\<delta> x / 2))"
      by force+
    show "S \<subseteq> (\<Union>x\<in>S. mball x (\<epsilon> x / 2))"
      using \<epsilon> \<open>S \<subseteq> M\<close> by force
    show "T \<subseteq> (\<Union>x\<in>T. mball x (\<delta> x / 2))"
      using \<delta> \<open>T \<subseteq> M\<close> by force
    show "disjnt (\<Union>x\<in>S. mball x (\<epsilon> x / 2)) (\<Union>x\<in>T. mball x (\<delta> x / 2))"
      using \<epsilon> \<delta> 
      apply (clarsimp simp: disjnt_iff subset_iff)
      by (smt (verit, ccfv_SIG) field_sum_of_halves triangle')
  qed 
qed

lemma metrizable_imp_normal_space:
   "metrizable_space X \<Longrightarrow> normal_space X"
  by (metis Metric_space.normal_space_mtopology metrizable_space_def)

subsection\<open>Topological limitin in metric spaces\<close>


lemma (in Metric_space) limitin_mspace:
   "limitin mtopology f l F \<Longrightarrow> l \<in> M"
  using limitin_topspace by fastforce

lemma (in Metric_space) limitin_metric_unique:
   "\<lbrakk>limitin mtopology f l1 F; limitin mtopology f l2 F; F \<noteq> bot\<rbrakk> \<Longrightarrow> l1 = l2"
  by (meson Hausdorff_space_mtopology limitin_Hausdorff_unique)

lemma (in Metric_space) limitin_metric:
   "limitin mtopology f l F \<longleftrightarrow> l \<in> M \<and> (\<forall>\<epsilon>>0. eventually (\<lambda>x. f x \<in> M \<and> d (f x) l < \<epsilon>) F)"  
   (is "?lhs=?rhs")
proof
  assume L: ?lhs
  show ?rhs
    unfolding limitin_def
  proof (intro conjI strip)
    show "l \<in> M"
      using L limitin_mspace by blast
    fix \<epsilon>::real
    assume "\<epsilon>>0"
    then have "\<forall>\<^sub>F x in F. f x \<in> mball l \<epsilon>"
      using L openin_mball by (fastforce simp: limitin_def)
    then show "\<forall>\<^sub>F x in F. f x \<in> M \<and> d (f x) l < \<epsilon>"
      using commute eventually_mono by fastforce
  qed
next
  assume R: ?rhs 
  then show ?lhs
    by (force simp: limitin_def commute openin_mtopology subset_eq elim: eventually_mono)
qed

lemma (in Metric_space) limit_metric_sequentially:
   "limitin mtopology f l sequentially \<longleftrightarrow>
     l \<in> M \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. f n \<in> M \<and> d (f n) l < \<epsilon>)"
  by (auto simp: limitin_metric eventually_sequentially)

lemma (in submetric) limitin_submetric_iff:
   "limitin sub.mtopology f l F \<longleftrightarrow>
     l \<in> A \<and> eventually (\<lambda>x. f x \<in> A) F \<and> limitin mtopology f l F" (is "?lhs=?rhs")
  by (simp add: limitin_subtopology mtopology_submetric)

lemma (in Metric_space) metric_closedin_iff_sequentially_closed:
   "closedin mtopology S \<longleftrightarrow>
    S \<subseteq> M \<and> (\<forall>\<sigma> l. range \<sigma> \<subseteq> S \<and> limitin mtopology \<sigma> l sequentially \<longrightarrow> l \<in> S)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (force simp: closedin_metric limitin_closedin range_subsetD)
next
  assume R: ?rhs
  show ?lhs
    unfolding closedin_metric
  proof (intro conjI strip)
    show "S \<subseteq> M"
      using R by blast
    fix x
    assume "x \<in> M - S"
    have False if "\<forall>r>0. \<exists>y. y \<in> M \<and> y \<in> S \<and> d x y < r"
    proof -
      have "\<forall>n. \<exists>y. y \<in> M \<and> y \<in> S \<and> d x y < inverse(Suc n)"
        using that by auto
      then obtain \<sigma> where \<sigma>: "\<And>n. \<sigma> n \<in> M \<and> \<sigma> n \<in> S \<and> d x (\<sigma> n) < inverse(Suc n)"
        by metis
      then have "range \<sigma> \<subseteq> M"
        by blast
      have "\<exists>N. \<forall>n\<ge>N. d x (\<sigma> n) < \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        have "real (Suc (nat \<lceil>inverse \<epsilon>\<rceil>)) \<ge> inverse \<epsilon>"
          by linarith
        then have "\<forall>n \<ge> nat \<lceil>inverse \<epsilon>\<rceil>. d x (\<sigma> n) < \<epsilon>"
          by (metis \<sigma> inverse_inverse_eq inverse_le_imp_le nat_ceiling_le_eq nle_le not_less_eq_eq order.strict_trans2 that)
        then show ?thesis ..
      qed
      with \<sigma> have "limitin mtopology \<sigma> x sequentially"
        using \<open>x \<in> M - S\<close> commute limit_metric_sequentially by auto
      then show ?thesis
        by (metis R DiffD2 \<sigma> image_subset_iff \<open>x \<in> M - S\<close>)
    qed
    then show "\<exists>r>0. disjnt S (mball x r)"
      by (meson disjnt_iff in_mball)
  qed
qed

lemma (in Metric_space) limit_atin_metric:
   "limitin X f y (atin mtopology x) \<longleftrightarrow>
      y \<in> topspace X \<and>
      (x \<in> M
       \<longrightarrow> (\<forall>V. openin X V \<and> y \<in> V
               \<longrightarrow> (\<exists>\<delta>>0.  \<forall>x'. x' \<in> M \<and> 0 < d x' x \<and> d x' x < \<delta> \<longrightarrow> f x' \<in> V)))"
  by (force simp: limitin_def eventually_atin_metric)

lemma (in Metric_space) limitin_metric_dist_null:
   "limitin mtopology f l F \<longleftrightarrow> l \<in> M \<and> eventually (\<lambda>x. f x \<in> M) F \<and> ((\<lambda>x. d (f x) l) \<longlongrightarrow> 0) F"
  by (simp add: limitin_metric tendsto_iff eventually_conj_iff all_conj_distrib imp_conjR gt_ex)


subsection\<open>Cauchy sequences and complete metric spaces\<close>

context Metric_space
begin

definition MCauchy :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "MCauchy \<sigma> \<equiv> range \<sigma> \<subseteq> M \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>)"

definition mcomplete
  where "mcomplete \<equiv> (\<forall>\<sigma>. MCauchy \<sigma> \<longrightarrow> (\<exists>x. limitin mtopology \<sigma> x sequentially))"

lemma mcomplete_empty [iff]: "Metric_space.mcomplete {} d"
  by (simp add: Metric_space.MCauchy_def Metric_space.mcomplete_def subspace)

lemma MCauchy_imp_MCauchy_suffix: "MCauchy \<sigma> \<Longrightarrow> MCauchy (\<sigma> \<circ> (+)n)"
  unfolding MCauchy_def image_subset_iff comp_apply
  by (metis UNIV_I add.commute trans_le_add1) 

lemma mcomplete:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<sigma>. (\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M) \<and>
     (\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>) \<longrightarrow>
     (\<exists>x. limitin mtopology \<sigma> x sequentially))" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix \<sigma>
    assume "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M"
      and \<sigma>: "\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    then obtain N where "\<And>n. n\<ge>N \<Longrightarrow> \<sigma> n \<in> M"
      by (auto simp: eventually_sequentially)
    with \<sigma> have "MCauchy (\<sigma> \<circ> (+)N)"
      unfolding MCauchy_def image_subset_iff comp_apply by (meson le_add1 trans_le_add2)
    then obtain x where "limitin mtopology (\<sigma> \<circ> (+)N) x sequentially"
      using L MCauchy_imp_MCauchy_suffix mcomplete_def by blast
    then have "limitin mtopology \<sigma> x sequentially"
      unfolding o_def by (auto simp: add.commute limitin_sequentially_offset_rev)
    then show "\<exists>x. limitin mtopology \<sigma> x sequentially" ..
  qed
qed (simp add: mcomplete_def MCauchy_def image_subset_iff)

lemma mcomplete_empty_mspace: "M = {} \<Longrightarrow> mcomplete"
  using MCauchy_def mcomplete_def by blast

lemma MCauchy_const [simp]: "MCauchy (\<lambda>n. a) \<longleftrightarrow> a \<in> M"
  using MCauchy_def mdist_zero by auto

lemma convergent_imp_MCauchy:
  assumes "range \<sigma> \<subseteq> M" and lim: "limitin mtopology \<sigma> l sequentially"
  shows "MCauchy \<sigma>"
  unfolding MCauchy_def image_subset_iff
proof (intro conjI strip)
  fix \<epsilon>::real
  assume "\<epsilon> > 0"
  then have "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>/2"
    using half_gt_zero lim limitin_metric by blast
  then obtain N where "\<And>n. n\<ge>N \<Longrightarrow> \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>/2"
    by (force simp: eventually_sequentially)
  then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    by (smt (verit) Metric_space.limitin_mspace Metric_space.mdist_reverse_triangle Metric_space_axioms field_sum_of_halves lim)
qed (use assms in blast)


lemma mcomplete_alt:
   "mcomplete \<longleftrightarrow> (\<forall>\<sigma>. MCauchy \<sigma> \<longleftrightarrow> range \<sigma> \<subseteq> M \<and> (\<exists>x. limitin mtopology \<sigma> x sequentially))"
  using MCauchy_def convergent_imp_MCauchy mcomplete_def by blast

lemma MCauchy_subsequence:
  assumes "strict_mono r" "MCauchy \<sigma>"
  shows "MCauchy (\<sigma> \<circ> r)"
proof -
  have "d (\<sigma> (r n)) (\<sigma> (r n')) < \<epsilon>"
    if "N \<le> n" "N \<le> n'" "strict_mono r" "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    for \<epsilon> N n n'
    using that by (meson le_trans strict_mono_imp_increasing)
  moreover have "range (\<lambda>x. \<sigma> (r x)) \<subseteq> M"
    using MCauchy_def assms by blast
  ultimately show ?thesis
    using assms by (simp add: MCauchy_def) metis
qed

lemma MCauchy_offset:
  assumes cau: "MCauchy (\<sigma> \<circ> (+)k)" and \<sigma>: "\<And>n. n < k \<Longrightarrow> \<sigma> n \<in> M" 
  shows "MCauchy \<sigma>"
  unfolding MCauchy_def image_subset_iff
proof (intro conjI strip)
  fix n
  show "\<sigma> n \<in> M"
    using assms
    unfolding MCauchy_def image_subset_iff
    by (metis UNIV_I comp_apply le_iff_add linorder_not_le)
next
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  obtain N where "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d ((\<sigma> \<circ> (+)k) n) ((\<sigma> \<circ> (+)k) n') < \<epsilon>"
    using cau \<open>\<epsilon> > 0\<close> by (fastforce simp: MCauchy_def)
  then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    unfolding o_def
    apply (rule_tac x="k+N" in exI)
    by (smt (verit, del_insts) add.assoc le_add1 less_eqE)
qed

lemma MCauchy_convergent_subsequence:
  assumes cau: "MCauchy \<sigma>" and "strict_mono r" 
     and lim: "limitin mtopology (\<sigma> \<circ> r) a sequentially"
  shows "limitin mtopology \<sigma> a sequentially"
  unfolding limitin_metric
proof (intro conjI strip)
  show "a \<in> M"
    by (meson assms limitin_mspace)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  then obtain N1 where N1: "\<And>n n'. \<lbrakk>n\<ge>N1; n'\<ge>N1\<rbrakk> \<Longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>/2"
    using cau unfolding MCauchy_def by (meson half_gt_zero)
  obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> (\<sigma> \<circ> r) n \<in> M \<and> d ((\<sigma> \<circ> r) n) a < \<epsilon>/2"
    by (metis (no_types, lifting) lim \<open>\<epsilon> > 0\<close> half_gt_zero limit_metric_sequentially)
  have "\<sigma> n \<in> M \<and> d (\<sigma> n) a < \<epsilon>" if "n \<ge> max N1 N2" for n
  proof (intro conjI)
    show "\<sigma> n \<in> M"
      using MCauchy_def cau by blast
    have "N1 \<le> r n"
      by (meson \<open>strict_mono r\<close> le_trans max.cobounded1 strict_mono_imp_increasing that)
    then show "d (\<sigma> n) a < \<epsilon>"
      using N1[of n "r n"] N2[of n] \<open>\<sigma> n \<in> M\<close> \<open>a \<in> M\<close> triangle that by fastforce
  qed
  then show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) a < \<epsilon>"
    using eventually_sequentially by blast
qed

lemma MCauchy_interleaving_gen:
  "MCauchy (\<lambda>n. if even n then x(n div 2) else y(n div 2)) \<longleftrightarrow>
    (MCauchy x \<and> MCauchy y \<and> (\<lambda>n. d (x n) (y n)) \<longlonglongrightarrow> 0)" (is "?lhs=?rhs")
proof
  assume L: ?lhs
  have evens: "strict_mono (\<lambda>n::nat. 2 * n)" and odds: "strict_mono (\<lambda>n::nat. Suc (2 * n))"
    by (auto simp: strict_mono_def)
  show ?rhs
  proof (intro conjI)
    show "MCauchy x" "MCauchy y"
      using MCauchy_subsequence [OF evens L] MCauchy_subsequence [OF odds L] by (auto simp: o_def)
    show "(\<lambda>n. d (x n) (y n)) \<longlonglongrightarrow> 0"
      unfolding LIMSEQ_iff
    proof (intro strip)
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then obtain N where N: 
        "\<And>n n'. \<lbrakk>n\<ge>N; n'\<ge>N\<rbrakk> \<Longrightarrow> d (if even n then x (n div 2) else y (n div 2))
                                   (if even n' then x (n' div 2) else y (n' div 2))  < \<epsilon>"
        using L MCauchy_def by fastforce
      have "d (x n) (y n) < \<epsilon>" if "n\<ge>N" for n
        using N [of "2*n" "Suc(2*n)"] that by auto
      then show "\<exists>N. \<forall>n\<ge>N. norm (d (x n) (y n) - 0) < \<epsilon>"
        by auto
    qed
  qed
next
  assume R: ?rhs
  show ?lhs
    unfolding MCauchy_def
  proof (intro conjI strip)
    show "range (\<lambda>n. if even n then x (n div 2) else y (n div 2)) \<subseteq> M"
      using R by (auto simp: MCauchy_def)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    obtain Nx where Nx: "\<And>n n'. \<lbrakk>n\<ge>Nx; n'\<ge>Nx\<rbrakk> \<Longrightarrow> d (x n) (x n')  < \<epsilon>/2"
      by (meson half_gt_zero MCauchy_def R \<open>\<epsilon> > 0\<close>)
    obtain Ny where Ny: "\<And>n n'. \<lbrakk>n\<ge>Ny; n'\<ge>Ny\<rbrakk> \<Longrightarrow> d (y n) (y n')  < \<epsilon>/2"
      by (meson half_gt_zero MCauchy_def R \<open>\<epsilon> > 0\<close>)
    obtain Nxy where Nxy: "\<And>n. n\<ge>Nxy \<Longrightarrow> d (x n) (y n) < \<epsilon>/2"
      using R \<open>\<epsilon> > 0\<close> half_gt_zero unfolding LIMSEQ_iff
      by (metis abs_mdist diff_zero real_norm_def)
    define N where "N \<equiv> 2 * Max{Nx,Ny,Nxy}"
    show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (if even n then x (n div 2) else y (n div 2)) (if even n' then x (n' div 2) else y (n' div 2)) < \<epsilon>"
    proof (intro exI strip)
      fix n n'
      assume "N \<le> n" and "N \<le> n'"
      then have "n div 2 \<ge> Nx" "n div 2 \<ge> Ny" "n div 2 \<ge> Nxy" "n' div 2 \<ge> Nx" "n' div 2 \<ge> Ny" 
        by (auto simp: N_def)
      then have dxyn: "d (x (n div 2)) (y (n div 2)) < \<epsilon>/2" 
            and dxnn': "d (x (n div 2)) (x (n' div 2)) < \<epsilon>/2"
            and dynn': "d (y (n div 2)) (y (n' div 2)) < \<epsilon>/2"
        using Nx Ny Nxy by blast+
      have inM: "x (n div 2) \<in> M" "x (n' div 2) \<in> M""y (n div 2) \<in> M" "y (n' div 2) \<in> M"
        using Metric_space.MCauchy_def Metric_space_axioms R by blast+
      show "d (if even n then x (n div 2) else y (n div 2)) (if even n' then x (n' div 2) else y (n' div 2)) < \<epsilon>"
      proof (cases "even n")
        case nt: True
        show ?thesis
        proof (cases "even n'")
          case True
          with \<open>\<epsilon> > 0\<close> nt dxnn' show ?thesis by auto
        next
          case False
          with nt dxyn dynn' inM triangle show ?thesis
            by fastforce
        qed
      next
        case nf: False
        show ?thesis 
        proof (cases "even n'")
          case True
          then show ?thesis
            by (smt (verit) \<open>\<epsilon> > 0\<close> dxyn dxnn' triangle commute inM field_sum_of_halves)
        next
          case False
          with \<open>\<epsilon> > 0\<close> nf dynn' show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma MCauchy_interleaving:
   "MCauchy (\<lambda>n. if even n then \<sigma>(n div 2) else a) \<longleftrightarrow>
    range \<sigma> \<subseteq> M \<and> limitin mtopology \<sigma> a sequentially"  (is "?lhs=?rhs")
proof -
  have "?lhs \<longleftrightarrow> (MCauchy \<sigma> \<and> a \<in> M \<and> (\<lambda>n. d (\<sigma> n) a) \<longlonglongrightarrow> 0)"
    by (simp add: MCauchy_interleaving_gen [where y = "\<lambda>n. a"])
  also have "... = ?rhs"
    by (metis MCauchy_def always_eventually convergent_imp_MCauchy limitin_metric_dist_null range_subsetD)
  finally show ?thesis .
qed

lemma mcomplete_nest:
   "mcomplete \<longleftrightarrow>
      (\<forall>C::nat \<Rightarrow>'a set. (\<forall>n. closedin mtopology (C n)) \<and>
          (\<forall>n. C n \<noteq> {}) \<and> decseq C \<and> (\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>)
          \<longrightarrow> \<Inter> (range C) \<noteq> {})" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding imp_conjL
  proof (intro strip)
    fix C :: "nat \<Rightarrow> 'a set"
    assume clo: "\<forall>n. closedin mtopology (C n)"
      and ne: "\<forall>n. C n \<noteq> ({}::'a set)"
      and dec: "decseq C"
      and cover [rule_format]: "\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>"
    obtain \<sigma> where \<sigma>: "\<And>n. \<sigma> n \<in> C n"
      by (meson ne empty_iff set_eq_iff)
    have "MCauchy \<sigma>"
      unfolding MCauchy_def
    proof (intro conjI strip)
      show "range \<sigma> \<subseteq> M"
        using \<sigma> clo metric_closedin_iff_sequentially_closed by auto 
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then obtain N a where N: "C N \<subseteq> mcball a (\<epsilon>/3)"
        using cover by fastforce
      have "d (\<sigma> m) (\<sigma> n) < \<epsilon>" if "N \<le> m" "N \<le> n" for m n
      proof -
        have "d a (\<sigma> m) \<le> \<epsilon>/3" "d a (\<sigma> n) \<le> \<epsilon>/3"
          using dec N \<sigma> that by (fastforce simp: decseq_def)+
        then have "d (\<sigma> m) (\<sigma> n) \<le> \<epsilon>/3 + \<epsilon>/3"
          using triangle \<sigma> commute dec decseq_def subsetD that N
          by (smt (verit, ccfv_threshold) in_mcball)
        also have "... < \<epsilon>"
          using \<open>\<epsilon> > 0\<close> by auto
        finally show ?thesis .
      qed
      then show "\<exists>N. \<forall>m n. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> d (\<sigma> m) (\<sigma> n) < \<epsilon>"
        by blast
    qed
    then obtain x where x: "limitin mtopology \<sigma> x sequentially"
      using L mcomplete_def by blast
    have "x \<in> C n" for n
    proof (rule limitin_closedin [OF x])
      show "closedin mtopology (C n)"
        by (simp add: clo)
      show "\<forall>\<^sub>F x in sequentially. \<sigma> x \<in> C n"
        by (metis \<sigma> dec decseq_def eventually_sequentiallyI subsetD)
    qed auto
    then show "\<Inter> (range C) \<noteq> {}"
      by blast
qed
next
  assume R: ?rhs  
  show ?lhs
    unfolding mcomplete_def
  proof (intro strip)
    fix \<sigma>
    assume "MCauchy \<sigma>"
    then have "range \<sigma> \<subseteq> M"
      using MCauchy_def by blast
    define C where "C \<equiv> \<lambda>n. mtopology closure_of (\<sigma> ` {n..})"
    have "\<forall>n. closedin mtopology (C n)" 
      by (auto simp: C_def)
    moreover
    have ne: "\<And>n. C n \<noteq> {}"
      using \<open>MCauchy \<sigma>\<close> by (auto simp: C_def MCauchy_def disjnt_iff closure_of_eq_empty_gen)
    moreover
    have dec: "decseq C"
      unfolding monotone_on_def
    proof (intro strip)
      fix m n::nat
      assume "m \<le> n"
      then have "{n..} \<subseteq> {m..}"
        by auto
      then show "C n \<subseteq> C m"
        unfolding C_def by (meson closure_of_mono image_mono)
    qed
    moreover
    have C: "\<exists>N u. C N \<subseteq> mcball u \<epsilon>" if "\<epsilon>>0" for \<epsilon>
    proof -
      obtain N where "\<And>m n. N \<le> m \<and> N \<le> n \<Longrightarrow> d (\<sigma> m) (\<sigma> n) < \<epsilon>"
        by (meson MCauchy_def \<open>0 < \<epsilon>\<close> \<open>MCauchy \<sigma>\<close>)
      then have "\<sigma> ` {N..} \<subseteq> mcball (\<sigma> N) \<epsilon>"
        using MCauchy_def \<open>MCauchy \<sigma>\<close> by (force simp: less_eq_real_def)
      then have "C N \<subseteq> mcball (\<sigma> N) \<epsilon>"
        by (simp add: C_def closure_of_minimal)
      then show ?thesis
        by blast
    qed
    ultimately obtain l where x: "l \<in> \<Inter> (range C)"
      by (metis R ex_in_conv)
    then have *: "\<And>\<epsilon> N. 0 < \<epsilon> \<Longrightarrow> \<exists>n'. N \<le> n' \<and> l \<in> M \<and> \<sigma> n' \<in> M \<and> d l (\<sigma> n') < \<epsilon>"
      by (force simp: C_def metric_closure_of)
    then have "l \<in> M"
      using gt_ex by blast
    show "\<exists>l. limitin mtopology \<sigma> l sequentially"
      unfolding limitin_metric
    proof (intro conjI strip exI)
      show "l \<in> M"
        using \<open>\<forall>n. closedin mtopology (C n)\<close> closedin_subset x by fastforce
      fix \<epsilon>::real
      assume "\<epsilon> > 0"
      obtain N where N: "\<And>m n. N \<le> m \<and> N \<le> n \<Longrightarrow> d (\<sigma> m) (\<sigma> n) < \<epsilon>/2"
        by (meson MCauchy_def \<open>0 < \<epsilon>\<close> \<open>MCauchy \<sigma>\<close> half_gt_zero)
      with * [of "\<epsilon>/2" N]
      have "\<forall>n\<ge>N. \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>"
        by (smt (verit) \<open>range \<sigma> \<subseteq> M\<close> commute field_sum_of_halves range_subsetD triangle)
      then show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>"
        using eventually_sequentially by blast
    qed
  qed
qed


lemma mcomplete_nest_sing:
   "mcomplete \<longleftrightarrow>
    (\<forall>C. (\<forall>n. closedin mtopology (C n)) \<and>
          (\<forall>n. C n \<noteq> {}) \<and> decseq C \<and> (\<forall>e>0. \<exists>n a. C n \<subseteq> mcball a e)
         \<longrightarrow> (\<exists>l. l \<in> M \<and> \<Inter> (range C) = {l}))"
proof -
  have *: False
    if clo: "\<forall>n. closedin mtopology (C n)"
      and cover: "\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>"
      and no_sing: "\<And>y. y \<in> M \<Longrightarrow> \<Inter> (range C) \<noteq> {y}"
      and l: "\<forall>n. l \<in> C n"
    for C :: "nat \<Rightarrow> 'a set" and l
  proof -
    have inM: "\<And>x. x \<in> \<Inter> (range C) \<Longrightarrow> x \<in> M"
      using closedin_metric clo by fastforce
    then have "l \<in> M"
      by (simp add: l)
    have False if l': "l' \<in> \<Inter> (range C)" and "l' \<noteq> l" for l'
    proof -
      have "l' \<in> M"
        using inM l' by blast
      obtain n a where na: "C n \<subseteq> mcball a (d l l' / 3)"
        using inM \<open>l \<in> M\<close> l' \<open>l' \<noteq> l\<close> cover by force
      then have "d a l \<le> (d l l' / 3)" "d a l' \<le> (d l l' / 3)" "a \<in> M"
        using l l' na in_mcball by auto
      then have "d l l' \<le> (d l l' / 3) + (d l l' / 3)"
        using \<open>l \<in> M\<close> \<open>l' \<in> M\<close> mdist_reverse_triangle by fastforce
      then show False
        using nonneg [of l l'] \<open>l' \<noteq> l\<close> \<open>l \<in> M\<close> \<open>l' \<in> M\<close> zero by force
    qed
    then show False
      by (metis l \<open>l \<in> M\<close> no_sing INT_I empty_iff insertI1 is_singletonE is_singletonI')
  qed
  show ?thesis
    unfolding mcomplete_nest imp_conjL 
    apply (intro all_cong1 imp_cong refl)
    using * 
    by (smt (verit) Inter_iff ex_in_conv range_constant range_eqI)
qed

lemma mcomplete_fip:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C \<in> \<C>. closedin mtopology C) \<and>
         (\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {})
        \<longrightarrow> \<Inter> \<C> \<noteq> {})" 
   (is "?lhs = ?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding mcomplete_nest_sing imp_conjL
  proof (intro strip)
    fix \<C> :: "'a set set"
    assume clo: "\<forall>C\<in>\<C>. closedin mtopology C"
      and cover: "\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e"
      and fip: "\<forall>\<F>. finite \<F> \<longrightarrow> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}"
    then have "\<forall>n. \<exists>C. C \<in> \<C> \<and> (\<exists>a. C \<subseteq> mcball a (inverse (Suc n)))"
      by simp
    then obtain C where C: "\<And>n. C n \<in> \<C>" 
          and coverC: "\<And>n. \<exists>a. C n \<subseteq> mcball a (inverse (Suc n))"
      by metis
    define D where "D \<equiv> \<lambda>n. \<Inter> (C ` {..n})"
    have cloD: "closedin mtopology (D n)" for n
      unfolding D_def using clo C by blast
    have neD: "D n \<noteq> {}" for n
      using fip C by (simp add: D_def image_subset_iff)
    have decD: "decseq D"
      by (force simp: D_def decseq_def)
    have coverD: "\<exists>n a. D n \<subseteq> mcball a \<epsilon>" if " \<epsilon> >0" for \<epsilon>
    proof -
      obtain n where "inverse (Suc n) < \<epsilon>"
        using \<open>0 < \<epsilon>\<close> reals_Archimedean by blast
      then obtain a where "C n \<subseteq> mcball a \<epsilon>"
        by (meson coverC less_eq_real_def mcball_subset_concentric order_trans)
      then show ?thesis
        unfolding D_def by blast
    qed
    have *: "a \<in> \<Inter>\<C>" if a: "\<Inter> (range D) = {a}" and "a \<in> M" for a
    proof -
      have aC: "a \<in> C n" for n
        using that by (auto simp: D_def)
      have eqa: "\<And>u. (\<forall>n. u \<in> C n) \<Longrightarrow> a = u"
        using that by (auto simp: D_def)
      have "a \<in> T" if "T \<in> \<C>" for T
      proof -
        have cloT: "closedin mtopology (T \<inter> D n)" for n
          using clo cloD that by blast
        have "\<Inter> (insert T (C ` {..n})) \<noteq> {}" for n
          using that C by (intro fip [rule_format]) auto
        then have neT: "T \<inter> D n \<noteq> {}" for n
          by (simp add: D_def)
        have decT: "decseq (\<lambda>n. T \<inter> D n)"
          by (force simp: D_def decseq_def)
        have coverT: "\<exists>n a. T \<inter> D n \<subseteq> mcball a \<epsilon>" if " \<epsilon> >0" for \<epsilon>
          by (meson coverD le_infI2 that)
        show ?thesis
          using L [unfolded mcomplete_nest_sing, rule_format, of "\<lambda>n. T \<inter> D n"] a
          by (force simp: cloT neT decT coverT)
      qed
      then show ?thesis by auto
    qed
    show "\<Inter> \<C> \<noteq> {}"
      by (metis L cloD neD decD coverD * empty_iff mcomplete_nest_sing)
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding mcomplete_nest imp_conjL
  proof (intro strip)
    fix C :: "nat \<Rightarrow> 'a set"
    assume clo: "\<forall>n. closedin mtopology (C n)"
      and ne: "\<forall>n. C n \<noteq> {}"
      and dec: "decseq C"
      and cover: "\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>"
    have "\<Inter>(C ` N) \<noteq> {}" if "finite N" for N
    proof -
      obtain k where "N \<subseteq> {..k}"
        using \<open>finite N\<close> finite_nat_iff_bounded_le by auto
      with dec have "C k \<subseteq> \<Inter>(C ` N)" by (auto simp: decseq_def)
      then show ?thesis
        using ne by force
    qed
    with clo cover R [of "range C"] show "\<Inter> (range C) \<noteq> {}"
      by (metis (no_types, opaque_lifting) finite_subset_image image_iff UNIV_I)
  qed
qed


lemma mcomplete_fip_sing:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C\<in>\<C>. closedin mtopology C) \<and>
     (\<forall>e>0. \<exists>c a. c \<in> \<C> \<and> c \<subseteq> mcball a e) \<and>
     (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}) \<longrightarrow>
     (\<exists>l. l \<in> M \<and> \<Inter> \<C> = {l}))"
   (is "?lhs = ?rhs")
proof
  have *: "l \<in> M" "\<Inter> \<C> = {l}"
    if clo: "Ball \<C> (closedin mtopology)"
      and cover: "\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e"
      and fin: "\<forall>\<F>. finite \<F> \<longrightarrow> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}"
      and l: "l \<in> \<Inter> \<C>"
    for \<C> :: "'a set set" and l
  proof -
    show "l \<in> M"
      by (meson Inf_lower2 clo cover gt_ex metric_closedin_iff_sequentially_closed subsetD that(4))
    show  "\<Inter> \<C> = {l}"
    proof (cases "\<C> = {}")
      case True
      then show ?thesis
        using cover mbounded_pos by auto
    next
      case False
      have CM: "\<And>a. a \<in> \<Inter>\<C> \<Longrightarrow> a \<in> M"
        using False clo closedin_subset by fastforce
      have "l' \<notin> \<Inter> \<C>" if "l' \<noteq> l" for l'
      proof 
        assume l': "l' \<in> \<Inter> \<C>"
        with CM have "l' \<in> M" by blast
        with that \<open>l \<in> M\<close> have gt0: "0 < d l l'"
          by simp
        then obtain C a where "C \<in> \<C>" and C: "C \<subseteq> mcball a (d l l' / 3)"
          using cover [rule_format, of "d l l' / 3"] by auto
        then have "d a l \<le> (d l l' / 3)" "d a l' \<le> (d l l' / 3)" "a \<in> M"
          using l l' in_mcball by auto
        then have "d l l' \<le> (d l l' / 3) + (d l l' / 3)"
          using \<open>l \<in> M\<close> \<open>l' \<in> M\<close> mdist_reverse_triangle by fastforce
        with gt0 show False by auto
      qed
      then show ?thesis
        using l by fastforce
    qed
  qed
  assume L: ?lhs
  with * show ?rhs
    unfolding mcomplete_fip imp_conjL ex_in_conv [symmetric]
    by (elim all_forward imp_forward2 asm_rl) (blast intro:  elim: )
next
  assume ?rhs then show ?lhs
    unfolding mcomplete_fip by (force elim!: all_forward)
qed

end

lemma MCauchy_iff_Cauchy [iff]: "Met_TC.MCauchy = Cauchy"
  by (force simp: Cauchy_def Met_TC.MCauchy_def)

lemma mcomplete_iff_complete [iff]:
  "Met_TC.mcomplete (Pure.type ::'a::metric_space itself) \<longleftrightarrow> complete (UNIV::'a set)"
  by (auto simp: Met_TC.mcomplete_def complete_def)

lemma euclidean_metric: "Met_TC.mcomplete (Pure.type ::'a::euclidean_space itself)"
  using complete_UNIV mcomplete_iff_complete by blast

context submetric
begin 

lemma MCauchy_submetric:
   "sub.MCauchy \<sigma> \<longleftrightarrow> range \<sigma> \<subseteq> A \<and> MCauchy \<sigma>"
  using MCauchy_def sub.MCauchy_def subset by force

lemma closedin_mcomplete_imp_mcomplete:
  assumes clo: "closedin mtopology A" and "mcomplete"
  shows "sub.mcomplete"
  unfolding sub.mcomplete_def
proof (intro strip)
  fix \<sigma>
  assume "sub.MCauchy \<sigma>"
  then have \<sigma>: "MCauchy \<sigma>" "range \<sigma> \<subseteq> A"
    using MCauchy_submetric by blast+
  then obtain x where x: "limitin mtopology \<sigma> x sequentially"
    using \<open>mcomplete\<close> unfolding mcomplete_def by blast
  then have "x \<in> A"
    using \<sigma> clo metric_closedin_iff_sequentially_closed by force
  with \<sigma> x show "\<exists>x. limitin sub.mtopology \<sigma> x sequentially"
    using limitin_submetric_iff range_subsetD by fastforce
qed


lemma sequentially_closedin_mcomplete_imp_mcomplete:
  assumes "mcomplete" and "\<And>\<sigma> l. range \<sigma> \<subseteq> A \<and> limitin mtopology \<sigma> l sequentially \<Longrightarrow> l \<in> A"
  shows "sub.mcomplete"
  using assms closedin_mcomplete_imp_mcomplete metric_closedin_iff_sequentially_closed subset by blast

end


context Metric_space
begin

lemma mcomplete_Un:
  assumes A: "submetric M d A" "Metric_space.mcomplete A d" 
      and B: "submetric M d B" "Metric_space.mcomplete B d"
  shows   "submetric M d (A \<union> B)" "Metric_space.mcomplete (A \<union> B) d" 
proof -
  show "submetric M d (A \<union> B)"
    by (meson assms le_sup_iff submetric_axioms_def submetric_def) 
  then interpret MAB: Metric_space "A \<union> B" d
    by (meson submetric.subset subspace)
  interpret MA: Metric_space A d
    by (meson A submetric.subset subspace)
  interpret MB: Metric_space B d
    by (meson B submetric.subset subspace)
  show "Metric_space.mcomplete (A \<union> B) d"
    unfolding MAB.mcomplete_def
  proof (intro strip)
    fix \<sigma>
    assume "MAB.MCauchy \<sigma>"
    then have "range \<sigma> \<subseteq> A \<union> B"
      using MAB.MCauchy_def by blast
    then have "UNIV \<subseteq> \<sigma> -` A \<union> \<sigma> -` B"
      by blast
    then consider "infinite (\<sigma> -` A)" | "infinite (\<sigma> -` B)"
      using finite_subset by auto
    then show "\<exists>x. limitin MAB.mtopology \<sigma> x sequentially"
    proof cases
      case 1
      then obtain r where "strict_mono r" and r: "\<And>n::nat. r n \<in> \<sigma> -` A"
        using infinite_enumerate by blast 
      then have "MA.MCauchy (\<sigma> \<circ> r)"
        using MA.MCauchy_def MAB.MCauchy_def MAB.MCauchy_subsequence \<open>MAB.MCauchy \<sigma>\<close> by auto
      with A obtain x where "limitin MA.mtopology (\<sigma> \<circ> r) x sequentially"
        using MA.mcomplete_def by blast
      then have "limitin MAB.mtopology (\<sigma> \<circ> r) x sequentially"
        by (metis MA.limit_metric_sequentially MAB.limit_metric_sequentially UnCI)
      then show ?thesis
        using MAB.MCauchy_convergent_subsequence \<open>MAB.MCauchy \<sigma>\<close> \<open>strict_mono r\<close> by blast
    next
      case 2
      then obtain r where "strict_mono r" and r: "\<And>n::nat. r n \<in> \<sigma> -` B"
        using infinite_enumerate by blast 
      then have "MB.MCauchy (\<sigma> \<circ> r)"
        using MB.MCauchy_def MAB.MCauchy_def MAB.MCauchy_subsequence \<open>MAB.MCauchy \<sigma>\<close> by auto
      with B obtain x where "limitin MB.mtopology (\<sigma> \<circ> r) x sequentially"
        using MB.mcomplete_def by blast
      then have "limitin MAB.mtopology (\<sigma> \<circ> r) x sequentially"
        by (metis MB.limit_metric_sequentially MAB.limit_metric_sequentially UnCI)
      then show ?thesis
        using MAB.MCauchy_convergent_subsequence \<open>MAB.MCauchy \<sigma>\<close> \<open>strict_mono r\<close> by blast
    qed
  qed
qed

lemma mcomplete_Union:
  assumes "finite \<S>"
    and "\<And>A. A \<in> \<S> \<Longrightarrow> submetric M d A" "\<And>A. A \<in> \<S> \<Longrightarrow> Metric_space.mcomplete A d"
  shows   "submetric M d (\<Union>\<S>)" "Metric_space.mcomplete (\<Union>\<S>) d" 
  using assms
  by (induction rule: finite_induct) (auto simp: mcomplete_Un)

lemma mcomplete_Inter:
  assumes "finite \<S>" "\<S> \<noteq> {}"
    and sub: "\<And>A. A \<in> \<S> \<Longrightarrow> submetric M d A" 
    and comp: "\<And>A. A \<in> \<S> \<Longrightarrow> Metric_space.mcomplete A d"
  shows "submetric M d (\<Inter>\<S>)" "Metric_space.mcomplete (\<Inter>\<S>) d"
proof -
  show "submetric M d (\<Inter>\<S>)"
    using assms unfolding submetric_def submetric_axioms_def
    by (metis Inter_lower equals0I inf.orderE le_inf_iff) 
  then interpret MS: submetric M d "\<Inter>\<S>" 
    by (meson submetric.subset subspace)
  show "Metric_space.mcomplete (\<Inter>\<S>) d"
    unfolding MS.sub.mcomplete_def
  proof (intro strip)
    fix \<sigma>
    assume "MS.sub.MCauchy \<sigma>"
    then have "range \<sigma> \<subseteq> \<Inter>\<S>"
      using MS.MCauchy_submetric by blast
    obtain A where "A \<in> \<S>" and A: "Metric_space.mcomplete A d"
      using assms by blast
    then have "range \<sigma> \<subseteq> A"
      using \<open>range \<sigma> \<subseteq> \<Inter>\<S>\<close> by blast
    interpret SA: submetric M d A
      by (meson \<open>A \<in> \<S>\<close> sub submetric.subset subspace)
    have "MCauchy \<sigma>"
      using MS.MCauchy_submetric \<open>MS.sub.MCauchy \<sigma>\<close> by blast
    then obtain x where x: "limitin SA.sub.mtopology \<sigma> x sequentially"
      by (metis A SA.sub.MCauchy_def SA.sub.mcomplete_alt MCauchy_def \<open>range \<sigma> \<subseteq> A\<close>)
    show "\<exists>x. limitin MS.sub.mtopology \<sigma> x sequentially"
      apply (rule_tac x="x" in exI)
      unfolding MS.limitin_submetric_iff
    proof (intro conjI)
      show "x \<in> \<Inter> \<S>"
      proof clarsimp
        fix U
        assume "U \<in> \<S>"
        interpret SU: submetric M d U 
          by (meson \<open>U \<in> \<S>\<close> sub submetric.subset subspace)
        have "range \<sigma> \<subseteq> U"
          using \<open>U \<in> \<S>\<close> \<open>range \<sigma> \<subseteq> \<Inter> \<S>\<close> by blast
        moreover have "Metric_space.mcomplete U d"
          by (simp add: \<open>U \<in> \<S>\<close> comp)
        ultimately obtain x' where x': "limitin SU.sub.mtopology \<sigma> x' sequentially"
          using MCauchy_def SU.sub.MCauchy_def SU.sub.mcomplete_alt \<open>MCauchy \<sigma>\<close> by meson 
        have "x' = x"
        proof (intro limitin_metric_unique)
          show "limitin mtopology \<sigma> x' sequentially"
            by (meson SU.submetric_axioms submetric.limitin_submetric_iff x')
          show "limitin mtopology \<sigma> x sequentially"
            by (meson SA.submetric_axioms submetric.limitin_submetric_iff x)
        qed auto
        then show "x \<in> U"
          using SU.sub.limitin_mspace x' by blast
      qed
      show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> \<Inter>\<S>"
        by (meson \<open>range \<sigma> \<subseteq> \<Inter> \<S>\<close> always_eventually range_subsetD)
      show "limitin mtopology \<sigma> x sequentially"
        by (meson SA.submetric_axioms submetric.limitin_submetric_iff x)
    qed
  qed
qed


lemma mcomplete_Int:
  assumes A: "submetric M d A" "Metric_space.mcomplete A d" 
      and B: "submetric M d B" "Metric_space.mcomplete B d"
    shows   "submetric M d (A \<inter> B)" "Metric_space.mcomplete (A \<inter> B) d"
  using mcomplete_Inter [of "{A,B}"] assms by force+

subsection\<open>Totally bounded subsets of metric spaces\<close>

definition mtotally_bounded 
  where "mtotally_bounded S \<equiv> \<forall>\<epsilon>>0. \<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"

lemma mtotally_bounded_empty [iff]: "mtotally_bounded {}"
by (simp add: mtotally_bounded_def)

lemma finite_imp_mtotally_bounded:
   "\<lbrakk>finite S; S \<subseteq> M\<rbrakk> \<Longrightarrow> mtotally_bounded S"
  by (auto simp: mtotally_bounded_def)

lemma mtotally_bounded_imp_subset: "mtotally_bounded S \<Longrightarrow> S \<subseteq> M"
  by (force simp: mtotally_bounded_def intro!: zero_less_one)

lemma mtotally_bounded_sing [simp]:
   "mtotally_bounded {x} \<longleftrightarrow> x \<in> M"
  by (meson empty_subsetI finite.simps finite_imp_mtotally_bounded insert_subset mtotally_bounded_imp_subset)

lemma mtotally_bounded_Un:
  assumes  "mtotally_bounded S" "mtotally_bounded T"
  shows "mtotally_bounded (S \<union> T)"
proof -
  have "\<exists>K. finite K \<and> K \<subseteq> S \<union> T \<and> S \<union> T \<subseteq> (\<Union>x\<in>K. mball x e)"
    if  "e>0" and K: "finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x e)"
      and L: "finite L \<and> L \<subseteq> T \<and> T \<subseteq> (\<Union>x\<in>L. mball x e)" for K L e
    using that by (rule_tac x="K \<union> L" in exI) auto
  with assms show ?thesis
    unfolding mtotally_bounded_def by presburger
qed
 
lemma mtotally_bounded_Union:
  assumes "finite f" "\<And>S. S \<in> f \<Longrightarrow> mtotally_bounded S"
  shows "mtotally_bounded (\<Union>f)"
  using assms by (induction f) (auto simp: mtotally_bounded_Un)

lemma mtotally_bounded_imp_mbounded:
  assumes "mtotally_bounded S"
  shows "mbounded S"
proof -
  obtain K where "finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x 1)" 
    using assms by (force simp: mtotally_bounded_def)
  then show ?thesis
    by (smt (verit) finite_imageI image_iff mbounded_Union mbounded_mball mbounded_subset)
qed


lemma mtotally_bounded_sequentially:
  "mtotally_bounded S \<longleftrightarrow>
    S \<subseteq> M \<and> (\<forall>\<sigma>::nat \<Rightarrow> 'a. range \<sigma> \<subseteq> S \<longrightarrow> (\<exists>r. strict_mono r \<and> MCauchy (\<sigma> \<circ> r)))"
  (is "_ \<longleftrightarrow> _ \<and> ?rhs")
proof (cases "S \<subseteq> M")
  case True
  show ?thesis
  proof -
    { fix \<sigma> :: "nat \<Rightarrow> 'a"                                                            
      assume L: "mtotally_bounded S" and \<sigma>: "range \<sigma> \<subseteq> S"
      have "\<exists>j > i. d (\<sigma> i) (\<sigma> j) < 3*\<epsilon>/2 \<and> infinite (\<sigma> -` mball (\<sigma> j) (\<epsilon>/2))"
        if inf: "infinite (\<sigma> -` mball (\<sigma> i) \<epsilon>)" and "\<epsilon> > 0" for i \<epsilon>
      proof -
        obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>x\<in>K. mball x (\<epsilon>/4))"
          by (metis L mtotally_bounded_def \<open>\<epsilon> > 0\<close> zero_less_divide_iff zero_less_numeral)
        then have K_imp_ex: "\<And>y. y \<in> S \<Longrightarrow> \<exists>x\<in>K. d x y < \<epsilon>/4"
          by fastforce
        have False if "\<forall>x\<in>K. d x (\<sigma> i) < \<epsilon> + \<epsilon>/4 \<longrightarrow> finite (\<sigma> -` mball x (\<epsilon>/4))"
        proof -
          have "\<exists>w. w \<in> K \<and> d w (\<sigma> i) < 5 * \<epsilon>/4 \<and> d w (\<sigma> j) < \<epsilon>/4"
            if "d (\<sigma> i) (\<sigma> j) < \<epsilon>" for j
          proof -
            obtain w where w: "d w (\<sigma> j) < \<epsilon>/4" "w \<in> K"
              using K_imp_ex \<sigma> by blast
            then have "d w (\<sigma> i) < \<epsilon> + \<epsilon>/4"
              by (smt (verit, ccfv_SIG) True \<open>K \<subseteq> S\<close> \<sigma> rangeI subset_eq that triangle')
            with w show ?thesis
              using in_mball by auto
          qed
          then have "(\<sigma> -` mball (\<sigma> i) \<epsilon>) \<subseteq> (\<Union>x\<in>K. if d x (\<sigma> i) < \<epsilon> + \<epsilon>/4 then \<sigma> -` mball x (\<epsilon>/4) else {})"
            using True \<open>K \<subseteq> S\<close> by force
          then show False
            using finite_subset inf \<open>finite K\<close> that by fastforce
        qed
        then obtain x where "x \<in> K" and dxi: "d x (\<sigma> i) < \<epsilon> + \<epsilon>/4" and infx: "infinite (\<sigma> -` mball x (\<epsilon>/4))"
          by blast
        then obtain j where "j \<in> (\<sigma> -` mball x (\<epsilon>/4)) - {..i}"
          using bounded_nat_set_is_finite by (meson Diff_infinite_finite finite_atMost)
        then have "j > i" and dxj: "d x (\<sigma> j) < \<epsilon>/4" 
          by auto
        have "(\<sigma> -` mball x (\<epsilon>/4)) \<subseteq> (\<sigma> -` mball y (\<epsilon>/2))" if "d x y < \<epsilon>/4" "y \<in> M" for y
          using that by (simp add: mball_subset Metric_space_axioms vimage_mono)
        then have infj: "infinite (\<sigma> -` mball (\<sigma> j) (\<epsilon>/2))"
          by (meson True \<open>d x (\<sigma> j) < \<epsilon>/4\<close> \<sigma> in_mono infx rangeI finite_subset)
        have "\<sigma> i \<in> M" "\<sigma> j \<in> M" "x \<in> M"  
          using True \<open>K \<subseteq> S\<close> \<open>x \<in> K\<close> \<sigma> by force+
        then have "d (\<sigma> i) (\<sigma> j) \<le> d x (\<sigma> i) + d x (\<sigma> j)"
          using triangle'' by blast
        also have "\<dots> < 3*\<epsilon>/2"
          using dxi dxj by auto
        finally have "d (\<sigma> i) (\<sigma> j) < 3*\<epsilon>/2" .
        with \<open>i < j\<close> infj show ?thesis by blast
      qed
      then obtain nxt where nxt: "\<And>i \<epsilon>. \<lbrakk>\<epsilon> > 0; infinite (\<sigma> -` mball (\<sigma> i) \<epsilon>)\<rbrakk> \<Longrightarrow> 
                 nxt i \<epsilon> > i \<and> d (\<sigma> i) (\<sigma> (nxt i \<epsilon>)) < 3*\<epsilon>/2 \<and> infinite (\<sigma> -` mball (\<sigma> (nxt i \<epsilon>)) (\<epsilon>/2))"
        by metis
      have "mbounded S"
        using L by (simp add: mtotally_bounded_imp_mbounded)
      then obtain B where B: "\<forall>y \<in> S. d (\<sigma> 0) y \<le> B" and "B > 0"
        by (meson \<sigma> mbounded_alt_pos range_subsetD)
      define eps where "eps \<equiv> \<lambda>n. (B+1) / 2^n"
      have [simp]: "eps (Suc n) = eps n / 2" "eps n > 0" for n
        using \<open>B > 0\<close> by (auto simp: eps_def)
      have "UNIV \<subseteq> \<sigma> -` mball (\<sigma> 0) (B+1)"
        using B True \<sigma> unfolding image_iff subset_iff
        by (smt (verit, best) UNIV_I in_mball vimageI)
      then have inf0: "infinite (\<sigma> -` mball (\<sigma> 0) (eps 0))"
        using finite_subset by (auto simp: eps_def)
      define r where "r \<equiv> rec_nat 0 (\<lambda>n rec. nxt rec (eps n))"
      have [simp]: "r 0 = 0" "r (Suc n) = nxt (r n) (eps n)" for n
        by (auto simp: r_def)
      have \<sigma>rM[simp]: "\<sigma> (r n) \<in> M" for n
        using True \<sigma> by blast
      have inf: "infinite (\<sigma> -` mball (\<sigma> (r n)) (eps n))" for n
      proof (induction n)
        case 0 then show ?case  
          by (simp add: inf0)
      next
        case (Suc n) then show ?case
          using nxt [of "eps n" "r n"] by simp
      qed
      then have "r (Suc n) > r n" for n
        by (simp add: nxt)
      then have "strict_mono r"
        by (simp add: strict_mono_Suc_iff)
      have d_less: "d (\<sigma> (r n)) (\<sigma> (r (Suc n))) < 3 * eps n / 2" for n
        using nxt [OF _ inf] by simp
      have eps_plus: "eps (k + n) = eps n * (1/2)^k" for k n
        by (simp add: eps_def power_add field_simps)
      have *: "d (\<sigma> (r n)) (\<sigma> (r (k + n))) < 3 * eps n" for n k
      proof -
        have "d (\<sigma> (r n)) (\<sigma> (r (k+n))) \<le> 3/2 * eps n * (\<Sum>i<k. (1/2)^i)"
        proof (induction k)
          case 0 then show ?case 
            by simp
        next
          case (Suc k)
          have "d (\<sigma> (r n)) (\<sigma> (r (Suc k + n))) \<le> d (\<sigma> (r n)) (\<sigma> (r (k + n))) + d (\<sigma> (r (k + n))) (\<sigma> (r (Suc (k + n))))"
            by (metis \<sigma>rM add.commute add_Suc_right triangle)
          with d_less[of "k+n"] Suc show ?case
            by (simp add: algebra_simps eps_plus)
        qed
        also have "\<dots> < 3/2 * eps n * 2"
          using geometric_sum [of "1/2::real" k] by simp
        finally show ?thesis by simp
      qed
      have "\<exists>N. \<forall>n\<ge>N. \<forall>n'\<ge>N. d (\<sigma> (r n)) (\<sigma> (r n')) < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
      proof -
        define N where "N \<equiv> nat \<lceil>(log 2 (6*(B+1) / \<epsilon>))\<rceil>"
        have \<section>: "b \<le> 2 ^ nat \<lceil>log 2 b\<rceil>" for b
          by (smt (verit) less_log_of_power real_nat_ceiling_ge)
        have N: "6 * eps N \<le> \<epsilon>"
          using \<section> [of "(6*(B+1) / \<epsilon>)"] that by (auto simp: N_def eps_def field_simps)
        have "d (\<sigma> (r N)) (\<sigma> (r n)) < 3 * eps N" if "n \<ge> N" for n
          by (metis * add.commute nat_le_iff_add that)
        then have "\<forall>n\<ge>N. \<forall>n'\<ge>N. d (\<sigma> (r n)) (\<sigma> (r n')) < 3 * eps N + 3 * eps N"
          by (smt (verit, best) \<sigma>rM triangle'')
        with N show ?thesis
          by fastforce
      qed
      then have "MCauchy (\<sigma> \<circ> r)"
        unfolding MCauchy_def using True \<sigma> by auto
      then have "\<exists>r. strict_mono r \<and> MCauchy (\<sigma> \<circ> r)"
        using \<open>strict_mono r\<close> by blast      
    }
    moreover
    { assume R: ?rhs
      have "mtotally_bounded S"
        unfolding mtotally_bounded_def
      proof (intro strip)
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        have False if \<section>: "\<And>K. \<lbrakk>finite K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>s\<in>S. s \<notin> (\<Union>x\<in>K. mball x \<epsilon>)"
        proof -
          obtain f where f: "\<And>K. \<lbrakk>finite K; K \<subseteq> S\<rbrakk> \<Longrightarrow> f K \<in> S \<and> f K \<notin> (\<Union>x\<in>K. mball x \<epsilon>)"
            using \<section> by metis
          define \<sigma> where "\<sigma> \<equiv> wfrec less_than (\<lambda>seq n. f (seq ` {..<n}))"
          have \<sigma>_eq: "\<sigma> n = f (\<sigma> ` {..<n})" for n
            by (simp add: cut_apply def_wfrec [OF \<sigma>_def])
          have [simp]: "\<sigma> n \<in> S" for n
            using wf_less_than
          proof (induction n rule: wf_induct_rule)
            case (less n) with f show ?case
              by (auto simp: \<sigma>_eq [of n])
          qed
          then have "range \<sigma> \<subseteq> S" by blast
          have \<sigma>: "p < n \<Longrightarrow> \<epsilon> \<le> d (\<sigma> p) (\<sigma> n)" for n p
            using f[of "\<sigma> ` {..<n}"] True by (fastforce simp: \<sigma>_eq [of n] Ball_def)
          then obtain r where "strict_mono r" "MCauchy (\<sigma> \<circ> r)"
            by (meson R \<open>range \<sigma> \<subseteq> S\<close>)
          with \<open>0 < \<epsilon>\<close> obtain N 
            where N: "\<And>n n'. \<lbrakk>n\<ge>N; n'\<ge>N\<rbrakk> \<Longrightarrow> d (\<sigma> (r n)) (\<sigma> (r n')) < \<epsilon>"
            by (force simp: MCauchy_def)
          show ?thesis
            using N [of N "Suc (r N)"] \<open>strict_mono r\<close>
            by (smt (verit) Suc_le_eq \<sigma> le_SucI order_refl strict_mono_imp_increasing)
        qed
        then show "\<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
          by blast
      qed
    }
    ultimately show ?thesis 
      using True by blast
  qed
qed (use mtotally_bounded_imp_subset in auto)


lemma mtotally_bounded_subset:
   "\<lbrakk>mtotally_bounded S; T \<subseteq> S\<rbrakk> \<Longrightarrow> mtotally_bounded T"
  by (meson mtotally_bounded_sequentially order_trans) 

lemma mtotally_bounded_submetric:
  assumes "mtotally_bounded S" "S \<subseteq> T" "T \<subseteq> M"
  shows "Metric_space.mtotally_bounded T d S"
proof -
  interpret submetric M d T
    by (simp add: Metric_space_axioms assms submetric.intro submetric_axioms.intro)
  show ?thesis
    using assms
    unfolding sub.mtotally_bounded_def mtotally_bounded_def
    by (force simp: subset_iff elim!: all_forward ex_forward)
qed

lemma mtotally_bounded_absolute:
   "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> Metric_space.mtotally_bounded S d S "
proof -
  have "mtotally_bounded S" if "S \<subseteq> M" "Metric_space.mtotally_bounded S d S"
  proof -
    interpret submetric M d S
      by (simp add: Metric_space_axioms submetric_axioms.intro submetric_def \<open>S \<subseteq> M\<close>)
    show ?thesis
      using that
      by (metis MCauchy_submetric Metric_space.mtotally_bounded_sequentially Metric_space_axioms subspace)
  qed
  moreover have "mtotally_bounded S \<Longrightarrow> Metric_space.mtotally_bounded S d S"
    by (simp add: mtotally_bounded_imp_subset mtotally_bounded_submetric)
  ultimately show ?thesis
    using mtotally_bounded_imp_subset by blast
qed

lemma mtotally_bounded_closure_of:
  assumes "mtotally_bounded S"
  shows "mtotally_bounded (mtopology closure_of S)"
proof -
  have "S \<subseteq> M"
    by (simp add: assms mtotally_bounded_imp_subset)
  have "mtotally_bounded(mtopology closure_of S)"
    unfolding mtotally_bounded_def
  proof (intro strip)
    fix \<epsilon>::real
    assume "\<epsilon> > 0"
    then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>x\<in>K. mball x (\<epsilon>/2))"
      by (metis assms mtotally_bounded_def half_gt_zero)
    have "mtopology closure_of S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
      unfolding metric_closure_of
    proof clarsimp
      fix x
      assume "x \<in> M" and x: "\<forall>r>0. \<exists>y\<in>S. y \<in> M \<and> d x y < r"
      then obtain y where "y \<in> S" and y: "d x y < \<epsilon>/2"
        using \<open>0 < \<epsilon>\<close> half_gt_zero by blast
      then obtain x' where "x' \<in> K" "y \<in> mball x' (\<epsilon>/2)"
        using K by auto
      then have "d x' x < \<epsilon>/2 + \<epsilon>/2"
        using triangle y \<open>x \<in> M\<close> commute by fastforce
      then show "\<exists>x'\<in>K. x' \<in> M \<and> d x' x < \<epsilon>"
        using \<open>K \<subseteq> S\<close> \<open>S \<subseteq> M\<close> \<open>x' \<in> K\<close> by force
    qed
    then show "\<exists>K. finite K \<and> K \<subseteq> mtopology closure_of S \<and> mtopology closure_of S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
      using closure_of_subset_Int  \<open>K \<subseteq> S\<close> \<open>finite K\<close> K by fastforce
  qed
  then show ?thesis
    by (simp add: assms inf.absorb2 mtotally_bounded_imp_subset)
qed

lemma mtotally_bounded_closure_of_eq:
   "S \<subseteq> M \<Longrightarrow> mtotally_bounded (mtopology closure_of S) \<longleftrightarrow> mtotally_bounded S"
  by (metis closure_of_subset mtotally_bounded_closure_of mtotally_bounded_subset topspace_mtopology)

lemma mtotally_bounded_cauchy_sequence:
  assumes "MCauchy \<sigma>"
  shows "mtotally_bounded (range \<sigma>)"
  unfolding MCauchy_def mtotally_bounded_def
proof (intro strip)
  fix \<epsilon>::real
  assume "\<epsilon> > 0"
  then obtain N where "\<And>n. N \<le> n \<Longrightarrow> d (\<sigma> N) (\<sigma> n) < \<epsilon>"
    using assms by (force simp: MCauchy_def)
  then have "\<And>m. \<exists>n\<le>N. \<sigma> n \<in> M \<and> \<sigma> m \<in> M \<and> d (\<sigma> n) (\<sigma> m) < \<epsilon>"
    by (metis MCauchy_def assms mdist_zero nle_le range_subsetD)
  then
  show "\<exists>K. finite K \<and> K \<subseteq> range \<sigma> \<and> range \<sigma> \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
    by (rule_tac x="\<sigma> ` {0..N}" in exI) force
qed

lemma MCauchy_imp_mbounded:
   "MCauchy \<sigma> \<Longrightarrow> mbounded (range \<sigma>)"
  by (simp add: mtotally_bounded_cauchy_sequence mtotally_bounded_imp_mbounded)

subsection\<open>Compactness in metric spaces\<close>

lemma Bolzano_Weierstrass_property:
  assumes "S \<subseteq> U" "S \<subseteq> M"
  shows
   "(\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> U \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)) \<longleftrightarrow>
    (\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> U \<inter> mtopology derived_set_of T \<noteq> {})"  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix T
    assume "T \<subseteq> S" and "infinite T"
      and T: "U \<inter> mtopology derived_set_of T = {}"
    then obtain \<sigma> :: "nat\<Rightarrow>'a" where "inj \<sigma>" "range \<sigma> \<subseteq> T"
      by (meson infinite_countable_subset)
    with L obtain l r where "l \<in> U" "strict_mono r" 
           and lr: "limitin mtopology (\<sigma> \<circ> r) l sequentially"
      by (meson \<open>T \<subseteq> S\<close> subset_trans)
    then obtain \<epsilon> where "\<epsilon> > 0" and \<epsilon>: "\<And>y. y \<in> T \<Longrightarrow> y = l \<or> \<not> d l y < \<epsilon>"
      using T \<open>T \<subseteq> S\<close> \<open>S \<subseteq> M\<close> 
      by (force simp: metric_derived_set_of limitin_metric disjoint_iff)
    with lr have "\<forall>\<^sub>F n in sequentially. \<sigma> (r n) \<in> M \<and> d (\<sigma> (r n)) l < \<epsilon>"
      by (auto simp: limitin_metric)
    then obtain N where N: "d (\<sigma> (r N)) l < \<epsilon>" "d (\<sigma> (r (Suc N))) l < \<epsilon>"
      using less_le_not_le by (auto simp: eventually_sequentially)
    moreover have "\<sigma> (r N) \<noteq> l \<or> \<sigma> (r (Suc N)) \<noteq> l"
      by (meson \<open>inj \<sigma>\<close> \<open>strict_mono r\<close> injD n_not_Suc_n strict_mono_eq)
    ultimately
    show False
       using \<epsilon> \<open>range \<sigma> \<subseteq> T\<close> commute by fastforce
  qed
next
  assume R: ?rhs 
  show ?lhs
  proof (intro strip)
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume "range \<sigma> \<subseteq> S"
    show "\<exists>l r. l \<in> U \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
    proof (cases "finite (range \<sigma>)")
      case True
      then obtain m where "infinite (\<sigma> -` {\<sigma> m})"
        by (metis image_iff inf_img_fin_dom nat_not_finite)
      then obtain r where [iff]: "strict_mono r" and r: "\<And>n::nat. r n \<in> \<sigma> -` {\<sigma> m}"
        using infinite_enumerate by blast 
      have [iff]: "\<sigma> m \<in> U" "\<sigma> m \<in> M"
        using \<open>range \<sigma> \<subseteq> S\<close> assms by blast+
      show ?thesis
      proof (intro conjI exI)
        show "limitin mtopology (\<sigma> \<circ> r) (\<sigma> m) sequentially"
          using r by (simp add: limitin_metric)
      qed auto
    next
      case False
      then obtain l where "l \<in> U" and l: "l \<in> mtopology derived_set_of (range \<sigma>)"
        by (meson R \<open>range \<sigma> \<subseteq> S\<close> disjoint_iff)
      then obtain g where g: "\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<sigma> (g \<epsilon>) \<noteq> l \<and> d l (\<sigma> (g \<epsilon>)) < \<epsilon>"
        by (simp add: metric_derived_set_of) metis
      have "range \<sigma> \<subseteq> M"
        using \<open>range \<sigma> \<subseteq> S\<close> assms by auto
      have "l \<in> M"
        using l metric_derived_set_of by auto
      define E where  \<comment>\<open>a construction to ensure monotonicity\<close>
        "E \<equiv> \<lambda>rec n. insert (inverse (Suc n)) ((\<lambda>i. d l (\<sigma> i)) ` (\<Union>k<n. {0..rec k})) - {0}"
      define r where "r \<equiv> wfrec less_than (\<lambda>rec n. g (Min (E rec n)))"
      have "(\<Union>k<n. {0..cut r less_than n k}) = (\<Union>k<n. {0..r k})" for n
        by (auto simp: cut_apply)
      then have r_eq: "r n = g (Min (E r n))" for n
        by (metis E_def def_wfrec [OF r_def] wf_less_than)
      have dl_pos[simp]: "d l (\<sigma> (r n)) > 0" for n
        using wf_less_than
      proof (induction n rule: wf_induct_rule)
        case (less n) 
        then have *: "Min (E r n) > 0"
          using \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> by (auto simp: E_def image_subset_iff)
        show ?case
          using g [OF *] r_eq [of n]
          by (metis \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> mdist_pos_less range_subsetD)
      qed
      then have non_l: "\<sigma> (r n) \<noteq> l" for n
        using \<open>range \<sigma> \<subseteq> M\<close> mdist_pos_eq by blast
      have Min_pos: "Min (E r n) > 0" for n
        using dl_pos \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> by (auto simp: E_def image_subset_iff)
      have d_small: "d (\<sigma>(r n)) l < inverse(Suc n)" for n
      proof -
        have "d (\<sigma>(r n)) l < Min (E r n)"
          by (simp add: \<open>0 < Min (E r n)\<close> commute g r_eq) 
        also have "... \<le> inverse(Suc n)"
          by (simp add: E_def)
        finally show ?thesis .
      qed
      have d_lt_d: "d l (\<sigma> (r n)) < d l (\<sigma> i)" if \<section>: "p < n" "i \<le> r p" "\<sigma> i \<noteq> l" for i p n
      proof -
        have 1: "d l (\<sigma> i) \<in> E r n"
          using \<section> \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> 
          by (force simp: E_def image_subset_iff image_iff)
        have "d l (\<sigma> (g (Min (E r n)))) < Min (E r n)"
          by (rule conjunct2 [OF g [OF Min_pos]])
        also have "Min (E r n) \<le> d l (\<sigma> i)"
          using 1 unfolding E_def by (force intro!: Min.coboundedI)
        finally show ?thesis
          by (simp add: r_eq) 
      qed
      have r: "r p < r n" if "p < n" for p n
        using d_lt_d [OF that] non_l by (meson linorder_not_le order_less_irrefl) 
      show ?thesis
      proof (intro exI conjI)
        show "strict_mono r"
          by (simp add: r strict_monoI)
        show "limitin mtopology (\<sigma> \<circ> r) l sequentially"
          unfolding limitin_metric
        proof (intro conjI strip \<open>l \<in> M\<close>)
          fix \<epsilon> :: real
          assume "\<epsilon> > 0"
          then have "\<forall>\<^sub>F n in sequentially. inverse(Suc n) < \<epsilon>"
            using Archimedean_eventually_inverse by auto
          then show "\<forall>\<^sub>F n in sequentially. (\<sigma> \<circ> r) n \<in> M \<and> d ((\<sigma> \<circ> r) n) l < \<epsilon>"
            by (smt (verit) \<open>range \<sigma> \<subseteq> M\<close> commute comp_apply d_small eventually_mono range_subsetD)
        qed
      qed (use \<open>l \<in> U\<close> in auto)
    qed
  qed
qed

subsubsection \<open>More on Bolzano Weierstrass\<close>

lemma Bolzano_Weierstrass_A: 
  assumes "compactin mtopology S" "T \<subseteq> S" "infinite T"
  shows "S \<inter> mtopology derived_set_of T \<noteq> {}"
  by (simp add: assms compactin_imp_Bolzano_Weierstrass)

lemma Bolzano_Weierstrass_B:
  fixes \<sigma> :: "nat \<Rightarrow> 'a"
  assumes "S \<subseteq> M" "range \<sigma> \<subseteq> S"
    and "\<And>T. \<lbrakk>T \<subseteq> S \<and> infinite T\<rbrakk> \<Longrightarrow> S \<inter> mtopology derived_set_of T \<noteq> {}"
  shows "\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
  using Bolzano_Weierstrass_property assms by blast

lemma Bolzano_Weierstrass_C:
  assumes "S \<subseteq> M"
  assumes "\<And>\<sigma>:: nat \<Rightarrow> 'a. range \<sigma> \<subseteq> S \<Longrightarrow>
                (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)"
  shows "mtotally_bounded S"
  unfolding mtotally_bounded_sequentially
  by (metis convergent_imp_MCauchy assms image_comp image_mono subset_UNIV subset_trans)

lemma Bolzano_Weierstrass_D:
  assumes "S \<subseteq> M" "S \<subseteq> \<Union>\<C>" and opeU: "\<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U"
  assumes \<section>: "(\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially))"
  shows "\<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
proof (rule ccontr)
  assume "\<not> (\<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U)"
  then have "\<forall>n. \<exists>x\<in>S. \<forall>U\<in>\<C>. \<not> mball x (inverse (Suc n)) \<subseteq> U"
    by simp
  then obtain \<sigma> where "\<And>n. \<sigma> n \<in> S" 
       and \<sigma>: "\<And>n U. U \<in> \<C> \<Longrightarrow> \<not> mball (\<sigma> n) (inverse (Suc n)) \<subseteq> U"
    by metis
  then obtain l r where "l \<in> S" "strict_mono r" 
         and lr: "limitin mtopology (\<sigma> \<circ> r) l sequentially"
    by (meson \<section> image_subsetI)
  with \<open>S \<subseteq> \<Union>\<C>\<close> obtain B where "l \<in> B" "B \<in> \<C>"
    by auto
  then obtain \<epsilon> where "\<epsilon> > 0" and \<epsilon>: "\<And>z. \<lbrakk>z \<in> M; d z l < \<epsilon>\<rbrakk> \<Longrightarrow> z \<in> B"
    by (metis opeU [OF \<open>B \<in> \<C>\<close>] commute in_mball openin_mtopology subset_iff)
  then have "\<forall>\<^sub>F n in sequentially. \<sigma> (r n) \<in> M \<and> d (\<sigma> (r n)) l < \<epsilon>/2"
    using lr half_gt_zero unfolding limitin_metric o_def by blast
  moreover have "\<forall>\<^sub>F n in sequentially. inverse (real (Suc n)) < \<epsilon>/2"
    using Archimedean_eventually_inverse \<open>0 < \<epsilon>\<close> half_gt_zero by blast
  ultimately obtain n where n: "d (\<sigma> (r n)) l < \<epsilon>/2" "inverse (real (Suc n)) < \<epsilon>/2"
    by (smt (verit, del_insts) eventually_sequentially le_add1 le_add2)
  have "x \<in> B" if "d (\<sigma> (r n)) x < inverse (Suc(r n))" "x \<in> M" for x
  proof -
    have rle: "inverse (real (Suc (r n))) \<le> inverse (real (Suc n))"
      using \<open>strict_mono r\<close> strict_mono_imp_increasing by auto
    have "d x l \<le> d (\<sigma> (r n)) x + d (\<sigma> (r n)) l"
      using that by (metis triangle \<open>\<And>n. \<sigma> n \<in> S\<close> \<open>l \<in> S\<close> \<open>S \<subseteq> M\<close> commute subsetD)
    also have "... < \<epsilon>"
      using that n rle by linarith
    finally show ?thesis
      by (simp add: \<epsilon> that)
  qed
  then show False
    using \<sigma> [of B "r n"] by (simp add: \<open>B \<in> \<C>\<close> subset_iff)
qed


lemma Bolzano_Weierstrass_E:
  assumes "mtotally_bounded S" "S \<subseteq> M"
  and S: "\<And>\<C>. \<lbrakk>\<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U; S \<subseteq> \<Union>\<C>\<rbrakk> \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
  shows "compactin mtopology S"
proof (clarsimp simp: compactin_def assms)
  fix \<U> :: "'a set set"
  assume \<U>: "\<forall>x\<in>\<U>. openin mtopology x" and "S \<subseteq> \<Union>\<U>"
  then obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>: "\<And>x. x \<in> S \<Longrightarrow> \<exists>U \<in> \<U>. mball x \<epsilon> \<subseteq> U"
    by (metis S)
  then obtain f where f: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> \<U> \<and> mball x \<epsilon> \<subseteq> f x"
    by metis
  then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
    by (metis \<open>0 < \<epsilon>\<close> \<open>mtotally_bounded S\<close> mtotally_bounded_def)
  show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>"
  proof (intro conjI exI)
    show "finite (f ` K)"
      by (simp add: \<open>finite K\<close>)
    show "f ` K \<subseteq> \<U>"
      using \<open>K \<subseteq> S\<close> f by blast
    show "S \<subseteq> \<Union>(f ` K)"
      using K \<open>K \<subseteq> S\<close> by (force dest: f)
  qed
qed


lemma compactin_eq_Bolzano_Weierstrass:
  "compactin mtopology S \<longleftrightarrow>
   S \<subseteq> M \<and> (\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> S \<inter> mtopology derived_set_of T \<noteq> {})"
  using Bolzano_Weierstrass_C Bolzano_Weierstrass_D Bolzano_Weierstrass_E
  by (smt (verit, del_insts) Bolzano_Weierstrass_property compactin_imp_Bolzano_Weierstrass compactin_subspace subset_refl topspace_mtopology)

lemma compactin_sequentially:
  shows "compactin mtopology S \<longleftrightarrow>
        S \<subseteq> M \<and>
        ((\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)))"
  by (metis Bolzano_Weierstrass_property compactin_eq_Bolzano_Weierstrass subset_refl)

lemma compactin_imp_mtotally_bounded: 
  "compactin mtopology S \<Longrightarrow> mtotally_bounded S"
  by (simp add: Bolzano_Weierstrass_C compactin_sequentially)

lemma lebesgue_number:
    "\<lbrakk>compactin mtopology S; S \<subseteq> \<Union>\<C>; \<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U\<rbrakk>
    \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
  by (simp add: Bolzano_Weierstrass_D compactin_sequentially)

lemma compact_space_sequentially:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> M
         \<longrightarrow> (\<exists>l r. l \<in> M \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially))"
  by (simp add: compact_space_def compactin_sequentially)

lemma compact_space_eq_Bolzano_Weierstrass:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>S. S \<subseteq> M \<and> infinite S \<longrightarrow> mtopology derived_set_of S \<noteq> {})"
  using Int_absorb1 [OF derived_set_of_subset_topspace [of mtopology]]
  by (force simp: compact_space_def compactin_eq_Bolzano_Weierstrass)

lemma compact_space_nest:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>C. (\<forall>n::nat. closedin mtopology (C n)) \<and> (\<forall>n. C n \<noteq> {}) \<and> decseq C \<longrightarrow> \<Inter>(range C) \<noteq> {})"
   (is "?lhs=?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof clarify
    fix C :: "nat \<Rightarrow> 'a set"
    assume "\<forall>n. closedin mtopology (C n)"
      and "\<forall>n. C n \<noteq> {}"
      and "decseq C"
      and "\<Inter> (range C) = {}"
    then obtain K where K: "finite K" "\<Inter>(C ` K) = {}"
      by (metis L compact_space_imp_nest)
    then obtain k where "K \<subseteq> {..k}"
      using finite_nat_iff_bounded_le by auto
    then have "C k \<subseteq> \<Inter>(C ` K)"
      using \<open>decseq C\<close> by (auto simp:decseq_def)
    then show False
      by (simp add: K \<open>\<forall>n. C n \<noteq> {}\<close>)
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding compact_space_sequentially
  proof (intro strip)
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume \<sigma>: "range \<sigma> \<subseteq> M"
    have "mtopology closure_of \<sigma> ` {n..} \<noteq> {}" for n
      using \<open>range \<sigma> \<subseteq> M\<close> by (auto simp: closure_of_eq_empty image_subset_iff)
    moreover have "decseq (\<lambda>n. mtopology closure_of \<sigma> ` {n..})"
      using closure_of_mono image_mono by (smt (verit) atLeast_subset_iff decseq_def) 
    ultimately obtain l where l: "\<And>n. l \<in> mtopology closure_of \<sigma> ` {n..}"
      using R [of "\<lambda>n. mtopology closure_of (\<sigma> ` {n..})"] by auto
    then have "l \<in> M" and "\<And>n. \<forall>r>0. \<exists>k\<ge>n. \<sigma> k \<in> M \<and> d l (\<sigma> k) < r"
      using metric_closure_of by fastforce+
    then obtain f where f: "\<And>n r. r>0 \<Longrightarrow> f n r \<ge> n \<and> \<sigma> (f n r) \<in> M \<and> d l (\<sigma> (f n r)) < r"
      by metis
    define r where "r = rec_nat (f 0 1) (\<lambda>n rec. (f (Suc rec) (inverse (Suc (Suc n)))))"
    have r: "d l (\<sigma>(r n)) < inverse(Suc n)" for n
      by (induction n) (auto simp: rec_nat_0_imp [OF r_def] rec_nat_Suc_imp [OF r_def] f)
    have "r n < r(Suc n)" for n
      by (simp add: Suc_le_lessD f r_def)
    then have "strict_mono r"
      by (simp add: strict_mono_Suc_iff)
    moreover have "limitin mtopology (\<sigma> \<circ> r) l sequentially"
      proof (clarsimp simp: limitin_metric \<open>l \<in> M\<close>)
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        then have "(\<forall>\<^sub>F n in sequentially. inverse (real (Suc n)) < \<epsilon>)"
          using Archimedean_eventually_inverse by blast
        then show "\<forall>\<^sub>F n in sequentially. \<sigma> (r n) \<in> M \<and> d (\<sigma> (r n)) l < \<epsilon>"
          by eventually_elim (metis commute \<open>range \<sigma> \<subseteq> M\<close>  order_less_trans r range_subsetD)
      qed
    ultimately show "\<exists>l r. l \<in> M \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
      using \<open>l \<in> M\<close> by blast
  qed
qed


lemma (in discrete_metric) mcomplete_discrete_metric: "disc.mcomplete"
proof (clarsimp simp: disc.mcomplete_def)
  fix \<sigma> :: "nat \<Rightarrow> 'a"
  assume "disc.MCauchy \<sigma>"
  then obtain N where "\<And>n. N \<le> n \<Longrightarrow> \<sigma> N = \<sigma> n"
    unfolding disc.MCauchy_def by (metis dd_def dual_order.refl order_less_irrefl zero_less_one)
  moreover have "range \<sigma> \<subseteq> M"
    using \<open>disc.MCauchy \<sigma>\<close> disc.MCauchy_def by blast
  ultimately have "limitin disc.mtopology \<sigma> (\<sigma> N) sequentially"
    by (metis disc.limit_metric_sequentially disc.zero range_subsetD)
  then show "\<exists>x. limitin disc.mtopology \<sigma> x sequentially" ..
qed

lemma compact_space_imp_mcomplete: "compact_space mtopology \<Longrightarrow> mcomplete"
  by (simp add: compact_space_nest mcomplete_nest)

lemma (in submetric) compactin_imp_mcomplete:
   "compactin mtopology A \<Longrightarrow> sub.mcomplete"
  by (simp add: compactin_subspace mtopology_submetric sub.compact_space_imp_mcomplete)

lemma (in submetric) mcomplete_imp_closedin:
  assumes "sub.mcomplete"
  shows "closedin mtopology A"
proof -
  have "l \<in> A"
    if "range \<sigma> \<subseteq> A" and l: "limitin mtopology \<sigma> l sequentially"
    for \<sigma> :: "nat \<Rightarrow> 'a" and l
  proof -
    have "sub.MCauchy \<sigma>"
      using convergent_imp_MCauchy subset that by (force simp: MCauchy_submetric)
    then have "limitin sub.mtopology \<sigma> l sequentially"
      using assms unfolding sub.mcomplete_def
      using l limitin_metric_unique limitin_submetric_iff trivial_limit_sequentially by blast
    then show ?thesis
      using limitin_submetric_iff by blast
  qed
  then show ?thesis
    using metric_closedin_iff_sequentially_closed subset by auto
qed

lemma (in submetric) closedin_eq_mcomplete:
   "mcomplete \<Longrightarrow> (closedin mtopology A \<longleftrightarrow> sub.mcomplete)"
  using closedin_mcomplete_imp_mcomplete mcomplete_imp_closedin by blast

lemma compact_space_eq_mcomplete_mtotally_bounded:
   "compact_space mtopology \<longleftrightarrow> mcomplete \<and> mtotally_bounded M"
  by (meson Bolzano_Weierstrass_C compact_space_imp_mcomplete compact_space_sequentially limitin_mspace 
            mcomplete_alt mtotally_bounded_sequentially subset_refl)


lemma compact_closure_of_imp_mtotally_bounded:
   "\<lbrakk>compactin mtopology (mtopology closure_of S); S \<subseteq> M\<rbrakk>
      \<Longrightarrow> mtotally_bounded S"
  using compactin_imp_mtotally_bounded mtotally_bounded_closure_of_eq by blast

lemma mtotally_bounded_eq_compact_closure_of:
  assumes "mcomplete"
  shows "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> compactin mtopology (mtopology closure_of S)"
  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding compactin_subspace
  proof (intro conjI)
    show "S \<subseteq> M"
      using L by (simp add: mtotally_bounded_imp_subset)
    show "mtopology closure_of S \<subseteq> topspace mtopology"
      by (simp add: \<open>S \<subseteq> M\<close> closure_of_minimal)
    then have MSM: "mtopology closure_of S \<subseteq> M"
      by auto
    interpret S: submetric M d "mtopology closure_of S"
    proof qed (use MSM in auto)
    have "S.sub.mtotally_bounded (mtopology closure_of S)"
      using L mtotally_bounded_absolute mtotally_bounded_closure_of by blast
    then
    show "compact_space (subtopology mtopology (mtopology closure_of S))"
      using S.closedin_mcomplete_imp_mcomplete S.mtopology_submetric S.sub.compact_space_eq_mcomplete_mtotally_bounded assms by force
  qed
qed (auto simp: compact_closure_of_imp_mtotally_bounded)



lemma compact_closure_of_eq_Bolzano_Weierstrass:
   "compactin mtopology (mtopology closure_of S) \<longleftrightarrow>
    (\<forall>T. infinite T \<and> T \<subseteq> S \<and> T \<subseteq> M \<longrightarrow> mtopology derived_set_of T \<noteq> {})"  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof (intro strip)
    fix T
    assume T: "infinite T \<and> T \<subseteq> S \<and> T \<subseteq> M"
    show "mtopology derived_set_of T \<noteq> {}"
    proof (intro compact_closure_of_imp_Bolzano_Weierstrass)
      show "compactin mtopology (mtopology closure_of S)"
        by (simp add: L)
    qed (use T in auto)
  qed
next
  have "compactin mtopology (mtopology closure_of S)"
    if \<section>: "\<And>T. \<lbrakk>infinite T; T \<subseteq> S\<rbrakk> \<Longrightarrow> mtopology derived_set_of T \<noteq> {}" and "S \<subseteq> M" for S
    unfolding compactin_sequentially
  proof (intro conjI strip)
    show MSM: "mtopology closure_of S \<subseteq> M"
      using closure_of_subset_topspace by fastforce
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume \<sigma>: "range \<sigma> \<subseteq> mtopology closure_of S"
    then have "\<exists>y \<in> S. d (\<sigma> n) y < inverse(Suc n)" for n
      by (simp add: metric_closure_of image_subset_iff) (metis inverse_Suc of_nat_Suc)
    then obtain \<tau> where \<tau>: "\<And>n. \<tau> n \<in> S \<and> d (\<sigma> n) (\<tau> n) < inverse(Suc n)"
      by metis
    then have "range \<tau> \<subseteq> S"
      by blast
    moreover
    have *: "\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> mtopology closure_of S \<inter> mtopology derived_set_of T \<noteq> {}"
      using "\<section>"(1) derived_set_of_mono derived_set_of_subset_closure_of by fastforce
    moreover have "S \<subseteq> mtopology closure_of S"
      by (simp add: \<open>S \<subseteq> M\<close> closure_of_subset)
    ultimately obtain l r where lr:
      "l \<in> mtopology closure_of S" "strict_mono r" "limitin mtopology (\<tau> \<circ> r) l sequentially"
      using Bolzano_Weierstrass_property \<open>S \<subseteq> M\<close> by metis
    then have "l \<in> M"
      using limitin_mspace by blast
    have dr_less: "d ((\<sigma> \<circ> r) n) ((\<tau> \<circ> r) n) < inverse(Suc n)" for n
    proof -
      have "d ((\<sigma> \<circ> r) n) ((\<tau> \<circ> r) n) < inverse(Suc (r n))"
        using \<tau> by auto
      also have "... \<le> inverse(Suc n)"
        using lr strict_mono_imp_increasing by auto
      finally show ?thesis .
    qed
    have "limitin mtopology (\<sigma> \<circ> r) l sequentially"
      unfolding limitin_metric
    proof (intro conjI strip)
      show "l \<in> M"
        using limitin_mspace lr by blast
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then have "\<forall>\<^sub>F n in sequentially. (\<tau> \<circ> r) n \<in> M \<and> d ((\<tau> \<circ> r) n) l < \<epsilon>/2"
        using lr half_gt_zero limitin_metric by blast 
      moreover have "\<forall>\<^sub>F n in sequentially. inverse (real (Suc n)) < \<epsilon>/2"
        using Archimedean_eventually_inverse \<open>0 < \<epsilon>\<close> half_gt_zero by blast
      then have "\<forall>\<^sub>F n in sequentially. d ((\<sigma> \<circ> r) n) ((\<tau> \<circ> r) n) < \<epsilon>/2"
        by eventually_elim (smt (verit, del_insts) dr_less)
      ultimately have "\<forall>\<^sub>F n in sequentially. d ((\<sigma> \<circ> r) n) l < \<epsilon>/2 + \<epsilon>/2"
        by eventually_elim (smt (verit) triangle \<open>l \<in> M\<close> MSM \<sigma> comp_apply order_trans range_subsetD)      
      then show "\<forall>\<^sub>F n in sequentially. (\<sigma> \<circ> r) n \<in> M \<and> d ((\<sigma> \<circ> r) n) l < \<epsilon>"
        apply eventually_elim
        using \<open>mtopology closure_of S \<subseteq> M\<close> \<sigma> by auto
    qed
    with lr show "\<exists>l r. l \<in> mtopology closure_of S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
      by blast
  qed
  then show "?rhs \<Longrightarrow> ?lhs"
    by (metis Int_subset_iff closure_of_restrict inf_le1 topspace_mtopology)
qed

end

lemma (in discrete_metric) mtotally_bounded_discrete_metric:
   "disc.mtotally_bounded S \<longleftrightarrow> finite S \<and> S \<subseteq> M" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof
    show "finite S"
      by (metis (no_types) L closure_of_subset_Int compactin_discrete_topology disc.mtotally_bounded_eq_compact_closure_of
          disc.topspace_mtopology discrete_metric.mcomplete_discrete_metric inf.absorb_iff2 mtopology_discrete_metric finite_subset)
    show "S \<subseteq> M"
      by (simp add: L disc.mtotally_bounded_imp_subset)
  qed
qed (simp add: disc.finite_imp_mtotally_bounded)


context Metric_space
begin

lemma derived_set_of_infinite_openin_metric:
   "mtopology derived_set_of S =
    {x \<in> M. \<forall>U. x \<in> U \<and> openin mtopology U \<longrightarrow> infinite(S \<inter> U)}"
  by (simp add: derived_set_of_infinite_openin Hausdorff_space_mtopology)

lemma derived_set_of_infinite_1: 
  assumes "infinite (S \<inter> mball x \<epsilon>)" 
  shows "infinite (S \<inter> mcball x \<epsilon>)"
  by (meson Int_mono assms finite_subset mball_subset_mcball subset_refl)

lemma derived_set_of_infinite_2:
  assumes "openin mtopology U" "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> infinite (S \<inter> mcball x \<epsilon>)" and "x \<in> U"
  shows "infinite (S \<inter> U)"
  by (metis assms openin_mtopology_mcball finite_Int inf.absorb_iff2 inf_assoc)

lemma derived_set_of_infinite_mball:
  "mtopology derived_set_of S = {x \<in> M. \<forall>e>0. infinite(S \<inter> mball x e)}"
  unfolding derived_set_of_infinite_openin_metric
  by (meson centre_in_mball_iff openin_mball derived_set_of_infinite_1 derived_set_of_infinite_2)

lemma derived_set_of_infinite_mcball:
  "mtopology derived_set_of S = {x \<in> M. \<forall>e>0. infinite(S \<inter> mcball x e)}"
  unfolding derived_set_of_infinite_openin_metric
  by (meson centre_in_mball_iff openin_mball derived_set_of_infinite_1 derived_set_of_infinite_2)

end

subsection\<open>Continuous functions on metric spaces\<close>

context Metric_space
begin

lemma continuous_map_to_metric:
   "continuous_map X mtopology f \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>\<epsilon>>0. \<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. f y \<in> mball (f x) \<epsilon>))"
   (is "?lhs=?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding continuous_map_eq_topcontinuous_at topcontinuous_at_def
    by (metis centre_in_mball_iff openin_mball topspace_mtopology)
next
  assume R: ?rhs
  then have "\<forall>x\<in>topspace X. f x \<in> M"
    by (meson gt_ex in_mball)
  moreover 
  have "\<And>x V. \<lbrakk>x \<in> topspace X; openin mtopology V; f x \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. f y \<in> V)"
    unfolding openin_mtopology by (metis Int_iff R inf.orderE)
  ultimately
  show ?lhs
    by (simp add: continuous_map_eq_topcontinuous_at topcontinuous_at_def)
qed 

lemma continuous_map_from_metric:
   "continuous_map mtopology X f \<longleftrightarrow>
    f ` M \<subseteq> topspace X \<and>
    (\<forall>a \<in> M. \<forall>U. openin X U \<and> f a \<in> U \<longrightarrow> (\<exists>r>0. \<forall>x. x \<in> M \<and> d a x < r \<longrightarrow> f x \<in> U))"
proof (cases "f ` M \<subseteq> topspace X")
  case True
  then show ?thesis
    by (fastforce simp: continuous_map openin_mtopology subset_eq)
next
  case False
  then show ?thesis
    by (simp add: continuous_map_eq_image_closure_subset_gen)
qed

text \<open>An abstract formulation, since the limits do not have to be sequential\<close>
lemma continuous_map_uniform_limit:
  assumes contf: "\<forall>\<^sub>F \<xi> in F. continuous_map X mtopology (f \<xi>)"
    and dfg: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F \<xi> in F. \<forall>x \<in> topspace X. g x \<in> M \<and> d (f \<xi> x) (g x) < \<epsilon>"
    and nontriv: "\<not> trivial_limit F"
  shows "continuous_map X mtopology g"
  unfolding continuous_map_to_metric
proof (intro strip)
  fix x and \<epsilon>::real
  assume "x \<in> topspace X" and "\<epsilon> > 0"
  then obtain \<xi> where k: "continuous_map X mtopology (f \<xi>)" 
    and gM: "\<forall>x \<in> topspace X. g x \<in> M" 
    and third: "\<forall>x \<in> topspace X. d (f \<xi> x) (g x) < \<epsilon>/3"
    using eventually_conj [OF contf] contf dfg [of "\<epsilon>/3"] eventually_happens' [OF nontriv]
    by (smt (verit, ccfv_SIG) zero_less_divide_iff)
  then obtain U where U: "openin X U" "x \<in> U" and Uthird: "\<forall>y\<in>U. d (f \<xi> y) (f \<xi> x) < \<epsilon>/3"
    unfolding continuous_map_to_metric
    by (metis \<open>0 < \<epsilon>\<close> \<open>x \<in> topspace X\<close> commute divide_pos_pos in_mball zero_less_numeral)
  have f_inM: "f \<xi> y \<in> M" if "y\<in>U" for y
    using U k openin_subset that by (fastforce simp: continuous_map_def)
  have "d (g y) (g x) < \<epsilon>" if "y\<in>U" for y
  proof -
    have "g y \<in> M"
      using U gM openin_subset that by blast
    have "d (g y) (g x) \<le> d (g y) (f \<xi> x) + d (f \<xi> x) (g x)"
      by (simp add: U \<open>g y \<in> M\<close> \<open>x \<in> topspace X\<close> f_inM gM triangle)
    also have "\<dots> \<le> d (g y) (f \<xi> y) + d (f \<xi> y) (f \<xi> x) + d (f \<xi> x) (g x)"
      by (simp add: U \<open>g y \<in> M\<close> commute f_inM that triangle')
    also have "\<dots> < \<epsilon>/3 + \<epsilon>/3 + \<epsilon>/3"
      by (smt (verit) U(1) Uthird \<open>x \<in> topspace X\<close> commute openin_subset subsetD that third)
    finally show ?thesis by simp
  qed
  with U gM show "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. g y \<in> mball (g x) \<epsilon>)"
    by (metis commute in_mball in_mono openin_subset)
qed


lemma continuous_map_uniform_limit_alt:
  assumes contf: "\<forall>\<^sub>F \<xi> in F. continuous_map X mtopology (f \<xi>)"
    and gim: "g ` (topspace X) \<subseteq> M"
    and dfg: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F \<xi> in F. \<forall>x \<in> topspace X. d (f \<xi> x) (g x) < \<epsilon>"
    and nontriv: "\<not> trivial_limit F"
  shows "continuous_map X mtopology g"
proof (rule continuous_map_uniform_limit [OF contf])
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  with gim dfg show "\<forall>\<^sub>F \<xi> in F. \<forall>x\<in>topspace X. g x \<in> M \<and> d (f \<xi> x) (g x) < \<epsilon>"
    by (simp add: image_subset_iff)
qed (use nontriv in auto)


lemma continuous_map_uniformly_Cauchy_limit:
  assumes "mcomplete"
  assumes contf: "\<forall>\<^sub>F n in sequentially. continuous_map X mtopology (f n)"
    and Cauchy': "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>m n x. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> x \<in> topspace X \<longrightarrow> d (f m x) (f n x) < \<epsilon>"
  obtains g where
    "continuous_map X mtopology g"
    "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. d (f n x) (g x) < \<epsilon>"
proof -
  have "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>l. limitin mtopology (\<lambda>n. f n x) l sequentially"
    using \<open>mcomplete\<close> [unfolded mcomplete, rule_format] assms
    by (smt (verit) contf continuous_map_def eventually_mono topspace_mtopology)
  then obtain g where g: "\<And>x. x \<in> topspace X \<Longrightarrow> limitin mtopology (\<lambda>n. f n x) (g x) sequentially"
    by metis
  show thesis
  proof
    show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. d (f n x) (g x) < \<epsilon>"
      if "\<epsilon> > 0" for \<epsilon> :: real
    proof -
      obtain N where N: "\<And>m n x. \<lbrakk>N \<le> m; N \<le> n; x \<in> topspace X\<rbrakk> \<Longrightarrow> d (f m x) (f n x) < \<epsilon>/2"
        by (meson Cauchy' \<open>0 < \<epsilon>\<close> half_gt_zero)
      obtain P where P: "\<And>n x. \<lbrakk>n \<ge> P; x \<in> topspace X\<rbrakk> \<Longrightarrow> f n x \<in> M"
        using contf by (auto simp: eventually_sequentially continuous_map_def)
      show ?thesis
      proof (intro eventually_sequentiallyI strip)
        fix n x
        assume "max N P \<le> n" and x: "x \<in> topspace X"
        obtain L where "g x \<in> M" and L: "\<forall>n\<ge>L. f n x \<in> M \<and> d (f n x) (g x) < \<epsilon>/2"
          using g [OF x] \<open>\<epsilon> > 0\<close> unfolding limitin_metric
          by (metis (no_types, lifting) eventually_sequentially half_gt_zero)
        define n' where "n' \<equiv> Max{L,N,P}"
        have L': "\<forall>m \<ge> n'. f m x \<in> M \<and> d (f m x) (g x) < \<epsilon>/2"
          using L by (simp add: n'_def)
        moreover
        have "d (f n x) (f n' x) < \<epsilon>/2"
          using N [of n n' x] \<open>max N P \<le> n\<close> n'_def x by fastforce
        ultimately have "d (f n x) (g x) < \<epsilon>/2 + \<epsilon>/2"
          by (smt (verit, ccfv_SIG) P \<open>g x \<in> M\<close> \<open>max N P \<le> n\<close> le_refl max.bounded_iff mdist_zero triangle' x)
        then show "d (f n x) (g x) < \<epsilon>" by simp
      qed
    qed
    then show "continuous_map X mtopology g"
      by (smt (verit, del_insts) eventually_mono g limitin_mspace trivial_limit_sequentially continuous_map_uniform_limit [OF contf])
  qed
qed

lemma metric_continuous_map:
  assumes "Metric_space M' d'"
  shows
   "continuous_map mtopology (Metric_space.mtopology M' d') f \<longleftrightarrow>
    f ` M \<subseteq> M' \<and> (\<forall>a \<in> M. \<forall>\<epsilon>>0. \<exists>\<delta>>0.  (\<forall>x. x \<in> M \<and> d a x < \<delta> \<longrightarrow> d' (f a) (f x) < \<epsilon>))"
   (is "?lhs = ?rhs")
proof -
  interpret M': Metric_space M' d'
    by (simp add: assms)
  show ?thesis
  proof
    assume L: ?lhs
    show ?rhs
    proof (intro conjI strip)
      show "f ` M \<subseteq> M'"
        using L by (auto simp: continuous_map_def)
      fix a and \<epsilon> :: real
      assume "a \<in> M" and "\<epsilon> > 0"
      then have "openin mtopology {x \<in> M. f x \<in> M'.mball (f a) \<epsilon>}" "f a \<in> M'"
        using L unfolding continuous_map_def by fastforce+
      then obtain \<delta> where "\<delta> > 0" "mball a \<delta> \<subseteq> {x \<in> M. f x \<in> M' \<and> d' (f a) (f x) < \<epsilon>}"
        using \<open>0 < \<epsilon>\<close> \<open>a \<in> M\<close> openin_mtopology by auto
      then show "\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> d a x < \<delta> \<longrightarrow> d' (f a) (f x) < \<epsilon>"
        using \<open>a \<in> M\<close> in_mball by blast
    qed
  next
    assume R: ?rhs    
    show ?lhs
      unfolding continuous_map_def
    proof (intro conjI strip)
      fix U
      assume "openin M'.mtopology U"
      then show "openin mtopology {x \<in> topspace mtopology. f x \<in> U}"
        apply (simp add: continuous_map_def openin_mtopology M'.openin_mtopology subset_iff)
        by (metis R image_subset_iff)
    qed (use R in auto)
  qed
qed

end (*Metric_space*)

end
