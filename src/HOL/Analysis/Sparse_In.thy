theory Sparse_In 
  imports Homotopy

begin

(*TODO: can we remove the definition isolated_points_of from 
  HOL-Complex_Analysis.Complex_Singularities?*)
(*TODO: more lemmas between sparse_in and discrete?*)

subsection \<open>A set of points sparse in another set\<close>

definition sparse_in:: "'a :: topological_space set \<Rightarrow> 'a set \<Rightarrow> bool"
    (infixl \<open>(sparse'_in)\<close> 50)
  where
  "pts sparse_in A = (\<forall>x\<in>A. \<exists>B. x\<in>B \<and> open B \<and> (\<forall>y\<in>B. \<not> y islimpt pts))"

lemma sparse_in_empty[simp]: "{} sparse_in A"
  by (meson UNIV_I empty_iff islimpt_def open_UNIV sparse_in_def)

lemma finite_imp_sparse:
  fixes pts::"'a:: t1_space set"
  shows "finite pts \<Longrightarrow> pts sparse_in S"
  by (meson UNIV_I islimpt_finite open_UNIV sparse_in_def)

lemma sparse_in_singleton[simp]: "{x} sparse_in (A::'a:: t1_space set)"
  by (rule finite_imp_sparse) auto

lemma sparse_in_ball_def:
  "pts sparse_in D \<longleftrightarrow> (\<forall>x\<in>D. \<exists>e>0. \<forall>y\<in>ball x e. \<not> y islimpt pts)"
  unfolding sparse_in_def
  by (meson Elementary_Metric_Spaces.open_ball open_contains_ball_eq subset_eq)

lemma get_sparse_in_cover:
  assumes "pts sparse_in A"
  obtains B where "open B" "A \<subseteq> B" "\<forall>y\<in>B. \<not> y islimpt pts"
proof -
  obtain getB where getB:"x\<in>getB x" "open (getB x)" "\<forall>y\<in>getB x. \<not> y islimpt pts"
    if "x\<in>A" for x
    using assms(1) unfolding sparse_in_def by metis
  define B where "B = Union (getB ` A)"
  have "open B" unfolding B_def using getB(2) by blast
  moreover have "A \<subseteq> B" unfolding B_def using getB(1) by auto
  moreover have "\<forall>y\<in>B. \<not> y islimpt pts" unfolding B_def by (meson UN_iff getB(3))
  ultimately show ?thesis using that by blast
qed

lemma sparse_in_open:
  assumes "open A"
  shows "pts sparse_in A \<longleftrightarrow> (\<forall>y\<in>A. \<not>y islimpt pts)"
  using assms unfolding sparse_in_def by auto

lemma sparse_in_not_in:
  assumes "pts sparse_in A" "x\<in>A"
  obtains B where "open B" "x\<in>B" "\<forall>y\<in>B. y\<noteq>x \<longrightarrow> y\<notin>pts"
  using assms unfolding sparse_in_def
  by (metis islimptI)

lemma sparse_in_subset:
  assumes "pts sparse_in A" "B \<subseteq> A"
  shows "pts sparse_in B"
  using assms unfolding sparse_in_def  by auto

lemma sparse_in_subset2:
  assumes "pts1 sparse_in D" "pts2 \<subseteq> pts1"
  shows "pts2 sparse_in D"
  by (meson assms(1) assms(2) islimpt_subset sparse_in_def)

lemma sparse_in_union:
  assumes "pts1 sparse_in D1" "pts2 sparse_in D1" 
  shows "(pts1 \<union> pts2) sparse_in (D1 \<inter> D2)" 
  using assms unfolding sparse_in_def islimpt_Un
  by (metis Int_iff open_Int)

lemma sparse_in_union': "A sparse_in C \<Longrightarrow> B sparse_in C \<Longrightarrow> A \<union> B sparse_in C"
  using sparse_in_union[of A C B C] by simp

lemma sparse_in_Union_finite:
  assumes "(\<And>A'. A' \<in> A \<Longrightarrow> A' sparse_in B)" "finite A"
  shows   "\<Union>A sparse_in B"
  using assms(2,1) by (induction rule: finite_induct) (auto intro!: sparse_in_union')

lemma sparse_in_UN_finite:
  assumes "(\<And>x. x \<in> A \<Longrightarrow> f x sparse_in B)" "finite A"
  shows   "(\<Union>x\<in>A. f x) sparse_in B"
  by (rule sparse_in_Union_finite) (use assms in auto)

lemma sparse_in_compact_finite:
  assumes "pts sparse_in A" "compact A"
  shows "finite (A \<inter> pts)"
  apply (rule finite_not_islimpt_in_compact[OF \<open>compact A\<close>])
  using assms unfolding sparse_in_def by blast

lemma sparse_imp_closedin_pts:
  assumes "pts sparse_in D" 
  shows "closedin (top_of_set D) (D \<inter> pts)"
  using assms islimpt_subset unfolding closedin_limpt sparse_in_def 
  by fastforce

lemma open_diff_sparse_pts:
  assumes "open D" "pts sparse_in D" 
  shows "open (D - pts)"
  using assms sparse_imp_closedin_pts
  by (metis Diff_Diff_Int Diff_cancel Diff_eq_empty_iff Diff_subset 
      closedin_def double_diff openin_open_eq topspace_euclidean_subtopology)

lemma sparse_in_UNIV_imp_closed: "X sparse_in UNIV \<Longrightarrow> closed X"
  by (simp add: Compl_eq_Diff_UNIV closed_open open_diff_sparse_pts)


lemma sparse_imp_countable:
  fixes D::"'a ::euclidean_space set"
  assumes  "open D" "pts sparse_in D"
  shows "countable (D \<inter> pts)"
proof -
  obtain K :: "nat \<Rightarrow> 'a ::euclidean_space set"
      where K: "D = (\<Union>n. K n)" "\<And>n. compact (K n)"
    using assms  by (metis open_Union_compact_subsets)
  then have "D\<inter> pts = (\<Union>n. K n \<inter> pts)"
    by blast
  moreover have "\<And>n. finite (K n \<inter> pts)"
    by (metis K(1) K(2) Union_iff assms(2) rangeI 
        sparse_in_compact_finite sparse_in_subset subsetI)
  ultimately show ?thesis
    by (metis countableI_type countable_UN countable_finite)
qed

lemma sparse_imp_connected:
  fixes D::"'a ::euclidean_space set"
  assumes  "2 \<le> DIM ('a)"  "connected D" "open D" "pts sparse_in D"
  shows "connected (D - pts)"
  using assms
  by (metis Diff_Compl Diff_Diff_Int Diff_eq connected_open_diff_countable 
      sparse_imp_countable)

lemma sparse_in_eventually_iff:
  assumes "open A"
  shows "pts sparse_in A \<longleftrightarrow> (\<forall>y\<in>A. (\<forall>\<^sub>F y in at y. y \<notin> pts))"
  unfolding sparse_in_open[OF \<open>open A\<close>] islimpt_iff_eventually
  by simp

lemma get_sparse_from_eventually:
  fixes A::"'a::topological_space set"
  assumes "\<forall>x\<in>A. \<forall>\<^sub>F z in at x. P z" "open A"
  obtains pts where "pts sparse_in A" "\<forall>x\<in>A - pts. P x"
proof -
  define pts::"'a set" where "pts={x. \<not>P x}"
  have "pts sparse_in A" "\<forall>x\<in>A - pts. P x"
    unfolding sparse_in_eventually_iff[OF \<open>open A\<close>] pts_def
    using assms(1) by simp_all
  then show ?thesis using that by blast
qed

lemma sparse_disjoint:
  assumes "pts \<inter> A = {}" "open A"
  shows "pts sparse_in A"
  using assms unfolding sparse_in_eventually_iff[OF \<open>open A\<close>]
      eventually_at_topological
  by blast

lemma sparse_in_translate:
  fixes A B :: "'a :: real_normed_vector set"
  assumes "A sparse_in B"
  shows   "(+) c ` A sparse_in (+) c ` B"
  unfolding sparse_in_def
proof safe
  fix x assume "x \<in> B"
  from get_sparse_in_cover[OF assms] obtain B' where B': "open B'" "B \<subseteq> B'" "\<forall>y\<in>B'. \<not>y islimpt A"
    by blast
  have "c + x \<in> (+) c ` B'" "open ((+) c ` B')"
    using B' \<open>x \<in> B\<close> by (auto intro: open_translation)
  moreover have "\<forall>y\<in>(+) c ` B'. \<not>y islimpt ((+) c ` A)"
  proof safe
    fix y assume y: "y \<in> B'" "c + y islimpt (+) c ` A"
    have "(-c) + (c + y) islimpt (+) (-c) ` (+) c ` A"
      by (intro islimpt_isCont_image[OF y(2)] continuous_intros)
         (auto simp: algebra_simps eventually_at_topological)
    hence "y islimpt A"
      by (simp add: image_image)
    with y(1) B' show False
      by blast
  qed
  ultimately show "\<exists>B. c + x \<in> B \<and> open B \<and> (\<forall>y\<in>B. \<not> y islimpt (+) c ` A)"
    by metis
qed

lemma sparse_in_translate':
  fixes A B :: "'a :: real_normed_vector set"
  assumes "A sparse_in B" "C \<subseteq> (+) c ` B"
  shows   "(+) c ` A sparse_in C"
  using sparse_in_translate[OF assms(1)] assms(2) by (rule sparse_in_subset)

lemma sparse_in_translate_UNIV:
  fixes A B :: "'a :: real_normed_vector set"
  assumes "A sparse_in UNIV"
  shows   "(+) c ` A sparse_in UNIV"
  using assms by (rule sparse_in_translate') auto


subsection \<open>Co-sparseness filter\<close>

text \<open>
  The co-sparseness filter allows us to talk about properties that hold on a given set except
  for an ``insignificant'' number of points that are sparse in that set.
\<close>
lemma is_filter_cosparse: "is_filter (\<lambda>P. {x. \<not>P x} sparse_in A)"
proof (standard, goal_cases)
  case 1
  thus ?case by auto
next
  case (2 P Q)
  from sparse_in_union[OF this, of UNIV] show ?case
    by (auto simp: Un_def)
next
  case (3 P Q)
  from 3(2) show ?case
    by (rule sparse_in_subset2) (use 3(1) in auto)
qed  

definition cosparse :: "'a set \<Rightarrow> 'a :: topological_space filter" where
 "cosparse A = Abs_filter (\<lambda>P. {x. \<not>P x} sparse_in A)"

syntax
  "_eventually_cosparse" :: "pttrn => 'a set => bool => bool"  (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<approx>\<close>\<close>\<forall>\<^sub>\<approx>_\<in>_./ _)\<close> [0, 0, 10] 10)
syntax_consts
  "_eventually_cosparse" == eventually
translations
  "\<forall>\<^sub>\<approx>x\<in>A. P" == "CONST eventually (\<lambda>x. P) (CONST cosparse A)"

syntax
  "_eventually_cosparse_UNIV" :: "pttrn => bool => bool"  (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<approx>\<close>\<close>\<forall>\<^sub>\<approx>_./ _)\<close> [0, 10] 10)
syntax_consts
  "_eventually_cosparse_UNIV" == eventually
translations
  "\<forall>\<^sub>\<approx>x. P" == "CONST eventually (\<lambda>x. P) (CONST cosparse CONST UNIV)"

syntax
  "_qeventually_cosparse" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<approx>\<close>\<close>\<forall>\<^sub>\<approx>_ | (_)./ _)\<close> [0, 0, 10] 10)
syntax_consts
  "_qeventually_cosparse" == eventually
translations
  "\<forall>\<^sub>\<approx>x|P. t" => "CONST eventually (\<lambda>x. t) (CONST cosparse {x. P})"
print_translation \<open>
  [(\<^const_syntax>\<open>eventually\<close>, K (Collect_binder_tr' \<^syntax_const>\<open>_qeventually_cosparse\<close>))]
\<close>

lemma eventually_cosparse: "eventually P (cosparse A) \<longleftrightarrow> {x. \<not>P x} sparse_in A"
  unfolding cosparse_def by (rule eventually_Abs_filter[OF is_filter_cosparse])

lemma eventually_not_in_cosparse:
  assumes "X sparse_in A"
  shows   "eventually (\<lambda>x. x \<notin> X) (cosparse A)"
  using assms by (auto simp: eventually_cosparse)

lemma eventually_cosparse_open_eq:
  "open A \<Longrightarrow> eventually P (cosparse A) \<longleftrightarrow> (\<forall>x\<in>A. eventually P (at x))"
  unfolding eventually_cosparse
  by (subst sparse_in_open) (auto simp: islimpt_conv_frequently_at frequently_def)

lemma eventually_cosparse_imp_eventually_at:
  "eventually P (cosparse A) \<Longrightarrow> x \<in> A \<Longrightarrow> eventually P (at x within B)"
  unfolding eventually_cosparse sparse_in_def islimpt_def eventually_at_topological 
  by fastforce

lemma eventually_in_cosparse:
  assumes "A \<subseteq> X" "open A"
  shows   "eventually (\<lambda>x. x \<in> X) (cosparse A)"
proof -
  have "eventually (\<lambda>x. x \<in> A) (cosparse A)"
    using assms by (auto simp: eventually_cosparse_open_eq intro: eventually_at_in_open')
  thus ?thesis
    by eventually_elim (use assms(1) in blast)
qed

lemma cosparse_eq_bot_iff: "cosparse A = bot \<longleftrightarrow> (\<forall>x\<in>A. open {x})"
proof -
  have "cosparse A = bot \<longleftrightarrow> eventually (\<lambda>_. False) (cosparse A)"
    by (simp add: trivial_limit_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>A. open {x})"
    unfolding eventually_cosparse sparse_in_def
    by (auto simp: islimpt_UNIV_iff)
  finally show ?thesis .
qed

lemma cosparse_empty [simp]: "cosparse {} = bot"
  by (rule filter_eqI) (auto simp: eventually_cosparse sparse_in_def)

lemma cosparse_eq_bot_iff' [simp]: "cosparse (A :: 'a :: perfect_space set) = bot \<longleftrightarrow> A = {}"
  by (auto simp: cosparse_eq_bot_iff not_open_singleton)

end