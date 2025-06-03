(*  Title:      HOL/Analysis/Linear_Algebra.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Elementary Linear Algebra on Euclidean Spaces\<close>

theory Linear_Algebra
imports
  Euclidean_Space
  "HOL-Library.Infinite_Set"
begin

lemma linear_simps:
  assumes "bounded_linear f"
  shows
    "f (a + b) = f a + f b"
    "f (a - b) = f a - f b"
    "f 0 = 0"
    "f (- a) = - f a"
    "f (s *\<^sub>R v) = s *\<^sub>R (f v)"
proof -
  interpret f: bounded_linear f by fact
  show "f (a + b) = f a + f b" by (rule f.add)
  show "f (a - b) = f a - f b" by (rule f.diff)
  show "f 0 = 0" by (rule f.zero)
  show "f (- a) = - f a" by (rule f.neg)
  show "f (s *\<^sub>R v) = s *\<^sub>R (f v)" by (rule f.scale)
qed

lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x \<in> (UNIV::'a::finite set)}"
  using finite finite_image_set by blast

lemma substdbasis_expansion_unique:
  includes inner_syntax
  assumes d: "d \<subseteq> Basis"
  shows "(\<Sum>i\<in>d. f i *\<^sub>R i) = (x::'a::euclidean_space) \<longleftrightarrow>
    (\<forall>i\<in>Basis. (i \<in> d \<longrightarrow> f i = x \<bullet> i) \<and> (i \<notin> d \<longrightarrow> x \<bullet> i = 0))"
proof -
  have *: "\<And>x a b P. x * (if P then a else b) = (if P then x * a else x * b)"
    by auto
  have **: "finite d"
    by (auto intro: finite_subset[OF assms])
  have ***: "\<And>i. i \<in> Basis \<Longrightarrow> (\<Sum>i\<in>d. f i *\<^sub>R i) \<bullet> i = (\<Sum>x\<in>d. if x = i then f x else 0)"
    using d
    by (auto intro!: sum.cong simp: inner_Basis inner_sum_left)
  show ?thesis
    unfolding euclidean_eq_iff[where 'a='a] by (auto simp: sum.delta[OF **] ***)
qed

lemma independent_substdbasis: "d \<subseteq> Basis \<Longrightarrow> independent d"
  by (rule independent_mono[OF independent_Basis])

lemma subset_translation_eq [simp]:
    fixes a :: "'a::real_vector" shows "(+) a ` s \<subseteq> (+) a ` t \<longleftrightarrow> s \<subseteq> t"
  by auto

lemma translate_inj_on:
  fixes A :: "'a::ab_group_add set"
  shows "inj_on (\<lambda>x. a + x) A"
  unfolding inj_on_def by auto

lemma translation_assoc:
  fixes a b :: "'a::ab_group_add"
  shows "(\<lambda>x. b + x) ` ((\<lambda>x. a + x) ` S) = (\<lambda>x. (a + b) + x) ` S"
  by auto

lemma translation_invert:
  fixes a :: "'a::ab_group_add"
  assumes "(\<lambda>x. a + x) ` A = (\<lambda>x. a + x) ` B"
  shows "A = B"
  using assms translation_assoc by fastforce

lemma translation_galois:
  fixes a :: "'a::ab_group_add"
  shows "T = ((\<lambda>x. a + x) ` S) \<longleftrightarrow> S = ((\<lambda>x. (- a) + x) ` T)"
  by (metis add.right_inverse group_cancel.rule0 translation_invert translation_assoc)

lemma translation_inverse_subset:
  assumes "((\<lambda>x. - a + x) ` V) \<le> (S :: 'n::ab_group_add set)"
  shows "V \<le> ((\<lambda>x. a + x) ` S)"
  by (metis assms subset_image_iff translation_galois)

subsection\<^marker>\<open>tag unimportant\<close> \<open>More interesting properties of the norm\<close>

unbundle inner_syntax

text\<open>Equality of vectors in terms of \<^term>\<open>(\<bullet>)\<close> products.\<close>

lemma linear_componentwise:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes lf: "linear f"
  shows "(f x) \<bullet> j = (\<Sum>i\<in>Basis. (x\<bullet>i) * (f i\<bullet>j))" (is "?lhs = ?rhs")
proof -
  interpret linear f by fact
  have "?rhs = (\<Sum>i\<in>Basis. (x\<bullet>i) *\<^sub>R (f i))\<bullet>j"
    by (simp add: inner_sum_left)
  then show ?thesis
    by (simp add: euclidean_representation sum[symmetric] scale[symmetric])
qed

lemma vector_eq: "x = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y \<and> y \<bullet> y = x \<bullet> x"
  by (metis (no_types, opaque_lifting) inner_commute inner_diff_right inner_eq_zero_iff right_minus_eq)

lemma norm_triangle_half_r:
  "norm (y - x1) < e/2 \<Longrightarrow> norm (y - x2) < e/2 \<Longrightarrow> norm (x1 - x2) < e"
  using dist_triangle_half_r unfolding dist_norm[symmetric] by auto

lemma norm_triangle_half_l:
  assumes "norm (x - y) < e/2" and "norm (x' - y) < e/2"
  shows "norm (x - x') < e"
  by (metis assms dist_norm dist_triangle_half_l)

lemma abs_triangle_half_r:
  fixes y :: "'a::linordered_field"
  shows "abs (y - x1) < e/2 \<Longrightarrow> abs (y - x2) < e/2 \<Longrightarrow> abs (x1 - x2) < e"
  by linarith

lemma abs_triangle_half_l:
  fixes y :: "'a::linordered_field"
  assumes "abs (x - y) < e/2" and "abs (x' - y) < e/2"
  shows "abs (x - x') < e"
  using assms by linarith

lemma sum_clauses:
  shows "sum f {} = 0"
    and "finite S \<Longrightarrow> sum f (insert x S) = (if x \<in> S then sum f S else f x + sum f S)"
  by (auto simp add: insert_absorb)

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = z" and vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = y"
  by (metis inner_commute vector_eq)+

subsection \<open>Substandard Basis\<close>

lemma ex_card:
  assumes "n \<le> card A"
  shows "\<exists>S\<subseteq>A. card S = n"
  by (meson assms obtain_subset_with_card_n)

lemma subspace_substandard: "subspace {x::'a::euclidean_space. (\<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0)}"
  by (auto simp: subspace_def inner_add_left)

lemma dim_substandard:
  assumes d: "d \<subseteq> Basis"
  shows "dim {x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0} = card d" (is "dim ?A = _")
proof (rule dim_unique)
  from d show "d \<subseteq> ?A"
    by (auto simp: inner_Basis)
  from d show "independent d"
    by (rule independent_mono [OF independent_Basis])
  have "x \<in> span d" if "\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0" for x
  proof -
    have "finite d"
      by (rule finite_subset [OF d finite_Basis])
    then have "(\<Sum>i\<in>d. (x \<bullet> i) *\<^sub>R i) \<in> span d"
      by (simp add: span_sum span_clauses)
    also have "(\<Sum>i\<in>d. (x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i)"
      by (rule sum.mono_neutral_cong_left [OF finite_Basis d]) (auto simp: that)
    finally show "x \<in> span d"
      by (simp only: euclidean_representation)
  qed
  then show "?A \<subseteq> span d" by auto
qed simp


subsection \<open>Orthogonality\<close>

definition\<^marker>\<open>tag important\<close> (in real_inner) "orthogonal x y \<longleftrightarrow> x \<bullet> y = 0"

context real_inner
begin

lemma orthogonal_self: "orthogonal x x \<longleftrightarrow> x = 0"
  by (simp add: orthogonal_def)

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x \<Longrightarrow> orthogonal a (c *\<^sub>R x)"
  "orthogonal a x \<Longrightarrow> orthogonal a (- x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a \<Longrightarrow> orthogonal (c *\<^sub>R x) a"
  "orthogonal x a \<Longrightarrow> orthogonal (- x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x - y) a"
  unfolding orthogonal_def inner_add inner_diff by auto

end

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  by (simp add: orthogonal_def inner_commute)

lemma orthogonal_scaleR [simp]: "c \<noteq> 0 \<Longrightarrow> orthogonal (c *\<^sub>R x) = orthogonal x"
  by (rule ext) (simp add: orthogonal_def)

lemma pairwise_ortho_scaleR:
    "pairwise (\<lambda>i j. orthogonal (f i) (g j)) B
    \<Longrightarrow> pairwise (\<lambda>i j. orthogonal (a i *\<^sub>R f i) (a j *\<^sub>R g j)) B"
  by (auto simp: pairwise_def orthogonal_clauses)

lemma orthogonal_rvsum:
    "\<lbrakk>finite s; \<And>y. y \<in> s \<Longrightarrow> orthogonal x (f y)\<rbrakk> \<Longrightarrow> orthogonal x (sum f s)"
  by (induction s rule: finite_induct) (auto simp: orthogonal_clauses)

lemma orthogonal_lvsum:
    "\<lbrakk>finite s; \<And>x. x \<in> s \<Longrightarrow> orthogonal (f x) y\<rbrakk> \<Longrightarrow> orthogonal (sum f s) y"
  by (induction s rule: finite_induct) (auto simp: orthogonal_clauses)

lemma norm_add_Pythagorean:
  assumes "orthogonal a b"
    shows "(norm (a + b))\<^sup>2 = (norm a)\<^sup>2 + (norm b)\<^sup>2"
proof -
  from assms have "(a - (0 - b)) \<bullet> (a - (0 - b)) = a \<bullet> a - (0 - b \<bullet> b)"
    by (simp add: algebra_simps orthogonal_def inner_commute)
  then show ?thesis
    by (simp add: power2_norm_eq_inner)
qed

lemma norm_sum_Pythagorean:
  assumes "finite I" "pairwise (\<lambda>i j. orthogonal (f i) (f j)) I"
    shows "(norm (sum f I))\<^sup>2 = (\<Sum>i\<in>I. (norm (f i))\<^sup>2)"
using assms
proof (induction I rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert x I)
  then have "orthogonal (f x) (sum f I)"
    by (metis pairwise_insert orthogonal_rvsum)
  with insert show ?case
    by (simp add: pairwise_insert norm_add_Pythagorean)
qed


subsection  \<open>Orthogonality of a transformation\<close>

definition\<^marker>\<open>tag important\<close>  "orthogonal_transformation f \<longleftrightarrow> linear f \<and> (\<forall>v w. f v \<bullet> f w = v \<bullet> w)"

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation:
  "orthogonal_transformation f \<longleftrightarrow> linear f \<and> (\<forall>v. norm (f v) = norm v)"
  by (smt (verit, ccfv_threshold) dot_norm linear_add norm_eq_sqrt_inner orthogonal_transformation_def)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_id [simp]: "orthogonal_transformation (\<lambda>x. x)"
  by (simp add: linear_iff orthogonal_transformation_def)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_orthogonal_transformation:
    "orthogonal_transformation f \<Longrightarrow> orthogonal (f x) (f y) \<longleftrightarrow> orthogonal x y"
  by (simp add: orthogonal_def orthogonal_transformation_def)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_compose:
   "\<lbrakk>orthogonal_transformation f; orthogonal_transformation g\<rbrakk> \<Longrightarrow> orthogonal_transformation(f \<circ> g)"
  by (auto simp: orthogonal_transformation_def linear_compose)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_neg:
  "orthogonal_transformation(\<lambda>x. -(f x)) \<longleftrightarrow> orthogonal_transformation f"
  by (auto simp: orthogonal_transformation_def dest: linear_compose_neg)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_scaleR: "orthogonal_transformation f \<Longrightarrow> f (c *\<^sub>R v) = c *\<^sub>R f v"
  by (simp add: linear_iff orthogonal_transformation_def)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_linear:
   "orthogonal_transformation f \<Longrightarrow> linear f"
  by (simp add: orthogonal_transformation_def)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_inj:
  "orthogonal_transformation f \<Longrightarrow> inj f"
  unfolding orthogonal_transformation_def inj_on_def
  by (metis vector_eq)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_surj:
  "orthogonal_transformation f \<Longrightarrow> surj f"
  for f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  by (simp add: linear_injective_imp_surjective orthogonal_transformation_inj orthogonal_transformation_linear)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_bij:
  "orthogonal_transformation f \<Longrightarrow> bij f"
  for f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  by (simp add: bij_def orthogonal_transformation_inj orthogonal_transformation_surj)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_inv:
  "orthogonal_transformation f \<Longrightarrow> orthogonal_transformation (inv f)"
  for f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  by (metis (no_types, opaque_lifting) bijection.inv_right bijection_def inj_linear_imp_inv_linear orthogonal_transformation orthogonal_transformation_bij orthogonal_transformation_inj)

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_norm:
  "orthogonal_transformation f \<Longrightarrow> norm (f x) = norm x"
  by (metis orthogonal_transformation)


subsection \<open>Bilinear functions\<close>

definition\<^marker>\<open>tag important\<close>
bilinear :: "('a::real_vector \<Rightarrow> 'b::real_vector \<Rightarrow> 'c::real_vector) \<Rightarrow> bool" where
"bilinear f \<longleftrightarrow> (\<forall>x. linear (\<lambda>y. f x y)) \<and> (\<forall>y. linear (\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h \<Longrightarrow> h (x + y) z = h x z + h y z"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_radd: "bilinear h \<Longrightarrow> h x (y + z) = h x y + h x z"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_times:
  fixes c::"'a::real_algebra" shows "bilinear (\<lambda>x y::'a. x*y)"
  by (auto simp: bilinear_def distrib_left distrib_right intro!: linearI)

lemma bilinear_lmul: "bilinear h \<Longrightarrow> h (c *\<^sub>R x) y = c *\<^sub>R h x y"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_rmul: "bilinear h \<Longrightarrow> h x (c *\<^sub>R y) = c *\<^sub>R h x y"
  by (simp add: bilinear_def linear_iff)

lemma bilinear_lneg: "bilinear h \<Longrightarrow> h (- x) y = - h x y"
  by (drule bilinear_lmul [of _ "- 1"]) simp

lemma bilinear_rneg: "bilinear h \<Longrightarrow> h x (- y) = - h x y"
  by (drule bilinear_rmul [of _ _ "- 1"]) simp

lemma (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  using add_left_imp_eq[of x y 0] by auto

lemma bilinear_lzero:
  assumes "bilinear h"
  shows "h 0 x = 0"
  using bilinear_ladd [OF assms, of 0 0 x] by (simp add: eq_add_iff field_simps)

lemma bilinear_rzero:
  assumes "bilinear h"
  shows "h x 0 = 0"
  using bilinear_radd [OF assms, of x 0 0 ] by (simp add: eq_add_iff field_simps)

lemma bilinear_lsub: "bilinear h \<Longrightarrow> h (x - y) z = h x z - h y z"
  using bilinear_ladd [of h x "- y"] by (simp add: bilinear_lneg)

lemma bilinear_rsub: "bilinear h \<Longrightarrow> h z (x - y) = h z x - h z y"
  using bilinear_radd [of h _ x "- y"] by (simp add: bilinear_rneg)

lemma bilinear_sum:
  assumes "bilinear h"
  shows "h (sum f S) (sum g T) = sum (\<lambda>(i,j). h (f i) (g j)) (S \<times> T) "
proof -
  interpret l: linear "\<lambda>x. h x y" for y using assms by (simp add: bilinear_def)
  interpret r: linear "\<lambda>y. h x y" for x using assms by (simp add: bilinear_def)
  have "h (sum f S) (sum g T) = sum (\<lambda>x. h (f x) (sum g T)) S"
    by (simp add: l.sum)
  also have "\<dots> = sum (\<lambda>x. sum (\<lambda>y. h (f x) (g y)) T) S"
    by (rule sum.cong) (simp_all add: r.sum)
  finally show ?thesis
    unfolding sum.cartesian_product .
qed


subsection \<open>Adjoints\<close>

definition\<^marker>\<open>tag important\<close> adjoint :: "(('a::real_inner) \<Rightarrow> ('b::real_inner)) \<Rightarrow> 'b \<Rightarrow> 'a" where
"adjoint f = (SOME f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y)"

lemma adjoint_unique:
  assumes "\<forall>x y. inner (f x) y = inner x (g y)"
  shows "adjoint f = g"
  unfolding adjoint_def
proof (rule some_equality)
  show "\<forall>x y. inner (f x) y = inner x (g y)"
    by (rule assms)
next
  fix h
  assume "\<forall>x y. inner (f x) y = inner x (h y)"
  then show "h = g"
    by (metis assms ext vector_eq_ldot) 
qed

text \<open>TODO: The following lemmas about adjoints should hold for any
  Hilbert space (i.e. complete inner product space).
  (see \<^url>\<open>https://en.wikipedia.org/wiki/Hermitian_adjoint\<close>)
\<close>

lemma adjoint_works:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
proof -
  interpret linear f by fact
  have "\<forall>y. \<exists>w. \<forall>x. f x \<bullet> y = x \<bullet> w"
  proof (intro allI exI)
    fix y :: "'m" and x
    let ?w = "(\<Sum>i\<in>Basis. (f i \<bullet> y) *\<^sub>R i) :: 'n"
    have "f x \<bullet> y = f (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i) \<bullet> y"
      by (simp add: euclidean_representation)
    also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) \<bullet> y"
      by (simp add: sum scale)
    finally show "f x \<bullet> y = x \<bullet> ?w"
      by (simp add: inner_sum_left inner_sum_right mult.commute)
  qed
  then show ?thesis
    unfolding adjoint_def choice_iff
    by (intro someI2_ex[where Q="\<lambda>f'. x \<bullet> f' y = f x \<bullet> y"]) auto
qed

lemma adjoint_clauses:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
    and "adjoint f y \<bullet> x = y \<bullet> f x"
  by (simp_all add: adjoint_works[OF lf] inner_commute)

lemma adjoint_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "linear (adjoint f)"
  by (simp add: lf linear_iff euclidean_eq_iff[where 'a='n] euclidean_eq_iff[where 'a='m]
    adjoint_clauses[OF lf] inner_distrib)

lemma adjoint_adjoint:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "adjoint (adjoint f) = f"
  by (rule adjoint_unique, simp add: adjoint_clauses [OF lf])


subsection\<^marker>\<open>tag unimportant\<close> \<open>Euclidean Spaces as Typeclass\<close>

lemma independent_Basis: "independent Basis"
  by (rule independent_Basis)

lemma span_Basis [simp]: "span Basis = UNIV"
  by (rule span_Basis)

lemma in_span_Basis: "x \<in> span Basis"
  unfolding span_Basis ..

lemma representation_euclidean_space:
  "representation Basis x = (\<lambda>b. if b \<in> Basis then inner x b else 0)"
proof (rule representation_eqI)
  have "(\<Sum>b | (if b \<in> Basis then inner x b else 0) \<noteq> 0. (if b \<in> Basis then inner x b else 0) *\<^sub>R b) =
          (\<Sum>b\<in>Basis. inner x b *\<^sub>R b)"
    by (intro sum.mono_neutral_cong_left) auto
  also have "\<dots> = x"
    by (simp add: euclidean_representation)
  finally show "(\<Sum>b | (if b \<in> Basis then inner x b else 0) \<noteq> 0.
                  (if b \<in> Basis then inner x b else 0) *\<^sub>R b) = x" .
qed (insert independent_Basis span_Basis, auto split: if_splits)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Linearity and Bilinearity continued\<close>

lemma linear_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
proof
  interpret linear f by fact
  let ?B = "\<Sum>b\<in>Basis. norm (f b)"
  show "\<forall>x. norm (f x) \<le> ?B * norm x"
  proof
    fix x :: 'a
    let ?g = "\<lambda>b. (x \<bullet> b) *\<^sub>R f b"
    have "norm (f x) = norm (f (\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b))"
      unfolding euclidean_representation ..
    also have "\<dots> = norm (sum ?g Basis)"
      by (simp add: sum scale)
    finally have th0: "norm (f x) = norm (sum ?g Basis)" .
    have th: "norm (?g i) \<le> norm (f i) * norm x" if "i \<in> Basis" for i
    proof -
      from Basis_le_norm[OF that, of x]
      show "norm (?g i) \<le> norm (f i) * norm x"
        unfolding norm_scaleR by (metis mult.commute mult_left_mono norm_ge_zero)
    qed
    from sum_norm_le[of _ ?g, OF th]
    show "norm (f x) \<le> ?B * norm x"
      by (simp add: sum_distrib_right th0)
  qed
qed

lemma linear_conv_bounded_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<longleftrightarrow> bounded_linear f"
  by (metis mult.commute bounded_linear_axioms.intro bounded_linear_def linear_bounded)

lemmas linear_linear = linear_conv_bounded_linear[symmetric]

lemma inj_linear_imp_inv_bounded_linear:
  fixes f::"'a::euclidean_space \<Rightarrow> 'a"
  shows "\<lbrakk>bounded_linear f; inj f\<rbrakk> \<Longrightarrow> bounded_linear (inv f)"
  by (simp add: inj_linear_imp_inv_linear linear_linear)

lemma linear_bounded_pos:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
 obtains B where "B > 0" "\<And>x. norm (f x) \<le> B * norm x"
  by (metis bounded_linear.pos_bounded lf linear_linear mult.commute)

lemma linear_invertible_bounded_below_pos:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "linear g" and gf: "g \<circ> f = id"
  obtains B where "B > 0" "\<And>x. B * norm x \<le> norm(f x)"
proof -
  obtain B where "B > 0" and B: "\<And>x. norm (g x) \<le> B * norm x"
    using linear_bounded_pos [OF \<open>linear g\<close>] by blast
  show thesis
  proof
    show "0 < 1/B"
      by (simp add: \<open>B > 0\<close>)
    show "1/B * norm x \<le> norm (f x)" for x
      by (smt (verit, ccfv_SIG) B \<open>0 < B\<close> gf comp_apply divide_inverse id_apply inverse_eq_divide 
              less_divide_eq mult.commute)
  qed
qed

lemma linear_inj_bounded_below_pos:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  obtains B where "B > 0" "\<And>x. B * norm x \<le> norm(f x)"
  using linear_injective_left_inverse [OF assms]
    linear_invertible_bounded_below_pos assms by blast

lemma bounded_linearI':
  fixes f ::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "bounded_linear f"
  using assms linearI linear_conv_bounded_linear by blast

lemma bilinear_bounded:
  fixes h :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'k::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof (clarify intro!: exI[of _ "\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. norm (h i j)"])
  fix x :: 'm
  fix y :: 'n
  have "norm (h x y) = norm (h (sum (\<lambda>i. (x \<bullet> i) *\<^sub>R i) Basis) (sum (\<lambda>i. (y \<bullet> i) *\<^sub>R i) Basis))"
    by (simp add: euclidean_representation)
  also have "\<dots> = norm (sum (\<lambda> (i,j). h ((x \<bullet> i) *\<^sub>R i) ((y \<bullet> j) *\<^sub>R j)) (Basis \<times> Basis))"
    unfolding bilinear_sum[OF bh] ..
  finally have th: "norm (h x y) = \<dots>" .
  have "\<And>i j. \<lbrakk>i \<in> Basis; j \<in> Basis\<rbrakk>
           \<Longrightarrow> \<bar>x \<bullet> i\<bar> * (\<bar>y \<bullet> j\<bar> * norm (h i j)) \<le> norm x * (norm y * norm (h i j))"
    by (auto simp add: zero_le_mult_iff Basis_le_norm mult_mono)
  then show "norm (h x y) \<le> (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. norm (h i j)) * norm x * norm y"
    unfolding sum_distrib_right th sum.cartesian_product
    by (clarsimp simp add: bilinear_rmul[OF bh] bilinear_lmul[OF bh]
      field_simps simp del: scaleR_scaleR intro!: sum_norm_le)
qed

lemma bilinear_conv_bounded_bilinear:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  shows "bilinear h \<longleftrightarrow> bounded_bilinear h"
proof
  assume "bilinear h"
  show "bounded_bilinear h"
  proof
    fix x y z
    show "h (x + y) z = h x z + h y z"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff by simp
  next
    fix x y z
    show "h x (y + z) = h x y + h x z"
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff by simp
  next
    show "h (scaleR r x) y = scaleR r (h x y)" "h x (scaleR r y) = scaleR r (h x y)" for r x y
      using \<open>bilinear h\<close> unfolding bilinear_def linear_iff
      by simp_all
  next
    have "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
      using \<open>bilinear h\<close> by (rule bilinear_bounded)
    then show "\<exists>K. \<forall>x y. norm (h x y) \<le> norm x * norm y * K"
      by (simp add: ac_simps)
  qed
next
  assume "bounded_bilinear h"
  then interpret h: bounded_bilinear h .
  show "bilinear h"
    unfolding bilinear_def linear_conv_bounded_linear
    using h.bounded_linear_left h.bounded_linear_right by simp
qed

lemma bilinear_bounded_pos:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
  by (metis mult.assoc bh bilinear_conv_bounded_bilinear bounded_bilinear.pos_bounded mult.commute)

lemma bounded_linear_imp_has_derivative: 
  "bounded_linear f \<Longrightarrow> (f has_derivative f) net"
  by (auto simp add: has_derivative_def linear_diff linear_linear linear_def
      dest: bounded_linear.linear)

lemma linear_imp_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> (f has_derivative f) net"
  by (simp add: bounded_linear_imp_has_derivative linear_conv_bounded_linear)

lemma bounded_linear_imp_differentiable: "bounded_linear f \<Longrightarrow> f differentiable net"
  using bounded_linear_imp_has_derivative differentiable_def by blast

lemma linear_imp_differentiable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable net"
  by (metis linear_imp_has_derivative differentiable_def)

lemma of_real_differentiable [simp,derivative_intros]: "of_real differentiable F"
  by (simp add: bounded_linear_imp_differentiable bounded_linear_of_real)

lemma bounded_linear_representation:
  fixes B :: "'a :: euclidean_space set"
  assumes "independent B" "span B = UNIV"
  shows   "bounded_linear (\<lambda>v. representation B v b)"
proof -
  have "Vector_Spaces.linear (*\<^sub>R) (*) (\<lambda>v. representation B v b)"
    by (rule real_vector.linear_representation) fact+
  then have "linear (\<lambda>v. representation B v b)"
    unfolding linear_def real_scaleR_def [abs_def] .
  thus ?thesis
    by (simp add: linear_conv_bounded_linear)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>We continue\<close>

lemma independent_bound:
  fixes S :: "'a::euclidean_space set"
  shows "independent S \<Longrightarrow> finite S \<and> card S \<le> DIM('a)"
  by (metis dim_subset_UNIV finiteI_independent dim_span_eq_card_independent)

lemmas independent_imp_finite = finiteI_independent

corollary\<^marker>\<open>tag unimportant\<close> independent_card_le:
  fixes S :: "'a::euclidean_space set"
  assumes "independent S"
  shows "card S \<le> DIM('a)"
  using assms independent_bound by auto

lemma dependent_biggerset:
  fixes S :: "'a::euclidean_space set"
  shows "(finite S \<Longrightarrow> card S > DIM('a)) \<Longrightarrow> dependent S"
  by (metis independent_bound not_less)

text \<open>Picking an orthogonal replacement for a spanning set.\<close>

lemma vector_sub_project_orthogonal:
  fixes b x :: "'a::euclidean_space"
  shows "b \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *\<^sub>R b) = 0"
  unfolding inner_simps by auto

lemma pairwise_orthogonal_insert:
  assumes "pairwise orthogonal S"
    and "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
  shows "pairwise orthogonal (insert x S)"
  using assms by (auto simp: pairwise_def orthogonal_commute)

lemma basis_orthogonal:
  fixes B :: "'a::real_inner set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
  using fB
proof (induct rule: finite_induct)
  case empty
  then show ?case
    using pairwise_empty by blast
next
  case (insert a B)
  note fB = \<open>finite B\<close> and aB = \<open>a \<notin> B\<close>
  from \<open>\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C\<close>
  obtain C where C: "finite C" "card C \<le> card B"
    "span C = span B" "pairwise orthogonal C" by blast
  let ?a = "a - sum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C"
    by simp
  have cC: "card ?C \<le> card (insert a B)"
    using C aB card_insert_if local.insert(1) by fastforce
  {
    fix x k
    have th0: "\<And>(a::'a) b c. a - (b - c) = c + (a - b)"
      by (simp add: field_simps)
    have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x)) \<in> span C \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
      unfolding scaleR_right_diff_distrib th0
      by (intro span_add_eq span_scale span_sum span_base)
  }
  then have SC: "span ?C = span (insert a B)"
    unfolding set_eq_iff span_breakdown_eq C(3)[symmetric] by auto
  {
    fix y
    assume yC: "y \<in> C"
    then have Cy: "C = insert y (C - {y})"
      by blast
    have fth: "finite (C - {y})"
      using C by simp
    have "y \<noteq> 0 \<Longrightarrow> \<forall>x\<in>C - {y}. x \<bullet> a * (x \<bullet> y) / (x \<bullet> x) = 0"
      using \<open>pairwise orthogonal C\<close>
      by (metis Cy DiffE div_0 insertCI mult_zero_right orthogonal_def pairwise_insert)
    then have "orthogonal ?a y"
      unfolding orthogonal_def
      unfolding inner_diff inner_sum_left right_minus_eq
      unfolding sum.remove [OF \<open>finite C\<close> \<open>y \<in> C\<close>]
      by (auto simp add: sum.neutral inner_commute[of y a])
  }
  with \<open>pairwise orthogonal C\<close> have CPO: "pairwise orthogonal ?C"
    by (rule pairwise_orthogonal_insert)
  from fC cC SC CPO have "?P (insert a B) ?C"
    by blast
  then show ?case by blast
qed

lemma orthogonal_basis_exists:
  fixes V :: "('a::euclidean_space) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and> (card B = dim V) \<and> pairwise orthogonal B"
proof -
  from basis_exists[of V] obtain B where
    B: "B \<subseteq> V" "independent B" "V \<subseteq> span B" "card B = dim V"
    by force
  from B have fB: "finite B" "card B = dim V"
    using independent_bound by auto
  from basis_orthogonal[OF fB(1)] obtain C where
    C: "finite C" "card C \<le> card B" "span C = span B" "pairwise orthogonal C"
    by blast
  from C B have CSV: "C \<subseteq> span V"
    by (metis span_superset span_mono subset_trans)
  from span_mono[OF B(3)] C have SVC: "span V \<subseteq> span C"
    by (simp add: span_span)
  from C fB have "card C \<le> dim V"
    by simp
  moreover have "dim V \<le> card C"
    using span_card_ge_dim[OF CSV SVC C(1)]
    by simp
  ultimately have "card C = dim V"
    using C(1) by simp
  with C B CSV show ?thesis
    by (metis SVC card_eq_dim dim_span)
qed

text \<open>Low-dimensional subset is in a hyperplane (weak orthogonal complement).\<close>

lemma span_not_UNIV_orthogonal:
  fixes S :: "'a::euclidean_space set"
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
proof -
  from sU obtain a where a: "a \<notin> span S"
    by blast
  from orthogonal_basis_exists obtain B where
    B: "independent B" "B \<subseteq> span S" "S \<subseteq> span B" "card B = dim S" "pairwise orthogonal B"
    by blast
  from B have fB: "finite B" "card B = dim S"
    using independent_bound by auto
  have sSB: "span S = span B"
    by (simp add: B span_eq)
  let ?a = "a - sum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B"
  have "sum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B \<in> span S"
    by (simp add: sSB span_base span_mul span_sum)
  with a have a0:"?a  \<noteq> 0"
    by auto
  have "?a \<bullet> x = 0" if "x\<in>span B" for x
  proof (rule span_induct [OF that])
    show "subspace {x. ?a \<bullet> x = 0}"
      by (auto simp add: subspace_def inner_add)
  next
    {
      fix x
      assume x: "x \<in> B"
      from x have B': "B = insert x (B - {x})"
        by blast
      have fth: "finite (B - {x})"
        using fB by simp
      have "(\<Sum>b\<in>B - {x}. a \<bullet> b * (b \<bullet> x) / (b \<bullet> b)) = 0" if "x \<noteq> 0"
        by (smt (verit) B' B(5) DiffD2 divide_eq_0_iff inner_real_def inner_zero_right insertCI orthogonal_def pairwise_insert sum.neutral)
      then have "?a \<bullet> x = 0"
        apply (subst B')
        using fB fth
        unfolding sum_clauses(2)[OF fth]
        by (auto simp add: inner_add_left inner_diff_left inner_sum_left)
    }
    then show "?a \<bullet> x = 0" if "x \<in> B" for x
      using that by blast
    qed
  with a0 sSB show ?thesis
    by blast
qed

lemma span_not_univ_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes SU: "span S \<noteq> UNIV"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using span_not_UNIV_orthogonal[OF SU] by auto

lemma lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes d: "dim S < DIM('a)"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using d dim_eq_full nless_le span_not_univ_subset_hyperplane by blast

lemma linear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> _"
  assumes lf: "linear f"
    and lg: "linear g"
    and fg: "\<And>b. b \<in> Basis \<Longrightarrow> f b = g b"
  shows "f = g"
  using linear_eq_on_span[OF lf lg, of Basis] fg by auto


text \<open>Similar results for bilinear functions.\<close>

lemma bilinear_eq:
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and SB: "S \<subseteq> span B"
    and TC: "T \<subseteq> span C"
    and "x\<in>S" "y\<in>T"
    and fg: "\<And>x y. \<lbrakk>x \<in> B; y\<in> C\<rbrakk> \<Longrightarrow> f x y = g x y"
  shows "f x y = g x y"
proof -
  let ?P = "{x. \<forall>y\<in> span C. f x y = g x y}"
  from bf bg have sp: "subspace ?P"
    unfolding bilinear_def linear_iff subspace_def bf bg
    by (auto simp add: span_zero bilinear_lzero[OF bf] bilinear_lzero[OF bg]
        span_add Ball_def
      intro: bilinear_ladd[OF bf])
  have sfg: "\<And>x. x \<in> B \<Longrightarrow> subspace {a. f x a = g x a}"
    by (auto simp: subspace_def bf bg bilinear_rzero bilinear_radd bilinear_rmul)
  have "\<forall>y\<in> span C. f x y = g x y" if "x \<in> span B" for x
    using span_induct [OF that sp] fg sfg span_induct by blast
  then show ?thesis
    using SB TC assms by auto
qed

lemma bilinear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> _"
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and fg: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> f i j = g i j"
  shows "f = g"
  using bilinear_eq[OF bf bg equalityD2[OF span_Basis] equalityD2[OF span_Basis]] fg by blast


subsection \<open>Infinity norm\<close>

definition\<^marker>\<open>tag important\<close> "infnorm (x::'a::euclidean_space) = Sup {\<bar>x \<bullet> b\<bar> |b. b \<in> Basis}"

lemma infnorm_set_image:
  fixes x :: "'a::euclidean_space"
  shows "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} = (\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  by blast

lemma infnorm_Max:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis)"
  by (simp add: infnorm_def infnorm_set_image cSup_eq_Max)

lemma infnorm_set_lemma:
  fixes x :: "'a::euclidean_space"
  shows "finite {\<bar>x \<bullet> i\<bar> |i. i \<in> Basis}"
    and "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} \<noteq> {}"
  unfolding infnorm_set_image by auto

lemma infnorm_pos_le:
  fixes x :: "'a::euclidean_space"
  shows "0 \<le> infnorm x"
  by (simp add: infnorm_Max Max_ge_iff ex_in_conv)

lemma infnorm_triangle:
  fixes x :: "'a::euclidean_space"
  shows "infnorm (x + y) \<le> infnorm x + infnorm y"
proof -
  have *: "\<And>a b c d :: real. \<bar>a\<bar> \<le> c \<Longrightarrow> \<bar>b\<bar> \<le> d \<Longrightarrow> \<bar>a + b\<bar> \<le> c + d"
    by simp
  show ?thesis
    by (auto simp: infnorm_Max inner_add_left intro!: *)
qed

lemma infnorm_eq_0:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = 0 \<longleftrightarrow> x = 0"
proof -
  have "infnorm x \<le> 0 \<longleftrightarrow> x = 0"
    unfolding infnorm_Max by (simp add: euclidean_all_zero_iff)
  then show ?thesis
    using infnorm_pos_le[of x] by simp
qed

lemma infnorm_0: "infnorm 0 = 0"
  by (simp add: infnorm_eq_0)

lemma infnorm_neg: "infnorm (- x) = infnorm x"
  unfolding infnorm_def by simp

lemma infnorm_sub: "infnorm (x - y) = infnorm (y - x)"
  by (metis infnorm_neg minus_diff_eq)

lemma absdiff_infnorm: "\<bar>infnorm x - infnorm y\<bar> \<le> infnorm (x - y)"
  by (smt (verit, del_insts) diff_add_cancel infnorm_sub infnorm_triangle)

lemma real_abs_infnorm: "\<bar>infnorm x\<bar> = infnorm x"
  using infnorm_pos_le[of x] by arith

lemma Basis_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "b \<in> Basis \<Longrightarrow> \<bar>x \<bullet> b\<bar> \<le> infnorm x"
  by (simp add: infnorm_Max)

lemma infnorm_mul: "infnorm (a *\<^sub>R x) = \<bar>a\<bar> * infnorm x"
  unfolding infnorm_Max
proof (safe intro!: Max_eqI)
  let ?B = "(\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  { fix b :: 'a
    assume "b \<in> Basis"
    then show "\<bar>a *\<^sub>R x \<bullet> b\<bar> \<le> \<bar>a\<bar> * Max ?B"
      by (simp add: abs_mult mult_left_mono)
  next
    from Max_in[of ?B] obtain b where "b \<in> Basis" "Max ?B = \<bar>x \<bullet> b\<bar>"
      by (auto simp del: Max_in)
    then show "\<bar>a\<bar> * Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis) \<in> (\<lambda>i. \<bar>a *\<^sub>R x \<bullet> i\<bar>) ` Basis"
      by (intro image_eqI[where x=b]) (auto simp: abs_mult)
  }
qed simp

lemma infnorm_mul_lemma: "infnorm (a *\<^sub>R x) \<le> \<bar>a\<bar> * infnorm x"
  unfolding infnorm_mul ..

lemma infnorm_pos_lt: "infnorm x > 0 \<longleftrightarrow> x \<noteq> 0"
  using infnorm_pos_le[of x] infnorm_eq_0[of x] by arith

text \<open>Prove that it differs only up to a bound from Euclidean norm.\<close>

lemma infnorm_le_norm: "infnorm x \<le> norm x"
  by (simp add: Basis_le_norm infnorm_Max)

lemma norm_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "norm x \<le> sqrt DIM('a) * infnorm x"
  unfolding norm_eq_sqrt_inner id_def
proof (rule real_le_lsqrt)
  show "sqrt DIM('a) * infnorm x \<ge> 0"
    by (simp add: zero_le_mult_iff infnorm_pos_le)
  have "x \<bullet> x \<le> (\<Sum>b\<in>Basis. x \<bullet> b * (x \<bullet> b))"
    by (metis euclidean_inner order_refl)
  also have "\<dots> \<le> DIM('a) * \<bar>infnorm x\<bar>\<^sup>2"
    by (rule sum_bounded_above) (metis Basis_le_infnorm abs_le_square_iff power2_eq_square real_abs_infnorm)
  also have "\<dots> \<le> (sqrt DIM('a) * infnorm x)\<^sup>2"
    by (simp add: power_mult_distrib)
  finally show "x \<bullet> x \<le> (sqrt DIM('a) * infnorm x)\<^sup>2" .
qed

lemma tendsto_infnorm [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F"
  shows "((\<lambda>x. infnorm (f x)) \<longlongrightarrow> infnorm a) F"
proof (rule tendsto_compose [OF LIM_I assms])
  fix r :: real
  assume "r > 0"
  then show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (infnorm x - infnorm a) < r"
    by (metis real_norm_def le_less_trans absdiff_infnorm infnorm_le_norm)
qed

text \<open>Equality in Cauchy-Schwarz and triangle inequalities.\<close>

lemma norm_cauchy_schwarz_eq: "x \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "x=0")
  case True
  then show ?thesis
    by auto
next
  case False 
  from inner_eq_zero_iff[of "norm y *\<^sub>R x - norm x *\<^sub>R y"]
  have "?rhs \<longleftrightarrow>
      (norm y * (norm y * norm x * norm x - norm x * (x \<bullet> y)) -
        norm x * (norm y * (y \<bullet> x) - norm x * norm y * norm y) = 0)"
    using False unfolding inner_simps
    by (auto simp add: power2_norm_eq_inner[symmetric] power2_eq_square inner_commute field_simps)
  also have "\<dots> \<longleftrightarrow> (2 * norm x * norm y * (norm x * norm y - x \<bullet> y) = 0)"
    using False  by (simp add: field_simps inner_commute)
  also have "\<dots> \<longleftrightarrow> ?lhs"
    using False by auto
  finally show ?thesis by metis
qed

lemma norm_cauchy_schwarz_abs_eq:
  "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow>
    norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm x *\<^sub>R y = - norm y *\<^sub>R x"
  using norm_cauchy_schwarz_eq [symmetric, of x y]
  using norm_cauchy_schwarz_eq [symmetric, of "-x" y] Cauchy_Schwarz_ineq2 [of x y]
  by auto

lemma norm_triangle_eq:
  fixes x y :: "'a::real_inner"
  shows "norm (x + y) = norm x + norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
proof (cases "x = 0 \<or> y = 0")
  case True
  then show ?thesis
    by force
next
  case False
  then have n: "norm x > 0" "norm y > 0"
    by auto
  have "norm (x + y) = norm x + norm y \<longleftrightarrow> (norm (x + y))\<^sup>2 = (norm x + norm y)\<^sup>2"
    by simp
  also have "\<dots> \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
    by (smt (verit, best) dot_norm inner_real_def inner_simps norm_cauchy_schwarz_eq power2_eq_square)
  finally show ?thesis .
qed

lemma dist_triangle_eq:
  fixes x y z :: "'a::real_inner"
  shows "dist x z = dist x y + dist y z \<longleftrightarrow>
    norm (x - y) *\<^sub>R (y - z) = norm (y - z) *\<^sub>R (x - y)"
  by (metis (no_types, lifting) add_diff_eq diff_add_cancel dist_norm norm_triangle_eq)

subsection \<open>Collinearity\<close>

definition\<^marker>\<open>tag important\<close> collinear :: "'a::real_vector set \<Rightarrow> bool"
  where "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u)"

lemma collinear_alt:
     "collinear S \<longleftrightarrow> (\<exists>u v. \<forall>x \<in> S. \<exists>c. x = u + c *\<^sub>R v)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding collinear_def by (metis add.commute diff_add_cancel)
next
  assume ?rhs
  then obtain u v where *: "\<And>x. x \<in> S \<Longrightarrow> \<exists>c. x = u + c *\<^sub>R v"
    by auto
  have "\<exists>c. x - y = c *\<^sub>R v" if "x \<in> S" "y \<in> S" for x y
        by (metis *[OF \<open>x \<in> S\<close>] *[OF \<open>y \<in> S\<close>] scaleR_left.diff add_diff_cancel_left)
  then show ?lhs
    using collinear_def by blast
qed

lemma collinear:
  fixes S :: "'a::{perfect_space,real_vector} set"
  shows "collinear S \<longleftrightarrow> (\<exists>u. u \<noteq> 0 \<and> (\<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u))"
proof -
  have "\<exists>v. v \<noteq> 0 \<and> (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R v)"
    if "\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R u" "u=0" for u
  proof -
    have "\<forall>x\<in>S. \<forall>y\<in>S. x = y"
      using that by auto
    moreover
    obtain v::'a where "v \<noteq> 0"
      using UNIV_not_singleton [of 0] by auto
    ultimately have "\<forall>x\<in>S. \<forall>y\<in>S. \<exists>c. x - y = c *\<^sub>R v"
      by auto
    then show ?thesis
      using \<open>v \<noteq> 0\<close> by blast
  qed
  then show ?thesis
    by (metis collinear_def)
qed

lemma collinear_subset: "\<lbrakk>collinear T; S \<subseteq> T\<rbrakk> \<Longrightarrow> collinear S"
  by (meson collinear_def subsetCE)

lemma collinear_empty [iff]: "collinear {}"
  by (simp add: collinear_def)

lemma collinear_sing [iff]: "collinear {x}"
  by (simp add: collinear_def)

lemma collinear_2 [iff]: "collinear {x, y}"
  by (simp add: collinear_def) (metis minus_diff_eq scaleR_left.minus scaleR_one)

lemma collinear_lemma: "collinear {0, x, y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "x = 0 \<or> y = 0")
  case True
  then show ?thesis
    by (auto simp: insert_commute)
next
  case False
  show ?thesis
  proof
    assume h: "?lhs"
    then obtain u where u: "\<forall> x\<in> {0,x,y}. \<forall>y\<in> {0,x,y}. \<exists>c. x - y = c *\<^sub>R u"
      unfolding collinear_def by blast
    from u[rule_format, of x 0] u[rule_format, of y 0]
    obtain cx and cy where
      cx: "x = cx *\<^sub>R u" and cy: "y = cy *\<^sub>R u"
      by auto
    from cx cy False have cx0: "cx \<noteq> 0" and cy0: "cy \<noteq> 0" by auto
    let ?d = "cy / cx"
    from cx cy cx0 have "y = ?d *\<^sub>R x"
      by simp
    then show ?rhs using False by blast
  next
    assume h: "?rhs"
    then obtain c where c: "y = c *\<^sub>R x"
      using False by blast
    show ?lhs
      apply (simp add: collinear_def c)
      by (metis (mono_tags, lifting) scaleR_left.minus scaleR_left_diff_distrib scaleR_one)
  qed
qed

lemma collinear_iff_Reals: "collinear {0::complex,w,z} \<longleftrightarrow> z/w \<in> \<real>"
proof
  show "z/w \<in> \<real> \<Longrightarrow> collinear {0,w,z}"
    by (metis Reals_cases collinear_lemma nonzero_divide_eq_eq scaleR_conv_of_real)
qed (auto simp: collinear_lemma scaleR_conv_of_real)

lemma collinear_scaleR_iff: "collinear {0, \<alpha> *\<^sub>R w, \<beta> *\<^sub>R z} \<longleftrightarrow> collinear {0,w,z} \<or> \<alpha>=0 \<or> \<beta>=0"
  (is "?lhs = ?rhs")
proof (cases "\<alpha>=0 \<or> \<beta>=0")
  case False
  then have "(\<exists>c. \<beta> *\<^sub>R z = (c * \<alpha>) *\<^sub>R w) = (\<exists>c. z = c *\<^sub>R w)"
    by (metis mult.commute scaleR_scaleR vector_fraction_eq_iff)
  then show ?thesis
    by (auto simp add: collinear_lemma)
qed (auto simp: collinear_lemma)

lemma norm_cauchy_schwarz_equal: "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow> collinear {0, x, y}"
proof (cases "x=0")
  case True
  then show ?thesis
    by (auto simp: insert_commute)
next
  case False
  then have nnz: "norm x \<noteq> 0"
    by auto
  show ?thesis
  proof
    assume "\<bar>x \<bullet> y\<bar> = norm x * norm y"
    then show "collinear {0, x, y}"
      unfolding norm_cauchy_schwarz_abs_eq collinear_lemma
      by (meson eq_vector_fraction_iff nnz)
  next
    assume "collinear {0, x, y}"
    with False show "\<bar>x \<bullet> y\<bar> = norm x * norm y"
      unfolding norm_cauchy_schwarz_abs_eq collinear_lemma  by (auto simp: abs_if)
  qed
qed

lemma norm_triangle_eq_imp_collinear:
  fixes x y :: "'a::real_inner"
  assumes "norm (x + y) = norm x + norm y"
  shows "collinear{0,x,y}"
  using assms norm_cauchy_schwarz_abs_eq norm_cauchy_schwarz_equal norm_triangle_eq 
  by blast


subsection\<open>Properties of special hyperplanes\<close>

lemma subspace_hyperplane: "subspace {x. a \<bullet> x = 0}"
  by (simp add: subspace_def inner_right_distrib)

lemma subspace_hyperplane2: "subspace {x. x \<bullet> a = 0}"
  by (simp add: inner_commute inner_right_distrib subspace_def)

lemma special_hyperplane_span:
  fixes S :: "'n::euclidean_space set"
  assumes "k \<in> Basis"
  shows "{x. k \<bullet> x = 0} = span (Basis - {k})"
proof -
  have *: "x \<in> span (Basis - {k})" if "k \<bullet> x = 0" for x
  proof -
    have "x = (\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b)"
      by (simp add: euclidean_representation)
    also have "\<dots> = (\<Sum>b \<in> Basis - {k}. (x \<bullet> b) *\<^sub>R b)"
      by (auto simp: sum.remove [of _ k] inner_commute assms that)
    finally have "x = (\<Sum>b\<in>Basis - {k}. (x \<bullet> b) *\<^sub>R b)" .
    then show ?thesis
      by (simp add: span_finite)
  qed
  show ?thesis
    apply (rule span_subspace [symmetric])
    using assms
    apply (auto simp: inner_not_same_Basis intro: * subspace_hyperplane)
    done
qed

lemma dim_special_hyperplane:
  fixes k :: "'n::euclidean_space"
  shows "k \<in> Basis \<Longrightarrow> dim {x. k \<bullet> x = 0} = DIM('n) - 1"
  by (metis Diff_subset card_Diff_singleton indep_card_eq_dim_span independent_substdbasis special_hyperplane_span)

proposition dim_hyperplane:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
    shows "dim {x. a \<bullet> x = 0} = DIM('a) - 1"
proof -
  have span0: "span {x. a \<bullet> x = 0} = {x. a \<bullet> x = 0}"
    by (rule span_unique) (auto simp: subspace_hyperplane)
  then obtain B where "independent B"
              and Bsub: "B \<subseteq> {x. a \<bullet> x = 0}"
              and subspB: "{x. a \<bullet> x = 0} \<subseteq> span B"
              and card0: "(card B = dim {x. a \<bullet> x = 0})"
              and ortho: "pairwise orthogonal B"
    using orthogonal_basis_exists by metis
  with assms have "a \<notin> span B"
    by (metis (mono_tags, lifting) span_eq inner_eq_zero_iff mem_Collect_eq span0)
  then have ind: "independent (insert a B)"
    by (simp add: \<open>independent B\<close> independent_insert)
  have "finite B"
    using \<open>independent B\<close> independent_bound by blast
  have "UNIV \<subseteq> span (insert a B)"
  proof fix y::'a
    obtain r z where "y = r *\<^sub>R a + z" "a \<bullet> z = 0"
      by (metis add.commute diff_add_cancel vector_sub_project_orthogonal)
    then show "y \<in> span (insert a B)"
      by (metis (mono_tags, lifting) Bsub add_diff_cancel_left'
          mem_Collect_eq span0 span_breakdown_eq span_eq subspB)
  qed
  then have "DIM('a) = dim(insert a B)"
    by (metis independent_Basis span_Basis dim_eq_card top.extremum_uniqueI)
  then show ?thesis
    by (metis One_nat_def \<open>a \<notin> span B\<close> \<open>finite B\<close> card0 card_insert_disjoint 
        diff_Suc_Suc diff_zero dim_eq_card_independent ind span_base)
qed

lemma lowdim_eq_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "dim S = DIM('a) - 1"
  obtains a where "a \<noteq> 0" and "span S = {x. a \<bullet> x = 0}"
proof -
  obtain b where b: "b \<noteq> 0" "span S \<subseteq> {a. b \<bullet> a = 0}"
    by (metis DIM_positive assms diff_less zero_less_one lowdim_subset_hyperplane)
  then show ?thesis
    by (metis assms dim_hyperplane dim_span dim_subset subspace_dim_equal subspace_hyperplane subspace_span that)
qed

lemma dim_eq_hyperplane:
  fixes S :: "'n::euclidean_space set"
  shows "dim S = DIM('n) - 1 \<longleftrightarrow> (\<exists>a. a \<noteq> 0 \<and> span S = {x. a \<bullet> x = 0})"
by (metis One_nat_def dim_hyperplane dim_span lowdim_eq_hyperplane)


subsection\<open> Orthogonal bases and Gram-Schmidt process\<close>

lemma pairwise_orthogonal_independent:
  assumes "pairwise orthogonal S" and "0 \<notin> S"
    shows "independent S"
proof -
  have 0: "\<And>x y. \<lbrakk>x \<noteq> y; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    using assms by (simp add: pairwise_def orthogonal_def)
  have "False" if "a \<in> S" and a: "a \<in> span (S - {a})" for a
  proof -
    obtain T U where "T \<subseteq> S - {a}" "a = (\<Sum>v\<in>T. U v *\<^sub>R v)"
      using a by (force simp: span_explicit)
    then have "a \<bullet> a = a \<bullet> (\<Sum>v\<in>T. U v *\<^sub>R v)"
      by simp
    also have "\<dots> = 0"
      apply (simp add: inner_sum_right)
      by (smt (verit) "0" DiffE \<open>T \<subseteq> S - {a}\<close> in_mono insertCI mult_not_zero sum.neutral that(1))
    finally show ?thesis
      using \<open>0 \<notin> S\<close> \<open>a \<in> S\<close> by auto
  qed
  then show ?thesis
    by (force simp: dependent_def)
qed

lemma pairwise_orthogonal_imp_finite:
  fixes S :: "'a::euclidean_space set"
  assumes "pairwise orthogonal S"
    shows "finite S"
  by (metis Set.set_insert assms finite_insert independent_bound pairwise_insert 
            pairwise_orthogonal_independent)

lemma subspace_orthogonal_to_vector: "subspace {y. orthogonal x y}"
  by (simp add: subspace_def orthogonal_clauses)

lemma subspace_orthogonal_to_vectors: "subspace {y. \<forall>x \<in> S. orthogonal x y}"
  by (simp add: subspace_def orthogonal_clauses)

lemma orthogonal_to_span:
  assumes a: "a \<in> span S" and x: "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
    shows "orthogonal x a"
  by (metis a orthogonal_clauses(1,2,4)
      span_induct_alt x)

proposition Gram_Schmidt_step:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S" and x: "x \<in> span S"
    shows "orthogonal x (a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b))"
proof -
  have "finite S"
    by (simp add: S pairwise_orthogonal_imp_finite)
  have "orthogonal (a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b)) x"
       if "x \<in> S" for x
  proof -
    have "a \<bullet> x = (\<Sum>y\<in>S. if y = x then y \<bullet> a else 0)"
      by (simp add: \<open>finite S\<close> inner_commute that)
    also have "\<dots> =  (\<Sum>b\<in>S. b \<bullet> a * (b \<bullet> x) / (b \<bullet> b))"
      apply (rule sum.cong [OF refl], simp)
      by (meson S orthogonal_def pairwise_def that)
   finally show ?thesis
     by (simp add: orthogonal_def algebra_simps inner_sum_left)
  qed
  then show ?thesis
    using orthogonal_to_span orthogonal_commute x by blast
qed


lemma orthogonal_extension_aux:
  fixes S :: "'a::euclidean_space set"
  assumes "finite T" "finite S" "pairwise orthogonal S"
    shows "\<exists>U. pairwise orthogonal (S \<union> U) \<and> span (S \<union> U) = span (S \<union> T)"
using assms
proof (induction arbitrary: S)
  case empty then show ?case
    by simp (metis sup_bot_right)
next
  case (insert a T)
  have 0: "\<And>x y. \<lbrakk>x \<noteq> y; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    using insert by (simp add: pairwise_def orthogonal_def)
  define a' where "a' = a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b)"
  obtain U where orthU: "pairwise orthogonal (S \<union> insert a' U)"
             and spanU: "span (insert a' S \<union> U) = span (insert a' S \<union> T)"
    by (rule exE [OF insert.IH [of "insert a' S"]])
      (auto simp: Gram_Schmidt_step a'_def insert.prems orthogonal_commute
        pairwise_orthogonal_insert span_clauses)
  have orthS: "\<And>x. x \<in> S \<Longrightarrow> a' \<bullet> x = 0"
    using Gram_Schmidt_step a'_def insert.prems orthogonal_commute orthogonal_def span_base by blast
  have "span (S \<union> insert a' U) = span (insert a' (S \<union> T))"
    using spanU by simp
  also have "\<dots> = span (insert a (S \<union> T))"
    by (simp add: a'_def span_neg span_sum span_base span_mul eq_span_insert_eq)
  also have "\<dots> = span (S \<union> insert a T)"
    by simp
  finally show ?case
    using orthU by blast
qed


proposition orthogonal_extension:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S"
  obtains U where "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> T)"
proof -
  obtain B where "finite B" "span B = span T"
    using basis_subspace_exists [of "span T"] subspace_span by metis
  with orthogonal_extension_aux [of B S]
  obtain U where "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> B)"
    using assms pairwise_orthogonal_imp_finite by auto
  with \<open>span B = span T\<close> show ?thesis
    by (rule_tac U=U in that) (auto simp: span_Un)
qed

corollary\<^marker>\<open>tag unimportant\<close> orthogonal_extension_strong:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S"
  obtains U where "U \<inter> (insert 0 S) = {}" "pairwise orthogonal (S \<union> U)"
                  "span (S \<union> U) = span (S \<union> T)"
proof -
  obtain U where U: "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> T)"
    using orthogonal_extension assms by blast
  moreover have "pairwise orthogonal (S \<union> (U - insert 0 S))"
    by (smt (verit, best) Un_Diff_Int Un_iff U pairwise_def)
  ultimately show ?thesis
    by (metis Diff_disjoint Un_Diff_cancel Un_insert_left inf_commute span_insert_0 that)
qed

subsection\<open>Decomposing a vector into parts in orthogonal subspaces\<close>

text\<open>existence of orthonormal basis for a subspace.\<close>

lemma orthogonal_spanningset_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "B \<subseteq> S" "pairwise orthogonal B" "span B = S"
  by (metis assms basis_orthogonal basis_subspace_exists span_eq)

lemma orthogonal_basis_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "0 \<notin> B" "B \<subseteq> S" "pairwise orthogonal B" "independent B"
                  "card B = dim S" "span B = S"
  by (metis assms dependent_zero orthogonal_basis_exists span_eq span_eq_iff)

proposition orthonormal_basis_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "B \<subseteq> S" "pairwise orthogonal B"
              and "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
              and "independent B" "card B = dim S" "span B = S"
proof -
  obtain B where "0 \<notin> B" "B \<subseteq> S"
             and orth: "pairwise orthogonal B"
             and "independent B" "card B = dim S" "span B = S"
    by (blast intro: orthogonal_basis_subspace [OF assms])
  have 1: "(\<lambda>x. x /\<^sub>R norm x) ` B \<subseteq> S"
    using \<open>span B = S\<close> span_superset span_mul by fastforce
  have 2: "pairwise orthogonal ((\<lambda>x. x /\<^sub>R norm x) ` B)"
    using orth by (force simp: pairwise_def orthogonal_clauses)
  have 3: "\<And>x. x \<in> (\<lambda>x. x /\<^sub>R norm x) ` B \<Longrightarrow> norm x = 1"
    by (metis (no_types, lifting) \<open>0 \<notin> B\<close> image_iff norm_sgn sgn_div_norm)
  have 4: "independent ((\<lambda>x. x /\<^sub>R norm x) ` B)"
    by (metis "2" "3" norm_zero pairwise_orthogonal_independent zero_neq_one)
  have "inj_on (\<lambda>x. x /\<^sub>R norm x) B"
  proof
    fix x y
    assume "x \<in> B" "y \<in> B" "x /\<^sub>R norm x = y /\<^sub>R norm y"
    moreover have "\<And>i. i \<in> B \<Longrightarrow> norm (i /\<^sub>R norm i) = 1"
      using 3 by blast
    ultimately show "x = y"
      by (metis norm_eq_1 orth orthogonal_clauses(7) orthogonal_commute orthogonal_def pairwise_def zero_neq_one)
  qed
  then have 5: "card ((\<lambda>x. x /\<^sub>R norm x) ` B) = dim S"
    by (metis \<open>card B = dim S\<close> card_image)
  have 6: "span ((\<lambda>x. x /\<^sub>R norm x) ` B) = S"
    by (metis "1" "4" "5" assms card_eq_dim independent_imp_finite span_subspace)
  show ?thesis
    by (rule that [OF 1 2 3 4 5 6])
qed


proposition\<^marker>\<open>tag unimportant\<close> orthogonal_to_subspace_exists_gen:
  fixes S :: "'a :: euclidean_space set"
  assumes "span S \<subset> span T"
  obtains x where "x \<noteq> 0" "x \<in> span T" "\<And>y. y \<in> span S \<Longrightarrow> orthogonal x y"
proof -
  obtain B where "B \<subseteq> span S" and orthB: "pairwise orthogonal B"
             and "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
             and "independent B" "card B = dim S" "span B = span S"
    by (metis dim_span orthonormal_basis_subspace subspace_span)
  with assms obtain u where spanBT: "span B \<subseteq> span T" and "u \<notin> span B" "u \<in> span T"
    by auto
  obtain C where orthBC: "pairwise orthogonal (B \<union> C)" and spanBC: "span (B \<union> C) = span (B \<union> {u})"
    by (blast intro: orthogonal_extension [OF orthB])
  show thesis
  proof (cases "C \<subseteq> insert 0 B")
    case True
    then have "C \<subseteq> span B"
      using span_eq
      by (metis span_insert_0 subset_trans)
    moreover have "u \<in> span (B \<union> C)"
      using \<open>span (B \<union> C) = span (B \<union> {u})\<close> span_superset by force
    ultimately show ?thesis
      using True \<open>u \<notin> span B\<close>
      by (metis Un_insert_left span_insert_0 sup.orderE)
  next
    case False
    then obtain x where "x \<in> C" "x \<noteq> 0" "x \<notin> B"
      by blast
    then have "x \<in> span T"
      by (smt (verit, ccfv_SIG) Set.set_insert  \<open>u \<in> span T\<close> empty_subsetI insert_subset 
          le_sup_iff spanBC spanBT span_mono span_span span_superset subset_trans)
    moreover have "orthogonal x y" if "y \<in> span B" for y
      using that
    proof (rule span_induct)
      show "subspace {a. orthogonal x a}"
        by (simp add: subspace_orthogonal_to_vector)
      show "\<And>b. b \<in> B \<Longrightarrow> orthogonal x b"
        by (metis Un_iff \<open>x \<in> C\<close> \<open>x \<notin> B\<close> orthBC pairwise_def)
    qed
    ultimately show ?thesis
      using \<open>x \<noteq> 0\<close> that \<open>span B = span S\<close> by auto
  qed
qed

corollary\<^marker>\<open>tag unimportant\<close> orthogonal_to_subspace_exists:
  fixes S :: "'a :: euclidean_space set"
  assumes "dim S < DIM('a)"
  obtains x where "x \<noteq> 0" "\<And>y. y \<in> span S \<Longrightarrow> orthogonal x y"
proof -
  have "span S \<subset> UNIV"
    by (metis assms dim_eq_full order_less_imp_not_less top.not_eq_extremum)
  with orthogonal_to_subspace_exists_gen [of S UNIV] that show ?thesis
    by (auto)
qed

corollary\<^marker>\<open>tag unimportant\<close> orthogonal_to_vector_exists:
  fixes x :: "'a :: euclidean_space"
  assumes "2 \<le> DIM('a)"
  obtains y where "y \<noteq> 0" "orthogonal x y"
proof -
  have "dim {x} < DIM('a)"
    using assms by auto
  then show thesis
    by (rule orthogonal_to_subspace_exists) (simp add: orthogonal_commute span_base that)
qed

proposition\<^marker>\<open>tag unimportant\<close> orthogonal_subspace_decomp_exists:
  fixes S :: "'a :: euclidean_space set"
  obtains y z
  where "y \<in> span S"
    and "\<And>w. w \<in> span S \<Longrightarrow> orthogonal z w"
    and "x = y + z"
proof -
  obtain T where "0 \<notin> T" "T \<subseteq> span S" "pairwise orthogonal T" "independent T"
    "card T = dim (span S)" "span T = span S"
    using orthogonal_basis_subspace subspace_span by blast
  let ?a = "\<Sum>b\<in>T. (b \<bullet> x / (b \<bullet> b)) *\<^sub>R b"
  have orth: "orthogonal (x - ?a) w" if "w \<in> span S" for w
    by (simp add: Gram_Schmidt_step \<open>pairwise orthogonal T\<close> \<open>span T = span S\<close>
        orthogonal_commute that)
  with that[of ?a "x-?a"] \<open>T \<subseteq> span S\<close> show ?thesis
    by (simp add: span_mul span_sum subsetD)
qed

lemma orthogonal_subspace_decomp_unique:
  fixes S :: "'a :: euclidean_space set"
  assumes "x + y = x' + y'"
      and ST: "x \<in> span S" "x' \<in> span S" "y \<in> span T" "y' \<in> span T"
      and orth: "\<And>a b. \<lbrakk>a \<in> S; b \<in> T\<rbrakk> \<Longrightarrow> orthogonal a b"
  shows "x = x' \<and> y = y'"
proof -
  have "x + y - y' = x'"
    by (simp add: assms)
  moreover have "\<And>a b. \<lbrakk>a \<in> span S; b \<in> span T\<rbrakk> \<Longrightarrow> orthogonal a b"
    by (meson orth orthogonal_commute orthogonal_to_span)
  ultimately have "0 = x' - x"
    using assms
    by (metis add.commute add_diff_cancel_right' diff_right_commute orthogonal_self span_diff)
  with assms show ?thesis by auto
qed

lemma vector_in_orthogonal_spanningset:
  fixes a :: "'a::euclidean_space"
  obtains S where "a \<in> S" "pairwise orthogonal S" "span S = UNIV"
  by (metis UnI1 Un_UNIV_right insertI1 orthogonal_extension pairwise_singleton span_UNIV)

lemma vector_in_orthogonal_basis:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
  obtains S where "a \<in> S" "0 \<notin> S" "pairwise orthogonal S" "independent S" "finite S"
                  "span S = UNIV" "card S = DIM('a)"
proof -
  obtain S where S: "a \<in> S" "pairwise orthogonal S" "span S = UNIV"
    using vector_in_orthogonal_spanningset .
  show thesis
  proof
    show "pairwise orthogonal (S - {0})"
      using pairwise_mono S(2) by blast
    show "independent (S - {0})"
      by (simp add: \<open>pairwise orthogonal (S - {0})\<close> pairwise_orthogonal_independent)
    show "finite (S - {0})"
      using \<open>independent (S - {0})\<close> independent_imp_finite by blast
    show "card (S - {0}) = DIM('a)"
      using span_delete_0 [of S] S
      by (simp add: \<open>independent (S - {0})\<close> indep_card_eq_dim_span)
  qed (use S \<open>a \<noteq> 0\<close> in auto)
qed

lemma vector_in_orthonormal_basis:
  fixes a :: "'a::euclidean_space"
  assumes "norm a = 1"
  obtains S where "a \<in> S" "pairwise orthogonal S" "\<And>x. x \<in> S \<Longrightarrow> norm x = 1"
    "independent S" "card S = DIM('a)" "span S = UNIV"
proof -
  have "a \<noteq> 0"
    using assms by auto
  then obtain S where "a \<in> S" "0 \<notin> S" "finite S"
          and S: "pairwise orthogonal S" "independent S" "span S = UNIV" "card S = DIM('a)"
    by (metis vector_in_orthogonal_basis)
  let ?S = "(\<lambda>x. x /\<^sub>R norm x) ` S"
  show thesis
  proof
    show "a \<in> ?S"
      using \<open>a \<in> S\<close> assms image_iff by fastforce
  next
    show "pairwise orthogonal ?S"
      using \<open>pairwise orthogonal S\<close> by (auto simp: pairwise_def orthogonal_def)
    show "\<And>x. x \<in> (\<lambda>x. x /\<^sub>R norm x) ` S \<Longrightarrow> norm x = 1"
      using \<open>0 \<notin> S\<close> by (auto simp: field_split_simps)
    then show ind: "independent ?S"
      by (metis \<open>pairwise orthogonal ((\<lambda>x. x /\<^sub>R norm x) ` S)\<close> norm_zero pairwise_orthogonal_independent zero_neq_one)
    have "inj_on (\<lambda>x. x /\<^sub>R norm x) S"
      unfolding inj_on_def
      by (metis (full_types) S(1) \<open>0 \<notin> S\<close> inverse_nonzero_iff_nonzero norm_eq_zero orthogonal_scaleR orthogonal_self pairwise_def)
    then show "card ?S = DIM('a)"
      by (simp add: card_image S)
    then show "span ?S = UNIV"
      by (metis ind dim_eq_card dim_eq_full)
  qed
qed

proposition dim_orthogonal_sum:
  fixes A :: "'a::euclidean_space set"
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    shows "dim(A \<union> B) = dim A + dim B"
proof -
  have 1: "\<And>x y. \<lbrakk>x \<in> span A; y \<in> B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    by (erule span_induct [OF _ subspace_hyperplane2]; simp add: assms)
  have "\<And>x y. \<lbrakk>x \<in> span A; y \<in> span B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    using 1 by (simp add: span_induct [OF _ subspace_hyperplane])
  then have 0: "\<And>x y. \<lbrakk>x \<in> span A; y \<in> span B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    by simp
  have "dim(A \<union> B) = dim (span (A \<union> B))"
    by (simp)
  also have "span (A \<union> B) = ((\<lambda>(a, b). a + b) ` (span A \<times> span B))"
    by (auto simp add: span_Un image_def)
  also have "dim \<dots> = dim {x + y |x y. x \<in> span A \<and> y \<in> span B}"
    by (auto intro!: arg_cong [where f=dim])
  also have "\<dots> = dim {x + y |x y. x \<in> span A \<and> y \<in> span B} + dim(span A \<inter> span B)"
    by (auto dest: 0)
  also have "\<dots> = dim A + dim B"
    using dim_sums_Int by fastforce
  finally show ?thesis .
qed

lemma dim_subspace_orthogonal_to_vectors:
  fixes A :: "'a::euclidean_space set"
  assumes "subspace A" "subspace B" "A \<subseteq> B"
    shows "dim {y \<in> B. \<forall>x \<in> A. orthogonal x y} + dim A = dim B"
proof -
  have "dim (span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A)) = dim (span B)"
  proof (rule arg_cong [where f=dim, OF subset_antisym])
    show "span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A) \<subseteq> span B"
      by (simp add: \<open>A \<subseteq> B\<close> Collect_restrict span_mono)
  next
    have *: "x \<in> span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A)"
         if "x \<in> B" for x
    proof -
      obtain y z where "x = y + z" "y \<in> span A" and orth: "\<And>w. w \<in> span A \<Longrightarrow> orthogonal z w"
        using orthogonal_subspace_decomp_exists [of A x] that by auto
      moreover
      have "y \<in> span B"
        using \<open>y \<in> span A\<close> assms(3) span_mono by blast
      ultimately have "z \<in> B \<and> (\<forall>x. x \<in> A \<longrightarrow> orthogonal x z)"
        using assms by (metis orthogonal_commute span_add_eq span_eq_iff that)
      then have z: "z \<in> span {y \<in> B. \<forall>x\<in>A. orthogonal x y}"
        by (simp add: span_base)
      then show ?thesis
        by (smt (verit, best) \<open>x = y + z\<close> \<open>y \<in> span A\<close> le_sup_iff span_add_eq span_subspace_induct 
            span_superset subset_iff subspace_span)
    qed
    show "span B \<subseteq> span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A)"
      by (rule span_minimal) (auto intro: * span_minimal)
  qed
  then show ?thesis
    by (metis (no_types, lifting) dim_orthogonal_sum dim_span mem_Collect_eq
        orthogonal_commute orthogonal_def)
qed

subsection\<open>Linear functions are (uniformly) continuous on any set\<close>

subsection\<^marker>\<open>tag unimportant\<close> \<open>Topological properties of linear functions\<close>

lemma linear_lim_0:
  assumes "bounded_linear f"
  shows "(f \<longlongrightarrow> 0) (at (0))"
proof -
  interpret f: bounded_linear f by fact
  have "(f \<longlongrightarrow> f 0) (at 0)"
    using tendsto_ident_at by (rule f.tendsto)
  then show ?thesis unfolding f.zero .
qed

lemma linear_continuous_at:
  "bounded_linear f \<Longrightarrow>continuous (at a) f"
  by (simp add: bounded_linear.isUCont isUCont_isCont)

lemma linear_continuous_within:
  "bounded_linear f \<Longrightarrow> continuous (at x within s) f"
  using continuous_at_imp_continuous_at_within linear_continuous_at by blast

lemma linear_continuous_on:
  "bounded_linear f \<Longrightarrow> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

lemma Lim_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and h :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "(f \<longlongrightarrow> l) F" "linear h"
  shows "((\<lambda>x. h(f x)) \<longlongrightarrow> h l) F"
proof -
  obtain B where B: "B > 0" "\<And>x. norm (h x) \<le> B * norm x"
    using linear_bounded_pos [OF \<open>linear h\<close>] by blast
  show ?thesis
    unfolding tendsto_iff
      by (simp add: assms bounded_linear.tendsto linear_linear tendstoD)
qed

lemma linear_continuous_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "continuous F f" "linear g"
  shows "continuous F (\<lambda>x. g(f x))"
  using assms unfolding continuous_def by (rule Lim_linear)

lemma linear_continuous_on_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "continuous_on S f" "linear g"
  shows "continuous_on S (\<lambda>x. g(f x))"
  using assms by (simp add: continuous_on_eq_continuous_within linear_continuous_compose)

text\<open>Also bilinear functions, in composition form\<close>

lemma bilinear_continuous_compose:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes "continuous F f" "continuous F g" "bilinear h"
  shows "continuous F (\<lambda>x. h (f x) (g x))"
  using assms bilinear_conv_bounded_bilinear bounded_bilinear.continuous by blast

lemma bilinear_continuous_on_compose:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
    and f :: "'d::t2_space \<Rightarrow> 'a"
  assumes "continuous_on S f" "continuous_on S g" "bilinear h"
  shows "continuous_on S (\<lambda>x. h (f x) (g x))"
  using assms by (simp add: continuous_on_eq_continuous_within bilinear_continuous_compose)

end
