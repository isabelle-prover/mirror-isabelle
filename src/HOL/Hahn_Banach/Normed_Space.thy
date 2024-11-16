(*  Title:      HOL/Hahn_Banach/Normed_Space.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>Normed vector spaces\<close>

theory Normed_Space
imports Subspace
begin

subsection \<open>Quasinorms\<close>

text \<open>
  A \<^emph>\<open>seminorm\<close> \<open>\<parallel>\<cdot>\<parallel>\<close> is a function on a real vector space into the reals that
  has the following properties: it is positive definite, absolute homogeneous
  and subadditive.
\<close>

locale seminorm =
  fixes V :: "'a::{minus, plus, zero, uminus} set"
  fixes norm :: "'a \<Rightarrow> real"    (\<open>\<parallel>_\<parallel>\<close>)
  assumes ge_zero [iff?]: "x \<in> V \<Longrightarrow> 0 \<le> \<parallel>x\<parallel>"
    and abs_homogenous [iff?]: "x \<in> V \<Longrightarrow> \<parallel>a \<cdot> x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>"
    and subadditive [iff?]: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> \<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"

declare seminorm.intro [intro?]

lemma (in seminorm) diff_subadditive:
  assumes "vectorspace V"
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> \<parallel>x - y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
proof -
  interpret vectorspace V by fact
  assume x: "x \<in> V" and y: "y \<in> V"
  then have "x - y = x + - 1 \<cdot> y"
    by (simp add: diff_eq2 negate_eq2a)
  also from x y have "\<parallel>\<dots>\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>- 1 \<cdot> y\<parallel>"
    by (simp add: subadditive)
  also from y have "\<parallel>- 1 \<cdot> y\<parallel> = \<bar>- 1\<bar> * \<parallel>y\<parallel>"
    by (rule abs_homogenous)
  also have "\<dots> = \<parallel>y\<parallel>" by simp
  finally show ?thesis .
qed

lemma (in seminorm) minus:
  assumes "vectorspace V"
  shows "x \<in> V \<Longrightarrow> \<parallel>- x\<parallel> = \<parallel>x\<parallel>"
proof -
  interpret vectorspace V by fact
  assume x: "x \<in> V"
  then have "- x = - 1 \<cdot> x" by (simp only: negate_eq1)
  also from x have "\<parallel>\<dots>\<parallel> = \<bar>- 1\<bar> * \<parallel>x\<parallel>" by (rule abs_homogenous)
  also have "\<dots> = \<parallel>x\<parallel>" by simp
  finally show ?thesis .
qed


subsection \<open>Norms\<close>

text \<open>
  A \<^emph>\<open>norm\<close> \<open>\<parallel>\<cdot>\<parallel>\<close> is a seminorm that maps only the \<open>0\<close> vector to \<open>0\<close>.
\<close>

locale norm = seminorm +
  assumes zero_iff [iff]: "x \<in> V \<Longrightarrow> (\<parallel>x\<parallel> = 0) = (x = 0)"


subsection \<open>Normed vector spaces\<close>

text \<open>
  A vector space together with a norm is called a \<^emph>\<open>normed space\<close>.
\<close>

locale normed_vectorspace = vectorspace + norm

declare normed_vectorspace.intro [intro?]

lemma (in normed_vectorspace) gt_zero [intro?]:
  assumes x: "x \<in> V" and neq: "x \<noteq> 0"
  shows "0 < \<parallel>x\<parallel>"
proof -
  from x have "0 \<le> \<parallel>x\<parallel>" ..
  also have "0 \<noteq> \<parallel>x\<parallel>"
  proof
    assume "0 = \<parallel>x\<parallel>"
    with x have "x = 0" by simp
    with neq show False by contradiction
  qed
  finally show ?thesis .
qed

text \<open>
  Any subspace of a normed vector space is again a normed vectorspace.
\<close>

lemma subspace_normed_vs [intro?]:
  fixes F E norm
  assumes "subspace F E" "normed_vectorspace E norm"
  shows "normed_vectorspace F norm"
proof -
  interpret subspace F E by fact
  interpret normed_vectorspace E norm by fact
  show ?thesis
  proof
    show "vectorspace F"
      by (rule vectorspace) unfold_locales
    have "Normed_Space.norm E norm" ..
    with subset show "Normed_Space.norm F norm"
      by (simp add: norm_def seminorm_def norm_axioms_def)
  qed
qed

end
