theory Infinite_Product
  imports Infinite_Products 
 

begin

text \<open>The recurring theme of the whole development: the sum theory works because
  addition is uniformly continuous on UNIV (one uniformity entourage is invariant
  under translation by any constant).  Multiplication is not, so the sum proofs
  cannot be ported verbatim.  It is, however, uniformly continuous away from 0,
  and in a product with a non-zero value almost all subproducts lie near 1.\<close>

section \<open>Unordered infinite products\<close>

definition HAS_SETPROD :: \<open>('a \<Rightarrow> 'b :: {semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool\<close> 
    where has_setprod_def: \<open>HAS_SETPROD f A x \<longleftrightarrow> (prod f \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>

abbreviation has_setprod (infixr "has'_setprod" 46) where
  "(f has_setprod S) A \<equiv> HAS_SETPROD f A S"
                                                                    
definition multipliable_on :: "('a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "multipliable'_on" 46) where
  "f multipliable_on A \<equiv> (\<exists>x. (f has_setprod x) A)"

(*
  this more robust notion of multipliability is akin to "convergent_prod" for
  products of sequences. It does not allow convergence to 0 and is more well-behaved in some cases.
*)
definition strongly_multipliable_on :: "('a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "strongly'_multipliable'_on" 46) where
  "f strongly_multipliable_on A \<equiv> finite {x\<in>A. f x = 0} \<and> (\<exists>P. (f has_setprod P) {x\<in>A. f x \<noteq> 0} \<and> P \<noteq> 0)"

definition infprod :: "('a \<Rightarrow> 'b::{semidom,topological_semigroup_mult,t2_space, t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infprod f A = (if f multipliable_on A then Lim (finite_subsets_at_top A) (prod f) else 1)"

definition abs_multipliable_on :: "('a \<Rightarrow> 'b::real_normed_algebra_1) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "abs'_multipliable'_on" 46) where
  "f abs_multipliable_on A \<longleftrightarrow> (\<lambda>x. 1 + norm (f x - 1)) multipliable_on A"

syntax (ASCII)
  "_infprod" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_mult"  ("(3INFPROD (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_infprod" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_mult"  ("(2\<Prod>\<^sub>\<infinity>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Prod>\<^sub>\<infinity>i\<in>A. b" \<rightleftharpoons> "CONST infprod (\<lambda>i. b) A"

syntax (ASCII)
  "_univinfprod" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3INFPROD _./ _)" [0, 10] 10)
syntax
  "_univinfprod" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Prod>\<^sub>\<infinity>_./ _)" [0, 10] 10)
translations
  "\<Prod>\<^sub>\<infinity>x. t" \<rightleftharpoons> "CONST infprod (\<lambda>x. t) (CONST UNIV)"

syntax (ASCII)
  "_qinfprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3INFPROD _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qinfprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Prod>\<^sub>\<infinity>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Prod>\<^sub>\<infinity>x|P. t" => "CONST infprod (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun prod_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qinfprod"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | prod_tr' _ = raise Match;
in [(@{const_syntax infprod}, K prod_tr')] end
\<close>

subsection \<open>General properties\<close>

lemma has_setprod_imp_multipliable: "(f has_setprod S) A \<Longrightarrow> f multipliable_on A"
  by (auto simp: multipliable_on_def)

lemma has_setprodI:
  assumes "((\<lambda>X. \<Prod>x\<in>X. f x) \<longlongrightarrow> P) (finite_subsets_at_top A)"
  shows   "(f has_setprod P) A"
  using assms unfolding has_setprod_def .

lemma has_setprodD:
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>X. \<Prod>x\<in>X. f x) \<longlongrightarrow> P) (finite_subsets_at_top A)"
  using assms unfolding has_setprod_def .

lemma infprodI:
  assumes \<open>(f has_setprod x) A\<close>
  shows \<open>infprod f A = x\<close>
  using has_setprodD[OF assms] assms unfolding infprod_def multipliable_on_def
  by (meson finite_subsets_at_top_neq_bot tendsto_Lim)

lemma infprod_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}\<close>
  assumes \<open>x = y\<close>
  assumes \<open>(f has_setprod x) A\<close>
  assumes \<open>(g has_setprod y) B\<close>
  shows \<open>infprod f A = infprod g B\<close>
  using assms infprodI by blast

lemma infprod_eqI':
  fixes f g :: \<open>'a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}\<close>
  assumes \<open>\<And>x. (f has_setprod x) A \<longleftrightarrow> (g has_setprod x) B\<close>
  shows \<open>infprod f A = infprod g B\<close>
  by (metis assms infprod_def infprod_eqI multipliable_on_def)

lemma infprod_not_exists:
  fixes f :: \<open>'a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}\<close>
  assumes \<open>\<not> f multipliable_on A\<close>
  shows \<open>infprod f A = 1\<close>
  by (simp add: assms infprod_def)

lemma multipliable_iff_has_setprod_infprod: "f multipliable_on A \<longleftrightarrow> (f has_setprod (infprod f A)) A"
  using infprodI multipliable_on_def by metis

lemma has_setprod_infprod[simp]:
  assumes \<open>f multipliable_on S\<close>
  shows \<open>(f has_setprod (infprod f S)) S\<close>
  using assms multipliable_iff_has_setprod_infprod by blast

lemma filterlim_Un_finite_subsets_at_top:
  assumes "finite Y"
  shows   "filterlim (\<lambda>X. X \<union> Y) (finite_subsets_at_top (X \<union> Y)) (finite_subsets_at_top X)"
  unfolding filterlim_def le_filter_def eventually_filtermap
proof safe
  fix P :: "'a set \<Rightarrow> bool"
  assume "\<forall>\<^sub>F A in finite_subsets_at_top (X \<union> Y). P A"
  then obtain A where A: "finite A" "A \<subseteq> X \<union> Y" "\<And>Z. finite Z \<Longrightarrow> A \<subseteq> Z \<Longrightarrow> Z \<subseteq> X \<union> Y \<Longrightarrow> P Z"
    unfolding eventually_finite_subsets_at_top by metis
  show "\<forall>\<^sub>F A in finite_subsets_at_top X. P (A \<union> Y)"
    unfolding eventually_finite_subsets_at_top
  proof (rule exI[of _ "A - Y"], intro allI conjI impI)
    show "finite (A - Y)" and "A - Y \<subseteq> X"
      using assms A(1,2) by auto
  next
    fix Z assume Z: "finite Z \<and> A - Y \<subseteq> Z \<and> Z \<subseteq> X"
    show "P (Z \<union> Y)"
      by (rule A) (use Z assms in auto)
  qed
qed

lemma has_setprod_cong_neutral:
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "(f has_setprod x) S \<longleftrightarrow> (g has_setprod x) T"
proof -
  have \<open>eventually P (filtermap (prod f) (finite_subsets_at_top S))
      = eventually P (filtermap (prod g) (finite_subsets_at_top T))\<close> for P
  proof 
    assume \<open>eventually P (filtermap (prod f) (finite_subsets_at_top S))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> S\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (prod f F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> T\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> T\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (prod g F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> T\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (prod f ((F\<inter>S) \<union> (F0\<inter>S)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> S\<close> \<open>finite F0\<close> that in auto)
      also have \<open>prod f ((F\<inter>S) \<union> (F0\<inter>S)) = prod g F\<close>
        by (intro prod.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> T\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (prod g) (finite_subsets_at_top T))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  next
    assume \<open>eventually P (filtermap (prod g) (finite_subsets_at_top T))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> T\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> T \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (prod g F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> S\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> S\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (prod f F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> S\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (prod g ((F\<inter>T) \<union> (F0\<inter>T)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> T\<close> \<open>finite F0\<close> that in auto)
      also have \<open>prod g ((F\<inter>T) \<union> (F0\<inter>T)) = prod f F\<close>
        by (intro prod.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> S\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (prod f) (finite_subsets_at_top S))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  qed

  then have tendsto_x: "(prod f \<longlongrightarrow> x) (finite_subsets_at_top S) \<longleftrightarrow> (prod g \<longlongrightarrow> x) (finite_subsets_at_top T)" for x
    by (simp add: le_filter_def filterlim_def)

  then show ?thesis
    by (simp add: has_setprod_def)
qed

lemma has_setprod_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "(f has_setprod x) A \<longleftrightarrow> (g has_setprod x) A"
  using assms by (intro has_setprod_cong_neutral) auto

lemma has_setprod_mult:
  assumes \<open>(f has_setprod a) A\<close>
  assumes \<open>(g has_setprod b) A\<close>
  shows \<open>((\<lambda>x. f x * g x) has_setprod (a * b)) A\<close>
proof -
  from assms have lim_f: \<open>(prod f \<longlongrightarrow> a)  (finite_subsets_at_top A)\<close>
    and lim_g: \<open>(prod g \<longlongrightarrow> b)  (finite_subsets_at_top A)\<close>
    by (simp_all add: has_setprod_def)
  then have lim: \<open>(prod (\<lambda>x. f x * g x) \<longlongrightarrow> a * b) (finite_subsets_at_top A)\<close>
    unfolding prod.distrib by (rule tendsto_mult)
  then show ?thesis using assms
    by (simp_all add: has_setprod_def)
qed

lemma has_setprod_Un_disjoint:
  assumes "(f has_setprod a) A"
  assumes "(f has_setprod b) B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>(f has_setprod (a * b)) (A \<union> B)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 1)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 1)\<close> for x
  have "(f has_setprod a) A \<longleftrightarrow> (fA has_setprod a) (A \<union> B)"
    by (intro has_setprod_cong_neutral) (auto simp: fA_def)
  with assms(1) have fA: \<open>(fA has_setprod a) (A \<union> B)\<close>
    by blast
  have "(f has_setprod b) B \<longleftrightarrow> (fB has_setprod b) (A \<union> B)"
    using disj by (intro has_setprod_cong_neutral) (auto simp: fB_def)
  with assms(2) have fB: \<open>(fB has_setprod b) (A \<union> B)\<close>
    by blast
  have fAB: \<open>f x = fA x * fB x\<close> for x
    unfolding fA_def fB_def by simp
  show ?thesis
    unfolding fAB
    using fA fB by (rule has_setprod_mult)
qed

lemma has_setprod_finite:
  assumes "finite A"
  shows   "(f has_setprod (\<Prod>x\<in>A. f x)) A"
  using assms by (auto simp: finite_subsets_at_top_finite has_setprod_def principal_eq_bot_iff)

lemma has_setprod_unique: "(f has_setprod P) A \<Longrightarrow> (f has_setprod P') A \<Longrightarrow> P = P'"
  using has_setprodD tendsto_unique finite_subsets_at_top_neq_bot by metis

lemma has_setprod_finite_iff [simp]:
  assumes "finite A"
  shows   "(f has_setprod P) A \<longleftrightarrow> P = (\<Prod>x\<in>A. f x)"
  using has_setprod_finite assms has_setprod_unique by fast

lemma multipliable_on_cong_neutral: 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "f multipliable_on S \<longleftrightarrow> g multipliable_on T"
  using has_setprod_cong_neutral[of T S g f, OF assms]
  by (simp add: multipliable_on_def)

lemma infprod_cong_neutral: 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows \<open>infprod f S = infprod g T\<close>
  by (smt (verit, best) assms has_setprod_cong_neutral infprod_eqI')

lemma multipliable_on_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "f multipliable_on A \<longleftrightarrow> g multipliable_on A"
  by (metis assms multipliable_on_def has_setprod_cong)

lemma abs_multipliable_on_cong_neutral: 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "f abs_multipliable_on S \<longleftrightarrow> g abs_multipliable_on T"
  unfolding abs_multipliable_on_def by (intro multipliable_on_cong_neutral) (use assms in auto)

lemma abs_multipliable_on_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "f abs_multipliable_on A \<longleftrightarrow> g abs_multipliable_on A"
  unfolding abs_multipliable_on_def by (intro multipliable_on_cong) (use assms in auto)

lemma infprod_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infprod f A = infprod g A"
  using assms infprod_eqI' has_setprod_cong by blast


lemma multipliable_on_cofin_subset:
  fixes f :: \<open>'a \<Rightarrow> 'b::real_normed_field\<close>
  assumes "f multipliable_on A" and "finite F" and "\<And>x. x \<in> F \<Longrightarrow> f x \<noteq> 0"
  shows "f multipliable_on (A - F)"
proof -
  define G where \<open>G = A \<inter> F\<close>
  have G_fin: \<open>finite G\<close>
    using assms(2) unfolding G_def by blast
  have G_sub: \<open>G \<subseteq> A\<close>
    unfolding G_def by blast
  have G_nz: \<open>prod f G \<noteq> 0\<close>
    unfolding G_def using assms(2,3)
    by (subst prod_zero_iff) auto
  from assms(1) obtain p where hp: \<open>(f has_setprod p) A\<close>
    unfolding multipliable_on_def by blast
  then have lim: \<open>(prod f \<longlongrightarrow> p) (finite_subsets_at_top A)\<close>
    unfolding has_setprod_def .
  have filt: \<open>filterlim (\<lambda>X. X \<union> G) (finite_subsets_at_top A) (finite_subsets_at_top (A - F))\<close>
    unfolding filterlim_def le_filter_def eventually_filtermap
  proof safe
    fix P assume \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. P X\<close>
    then obtain X0 where X0: \<open>finite X0\<close> \<open>X0 \<subseteq> A\<close>
        and X0_P: \<open>\<And>X. finite X \<Longrightarrow> X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> P X\<close>
      unfolding eventually_finite_subsets_at_top by metis
    show \<open>\<forall>\<^sub>F X in finite_subsets_at_top (A - F). P (X \<union> G)\<close>
      unfolding eventually_finite_subsets_at_top
    proof (intro exI allI conjI impI)
      show \<open>finite (X0 - F)\<close> using X0(1) by blast
      show \<open>X0 - F \<subseteq> A - F\<close> using X0(2) by blast
    next
      fix X assume X: \<open>finite X \<and> X0 - F \<subseteq> X \<and> X \<subseteq> A - F\<close>
      have \<open>X0 \<subseteq> X \<union> G\<close>
        using X X0(2) unfolding G_def by blast
      moreover have \<open>X \<union> G \<subseteq> A\<close>
        using X G_sub by blast
      ultimately show \<open>P (X \<union> G)\<close>
        by (intro X0_P) (use X G_fin in auto)
    qed
  qed
  have ev_eq: \<open>\<forall>\<^sub>F X in finite_subsets_at_top (A - F). prod f (X \<union> G) = prod f X * prod f G\<close>
    unfolding eventually_finite_subsets_at_top
  proof (rule exI[of _ \<open>{}\<close>], intro allI conjI impI)
    fix X assume X: \<open>finite X \<and> {} \<subseteq> X \<and> X \<subseteq> A - F\<close>
    then have \<open>X \<inter> G = {}\<close> unfolding G_def by blast
    then show \<open>prod f (X \<union> G) = prod f X * prod f G\<close>
      using X G_fin by (subst prod.union_disjoint) auto
  qed auto
  have \<open>(prod f \<longlongrightarrow> p) (filtermap (\<lambda>X. X \<union> G) (finite_subsets_at_top (A - F)))\<close>
    using lim filt by (metis filterlim_def tendsto_mono)
  then have comp: \<open>((\<lambda>X. prod f (X \<union> G)) \<longlongrightarrow> p) (finite_subsets_at_top (A - F))\<close>
    by (subst (asm) tendsto_compose_filtermap[symmetric]) (simp add: o_def)
  have \<open>((\<lambda>X. prod f X * prod f G) \<longlongrightarrow> p) (finite_subsets_at_top (A - F))\<close>
    using comp ev_eq by (rule Lim_transform_eventually)
  then have \<open>((\<lambda>X. prod f X * prod f G) \<longlongrightarrow> (p / prod f G) * prod f G) (finite_subsets_at_top (A - F))\<close>
    by (simp add: G_nz)
  then have \<open>(prod f \<longlongrightarrow> p / prod f G) (finite_subsets_at_top (A - F))\<close>
    using G_nz by (subst (asm) tendsto_mult_right_iff)
  thus ?thesis
    unfolding multipliable_on_def has_setprod_def by blast
qed

lemma zero_imp_has_setprod_0:
  assumes "x \<in> A" "f x = 0"
  shows   "(f has_setprod 0) A"
proof -
  have "eventually (\<lambda>X. {x} \<subseteq> X \<and> finite X) (finite_subsets_at_top A)"
    unfolding eventually_finite_subsets_at_top using assms by force
  hence "eventually (\<lambda>X. prod f X = 0) (finite_subsets_at_top A)"
    by eventually_elim (use assms in auto)
  thus ?thesis
    unfolding has_setprod_def using tendsto_eventually by blast
qed  

lemma
  fixes a b :: "'a::real_normed_field"
  assumes \<open>(f has_setprod b) B\<close> and \<open>(f has_setprod a) A\<close> and AB: "A \<subseteq> B"
  assumes [simp]: "a \<noteq> 0"
  shows has_setprod_Diff: "(f has_setprod (b / a)) (B - A)"
proof -
  have nonzero: "f x \<noteq> 0" if "x \<in> A" for x
    using that assms(2) using zero_imp_has_setprod_0[of x A f] has_setprod_unique
    by fastforce
  have finite_subsets1:
    "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
  proof (rule filter_leI)
    fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
    then obtain X where "finite X" and "X \<subseteq> B" 
      and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
      unfolding eventually_filtermap eventually_finite_subsets_at_top by auto
    hence "finite (X-A)" and "X-A \<subseteq> B - A"
      by auto
    moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
      using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
      by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
    ultimately show "eventually P (finite_subsets_at_top (B - A))"
      unfolding eventually_finite_subsets_at_top by meson
  qed
  have finite_subsets2: 
    "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
    apply (rule filter_leI)
      using assms unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (metis Int_subset_iff finite_Int inf_le2 subset_trans)

  from assms(1) have limB: "(prod f \<longlongrightarrow> b) (finite_subsets_at_top B)"
    using has_setprod_def by auto
  from assms(2) have limA: "(prod f \<longlongrightarrow> a) (finite_subsets_at_top A)"
    using has_setprod_def by blast
  have "((\<lambda>F. prod f (F\<inter>A)) \<longlongrightarrow> a) (finite_subsets_at_top B)"
  proof (subst asm_rl [of "(\<lambda>F. prod f (F\<inter>A)) = prod f \<circ> (\<lambda>F. F\<inter>A)"])
    show "(\<lambda>F. prod f (F \<inter> A)) = prod f \<circ> (\<lambda>F. F \<inter> A)"
      unfolding o_def by auto
    show "((prod f \<circ> (\<lambda>F. F \<inter> A)) \<longlongrightarrow> a) (finite_subsets_at_top B)"
      unfolding o_def 
      using tendsto_compose_filtermap finite_subsets2 limA tendsto_mono
        \<open>(\<lambda>F. prod f (F \<inter> A)) = prod f \<circ> (\<lambda>F. F \<inter> A)\<close> by fastforce
  qed

  with limB have "((\<lambda>F. prod f F / prod f (F\<inter>A)) \<longlongrightarrow> b / a) (finite_subsets_at_top B)"
    by (intro tendsto_divide) auto
  have "prod f X / prod f (X \<inter> A) = prod f (X - A)" 
    if "finite X" and "X \<subseteq> B" for X :: "'b set"
  proof (subst prod.Int_Diff[of _ _ A])
    have "prod f (X \<inter> A) \<noteq> 0"
      using that by (auto simp: nonzero)
    thus "prod f (X \<inter> A) * prod f (X - A) / prod f (X \<inter> A) = prod f (X - A)"
      by simp
  qed fact+
  hence "\<forall>\<^sub>F x in finite_subsets_at_top B. prod f x / prod f (x \<inter> A) = prod f (x - A)"
    by (rule eventually_finite_subsets_at_top_weakI)  
  hence "((\<lambda>F. prod f (F-A)) \<longlongrightarrow> b / a) (finite_subsets_at_top B)"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>F. prod f F / prod f (F \<inter> A)) \<longlongrightarrow> b / a) (finite_subsets_at_top B)\<close> by fastforce
  hence "(prod f \<longlongrightarrow> b / a) (filtermap (\<lambda>F. F-A) (finite_subsets_at_top B))"
    by (subst tendsto_compose_filtermap[symmetric], simp add: o_def)
  thus ?thesis
    using finite_subsets1 has_setprod_def tendsto_mono by blast
qed

lemma multipliable_on_finite[simp]:
  assumes "finite F"
  shows "f multipliable_on F"
  using assms multipliable_on_def has_setprod_finite by blast

lemma abs_multipliable_on_finite[simp]:
  assumes "finite F"
  shows "f abs_multipliable_on F"
  unfolding abs_multipliable_on_def using assms by simp

lemma infprod_finite[simp]:
  assumes "finite F"
  shows "infprod f F = prod f F"
  using assms by (simp add: has_setprod_finite infprodI)

lemma has_setprod_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{semidom,topological_semigroup_mult,metric_space}"
  assumes "(f has_setprod x) A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (prod f F) x \<le> \<epsilon>"
proof -
  have "(prod f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    by (simp add: assms(1) has_setprodD)
  hence *: "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (prod f F) x < \<epsilon>"
    using assms(2) by (rule tendstoD)
  thus ?thesis
    unfolding eventually_finite_subsets_at_top by fastforce
qed

lemma infprod_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{semidom,topological_semigroup_mult,metric_space}"
  assumes "f multipliable_on A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (prod f F) (infprod f A) \<le> \<epsilon>"
proof -
  from assms have "(f has_setprod (infprod f A)) A"
    by (simp add: multipliable_iff_has_setprod_infprod)
  from this and \<open>\<epsilon> > 0\<close> show ?thesis
    by (rule has_setprod_finite_approximation)
qed

theorem abs_convergent_prod_imp_convergent_prod:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra,complete_space,comm_ring_1}"
  assumes "abs_convergent_prod f"
  shows   "convergent_prod f"
proof -
  from assms have "eventually (\<lambda>n. f n \<noteq> 0) sequentially"
    by (rule abs_convergent_prod_imp_ev_nonzero)
  then obtain N where N: "f n \<noteq> 0" if "n \<ge> N" for n 
    by (auto simp: eventually_at_top_linorder)
  let ?P = "\<lambda>n. \<Prod>i\<le>n. f (i + N)" and ?Q = "\<lambda>n. \<Prod>i\<le>n. 1 + norm (f (i + N) - 1)"

  have "Cauchy ?P"
  proof (rule CauchyI', goal_cases)
    case (1 \<epsilon>)
    from assms have "abs_convergent_prod (\<lambda>n. f (n + N))"
      by (rule abs_convergent_prod_ignore_initial_segment)
    hence "Cauchy ?Q"
      unfolding abs_convergent_prod_def
      by (intro convergent_Cauchy convergent_prod_imp_convergent)
    from CauchyD[OF this 1] obtain M where M: "norm (?Q m - ?Q n) < \<epsilon>" if "m \<ge> M" "n \<ge> M" for m n
      by blast
    show ?case
    proof (rule exI[of _ M], safe, goal_cases)
      case (1 m n)
      have "dist (?P m) (?P n) = norm (?P n - ?P m)"
        by (simp add: dist_norm norm_minus_commute)
      also from 1 have "{..n} = {..m} \<union> {m<..n}" by auto
      hence "norm (?P n - ?P m) = norm (?P m * (\<Prod>k\<in>{m<..n}. f (k + N)) - ?P m)"
        by (subst prod.union_disjoint [symmetric]) (auto simp: algebra_simps)
      also have "\<dots> = norm (?P m * ((\<Prod>k\<in>{m<..n}. f (k + N)) - 1))"
        by (simp add: algebra_simps)
      also have "\<dots> = (\<Prod>k\<le>m. norm (f (k + N))) * norm ((\<Prod>k\<in>{m<..n}. f (k + N)) - 1)"
        by (simp add: norm_mult prod_norm)
      also have "\<dots> \<le> ?Q m * ((\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) - 1)"
        using norm_prod_minus1_le_prod_minus1[of "\<lambda>k. f (k + N) - 1" "{m<..n}"]
              norm_triangle_ineq[of 1 "f k - 1" for k]
        by (intro mult_mono prod_mono ballI conjI norm_prod_minus1_le_prod_minus1 prod_nonneg) auto
      also have "\<dots> = ?Q m * (\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) - ?Q m"
        by (simp add: algebra_simps)
      also have "?Q m * (\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) = 
                   (\<Prod>k\<in>{..m}\<union>{m<..n}. 1 + norm (f (k + N) - 1))"
        by (rule prod.union_disjoint [symmetric]) auto
      also from 1 have "{..m}\<union>{m<..n} = {..n}" by auto
      also have "?Q n - ?Q m \<le> norm (?Q n - ?Q m)" by simp
      also from 1 have "\<dots> < \<epsilon>" by (intro M) auto
      finally show ?case .
    qed
  qed
  hence conv: "convergent ?P" by (rule Cauchy_convergent)
  then obtain L where L: "?P \<longlonglongrightarrow> L"
    by (auto simp: convergent_def)

  have "L \<noteq> 0"
  proof
    assume [simp]: "L = 0"
    from tendsto_norm[OF L] have limit: "(\<lambda>n. \<Prod>k\<le>n. norm (f (k + N))) \<longlonglongrightarrow> 0" 
      by (simp add: prod_norm)

    from assms have "(\<lambda>n. f (n + N)) \<longlonglongrightarrow> 1"
      by (intro abs_convergent_prod_imp_LIMSEQ abs_convergent_prod_ignore_initial_segment)
    hence "eventually (\<lambda>n. norm (f (n + N) - 1) < 1) sequentially"
      by (auto simp: tendsto_iff dist_norm)
    then obtain M0 where M0: "norm (f (n + N) - 1) < 1" if "n \<ge> M0" for n
      by (auto simp: eventually_at_top_linorder)

    {
      fix M assume M: "M \<ge> M0"
      with M0 have M: "norm (f (n + N) - 1) < 1" if "n \<ge> M" for n using that by simp

      have "(\<lambda>n. \<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<longlonglongrightarrow> 0"
      proof (rule tendsto_sandwich)
        show "eventually (\<lambda>n. (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<ge> 0) sequentially"
          using M by (intro always_eventually prod_nonneg allI ballI) (auto intro: less_imp_le)
        have "norm (1::'a) - norm (f (i + M + N) - 1) \<le> norm (f (i + M + N))" for i
          using norm_triangle_ineq3[of "f (i + M + N)" 1] by simp
        thus "eventually (\<lambda>n. (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<le> (\<Prod>k\<le>n. norm (f (k+M+N)))) at_top"
          using M by (intro always_eventually allI prod_mono ballI conjI) (auto intro: less_imp_le)
        
        define C where "C = (\<Prod>k<M. norm (f (k + N)))"
        from N have [simp]: "C \<noteq> 0" by (auto simp: C_def)
        from L have "(\<lambda>n. norm (\<Prod>k\<le>n+M. f (k + N))) \<longlonglongrightarrow> 0"
          by (intro LIMSEQ_ignore_initial_segment) (simp add: tendsto_norm_zero_iff)
        also have "(\<lambda>n. norm (\<Prod>k\<le>n+M. f (k + N))) = (\<lambda>n. C * (\<Prod>k\<le>n. norm (f (k + M + N))))"
        proof (rule ext, goal_cases)
          case (1 n)
          have "{..n+M} = {..<M} \<union> {M..n+M}" by auto
          also have "norm (\<Prod>k\<in>\<dots>. f (k + N)) = C * norm (\<Prod>k=M..n+M. f (k + N))"
            unfolding C_def by (subst prod.union_disjoint) (auto simp: norm_mult prod_norm)
          also have "(\<Prod>k=M..n+M. f (k + N)) = (\<Prod>k\<le>n. f (k + N + M))"
            by (intro prod.reindex_bij_witness[of _ "\<lambda>i. i + M" "\<lambda>i. i - M"]) auto
          finally show ?case by (simp add: add_ac prod_norm)
        qed
        finally have "(\<lambda>n. C * (\<Prod>k\<le>n. norm (f (k + M + N))) / C) \<longlonglongrightarrow> 0 / C"
          by (intro tendsto_divide tendsto_const) auto
        thus "(\<lambda>n. \<Prod>k\<le>n. norm (f (k + M + N))) \<longlonglongrightarrow> 0" by simp
      qed simp_all

      have "1 - (\<Sum>i. norm (f (i + M + N) - 1)) \<le> 0"
      proof (rule tendsto_le)
        show "eventually (\<lambda>n. 1 - (\<Sum>k\<le>n. norm (f (k+M+N) - 1)) \<le> 
                                (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1))) at_top"
          using M by (intro always_eventually allI Weierstrass_prod_ineq) (auto intro: less_imp_le)
        show "(\<lambda>n. \<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<longlonglongrightarrow> 0" by fact
        show "(\<lambda>n. 1 - (\<Sum>k\<le>n. norm (f (k + M + N) - 1)))
                  \<longlonglongrightarrow> 1 - (\<Sum>i. norm (f (i + M + N) - 1))"
          by (intro tendsto_intros summable_LIMSEQ' summable_ignore_initial_segment 
                abs_convergent_prod_imp_summable assms)
      qed simp_all
      hence "(\<Sum>i. norm (f (i + M + N) - 1)) \<ge> 1" by simp
      also have "\<dots> + (\<Sum>i<M. norm (f (i + N) - 1)) = (\<Sum>i. norm (f (i + N) - 1))"
        by (intro suminf_split_initial_segment [symmetric] summable_ignore_initial_segment
              abs_convergent_prod_imp_summable assms)
      finally have "1 + (\<Sum>i<M. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))" by simp
    } note * = this

    have "1 + (\<Sum>i. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))"
    proof (rule tendsto_le)
      show "(\<lambda>M. 1 + (\<Sum>i<M. norm (f (i + N) - 1))) \<longlonglongrightarrow> 1 + (\<Sum>i. norm (f (i + N) - 1))"
        by (intro tendsto_intros summable_LIMSEQ summable_ignore_initial_segment 
                abs_convergent_prod_imp_summable assms)
      show "eventually (\<lambda>M. 1 + (\<Sum>i<M. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))) at_top"
        using eventually_ge_at_top[of M0] by eventually_elim (use * in auto)
    qed simp_all
    thus False by simp
  qed
  with L show ?thesis by (auto simp: prod_defs)
qed

lemma abs_multipliable_multipliable:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {banach, real_normed_div_algebra, semidom}\<close>
  assumes \<open>f abs_multipliable_on A\<close>
  shows \<open>f multipliable_on A\<close>
proof -
  define g where "g x = 1 + norm (f x - 1)" for x
  from assms obtain L where lim: "(prod g \<longlongrightarrow> L) (finite_subsets_at_top A)"
    unfolding abs_multipliable_on_def multipliable_on_def has_setprod_def g_def by blast
  have g_ge: "g x \<ge> 1" for x
    unfolding g_def by auto
  have g_ge0: "g x \<ge> 0" for x
    using g_ge[of x] by linarith
  have norm_f_le_g: "norm (f x) \<le> g x" for x
  proof -
    have "norm (f x) = norm (1 + (f x - 1))" by simp
    also have "\<dots> \<le> norm (1::'b) + norm (f x - 1)" by (rule norm_triangle_ineq)
    also have "\<dots> = 1 + norm (f x - 1)" by simp
    also have "\<dots> = g x" unfolding g_def ..
    finally show ?thesis .
  qed
  have norm_prod_le_prod_g: "norm (prod f F) \<le> prod g F" if "finite F" for F
  proof -
    have "norm (prod f F) = prod (\<lambda>x. norm (f x)) F"
      by (simp add: prod_norm)
    also have "\<dots> \<le> prod g F"
      by (intro prod_mono conjI norm_f_le_g ballI) auto
    finally show ?thesis .
  qed
  have prod_g_nonneg: "prod g F \<ge> 0" if "finite F" for F
    by (intro prod_nonneg ballI) (use g_ge0 in auto)
  have dist_le: "dist (prod f F1) (prod f F2) \<le> dist (prod g F1) (prod g F2)"
    if F12: "F2 \<subseteq> F1" "finite F1" "F1 \<subseteq> A" for F1 F2
  proof -
    from F12 have finF2: "finite F2" using finite_subset by blast
    have "prod f F1 = prod f (F1 - F2) * prod f F2"
      using prod.subset_diff[OF F12(1,2)] by (simp add: mult.commute)
    hence eq1: "prod f F1 - prod f F2 = (prod f (F1 - F2) - 1) * prod f F2"
      by (simp add: algebra_simps)
    have "prod g F1 = prod g (F1 - F2) * prod g F2"
      using prod.subset_diff[OF F12(1,2)] by (simp add: mult.commute)
    hence eq2: "prod g F1 - prod g F2 = (prod g (F1 - F2) - 1) * prod g F2"
      by (simp add: algebra_simps)
    have key1: "norm (prod f (F1 - F2) - 1) \<le> prod g (F1 - F2) - 1"
    proof -
      have aux: "norm ((\<Prod>x\<in>S. f x) - 1) \<le> (\<Prod>x\<in>S. g x) - 1" if "finite S" for S
        using that
      proof (induction S)
        case empty
        then show ?case by simp
      next
        case (insert x S)
        have "norm ((\<Prod>y\<in>insert x S. f y) - 1) = norm (f x * prod f S - 1)"
          using insert.hyps by simp
        also have "\<dots> = norm ((f x - 1) * prod f S + (prod f S - 1))"
          by (simp add: algebra_simps)
        also have "\<dots> \<le> norm ((f x - 1) * prod f S) + norm (prod f S - 1)"
          by (rule norm_triangle_ineq)
        also have "\<dots> = norm (f x - 1) * norm (prod f S) + norm (prod f S - 1)"
          by (simp add: norm_mult)
        also have "\<dots> \<le> norm (f x - 1) * prod g S + (prod g S - 1)"
          by (simp add: add_mono insert mult_mono norm_prod_le_prod_g)
        also have "\<dots> = (1 + norm (f x - 1)) * prod g S - 1"
          by (simp add: algebra_simps)
        also have "\<dots> = g x * prod g S - 1"
          unfolding g_def ..
        also have "g x * prod g S = (\<Prod>y\<in>insert x S. g y)"
          using insert.hyps by simp
        finally show ?case by simp
      qed
      thus ?thesis
        using F12(2) by (auto intro: finite_Diff)
    qed
    have key2: "norm (prod f F2) \<le> prod g F2"
      using finF2 by (rule norm_prod_le_prod_g)
    have g_diff_ge1: "prod g (F1 - F2) \<ge> 1"
      by (meson DiffD1 F12(2) finite_Diff g_ge prod_ge_1)
    have g_F2_ge0: "prod g F2 \<ge> 0"
      using finF2 by (rule prod_g_nonneg)
    have "norm (prod f F1 - prod f F2) = norm ((prod f (F1 - F2) - 1) * prod f F2)"
      by (simp add: eq1)
    also have "\<dots> = norm (prod f (F1 - F2) - 1) * norm (prod f F2)"
      by (rule norm_mult)
    also have "\<dots> \<le> (prod g (F1 - F2) - 1) * prod g F2"
      by (intro mult_mono key1 key2 norm_ge_zero) (use g_diff_ge1 in linarith)
    also have "\<dots> = prod g F1 - prod g F2"
      using eq2 by simp
    also have "\<dots> \<le> \<bar>prod g F1 - prod g F2\<bar>"
      by linarith
    also have "\<dots> = dist (prod g F1) (prod g F2)"
      unfolding dist_real_def ..
    finally show ?thesis unfolding dist_norm .
  qed
  \<comment> \<open>The absolute product is Cauchy, so the original product is too\<close>
  have cauchy_f: "cauchy_filter (filtermap (prod f) (finite_subsets_at_top A))"
    unfolding cauchy_filter_metric_filtermap
  proof (intro allI impI)
    fix e :: real assume "e > 0"
    \<comment> \<open>Since prod g converges to L, it is Cauchy\<close>
    from lim have cauchy_g: "cauchy_filter (filtermap (prod g) (finite_subsets_at_top A))"
      by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)
    define d where "d = e / 2"
    have "d > 0" using \<open>e > 0\<close> unfolding d_def by simp
    have "\<exists>P. eventually P (finite_subsets_at_top A) \<and>
              (\<forall>x y. P x \<and> P y \<longrightarrow> dist (prod g x) (prod g y) < d)"
      using cauchy_g \<open>d > 0\<close> by (simp add: cauchy_filter_metric_filtermap)
    then obtain P where ev_P: "eventually P (finite_subsets_at_top A)"
      and P_close: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> dist (prod g x) (prod g y) < d"
      by blast
    from ev_P obtain F0 where F0: "finite F0" "F0 \<subseteq> A"
      and F0_P: "\<And>F. finite F \<Longrightarrow> F0 \<subseteq> F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> P F"
      unfolding eventually_finite_subsets_at_top by metis
    define Q where "Q F \<longleftrightarrow> finite F \<and> F0 \<subseteq> F \<and> F \<subseteq> A" for F
    have ev_Q: "eventually Q (finite_subsets_at_top A)"
      unfolding Q_def eventually_finite_subsets_at_top using F0 by blast
    have "dist (prod f x) (prod f y) < e" if "Q x" "Q y" for x y
    proof -
      define F where "F = x \<union> y"
      have F_fin: "finite F" and F_sub: "F \<subseteq> A" and x_sub: "x \<subseteq> F" and y_sub: "y \<subseteq> F"
        using that unfolding F_def Q_def by auto
      have F0_sub_F: "F0 \<subseteq> F" using that unfolding F_def Q_def by auto
      have "P F" using F0_P F_fin F0_sub_F F_sub by auto
      have "P x" using F0_P that unfolding Q_def by auto
      have "P y" using F0_P that unfolding Q_def by auto
      have fx_le: "dist (prod f F) (prod f x) \<le> dist (prod g F) (prod g x)"
        using dist_le[of x F] x_sub F_fin F_sub by auto
      have fy_le: "dist (prod f F) (prod f y) \<le> dist (prod g F) (prod g y)"
        using dist_le[of y F] y_sub F_fin F_sub by auto
      have gx_lt: "dist (prod g F) (prod g x) < d"
        using P_close[OF \<open>P F\<close> \<open>P x\<close>] .
      have gy_lt: "dist (prod g F) (prod g y) < d"
        using P_close[OF \<open>P F\<close> \<open>P y\<close>] .
      have "dist (prod f x) (prod f y) \<le> dist (prod f F) (prod f x) + dist (prod f F) (prod f y)"
        by (rule dist_triangle3)
      also have "\<dots> \<le> dist (prod g F) (prod g x) + dist (prod g F) (prod g y)"
        by (intro add_mono fx_le fy_le)
      also have "\<dots> < d + d"
        by (intro add_strict_mono gx_lt gy_lt)
      also have "\<dots> = e" unfolding d_def by simp
      finally show ?thesis .
    qed
    thus "\<exists>P. eventually P (finite_subsets_at_top A) \<and>
              (\<forall>x y. P x \<and> P y \<longrightarrow> dist (prod f x) (prod f y) < e)"
      using ev_Q by blast
  qed
  moreover have "complete (UNIV :: 'b set)"
    using Cauchy_convergent complete_def convergent_def by blast
  ultimately obtain L' where "(prod f \<longlongrightarrow> L') (finite_subsets_at_top A)"
    using cauchy_filter_complete_converges[of "filtermap (prod f) (finite_subsets_at_top A)" UNIV]
    by (auto simp: filterlim_def filtermap_bot_iff)
  thus ?thesis
    unfolding multipliable_on_def has_setprod_def by blast
qed

lemma infprod_tendsto:
  assumes \<open>f multipliable_on S\<close>
  shows \<open>((\<lambda>F. prod f F) \<longlongrightarrow> infprod f S) (finite_subsets_at_top S)\<close>
  using assms has_setprod_infprod by (simp add: has_setprodD)

lemma has_setprod_1: 
  assumes \<open>\<And>x. x \<in> M \<Longrightarrow> f x = 1\<close>
  shows \<open>(f has_setprod 1) M\<close>
proof -
  have "(f has_setprod 1) M \<longleftrightarrow> ((\<lambda>_ :: 'a. 1 :: 'b) has_setprod 1) {}"
    by (intro has_setprod_cong_neutral) (use assms in auto)
  thus ?thesis
    by simp
qed

lemma multipliable_on_1:
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 1\<close>
  shows \<open>f multipliable_on M\<close>
  using assms multipliable_on_def has_setprod_1 by blast

lemma infprod_1:
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 1\<close>
  shows \<open>infprod f M = 1\<close>
  using assms by (simp add: has_setprod_1 infprodI)

lemma infprod_0_simp[simp]: \<open>infprod (\<lambda>_. 1) M = 1\<close>
  by (simp_all add: infprod_1)

lemma multipliable_on_0_simp[simp]: \<open>(\<lambda>_. 1) multipliable_on M\<close>
  by (simp_all add: multipliable_on_1)

lemma has_setprod_0_simp[simp]: \<open>((\<lambda>_. 1) has_setprod 1) M\<close>
  by (simp_all add: has_setprod_1)

lemma multipliable_on_mult:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes \<open>f multipliable_on A\<close>
  assumes \<open>g multipliable_on A\<close>
  shows \<open>(\<lambda>x. f x * g x) multipliable_on A\<close>
  by (metis (full_types) assms multipliable_on_def has_setprod_mult)

lemma infprod_mult:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes \<open>f multipliable_on A\<close>
  assumes \<open>g multipliable_on A\<close>
  shows \<open>infprod (\<lambda>x. f x * g x) A = infprod f A * infprod g A\<close>
  by (simp add: assms has_setprod_mult infprodI)

lemma multipliable_on_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes "f multipliable_on A"
  assumes "f multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>f multipliable_on (A \<union> B)\<close>
  by (meson assms disj multipliable_on_def has_setprod_Un_disjoint)

lemma abs_multipliable_on_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: real_normed_algebra_1"
  assumes "f abs_multipliable_on A"
  assumes "f abs_multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>f abs_multipliable_on (A \<union> B)\<close>
  using assms unfolding abs_multipliable_on_def by (intro multipliable_on_Un_disjoint)

lemma infprod_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes "f multipliable_on A"
  assumes "f multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>infprod f (A \<union> B) = infprod f A * infprod f B\<close>
  by (intro infprodI has_setprod_Un_disjoint has_setprod_infprod assms)  

lemma abs_convergent_prod_imp_setprod:
  fixes f :: "nat \<Rightarrow> 'b :: real_normed_field"
  assumes "abs_convergent_prod f" and "f has_prod P"
  shows   "(f has_setprod P) (UNIV :: nat set)"
proof (rule has_setprodI, unfold tendsto_iff, intro allI impI)
  fix e :: real assume \<open>e > 0\<close>
  from assms(2) have seq_lim: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> P\<close>
    by (rule has_prod_imp_tendsto)
  from assms(1) have ev_nz: \<open>\<forall>\<^sub>F n in sequentially. f n \<noteq> 0\<close>
    by (rule abs_convergent_prod_imp_ev_nonzero)
  then obtain N0 where N0: \<open>\<And>n. n \<ge> N0 \<Longrightarrow> f n \<noteq> 0\<close>
    by (auto simp: eventually_at_top_linorder)

  \<comment> \<open>The absolute product converges sequentially\<close>
  define g where \<open>g n = 1 + norm (f n - 1)\<close> for n
  from assms(1)[unfolded abs_convergent_prod_def]
  have abs_conv: \<open>convergent_prod g\<close> unfolding g_def .
  have g_nz: \<open>g n \<noteq> 0\<close> for n
    unfolding g_def by (metis le_add_same_cancel1 norm_ge_zero not_one_le_zero)
  then obtain L_abs where L_abs: \<open>g has_prod L_abs\<close> and \<open>L_abs \<noteq> 0\<close>
    using abs_conv convergent_prod_has_prod prodinf_nonzero by blast
  have g_ge1: \<open>g n \<ge> 1\<close> for n unfolding g_def by auto
  have g_ge0: \<open>g n \<ge> 0\<close> for n using g_ge1[of n] by linarith
  from L_abs have g_seq: \<open>(\<lambda>n. prod g {..n}) \<longlonglongrightarrow> L_abs\<close>
    by (rule has_prod_imp_tendsto)
  have norm_bound: \<open>norm ((\<Prod>n\<in>S. f n) - 1) \<le> (\<Prod>n\<in>S. g n) - 1\<close>
    if \<open>finite S\<close> for S :: \<open>nat set\<close>
    using norm_prod_minus1_le_prod_minus1[of \<open>\<lambda>n. f n - 1\<close> S] by (simp add: g_def)
  have norm_prod_bound: \<open>norm (prod f S) \<le> prod g S\<close>
    if \<open>finite S\<close> for S :: \<open>nat set\<close>
    using that
  proof induction
    case empty
    then show ?case by auto
  next
    case (insert n S)
    then show ?case
      by (metis (no_types, lifting) prod_norm g_def prod_mono norm_ge_zero norm_one norm_triangle_sub)
  qed

  \<comment> \<open>Partial products of g are bounded\<close>
  have g_partial_le: \<open>prod g {..n} \<le> L_abs\<close> for n
  proof (rule ccontr)
    assume \<open>\<not> prod g {..n} \<le> L_abs\<close>
    then have gt: \<open>prod g {..n} > L_abs\<close> by simp
    define e' where \<open>e' = prod g {..n} - L_abs\<close>
    have \<open>e' > 0\<close> using gt by (simp add: e'_def)
    from g_seq[unfolded tendsto_iff, rule_format, OF this]
    obtain N' where N': \<open>\<And>m. m \<ge> N' \<Longrightarrow> dist (prod g {..m}) L_abs < e'\<close>
      by (auto simp: eventually_at_top_linorder)
    have \<open>prod g {..n} \<le> prod g {..max n N'}\<close>
      by (intro prod_mono2) (use g_ge1 g_ge0 in auto)
    hence \<open>dist (prod g {..max n N'}) L_abs \<ge> e'\<close>
      using gt by (simp add: dist_real_def e'_def)
    moreover have \<open>dist (prod g {..max n N'}) L_abs < e'\<close>
      using N'[of \<open>max n N'\<close>] by simp
    ultimately show False by linarith
  qed

  show \<open>\<forall>\<^sub>F x in finite_subsets_at_top (UNIV :: nat set). dist (prod f x) P < e\<close>
  proof -
    from seq_lim[unfolded tendsto_iff, rule_format, OF half_gt_zero[OF \<open>e > 0\<close>]]
    obtain N1 where N1: \<open>\<And>n. n \<ge> N1 \<Longrightarrow> dist (prod f {..n}) P < e/2\<close>
      by (auto simp: eventually_at_top_linorder)
    from g_seq[unfolded tendsto_iff, rule_format, OF half_gt_zero[OF \<open>e > 0\<close>]]
    obtain N2 where N2: \<open>\<And>n. n \<ge> N2 \<Longrightarrow> dist (prod g {..n}) L_abs < e/2\<close>
      by (auto simp: eventually_at_top_linorder)
    define N where \<open>N = max N1 N2\<close>
    \<comment> \<open>The witness set is @term\<open>{..N}\<close>\<close>
    show ?thesis
      unfolding eventually_finite_subsets_at_top
    proof (intro exI conjI allI impI)
      show \<open>finite {..N}\<close> by simp
      show \<open>{..N} \<subseteq> (UNIV :: nat set)\<close> by simp
    next
      fix Y :: \<open>nat set\<close>
      assume Y: \<open>finite Y \<and> {..N} \<subseteq> Y \<and> Y \<subseteq> UNIV\<close>
      then have finY: \<open>finite Y\<close> and NY: \<open>{..N} \<subseteq> Y\<close> by auto
      define M where \<open>M = Max Y\<close>
      have \<open>Y \<noteq> {}\<close> using NY by auto
      then have MMax: \<open>M = Max Y\<close> and MY: \<open>Y \<subseteq> {..M}\<close> and MN: \<open>M \<ge> N\<close>
        using finY NY by (auto simp: M_def intro: Max_ge subset_iff[THEN iffD2])
      have finM: \<open>finite {..M}\<close> by simp
      have factor_f: \<open>prod f {..M} = prod f ({..M} - Y) * prod f Y\<close>
        using prod.subset_diff[OF MY finM, of f] .
      have factor_g: \<open>prod g {..M} = prod g ({..M} - Y) * prod g Y\<close>
        using prod.subset_diff[OF MY finM, of g] .
      have dist_bound: \<open>dist (prod f Y) (prod f {..M}) \<le> L_abs - prod g {..N}\<close>
      proof -
        have \<open>dist (prod f Y) (prod f {..M}) = norm (prod f Y - prod f {..M})\<close>
          by (simp add: dist_norm)
        also have \<open>\<dots> = norm (prod f Y - prod f ({..M} - Y) * prod f Y)\<close>
          by (simp add: factor_f mult.commute)
        also have \<open>\<dots> = norm (prod f Y * (1 - prod f ({..M} - Y)))\<close>
          by (simp add: algebra_simps)
        also have \<open>\<dots> = norm (prod f Y) * norm (1 - prod f ({..M} - Y))\<close>
          by (simp add: norm_mult)
        also have \<open>\<dots> = norm (prod f Y) * norm (prod f ({..M} - Y) - 1)\<close>
          by (metis norm_minus_commute)
        also have \<open>\<dots> \<le> prod g Y * (prod g ({..M} - Y) - 1)\<close>
        proof (intro mult_mono)
          show \<open>norm (prod f Y) \<le> prod g Y\<close>
            using norm_prod_bound[OF finY] .
          show \<open>norm (prod f ({..M} - Y) - 1) \<le> prod g ({..M} - Y) - 1\<close>
            using norm_bound[of \<open>{..M} - Y\<close>] finM finite_Diff by blast
          show \<open>0 \<le> norm (prod f ({..M} - Y) - 1)\<close> by simp
          show \<open>0 \<le> prod g Y\<close>
            by (intro prod_nonneg) (use g_ge0 in auto)
        qed
        also have \<open>\<dots> = prod g {..M} - prod g Y\<close>
          using factor_g by (simp add: algebra_simps)
        also have \<open>\<dots> \<le> prod g {..M} - prod g {..N}\<close>
        proof -
          have \<open>prod g {..N} \<le> prod g Y\<close>
            by (intro prod_mono2 finY) (use NY g_ge1 g_ge0 in auto)
          thus ?thesis by linarith
        qed
        also have \<open>\<dots> \<le> L_abs - prod g {..N}\<close>
          using g_partial_le by force
        finally show ?thesis .
      qed
      have tail_bound: \<open>L_abs - prod g {..N} < e/2\<close>
      proof -
        have \<open>dist (prod g {..N}) L_abs < e/2\<close>
          using N2[of N] by (auto simp: N_def)
        moreover have \<open>prod g {..N} \<le> L_abs\<close>
          using g_partial_le .
        ultimately show ?thesis by (simp add: dist_real_def)
      qed
      have seq_bound: \<open>dist (prod f {..M}) P < e/2\<close>
        using N1[of M] MN by (auto simp: N_def)
      \<comment> \<open>Combine\<close>
      have \<open>dist (prod f Y) P \<le> dist (prod f Y) (prod f {..M}) + dist (prod f {..M}) P\<close>
        by (rule dist_triangle)
      also have \<open>\<dots> < (L_abs - prod g {..N}) + e/2\<close>
        using dist_bound seq_bound by linarith
      also have \<open>\<dots> < e/2 + e/2\<close> using tail_bound by linarith
      also have \<open>\<dots> = e\<close> by simp
      finally show \<open>dist (prod f Y) P < e\<close> .
    qed
  qed
qed


lemma abs_convergent_prod_imp_multipliable_on:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field,complete_space,comm_ring_1}"
  assumes "abs_convergent_prod f"
  shows   "f multipliable_on UNIV"
proof -
  from assms have "convergent_prod f"
    by (rule abs_convergent_prod_imp_convergent_prod)
  thus ?thesis
    using abs_convergent_prod_imp_setprod[OF assms] multipliable_on_def by blast
qed

subsection \<open>Subsets\<close>

text \<open>
  For sums, unordered summability on \<^term>\<open>A\<close> passes to every subset of \<^term>\<open>A\<close>
  (\<open>summable_on_subset_banach\<close>).  For products the corresponding statement with only the side
  condition @{term\<open>f x \<noteq> 0\<close>} for @{term\<open>x \<in> A - B\<close>} is \<^emph>\<open>false\<close>, and no strengthening of the type class
  helps.  A counterexample already exists over \<^typ>\<open>real\<close>: take the index type
  \<^typ>\<open>bool \<times> nat\<close>, let \<^term>\<open>A = UNIV\<close> and let \<open>B\<close> be the \<open>True\<close> half, and put
  @{term\<open>f p = (if fst p then -1 else 1/2)\<close>}.  The factors \<open>1/2\<close> force the partial products over
  \<^term>\<open>A\<close> to tend to \<open>0\<close>, so \<open>f\<close> is multipliable on \<^term>\<open>A\<close>, and \<open>f\<close> is non-zero
  everywhere; but over \<open>B\<close> the partial products are \<open>1\<close> and \<open>-1\<close> alternately, so \<open>f\<close> is not
  multipliable on \<open>B\<close>.

  The obstruction is a product equal to \<open>0\<close>: it lets the partial products shrink to \<open>0\<close> along
  \<^term>\<open>A\<close> while oscillating along \<open>B\<close>.  Excluding it -- that is, assuming a \<^emph>\<open>non-zero\<close>
  product, equivalently strong multipliability -- makes the subset principle true, and that is
  what we prove here.  The engine is the multiplicative Cauchy criterion
  \<open>has_setprod_prods_near_1\<close>: multiplication is not uniformly continuous on all of \<^term>\<open>UNIV\<close>,
  which is why the additive proof cannot be transferred, but it is uniformly continuous away
  from \<open>0\<close>, and for a non-zero product all the far-out subproducts live near \<open>1\<close>.
\<close>

text \<open>
  The multiplicative Cauchy criterion: if the product over \<^term>\<open>M\<close> converges to a non-zero
  limit then, outside a suitable finite set, \<^emph>\<open>every\<close> finite subproduct is close to \<open>1\<close>.
  This strengthens \<open>has_setprod_factors_tend_to_1\<close> below, which is the special case of
  singleton subproducts.
\<close>
lemma has_setprod_prods_near_1:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra, comm_monoid_mult}"
  assumes lim: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top M)" and nz: "L \<noteq> 0" and \<epsilon>: "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>D. finite D \<longrightarrow> D \<subseteq> M - F \<longrightarrow> dist (prod f D) 1 < \<epsilon>)"
proof -
  have L0: "norm L > 0"
    using nz by simp
  define \<delta> where "\<delta> = min (\<epsilon> * norm L / 4) (norm L / 4)"
  have \<delta>0: "\<delta> > 0"
    unfolding \<delta>_def using \<epsilon> L0 by simp
  have \<delta>1: "\<delta> \<le> \<epsilon> * norm L / 4" and \<delta>2: "\<delta> \<le> norm L / 4"
    unfolding \<delta>_def by auto
  from tendstoD[OF lim \<delta>0] obtain F where F: "finite F" "F \<subseteq> M"
    and Fclose: "\<And>Y. finite Y \<Longrightarrow> F \<subseteq> Y \<Longrightarrow> Y \<subseteq> M \<Longrightarrow> dist (prod f Y) L < \<delta>"
    unfolding eventually_finite_subsets_at_top by metis
  have dF: "dist (prod f F) L < \<delta>"
    using Fclose F by blast
  have "norm L - norm (prod f F - L) \<le> norm (prod f F)"
    by (metis dist_commute dist_diff(1) dist_norm norm_triangle_ineq2)
  with dF \<delta>2 L0 have normF: "norm (prod f F) > norm L / 2"
    unfolding dist_norm by linarith
  have "dist (prod f D) 1 < \<epsilon>" if D: "finite D" "D \<subseteq> M - F" for D
  proof -
    have "dist (prod f (F \<union> D)) L < \<delta>"
      using Fclose[of "F \<union> D"] F D by auto
    with dF have "dist (prod f (F \<union> D)) (prod f F) < 2 * \<delta>"
      by (smt (verit) dist_commute dist_triangle)
    moreover have "prod f (F \<union> D) = prod f F * prod f D"
      using F(1) D by (subst prod.union_disjoint) auto
    ultimately have "dist (prod f F * prod f D) (prod f F * 1) < 2 * \<delta>"
      by simp
    hence "norm (prod f F) * dist (prod f D) 1 < 2 * \<delta>"
      by (metis dist_norm norm_mult right_diff_distrib)
    hence n_d: "dist (prod f D) 1 * norm (prod f F) < 2 * \<delta>"
      by (simp add: mult.commute)
    have nF0: "norm (prod f F) > 0"
      using normF L0 by linarith
    from n_d nF0 have "dist (prod f D) 1 < 2 * \<delta> / norm (prod f F)"
      by (simp add: pos_less_divide_eq)
    also have "\<dots> \<le> 2 * \<delta> / (norm L / 2)"
      using normF \<delta>0 L0 nF0 by (intro divide_left_mono mult_pos_pos) auto
    also have "\<dots> \<le> \<epsilon>"
      using \<delta>1 L0 by (simp add: field_simps)
    finally show ?thesis .
  qed
  with F show ?thesis
    by blast
qed

text \<open>
  For a non-vanishing multipliable family the partial products are uniformly bounded, whatever
  the value of the product.  (Non-vanishing is essential: if \<open>f\<close> has a zero in \<^term>\<open>M\<close> then
  \<open>f\<close> is multipliable on \<^term>\<open>M\<close> with product \<open>0\<close>, and the remaining partial products are
  unconstrained.)
\<close>
lemma multipliable_on_imp_bdd_prods:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes lim: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top M)"
    and nz: "\<And>x. x \<in> M \<Longrightarrow> f x \<noteq> 0"
  shows "\<exists>C>0. \<forall>X. finite X \<longrightarrow> X \<subseteq> M \<longrightarrow> norm (prod f X) \<le> C"
proof -
  from tendstoD[OF lim zero_less_one] obtain F where F: "finite F" "F \<subseteq> M"
    and Fclose: "\<And>Y. finite Y \<Longrightarrow> F \<subseteq> Y \<Longrightarrow> Y \<subseteq> M \<Longrightarrow> dist (prod f Y) L < 1"
    unfolding eventually_finite_subsets_at_top by metis
  define m where "m = (\<Prod>x\<in>F. min (norm (f x)) 1)"
  have m0: "m > 0"
    unfolding m_def using F nz by (intro prod_pos) auto
  have m_le: "m \<le> norm (prod f G)" if GF: "G \<subseteq> F" for G
  proof -
    have "m = (\<Prod>x\<in>F-G. min (norm (f x)) 1) * (\<Prod>x\<in>G. min (norm (f x)) 1)"
      unfolding m_def using GF F(1) by (intro prod.subset_diff)
    also have "\<dots> \<le> 1 * (\<Prod>x\<in>G. min (norm (f x)) 1)"
      by (intro mult_right_mono prod_le_1 prod_nonneg) auto
    also have "\<dots> = (\<Prod>x\<in>G. min (norm (f x)) 1)"
      by simp
    also have "\<dots> \<le> (\<Prod>x\<in>G. norm (f x))"
      by (intro prod_mono) auto
    also have "\<dots> = norm (prod f G)"
      by (simp add: prod_norm)
    finally show ?thesis .
  qed
  have bound: "norm (prod f X) \<le> (norm L + 1) / m" if X: "finite X" "X \<subseteq> M" for X
  proof -
    have "prod f (X \<union> F) = prod f (X \<union> (F - X))"
      by (simp add: Un_Diff_cancel2)
    also have "\<dots> = prod f X * prod f (F - X)"
      using X(1) F(1) by (intro prod.union_disjoint) auto
    finally have eq: "prod f (X \<union> F) = prod f X * prod f (F - X)" .
    have "dist (prod f (X \<union> F)) L < 1"
      using Fclose[of "X \<union> F"] X F by auto
    hence lt: "norm (prod f (X \<union> F)) < norm L + 1"
      using norm_triangle_sub[of "prod f (X \<union> F)" L] by (simp add: dist_norm)
    have "norm (prod f X) * m \<le> norm (prod f X) * norm (prod f (F - X))"
      by (intro mult_left_mono m_le) auto
    also have "\<dots> = norm (prod f (X \<union> F))"
      by (simp add: eq norm_mult)
    also have "\<dots> < norm L + 1"
      by (rule lt)
    finally have "norm (prod f X) * m \<le> norm L + 1"
      by simp
    with m0 show ?thesis
      by (simp add: mult_imp_le_div_pos)
  qed
  have "(norm L + 1) / m > 0"
    using m0 norm_ge_zero[of L] by (intro divide_pos_pos) linarith+
  with bound show ?thesis
    by blast
qed

text \<open>
  If only finitely many factors are dropped, no extra hypothesis beyond non-vanishing of those
  factors is needed: one simply divides them out.
\<close>
lemma multipliable_on_subset_finite_Diff:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes mult: "f multipliable_on A" and BA: "B \<subseteq> A" and fin: "finite (A - B)"
    and nz: "\<And>x. x \<in> A - B \<Longrightarrow> f x \<noteq> 0"
  shows "f multipliable_on B"
proof -
  from mult obtain S where S: "(f has_setprod S) A"
    using multipliable_on_def by blast
  have "(f has_setprod prod f (A - B)) (A - B)"
    using fin by (rule has_setprod_finite)
  moreover have "prod f (A - B) \<noteq> 0"
    using fin nz by auto
  ultimately have "(f has_setprod (S / prod f (A - B))) (A - (A - B))"
    using S by (intro has_setprod_Diff) auto
  moreover have "A - (A - B) = B"
    using BA by blast
  ultimately show ?thesis
    using has_setprod_imp_multipliable by metis
qed

text \<open>
  The subset principle, in the form that is actually true: a product with a \<^emph>\<open>non-zero\<close> value
  restricts to every subset, and the restricted product is again non-zero.
\<close>
lemma has_setprod_subset_nonzero:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_field, complete_space}"
  assumes lim: "(f has_setprod L) A" and nz: "L \<noteq> 0" and BA: "B \<subseteq> A"
  shows "\<exists>P. (f has_setprod P) B \<and> P \<noteq> 0"
proof -
  from lim have limA: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top A)"
    by (simp add: has_setprod_def)
  have fnz: "f x \<noteq> 0" if "x \<in> A" for x
    using that lim nz has_setprod_unique zero_imp_has_setprod_0[of x A f] by fastforce
  \<comment> \<open>A master seed: past \<^term>\<open>F1\<close> every subproduct is within \<open>1/2\<close> of \<open>1\<close>.\<close>
  have half: "(1/2::real) > 0"
    by simp
  obtain F1 where F1: "finite F1" "F1 \<subseteq> A"
    and F1_near: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A - F1 \<Longrightarrow> dist (prod f D) 1 < 1/2"
    using has_setprod_prods_near_1[OF limA nz half] by blast
  define c where "c = prod f (F1 \<inter> B)"
  have c0: "norm c > 0"
    unfolding c_def using F1 fnz BA by (simp add: prod_norm prod_pos subset_eq)
  \<comment> \<open>Past the master seed, a subset of \<^term>\<open>B\<close> meets \<^term>\<open>F1\<close> in exactly \<^term>\<open>F1 \<inter> B\<close>.\<close>
  have split: "prod f X = c * prod f (X - F1)" if X: "finite X" "F1 \<inter> B \<subseteq> X" "X \<subseteq> B" for X
    using c_def that by (metis inf.absorb_iff2 inf.orderE inf_assoc prod.Int_Diff)
  have tail: "norm (prod f (X - F1)) \<le> 3/2" and tail': "norm (prod f (X - F1)) \<ge> 1/2"
    if X: "finite X" "X \<subseteq> B" for X
  proof -
    have less: "norm (prod f (X - F1) - 1) < 1/2"
      using X BA by (intro F1_near[unfolded dist_norm]) auto
    have n1: "norm (1::'b) = 1"
      by simp
    show "norm (prod f (X - F1)) \<le> 3/2"
      using norm_triangle_ineq2[of "prod f (X - F1)" 1] less n1 by linarith
    show "norm (prod f (X - F1)) \<ge> 1/2"
      using norm_triangle_ineq2[of 1 "prod f (X - F1)"] less n1
            norm_minus_commute[of 1 "prod f (X - F1)"] by linarith
  qed
  have upper: "norm (prod f X) \<le> 3/2 * norm c" and lower: "norm (prod f X) \<ge> norm c / 2"
    if X: "finite X" "F1 \<inter> B \<subseteq> X" "X \<subseteq> B" for X
  proof -
    have "norm (prod f X) = norm c * norm (prod f (X - F1))"
      using split[OF X] by (simp add: norm_mult)
    thus "norm (prod f X) \<le> 3/2 * norm c" and "norm (prod f X) \<ge> norm c / 2"
      using tail[OF X(1) X(3)] tail'[OF X(1) X(3)] c0 by (simp_all add: mult_left_mono)
  qed
  \<comment> \<open>The partial products over \<^term>\<open>B\<close> form a Cauchy net.\<close>
  have "cauchy_filter (filtermap (prod f) (finite_subsets_at_top B))"
    unfolding cauchy_filter_metric_filtermap
  proof (intro allI impI)
    fix e :: real assume "e > 0"
    define \<epsilon> where "\<epsilon> = e / (4 * norm c)"
    have \<epsilon>0: "\<epsilon> > 0"
      unfolding \<epsilon>_def using \<open>e > 0\<close> c0 by simp
    obtain F2 where F2: "finite F2" "F2 \<subseteq> A"
      and F2_near: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A - F2 \<Longrightarrow> dist (prod f D) 1 < \<epsilon>"
      using has_setprod_prods_near_1[OF limA nz \<epsilon>0] by blast
    define F where "F = F1 \<union> F2"
    have Ffin: "finite F" and FA: "F \<subseteq> A"
      unfolding F_def using F1 F2 by auto
    define P where "P = (\<lambda>X. finite X \<and> F \<inter> B \<subseteq> X \<and> X \<subseteq> B)"
    have ev: "eventually P (finite_subsets_at_top B)"
      unfolding eventually_finite_subsets_at_top P_def
      using Ffin by (intro exI[of _ "F \<inter> B"]) auto
    have "dist (prod f X) (prod f Y) < e" if "P X" "P Y" for X Y
    proof -
      from that have X: "finite X" "F \<inter> B \<subseteq> X" "X \<subseteq> B"
                 and Y: "finite Y" "F \<inter> B \<subseteq> Y" "Y \<subseteq> B"
        unfolding P_def by auto
      have XY: "finite (X \<inter> Y)" "F1 \<inter> B \<subseteq> X \<inter> Y" "X \<inter> Y \<subseteq> B"
        using X Y unfolding F_def by auto
      have diff: "X - Y \<subseteq> A - F2" "Y - X \<subseteq> A - F2"
        using X Y BA unfolding F_def by auto
      have "prod f X - prod f Y = prod f (X \<inter> Y) * (prod f (X - Y) - prod f (Y - X))"
        using X(1) Y(1)
        by (metis Int_commute prod.Int_Diff right_diff_distrib)
      hence "norm (prod f X - prod f Y)
               = norm (prod f (X \<inter> Y)) * norm (prod f (X - Y) - prod f (Y - X))"
        by (simp add: norm_mult)
      also have "\<dots> \<le> (3/2 * norm c) * (2 * \<epsilon>)"
      proof (intro mult_mono)
        show "norm (prod f (X \<inter> Y)) \<le> 3/2 * norm c"
          by (rule upper[OF XY])
        have "dist (prod f (X - Y)) 1 < \<epsilon>" "dist (prod f (Y - X)) 1 < \<epsilon>"
          using X Y diff by (auto intro!: F2_near)
        thus "norm (prod f (X - Y) - prod f (Y - X)) \<le> 2 * \<epsilon>"
          using norm_triangle_ineq4[of "prod f (X - Y) - 1" "prod f (Y - X) - 1"]
          by (simp add: dist_norm)
      qed (use \<epsilon>0 c0 in auto)
      also have "\<dots> < e"
        unfolding \<epsilon>_def using c0 \<open>e > 0\<close> by (simp add: field_simps)
      finally show ?thesis
        by (simp add: dist_norm)
    qed
    with ev show "\<exists>P. eventually P (finite_subsets_at_top B)
                      \<and> (\<forall>X Y. P X \<and> P Y \<longrightarrow> dist (prod f X) (prod f Y) < e)"
      by blast
  qed
  from cauchy_filter_complete_converges[OF this complete_UNIV]
  obtain P where "filtermap (prod f) (finite_subsets_at_top B) \<le> nhds P"
    by (auto simp: filtermap_bot_iff)
  hence limB: "(prod f \<longlongrightarrow> P) (finite_subsets_at_top B)"
    by (simp add: filterlim_def)
  \<comment> \<open>The restricted product is bounded away from \<open>0\<close>, hence non-zero.\<close>
  have "norm c / 2 \<le> norm P"
  proof (rule tendsto_lowerbound[OF tendsto_norm[OF limB]])
    show "\<forall>\<^sub>F X in finite_subsets_at_top B. norm c / 2 \<le> norm (prod f X)"
      unfolding eventually_finite_subsets_at_top
      using F1 lower by (intro exI[of _ "F1 \<inter> B"]) auto
  qed auto
  with c0 have "P \<noteq> 0"
    by auto
  with limB show ?thesis
    by (auto simp: has_setprod_def)
qed

corollary multipliable_on_subset_nonzero:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_field, complete_space}"
  assumes "(f has_setprod L) A" and "L \<noteq> 0" and "B \<subseteq> A"
  shows "f multipliable_on B"
  using has_setprod_subset_nonzero[OF assms] has_setprod_imp_multipliable by blast

text \<open>
  A non-zero product splits along any decomposition of the index set.  Note that this needs the
  subset principle: without it one does not know that either part is multipliable at all.
\<close>
lemma infprod_split:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_field, complete_space}"
  assumes mult: "f multipliable_on A" and nz: "infprod f A \<noteq> 0" and BA: "B \<subseteq> A"
  shows "infprod f A = infprod f B * infprod f (A - B)"
proof -
  have P: "(f has_setprod infprod f A) A"
    using mult by (rule has_setprod_infprod)
  obtain Q where Q: "(f has_setprod Q) B" "Q \<noteq> 0"
    using has_setprod_subset_nonzero[OF P nz BA] by blast
  obtain R where R: "(f has_setprod R) (A - B)" "R \<noteq> 0"
    using has_setprod_subset_nonzero[OF P nz Diff_subset] by blast
  have "(f has_setprod Q * R) (B \<union> (A - B))"
    using Q(1) R(1) by (intro has_setprod_Un_disjoint) auto
  moreover have "B \<union> (A - B) = A"
    using BA by auto
  ultimately have "(f has_setprod Q * R) A"
    by simp
  with P have "infprod f A = Q * R"
    using has_setprod_unique by blast
  moreover have "infprod f B = Q"
    using Q(1) by (rule infprodI)
  moreover have "infprod f (A - B) = R"
    using R(1) by (rule infprodI)
  ultimately show ?thesis
    by simp
qed

text \<open>
  In the language of strong multipliability the subset principle takes its cleanest form:
  it is simply inherited by subsets.
\<close>
lemma strongly_multipliable_on_subset:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_field, complete_space}"
  assumes A: "f strongly_multipliable_on A" and BA: "B \<subseteq> A"
  shows "f strongly_multipliable_on B"
proof -
  from A obtain P where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}" "P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  have "{x\<in>B. f x \<noteq> 0} \<subseteq> {x\<in>A. f x \<noteq> 0}"
    using BA by blast
  from has_setprod_subset_nonzero[OF P(2) P(3) this]
  obtain Q where Q: "(f has_setprod Q) {x\<in>B. f x \<noteq> 0}" "Q \<noteq> 0"
    by blast
  have "finite {x\<in>B. f x = 0}"
    by (rule finite_subset[OF _ P(1)]) (use BA in auto)
  with Q show ?thesis
    unfolding strongly_multipliable_on_def by blast
qed

lemma has_setprod_empty[simp]: \<open>(f has_setprod 1) {}\<close>
  by (meson ex_in_conv has_setprod_1)

lemma multipliable_on_empty[simp]: \<open>f multipliable_on {}\<close>
  by auto

lemma infprod_empty[simp]: \<open>infprod f {} = 1\<close>
  by simp

lemma prod_has_setprod:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes \<open>finite A\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> (f has_setprod (s a)) (B a)\<close>
  assumes \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>(f has_setprod (prod s A)) (\<Union>a\<in>A. B a)\<close>
  using assms 
proof (induction)
  case empty
  then show ?case 
    by simp
next
  case (insert x A)
  have \<open>(f has_setprod (s x)) (B x)\<close>
    by (simp add: insert.prems)
  moreover have IH: \<open>(f has_setprod (prod s A)) (\<Union>a\<in>A. B a)\<close>
    using insert by simp
  ultimately have \<open>(f has_setprod (s x * prod s A)) (B x \<union> (\<Union>a\<in>A. B a))\<close>
    using insert by (intro has_setprod_Un_disjoint) auto
  then show ?case
    using insert.hyps by auto
qed


lemma multipliable_on_finite_union_disjoint:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f multipliable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>f multipliable_on (\<Union>a\<in>A. B a)\<close>
  using prod_has_setprod [of A f B] assms unfolding multipliable_on_def by metis

lemma prod_infprod:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f multipliable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>prod (\<lambda>a. infprod f (B a)) A = infprod f (\<Union>a\<in>A. B a)\<close>
  by (metis (no_types, lifting) assms has_setprod_infprod infprodI prod_has_setprod)

lemma has_setprod_comm_multiplicative_general: 
  fixes f :: \<open>'b::{banach, field, topological_semigroup_mult} \<Rightarrow> 'c::{banach, field, topological_semigroup_mult}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
  assumes cont: \<open>f \<midarrow>x\<rightarrow> f x\<close>
  assumes infprod: \<open>(g has_setprod x) S\<close>
  shows \<open>((f \<circ> g) has_setprod (f x)) S\<close> 
proof -
  from infprod have lim_g: \<open>(prod g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    by (simp add: has_setprod_def)
  \<comment> \<open>Compose f with the limit\<close>
  have \<open>((f \<circ> prod g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
  proof (rule topological_tendstoI)
    fix U assume \<open>open U\<close> \<open>f x \<in> U\<close>
    with cont[unfolded continuous_at_open]
    obtain V where \<open>open V\<close> \<open>x \<in> V\<close> and V_sub: \<open>\<And>y. y \<in> V \<Longrightarrow> f y \<in> U\<close>
      by (metis continuous_at_open isCont_def)
    from lim_g[THEN topological_tendstoD, OF \<open>open V\<close> \<open>x \<in> V\<close>]
    show \<open>\<forall>\<^sub>F F in finite_subsets_at_top S. (f \<circ> prod g) F \<in> U\<close>
      by (eventually_elim) (auto intro: V_sub)
  qed
  moreover have \<open>\<forall>\<^sub>F F in finite_subsets_at_top S. prod (f \<circ> g) F = (f \<circ> prod g) F\<close>
    by (rule eventually_finite_subsets_at_top_weakI) (use f_sum in auto)
  ultimately have \<open>(prod (f \<circ> g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    using tendsto_cong by blast
  then show ?thesis
    by (simp add: has_setprod_def)
qed

lemma multipliable_on_comm_multiplicative_general:
  fixes f :: \<open>'b :: {banach, field, topological_semigroup_mult} \<Rightarrow> 'c :: {banach, field, topological_semigroup_mult}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>\<And>x. (g has_setprod x) S \<Longrightarrow> f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g multipliable_on S\<close>
  shows \<open>(f \<circ> g) multipliable_on S\<close>
  by (meson assms multipliable_on_def has_setprod_comm_multiplicative_general has_setprod_def infprod_tendsto)

lemma infprod_comm_additive_general:
  fixes f :: \<open>'b :: {banach, field, topological_semigroup_mult} \<Rightarrow> 'c :: {banach, field, topological_semigroup_mult}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>isCont f (infprod g S)\<close>
  assumes \<open>g multipliable_on S\<close>
  shows \<open>infprod (f \<circ> g) S = f (infprod g S)\<close>
  using assms
  by (intro infprodI has_setprod_comm_multiplicative_general has_setprod_infprod) (auto simp: isCont_def)

lemma has_setprod_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>(g has_setprod P) (h ` A) \<longleftrightarrow> ((g \<circ> h) has_setprod P) A\<close>
proof -
  have \<open>(g has_setprod P) (h ` A) \<longleftrightarrow> (prod g \<longlongrightarrow> P) (finite_subsets_at_top (h ` A))\<close>
    by (simp add: has_setprod_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>F. prod g (h ` F)) \<longlongrightarrow> P) (finite_subsets_at_top A)\<close>
    by (metis assms filterlim_filtermap filtermap_image_finite_subsets_at_top)
  also have \<open>\<dots> \<longleftrightarrow> (prod (g \<circ> h) \<longlongrightarrow> P) (finite_subsets_at_top A)\<close>
  proof (intro tendsto_cong eventually_finite_subsets_at_top_weakI prod.reindex)
    show "\<And>X. \<lbrakk>finite X; X \<subseteq> A\<rbrakk> \<Longrightarrow> inj_on h X"
      using assms inj_on_subset by blast
  qed
  also have \<open>\<dots> \<longleftrightarrow> ((g \<circ> h) has_setprod P) A\<close>
    by (simp add: has_setprod_def)
  finally show ?thesis .
qed

lemma multipliable_on_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>g multipliable_on (h ` A) \<longleftrightarrow> (g \<circ> h) multipliable_on A\<close>
  by (simp add: assms multipliable_on_def has_setprod_reindex)

lemma infprod_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>infprod g (h ` A) = infprod (g \<circ> h) A\<close>
  by (metis assms has_setprod_infprod has_setprod_reindex infprodI infprod_def)

lemma multipliable_on_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "(\<lambda>x. f (g x)) multipliable_on A \<longleftrightarrow> f multipliable_on B"
  by (smt (verit) assms bij_betw_def o_apply multipliable_on_cong multipliable_on_reindex) 

lemma infprod_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infprod (\<lambda>x. f (g x)) A = infprod f B"
  by (metis (mono_tags, lifting) assms bij_betw_def infprod_cong infprod_reindex o_def)

lemma prod_uniformity:
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'b::{uniform_space,comm_monoid_mult},y). x*y)\<close>
  assumes EE: \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually D uniformity\<close> 
    and \<open>\<And>M::'a set. \<And>f f' :: 'a \<Rightarrow> 'b. card M \<le> n \<and> (\<forall>m\<in>M. D (f m, f' m)) \<Longrightarrow> E (prod f M, prod f' M)\<close>
proof (atomize_elim, insert EE, induction n arbitrary: E rule:nat_induct)
  case 0
  then show ?case
    by (metis card_eq_0_iff equals0D le_zero_eq prod.infinite prod.not_neutral_contains_not_neutral uniformity_refl)
next
  case (Suc n)
  from times_cont[unfolded uniformly_continuous_on_uniformity filterlim_def le_filter_def, rule_format, OF Suc.prems]
  obtain D1 D2 where \<open>eventually D1 uniformity\<close> and \<open>eventually D2 uniformity\<close> 
    and D1D2E: \<open>D1 (x, y) \<Longrightarrow> D2 (x', y') \<Longrightarrow> E (x * x', y * y')\<close> for x y x' y'
    apply atomize_elim
    by (auto simp: eventually_prod_filter case_prod_beta uniformity_prod_def eventually_filtermap)

  from Suc.IH[OF \<open>eventually D2 uniformity\<close>]
  obtain D3 where \<open>eventually D3 uniformity\<close> and D3: \<open>card M \<le> n \<Longrightarrow> (\<forall>m\<in>M. D3 (f m, f' m)) \<Longrightarrow> D2 (prod f M, prod f' M)\<close> 
    for M :: \<open>'a set\<close> and f f'
    by metis

  define D where \<open>D x \<equiv> D1 x \<and> D3 x\<close> for x
  have \<open>eventually D uniformity\<close>
    using D_def \<open>eventually D1 uniformity\<close> \<open>eventually D3 uniformity\<close> eventually_elim2 by blast

  have \<open>E (prod f M, prod f' M)\<close> 
    if \<open>card M \<le> Suc n\<close> and DM: \<open>\<forall>m\<in>M. D (f m, f' m)\<close>
    for M :: \<open>'a set\<close> and f f'
  proof (cases \<open>card M = 0\<close>)
    case True
    then show ?thesis
      by (metis Suc.prems card_eq_0_iff prod.empty prod.infinite uniformity_refl) 
  next
    case False
    with \<open>card M \<le> Suc n\<close> obtain N x where \<open>card N \<le> n\<close> and \<open>x \<notin> N\<close> and \<open>M = insert x N\<close>
      by (metis card_Suc_eq less_Suc_eq_0_disj less_Suc_eq_le)

    from DM have \<open>\<And>m. m\<in>N \<Longrightarrow> D (f m, f' m)\<close>
      using \<open>M = insert x N\<close> by blast
    with D3[OF \<open>card N \<le> n\<close>]
    have D2_N: \<open>D2 (prod f N, prod f' N)\<close>
      using D_def by blast

    from DM 
    have \<open>D (f x, f' x)\<close>
      using \<open>M = insert x N\<close> by blast
    then have \<open>D1 (f x, f' x)\<close>
      by (simp add: D_def)

    with D2_N
    have \<open>E (f x * prod f N, f' x * prod f' N)\<close>
      using D1D2E by presburger

    then show \<open>E (prod f M, prod f' M)\<close>
      by (metis False \<open>M = insert x N\<close> \<open>x \<notin> N\<close> card.infinite finite_insert prod.insert)
  qed
  with \<open>eventually D uniformity\<close> show ?case 
    by auto
qed


text \<open>Metric "splitting lemma" for products, the multiplicative replacement for the uniformity
  machinery of @{thm [source] prod_uniformity}: a finite product is Lipschitz in its factors,
  PROVIDED the factors stay bounded. (Multiplication is uniformly continuous on bounded sets,
  which is enough here -- the factors that occur are partial products near the nonzero limits.)\<close>

lemma norm_prod_diff_le:
  fixes g g' :: "'i \<Rightarrow> 'b :: real_normed_field"
  assumes "finite M"
    and "\<And>m. m \<in> M \<Longrightarrow> norm (g m) \<le> C" and "\<And>m. m \<in> M \<Longrightarrow> norm (g' m) \<le> C"
    and "\<And>m. m \<in> M \<Longrightarrow> norm (g m - g' m) \<le> d" and "C \<ge> 1" and "d \<ge> 0"
  shows "norm (prod g M - prod g' M) \<le> real (card M) * C ^ (card M) * d"
  using assms
proof (induction M rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x M)
  have gx: "norm (g x) \<le> C" and gM: "\<And>m. m \<in> M \<Longrightarrow> norm (g m) \<le> C" using insert.prems(1) by auto
  have g'x: "norm (g' x) \<le> C" and g'M: "\<And>m. m \<in> M \<Longrightarrow> norm (g' m) \<le> C" using insert.prems(2) by auto
  have dx: "norm (g x - g' x) \<le> d" and dM: "\<And>m. m \<in> M \<Longrightarrow> norm (g m - g' m) \<le> d" using insert.prems(3) by auto
  have C0: "C \<ge> 1" and d0: "d \<ge> 0" using insert.prems(4,5) by auto
  have Cnn: "C \<ge> 0" using C0 by simp
  have IH: "norm (prod g M - prod g' M) \<le> real (card M) * C ^ (card M) * d"
    using insert.IH[OF gM g'M dM C0 d0] .
  define P P' where "P = prod g M" and "P' = prod g' M"
  have normP': "norm P' \<le> C ^ (card M)"
  proof -
    have "norm P' = (\<Prod>m\<in>M. norm (g' m))" unfolding P'_def by (simp add: prod_norm)
    also have "\<dots> \<le> (\<Prod>m\<in>M. C)" by (intro prod_mono conjI g'M) auto
    also have "\<dots> = C ^ (card M)" by (simp add: prod_constant)
    finally show ?thesis .
  qed
  have pownn: "C ^ (card M) \<ge> 0" using Cnn by simp
  have prod_eq: "prod g (insert x M) - prod g' (insert x M) = g x * P - g' x * P'"
    using insert.hyps by (simp add: P_def P'_def)
  have split: "g x * P - g' x * P' = g x * (P - P') + (g x - g' x) * P'"
    by (simp add: algebra_simps)
  have B: "norm (g x * P - g' x * P') \<le> norm (g x) * norm (P - P') + norm (g x - g' x) * norm P'"
    unfolding split by (smt (verit) norm_triangle_ineq norm_mult)
  have step1: "norm (g x) * norm (P - P') \<le> C * (real (card M) * C ^ (card M) * d)"
    using IH gx P_def P'_def Cnn by (intro mult_mono) auto
  have step2: "norm (g x - g' x) * norm P' \<le> d * C ^ (card M)"
    using dx normP' d0 pownn by (intro mult_mono) auto
  have "norm (prod g (insert x M) - prod g' (insert x M)) = norm (g x * P - g' x * P')"
    by (simp add: prod_eq)
  also have "\<dots> \<le> C * (real (card M) * C ^ (card M) * d) + d * C ^ (card M)"
    using B step1 step2 by linarith
  also have "\<dots> = real (card M) * (C ^ (Suc (card M))) * d + C ^ (card M) * d"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> real (card M) * (C ^ (Suc (card M))) * d + C ^ (Suc (card M)) * d"
    using C0 pownn d0 by (simp add: mult_right_mono mult_left_mono)
  also have "\<dots> = real (card (insert x M)) * C ^ (card (insert x M)) * d"
    using insert.hyps by (simp add: algebra_simps)
  finally show ?case .
qed

lemma prod_close_of_factors_close:
  fixes M :: "'i set" and C \<epsilon> :: real
  assumes "finite M" and "C \<ge> 1" and "\<epsilon> > 0"
  shows "\<exists>\<delta>>0. \<forall>h h' :: 'i \<Rightarrow> 'b :: real_normed_field.
           (\<forall>m\<in>M. norm (h m) \<le> C \<and> norm (h' m) \<le> C \<and> dist (h m) (h' m) < \<delta>)
           \<longrightarrow> dist (prod h M) (prod h' M) < \<epsilon>"
proof -
  define K where "K = real (card M) * C ^ (card M) + 1"
  have K0: "K > 0" using assms by (simp add: K_def add_nonneg_pos)
  define \<delta> where "\<delta> = \<epsilon> / K"
  have \<delta>0: "\<delta> > 0" using assms K0 by (simp add: \<delta>_def)
  have "dist (prod h M) (prod h' M) < \<epsilon>"
    if H: "\<forall>m\<in>M. norm (h m) \<le> C \<and> norm (h' m) \<le> C \<and> dist (h m) (h' m) < \<delta>"
    for h h' :: "'i \<Rightarrow> 'b"
  proof -
    have nH: "\<And>m. m \<in> M \<Longrightarrow> norm (h m) \<le> C" using H by blast
    have nH': "\<And>m. m \<in> M \<Longrightarrow> norm (h' m) \<le> C" using H by blast
    have dH: "\<And>m. m \<in> M \<Longrightarrow> norm (h m - h' m) \<le> \<delta>" using H by (simp add: dist_norm less_imp_le)
    have "norm (prod h M - prod h' M) \<le> real (card M) * C ^ (card M) * \<delta>"
      using norm_prod_diff_le[OF assms(1) nH nH' dH assms(2)] \<delta>0 by simp
    also have "\<dots> < \<epsilon>"
      using \<delta>0 K0 assms unfolding \<delta>_def K_def by (simp add: field_simps)
    finally show ?thesis by (simp add: dist_norm)
  qed
  thus ?thesis using \<delta>0 by blast
qed

lemma has_setprod_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "(f has_setprod a) (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod b x) (B x)\<close>
  shows "(b has_setprod a) A"
proof -
  define F FB FA where \<open>F = finite_subsets_at_top (Sigma A B)\<close> and \<open>FB x = finite_subsets_at_top (B x)\<close>
    and \<open>FA = finite_subsets_at_top A\<close> for x

  from multipliableB
  have sum_b: \<open>(prod (\<lambda>y. f (x, y)) \<longlongrightarrow> b x) (FB x)\<close> if \<open>x \<in> A\<close> for x
    using FB_def[abs_def] has_setprod_def that by auto
  from multipliableAB
  have sum_S: \<open>(prod f \<longlongrightarrow> a) F\<close>
    using F_def has_setprod_def by blast

  have finite_proj: \<open>finite {b| b. (a,b) \<in> H}\<close> if \<open>finite H\<close> for H :: \<open>('a\<times>'b) set\<close> and a
    by (metis (no_types, lifting) finite_imageI finite_subset image_eqI mem_Collect_eq snd_conv subsetI that)

  have \<open>(prod b \<longlongrightarrow> a) FA\<close>
  proof (rule tendsto_iff_uniformity[THEN iffD2, rule_format])
    fix E :: \<open>('c \<times> 'c) \<Rightarrow> bool\<close>
    assume \<open>eventually E uniformity\<close>
    then obtain D where D_uni: \<open>eventually D uniformity\<close> and DDE': \<open>\<And>x y z. D (x, y) \<Longrightarrow> D (y, z) \<Longrightarrow> E (x, z)\<close>
      by (metis (no_types, lifting) \<open>eventually E uniformity\<close> uniformity_transE)
    from sum_S obtain G where \<open>finite G\<close> and \<open>G \<subseteq> Sigma A B\<close>
      and G_sum: \<open>G \<subseteq> H \<Longrightarrow> H \<subseteq> Sigma A B \<Longrightarrow> finite H \<Longrightarrow> D (prod f H, a)\<close> for H
      unfolding tendsto_iff_uniformity
      by (metis (mono_tags, lifting) D_uni F_def eventually_finite_subsets_at_top)
    have \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> by auto
    thm uniformity_prod_def
    define Ga where \<open>Ga a = {b. (a,b) \<in> G}\<close> for a
    have Ga_fin: \<open>finite (Ga a)\<close> and Ga_B: \<open>Ga a \<subseteq> B a\<close> for a
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> finite_proj by (auto simp: Ga_def finite_proj)

    have \<open>E (prod b M, a)\<close> if \<open>M \<supseteq> fst ` G\<close> and \<open>finite M\<close> and \<open>M \<subseteq> A\<close> for M
    proof -
      define FMB where \<open>FMB = finite_subsets_at_top (Sigma M B)\<close>
      have \<open>eventually (\<lambda>H. D (\<Prod>a\<in>M. b a, \<Prod>(a,b)\<in>H. f (a,b))) FMB\<close>
      proof -
        \<comment> \<open>Metric replacement for the (false in general) prod-uniformity step.\<close>
        from D_uni obtain eD where eD0: \<open>eD > 0\<close>
          and eD_D: \<open>\<And>x y::'c. dist x y < eD \<Longrightarrow> D (x, y)\<close>
          by (auto simp: eventually_uniformity_metric)
        define C where \<open>C = Max (insert 1 ((\<lambda>a. norm (b a) + 1) ` M))\<close>
        have C1: \<open>C \<ge> 1\<close> using \<open>finite M\<close> by (simp add: C_def)
        have bC: \<open>norm (b a) + 1 \<le> C\<close> if \<open>a \<in> M\<close> for a
          using that \<open>finite M\<close> by (simp add: C_def)
        obtain \<delta>0 where \<delta>00: \<open>\<delta>0 > 0\<close>
          and \<delta>0_prod: \<open>\<And>h h'::'a\<Rightarrow>'c. (\<forall>m\<in>M. norm (h m) \<le> C \<and> norm (h' m) \<le> C \<and> dist (h m) (h' m) < \<delta>0)
                          \<Longrightarrow> dist (prod h M) (prod h' M) < eD\<close>
          using prod_close_of_factors_close[OF \<open>finite M\<close> C1 eD0] by blast
        define \<delta> where \<open>\<delta> = min \<delta>0 1\<close>
        have \<delta>0: \<open>\<delta> > 0\<close> using \<delta>00 by (simp add: \<delta>_def)
        define D' where \<open>D' = (\<lambda>(x::'c,y::'c). dist x y < \<delta>)\<close>
        have D'_uni: \<open>eventually D' uniformity\<close>
          unfolding D'_def using \<delta>0 by (auto simp: eventually_uniformity_metric)

        obtain Ha where \<open>Ha a \<supseteq> Ga a\<close> and Ha_fin: \<open>finite (Ha a)\<close> and Ha_B: \<open>Ha a \<subseteq> B a\<close>
          and D'_sum_Ha: \<open>Ha a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (b a, prod (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
        proof -
          from sum_b[unfolded tendsto_iff_uniformity, rule_format, OF _ D'_uni[THEN uniformity_sym]]
          obtain Ha0 where \<open>finite (Ha0 a)\<close> and \<open>Ha0 a \<subseteq> B a\<close>
            and \<open>Ha0 a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (b a, prod (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
            unfolding FB_def eventually_finite_subsets_at_top unfolding prod.case by metis
          moreover define Ha where \<open>Ha a = Ha0 a \<union> Ga a\<close> for a
          ultimately show ?thesis
            using that[where Ha=Ha]
            using Ga_fin Ga_B by auto
        qed

        have \<open>D (\<Prod>a\<in>M. b a, \<Prod>(a,b)\<in>H. f (a,b))\<close> if \<open>finite H\<close> and \<open>H \<subseteq> Sigma M B\<close> and \<open>H \<supseteq> Sigma M Ha\<close> for H
        proof -
          define Ha' where \<open>Ha' a = {b| b. (a,b) \<in> H}\<close> for a
          have [simp]: \<open>finite (Ha' a)\<close> and [simp]: \<open>Ha' a \<supseteq> Ha a\<close> and [simp]: \<open>Ha' a \<subseteq> B a\<close> if \<open>a \<in> M\<close> for a
            unfolding Ha'_def using \<open>finite H\<close> \<open>H \<subseteq> Sigma M B\<close> \<open>Sigma M Ha \<subseteq> H\<close> that finite_proj by auto
          have \<open>Sigma M Ha' = H\<close>
            using that by (auto simp: Ha'_def)
          then have *: \<open>(\<Prod>(a,b)\<in>H. f (a,b)) = (\<Prod>a\<in>M. \<Prod>b\<in>Ha' a. f (a,b))\<close>
            by (simp add: \<open>finite M\<close> prod.Sigma)
          have D'close: \<open>D' (b a, prod (\<lambda>b. f (a,b)) (Ha' a))\<close> if \<open>a \<in> M\<close> for a
            using D'_sum_Ha \<open>M \<subseteq> A\<close> that by auto
          \<comment> \<open>Both factors are \<open>\<delta>\<close>-close and \<open>C\<close>-bounded, so the products are \<open>eD\<close>-close, hence \<open>D\<close>-related.\<close>
          have bnd: \<open>norm (b a) \<le> C \<and> norm (prod (\<lambda>b. f (a,b)) (Ha' a)) \<le> C
                     \<and> dist (b a) (prod (\<lambda>b. f (a,b)) (Ha' a)) < \<delta>0\<close> if \<open>a \<in> M\<close> for a
          proof -
            have d1: \<open>dist (b a) (prod (\<lambda>b. f (a,b)) (Ha' a)) < \<delta>\<close>
              using D'close[OF that] by (simp add: D'_def)
            have nb: \<open>norm (b a) \<le> C\<close> using bC[OF that] by simp
            have \<open>norm (prod (\<lambda>b. f (a,b)) (Ha' a)) \<le> norm (b a) + dist (b a) (prod (\<lambda>b. f (a,b)) (Ha' a))\<close>
            proof -
              have \<open>norm (prod (\<lambda>b. f (a,b)) (Ha' a))
                      = norm (b a + (prod (\<lambda>b. f (a,b)) (Ha' a) - b a))\<close> by simp
              also have \<open>\<dots> \<le> norm (b a) + norm (prod (\<lambda>b. f (a,b)) (Ha' a) - b a)\<close>
                by (rule norm_triangle_ineq)
              also have \<open>norm (prod (\<lambda>b. f (a,b)) (Ha' a) - b a) = dist (b a) (prod (\<lambda>b. f (a,b)) (Ha' a))\<close>
                by (simp add: dist_norm norm_minus_commute)
              finally show ?thesis by simp
            qed
            also have \<open>\<dots> \<le> norm (b a) + 1\<close> using d1 by (simp add: \<delta>_def)
            also have \<open>\<dots> \<le> C\<close> using bC[OF that] by simp
            finally show ?thesis using nb d1 by (simp add: \<delta>_def)
          qed
          have \<open>dist (\<Prod>a\<in>M. b a) (\<Prod>a\<in>M. prod (\<lambda>b. f (a,b)) (Ha' a)) < eD\<close>
            by (rule \<delta>0_prod) (use bnd in blast)
          then have \<open>D (\<Prod>a\<in>M. b a, \<Prod>a\<in>M. prod (\<lambda>b. f (a,b)) (Ha' a))\<close>
            by (rule eD_D)
          with * show ?thesis
            by auto
        qed
        moreover have \<open>Sigma M Ha \<subseteq> Sigma M B\<close>
          using Ha_B \<open>M \<subseteq> A\<close> by auto
        ultimately show ?thesis
          unfolding FMB_def eventually_finite_subsets_at_top
          by (metis (no_types, lifting) Ha_fin finite_SigmaI subsetD that(2) that(3))
      qed
      moreover have \<open>eventually (\<lambda>H. D (\<Prod>(a,b)\<in>H. f (a,b), a)) FMB\<close>
        unfolding FMB_def eventually_finite_subsets_at_top
      proof (rule exI[of _ G], safe)
        fix Y assume Y: "finite Y" "G \<subseteq> Y" "Y \<subseteq> Sigma M B"
        thus "D (\<Prod>(a,b)\<in>Y. f (a, b), a)"
          using G_sum[of Y] Y using that(3) by fastforce
      qed (use \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> that in auto)
      ultimately have \<open>\<forall>\<^sub>F x in FMB. E (prod b M, a)\<close>
        by eventually_elim (use DDE' in auto)
      then show \<open>E (prod b M, a)\<close>
        using FMB_def by force
    qed
    then show \<open>\<forall>\<^sub>F x in FA. E (prod b x, a)\<close>
      using \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      by (metis (mono_tags, lifting) FA_def eventually_finite_subsets_at_top)
  qed
  then show ?thesis
    by (simp add: FA_def has_setprod_def)
qed

lemma has_setprod_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: real_normed_field"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
  assumes g: "(g has_setprod S) A"
  assumes multipliable: "f multipliable_on Sigma A B"
  shows   "(f has_setprod S) (Sigma A B)"
  by (metis f g has_setprod_Sigma has_setprod_infprod has_setprod_unique local.multipliable)

lemma multipliable_on_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close>
proof -
  from multipliableAB obtain a where a: \<open>((\<lambda>(x,y). f x y) has_setprod a) (Sigma A B)\<close>
    using has_setprod_infprod by blast
  from multipliableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x has_setprod infprod (f x) (B x)) (B x)\<close>
    by (auto intro!: has_setprod_infprod)
  show ?thesis
    using a b
    by (smt (verit) has_setprod_Sigma[where f=\<open>\<lambda>(x,y). f x y\<close>] has_setprod_cong old.prod.case multipliable_on_def) 
qed

lemma infprod_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "f multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) multipliable_on (B x)\<close>
  shows "infprod f (Sigma A B) = infprod (\<lambda>x. infprod (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from multipliableAB have a: \<open>(f has_setprod infprod f (Sigma A B)) (Sigma A B)\<close>
    using has_setprod_infprod by blast
  from multipliableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod infprod (\<lambda>y. f (x, y)) (B x)) (B x)\<close>
    by (auto intro!: has_setprod_infprod)
  show ?thesis
    using a b by (auto intro: infprodI[symmetric] has_setprod_Sigma simp: multipliable_on_def)
qed

lemma infprod_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>infprod (\<lambda>x. infprod (f x) (B x)) A = infprod (\<lambda>(x,y). f x y) (Sigma A B)\<close>
  using infprod_Sigma[of \<open>\<lambda>(x,y). f x y\<close> A B]
  using assms by auto

text \<open>
  These are the variants that do \<^emph>\<open>not\<close> assume multipliability of each fibre but derive it.
  This needs more than multipliability of the whole family: it needs the
  product to be non-zero (see \<open>has_setprod_subset_nonzero\<close> and the counterexample discussed
  there).  Note that a non-zero product also implies that no factor vanishes, so this replaces
  -- rather than adds to -- the former pointwise non-vanishing hypothesis.
\<close>
lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{banach,real_normed_field}\<close>
  assumes [simp]: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes nz: \<open>infprod (\<lambda>(x,y). f x y) (Sigma A B) \<noteq> 0\<close>
  shows infprod_Sigma'_banach: \<open>infprod (\<lambda>x. infprod (f x) (B x)) A = infprod (\<lambda>(x,y). f x y) (Sigma A B)\<close> (is ?thesis1)
    and multipliable_on_Sigma_banach: \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close> (is ?thesis2)
proof -
  have mult_B: \<open>(f x) multipliable_on (B x)\<close> if xA: \<open>x \<in> A\<close> for x
  proof -
    have step1: \<open>(\<lambda>(x,y). f x y) multipliable_on Sigma {x} B\<close>
    proof (rule multipliable_on_subset_nonzero[OF _ nz])
      show \<open>((\<lambda>(x,y). f x y) has_setprod infprod (\<lambda>(x,y). f x y) (Sigma A B)) (Sigma A B)\<close>
        by simp
      show \<open>Sigma {x} B \<subseteq> Sigma A B\<close> using xA by auto
    qed
    have step2: \<open>(\<lambda>y. f x y) \<circ> snd multipliable_on Sigma {x} B\<close>
      using step1 multipliable_on_cong[of \<open>Sigma {x} B\<close> \<open>\<lambda>(a,b). f a b\<close> \<open>(\<lambda>y. f x y) \<circ> snd\<close>]
      by auto
    have inj: \<open>inj_on snd (Sigma {x} B)\<close>
      by (auto intro!: inj_onI simp: Sigma_def)
    have step3: \<open>(\<lambda>y. f x y) multipliable_on snd ` Sigma {x} B\<close>
      using step2 multipliable_on_reindex[OF inj, of \<open>\<lambda>y. f x y\<close>] by simp
    have \<open>snd ` Sigma {x} B = B x\<close>
      by (force simp: Sigma_def)
    with step3 show ?thesis by simp
  qed
  then show ?thesis1
    using infprod_Sigma' assms by blast
  show ?thesis2
    unfolding multipliable_on_def
  proof -
    have \<open>(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)\<close> by simp
    then have ab: \<open>((\<lambda>(x,y). f x y) has_setprod infprod (\<lambda>(x,y). f x y) (Sigma A B)) (Sigma A B)\<close>
      by (rule has_setprod_infprod)
    have bx: \<open>(f x has_setprod infprod (f x) (B x)) (B x)\<close> if \<open>x \<in> A\<close> for x
      using mult_B[OF that] has_setprod_infprod by auto
    have bx': \<open>((\<lambda>y. (case (x,y) of (a,b) \<Rightarrow> f a b)) has_setprod infprod (f x) (B x)) (B x)\<close> if \<open>x \<in> A\<close> for x
      using bx[OF that] by simp
    from has_setprod_Sigma[OF ab bx']
    show \<open>\<exists>a. ((\<lambda>x. infprod (f x) (B x)) has_setprod a) A\<close>
      by blast
  qed
qed

lemma infprod_Sigma_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{banach,real_normed_field}\<close>
  assumes [simp]: "f multipliable_on (Sigma A B)"
  assumes \<open>infprod f (Sigma A B) \<noteq> 0\<close>
  shows \<open>infprod (\<lambda>x. infprod (\<lambda>y. f (x,y)) (B x)) A = infprod f (Sigma A B)\<close>
  using assms
  by (simp add: infprod_Sigma'_banach)

lemma infprod_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field"
  assumes \<open>(\<lambda>(x, y). f x y) multipliable_on (A \<times> B)\<close>
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> (f a) multipliable_on B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> (\<lambda>a. f a b) multipliable_on A\<close>
  shows \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
proof -
  have "(\<lambda>(x, y). f y x) \<circ> prod.swap multipliable_on A \<times> B"
    by (simp add: assms(1) multipliable_on_cong)
  then have fyx: \<open>(\<lambda>(x, y). f y x) multipliable_on (B \<times> A)\<close>
    by (metis has_setprod_reindex infprod_reindex inj_swap product_swap multipliable_iff_has_setprod_infprod)
  have \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using infprod_Sigma' assms by blast
  also have \<open>\<dots> = infprod (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    by (simp add: product_swap [symmetric, of B] infprod_reindex o_def)
  also have \<open>\<dots> = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
    using assms(3) fyx infprod_Sigma by force
  finally show ?thesis .
qed

lemma infprod_swap_banach:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{banach,real_normed_field}"
  assumes mult: \<open>(\<lambda>(x, y). f x y) multipliable_on (A \<times> B)\<close>
  assumes nz: \<open>infprod (\<lambda>(x, y). f x y) (A \<times> B) \<noteq> 0\<close>
  shows "infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B"
proof -
  have \<section>: \<open>(\<lambda>(x, y). f y x) multipliable_on (B \<times> A)\<close>
    by (metis (mono_tags, lifting) mult case_swap inj_swap o_apply product_swap multipliable_on_cong multipliable_on_reindex)
  have swap: \<open>infprod (\<lambda>(x,y). f y x) (B \<times> A) = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infprod_reindex)
    using mult by (auto simp: o_def)
  have \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using mult nz infprod_Sigma'_banach by blast
  also have \<open>\<dots> = infprod (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    by (simp add: swap)
  also have \<open>\<dots> = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
    using \<section> nz swap by (intro infprod_Sigma'_banach [symmetric]) auto
  finally show ?thesis .
qed

lemma has_setprod_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>((\<lambda>_. c) has_setprod c ^ card F) F\<close>
  by (metis assms has_setprod_finite prod_constant)

lemma infprod_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infprod (\<lambda>_. c) F = c ^ card F\<close>
  by (simp add: assms)

lemma has_setprod_power:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>x. f x ^ n) has_setprod (P ^ n)) A"
  using assms by (induction n) (auto intro!: has_setprod_mult)

lemma multipliable_on_power:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A"
  shows   "(\<lambda>x. f x ^ n) multipliable_on A"
  using assms by (induction n) (auto intro!: multipliable_on_mult)

lemma infprod_power:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A"
  shows \<open>infprod (\<lambda>x. f x ^ n) A = infprod f A ^ n\<close>
  using assms by (simp add: has_setprod_power infprodI)

lemma has_setprod_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod (inverse a)) A" and "a \<noteq> 0"
  shows   \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close>
proof (rule has_setprodI)
  from assms(1) have lim: \<open>(prod f \<longlongrightarrow> inverse a) (finite_subsets_at_top A)\<close>
    by (rule has_setprodD)
  from assms(2) have \<open>inverse a \<noteq> 0\<close> by simp
  from tendsto_inverse[OF lim this] have \<open>((\<lambda>X. inverse (prod f X)) \<longlongrightarrow> inverse (inverse a)) (finite_subsets_at_top A)\<close> .
  also have \<open>inverse (inverse a) = a\<close> using assms(2) by simp
  finally show \<open>((\<lambda>X. prod (\<lambda>x. inverse (f x)) X) \<longlongrightarrow> a) (finite_subsets_at_top A)\<close>
    by (simp add: prod_inversef[symmetric] o_def)
qed

lemma has_setprod_inverse_iff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "a \<noteq> 0"
  shows \<open>((\<lambda>x. inverse (f x)) has_setprod a) A \<longleftrightarrow> (f has_setprod (inverse a)) A\<close>
proof
  assume h: \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close>
  have \<open>a = inverse (inverse a)\<close> using assms by simp
  with h have \<open>((\<lambda>x. inverse (f x)) has_setprod (inverse (inverse a))) A\<close> by simp
  from has_setprod_inverse[OF this] assms show \<open>(f has_setprod (inverse a)) A\<close>
    by (simp add: inverse_inverse_eq)
next
  assume \<open>(f has_setprod (inverse a)) A\<close>
  from has_setprod_inverse[OF this] assms show \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close> by simp
qed

lemma multipliable_on_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" and "infprod f A \<noteq> 0"
  shows   "(\<lambda>x. inverse (f x)) multipliable_on A"
proof -
  from assms(1) have \<open>(f has_setprod (infprod f A)) A\<close>
    by (rule has_setprod_infprod)
  moreover have \<open>infprod f A = inverse (inverse (infprod f A))\<close>
    using assms(2) by simp
  ultimately have \<open>(f has_setprod (inverse (inverse (infprod f A)))) A\<close>
    by simp
  from has_setprod_inverse[OF this] assms(2) 
  have \<open>((\<lambda>x. inverse (f x)) has_setprod (inverse (infprod f A))) A\<close>
    by simp
  thus ?thesis
    unfolding multipliable_on_def by blast
qed


lemma infprod_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes \<open>f multipliable_on A\<close> and \<open>infprod f A \<noteq> 0\<close>
  shows \<open>infprod (\<lambda>x. inverse (f x)) A = inverse (infprod f A)\<close>
proof -
  have \<open>(f has_setprod (infprod f A)) A\<close>
    using assms(1) by (rule has_setprod_infprod)
  moreover have \<open>infprod f A = inverse (inverse (infprod f A))\<close>
    using assms(2) by simp
  ultimately have \<open>(f has_setprod (inverse (inverse (infprod f A)))) A\<close>
    by simp
  from has_setprod_inverse[OF this] assms(2)
  have \<open>((\<lambda>x. inverse (f x)) has_setprod (inverse (infprod f A))) A\<close>
    by simp
  thus ?thesis by (rule infprodI)
qed

text \<open>
  Quotients.  \<open>has_setprod_mult\<close> and \<open>has_setprod_inverse\<close> are here already; this is the
  combination one actually writes.
\<close>
lemma has_setprod_divide:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes f: "(f has_setprod a) A" and g: "(g has_setprod b) A" and b: "b \<noteq> 0"
  shows   "((\<lambda>x. f x / g x) has_setprod (a / b)) A"
proof -
  have "((\<lambda>x. inverse (g x)) has_setprod inverse b) A"
  proof (subst has_setprod_inverse_iff)
    show "inverse b \<noteq> 0"
      using b by simp
    show "(g has_setprod inverse (inverse b)) A"
      using g b by simp
  qed
  from has_setprod_mult[OF f this] show ?thesis
    by (simp add: divide_inverse)
qed

lemma multipliable_on_divide:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" "g multipliable_on A" "infprod g A \<noteq> 0"
  shows   "(\<lambda>x. f x / g x) multipliable_on A"
  using has_setprod_divide[OF has_setprod_infprod[OF assms(1)] has_setprod_infprod[OF assms(2)]
                              assms(3)]
  by (rule has_setprod_imp_multipliable)

lemma infprod_divide:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" "g multipliable_on A" "infprod g A \<noteq> 0"
  shows   "infprod (\<lambda>x. f x / g x) A = infprod f A / infprod g A"
  using has_setprod_divide[OF has_setprod_infprod[OF assms(1)] has_setprod_infprod[OF assms(2)] assms(3)]
  by (rule infprodI)

lemma multipliable_on_inverse_iff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  shows \<open>(f multipliable_on A \<and> infprod f A \<noteq> 0) \<longleftrightarrow>
         ((\<lambda>x. inverse (f x)) multipliable_on A \<and> infprod (\<lambda>x. inverse (f x)) A \<noteq> 0)\<close>
proof (intro iffI conjI)
  assume asm: \<open>f multipliable_on A \<and> infprod f A \<noteq> 0\<close>
  then show \<open>(\<lambda>x. inverse (f x)) multipliable_on A\<close>
    by (intro multipliable_on_inverse) auto
  from asm show \<open>infprod (\<lambda>x. inverse (f x)) A \<noteq> 0\<close>
    by (simp add: infprod_inverse)
next
  assume asm: \<open>(\<lambda>x. inverse (f x)) multipliable_on A \<and> infprod (\<lambda>x. inverse (f x)) A \<noteq> 0\<close>
  then have mult_inv: \<open>(\<lambda>x. inverse (f x)) multipliable_on A\<close> and
            nz_inv: \<open>infprod (\<lambda>x. inverse (f x)) A \<noteq> 0\<close> by auto
  from multipliable_on_inverse[OF mult_inv nz_inv]
  have inv_mult: \<open>(\<lambda>x. inverse (inverse (f x))) multipliable_on A\<close> .
  then show \<open>f multipliable_on A\<close>
    using multipliable_on_cong[of A \<open>\<lambda>x. inverse (inverse (f x))\<close> f] by auto
  from infprod_inverse[OF mult_inv nz_inv]
  have \<open>infprod (\<lambda>x. inverse (inverse (f x))) A = inverse (infprod (\<lambda>x. inverse (f x)) A)\<close> .
  moreover have \<open>infprod (\<lambda>x. inverse (inverse (f x))) A = infprod f A\<close>
    by (intro infprod_cong) auto
  ultimately show \<open>infprod f A \<noteq> 0\<close>
    using nz_inv by simp
qed


lemma has_setprod_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod P) A" and "P \<noteq> 0"
  shows   "((\<lambda>x. f x powi n) has_setprod (P powi n)) A"
proof (cases \<open>n \<ge> 0\<close>)
  case True
  then show ?thesis
    using assms(1) by (auto simp: power_int_def intro!: has_setprod_power)
next
  case False
  then have \<open>P ^ nat (- n) \<noteq> 0\<close> using assms(2) by auto
  with False show ?thesis
    using assms(1) by (auto simp: power_int_def power_inverse intro!: has_setprod_power has_setprod_inverse)
qed

lemma multipliable_on_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" and "infprod f A \<noteq> 0"
  shows   "(\<lambda>x. f x powi n) multipliable_on A"
proof (cases \<open>n \<ge> 0\<close>)
  case True
  then show ?thesis
    using assms(1) by (auto simp: power_int_def intro!: multipliable_on_power)
next
  case False
  have \<open>(\<lambda>x. f x ^ nat (-n)) multipliable_on A\<close>
    using assms(1) by (rule multipliable_on_power)
  moreover have \<open>infprod (\<lambda>x. f x ^ nat (-n)) A \<noteq> 0\<close>
    using assms by (simp add: infprod_power)
  ultimately have \<open>(\<lambda>x. inverse (f x ^ nat (-n))) multipliable_on A\<close>
    by (rule multipliable_on_inverse)
  with False show ?thesis
    by (auto simp: power_int_def power_inverse)
qed

lemma infprod_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" and "infprod f A \<noteq> 0"
  shows \<open>infprod (\<lambda>x. f x powi n) A = infprod f A powi n\<close>
  using infprod_inverse
infprod_power
  using assms has_setprod_power_int infprodI multipliable_iff_has_setprod_infprod by blast

lemma has_sum_imp_has_setprod_exp:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_sum S) A"
  shows   "((\<lambda>x. exp (f x)) has_setprod exp S) A"
proof (rule has_setprodI)
  have "((\<lambda>X. exp (sum f X)) \<longlongrightarrow> exp S) (finite_subsets_at_top A)"
    using assms by (intro tendsto_exp) (auto simp: has_sum_def)
  also have "?this \<longleftrightarrow> ((\<lambda>X. (\<Prod>x\<in>X. exp (f x))) \<longlongrightarrow> exp S) (finite_subsets_at_top A)"
    by (intro filterlim_cong refl eventually_finite_subsets_at_top_weakI) (auto simp: exp_sum)
  finally show "((\<lambda>X. (\<Prod>x\<in>X. exp (f x))) \<longlongrightarrow> exp S) (finite_subsets_at_top A)" .
qed

lemma multipliable_on_exp:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f summable_on A"
  shows   "(\<lambda>x. exp (f x)) multipliable_on A"
proof -
  from assms obtain S where S: "(f has_sum S) A"
    by (auto simp: summable_on_def)
  show ?thesis
    using has_sum_imp_has_setprod_exp[OF S]  has_setprod_imp_multipliable by blast
qed

lemma has_setprod_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "((\<lambda>x. f (g x)) has_setprod S) A = (f has_setprod S) B"
proof -
  have "((\<lambda>x. f (g x)) has_setprod S) A \<longleftrightarrow> (f has_setprod S) (g ` A)"
    by (subst has_setprod_reindex) (use assms in \<open>auto dest: bij_betw_imp_inj_on simp: o_def\<close>)
  then show ?thesis
    using assms bij_betw_imp_surj_on by blast 
qed

lemma has_setprod_reindex_bij_witness:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  assumes "s = s'"
  shows   "(g has_setprod s) S = (h has_setprod s') T"
  by (smt (verit, del_insts) assms bij_betwI' has_setprod_cong has_setprod_reindex_bij_betw)


lemma has_setprod_homomorphism:
  assumes "(f has_setprod S) A" "h 1 = 1" "\<And>a b. h (a * b) = h a * h b" "continuous_on UNIV h"
  shows   "((\<lambda>x. h (f x)) has_setprod (h S)) A"
proof -
  have "prod (h \<circ> f) X = h (prod f X)" for X
    by (induction X rule: infinite_finite_induct) (simp_all add: assms)
  hence prod_h: "prod (h \<circ> f) = h \<circ> prod f"
    by (intro ext) auto
  have "((\<lambda>x. h (prod f x)) \<longlongrightarrow> h S) (finite_subsets_at_top A)"
    by (rule continuous_on_tendsto_compose[OF assms(4) has_setprodD[OF assms(1)]]) auto
  hence "((h \<circ> f) has_setprod h S) A"
    unfolding has_setprod_def prod_h unfolding o_def by simp
  thus ?thesis
    by (simp add: o_def)
qed

lemma multipliable_on_homomorphism:
  assumes "f multipliable_on A" "h 1 = 1" "\<And>a b. h (a * b) = h a * h b" "continuous_on UNIV h"
  shows   "(\<lambda>x. h (f x)) multipliable_on A"
proof -
  from assms(1) obtain S where "(f has_setprod S) A"
    by (auto simp: multipliable_on_def)
  hence "((\<lambda>x. h (f x)) has_setprod h S) A"
    by (rule has_setprod_homomorphism) (use assms in auto)
  thus ?thesis
    by (auto simp: multipliable_on_def)
qed

lemma infprod_homomorphism_strong:
  fixes h :: "'a :: {t2_space, topological_comm_monoid_mult, semidom} \<Rightarrow>
                'b :: {t2_space, topological_comm_monoid_mult, semidom}"
  assumes "(\<lambda>x. h (f x)) multipliable_on A \<longleftrightarrow> f multipliable_on A"
  assumes "h 1 = 1"
  assumes "\<And>S. (f has_setprod S) A \<Longrightarrow> ((\<lambda>x. h (f x)) has_setprod (h S)) A"
  shows   "infprod (\<lambda>x. h (f x)) A = h (infprod f A)"
  by (metis assms has_setprod_infprod infprodI infprod_not_exists)

lemma has_setprod_of_nat: "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. of_nat (f x)) has_setprod of_nat S) A"
  by (erule has_setprod_homomorphism) (auto intro!: continuous_intros)

lemma has_setprod_of_int: "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. of_int (f x)) has_setprod of_int S) A"
  by (erule has_setprod_homomorphism) (auto intro!: continuous_intros)

lemma multipliable_on_of_nat: "f multipliable_on A \<Longrightarrow> (\<lambda>x. of_nat (f x)) multipliable_on A"
  by (erule multipliable_on_homomorphism) (auto intro!: continuous_intros)

lemma multipliable_on_of_int: "f multipliable_on A \<Longrightarrow> (\<lambda>x. of_int (f x)) multipliable_on A"
  by (erule multipliable_on_homomorphism) (auto intro!: continuous_intros)

text \<open>The same for the embedding of the reals, which is how a real product becomes a complex one.\<close>
lemma has_setprod_of_real:
  "(f has_setprod S) A \<Longrightarrow>
     ((\<lambda>x. of_real (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult})
        has_setprod of_real S) A"
  by (erule has_setprod_homomorphism) (auto intro!: continuous_intros)

lemma multipliable_on_of_real:
  "f multipliable_on A \<Longrightarrow>
     (\<lambda>x. of_real (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult})
        multipliable_on A"
  by (erule multipliable_on_homomorphism) (auto intro!: continuous_intros)

lemma infprod_of_real:
  assumes "f multipliable_on A"
  shows "infprod (\<lambda>x. of_real (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) A
           = of_real (infprod f A)"
  using has_setprod_of_real[OF has_setprod_infprod[OF assms]] by (rule infprodI)

lemma multipliable_on_discrete_iff:
  fixes f :: "'a \<Rightarrow> 'b :: {ring_1_no_zero_divisors, discrete_topology, topological_comm_monoid_mult, semidom}"
  shows "f multipliable_on A \<longleftrightarrow> (\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}"
proof
  assume \<open>(\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}\<close>
  then show \<open>f multipliable_on A\<close>
  proof
    assume \<open>\<exists>x\<in>A. f x = 0\<close>
    then obtain x where \<open>x \<in> A\<close> \<open>f x = 0\<close> by auto
    with zero_imp_has_setprod_0
    show \<open>f multipliable_on A\<close> unfolding multipliable_on_def by metis
  next
    assume *: \<open>finite {x\<in>A. f x \<noteq> 1}\<close>
    hence \<open>f multipliable_on {x\<in>A. f x \<noteq> 1}\<close>
      by (rule multipliable_on_finite)
    then show \<open>f multipliable_on A\<close>
      by (smt (verit) DiffE mem_Collect_eq multipliable_on_cong_neutral)
  qed
next
  assume \<open>f multipliable_on A\<close>
  then obtain S where S: \<open>(f has_setprod S) A\<close>
    by (auto simp: multipliable_on_def)
  hence \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. prod f x = S\<close>
    unfolding has_setprod_def tendsto_discrete .
  then obtain X where X: \<open>finite X\<close> \<open>X \<subseteq> A\<close> \<open>\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y = S\<close>
    unfolding eventually_finite_subsets_at_top by metis
  have prodX: \<open>prod f X = S\<close> using X by auto
  show \<open>(\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}\<close>
  proof (cases \<open>S = 0\<close>)
    case True
    then have \<open>prod f X = 0\<close> using prodX by simp
    then obtain x where \<open>x \<in> X\<close> \<open>f x = 0\<close>
      using X(1) by (metis prod_zero_iff)
    with X(2) show ?thesis by auto
  next
    case False
    have \<open>{x\<in>A. f x \<noteq> 1} \<subseteq> X\<close>
    proof
      fix x assume x: \<open>x \<in> {x\<in>A. f x \<noteq> 1}\<close>
      show \<open>x \<in> X\<close>
      proof (rule ccontr)
        assume [simp]: \<open>x \<notin> X\<close>
        have \<open>prod f (insert x X) = S\<close>
          using X x by (intro X) auto
        then have \<open>f x * prod f X = S\<close>
          using X(1) by simp
        then have \<open>f x * S = S\<close> using prodX by simp
        with False have \<open>f x = 1\<close>
          by (metis mult_cancel_right1)
        with x show False by auto
      qed
    qed
    thus ?thesis using X(1) finite_subset by blast
  qed
qed

lemma has_setprod_imp_has_prod:
  fixes f :: \<open>nat \<Rightarrow> 'a::real_normed_field\<close>
  assumes \<open>(f has_setprod S) (UNIV :: nat set)\<close> and \<open>convergent_prod f\<close>
  shows \<open>f has_prod S\<close>
proof -
  from assms(1) have \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_setprod_def)
  then have lim_S: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> S\<close>
  proof (rule filterlim_compose)
    show \<open>filterlim (\<lambda>n. {..n}) (finite_subsets_at_top UNIV) sequentially\<close>
      using filterlim_atMost_at_top by auto
  qed
  from assms(2) have lim_P: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> prodinf f\<close>
    using convergent_prod_LIMSEQ by blast
  from lim_S lim_P have \<open>S = prodinf f\<close>
    by (rule LIMSEQ_unique)
  with assms(2) show \<open>f has_prod S\<close>
    using convergent_prod_has_prod by blast
qed

lemma multipliable_on_imp_convergent_prod:
  fixes f :: \<open>nat \<Rightarrow> 'a::real_normed_field\<close>
  assumes \<open>f multipliable_on (UNIV :: nat set)\<close> and \<open>infprod f UNIV \<noteq> 0\<close>
  shows \<open>convergent_prod f\<close>
proof -
  define S where \<open>S = infprod f UNIV\<close>
  from assms(1) have \<open>(f has_setprod S) UNIV\<close>
    unfolding S_def by (rule has_setprod_infprod)
  then have lim: \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_setprod_def)
  then have seq_lim: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> S\<close>
  proof (rule filterlim_compose)
    show \<open>filterlim (\<lambda>n. {..n}) (finite_subsets_at_top UNIV) sequentially\<close>
      using filterlim_atMost_at_top by auto
  qed
  \<comment> \<open>Since S is nonzero, eventually partial products are nonzero\<close>
  from seq_lim assms(2)[folded S_def] have \<open>\<forall>\<^sub>F n in sequentially. prod f {..n} \<noteq> 0\<close>
    by (intro tendsto_imp_eventually_ne) auto
  then obtain N where N: \<open>\<And>n. n \<ge> N \<Longrightarrow> prod f {..n} \<noteq> 0\<close>
    by (auto simp: eventually_at_top_linorder)
  have fnz: \<open>f n \<noteq> 0\<close> if \<open>n > N\<close> for n
  proof -
    from N[of n] N[of \<open>n - 1\<close>] that
    have \<open>prod f {..n} \<noteq> 0\<close> \<open>prod f {..n-1} \<noteq> 0\<close> by auto
    moreover have \<open>prod f {..n} = f n * prod f {..n-1}\<close> using that
      by (metis Suc_pred' gr_implies_not_zero mult.commute not_gr_zero prod.atMost_Suc)
    ultimately show \<open>f n \<noteq> 0\<close> by auto
  qed
  \<comment> \<open>The shifted sequence converges to a nonzero limit\<close>
  have \<open>convergent_prod (\<lambda>i. f (i + Suc N))\<close>
  proof -
    have lim: \<open>(\<lambda>n. \<Prod>i\<le>n. f (i + Suc N)) \<longlonglongrightarrow> S / prod f {..N}\<close>
    proof -
      have \<open>(\<lambda>n. prod f {..n + Suc N}) \<longlonglongrightarrow> S\<close>
        using seq_lim LIMSEQ_ignore_initial_segment
        by blast
      moreover have \<open>prod f {..n + Suc N} = prod f {..N} * prod (\<lambda>i. f (i + Suc N)) {..n}\<close> for n
      proof -
        have \<open>{..n + Suc N} = {..N} \<union> {Suc N..n + Suc N}\<close> by auto
        also have \<open>prod f \<dots> = prod f {..N} * prod f {Suc N..n + Suc N}\<close>
          by (subst prod.union_disjoint) auto
        also have \<open>prod f {Suc N..n + Suc N} = prod (\<lambda>i. f (i + Suc N)) {..n}\<close>
          by (metis (no_types) add_0 atMost_atLeast0 prod.shift_bounds_cl_nat_ivl)
        finally show ?thesis .
      qed
      ultimately have \<open>(\<lambda>n. prod f {..N} * prod (\<lambda>i. f (i + Suc N)) {..n}) \<longlonglongrightarrow> S\<close>
        by (simp add: tendsto_cong)
      then have \<open>(\<lambda>n. prod f {..N} * prod (\<lambda>i. f (i + Suc N)) {..n} / prod f {..N}) \<longlonglongrightarrow> S / prod f {..N}\<close>
        using N[of N, simplified]
        by (intro tendsto_divide tendsto_const) auto
      then show ?thesis
        using N[of N, simplified] by (simp add: field_simps)
    qed
    moreover have \<open>S / prod f {..N} \<noteq> 0\<close>
      using assms(2)[folded S_def] N[of N, simplified] by auto
    ultimately have \<open>raw_has_prod (\<lambda>i. f (i + Suc N)) 0 (S / prod f {..N})\<close>
      by (simp add: raw_has_prod_def)
    then show ?thesis
      unfolding convergent_prod_def by blast
  qed
  then show \<open>convergent_prod f\<close>
    by (rule convergent_prod_offset)
qed

lemma has_prod_imp_sums_ln_real: 
  fixes f :: "'a \<Rightarrow> real"
  assumes "(f has_setprod p) A" "p \<noteq> 0"
  shows "((\<lambda>x. ln (f x)) has_sum (ln p)) A"
proof -
  have nz: "f x \<noteq> 0" if "x \<in> A" for x
    using assms that by (metis infprodI zero_imp_has_setprod_0)
  have "((\<lambda>X. ln (prod f X)) \<longlongrightarrow> ln p) (finite_subsets_at_top A)"
  proof (rule tendsto_ln)
    show "(prod f \<longlongrightarrow> p) (finite_subsets_at_top A)"
      using assms(1) unfolding has_setprod_def by blast
  qed (use assms in auto)
  also have "?this \<longleftrightarrow> (sum (\<lambda>x. ln (f x)) \<longlongrightarrow> ln p) (finite_subsets_at_top A)"
  proof (intro filterlim_cong)
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. X \<subseteq> A \<and> finite X"
      by (rule eventually_finite_subsets_at_top_weakI) auto
    thus "\<forall>\<^sub>F x in finite_subsets_at_top A. ln (prod f x) = (\<Sum>x\<in>x. ln (f x))"
      by eventually_elim (subst ln_prod, use nz in auto)
  qed auto
  finally show ?thesis
    unfolding has_sum_def .
qed


subsection \<open>Strong multipliability\<close>

text \<open>
  A finite family is strongly multipliable, with no side condition: the set of vanishing factors is
  trivially finite, and a finite product of non-zero elements of a semidom is non-zero.  Compare
  \<open>multipliable_on_finite\<close> and \<open>abs_multipliable_on_finite\<close>.
\<close>
lemma strongly_multipliable_on_finite [simp]:
  assumes "finite A"
  shows   "f strongly_multipliable_on A"
proof -
  have "finite {x \<in> A. f x \<noteq> 0}"
    using assms by simp
  hence "(f has_setprod prod f {x \<in> A. f x \<noteq> 0}) {x \<in> A. f x \<noteq> 0}"
    by (rule has_setprod_finite)
  moreover have "prod f {x \<in> A. f x \<noteq> 0} \<noteq> 0"
    using assms by (subst prod_zero_iff) auto
  ultimately show ?thesis
    unfolding strongly_multipliable_on_def using assms by auto
qed

lemma strongly_multipliable_imp_multipliable:
  assumes "f strongly_multipliable_on A"
  shows   "f multipliable_on A"
proof -
  from assms obtain P where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}"
    by (auto simp: strongly_multipliable_on_def)
  have "(f has_setprod (P * prod f {x\<in>A. f x = 0})) ({x\<in>A. f x \<noteq> 0} \<union> {x\<in>A. f x = 0})"
    by (intro has_setprod_Un_disjoint P has_setprod_finite) auto
  also have "{x\<in>A. f x \<noteq> 0} \<union> {x\<in>A. f x = 0} = A"
    by auto
  finally show ?thesis
    by (rule has_setprod_imp_multipliable)
qed

text \<open>
  For a non-zero family, strong multipliability is equivalent to the product being non-zero.
\<close>
lemma strongly_multipliable_on_nonzero_iff:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "f strongly_multipliable_on A \<longleftrightarrow> (\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0)"
proof
  assume *: "(\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0)"
  from assms have [simp]: "{x\<in>A. f x = 0} = {}" "{x\<in>A. f x \<noteq> 0} = A"
    by auto
  from * obtain P where P: "(f has_setprod P) A" "P \<noteq> 0"
    by blast
  thus "f strongly_multipliable_on A"
    by (auto simp: strongly_multipliable_on_def assms)
next
  assume "f strongly_multipliable_on A"
  then obtain P where "(f has_setprod P) {x\<in>A. f x \<noteq> 0} \<and> P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  also have "{x\<in>A. f x \<noteq> 0} = A"
    using assms by auto
  finally show "\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0"
    by blast
qed

text \<open>
  When the product is \<^emph>\<open>strongly\<close> multipliable its value vanishes only for the obvious reason.  Some
  hypothesis of that kind is needed: over an infinite index set \<^term>\<open>\<lambda>_. 1/2 :: real\<close> is
  multipliable with value \<open>0\<close> and no vanishing factor.
\<close>
lemma has_setprod_eq_0_iff:
  assumes "f strongly_multipliable_on A" and P: "(f has_setprod P) A"
  shows   "P = 0 \<longleftrightarrow> (\<exists>x\<in>A. f x = 0)"
proof
  assume "\<exists>x\<in>A. f x = 0"
  then obtain x where "x \<in> A" "f x = 0"
    by blast
  hence "(f has_setprod 0) A"
    by (rule zero_imp_has_setprod_0)
  with P show "P = 0"
    by (rule has_setprod_unique)
next
  assume P0: "P = 0"
  show "\<exists>x\<in>A. f x = 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>x\<in>A. f x = 0)"
    hence nz: "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
      by blast
    \<comment> \<open>\<^bold>\<open>NB\<close> \<open>blast\<close> on \<open>strongly_multipliable_on_nonzero_iff\<close> together with the existential
        diverges; apply the equivalence explicitly\<close>
    have "\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0"
      by (rule iffD1[OF strongly_multipliable_on_nonzero_iff[OF nz] assms(1)])
    then obtain Q where Q: "(f has_setprod Q) A" "Q \<noteq> 0"
      by blast
    from has_setprod_unique[OF P Q(1)] Q(2) P0 show False
      by simp
  qed
qed

corollary infprod_eq_0_iff:
  assumes "f strongly_multipliable_on A"
  shows   "infprod f A = 0 \<longleftrightarrow> (\<exists>x\<in>A. f x = 0)"
proof -
  have "f multipliable_on A"
    using assms by (rule strongly_multipliable_imp_multipliable)
  hence "(f has_setprod infprod f A) A"
    by (rule has_setprod_infprod)
  with assms show ?thesis
    by (rule has_setprod_eq_0_iff)
qed

lemma strongly_multipliable_on_Diff_finite:
  fixes f :: "_ \<Rightarrow> 'a :: real_normed_field"
  assumes "f strongly_multipliable_on A" "finite B"
  shows   "f strongly_multipliable_on (A - B)"
proof -
  from assms(1) obtain P where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}" "P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  define Q where "Q = prod f {x\<in>B\<inter>A. f x \<noteq> 0}"
  have Q: "(f has_setprod Q) {x\<in>B\<inter>A. f x \<noteq> 0}"
    unfolding Q_def by (intro has_setprod_finite) (use assms(2) in auto)
  have [simp]: "Q \<noteq> 0"
    using assms(2) by (auto simp: Q_def)

  have "(f has_setprod (P / Q)) ({x\<in>A. f x \<noteq> 0} - {x\<in>B\<inter>A. f x \<noteq> 0})"
    by (intro has_setprod_Diff P Q) auto
  also have "{x\<in>A. f x \<noteq> 0} - {x\<in>B\<inter>A. f x \<noteq> 0} = {x\<in>A-B. f x \<noteq> 0}"
    by blast
  finally have "(f has_setprod P / Q) {x\<in>A-B. f x \<noteq> 0}" .
  moreover have "finite {x\<in>A-B. f x = 0}"
    by (rule finite_subset[OF _ P(1)]) auto
  moreover have "P / Q \<noteq> 0"
    using P(3) by auto
  ultimately show ?thesis
    unfolding strongly_multipliable_on_def by blast
qed


subsection \<open>Absolute convergence\<close>

(*
  TODO: why does this use the explicit limit rather than has_setprod?
  Also, this seems a bit too concrete. One should be able to prove something like
  the version below in a more general setting (but it will probably require a bit of juggling
  with uniformity).
*)
lemma has_setprod_factors_tend_to_1:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra,comm_monoid_mult}"
  assumes lim: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top M)" and nz: "L \<noteq> 0"
  shows "\<forall>\<epsilon>>0. \<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. dist (f x) 1 < \<epsilon>)"
proof (intro allI impI)
  fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
  obtain F where F: "finite F" "F \<subseteq> M"
    and near: "\<And>D. finite D \<Longrightarrow> D \<subseteq> M - F \<Longrightarrow> dist (prod f D) 1 < \<epsilon>"
    using has_setprod_prods_near_1[OF lim nz \<epsilon>] by blast
  have "dist (f x) 1 < \<epsilon>" if "x \<in> M - F" for x
    using near[of "{x}"] that by simp
  with F show "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. dist (f x) 1 < \<epsilon>)"
    by blast
qed

lemma has_setprod_factors_tend_to_1':
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra, comm_monoid_mult}"
  assumes lim: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top M)" and nz: "L \<noteq> 0"
  assumes X: "open X" "1 \<in> X"
  shows "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. f x \<in> X)"
proof -
  from X obtain \<epsilon> where "\<epsilon> > 0" and ball_sub: "ball 1 \<epsilon> \<subseteq> X"
    using openE by blast
  from has_setprod_factors_tend_to_1[OF lim nz, rule_format, OF \<open>\<epsilon> > 0\<close>]
  obtain F where "finite F" "F \<subseteq> M" "\<And>x. x \<in> M - F \<Longrightarrow> dist (f x) 1 < \<epsilon>"
    by blast
  then show ?thesis
    using ball_sub by (intro exI[of _ F]) (auto simp: ball_def dist_commute)
qed

text \<open>
  For a strongly multipliable family, all but finitely many values are close to 1.
\<close>
lemma strongly_multipliable_on_imp_nhds_1:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_div_algebra,semidom}"
  assumes "f strongly_multipliable_on A" "open X" "1 \<in> X"
  shows "\<exists>B. B \<subseteq> A \<and> finite B \<and> (\<forall>x\<in>A-B. f x \<in> X)"
proof -
  from assms(1) obtain P 
    where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}" "P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  have "\<exists>F. finite F \<and> F \<subseteq> {x \<in> A. f x \<noteq> 0} \<and> (\<forall>x\<in>{x \<in> A. f x \<noteq> 0} - F. f x \<in> X)"
    by (rule has_setprod_factors_tend_to_1'[where L = P])
       (use assms P in \<open>auto simp: has_setprod_def\<close>)
  then obtain F where F: "finite F" "F \<subseteq> {x\<in>A. f x \<noteq> 0}" "\<forall>x\<in>{x \<in> A. f x \<noteq> 0} - F. f x \<in> X"
    by blast
  define B where "B = F \<union> {x\<in>A. f x = 0}"
  have "B \<subseteq> A" "finite B" "\<forall>x\<in>A-B. f x \<in> X"
    unfolding B_def using F P by auto
  thus ?thesis
    by blast
qed

text \<open>
  The equivalent for summable familes: In a summable family, all but finitely many elements are
  close to 0.
\<close>
lemma summable_on_imp_nhds_0:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes lim: "f summable_on M"
  assumes X: "open X" "0 \<in> X"
  shows "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. f x \<in> X)"
proof -
  from lim obtain S where S: "(f has_sum S) M"
    unfolding summable_on_def by blast
  hence tend: "((\<lambda>U. sum f U) \<longlongrightarrow> S) (finite_subsets_at_top M)"
    by (auto simp: has_sum_def)
  \<comment> \<open>Find open W around S such that $a - b \<in> X$ whenever $a$, $b \<in> W$\<close>
  have "continuous_on UNIV (\<lambda>(a::'b, b). a - b)"
    by (auto intro!: continuous_intros simp: case_prod_unfold)
  hence cont: "isCont (\<lambda>(a::'b, b). a - b) (S, S)"
    by (simp add: continuous_on_eq_continuous_at)
  from cont[unfolded isCont_def] have "((\<lambda>(a,b). a - b) \<longlongrightarrow> (0::'b)) (nhds (S, S))"
    by (simp add: tendsto_nhds_iff)
  from this[unfolded tendsto_def, rule_format, OF X(1) X(2)]
  have "eventually (\<lambda>(a,b). a - b \<in> X) (nhds (S, S))"
    by (simp add: case_prod_unfold)
  hence "\<forall>\<^sub>F (a, b) in nhds S \<times>\<^sub>F nhds S. a - b \<in> X"
    by (simp add: nhds_prod[symmetric])
  then obtain Q where Q_ev: "eventually Q (nhds S)" and Q_sub: "\<And>a b. Q a \<Longrightarrow> Q b \<Longrightarrow> a - b \<in> X"
    unfolding eventually_prod_same by auto
  then obtain W where W: "open W" "S \<in> W" "W \<subseteq> Collect Q"
    unfolding eventually_nhds by auto
  have W_sub: "a - b \<in> X" if "a \<in> W" "b \<in> W" for a b
    using Q_sub that W(3) by auto
  \<comment> \<open>Get F such that all partial sums beyond F are in W\<close>
  from tend have "eventually (\<lambda>U. sum f U \<in> W) (finite_subsets_at_top M)"
    using topological_tendstoD W by blast
  then obtain F where F: "finite F" "F \<subseteq> M" 
    "\<And>U. finite U \<Longrightarrow> F \<subseteq> U \<Longrightarrow> U \<subseteq> M \<Longrightarrow> sum f U \<in> W"
    unfolding eventually_finite_subsets_at_top by metis
  show ?thesis
  proof (intro exI conjI ballI)
    show "finite F" "F \<subseteq> M" by fact+
    fix x assume "x \<in> M - F"
    hence xM: "x \<in> M" and xF: "x \<notin> F" by auto
    have "sum f (insert x F) \<in> W"
      by (intro F) (use F xM in auto)
    moreover have "sum f F \<in> W"
      by (intro F) (use F in auto)
    ultimately have "sum f (insert x F) - sum f F \<in> X"
      by (rule W_sub)
    also have "sum f (insert x F) - sum f F = f x"
      using F(1) xF by simp
    finally show "f x \<in> X" .
  qed
qed
lemma has_setprod_imp_has_prod_nonzero:
  assumes \<open>(f has_setprod S) (UNIV :: nat set)\<close> and \<open>S \<noteq> 0\<close>
  shows   \<open>f has_prod S\<close>
proof -
  from assms(1) have \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_setprod_def)
  then have \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> S\<close>
  proof (rule filterlim_compose)
    show \<open>filterlim (\<lambda>n. {..n}) (finite_subsets_at_top UNIV) sequentially\<close>
      using filterlim_atMost_at_top by auto
  qed
  with \<open>S \<noteq> 0\<close> have \<open>raw_has_prod f 0 S\<close>
    by (simp add: raw_has_prod_def)
  then show \<open>f has_prod S\<close>
    by (simp add: has_prod_def)
qed

text \<open>
  Could the hypothesis \<^term>\<open>1 \<le> f x\<close> could be replaced by strong multipliability
  together with \<^term>\<open>0 \<le> f x\<close>?  It cannot: that statement is FALSE.  Take
  \<^term>\<open>A = (UNIV :: nat set)\<close> and \<^term>\<open>f = (\<lambda>k. 1 - 1 / 2 ^ (k + 2))\<close>.  Every factor is positive
  and $\sum_k 2^{-(k+2)}$ converges, so this \<^term>\<open>f\<close> is strongly multipliable with a positive
  value $L$; but every factor is smaller than $1$, so $L < 3/4 = $ \<^term>\<open>prod f {0}\<close> and the
  inequality goes the wrong way.  Factors below $1$ shrink the product, and monotonicity of the
  partial products is precisely what the conclusion needs.

  What can be weakened is where the hypothesis is required: only the factors OUTSIDE \<^term>\<open>F\<close>
  need to be at least $1$, those inside merely non-negative.  That covers a product with finitely
  many small factors, which is the case that occurs in practice.
\<close>
lemma finite_prod_le_infprod:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f multipliable_on A" "finite F" "F \<subseteq> A"
    and ge1: "\<And>x. x \<in> A - F \<Longrightarrow> 1 \<le> f x" and nonneg: "\<And>x. x \<in> F \<Longrightarrow> 0 \<le> f x"
  shows "prod f F \<le> infprod f A"
proof -
  have tendsto: "(prod f \<longlongrightarrow> infprod f A) (finite_subsets_at_top A)"
    using infprod_tendsto[OF assms(1)] .
  have "Limsup (finite_subsets_at_top A) (prod f) = infprod f A"
    using finite_subsets_at_top_neq_bot tendsto tendsto_iff_Liminf_eq_Limsup by blast
  moreover have "prod f F \<le> Limsup (finite_subsets_at_top A) (prod f)"
  proof (rule le_Limsup[OF finite_subsets_at_top_neq_bot])
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. ereal (prod f F) \<le> ereal (prod f X)"
      unfolding eventually_finite_subsets_at_top
    proof (intro exI conjI allI impI)
      show "finite F" by fact
      show "F \<subseteq> A" by fact
      fix Y assume "finite Y \<and> F \<subseteq> Y \<and> Y \<subseteq> A"
      then have Y: "finite Y" "F \<subseteq> Y" "Y \<subseteq> A" by auto
      have "prod f F \<le> prod f Y"
        using Y ge1 nonneg by (intro prod_mono2) auto
      thus "ereal (prod f F) \<le> ereal (prod f Y)"
        by simp
    qed
  qed
  ultimately show ?thesis by simp
qed


lemma abs_multipliable_on_iff_bdd_above:
  shows \<open>f abs_multipliable_on A \<longleftrightarrow> bdd_above (prod (\<lambda>x. 1 + norm (f x - 1)) ` {F. F\<subseteq>A \<and> finite F})\<close>
proof (rule iffI)
  assume asm: \<open>f abs_multipliable_on A\<close>
  then have mult: \<open>(\<lambda>x. 1 + norm (f x - 1)) multipliable_on A\<close>
    by (simp add: abs_multipliable_on_def)
  show \<open>bdd_above (prod (\<lambda>x. 1 + norm (f x - 1)) ` {F. F \<subseteq> A \<and> finite F})\<close>
  proof (rule bdd_aboveI2)
    fix F assume F: "F \<in> {F. F \<subseteq> A \<and> finite F}"
    then have "finite F" "F \<subseteq> A" by auto
    show "(\<Prod>x\<in>F. 1 + norm (f x - 1)) \<le> (\<Prod>\<^sub>\<infinity>x\<in>A. 1 + norm (f x - 1))"
      by (rule finite_prod_le_infprod[OF mult \<open>finite F\<close> \<open>F \<subseteq> A\<close>]) auto
  qed
next
  assume bdd: \<open>bdd_above (prod (\<lambda>x. 1 + norm (f x - 1)) ` {F. F\<subseteq>A \<and> finite F})\<close>
  show \<open>f abs_multipliable_on A\<close>
    unfolding abs_multipliable_on_def
  proof -
    define g where \<open>g x = 1 + norm (f x - 1)\<close> for x
    have g_ge1: \<open>g x \<ge> 1\<close> for x unfolding g_def by auto
    from bdd obtain C where C: \<open>prod g F \<le> C\<close> if \<open>F \<subseteq> A\<close> \<open>finite F\<close> for F
      unfolding bdd_above_def g_def by auto
    have g_ge0: \<open>g x \<ge> 0\<close> for x using g_ge1[of x] by linarith
    have mono: \<open>prod g F \<le> prod g G\<close> if \<open>F \<subseteq> G\<close> \<open>G \<subseteq> A\<close> \<open>finite G\<close> for F G
      using that g_ge1 g_ge0 by (intro prod_mono2) auto
    have \<open>(prod g \<longlongrightarrow> (SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F)) (finite_subsets_at_top A)\<close>
    proof (rule order_tendstoI)
      fix a :: real assume \<open>a < (SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F)\<close>
      then obtain F where F: \<open>F \<subseteq> A\<close> \<open>finite F\<close> \<open>a < prod g F\<close>
        using less_cSUP_iff[of \<open>{F. F \<subseteq> A \<and> finite F}\<close> \<open>prod g\<close> a]
          bdd[unfolded g_def[abs_def]]
        unfolding g_def by auto
      show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. a < prod g X\<close>
        unfolding eventually_finite_subsets_at_top
      proof (intro exI[of _ F] conjI allI impI)
        show \<open>finite F\<close> by fact
        show \<open>F \<subseteq> A\<close> by fact
        fix Y assume \<open>finite Y \<and> F \<subseteq> Y \<and> Y \<subseteq> A\<close>
        then show \<open>a < prod g Y\<close>
          using F(3) mono[of F Y] by auto
      qed
    next
      fix a :: real assume \<open>(SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F) < a\<close>
      show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. prod g X < a\<close>
        unfolding eventually_finite_subsets_at_top
      proof (intro exI[of _ "{}"] conjI allI impI)
        show \<open>finite {}\<close> by simp
        show \<open>{} \<subseteq> A\<close> by simp
        fix Y assume \<open>finite Y \<and> {} \<subseteq> Y \<and> Y \<subseteq> A\<close>
        then have \<open>prod g Y \<le> (SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F)\<close>
          using bdd
          by (intro cSUP_upper bdd[unfolded g_def[abs_def]]) (auto simp: g_def)
        also have \<open>\<dots> < a\<close> by fact
        finally show \<open>prod g Y < a\<close> .
      qed
    qed
    then have \<open>g multipliable_on A\<close>
      unfolding multipliable_on_def has_setprod_def by blast
    then show \<open>(\<lambda>x. 1 + norm (f x - 1)) multipliable_on A\<close>
      unfolding g_def .
  qed
qed

lemma multipliable_on_comparison_test:
  fixes f g :: "'b \<Rightarrow> real"
  assumes "f multipliable_on A" and "\<And>x. x \<in> A \<Longrightarrow> g x \<le> f x" and "\<And>x. x \<in> A \<Longrightarrow> 1 \<le> g x"
  shows   "g multipliable_on A"
proof -
  from assms(1) obtain S where S: "(prod f \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding multipliable_on_def has_setprod_def by blast
  have g_ge1: "1 \<le> g x" if "x \<in> A" for x
    using assms(3)[OF that] .
  have g_nonneg: "0 \<le> g x" if "x \<in> A" for x
    using g_ge1[OF that] by (meson dual_order.trans zero_le_one)
  have g_le_f_prod: "prod g X \<le> prod f X" if "X \<subseteq> A" "finite X" for X
  proof (rule prod_mono)
    fix i assume "i \<in> X"
    with that have "i \<in> A" by auto
    thus "0 \<le> g i \<and> g i \<le> f i"
      using g_nonneg assms(2) by auto
  qed
  have g_mono: "prod g X \<le> prod g Y" if "X \<subseteq> Y" "Y \<subseteq> A" "finite Y" for X Y
  proof (rule prod_mono2[OF \<open>finite Y\<close> \<open>X \<subseteq> Y\<close>])
    fix b assume "b \<in> Y - X"
    with that have "b \<in> A" by auto
    thus "1 \<le> g b" using g_ge1 by auto
  next
    fix a assume "a \<in> X"
    with that have "a \<in> A" by auto
    thus "0 \<le> g a" using g_nonneg by auto
  qed
  have f_bound: "\<exists>C. \<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> C"
  proof (cases "\<exists>C. C > S")
    case True
    then obtain C where C: "C > S" by blast
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X < C"
      using S C by (rule order_tendstoD)
    thus ?thesis
      by (meson eventually_mono nless_le)
  next
    case False thus ?thesis
      by (meson not_eventuallyD not_le_imp_less)
  qed
  then obtain C where C: "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> C"
    by blast
  from C obtain X0 where X0: "finite X0" "X0 \<subseteq> A"
    and X0_bound: "\<And>X. finite X \<Longrightarrow> X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> prod f X \<le> C"
    unfolding eventually_finite_subsets_at_top by auto
  have g_bdd: "prod g X \<le> C" if "finite X" "X \<subseteq> A" for X
  proof -
    have "prod g X \<le> prod g (X \<union> X0)"
      using that X0 by (intro g_mono) auto
    also have "\<dots> \<le> prod f (X \<union> X0)"
      using that X0 by (intro g_le_f_prod) auto
    also have "\<dots> \<le> C"
      using that X0 X0_bound[of "X \<union> X0"] by auto
    finally show ?thesis .
  qed
  hence bdd: "bdd_above (prod g ` {X. X \<subseteq> A \<and> finite X})"
    by (auto simp: bdd_above_def)
  show ?thesis unfolding multipliable_on_def has_setprod_def
  proof (rule exI, rule increasing_tendsto)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. prod g X \<le> Sup (prod g ` {X. X \<subseteq> A \<and> finite X})"
      by (intro eventually_finite_subsets_at_top_weakI cSUP_upper[OF _ bdd]) auto
  next
    fix y assume "y < Sup (prod g ` {X. X \<subseteq> A \<and> finite X})"
    then obtain X where X: "X \<subseteq> A" "finite X" "y < prod g X"
      by (subst (asm) less_cSUP_iff[OF _ bdd]) auto
    from X have "eventually (\<lambda>X'. X \<subseteq> X' \<and> X' \<subseteq> A \<and> finite X') (finite_subsets_at_top A)"
      by (auto simp: eventually_finite_subsets_at_top)
    thus "eventually (\<lambda>X'. y < prod g X') (finite_subsets_at_top A)"
    proof eventually_elim
      case (elim X')
      note \<open>y < prod g X\<close>
      also have "prod g X \<le> prod g X'"
        using elim by (intro g_mono) auto
      finally show ?case .
    qed
  qed
qed


lemma multipliable_on_imp_bdd_above_prods:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_semigroup_mult, linorder_topology, semidom, t2_space}"
  assumes f: "f multipliable_on A"
  shows   "\<exists>C. eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
proof -
  from assms obtain S where S: "(prod f \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding multipliable_on_def has_setprod_def by blast
  show ?thesis
  proof (cases "\<exists>C. C > S")
    case True
    then obtain C where C: "C > S"
      by blast
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X < C"
      using S C by (rule order_tendstoD(2))
    thus ?thesis
      by (meson eventually_mono nless_le)
  next
    case False thus ?thesis
      by (meson not_eventuallyD not_le_imp_less)
  qed
qed



context
  assumes "SORT_CONSTRAINT('a :: {topological_semigroup_mult, order_topology,
             conditionally_complete_linorder, linordered_idom, t2_space})"
begin

text \<open>
  Any family of non-negative numbers with bounded partial sums is multipliable, and the sum
  is simply the supremum of the partial sums.
\<close>
lemma ge_1_bdd_above_prods_imp_has_setprod_SUP:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (1::'a)"
      and bound:  "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
  shows   "(f has_setprod (SUP X\<in>{X. X \<subseteq> A \<and> finite X}. prod f X)) A"
proof -
  from bound obtain X0
    where X0: "X0 \<subseteq> A" "finite X0" "\<And>X. X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> prod f X \<le> C"
    by (force simp: eventually_finite_subsets_at_top)
  have bound': "prod f X \<le> C" if "X \<subseteq> A" "finite X" for X
  proof -
    have "prod f X \<le> prod f (X \<union> X0)"
      using that X0 assms(1) \<open>finite X0\<close>
      by (smt (verit, best) DiffE dual_order.trans finite_Un nle_le not_one_le_zero prod_mono2 subset_eq sup.bounded_iff)
    also have "\<dots> \<le> C"
      by (simp add: X0 that)
    finally show ?thesis .
  qed
  hence bdd: "bdd_above (prod f ` {X. X \<subseteq> A \<and> finite X})"
    by (auto simp: bdd_above_def)

  show ?thesis unfolding has_setprod_def
  proof (rule increasing_tendsto)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> Sup (prod f ` {X. X \<subseteq> A \<and> finite X})"
      by (intro eventually_finite_subsets_at_top_weakI cSUP_upper[OF _ bdd]) auto
  next
    fix y assume "y < Sup (prod f ` {X. X \<subseteq> A \<and> finite X})"
    then obtain X where X: "X \<subseteq> A" "finite X" "y < prod f X"
      by (subst (asm) less_cSUP_iff[OF _ bdd]) auto
    from X have "eventually (\<lambda>X'. X \<subseteq> X' \<and> X' \<subseteq> A \<and> finite X') (finite_subsets_at_top A)"
      by (auto simp: eventually_finite_subsets_at_top)
    thus "eventually (\<lambda>X'. y < prod f X') (finite_subsets_at_top A)"
    proof eventually_elim
      case (elim X')
      note \<open>y < prod f X\<close>
      also have "prod f X \<le> prod f X'"
        by (smt (verit) Diff_iff dual_order.trans elim nonneg prod_mono2 subset_iff zero_le_one)
      finally show ?case .
    qed
  qed
qed

lemma ge_1_bdd_above_prods_imp_multipliable_on:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (1::'a)"
      and bound:  "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
  shows   "f multipliable_on A"
  using ge_1_bdd_above_prods_imp_has_setprod_SUP[OF assms] by (auto simp: multipliable_on_def)

end

lemma abs_multipliable_on_iff_summable_on:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra_1}"
  shows "f abs_multipliable_on A \<longleftrightarrow> (\<lambda>n. norm (f n - 1)) summable_on A"
proof
  define g where \<open>g n = norm (f n - 1)\<close> for n
  have g_nn: \<open>g n \<ge> 0\<close> for n unfolding g_def by simp
  assume \<open>f abs_multipliable_on A\<close>
  then obtain L where lim: \<open>((\<lambda>F. \<Prod>x\<in>F. 1 + g x) \<longlongrightarrow> L) (finite_subsets_at_top A)\<close>
    unfolding abs_multipliable_on_def multipliable_on_def has_setprod_def g_def by blast
  show \<open>(\<lambda>n. norm (f n - 1)) summable_on A\<close>
    unfolding g_def[symmetric]
  proof (rule nonneg_bounded_partial_sums_imp_summable_on)
    show \<open>\<And>x. x \<in> A \<Longrightarrow> 0 \<le> g x\<close> using g_nn by simp
    from lim have \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. dist (prod (\<lambda>x. 1 + g x) X) L < 1\<close>
      unfolding tendsto_iff by auto
    then have \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. prod (\<lambda>x. 1 + g x) X < L + 1\<close>
      by (eventually_elim) (auto simp: dist_real_def)
    then show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. sum g X \<le> L + 1\<close>
    proof eventually_elim
      case (elim X)
      have \<open>sum g X \<le> prod (\<lambda>x. 1 + g x) X\<close>
        by (rule sum_le_prod) (use g_nn in auto)
      also have \<open>\<dots> < L + 1\<close> by (rule elim)
      finally show ?case by linarith
    qed
  qed
next
  define g where \<open>g n = norm (f n - 1)\<close> for n
  have g_nn: \<open>g n \<ge> 0\<close> for n unfolding g_def by simp
  assume \<open>(\<lambda>n. norm (f n - 1)) summable_on A\<close>
  then obtain L where lim: \<open>(sum g \<longlongrightarrow> L) (finite_subsets_at_top A)\<close>
    unfolding summable_on_def has_sum_def g_def by blast
  show \<open>f abs_multipliable_on A\<close>
    unfolding abs_multipliable_on_def g_def[symmetric]
  proof (rule ge_1_bdd_above_prods_imp_multipliable_on)
    show \<open>\<And>x. x \<in> A \<Longrightarrow> 1 \<le> (\<lambda>x. 1 + g x) x\<close> using g_nn by auto
    \<comment> \<open>Partial products are bounded by exp(L+1)\<close>
    from lim have \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. dist (sum g X) L < 1\<close>
      unfolding tendsto_iff by auto
    then have sum_bound: \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. sum g X < L + 1\<close>
      by (eventually_elim) (auto simp: dist_real_def)
    show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. prod (\<lambda>x. 1 + g x) X \<le> exp (L + 1)\<close>
      using sum_bound
    proof eventually_elim
      case (elim X)
      have \<open>prod (\<lambda>x. 1 + g x) X \<le> exp (sum g X)\<close>
        by (rule prod_le_exp_sum) (use g_nn in auto)
      also have \<open>\<dots> \<le> exp (L + 1)\<close>
        using elim by simp
      finally show ?case .
    qed
  qed
qed

text \<open>
  Absolute multipliability, unlike plain multipliability, does pass to arbitrary subsets without
  further ado -- it is just absolute summability of \<^term>\<open>\<lambda>x. norm (f x - 1)\<close> in disguise.
\<close>
lemma abs_multipliable_on_subset:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra_1}"
  assumes "f abs_multipliable_on A" and "B \<subseteq> A"
  shows   "f abs_multipliable_on B"
  using assms unfolding abs_multipliable_on_iff_summable_on
  by (rule summable_on_subset_banach)


lemma abs_multipliable_on_comparison_test:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, real_normed_algebra_1}\<close>
    and g :: \<open>'a \<Rightarrow> 'c::{banach, real_normed_algebra_1}\<close>
  assumes \<open>g abs_multipliable_on A\<close>
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> norm (f x - 1) \<le> norm (g x - 1)\<close>
  shows   \<open>f abs_multipliable_on A\<close>
proof -
  \<comment> \<open>Step 1: From g abs_multipliable, get that partial sums of @{term\<open>norm(g x - 1)\<close>} are bounded\<close>
  define gn where \<open>gn x = norm (g x - 1)\<close> for x
  define fn where \<open>fn x = norm (f x - 1)\<close> for x
  have gn_nn: \<open>gn x \<ge> 0\<close> for x unfolding gn_def by simp
  have fn_nn: \<open>fn x \<ge> 0\<close> for x unfolding fn_def by simp
  have fn_le_gn: \<open>fn x \<le> gn x\<close> if \<open>x \<in> A\<close> for x
    unfolding fn_def gn_def using assms(2)[OF that] by simp
  \<comment> \<open>The partial products of (1 + gn) converge\<close>
  from assms(1) have k_mult: \<open>(\<lambda>x. 1 + gn x) multipliable_on A\<close>
    unfolding abs_multipliable_on_def gn_def by simp
  from infprod_tendsto[OF k_mult]
  have k_tendsto: \<open>(prod (\<lambda>x. 1 + gn x) \<longlongrightarrow> infprod (\<lambda>x. 1 + gn x) A) (finite_subsets_at_top A)\<close> .
  \<comment> \<open>So partial products are eventually bounded\<close>
  from tendstoD[OF k_tendsto, of 1]
  have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. dist (prod (\<lambda>x. 1 + gn x) F) (infprod (\<lambda>x. 1 + gn x) A) < 1\<close>
    by simp
  then have prod_bound: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. prod (\<lambda>x. 1 + gn x) F < infprod (\<lambda>x. 1 + gn x) A + 1\<close>
    by (eventually_elim) (auto simp: dist_real_def)
  \<comment> \<open>Partial sums of gn are bounded by partial products\<close>
  have sum_bound: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum gn F \<le> infprod (\<lambda>x. 1 + gn x) A + 1\<close>
    using prod_bound
  proof eventually_elim
    case (elim F)
    have \<open>sum gn F \<le> prod (\<lambda>x. 1 + gn x) F\<close>
      by (rule sum_le_prod) (use gn_nn in auto)
    also have \<open>\<dots> < infprod (\<lambda>x. 1 + gn x) A + 1\<close> by (rule elim)
    finally show ?case by linarith
  qed
  \<comment> \<open>Step 2: gn is summable\<close>
  have gn_summable: \<open>gn summable_on A\<close>
    by (rule nonneg_bounded_partial_sums_imp_summable_on) (use gn_nn sum_bound in auto)
  \<comment> \<open>Step 3: fn is summable by comparison\<close>
  have fn_bound: \<open>\<exists>C. \<forall>\<^sub>F F in finite_subsets_at_top A. sum fn F \<le> C\<close>
  proof -
    from summable_on_imp_bounded_partial_sums[OF gn_summable]
    obtain C where C: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum gn F \<le> C\<close> by auto
    have FA: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. F \<subseteq> A\<close>
      by (auto simp: eventually_finite_subsets_at_top)
    from C FA have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum fn F \<le> C\<close>
    proof eventually_elim
      case (elim F)
      have \<open>sum fn F \<le> sum gn F\<close>
        by (intro sum_mono) (use fn_le_gn elim in auto)
      also have \<open>\<dots> \<le> C\<close> by (rule elim)
      finally show ?case .
    qed
    thus ?thesis by auto
  qed
  have fn_summable: \<open>fn summable_on A\<close>
    using fn_bound fn_nn
    by (auto intro!: nonneg_bounded_partial_sums_imp_summable_on)
  show \<open>f abs_multipliable_on A\<close>
    using fn_summable unfolding fn_def
    by (subst abs_multipliable_on_iff_summable_on)
qed

lemma abs_multipliable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "x abs_multipliable_on A"
    and y2_sum: "y abs_multipliable_on A"
  shows "(\<lambda>i. x i * y i) abs_multipliable_on A"
proof -
  define xn yn where "xn i = norm (x i - 1)" and "yn i = norm (y i - 1)" for i
  have xn_nn: "xn i \<ge> 0" for i unfolding xn_def by simp
  have yn_nn: "yn i \<ge> 0" for i unfolding yn_def by simp

  \<comment> \<open>Key inequality: 1 + norm(xy - 1) \<le> (1 + norm(x-1)) * (1 + norm(y-1))\<close>
  have prod_ineq: "1 + norm (x i * y i - 1) \<le> (1 + xn i) * (1 + yn i)" for i
  proof -
    have "x i * y i - 1 = (x i - 1) * (y i - 1) + (x i - 1) + (y i - 1)"
      by (simp add: algebra_simps)
    then have "norm (x i * y i - 1) \<le> norm ((x i - 1) * (y i - 1)) + norm (x i - 1) + norm (y i - 1)"
      by (metis dual_order.refl norm_triangle_mono)
    also have "\<dots> = xn i * yn i + xn i + yn i"
      by (simp add: norm_mult xn_def yn_def)
    finally have "1 + norm (x i * y i - 1) \<le> 1 + xn i * yn i + xn i + yn i"
      by linarith
    also have "\<dots> = (1 + xn i) * (1 + yn i)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  \<comment> \<open>From the assumptions, get that (1 + xn) and (1 + yn) are multipliable\<close>
  from x2_sum have xn_mult: "(\<lambda>i. 1 + xn i) multipliable_on A"
    unfolding abs_multipliable_on_def xn_def by simp
  from y2_sum have yn_mult: "(\<lambda>i. 1 + yn i) multipliable_on A"
    unfolding abs_multipliable_on_def yn_def by simp

  \<comment> \<open>Their pointwise product is multipliable\<close>
  have prod_mult: "(\<lambda>i. (1 + xn i) * (1 + yn i)) multipliable_on A"
    by (rule multipliable_on_mult[OF xn_mult yn_mult])
  show "(\<lambda>i. x i * y i) abs_multipliable_on A"
    unfolding abs_multipliable_on_def
  proof (rule multipliable_on_comparison_test[OF prod_mult])
    fix i assume "i \<in> A"
    show "1 + norm (x i * y i - 1) \<le> (1 + xn i) * (1 + yn i)"
      by (rule prod_ineq)
  next
    fix i assume "i \<in> A"
    show "(1::real) \<le> 1 + norm (x i * y i - 1)" by simp
  qed
qed

lemma abs_multipliable_on_inverse:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_field}"
  assumes "f abs_multipliable_on A" and nz: "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "(\<lambda>x. inverse (f x)) abs_multipliable_on A"
proof -
  have norm_sum: "(\<lambda>x. norm (f x - 1)) summable_on A"
    using assms(1) by (subst (asm) abs_multipliable_on_iff_summable_on)
  from summable_on_imp_nhds_0[OF norm_sum, of "ball 0 (1/2 :: real)"]
  obtain F where F_fin: "finite F" and F_sub: "F \<subseteq> A" 
    and F_small: "\<And>x. x \<in> A - F \<Longrightarrow> norm (f x - 1) \<in> ball 0 (1/2)"
    by auto
  have inv_bound: "norm (inverse (f x) - 1) \<le> 2 * norm (f x - 1)" if xSF: "x \<in> A - F" for x
  proof -
    have fx_nz: "f x \<noteq> 0" using xSF nz by auto
    have small: "norm (f x - 1) < 1/2" using F_small xSF by auto
    have "inverse (f x) - 1 = inverse (f x) * (1 - f x)"
      using fx_nz by (simp add: field_simps)
    hence "norm (inverse (f x) - 1) = norm (inverse (f x)) * norm (f x - 1)"
      by (simp add: norm_mult norm_minus_commute)
    moreover have "norm (inverse (f x)) \<le> 2"
    proof -
      have "norm (f x) \<ge> 1 - norm (f x - 1)"
        by (smt (verit, ccfv_SIG) norm_minus_commute norm_one norm_triangle_ineq2)
      hence "norm (f x) > 1/2" using small by linarith
      hence "norm (inverse (f x)) = inverse (norm (f x))"
        by (simp add: norm_inverse)
      also have "\<dots> \<le> 2" using \<open>norm (f x) > 1/2\<close>
        by (simp add: inverse_less_imp_less less_eq_real_def)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by (simp add: mult_right_mono)
  qed
  have "(\<lambda>x. norm (inverse (f x) - 1)) summable_on (A - F)"
  proof (rule summable_on_comparison_test)
    show "(\<lambda>x. 2 * norm (f x - 1)) summable_on (A - F)"
      using norm_sum F_sub F_fin summable_on_cmult_right summable_on_cofin_subset by blast
    fix x assume "x \<in> A - F"
    thus "norm (inverse (f x) - 1) \<le> 2 * norm (f x - 1)"
      using inv_bound by simp
  qed auto
  \<comment> \<open>Combine with finite part\<close>
  moreover have "(\<lambda>x. norm (inverse (f x) - 1)) summable_on F"
    using F_fin by simp
  ultimately have "(\<lambda>x. norm (inverse (f x) - 1)) summable_on (A - F \<union> F)"
    by (intro summable_on_Un_disjoint) auto
  also have "A - F \<union> F = A" using F_sub by auto
  finally show "(\<lambda>x. inverse (f x)) abs_multipliable_on A"
      by (subst abs_multipliable_on_iff_summable_on)
qed

text \<open>The types @{typ ennreal}, @{typ ereal}, and @{typ enat} cannot be used with the
  infinite-product framework (@{const multipliable_on}, @{const has_setprod}, @{const infprod})
  because it requires @{class semidom}, which demands additive cancellation.
  These types fail cancellation: e.g.\ @{term \<open>(\<infinity>::ennreal) + 1 = \<infinity> + 2\<close>} but @{term \<open>(1::ennreal) \<noteq> 2\<close>}.
  Supporting them would require weakening the type class constraints on the framework definitions.\<close>


(* The correct statement for products requires a nonzero limit (i.e. strongly_multipliable_on),
   since factors must tend to 1 by has_setprod_factors_tend_to_1. *)
lemma multipliable_countable:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {real_normed_div_algebra, semidom}\<close>
  assumes \<open>f strongly_multipliable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 1}\<close>
proof -
  have "\<exists>F. finite F \<and> F \<subseteq> A \<and> (\<forall>x\<in>A - F. f x \<in> ball 1 (1 / real (Suc n)))" for n
    using strongly_multipliable_on_imp_nhds_1[OF assms, of "ball 1 (1 / real (Suc n))"] by auto
  then obtain F where F_fin: "\<And>n. finite (F n)" and F_sub: "\<And>n. F n \<subseteq> A"
    and F_ball: "\<And>n x. x \<in> A - F n \<Longrightarrow> f x \<in> ball 1 (1 / real (Suc n))"
    by metis
  have "{x\<in>A. f x \<noteq> 1} \<subseteq> (\<Union>n. F n)"
  proof (rule subsetI)
    fix x assume "x \<in> {x\<in>A. f x \<noteq> 1}"
    hence "x \<in> A" "f x \<noteq> 1" by auto
    hence "dist (f x) 1 > 0" by auto
    then obtain n where "1 / real (Suc n) < dist (f x) 1"
      using reals_Archimedean[of "dist (f x) 1"]
      by (metis inverse_eq_divide)
    hence "f x \<notin> ball 1 (1 / real (Suc n))"
      by (simp add: dist_commute)
    hence "x \<notin> A - F n"
      using F_ball[of x n] by blast
    hence "x \<in> F n"
      using \<open>x \<in> A\<close> by auto
    thus "x \<in> (\<Union>n. F n)" by auto
  qed
  moreover have "countable (\<Union>n. F n)"
    using F_fin by (intro countable_UN) (auto intro: countable_finite)
  ultimately show ?thesis
    by (rule countable_subset)
qed

text \<open>
  Taking norms turns an unordered product into an unordered product of reals; this is the bridge
  to the real theory (and to \<open>strongly_multipliable_on_iff_abs_multipliable_on_real\<close>).
\<close>
lemma has_setprod_norm:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra, semidom}"
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>x. norm (f x)) has_setprod norm P) A"
proof -
  have "((\<lambda>X. norm (prod f X)) \<longlongrightarrow> norm P) (finite_subsets_at_top A)"
    using assms unfolding has_setprod_def by (intro tendsto_norm)
  moreover have "norm (prod f X) = (\<Prod>x\<in>X. norm (f x))" for X
    by (simp add: Real_Vector_Spaces.prod_norm)
  ultimately show ?thesis
    unfolding has_setprod_def by simp
qed

corollary multipliable_on_norm:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra, semidom}"
  assumes "f multipliable_on A"
  shows   "(\<lambda>x. norm (f x)) multipliable_on A"
  using assms has_setprod_norm has_setprod_imp_multipliable multipliable_on_def by blast

lemma prod_norm_le:
  fixes  f::"'b \<Rightarrow> 'a::real_normed_field"
  assumes "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  shows "norm (prod f S) \<le> prod g S"
  by (metis norm_ge_zero prod_mono prod_norm assms)

lemma norm_infprod_le:
  fixes  f::"'b \<Rightarrow> 'a::real_normed_field"
  assumes "(f has_setprod S) X"
  assumes "(g has_setprod T) X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> norm (f x) \<le> g x"
  shows   "norm S \<le> T"
proof (rule tendsto_le)
  show "((\<lambda>Y. norm (\<Prod>x\<in>Y. f x)) \<longlongrightarrow> norm S) (finite_subsets_at_top X)"
    using assms(1) unfolding has_setprod_def by (intro tendsto_norm)
  show "((\<lambda>Y. \<Prod>x\<in>Y. g x) \<longlongrightarrow> T) (finite_subsets_at_top X)"
    using assms(2) unfolding has_setprod_def .
  show "\<forall>\<^sub>F x in finite_subsets_at_top X. norm (prod f x) \<le> (\<Prod>x\<in>x. g x)"
    by (simp add: assms(3) eventually_finite_subsets_at_top_weakI in_mono prod_norm_le)
qed auto


lemma abs_multipliable_on_exp:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_field, banach}"
  assumes "f abs_summable_on A"
  shows   "(\<lambda>x. exp (f x)) abs_multipliable_on A"
  unfolding abs_multipliable_on_iff_summable_on
proof -
  obtain B where B: "finite B" "B \<subseteq> A" "\<forall>x\<in>A-B. f x \<in> ball 0 (1/2)"
    using summable_on_imp_nhds_0[OF abs_summable_summable[OF assms(1)], of "ball 0 (1/2)"] by auto
  have "(\<lambda>x. exp (f x) - 1) abs_summable_on (A-B)"
  proof (rule summable_on_comparison_test)
    show "(\<lambda>x. 3/2 * norm (f x)) summable_on (A - B)"
      by (intro summable_on_cmult_right summable_on_subset[OF assms]) auto
  next
    fix x assume x: "x \<in> A - B"
    have "norm (f x) \<le> 1 / 2"
      by (intro less_imp_le) (use B x in auto)
    thus "norm (exp (f x) - 1) \<le> 3/2 * norm (f x)"
      using norm_exp_bounds(2)[of "f x"] by simp
  qed auto
  hence "(\<lambda>x. exp (f x) - 1) abs_summable_on (A - B \<union> B)"
    by (intro summable_on_Un_disjoint) (use B in auto)
  also have "A - B \<union> B = A"
    using B by blast
  finally show "(\<lambda>x. exp (f x) - 1) abs_summable_on A" .
qed

lemma abs_multipliable_on_imp_strongly_multipliable_on:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_field}"
  assumes "f abs_multipliable_on A"
  shows   "f strongly_multipliable_on A"
proof -
  \<comment> \<open>Step 1: norm(f x - 1) is summable\<close>
  have norm_sum: "(\<lambda>x. norm (f x - 1)) summable_on A"
    using assms by (subst (asm) abs_multipliable_on_iff_summable_on)
  \<comment> \<open>Step 2: Only finitely many zeros\<close>
  have fin_zeros: "finite {x\<in>A. f x = 0}"
  proof -
    from summable_on_imp_nhds_0[OF abs_summable_summable[OF norm_sum], of "ball 0 (1::real)"]
    obtain F where F: "finite F" "F \<subseteq> A" "\<forall>x\<in>A - F. norm (f x - 1) \<in> ball 0 1"
      by auto
    show ?thesis
      by (rule finite_subset[OF _ F(1)]) (use F(3) in force)
  qed
  \<comment> \<open>Step 3: f is abs_multipliable on the nonzero part\<close>
  define S where "S = {x\<in>A. f x \<noteq> 0}"
  have S_sub: "S \<subseteq> A" unfolding S_def by auto
  have nz: "\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> 0" unfolding S_def by auto
  have norm_sum_S: "(\<lambda>x. norm (f x - 1)) summable_on S"
    using norm_sum S_sub by (rule summable_on_subset_banach)
  have abs_mult_S: "f abs_multipliable_on S"
    using norm_sum_S by (subst abs_multipliable_on_iff_summable_on)
  \<comment> \<open>Step 4: f is multipliable on S\<close>
  have mult_S: "f multipliable_on S"
    by (rule abs_multipliable_multipliable[OF abs_mult_S])
  \<comment> \<open>Step 5: The inverse is also abs_multipliable on S\<close>
  have inv_abs_mult_S: "(\<lambda>x. inverse (f x)) abs_multipliable_on S"
    by (rule abs_multipliable_on_inverse) fact+
  \<comment> \<open>Step 6: The product over S is nonzero\<close>
  have inv_mult_S: "(\<lambda>x. inverse (f x)) multipliable_on S"
    by (rule abs_multipliable_multipliable[OF inv_abs_mult_S])
  have "infprod (\<lambda>x. f x * inverse (f x)) S = infprod f S * infprod (\<lambda>x. inverse (f x)) S"
    by (rule infprod_mult[OF mult_S inv_mult_S])
  moreover have "infprod (\<lambda>x. f x * inverse (f x)) S = 1"
    by (intro infprod_1) (use nz in auto)
  ultimately have prod_nz: "infprod f S \<noteq> 0"
    by (metis mult_zero_left zero_neq_one)
  \<comment> \<open>Conclusion\<close>
  from mult_S prod_nz obtain P where "(f has_setprod P) S" "P \<noteq> 0"
    using has_setprod_infprod multipliable_on_def by fastforce
  with fin_zeros show ?thesis
    unfolding strongly_multipliable_on_def S_def by blast
qed


lemma multipliable_on_union:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_field, complete_space}"
  assumes "f multipliable_on A" "f multipliable_on B"
  shows "f multipliable_on (A \<union> B)"
proof (cases "\<exists>x\<in>A \<union> B. f x = 0")
  case True
  then obtain x where "x \<in> A \<union> B" "f x = 0" by auto
  then show ?thesis
    unfolding multipliable_on_def using zero_imp_has_setprod_0
    by metis
next
  case False
  hence nz: "\<And>x. x \<in> A \<union> B \<Longrightarrow> f x \<noteq> 0" by auto
  from assms(2) obtain T where T: "(f has_setprod T) B"
    using multipliable_on_def by blast
  show ?thesis
  proof (cases "T = 0")
    case False
    \<comment> \<open>the product over \<^term>\<open>B\<close> is non-zero, so it restricts to \<^term>\<open>B - A\<close>\<close>
    then obtain P where "(f has_setprod P) (B - A)"
      using has_setprod_subset_nonzero[OF T] by blast
    then have "f multipliable_on (B - A)"
      by (rule has_setprod_imp_multipliable)
    then show ?thesis
      using assms(1)
      by (metis Diff_disjoint Un_Diff_cancel multipliable_on_Un_disjoint)
  next
    case True
    \<comment> \<open>the product over \<^term>\<open>B\<close> is \<open>0\<close>; since the partial products over \<^term>\<open>A\<close> are
        bounded, the product over \<^term>\<open>A \<union> B\<close> is \<open>0\<close> as well\<close>
    have limA: "(prod f \<longlongrightarrow> infprod f A) (finite_subsets_at_top A)"
      using has_setprod_infprod[OF assms(1)] by (simp add: has_setprod_def)
    obtain C where C: "C > 0"
      and Cbd: "\<And>Y. finite Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> norm (prod f Y) \<le> C"
      using multipliable_on_imp_bdd_prods[OF limA] nz by blast
    have "(f has_setprod 0) (A \<union> B)"
      unfolding has_setprod_def
    proof (rule tendstoI)
      fix e :: real assume "e > 0"
      with C have eC: "e / C > 0" by simp
      from T True have "(prod f \<longlongrightarrow> 0) (finite_subsets_at_top B)"
        by (simp add: has_setprod_def)
      from tendstoD[OF this eC] obtain W where W: "finite W" "W \<subseteq> B"
        and Wclose: "\<And>Y. finite Y \<Longrightarrow> W \<subseteq> Y \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> dist (prod f Y) 0 < e / C"
        unfolding eventually_finite_subsets_at_top by metis
      show "\<forall>\<^sub>F X in finite_subsets_at_top (A \<union> B). dist (prod f X) 0 < e"
        unfolding eventually_finite_subsets_at_top
      proof (intro exI[of _ W] conjI allI impI)
        show "finite W" "W \<subseteq> A \<union> B" using W by auto
        fix X assume X: "finite X \<and> W \<subseteq> X \<and> X \<subseteq> A \<union> B"
        hence Xf: "finite X" and WX: "W \<subseteq> X" and XAB: "X \<subseteq> A \<union> B" by auto
        have XB: "X - B \<subseteq> A"
          using XAB by blast
        have "prod f X = prod f (X \<inter> B) * prod f (X - B)"
          using Xf by (rule prod.Int_Diff)
        hence "norm (prod f X) = norm (prod f (X \<inter> B)) * norm (prod f (X - B))"
          by (simp add: norm_mult)
        also have "\<dots> < e / C * C"
        proof (rule mult_less_le_imp_less)
          show "norm (prod f (X \<inter> B)) < e / C"
            using Wclose[of "X \<inter> B"] Xf WX W by (auto simp: dist_norm)
          show "norm (prod f (X - B)) \<le> C"
            using Cbd[of "X - B"] Xf XB by auto
          show "0 \<le> norm (prod f (X \<inter> B))" by simp
          show "0 < norm (prod f (X - B))"
            using Xf XB nz by (auto simp: prod_norm intro!: prod_pos)
        qed
        also have "\<dots> = e"
          using C by simp
        finally show "dist (prod f X) 0 < e"
          by simp
      qed
    qed
    thus ?thesis
      by (rule has_setprod_imp_multipliable)
  qed
qed


lemma multipliable_on_insert_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_field, complete_space}"
  assumes "f x \<noteq> 0"
  shows "f multipliable_on insert x A \<longleftrightarrow> f multipliable_on A"
proof
  assume "f multipliable_on A"
  then show "f multipliable_on insert x A"
    using multipliable_on_union[of f A "{x}"] by simp
next
  assume *: "f multipliable_on insert x A"
  show "f multipliable_on A"
  proof (rule multipliable_on_subset_finite_Diff[OF *])
    show "A \<subseteq> insert x A" by auto
    show "finite (insert x A - A)"
      by (rule finite_subset[of _ "{x}"]) auto
    fix y assume "y \<in> insert x A - A"
    hence "y = x" by auto
    with assms show "f y \<noteq> 0" by simp
  qed
qed

lemma has_setprod_finiteI: "finite A \<Longrightarrow> S = prod f A \<Longrightarrow> (f has_setprod S) A"
  by simp

lemma has_setprod_insert:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_comm_monoid_mult, semidom, t2_space}"
  assumes "x \<notin> A" and "(f has_setprod S) A"
  shows   "(f has_setprod (f x * S)) (insert x A)"
proof -
  have "(f has_setprod (f x * S)) ({x} \<union> A)"
    using assms by (intro has_setprod_Un_disjoint) (auto intro: has_setprod_finiteI)
  thus ?thesis by simp
qed

lemma infprod_insert:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_mult, semidom, t2_space}"
  assumes "f multipliable_on A" "a \<notin> A"
  shows   "infprod f (insert a A) = f a * infprod f A"
  by (meson assms has_setprod_insert infprodI multipliable_iff_has_setprod_infprod)

text \<open>
  Restricting a product to one fibre again needs a non-zero product: for a family that is merely
  multipliable this fails, even when all the factors off the fibre are non-zero.  (Take
  \<^term>\<open>A = {True, False}\<close>, both fibres \<^term>\<open>UNIV :: nat set\<close>, \<open>f True b = -1\<close> and
  \<open>f False b = 1/2\<close>: the whole family is multipliable with product \<open>0\<close>, but the fibre over
  \<^term>\<open>True\<close> is not multipliable.)
\<close>
lemma multipliable_on_SigmaD1:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {real_normed_field, complete_space}"
  assumes f: "(\<lambda>(x,y). f x y) strongly_multipliable_on Sigma A B"
  assumes x: "x \<in> A"
  shows   "f x multipliable_on B x"
proof -
  have "Sigma {x} B \<subseteq> Sigma A B"
    using x by auto
  from strongly_multipliable_on_subset[OF f this]
  have step1: "(\<lambda>(x,y). f x y) multipliable_on Sigma {x} B"
    by (rule strongly_multipliable_imp_multipliable)
  have step2: "(\<lambda>y. f x y) \<circ> snd multipliable_on Sigma {x} B"
    using step1 multipliable_on_cong[of "Sigma {x} B" "\<lambda>(a,b). f a b" "(\<lambda>y. f x y) \<circ> snd"]
    by auto
  have inj: "inj_on snd (Sigma {x} B)"
    by (auto intro!: inj_onI simp: Sigma_def)
  have step3: "(\<lambda>y. f x y) multipliable_on snd ` Sigma {x} B"
    using step2 multipliable_on_reindex[OF inj, of "\<lambda>y. f x y"] by simp
  have "snd ` Sigma {x} B = B x"
    by (force simp: Sigma_def)
  with step3 show ?thesis by simp
qed

lemma has_setprod_swap:
  "(f has_setprod S) (A \<times> B) \<longleftrightarrow> ((\<lambda>(x,y). f (y,x)) has_setprod S) (B \<times> A)"
proof -
  have "bij_betw (\<lambda>(x,y). (y,x)) (B \<times> A) (A \<times> B)"
    by (rule bij_betwI[of _ _ _ "\<lambda>(x,y). (y,x)"]) auto
  from has_setprod_reindex_bij_betw[OF this, where f = f] show ?thesis
    by (simp add: case_prod_unfold)
qed


lemma multipliable_on_swap:
  "f multipliable_on (A \<times> B) \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) multipliable_on (B \<times> A)"
  by (metis has_setprod_swap multipliable_on_def)

text \<open>
  \<^bold>\<open>Not\<close> lemmas.  For \<^term>\<open>c \<noteq> 0\<close>, neither
  \<open>((\<lambda>x. c * f x) has_setprod S) A\<close> nor \<open>((\<lambda>x. f x * c) has_setprod S) A\<close> is
  equivalent to \<open>(f has_setprod S / c) A\<close>: scaling every factor scales the product by
  \<^term>\<open>c ^ card A\<close>, not by \<^term>\<open>c\<close>.  Counterexample: for \<^term>\<open>A = {1, 2 :: nat}\<close>,
  \<^term>\<open>f = (\<lambda>_. 1 :: real)\<close> and \<^term>\<open>c = (2 :: real)\<close> the scaled product is $4$,
  while the product of \<^term>\<open>f\<close> is $1$ and \<^term>\<open>S / c\<close> is $2$.
\<close>

lemma finite_nonzero_values_imp_multipliable_on:
  assumes "finite {x\<in>X. f x \<noteq> 0}"
  shows   "f multipliable_on X"
proof (cases "finite X")
  case True
  then show ?thesis by simp
next
  case False
  then have "X - {x\<in>X. f x \<noteq> 0} \<noteq> {}"
    using assms by (metis Collect_mem_eq Diff_eq_empty_iff finite_subset subset_refl)
  then obtain x where "x \<in> X" "f x = 0" by auto
  then have "(f has_setprod 0) X"
    by (rule zero_imp_has_setprod_0)
  then show ?thesis
    unfolding multipliable_on_def by blast
qed

lemma multipliable_on_of_int_iff:
  "(\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1, topological_semigroup_mult, semidom}) multipliable_on A \<longleftrightarrow> f multipliable_on A"
proof
  assume "f multipliable_on A"
  thus "(\<lambda>x. of_int (f x)) multipliable_on A"
    by (rule multipliable_on_homomorphism) auto
next
  assume "(\<lambda>x. of_int (f x) :: 'b) multipliable_on A"
  then obtain S where "((\<lambda>x. of_int (f x) :: 'b) has_setprod S) A"
    by (auto simp: multipliable_on_def)
  hence "(prod (\<lambda>x. of_int (f x) :: 'b) \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding has_setprod_def .
  moreover have "1/2 > (0 :: real)"
    by auto
  ultimately have "eventually (\<lambda>X. dist (prod (\<lambda>x. of_int (f x) :: 'b) X) S < 1/2)
                     (finite_subsets_at_top A)"
    unfolding tendsto_iff by blast
  then obtain X where X: "finite X" "X \<subseteq> A"
     "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> dist (prod (\<lambda>x. of_int (f x)) Y) S < 1/2"
    unfolding eventually_finite_subsets_at_top by metis

  have "prod f Y = prod f X" if "finite Y" "X \<subseteq> Y" "Y \<subseteq> A" for Y
  proof -
    have "dist (prod (\<lambda>x. of_int (f x)) X) S < 1/2"
      by (intro X) auto
    moreover have "dist (prod (\<lambda>x. of_int (f x)) Y) S < 1/2"
      by (intro X that)
    ultimately have "dist (prod (\<lambda>x. of_int (f x)) X) (prod (\<lambda>x. of_int (f x) :: 'b) Y) <
                       1/2 + 1/2"
      using dist_triangle_less_add by blast
    have eq: "of_int (prod f X) = (of_int (prod f Y) :: 'b)"
    proof (rule ccontr)
      assume "of_int (prod f X) \<noteq> (of_int (prod f Y) :: 'b)"
      hence "prod f X \<noteq> prod f Y" by auto
      hence "abs (prod f X - prod f Y) \<ge> 1" 
        by (simp del: of_int_prod of_nat_prod)
      hence "norm (of_int (prod f X - prod f Y) :: 'b) \<ge> 1"
        by (simp add: norm_of_int del: of_int_prod of_nat_prod of_int_diff)
      hence "norm (of_int (prod f X) - (of_int (prod f Y) :: 'b)) \<ge> 1"
        by (simp add: of_int_diff)
      moreover have "(of_int (prod f X) :: 'b) = prod (\<lambda>x. of_int (f x)) X"
        using X(1) by (induction X rule: finite_induct) (auto simp: of_int_mult)
      moreover have "(of_int (prod f Y) :: 'b) = prod (\<lambda>x. of_int (f x)) Y"
        using that(1) by (induction Y rule: finite_induct) (auto simp: of_int_mult)
      ultimately show False
        using \<open>dist (prod (\<lambda>x. of_int (f x)) X) (prod (\<lambda>x. of_int (f x) :: 'b) Y) < 1/2 + 1/2\<close>
        by (simp add: dist_norm)
    qed
    thus ?thesis 
      using eq by (simp add: of_int_eq_iff del: of_int_prod of_nat_prod)
  qed
  have "(prod f \<longlongrightarrow> prod f X) (finite_subsets_at_top A)"
  proof (rule tendsto_eventually)
    show "\<forall>\<^sub>F Y in finite_subsets_at_top A. prod f Y = prod f X"
      unfolding eventually_finite_subsets_at_top
      using X(1,2) \<open>\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y = prod f X\<close>
      by blast
  qed
  thus "f multipliable_on A"
    unfolding multipliable_on_def has_setprod_def by blast
qed

lemma multipliable_on_of_nat_iff:
  "(\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) multipliable_on A \<longleftrightarrow> f multipliable_on A"
proof
  assume "f multipliable_on A"
  thus "(\<lambda>x. of_nat (f x) :: 'b) multipliable_on A"
    by (rule multipliable_on_homomorphism) auto
next
  assume "(\<lambda>x. of_nat (f x) :: 'b) multipliable_on A"
  hence "(\<lambda>x. of_int (int (f x)) :: 'b) multipliable_on A"
    by simp
  also have "?this \<longleftrightarrow> (\<lambda>x. int (f x)) multipliable_on A"
    by (rule multipliable_on_of_int_iff)
  also have "\<dots> \<longleftrightarrow> f multipliable_on A"
  proof
    have prod_int: "prod (\<lambda>x. int (f x)) X = int (prod f X)" if "finite X" for X
      using that by (induction X rule: finite_induct) auto
    show "(\<lambda>x. int (f x)) multipliable_on A \<Longrightarrow> f multipliable_on A"
    proof -
      assume "(\<lambda>x. int (f x)) multipliable_on A"
      then obtain S where lim: "(prod (\<lambda>x. int (f x)) \<longlongrightarrow> S) (finite_subsets_at_top A)"
        by (auto simp: multipliable_on_def has_setprod_def)
      have "\<forall>\<^sub>F X in finite_subsets_at_top A. prod (\<lambda>x. int (f x)) X = S"
        using lim by (simp add: tendsto_discrete)
      then obtain X where X: "finite X" "X \<subseteq> A"
        "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod (\<lambda>x. int (f x)) Y = S"
        unfolding eventually_finite_subsets_at_top by metis
      have "prod f Y = prod f X" if "finite Y" "X \<subseteq> Y" "Y \<subseteq> A" for Y
      proof -
        have "int (prod f X) = prod (\<lambda>x. int (f x)) X"
          using prod_int[OF X(1)] by simp
        also have "\<dots> = S" by (rule X(3)) (use X in auto)
        also have "\<dots> = prod (\<lambda>x. int (f x)) Y" by (rule X(3)[symmetric]) (use that in auto)
        also have "\<dots> = int (prod f Y)"
          using prod_int[OF that(1)] by simp
        finally show ?thesis by presburger
      qed
      hence "(prod f \<longlongrightarrow> prod f X) (finite_subsets_at_top A)"
        by (intro tendsto_eventually)
           (auto simp: eventually_finite_subsets_at_top intro!: exI[of _ X] X(1,2))
      thus "f multipliable_on A"
        unfolding multipliable_on_def has_setprod_def by blast
    qed
    show "f multipliable_on A \<Longrightarrow> (\<lambda>x. int (f x)) multipliable_on A"
      by (rule multipliable_on_homomorphism) auto
  qed
  finally show "f multipliable_on A" .
qed

lemma infprod_of_nat:
  "infprod (\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) A = of_nat (infprod f A)"
  by (metis has_setprod_empty has_setprod_infprod has_setprod_of_nat infprodI infprod_def
      multipliable_on_of_nat_iff)

lemma infprod_of_int:
  "infprod (\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) A = of_int (infprod f A)"
  by (metis has_setprod_infprod has_setprod_of_int infprodI infprod_not_exists
      multipliable_on_of_int_iff of_int_1)

text \<open>
  The \<open>has_setprod\<close> forms of the two lemmas above.  \<open>has_setprod_of_nat\<close> and \<open>has_setprod_of_int\<close>
  only go one way; here the embedded product converges only for an embedded value, and only when
  the original product converges to it.
\<close>
lemma has_setprod_of_nat_iff:
  "((\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult})
      has_setprod S) A \<longleftrightarrow> (\<exists>S'. S = of_nat S' \<and> (f has_setprod S') A)"
proof
  assume *: "((\<lambda>x. of_nat (f x) :: 'b) has_setprod S) A"
  hence "f multipliable_on A"
    using has_setprod_imp_multipliable multipliable_on_of_nat_iff by blast
  hence "(f has_setprod infprod f A) A"
    by (rule has_setprod_infprod)
  moreover from this have "S = of_nat (infprod f A)"
    using * has_setprod_of_nat has_setprod_unique by blast
  ultimately show "\<exists>S'. S = of_nat S' \<and> (f has_setprod S') A"
    by blast
qed (use has_setprod_of_nat in blast)

lemma has_setprod_of_int_iff:
  "((\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult})
      has_setprod S) A \<longleftrightarrow> (\<exists>S'. S = of_int S' \<and> (f has_setprod S') A)"
proof
  assume *: "((\<lambda>x. of_int (f x) :: 'b) has_setprod S) A"
  hence "f multipliable_on A"
    using has_setprod_imp_multipliable multipliable_on_of_int_iff by blast
  hence "(f has_setprod infprod f A) A"
    by (rule has_setprod_infprod)
  moreover from this have "S = of_int (infprod f A)"
    using * has_setprod_of_int has_setprod_unique by blast
  ultimately show "\<exists>S'. S = of_int S' \<and> (f has_setprod S') A"
    by blast
qed (use has_setprod_of_int in blast)


text \<open>
  \<^bold>\<open>Fubini for absolute multipliability.\<close>  The criterion below replaces an earlier
  \<open>multipliable_on_SigmaI\<close> whose hypotheses were \<^term>\<open>f (x, y) \<ge> 1\<close> together with the order
  classes \<^class>\<open>conditionally_complete_linorder\<close> and \<^class>\<open>linordered_idom\<close>.  Those were not
  arbitrary -- they are the multiplicative transcription of the library's own
  \<open>summable_on_SigmaI\<close>, which assumes \<^term>\<open>f (x, y) \<ge> 0\<close> and proves summability through a
  supremum -- but products admit a route that sums do not: absolute multipliability is
  \<^emph>\<open>summability of the norms of the deviations from\<close> \<open>1\<close> (\<open>abs_multipliable_on_iff_summable_on\<close>),
  so the whole question can be handed to \<open>abs_summable_on_Sigma_iff\<close> in
  \<^theory>\<open>HOL-Analysis.Infinite_Sum\<close>.  That needs no order at all, only a Banach algebra, and it
  gives an iff rather than one implication.

  Nothing is lost over the reals: for a family with \<^term>\<open>f x \<ge> 1\<close> one has
  \<^term>\<open>1 + norm (f x - 1) = f x\<close>, so multipliability and absolute multipliability coincide there.
  The hypotheses have a different shape, though -- summability of the fibre sums
  \<^term>\<open>\<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y) - 1)\<close> in place of multipliability of the fibre products -- and
  the equivalence of the two shapes is not proved here.
\<close>
lemma abs_multipliable_on_Sigma_iff:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: {banach, real_normed_algebra_1}"
  shows "f abs_multipliable_on Sigma A B \<longleftrightarrow>
           (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_multipliable_on B x) \<and>
           ((\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y) - 1)) summable_on A)"
  \<comment> \<open>\<^bold>\<open>NB\<close> \<open>summable_on_iff_abs_summable_on_real\<close> must never be given to the simplifier: it
      rewrites \<open>f summable_on A\<close> to \<open>(\<lambda>x. norm (f x)) summable_on A\<close>, which matches itself again.
      Hence the explicit calculation below.\<close>
proof -
  define g where "g = (\<lambda>p. norm (f p - 1))"
  have nn: "g p \<ge> 0" for p
    by (simp add: g_def)
  have norm_g: "norm (g p) = g p" for p
    using nn by simp
  have "f abs_multipliable_on Sigma A B \<longleftrightarrow> g summable_on Sigma A B"
    unfolding g_def by (rule abs_multipliable_on_iff_summable_on)
  also have "\<dots> \<longleftrightarrow> g abs_summable_on Sigma A B"
    by (rule summable_on_iff_abs_summable_on_real)
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>A. (\<lambda>y. g (x, y)) abs_summable_on B x) \<and>
                    ((\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (g (x, y))) abs_summable_on A)"
    by (rule Infinite_Sum.abs_summable_on_Sigma_iff)
  \<comment> \<open>drop the norms: \<^term>\<open>g\<close> is non-negative.  \<open>norm_g\<close> reaches inside the fibre component, whose
      norm sits on \<^term>\<open>g\<close>, but not the outer one, whose norm sits on the fibre \<^emph>\<open>sum\<close>\<close>
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>A. (\<lambda>y. g (x, y)) summable_on B x) \<and>
                    ((\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. g (x, y)) summable_on A)"
  proof -
    have "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. g (x, y)) abs_summable_on A
            \<longleftrightarrow> (\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. g (x, y)) summable_on A"
      by (rule summable_on_iff_abs_summable_on_real[symmetric])
    thus ?thesis
      unfolding norm_g by blast
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_multipliable_on B x) \<and>
                    ((\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y) - 1)) summable_on A)"
    by (simp add: abs_multipliable_on_iff_summable_on g_def)
  finally show ?thesis .
qed

corollary abs_multipliable_on_SigmaI:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: {banach, real_normed_algebra_1}"
  assumes "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) abs_multipliable_on B x"
    and "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y) - 1)) summable_on A"
  shows   "f abs_multipliable_on Sigma A B"
  using assms by (simp add: abs_multipliable_on_Sigma_iff)

corollary multipliable_on_SigmaI:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: {banach, real_normed_field}"
  assumes "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) abs_multipliable_on B x"
    and "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y) - 1)) summable_on A"
  shows   "f multipliable_on Sigma A B"
  using abs_multipliable_on_SigmaI[OF assms]
  by (blast intro: strongly_multipliable_imp_multipliable
                   abs_multipliable_on_imp_strongly_multipliable_on)

corollary abs_multipliable_on_UnionI:
  fixes f :: "'b \<Rightarrow> 'c :: {banach, real_normed_algebra_1}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> f abs_multipliable_on B x"
    and sum: "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f y - 1)) summable_on A"
    and disj: "disjoint_family_on B A"
  shows   "f abs_multipliable_on (\<Union>x\<in>A. B x)"
proof -
  have "(f \<circ> snd) abs_multipliable_on Sigma A B"
    using f sum by (intro abs_multipliable_on_SigmaI) auto
  also have "?this \<longleftrightarrow> f abs_multipliable_on (snd ` Sigma A B)"
    unfolding abs_multipliable_on_def o_def using disj
    by (subst multipliable_on_reindex[where h = snd, unfolded o_def];
        force simp: disjoint_family_on_def inj_on_def)
  also have "snd ` Sigma A B = (\<Union>x\<in>A. B x)"
    by force
  finally show ?thesis .
qed

corollary multipliable_on_UnionI:
  fixes f :: "'b \<Rightarrow> 'c :: {banach, real_normed_field}"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f abs_multipliable_on B x"
    and "(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f y - 1)) summable_on A"
    and "disjoint_family_on B A"
  shows   "f multipliable_on (\<Union>x\<in>A. B x)"
  using abs_multipliable_on_UnionI[OF assms]
  by (blast intro: strongly_multipliable_imp_multipliable
                   abs_multipliable_on_imp_strongly_multipliable_on)

lemma multipliable_on_SigmaD:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: real_normed_field"
  assumes sum1: "f multipliable_on (Sigma A B)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) multipliable_on (B x)"
  shows   "(\<lambda>x. infprod (\<lambda>y. f (x, y)) (B x)) multipliable_on A"
  using assms unfolding multipliable_on_def
  by (smt (verit, del_insts) assms has_setprod_Sigma has_setprod_cong has_setprod_infprod)

lemma multipliable_on_UnionD:
  fixes f :: "'a \<Rightarrow> 'c :: real_normed_field"
  assumes sum1: "f multipliable_on (\<Union>x\<in>A. B x)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> f multipliable_on (B x)"
  assumes disj: "disjoint_family_on B A"
  shows   "(\<lambda>x. infprod f (B x)) multipliable_on A"
proof -
  have "(\<Union>x\<in>A. B x) = snd ` Sigma A B"
    by (force simp: Sigma_def)
  with sum1 have "f multipliable_on (snd ` Sigma A B)"
    by simp
  also have "?this \<longleftrightarrow> (f \<circ> snd) multipliable_on (Sigma A B)"
    using disj by (intro multipliable_on_reindex inj_onI) (force simp: disjoint_family_on_def)
  finally show "(\<lambda>x. infprod f (B x)) multipliable_on A"
    using multipliable_on_SigmaD[of "f \<circ> snd" A B] sum2 by simp
qed

text \<open>
  \<^bold>\<open>NOTE.\<close>  The next lemma is about sums, not products, and belongs in
  \<^theory>\<open>HOL-Analysis.Infinite_Sum\<close>.  It is the Weierstrass \<open>M\<close>-test for \<^emph>\<open>unordered\<close> sums in its
  uniform form: a family dominated by a summable \<^term>\<open>M\<close> converges uniformly on \<^term>\<open>B\<close> along
  \<^term>\<open>finite_subsets_at_top A\<close>.  It is proved here because that is where it was needed.
\<close>
lemma uniform_limit_infsum_M_test:
  fixes h :: "'k \<Rightarrow> 'a \<Rightarrow> real"
  assumes le: "\<And>k y. k \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> h k y \<le> M k"
    and nn: "\<And>k y. k \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> 0 \<le> h k y"
    and M: "M summable_on A"
  shows "uniform_limit B (\<lambda>X y. \<Sum>k\<in>X. h k y) (\<lambda>y. \<Sum>\<^sub>\<infinity>k\<in>A. h k y) (finite_subsets_at_top A)"
proof (cases "B = {}")
  case True
  thus ?thesis
    by simp
next
  case False
  then obtain y0 where y0: "y0 \<in> B" by blast
  have Mnn: "0 \<le> M k" if "k \<in> A" for k
    using nn[OF that y0] le[OF that y0] by linarith
  have summ: "(\<lambda>k. h k y) summable_on A" if "y \<in> B" for y
    using M by (rule summable_on_comparison_test) (use le nn that in auto)
  have summ_sub: "(\<lambda>k. h k y) summable_on A'" if "y \<in> B" "A' \<subseteq> A" for y A'
    using summ[OF that(1)] that(2) by (rule summable_on_subset_banach)
  have M_sub: "M summable_on A'" if "A' \<subseteq> A" for A'
    using M that by (rule summable_on_subset_banach)
  \<comment> \<open>splitting off a finite part of the index set\<close>
  have split: "(\<Sum>\<^sub>\<infinity>k\<in>A. h k y) = (\<Sum>k\<in>X. h k y) + (\<Sum>\<^sub>\<infinity>k\<in>A-X. h k y)"
    if "y \<in> B" "finite X" "X \<subseteq> A" for y X
  proof -
    have "A = X \<union> (A - X)"
      using that by auto
    hence "(\<Sum>\<^sub>\<infinity>k\<in>A. h k y) = (\<Sum>\<^sub>\<infinity>k\<in>X \<union> (A - X). h k y)"
      by simp
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>k\<in>X. h k y) + (\<Sum>\<^sub>\<infinity>k\<in>A-X. h k y)"
      using that by (intro infsum_Un_disjoint summ_sub) auto
    finally show ?thesis
      using that by simp
  qed
  have splitM: "(\<Sum>\<^sub>\<infinity>k\<in>A. M k) = (\<Sum>k\<in>X. M k) + (\<Sum>\<^sub>\<infinity>k\<in>A-X. M k)"
    if "finite X" "X \<subseteq> A" for X
  proof -
    have "A = X \<union> (A - X)"
      using that by auto
    hence "(\<Sum>\<^sub>\<infinity>k\<in>A. M k) = (\<Sum>\<^sub>\<infinity>k\<in>X \<union> (A - X). M k)"
      by simp
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>k\<in>X. M k) + (\<Sum>\<^sub>\<infinity>k\<in>A-X. M k)"
      using that by (intro infsum_Un_disjoint M_sub) auto
    finally show ?thesis
      using that by simp
  qed
  show ?thesis
    unfolding uniform_limit_iff
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
    \<comment> \<open>a seed whose \<^term>\<open>M\<close>-tail is small; it works for every \<^term>\<open>y \<in> B\<close> at once\<close>
    obtain S where S: "finite S" "S \<subseteq> A" and Sclose: "dist (\<Sum>k\<in>S. M k) (\<Sum>\<^sub>\<infinity>k\<in>A. M k) \<le> \<epsilon>/2"
      using infsum_finite_approximation[OF M, of "\<epsilon>/2"] \<epsilon> by auto
    have tailM: "(\<Sum>\<^sub>\<infinity>k\<in>A-S. M k) \<le> \<epsilon>/2"
      using Sclose splitM[OF S] by (simp add: dist_real_def)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. \<forall>y\<in>B. dist (\<Sum>k\<in>X. h k y) (\<Sum>\<^sub>\<infinity>k\<in>A. h k y) < \<epsilon>"
      unfolding eventually_finite_subsets_at_top
    proof (intro exI[of _ S] conjI allI impI S)
      fix X assume X: "finite X \<and> S \<subseteq> X \<and> X \<subseteq> A"
      hence X': "finite X" "S \<subseteq> X" "X \<subseteq> A" by auto
      show "\<forall>y\<in>B. dist (\<Sum>k\<in>X. h k y) (\<Sum>\<^sub>\<infinity>k\<in>A. h k y) < \<epsilon>"
      proof
        fix y assume y: "y \<in> B"
        have nonneg: "0 \<le> (\<Sum>\<^sub>\<infinity>k\<in>A-X. h k y)"
          using nn y by (intro infsum_nonneg) auto
        have "(\<Sum>\<^sub>\<infinity>k\<in>A-X. h k y) \<le> (\<Sum>\<^sub>\<infinity>k\<in>A-X. M k)"
          using y X' le by (intro infsum_mono summ_sub M_sub) auto
        also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>k\<in>A-S. M k)"
          using X' Mnn by (intro infsum_mono2 M_sub) auto
        also have "\<dots> \<le> \<epsilon>/2"
          by (rule tailM)
        finally have "(\<Sum>\<^sub>\<infinity>k\<in>A-X. h k y) \<le> \<epsilon>/2" .
        moreover have "dist (\<Sum>k\<in>X. h k y) (\<Sum>\<^sub>\<infinity>k\<in>A. h k y) = (\<Sum>\<^sub>\<infinity>k\<in>A-X. h k y)"
          using split[OF y X'(1,3)] nonneg by (simp add: dist_real_def)
        ultimately show "dist (\<Sum>k\<in>X. h k y) (\<Sum>\<^sub>\<infinity>k\<in>A. h k y) < \<epsilon>"
          using \<epsilon> by simp
      qed
    qed
  qed
qed

text \<open>
  The workhorse for products.  Earlier versions of this lemma assumed \<^term>\<open>continuous_on B (f n)\<close>
  for every \<^term>\<open>n\<close> together with \<^term>\<open>compact B\<close>; those served only to bound the limit
  \<^term>\<open>L\<close> of the partial sums on \<^term>\<open>B\<close>, so that bound is now the hypothesis and \<^term>\<open>B\<close> may be
  any set.  The usable form is the \<open>M\<close>-test \<open>uniform_limit_infprod_M_test\<close> below, which discharges
  the uniform-convergence hypothesis as well.
\<close>
lemma uniform_limit_prodinf:
  fixes f :: "'k \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach, semidom, topological_semigroup_mult, t2_space}"
  assumes conv_sum: "uniform_limit B (\<lambda>X y. \<Sum>x\<in>X. norm (f x y)) L (finite_subsets_at_top A)"
  assumes bdd: "\<And>y. y \<in> B \<Longrightarrow> L y \<le> C"
  shows   "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. 1 + f x y) (\<lambda>y. \<Prod>\<^sub>\<infinity>x\<in>A. 1 + f x y) (finite_subsets_at_top A)"
  unfolding uniform_limit_iff
proof (intro allI impI)
  fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"

  \<comment> \<open>From uniform convergence of sums, get pointwise summability and multipliability\<close>
  have summ_y: "(\<lambda>n. norm (f n y)) summable_on A" if "y \<in> B" for y
  proof -
    from conv_sum that have "((\<lambda>X. \<Sum>x\<in>X. norm (f x y)) \<longlongrightarrow> L y) (finite_subsets_at_top A)"
      by (intro tendsto_uniform_limitI)
    thus ?thesis
      unfolding summable_on_def has_sum_def by blast
  qed

  have mult_y: "(\<lambda>x. 1 + f x y) multipliable_on A" if "y \<in> B" for y
    by (simp add: abs_multipliable_multipliable abs_multipliable_on_iff_summable_on summ_y that)

  \<comment> \<open>The infprod is well-defined and is the pointwise limit\<close>
  have prod_tendsto: "(prod (\<lambda>x. 1 + f x y) \<longlongrightarrow> infprod (\<lambda>x. 1 + f x y) A) (finite_subsets_at_top A)" 
    if "y \<in> B" for y
    using mult_y[OF that] by (rule infprod_tendsto)

  \<comment> \<open>Now show: for all \<open>\<epsilon> > 0\<close>, eventually \<open>dist(partial_prod, infprod) < \<epsilon>\<close> uniformly in \<open>y\<close>.
    The estimate is \<open>dist(prod X, prod X2) \<le> norm(prod X) * norm(prod(X2-X) - 1)
      \<le> exp(\<Sum>\<^bsub>X\<^esub> norm f) * (exp(\<Sum>\<^bsub>X2-X\<^esub> norm f) - 1)\<close>; controlling the first factor uniformly
    is what the bound \<^term>\<open>C\<close> on \<^term>\<open>L\<close> is for.\<close>
  note C = bdd

  \<comment> \<open>Pick the seed level so that the product estimate is \<open>< \<epsilon>\<close> for every \<open>y\<in>B\<close>.\<close>
  define r where "r = ln (1 + \<epsilon> / exp (C+1))"
  have r_pos: "r > 0"
    unfolding r_def using \<epsilon> by (intro ln_gt_zero) (auto intro: add_pos_pos)
  have exp_r: "exp r = 1 + \<epsilon> / exp (C+1)"
    unfolding r_def using \<epsilon> by (subst exp_ln) (auto intro: add_pos_pos)

  have "\<forall>\<^sub>F X in finite_subsets_at_top A. \<forall>y\<in>B. dist (\<Sum>x\<in>X. norm (f x y)) (L y) < min 1 (r/4)"
  proof -
    have "min 1 (r/4) > 0" using r_pos by auto
    with conv_sum show ?thesis unfolding uniform_limit_iff by blast
  qed
  then obtain X0 where X0: "finite X0" "X0 \<subseteq> A" and
    X0_prop: "\<And>X. \<lbrakk>finite X; X0 \<subseteq> X; X \<subseteq> A\<rbrakk> \<Longrightarrow> \<forall>y\<in>B. dist (\<Sum>x\<in>X. norm (f x y)) (L y) < min 1 (r/4)"
    by (auto simp: eventually_finite_subsets_at_top)

  show "\<forall>\<^sub>F X in finite_subsets_at_top A. \<forall>y\<in>B. dist (\<Prod>x\<in>X. 1 + f x y) (\<Prod>\<^sub>\<infinity>x\<in>A. 1 + f x y) < \<epsilon>"
    unfolding eventually_finite_subsets_at_top
  proof (intro exI conjI allI impI)
    show "finite X0" by (rule X0(1))
    show "X0 \<subseteq> A" by (rule X0(2))
    fix X assume X_props: "finite X \<and> X0 \<subseteq> X \<and> X \<subseteq> A"
    then have X_fin: "finite X" and X0_X: "X0 \<subseteq> X" and X_sub: "X \<subseteq> A" by auto
    show "\<forall>y\<in>B. dist (\<Prod>x\<in>X. 1 + f x y) (\<Prod>\<^sub>\<infinity>x\<in>A. 1 + f x y) < \<epsilon>"
    proof
      fix y assume y: "y \<in> B"
      define g where "g = (\<lambda>x. 1 + f x y)"
      have limg: "(prod g \<longlongrightarrow> infprod g A) (finite_subsets_at_top A)"
        using prod_tendsto[OF y] unfolding g_def .
      have dX: "dist (\<Sum>x\<in>X. norm (f x y)) (L y) < min 1 (r/4)"
        using X0_prop[OF X_fin X0_X X_sub] y by blast
      have sumX_le: "(\<Sum>x\<in>X. norm (f x y)) \<le> L y + 1"
        using dX unfolding dist_real_def by linarith
      \<comment> \<open>The partial product over \<open>X\<close> is bounded by \<open>exp(L y + 1)\<close>.\<close>
      have normgX: "norm (prod g X) \<le> exp (L y + 1)"
      proof -
        have pe: "norm (g x) \<le> 1 + norm (f x y)" for x
          unfolding g_def using norm_triangle_ineq[of 1 "f x y"] by simp
        have "norm (prod g X) = (\<Prod>x\<in>X. norm (g x))"
          by (simp add: prod_norm)
        also have "\<dots> \<le> (\<Prod>x\<in>X. 1 + norm (f x y))"
          by (intro prod_mono conjI) (use pe in auto)
        also have "\<dots> \<le> exp (\<Sum>x\<in>X. norm (f x y))"
          by (intro prod_le_exp_sum) auto
        also have "\<dots> \<le> exp (L y + 1)"
          using sumX_le by simp
        finally show ?thesis .
      qed
      \<comment> \<open>Key estimate: \<open>dist(prod X, prod X2) \<le> exp(L y + 1) * (exp(\<Sum>\<^bsub>X2-X\<^esub> norm f) - 1)\<close>.\<close>
      have step_bound: "dist (prod g X) (prod g X2) \<le> exp (L y + 1) * (exp (\<Sum>x\<in>X2 - X. norm (f x y)) - 1)"
        if X2: "finite X2" "X \<subseteq> X2" "X2 \<subseteq> A" for X2
      proof -
        define D where "D = X2 - X"
        have Dfin: "finite D" and Ddisj: "X \<inter> D = {}" and X2eq: "X2 = X \<union> D"
          using X2 X_fin unfolding D_def by auto
        have normD: "norm (prod g D - 1) \<le> exp (\<Sum>x\<in>D. norm (f x y)) - 1"
        proof -
          have "norm (prod g D - 1) \<le> (\<Prod>x\<in>D. 1 + norm (f x y)) - 1"
            unfolding g_def using norm_prod_minus1_le_prod_minus1[of "\<lambda>x. f x y" D] by simp
          also have "(\<Prod>x\<in>D. 1 + norm (f x y)) \<le> exp (\<Sum>x\<in>D. norm (f x y))"
            by (intro prod_le_exp_sum) auto
          finally show ?thesis by simp
        qed
        have "prod g X2 = prod g X * prod g D"
          unfolding X2eq using X_fin Dfin Ddisj by (simp add: prod.union_disjoint)
        hence "prod g X2 - prod g X = prod g X * (prod g D - 1)"
          by (simp add: algebra_simps)
        hence "dist (prod g X) (prod g X2) = norm (prod g X) * norm (prod g D - 1)"
          by (simp add: dist_norm norm_mult norm_minus_commute)
        also have "\<dots> \<le> exp (L y + 1) * (exp (\<Sum>x\<in>D. norm (f x y)) - 1)"
          by (intro mult_mono normgX normD) auto
        finally show ?thesis unfolding D_def .
      qed
      \<comment> \<open>The tail sum is small because both \<open>X\<close> and \<open>X2\<close> contain the seed \<open>X0\<close>.\<close>
      have tail_bound: "(\<Sum>x\<in>X2 - X. norm (f x y)) \<le> r/2"
        if X2: "finite X2" "X \<subseteq> X2" "X2 \<subseteq> A" for X2
      proof -
        have "(\<Sum>x\<in>X2. norm (f x y)) = (\<Sum>x\<in>X. norm (f x y)) + (\<Sum>x\<in>X2 - X. norm (f x y))"
          using X2 X_fin by (subst sum.subset_diff[of X X2]) auto
        moreover have "dist (\<Sum>x\<in>X2. norm (f x y)) (L y) < min 1 (r/4)"
          using X0_prop[OF X2(1) _ X2(3)] X0_X X2(2) y by blast
        ultimately show ?thesis using dX unfolding dist_real_def by linarith
      qed
      have dist_le_C: "dist (prod g X) (prod g X2) \<le> exp (L y + 1) * (exp (r/2) - 1)"
        if X2: "finite X2" "X \<subseteq> X2" "X2 \<subseteq> A" for X2
        using step_bound tail_bound that
        by (smt (verit, best) exp_ge_zero exp_mono mult_left_mono)
      \<comment> \<open>Pass to the limit \<open>X2 \<rightarrow> A\<close> using that the closed ball is closed.\<close>
      have "infprod g A \<in> cball (prod g X) (exp (L y + 1) * (exp (r/2) - 1))"
      proof (rule Lim_in_closed_set[OF closed_cball _ _ limg])
        show "\<forall>\<^sub>F X2 in finite_subsets_at_top A. prod g X2 \<in> cball (prod g X) (exp (L y + 1) * (exp (r/2) - 1))"
          unfolding eventually_finite_subsets_at_top
          using X_props dist_le_C by auto
      qed auto
      hence lim_le_C: "dist (prod g X) (infprod g A) \<le> exp (L y + 1) * (exp (r/2) - 1)"
        by (simp add: dist_commute mem_cball)
      \<comment> \<open>The bound is \<open>< \<epsilon>\<close> because \<open>L y \<le> C\<close> and \<open>r/2 < r\<close>.\<close>
      have "exp (L y + 1) * (exp (r/2) - 1) < \<epsilon>"
      proof -
        have "exp (L y + 1) * (exp (r/2) - 1) \<le> exp (C + 1) * (exp (r/2) - 1)"
          using r_pos C[OF y] by (intro mult_right_mono) auto
        also have "\<dots> < exp (C + 1) * (exp r - 1)"
          using r_pos by (intro mult_strict_left_mono) auto
        also have "\<dots> = \<epsilon>"
          using exp_r by (simp add: field_simps)
        finally show ?thesis .
      qed
      with lim_le_C have "dist (prod g X) (infprod g A) < \<epsilon>" by linarith
      thus "dist (\<Prod>x\<in>X. 1 + f x y) (\<Prod>\<^sub>\<infinity>x\<in>A. 1 + f x y) < \<epsilon>"
        unfolding g_def by simp
    qed
  qed
qed

lemma uniform_limit_prodinf':
  fixes f :: "'k \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach, semidom, topological_semigroup_mult, t2_space}"
  assumes conv_sum: "uniform_limit B (\<lambda>X y. \<Sum>x\<in>X. norm (f x y - 1)) L (finite_subsets_at_top A)"
  assumes bdd: "\<And>y. y \<in> B \<Longrightarrow> L y \<le> C"
  shows   "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. f x y) (\<lambda>y. \<Prod>\<^sub>\<infinity>x\<in>A. f x y) (finite_subsets_at_top A)"
proof -
  have "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. 1 + (f x y - 1)) (\<lambda>y. \<Prod>\<^sub>\<infinity>x\<in>A. 1 + (f x y - 1)) (finite_subsets_at_top A)"
    by (rule uniform_limit_prodinf[where L = L and C = C]) (use assms in auto)
  then show ?thesis
    by simp
qed

text \<open>
  \<^bold>\<open>The Weierstrass \<open>M\<close>-test for unordered products\<close>, and the form to use in practice: a
  dominating summable \<^term>\<open>M\<close> is all one has to produce.  No continuity, no compactness, and no
  uniform-convergence hypothesis -- \<open>uniform_limit_infsum_M_test\<close> supplies the latter and the
  bound \<^term>\<open>\<Sum>\<^sub>\<infinity>k\<in>A. M k\<close> the former.  This is the shape in which Weierstrass products arise: on
  a compact set one bounds \<^term>\<open>norm (f k z - 1)\<close> by a summable sequence independent of \<^term>\<open>z\<close>.
  Feeding it to \<open>logderiv_infprod_uniform_limit\<close> gives the logarithmic derivative as a uniformly
  convergent sum.
\<close>
corollary uniform_limit_infprod_M_test:
  fixes f :: "'k \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach, semidom, topological_semigroup_mult, t2_space}"
  assumes le: "\<And>k y. k \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> norm (f k y - 1) \<le> M k"
    and M: "M summable_on A"
  shows "uniform_limit B (\<lambda>X y. \<Prod>k\<in>X. f k y) (\<lambda>y. \<Prod>\<^sub>\<infinity>k\<in>A. f k y) (finite_subsets_at_top A)"
  \<comment> \<open>every step instantiated: at a general index type the search-based versions of these two
      applications diverge\<close>
proof (rule uniform_limit_prodinf'[where L = "\<lambda>y. \<Sum>\<^sub>\<infinity>k\<in>A. norm (f k y - 1)"
                                     and C = "\<Sum>\<^sub>\<infinity>k\<in>A. M k"])
  show "uniform_limit B (\<lambda>X y. \<Sum>k\<in>X. norm (f k y - 1))
                        (\<lambda>y. \<Sum>\<^sub>\<infinity>k\<in>A. norm (f k y - 1)) (finite_subsets_at_top A)"
  proof (rule uniform_limit_infsum_M_test[where h = "\<lambda>k y. norm (f k y - 1)" and M = M])
    show "\<And>k y. k \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> norm (f k y - 1) \<le> M k"
      using le by blast
    show "\<And>k y. k \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> 0 \<le> norm (f k y - 1)"
      by simp
    show "M summable_on A"
      by (rule M)
  qed
  show "(\<Sum>\<^sub>\<infinity>k\<in>A. norm (f k y - 1)) \<le> (\<Sum>\<^sub>\<infinity>k\<in>A. M k)" if y: "y \<in> B" for y
  proof (intro M infsum_mono)
    show "(\<lambda>k. norm (f k y - 1)) summable_on A"
      using M le summable_on_comparison_test y by fastforce
    show "\<And>k. k \<in> A \<Longrightarrow> norm (f k y - 1) \<le> M k"
      using le y by blast
  qed
qed

text \<open>
  The bridge to the sequential theory.  A uniform limit along
  \<^term>\<open>finite_subsets_at_top (UNIV :: nat set)\<close> specialises to a uniform limit over the initial
  segments.  For the logarithmic derivative of a
  Weierstrass product the detour is no longer needed: \<open>uniform_limit_prodinf'\<close> feeds
  \<open>logderiv_infprod_uniform_limit\<close> above directly, both being stated along
  \<^term>\<open>finite_subsets_at_top A\<close>.
\<close>
corollary uniform_limit_prod_lessThan:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: {metric_space, comm_monoid_mult}"
  assumes "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. f x y) P (finite_subsets_at_top UNIV)"
  shows   "uniform_limit B (\<lambda>n y. \<Prod>k<n. f k y) P sequentially"
  using assms filterlim_lessThan_at_top by (rule filterlim_compose)


subsection \<open>Real numbers\<close>

text \<open>Most lemmas in the general property section already apply to real numbers.
      A few ones that are specific to reals are given here.\<close>

(*
  Contributed by Manuel: for real numbers, strong multipliability is equivalent to
  absolute multipliability. The same clearly does not hold for "normal" multipliability.
*)
lemma strongly_multipliable_on_iff_abs_multipliable_on_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  shows \<open>f strongly_multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
proof
  assume *: "f strongly_multipliable_on A"
  then obtain B where B: "B \<subseteq> A" "finite B" "\<And>x. x \<in> A-B \<Longrightarrow> f x \<in> {0<..}"
    using strongly_multipliable_on_imp_nhds_1[OF *, of "{0<..}"] by auto
  have "f strongly_multipliable_on (A - B)"
    by (rule strongly_multipliable_on_Diff_finite) fact+
  moreover from B(3) have "f x \<noteq> 0" if "x \<in> A - B" for x
    using that by force
  ultimately obtain P where P: "(f has_setprod P) (A - B)" "P \<noteq> 0"
    by (subst (asm) strongly_multipliable_on_nonzero_iff) auto

  from P have "((\<lambda>x. ln (f x)) has_sum ln P) (A - B)"
    by (intro has_prod_imp_sums_ln_real)
  hence "(\<lambda>x. ln (f x)) summable_on (A - B)"
    using has_sum_imp_summable by blast
  hence "(\<lambda>x. ln (f x)) abs_summable_on (A - B)"
    by (subst (asm) summable_on_iff_abs_summable_on_real)
  hence "(\<lambda>x. exp (ln (f x))) abs_multipliable_on (A - B)"
    by (intro abs_multipliable_on_exp)
  also have "?this \<longleftrightarrow> f abs_multipliable_on (A - B)"
    by (intro abs_multipliable_on_cong) (use B in auto)
  finally have "f abs_multipliable_on (A - B \<union> B)"
    by (intro abs_multipliable_on_Un_disjoint) (use B in auto)
  also have "A - B \<union> B = A"
    using B by auto
  finally show "f abs_multipliable_on A" .
qed (use abs_multipliable_on_imp_strongly_multipliable_on in blast)

subsection \<open>Complex numbers\<close>

text \<open>
  A criterion that is useful when one controls the finite \<^emph>\<open>partial sums\<close> rather than the
  individual summands: if all of them are bounded, the family is absolutely summable.  Splitting
  a finite subset according to the sign of \<open>g\<close> turns a bound on \<^term>\<open>\<bar>sum g D\<bar>\<close> into a bound
  on \<^term>\<open>sum (\<lambda>x. \<bar>g x\<bar>) D\<close>, and then \<open>nonneg_bdd_above_summable_on\<close> applies.
\<close>
lemma sum_abs_le_of_bdd_partial_sums:
  fixes g :: "'a \<Rightarrow> real"
  assumes bdd: "\<And>E. finite E \<Longrightarrow> E \<subseteq> A \<Longrightarrow> \<bar>sum g E\<bar> \<le> C"
  assumes D: "finite D" "D \<subseteq> A"
  shows "(\<Sum>x\<in>D. \<bar>g x\<bar>) \<le> 2 * C"
proof -
  define P where "P = {x \<in> D. g x \<ge> 0}"
  have PD: "P \<subseteq> D" and Pfin: "finite P"
    using D by (auto simp: P_def)
  have e1: "(\<Sum>x\<in>P. \<bar>g x\<bar>) = sum g P"
    by (intro sum.cong refl) (auto simp: P_def)
  have "(\<Sum>x\<in>D-P. \<bar>g x\<bar>) = (\<Sum>x\<in>D-P. - g x)"
    by (intro sum.cong refl) (auto simp: P_def)
  then have e2: "(\<Sum>x\<in>D-P. \<bar>g x\<bar>) = - sum g (D - P)"
    by (simp add: sum_negf)
  have DPA: "D - P \<subseteq> A" and PA: "P \<subseteq> A"
    using D(2) PD by auto
  have f1: "finite (D - P)"
    using D(1) by simp
  have b1: "- sum g (D - P) \<le> C"
    using bdd[OF f1 DPA] by (simp add: abs_le_iff)
  have b2: "sum g P \<le> C"
    using bdd[OF Pfin PA] by (simp add: abs_le_iff)
  have "(\<Sum>x\<in>D. \<bar>g x\<bar>) = (\<Sum>x\<in>D-P. \<bar>g x\<bar>) + (\<Sum>x\<in>P. \<bar>g x\<bar>)"
    using PD D(1) by (rule sum.subset_diff)
  also have "\<dots> = - sum g (D - P) + sum g P"
    by (simp add: e1 e2)
  also have "\<dots> \<le> 2 * C"
    using b1 b2 by linarith
  finally show ?thesis .
qed

lemma abs_summable_on_real_of_bdd_partial_sums:
  fixes g :: "'a \<Rightarrow> real"
  assumes bdd: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A \<Longrightarrow> \<bar>sum g D\<bar> \<le> C"
  shows "g abs_summable_on A"
proof (rule nonneg_bdd_above_summable_on)
  show "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> norm (g x)"
    by simp
  show "bdd_above (sum (\<lambda>x. norm (g x)) ` {D. D \<subseteq> A \<and> finite D})"
    using sum_abs_le_of_bdd_partial_sums[OF bdd]
    by fastforce
qed

lemma abs_summable_on_of_bdd_partial_sums:
  fixes g :: "'a \<Rightarrow> complex"
  assumes bdd: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A \<Longrightarrow> norm (sum g D) \<le> C"
  shows "g abs_summable_on A"
proof (rule nonneg_bdd_above_summable_on)
  show "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> norm (g x)"
    by simp
  show "bdd_above (sum (\<lambda>x. norm (g x)) ` {D. D \<subseteq> A \<and> finite D})"
  proof (rule bdd_aboveI2)
    fix D assume "D \<in> {D. D \<subseteq> A \<and> finite D}"
    then have D: "finite D" "D \<subseteq> A" by auto
    have re: "\<bar>sum (\<lambda>x. Re (g x)) E\<bar> \<le> C" if "finite E" "E \<subseteq> A" for E
      using bdd[OF that] abs_Re_le_cmod[of "sum g E"] by simp
    have im: "\<bar>sum (\<lambda>x. Im (g x)) E\<bar> \<le> C" if "finite E" "E \<subseteq> A" for E
      using bdd[OF that] abs_Im_le_cmod[of "sum g E"] by simp
    have "(\<Sum>x\<in>D. norm (g x)) \<le> (\<Sum>x\<in>D. \<bar>Re (g x)\<bar> + \<bar>Im (g x)\<bar>)"
      by (intro sum_mono cmod_le)
    also have "\<dots> = (\<Sum>x\<in>D. \<bar>Re (g x)\<bar>) + (\<Sum>x\<in>D. \<bar>Im (g x)\<bar>)"
      by (rule sum.distrib)
    also have "\<dots> \<le> 2 * C + 2 * C"
      using sum_abs_le_of_bdd_partial_sums[OF re D] sum_abs_le_of_bdd_partial_sums[OF im D]
      by simp
    finally show "(\<Sum>x\<in>D. norm (g x)) \<le> 4 * C"
      by simp
  qed
qed

text \<open>
  \<^bold>\<open>The logarithm of an unordered product.\<close>  There is no unconditional complex analogue of
  \<open>has_prod_imp_sums_ln_real\<close>: \<open>((\<lambda>x. Ln (f x)) has_sum Ln P) A\<close> already fails on a two-element
  index set.  Take \<^term>\<open>A = {1, 2 :: nat}\<close> and \<^term>\<open>f = (\<lambda>_. -1 :: complex)\<close>; then
  \<^term>\<open>P = (1 :: complex)\<close> is non-zero with \<^term>\<open>Ln P = 0\<close>, whereas
  \<^term>\<open>Ln (-1 :: complex) = \<i> * pi\<close> and the sum is \<^term>\<open>2 * \<i> * pi\<close>.  Factors far from \<open>1\<close> wrap the
  branch.

  What is true is the statement under a hypothesis that rules the wrapping out, and every product
  with a non-zero value satisfies that hypothesis once a finite set of factors is removed.  The
  first lemma isolates the additivity of \<open>Ln\<close>, which was previously buried in the proof of
  \<open>strongly_multipliable_on_iff_abs_multipliable_on_complex\<close> below.
\<close>
lemma Ln_prod_of_prods_near_1:
  fixes f :: "'a \<Rightarrow> complex"
  assumes near: "\<And>E. finite E \<Longrightarrow> E \<subseteq> S \<Longrightarrow> norm (prod f E - 1) < 1/2"
    and D: "finite D" "D \<subseteq> S"
  shows "Ln (prod f D) = (\<Sum>x\<in>D. Ln (f x))"
proof -
  \<comment> \<open>every subproduct has positive real part, so \<open>Ln\<close> stays well away from the branch cut\<close>
  have Repos: "Re (prod f E) > 0" if E: "finite E" "E \<subseteq> S" for E
  proof -
    have "\<bar>Re (prod f E - 1)\<bar> \<le> norm (prod f E - 1)"
      by (rule abs_Re_le_cmod)
    with near[OF E] show ?thesis
      by simp
  qed
  have prod_nz: "prod f E \<noteq> 0" if "finite E" "E \<subseteq> S" for E
    using Repos[OF that] by auto
  have nzS: "f x \<noteq> 0" if "x \<in> S" for x
    using prod_nz[of "{x}"] that by simp
  have ImLn: "\<bar>Im (Ln (prod f E))\<bar> < pi/2" if "finite E" "E \<subseteq> S" for E
    using Repos[OF that] by (rule Re_Ln_pos_lt_imp)
  \<comment> \<open>hence \<open>Ln\<close> is exactly additive: no winding number appears\<close>
  have Ln_prod: "Ln (prod f E) = (\<Sum>x\<in>E. Ln (f x))" if "finite E" "E \<subseteq> S" for E
    using that
  proof (induction E rule: finite_induct)
    case empty
    show ?case by simp
  next
    case (insert a E)
    from insert.prems have aS: "a \<in> S" and ES: "E \<subseteq> S" by auto
    have IH: "Ln (prod f E) = (\<Sum>x\<in>E. Ln (f x))"
      using insert.IH ES by blast
    have b1: "- (pi/2) < Im (Ln (f a))" "Im (Ln (f a)) < pi/2"
      using ImLn[of "{a}"] aS by (auto simp: abs_less_iff)
    have b2: "- (pi/2) < Im (Ln (prod f E))" "Im (Ln (prod f E)) < pi/2"
      using ImLn[of E] insert.hyps(1) ES by (auto simp: abs_less_iff)
    have "Ln (prod f (insert a E)) = Ln (f a * prod f E)"
      using insert.hyps by simp
    also have "\<dots> = Ln (f a) + Ln (prod f E)"
    proof (rule Ln_times_simple)
      show "f a \<noteq> 0" using aS by (rule nzS)
      show "prod f E \<noteq> 0" using insert.hyps(1) ES by (rule prod_nz)
      show "- pi < Im (Ln (f a)) + Im (Ln (prod f E))"
        using b1 b2 by linarith
      show "Im (Ln (f a)) + Im (Ln (prod f E)) \<le> pi"
        using b1 b2 by linarith
    qed
    also have "\<dots> = (\<Sum>x\<in>insert a E. Ln (f x))"
      using insert.hyps IH by simp
    finally show ?case .
  qed
  show ?thesis
    using D by (rule Ln_prod)
qed

text \<open>
  With additivity available, the logarithm of the product is the sum of the logarithms: the partial
  sums are literally \<^term>\<open>Ln (prod f X)\<close>, and the limit is off the branch cut because the closed
  ball \<^term>\<open>cball (1::complex) (1/2)\<close> is, so \<open>tendsto_Ln\<close> applies.
\<close>
lemma has_sum_Ln_of_prods_near_1:
  fixes f :: "'a \<Rightarrow> complex"
  assumes P: "(f has_setprod P) A"
    and near: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A \<Longrightarrow> norm (prod f D - 1) < 1/2"
  shows "((\<lambda>x. Ln (f x)) has_sum Ln P) A"
proof -
  have lim: "(prod f \<longlongrightarrow> P) (finite_subsets_at_top A)"
    using P by (simp add: has_setprod_def)
  \<comment> \<open>the value inherits the bound on the subproducts\<close>
  have "P \<in> cball 1 (1/2)"
  proof (rule Lim_in_closed_set[OF closed_cball _ _ lim])
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<in> cball 1 (1/2)"
    proof (intro eventually_finite_subsets_at_top_weakI)
      fix X assume X: "finite X" "X \<subseteq> A"
      have "norm (prod f X - 1) < 1/2"
        by (rule near[OF X])
      thus "prod f X \<in> cball 1 (1/2)"
        by (simp add: dist_norm norm_minus_commute)
    qed
  qed auto
  hence "norm (P - 1) \<le> 1/2"
    by (simp add: dist_norm norm_minus_commute)
  hence ReP: "Re P > 0"
    using abs_Re_le_cmod[of "P - 1"] by simp
  hence "P \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (auto simp: complex_nonpos_Reals_iff)
  have "((\<lambda>X. Ln (prod f X)) \<longlongrightarrow> Ln P) (finite_subsets_at_top A)"
    by (rule tendsto_Ln[OF lim]) fact
  also have "?this \<longleftrightarrow> (sum (\<lambda>x. Ln (f x)) \<longlongrightarrow> Ln P) (finite_subsets_at_top A)"
  proof (intro filterlim_cong)
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. X \<subseteq> A \<and> finite X"
      by (rule eventually_finite_subsets_at_top_weakI) auto
    thus "\<forall>\<^sub>F X in finite_subsets_at_top A. Ln (prod f X) = (\<Sum>x\<in>X. Ln (f x))"
      by eventually_elim (use Ln_prod_of_prods_near_1[OF near] in blast)
  qed auto
  finally show ?thesis
    unfolding has_sum_def .
qed

text \<open>
  The general form: for a product with a non-zero value the logarithms are summable, and sum to the
  logarithm of the product, after removing finitely many factors.  As the counterexample above
  shows, the finite exceptional set cannot be dispensed with.
\<close>
corollary has_sum_Ln_of_has_setprod_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes P: "(f has_setprod P) A" and nz: "P \<noteq> 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and>
             ((\<lambda>x. Ln (f x)) has_sum Ln (\<Prod>\<^sub>\<infinity>x\<in>A-F. f x)) (A - F)"
proof -
  have lim: "(prod f \<longlongrightarrow> P) (finite_subsets_at_top A)"
    using P by (simp add: has_setprod_def)
  have half: "(1/2::real) > 0"
    by simp
  obtain F where F: "finite F" "F \<subseteq> A"
    and near: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A - F \<Longrightarrow> dist (prod f D) 1 < 1/2"
    using has_setprod_prods_near_1[OF lim nz half] by blast
  obtain Q where Q: "(f has_setprod Q) (A - F)" "Q \<noteq> 0"
    using has_setprod_subset_nonzero[OF P nz Diff_subset] by blast
  \<comment> \<open>\<^bold>\<open>NB\<close> \<open>infprodI\<close> must not be given to the simplifier: its premise contains the value as a
      schematic variable, so rewriting \<^term>\<open>infprod f A\<close> sends it looking for one\<close>
  have Qeq: "(\<Prod>\<^sub>\<infinity>x\<in>A-F. f x) = Q"
    by (rule infprodI[OF Q(1)])
  have sum: "((\<lambda>x. Ln (f x)) has_sum Ln Q) (A - F)"
    by (rule has_sum_Ln_of_prods_near_1[OF Q(1)]) (use near in \<open>simp add: dist_norm\<close>)
  show ?thesis
    using F Qeq sum by blast
qed
text \<open>
  The complex analogue of \<open>strongly_multipliable_on_iff_abs_multipliable_on_real\<close>.  The
  difficulty anticipated in the original note -- that \<^term>\<open>\<Sum>x. Ln (f x)\<close> might cross branch
  cuts, with an ill-defined winding count for an unordered index set -- does not in fact arise.
  A non-zero product forces every finite subproduct outside a suitable finite set to lie within
  \<open>1/2\<close> of \<open>1\<close>, and \<open>Ln_prod_of_prods_near_1\<close> above turns that into exact additivity of \<open>Ln\<close>.  The
  resulting partial sums of \<^term>\<open>Ln \<circ> f\<close> are then bounded by \<open>norm_Ln_le\<close>, which gives absolute
  summability and hence absolute multipliability.
\<close>
lemma strongly_multipliable_on_iff_abs_multipliable_on_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>f strongly_multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
proof
  assume *: "f strongly_multipliable_on A"
  define A0 where "A0 = {x \<in> A. f x \<noteq> 0}"
  from * obtain P where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) A0" "P \<noteq> 0"
    unfolding strongly_multipliable_on_def A0_def by blast
  have limA0: "(prod f \<longlongrightarrow> P) (finite_subsets_at_top A0)"
    using P(2) by (simp add: has_setprod_def)
  have half: "(1/2::real) > 0"
    by simp
  obtain F where F: "finite F" "F \<subseteq> A0"
    and near: "\<And>D. finite D \<Longrightarrow> D \<subseteq> A0 - F \<Longrightarrow> dist (prod f D) 1 < 1/2"
    using has_setprod_prods_near_1[OF limA0 P(3) half] by blast
  define S where "S = A0 - F"
  have SA: "S \<subseteq> A"
    by (auto simp: S_def A0_def)
  have nzS: "f x \<noteq> 0" if "x \<in> S" for x
    using that by (auto simp: S_def A0_def)
  have near': "norm (prod f D - 1) < 1/2" if "finite D" "D \<subseteq> S" for D
    using near[of D] that by (simp add: S_def dist_norm)
  \<comment> \<open>\<open>Ln\<close> is exactly additive along these subproducts: no winding number appears\<close>
  have Ln_prod: "Ln (prod f D) = (\<Sum>x\<in>D. Ln (f x))" if "finite D" "D \<subseteq> S" for D
    by (rule Ln_prod_of_prods_near_1[OF near' that])
  \<comment> \<open>so the partial sums of \<open>Ln \<circ> f\<close> are bounded\<close>
  have bdd: "norm (\<Sum>x\<in>D. Ln (f x)) \<le> 1" if D: "finite D" "D \<subseteq> S" for D
  proof -
    have eq: "(\<Sum>x\<in>D. Ln (f x)) = Ln (1 + (prod f D - 1))"
      using Ln_prod[OF D] by simp
    have "norm (Ln (1 + (prod f D - 1))) \<le> 2 * norm (prod f D - 1)"
      by (rule norm_Ln_le) (use near'[OF D] in simp)
    also have "\<dots> \<le> 1"
      using near'[OF D] by simp
    finally show ?thesis
      using eq by simp
  qed
  have "(\<lambda>x. Ln (f x)) abs_summable_on S"
    by (rule abs_summable_on_of_bdd_partial_sums[where C = 1]) (use bdd in auto)
  hence "(\<lambda>x. exp (Ln (f x))) abs_multipliable_on S"
    by (intro abs_multipliable_on_exp)
  also have "?this \<longleftrightarrow> f abs_multipliable_on S"
    by (intro abs_multipliable_on_cong) (use nzS in auto)
  finally have S: "f abs_multipliable_on S" .
  \<comment> \<open>and the finitely many exceptional points do no harm\<close>
  have "A - S \<subseteq> {x\<in>A. f x = 0} \<union> F"
    by (auto simp: S_def A0_def)
  hence finAS: "finite (A - S)"
    using P(1) F(1) by (auto elim: finite_subset)
  have "f abs_multipliable_on (S \<union> (A - S))"
    using S abs_multipliable_on_finite[OF finAS] by (intro abs_multipliable_on_Un_disjoint) auto
  also have "S \<union> (A - S) = A"
    using SA by auto
  finally show "f abs_multipliable_on A" .
qed (use abs_multipliable_on_imp_strongly_multipliable_on in blast)

text \<open>
  A striking consequence, for real and for complex families: an unordered product whose value is
  non-zero converges \<^emph>\<open>absolutely\<close>.  So for these types there is no distinction between
  unconditional and absolute convergence of products once the value \<open>0\<close> is excluded -- the exact
  analogue of the corresponding fact for sums.
\<close>
corollary multipliable_on_imp_abs_multipliable_on_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes mult: "f multipliable_on A" and nz: "infprod f A \<noteq> 0"
  shows "f abs_multipliable_on A"
proof -
  have P: "(f has_setprod infprod f A) A"
    using mult by (rule has_setprod_infprod)
  have nzf: "f x \<noteq> 0" if "x \<in> A" for x
    using nz that by (meson infprodI zero_imp_has_setprod_0)
  have empty: "{x \<in> A. f x = 0} = {}"
    using nzf by blast
  have all: "{x \<in> A. f x \<noteq> 0} = A"
    using nzf by blast
  have "f strongly_multipliable_on A"
    using P nz nzf strongly_multipliable_on_nonzero_iff by blast
  thus ?thesis
    by (simp add: strongly_multipliable_on_iff_abs_multipliable_on_complex)
qed

corollary multipliable_on_imp_abs_multipliable_on_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes mult: "f multipliable_on A" and nz: "infprod f A \<noteq> 0"
  shows "f abs_multipliable_on A"
proof -
  have P: "(f has_setprod infprod f A) A"
    using mult by (rule has_setprod_infprod)
  have nzf: "f x \<noteq> 0" if "x \<in> A" for x
    using nz that by (meson infprodI zero_imp_has_setprod_0)
  have empty: "{x \<in> A. f x = 0} = {}"
    using nzf by blast
  have all: "{x \<in> A. f x \<noteq> 0} = A"
    using nzf by blast
  have "f strongly_multipliable_on A"
    using P nz nzf strongly_multipliable_on_nonzero_iff by blast
  thus ?thesis
    by (simp add: strongly_multipliable_on_iff_abs_multipliable_on_real)
qed

lemma has_setprod_cnj_iff[simp]: 
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>((\<lambda>x. cnj (f x)) has_setprod cnj a) M \<longleftrightarrow> (f has_setprod a) M\<close>
  using lim_cnj by (fastforce simp add: has_setprod_def)

lemma multipliable_on_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) multipliable_on A \<longleftrightarrow> f multipliable_on A"
  by (metis complex_cnj_cnj multipliable_on_def has_setprod_cnj_iff)

lemma infprod_cnj[simp]: \<open>infprod (\<lambda>x. cnj (f x)) M = cnj (infprod f M)\<close>
  by (metis complex_cnj_one has_setprod_cnj_iff has_setprod_infprod infprodI
      infprod_not_exists multipliable_on_cnj_iff)

lemma has_setprod_Re:
  assumes "(f has_setprod a) M" and real: "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>"
  shows "((\<lambda>x. Re (f x)) has_setprod Re a) M"
proof -
  have eq: "\<forall>\<^sub>F X in finite_subsets_at_top M. prod (\<lambda>x. Re (f x)) X = Re (prod f X)"
    by (simp add: Re_prod_Reals eventually_finite_subsets_at_top_weakI real subsetD)
  from assms(1) have "((\<lambda>X. Re (prod f X)) \<longlongrightarrow> Re a) (finite_subsets_at_top M)"
    by (simp add: has_setprodD tendsto_Re)
  then show ?thesis
    using eq unfolding has_setprod_def by (simp add: filterlim_cong)
qed

lemma infprod_Re:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>"
  shows "infprod (\<lambda>x. Re (f x)) M = Re (infprod f M)"
  by (simp add: assms has_setprod_Re infprodI)

lemma multipliable_on_Re:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>"
  shows "(\<lambda>x. Re (f x)) multipliable_on M"
  by (metis assms has_setprod_Re multipliable_on_def)

lemma has_setprod_Im:
  assumes "(f has_setprod a) M" and real: "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>" and "M \<noteq> {}"
  shows "((\<lambda>x. Im (f x)) has_setprod Im a) M"
proof -
  from \<open>M \<noteq> {}\<close> obtain m where "m \<in> M" by blast
  have eq: "\<forall>\<^sub>F X in finite_subsets_at_top M. prod (\<lambda>x. Im (f x)) X = Im (prod f X)"
    unfolding eventually_finite_subsets_at_top
  proof (intro exI conjI allI impI)
    show "finite {m}" "{m} \<subseteq> M" using \<open>m \<in> M\<close> by auto
  next
    fix X assume "finite X \<and> {m} \<subseteq> X \<and> X \<subseteq> M"
    then have "finite X" "X \<subseteq> M" "X \<noteq> {}" by auto
    have "Im (f x) = 0" if "x \<in> X" for x
      using real \<open>X \<subseteq> M\<close> that by (auto simp: complex_is_Real_iff subset_iff)
    then have "prod (\<lambda>x. Im (f x)) X = prod (\<lambda>x. (0::real)) X"
      by (intro prod.cong) auto
    also have "\<dots> = 0"
      using \<open>finite X\<close> \<open>X \<noteq> {}\<close> by (intro prod_zero) auto
    finally have lhs: "prod (\<lambda>x. Im (f x)) X = 0" .
    have "prod f X \<in> \<real>"
      using real \<open>X \<subseteq> M\<close> by (intro prod_in_Reals) (auto simp: subset_iff)
    then have "Im (prod f X) = 0"
      by (simp add: complex_is_Real_iff)
    with lhs show "prod (\<lambda>x. Im (f x)) X = Im (prod f X)" by simp
  qed
  from assms(1) have "(prod f \<longlongrightarrow> a) (finite_subsets_at_top M)"
    by (simp add: has_setprod_def)
  then have "((\<lambda>X. Im (prod f X)) \<longlongrightarrow> Im a) (finite_subsets_at_top M)"
    by (rule tendsto_Im)
  then show ?thesis
    unfolding has_setprod_def using eq tendsto_cong by fastforce
qed

lemma infprod_Im:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>" and "M \<noteq> {}"
  shows "infprod (\<lambda>x. Im (f x)) M = Im (infprod f M)"
  by (simp add: assms has_setprod_Im infprodI)

lemma multipliable_on_Im:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>" and "M \<noteq> {}"
  shows "(\<lambda>x. Im (f x)) multipliable_on M"
  by (metis assms has_setprod_Im multipliable_on_def)

end
