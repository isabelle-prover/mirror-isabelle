(*  Title:      HOL/HOLCF/Ssum.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section \<open>The type of strict sums\<close>

theory Ssum
  imports Tr
begin

subsection \<open>Definition of strict sum type\<close>

definition "ssum =
  {p :: tr \<times> ('a::pcpo \<times> 'b::pcpo). p = \<bottom> \<or>
    (fst p = TT \<and> fst (snd p) \<noteq> \<bottom> \<and> snd (snd p) = \<bottom>) \<or>
    (fst p = FF \<and> fst (snd p) = \<bottom> \<and> snd (snd p) \<noteq> \<bottom>)}"

pcpodef ('a::pcpo, 'b::pcpo) ssum  (\<open>(\<open>notation=\<open>infix strict sum\<close>\<close>_ \<oplus>/ _)\<close> [21, 20] 20) =
  "ssum :: (tr \<times> 'a \<times> 'b) set"
  by (simp_all add: ssum_def)

instance ssum :: ("{chfin,pcpo}", "{chfin,pcpo}") chfin
  by (rule typedef_chfin [OF type_definition_ssum below_ssum_def])

type_notation (ASCII)
  ssum  (infixr \<open>++\<close> 10)


subsection \<open>Definitions of constructors\<close>

definition sinl :: "'a::pcpo \<rightarrow> ('a ++ 'b::pcpo)"
  where "sinl = (\<Lambda> a. Abs_ssum (seq\<cdot>a\<cdot>TT, a, \<bottom>))"

definition sinr :: "'b::pcpo \<rightarrow> ('a::pcpo ++ 'b)"
  where "sinr = (\<Lambda> b. Abs_ssum (seq\<cdot>b\<cdot>FF, \<bottom>, b))"

lemma sinl_ssum: "(seq\<cdot>a\<cdot>TT, a, \<bottom>) \<in> ssum"
  by (simp add: ssum_def seq_conv_if)

lemma sinr_ssum: "(seq\<cdot>b\<cdot>FF, \<bottom>, b) \<in> ssum"
  by (simp add: ssum_def seq_conv_if)

lemma Rep_ssum_sinl: "Rep_ssum (sinl\<cdot>a) = (seq\<cdot>a\<cdot>TT, a, \<bottom>)"
  by (simp add: sinl_def cont_Abs_ssum Abs_ssum_inverse sinl_ssum)

lemma Rep_ssum_sinr: "Rep_ssum (sinr\<cdot>b) = (seq\<cdot>b\<cdot>FF, \<bottom>, b)"
  by (simp add: sinr_def cont_Abs_ssum Abs_ssum_inverse sinr_ssum)

lemmas Rep_ssum_simps =
  Rep_ssum_inject [symmetric] below_ssum_def
  prod_eq_iff below_prod_def
  Rep_ssum_strict Rep_ssum_sinl Rep_ssum_sinr


subsection \<open>Properties of \emph{sinl} and \emph{sinr}\<close>

text \<open>Ordering\<close>

lemma sinl_below [simp]: "sinl\<cdot>x \<sqsubseteq> sinl\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
  by (simp add: Rep_ssum_simps seq_conv_if)

lemma sinr_below [simp]: "sinr\<cdot>x \<sqsubseteq> sinr\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
  by (simp add: Rep_ssum_simps seq_conv_if)

lemma sinl_below_sinr [simp]: "sinl\<cdot>x \<sqsubseteq> sinr\<cdot>y \<longleftrightarrow> x = \<bottom>"
  by (simp add: Rep_ssum_simps seq_conv_if)

lemma sinr_below_sinl [simp]: "sinr\<cdot>x \<sqsubseteq> sinl\<cdot>y \<longleftrightarrow> x = \<bottom>"
  by (simp add: Rep_ssum_simps seq_conv_if)

text \<open>Equality\<close>

lemma sinl_eq [simp]: "sinl\<cdot>x = sinl\<cdot>y \<longleftrightarrow> x = y"
  by (simp add: po_eq_conv)

lemma sinr_eq [simp]: "sinr\<cdot>x = sinr\<cdot>y \<longleftrightarrow> x = y"
  by (simp add: po_eq_conv)

lemma sinl_eq_sinr [simp]: "sinl\<cdot>x = sinr\<cdot>y \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (subst po_eq_conv) simp

lemma sinr_eq_sinl [simp]: "sinr\<cdot>x = sinl\<cdot>y \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (subst po_eq_conv) simp

lemma sinl_inject: "sinl\<cdot>x = sinl\<cdot>y \<Longrightarrow> x = y"
  by (rule sinl_eq [THEN iffD1])

lemma sinr_inject: "sinr\<cdot>x = sinr\<cdot>y \<Longrightarrow> x = y"
  by (rule sinr_eq [THEN iffD1])

text \<open>Strictness\<close>

lemma sinl_strict [simp]: "sinl\<cdot>\<bottom> = \<bottom>"
  by (simp add: Rep_ssum_simps)

lemma sinr_strict [simp]: "sinr\<cdot>\<bottom> = \<bottom>"
  by (simp add: Rep_ssum_simps)

lemma sinl_bottom_iff [simp]: "sinl\<cdot>x = \<bottom> \<longleftrightarrow> x = \<bottom>"
  using sinl_eq [of "x" "\<bottom>"] by simp

lemma sinr_bottom_iff [simp]: "sinr\<cdot>x = \<bottom> \<longleftrightarrow> x = \<bottom>"
  using sinr_eq [of "x" "\<bottom>"] by simp

lemma sinl_defined: "x \<noteq> \<bottom> \<Longrightarrow> sinl\<cdot>x \<noteq> \<bottom>"
  by simp

lemma sinr_defined: "x \<noteq> \<bottom> \<Longrightarrow> sinr\<cdot>x \<noteq> \<bottom>"
  by simp

text \<open>Compactness\<close>

lemma compact_sinl: "compact x \<Longrightarrow> compact (sinl\<cdot>x)"
  by (rule compact_ssum) (simp add: Rep_ssum_sinl)

lemma compact_sinr: "compact x \<Longrightarrow> compact (sinr\<cdot>x)"
  by (rule compact_ssum) (simp add: Rep_ssum_sinr)

lemma compact_sinlD: "compact (sinl\<cdot>x) \<Longrightarrow> compact x"
  unfolding compact_def
  by (drule adm_subst [OF cont_Rep_cfun2 [where f=sinl]], simp)

lemma compact_sinrD: "compact (sinr\<cdot>x) \<Longrightarrow> compact x"
  unfolding compact_def
  by (drule adm_subst [OF cont_Rep_cfun2 [where f=sinr]], simp)

lemma compact_sinl_iff [simp]: "compact (sinl\<cdot>x) = compact x"
  by (safe elim!: compact_sinl compact_sinlD)

lemma compact_sinr_iff [simp]: "compact (sinr\<cdot>x) = compact x"
  by (safe elim!: compact_sinr compact_sinrD)


subsection \<open>Case analysis\<close>

lemma ssumE [case_names bottom sinl sinr, cases type: ssum]:
  obtains "p = \<bottom>"
  | x where "p = sinl\<cdot>x" and "x \<noteq> \<bottom>"
  | y where "p = sinr\<cdot>y" and "y \<noteq> \<bottom>"
  using Rep_ssum [of p] by (auto simp add: ssum_def Rep_ssum_simps)

lemma ssum_induct [case_names bottom sinl sinr, induct type: ssum]:
  "\<lbrakk>P \<bottom>;
   \<And>x. x \<noteq> \<bottom> \<Longrightarrow> P (sinl\<cdot>x);
   \<And>y. y \<noteq> \<bottom> \<Longrightarrow> P (sinr\<cdot>y)\<rbrakk> \<Longrightarrow> P x"
  by (cases x) simp_all

lemma ssumE2 [case_names sinl sinr]:
  "\<lbrakk>\<And>x. p = sinl\<cdot>x \<Longrightarrow> Q; \<And>y. p = sinr\<cdot>y \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (cases p, simp only: sinl_strict [symmetric], simp, simp)

lemma below_sinlD: "p \<sqsubseteq> sinl\<cdot>x \<Longrightarrow> \<exists>y. p = sinl\<cdot>y \<and> y \<sqsubseteq> x"
  by (cases p, rule_tac x="\<bottom>" in exI, simp_all)

lemma below_sinrD: "p \<sqsubseteq> sinr\<cdot>x \<Longrightarrow> \<exists>y. p = sinr\<cdot>y \<and> y \<sqsubseteq> x"
  by (cases p, rule_tac x="\<bottom>" in exI, simp_all)


subsection \<open>Case analysis combinator\<close>

definition sscase :: "('a::pcpo \<rightarrow> 'c::pcpo) \<rightarrow> ('b::pcpo \<rightarrow> 'c) \<rightarrow> ('a ++ 'b) \<rightarrow> 'c"
  where "sscase = (\<Lambda> f g s. (\<lambda>(t, x, y). If t then f\<cdot>x else g\<cdot>y) (Rep_ssum s))"

translations
  "case s of XCONST sinl\<cdot>x \<Rightarrow> t1 | XCONST sinr\<cdot>y \<Rightarrow> t2" \<rightleftharpoons> "CONST sscase\<cdot>(\<Lambda> x. t1)\<cdot>(\<Lambda> y. t2)\<cdot>s"
  "case s of (XCONST sinl :: 'a)\<cdot>x \<Rightarrow> t1 | XCONST sinr\<cdot>y \<Rightarrow> t2" \<rightharpoonup> "CONST sscase\<cdot>(\<Lambda> x. t1)\<cdot>(\<Lambda> y. t2)\<cdot>s"

translations
  "\<Lambda>(XCONST sinl\<cdot>x). t" \<rightleftharpoons> "CONST sscase\<cdot>(\<Lambda> x. t)\<cdot>\<bottom>"
  "\<Lambda>(XCONST sinr\<cdot>y). t" \<rightleftharpoons> "CONST sscase\<cdot>\<bottom>\<cdot>(\<Lambda> y. t)"

lemma beta_sscase: "sscase\<cdot>f\<cdot>g\<cdot>s = (\<lambda>(t, x, y). If t then f\<cdot>x else g\<cdot>y) (Rep_ssum s)"
  by (simp add: sscase_def cont_Rep_ssum)

lemma sscase1 [simp]: "sscase\<cdot>f\<cdot>g\<cdot>\<bottom> = \<bottom>"
  by (simp add: beta_sscase Rep_ssum_strict)

lemma sscase2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = f\<cdot>x"
  by (simp add: beta_sscase Rep_ssum_sinl)

lemma sscase3 [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>y) = g\<cdot>y"
  by (simp add: beta_sscase Rep_ssum_sinr)

lemma sscase4 [simp]: "sscase\<cdot>sinl\<cdot>sinr\<cdot>z = z"
  by (cases z) simp_all


subsection \<open>Strict sum preserves flatness\<close>

instance ssum :: (flat, flat) flat
  apply (intro_classes, clarify)
  apply (case_tac x, simp)
   apply (case_tac y, simp_all add: flat_below_iff)
  apply (case_tac y, simp_all add: flat_below_iff)
  done

end
