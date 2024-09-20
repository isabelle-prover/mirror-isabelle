section \<open>Equipollence and Other Relations Connected with Cardinality\<close>

theory "Equipollence"
  imports FuncSet Countable_Set
begin

subsection\<open>Eqpoll\<close>

definition eqpoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl \<open>\<approx>\<close> 50)
  where "eqpoll A B \<equiv> \<exists>f. bij_betw f A B"

definition lepoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl \<open>\<lesssim>\<close> 50)
  where "lepoll A B \<equiv> \<exists>f. inj_on f A \<and> f ` A \<subseteq> B"

definition lesspoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl \<open>\<prec>\<close> 50)
  where "A \<prec> B == A \<lesssim> B \<and> ~(A \<approx> B)"

lemma lepoll_def': "lepoll A B \<equiv> \<exists>f. inj_on f A \<and> f \<in> A \<rightarrow> B"
  by (simp add: Pi_iff image_subset_iff lepoll_def)

lemma eqpoll_empty_iff_empty [simp]: "A \<approx> {} \<longleftrightarrow> A={}"
  by (simp add: bij_betw_iff_bijections eqpoll_def)

lemma lepoll_empty_iff_empty [simp]: "A \<lesssim> {} \<longleftrightarrow> A = {}"
  by (auto simp: lepoll_def)

lemma not_lesspoll_empty: "\<not> A \<prec> {}"
  by (simp add: lesspoll_def)

(*The HOL Light CARD_LE_RELATIONAL_FULL*)
lemma lepoll_relational_full:
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x. x \<in> A \<and> R x y"
    and "\<And>x y y'. \<lbrakk>x \<in> A; y \<in> B; y' \<in> B; R x y; R x y'\<rbrakk> \<Longrightarrow> y = y'"
  shows "B \<lesssim> A"
proof -
  obtain f where f: "\<And>y. y \<in> B \<Longrightarrow> f y \<in> A \<and> R (f y) y"
    using assms by metis
  with assms have "inj_on f B"
    by (metis inj_onI)
  with f show ?thesis
    unfolding lepoll_def by blast
qed

lemma eqpoll_iff_card_of_ordIso: "A \<approx> B \<longleftrightarrow> ordIso2 (card_of A) (card_of B)"
  by (simp add: card_of_ordIso eqpoll_def)

lemma eqpoll_refl [iff]: "A \<approx> A"
  by (simp add: card_of_refl eqpoll_iff_card_of_ordIso)

lemma eqpoll_finite_iff: "A \<approx> B \<Longrightarrow> finite A \<longleftrightarrow> finite B"
  by (meson bij_betw_finite eqpoll_def)

lemma eqpoll_iff_card:
  assumes "finite A" "finite B"
  shows  "A \<approx> B \<longleftrightarrow> card A = card B"
  using assms by (auto simp: bij_betw_iff_card eqpoll_def)

lemma eqpoll_singleton_iff: "A \<approx> {x} \<longleftrightarrow> (\<exists>u. A = {u})"
  by (metis card.infinite card_1_singleton_iff eqpoll_finite_iff eqpoll_iff_card not_less_eq_eq)

lemma eqpoll_doubleton_iff: "A \<approx> {x,y} \<longleftrightarrow> (\<exists>u v. A = {u,v} \<and> (u=v \<longleftrightarrow> x=y))"
proof (cases "x=y")
  case True
  then show ?thesis
    by (simp add: eqpoll_singleton_iff)
next
  case False
  then show ?thesis
    by (smt (verit, ccfv_threshold) card_1_singleton_iff card_Suc_eq_finite eqpoll_finite_iff
        eqpoll_iff_card finite.insertI singleton_iff)
qed

lemma lepoll_antisym:
  assumes "A \<lesssim> B" "B \<lesssim> A" shows "A \<approx> B"
  using assms unfolding eqpoll_def lepoll_def by (metis Schroeder_Bernstein)

lemma lepoll_trans [trans]:
  assumes "A \<lesssim> B" " B \<lesssim> C" shows "A \<lesssim> C"
proof -
  obtain f g where fg: "inj_on f A" "inj_on g B" and "f : A \<rightarrow> B" "g \<in> B \<rightarrow> C"
    by (metis assms lepoll_def')
  then have "g \<circ> f \<in> A \<rightarrow> C"
    by auto
  with fg show ?thesis
    unfolding lepoll_def
    by (metis \<open>f \<in> A \<rightarrow> B\<close> comp_inj_on image_subset_iff_funcset inj_on_subset)
qed

lemma lepoll_trans1 [trans]: "\<lbrakk>A \<approx> B; B \<lesssim> C\<rbrakk> \<Longrightarrow> A \<lesssim> C"
  by (meson card_of_ordLeq eqpoll_iff_card_of_ordIso lepoll_def lepoll_trans ordIso_iff_ordLeq)

lemma lepoll_trans2 [trans]: "\<lbrakk>A \<lesssim> B; B \<approx> C\<rbrakk> \<Longrightarrow> A \<lesssim> C"
  by (metis bij_betw_def eqpoll_def lepoll_def lepoll_trans order_refl)

lemma eqpoll_sym: "A \<approx> B \<Longrightarrow> B \<approx> A"
  unfolding eqpoll_def
  using bij_betw_the_inv_into by auto

lemma eqpoll_trans [trans]: "\<lbrakk>A \<approx> B; B \<approx> C\<rbrakk> \<Longrightarrow> A \<approx> C"
  unfolding eqpoll_def using bij_betw_trans by blast

lemma eqpoll_imp_lepoll: "A \<approx> B \<Longrightarrow> A \<lesssim> B"
  unfolding eqpoll_def lepoll_def by (metis bij_betw_def order_refl)

lemma subset_imp_lepoll: "A \<subseteq> B \<Longrightarrow> A \<lesssim> B"
  by (force simp: lepoll_def)

lemma lepoll_refl [iff]: "A \<lesssim> A"
  by (simp add: subset_imp_lepoll)

lemma lepoll_iff: "A \<lesssim> B \<longleftrightarrow> (\<exists>g. A \<subseteq> g ` B)"
  unfolding lepoll_def
proof safe
  fix g assume "A \<subseteq> g ` B"
  then show "\<exists>f. inj_on f A \<and> f ` A \<subseteq> B"
    by (rule_tac x="inv_into B g" in exI) (auto simp: inv_into_into inj_on_inv_into)
qed (metis image_mono the_inv_into_onto)

lemma empty_lepoll [iff]: "{} \<lesssim> A"
  by (simp add: lepoll_iff)

lemma subset_image_lepoll: "B \<subseteq> f ` A \<Longrightarrow> B \<lesssim> A"
  by (auto simp: lepoll_iff)

lemma image_lepoll: "f ` A \<lesssim> A"
  by (auto simp: lepoll_iff)

lemma infinite_le_lepoll: "infinite A \<longleftrightarrow> (UNIV::nat set) \<lesssim> A"
  by (simp add: infinite_iff_countable_subset lepoll_def)

lemma lepoll_Pow_self: "A \<lesssim> Pow A"
  unfolding lepoll_def inj_def
  proof (intro exI conjI)
    show "inj_on (\<lambda>x. {x}) A"
      by (auto simp: inj_on_def)
qed auto

lemma eqpoll_iff_bijections:
   "A \<approx> B \<longleftrightarrow> (\<exists>f g. (\<forall>x \<in> A. f x \<in> B \<and> g(f x) = x) \<and> (\<forall>y \<in> B. g y \<in> A \<and> f(g y) = y))"
    by (auto simp: eqpoll_def bij_betw_iff_bijections)

lemma lepoll_restricted_funspace:
   "{f. f ` A \<subseteq> B \<and> {x. f x \<noteq> k x} \<subseteq> A \<and> finite {x. f x \<noteq> k x}} \<lesssim> Fpow (A \<times> B)"
proof -
  have *: "\<exists>U \<in> Fpow (A \<times> B). f = (\<lambda>x. if \<exists>y. (x, y) \<in> U then SOME y. (x,y) \<in> U else k x)"
    if "f ` A \<subseteq> B" "{x. f x \<noteq> k x} \<subseteq> A" "finite {x. f x \<noteq> k x}" for f
    apply (rule_tac x="(\<lambda>x. (x, f x)) ` {x. f x \<noteq> k x}" in bexI)
    using that by (auto simp: image_def Fpow_def)
  show ?thesis
    apply (rule subset_image_lepoll [where f = "\<lambda>U x. if \<exists>y. (x,y) \<in> U then @y. (x,y) \<in> U else k x"])
    using * by (auto simp: image_def)
qed

lemma singleton_lepoll: "{x} \<lesssim> insert y A"
  by (force simp: lepoll_def)

lemma singleton_eqpoll: "{x} \<approx> {y}"
  by (blast intro: lepoll_antisym singleton_lepoll)

lemma subset_singleton_iff_lepoll: "(\<exists>x. S \<subseteq> {x}) \<longleftrightarrow> S \<lesssim> {()}"
  using lepoll_iff by fastforce

lemma infinite_insert_lepoll:
  assumes "infinite A" shows "insert a A \<lesssim> A"
proof -
  obtain f :: "nat \<Rightarrow> 'a" where "inj f" and f: "range f \<subseteq> A"
    using assms infinite_countable_subset by blast
  let ?g = "(\<lambda>z. if z=a then f 0 else if z \<in> range f then f (Suc (inv f z)) else z)"
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on ?g (insert a A)"
      using inj_on_eq_iff [OF \<open>inj f\<close>]
      by (auto simp: inj_on_def)
    show "?g ` insert a A \<subseteq> A"
      using f by auto
  qed
qed

lemma infinite_insert_eqpoll: "infinite A \<Longrightarrow> insert a A \<approx> A"
  by (simp add: lepoll_antisym infinite_insert_lepoll subset_imp_lepoll subset_insertI)

lemma finite_lepoll_infinite:
  assumes "infinite A" "finite B" shows "B \<lesssim> A"
proof -
  have "B \<lesssim> (UNIV::nat set)"
    unfolding lepoll_def
    using finite_imp_inj_to_nat_seg [OF \<open>finite B\<close>] by blast
  then show ?thesis
    using \<open>infinite A\<close> infinite_le_lepoll lepoll_trans by auto
qed

lemma countable_lepoll: "\<lbrakk>countable A; B \<lesssim> A\<rbrakk> \<Longrightarrow> countable B"
  by (meson countable_image countable_subset lepoll_iff)

lemma countable_eqpoll: "\<lbrakk>countable A; B \<approx> A\<rbrakk> \<Longrightarrow> countable B"
  using countable_lepoll eqpoll_imp_lepoll by blast

subsection\<open>The strict relation\<close>

lemma lesspoll_not_refl [iff]: "~ (i \<prec> i)"
  by (simp add: lepoll_antisym lesspoll_def)

lemma lesspoll_imp_lepoll: "A \<prec> B ==> A \<lesssim> B"
by (unfold lesspoll_def, blast)

lemma lepoll_iff_leqpoll: "A \<lesssim> B \<longleftrightarrow> A \<prec> B | A \<approx> B"
  using eqpoll_imp_lepoll lesspoll_def by blast

lemma lesspoll_trans [trans]: "\<lbrakk>X \<prec> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (meson eqpoll_sym lepoll_antisym lepoll_trans lepoll_trans1 lesspoll_def)

lemma lesspoll_trans1 [trans]: "\<lbrakk>X \<lesssim> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (meson eqpoll_sym lepoll_antisym lepoll_trans lepoll_trans1 lesspoll_def)

lemma lesspoll_trans2 [trans]: "\<lbrakk>X \<prec> Y; Y \<lesssim> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (meson eqpoll_imp_lepoll eqpoll_sym lepoll_antisym lepoll_trans lesspoll_def)

lemma eq_lesspoll_trans [trans]: "\<lbrakk>X \<approx> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  using eqpoll_imp_lepoll lesspoll_trans1 by blast

lemma lesspoll_eq_trans [trans]: "\<lbrakk>X \<prec> Y; Y \<approx> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  using eqpoll_imp_lepoll lesspoll_trans2 by blast

lemma lesspoll_Pow_self: "A \<prec> Pow A"
  unfolding lesspoll_def bij_betw_def eqpoll_def
  by (meson lepoll_Pow_self Cantors_theorem)

lemma finite_lesspoll_infinite:
  assumes "infinite A" "finite B" shows "B \<prec> A"
  by (meson assms eqpoll_finite_iff finite_lepoll_infinite lesspoll_def)

lemma countable_lesspoll: "\<lbrakk>countable A; B \<prec> A\<rbrakk> \<Longrightarrow> countable B"
  using countable_lepoll lesspoll_def by blast

lemma lepoll_iff_card_le: "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> A \<lesssim> B \<longleftrightarrow> card A \<le> card B"
  by (simp add: inj_on_iff_card_le lepoll_def)

lemma lepoll_iff_finite_card: "A \<lesssim> {..<n::nat} \<longleftrightarrow> finite A \<and> card A \<le> n"
  by (metis card_lessThan finite_lessThan finite_surj lepoll_iff lepoll_iff_card_le)

lemma eqpoll_iff_finite_card: "A \<approx> {..<n::nat} \<longleftrightarrow> finite A \<and> card A = n"
  by (metis card_lessThan eqpoll_finite_iff eqpoll_iff_card finite_lessThan)

lemma lesspoll_iff_finite_card: "A \<prec> {..<n::nat} \<longleftrightarrow> finite A \<and> card A < n"
  by (metis eqpoll_iff_finite_card lepoll_iff_finite_card lesspoll_def order_less_le)

subsection\<open>Mapping by an injection\<close>

lemma inj_on_image_eqpoll_self: "inj_on f A \<Longrightarrow> f ` A \<approx> A"
  by (meson bij_betw_def eqpoll_def eqpoll_sym)

lemma inj_on_image_lepoll_1 [simp]:
  assumes "inj_on f A" shows "f ` A \<lesssim> B \<longleftrightarrow> A \<lesssim> B"
  by (meson assms image_lepoll lepoll_def lepoll_trans order_refl)

lemma inj_on_image_lepoll_2 [simp]:
  assumes "inj_on f B" shows "A \<lesssim> f ` B \<longleftrightarrow> A \<lesssim> B"
  by (meson assms eq_iff image_lepoll lepoll_def lepoll_trans)

lemma inj_on_image_lesspoll_1 [simp]:
  assumes "inj_on f A" shows "f ` A \<prec> B \<longleftrightarrow> A \<prec> B"
  by (meson assms image_lepoll le_less lepoll_def lesspoll_trans1)

lemma inj_on_image_lesspoll_2 [simp]:
  assumes "inj_on f B" shows "A \<prec> f ` B \<longleftrightarrow> A \<prec> B"
  by (meson assms eqpoll_sym inj_on_image_eqpoll_self lesspoll_eq_trans)

lemma inj_on_image_eqpoll_1 [simp]:
  assumes "inj_on f A" shows "f ` A \<approx> B \<longleftrightarrow> A \<approx> B"
  by (metis assms eqpoll_trans inj_on_image_eqpoll_self eqpoll_sym)

lemma inj_on_image_eqpoll_2 [simp]:
  assumes "inj_on f B" shows "A \<approx> f ` B \<longleftrightarrow> A \<approx> B"
  by (metis assms inj_on_image_eqpoll_1 eqpoll_sym)

subsection \<open>Inserting elements into sets\<close>

lemma insert_lepoll_insertD:
  assumes "insert u A \<lesssim> insert v B" "u \<notin> A" "v \<notin> B" shows "A \<lesssim> B"
proof -
  obtain f where inj: "inj_on f (insert u A)" and fim: "f ` (insert u A) \<subseteq> insert v B"
    by (meson assms lepoll_def)
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    let ?g = "\<lambda>x\<in>A. if f x = v then f u else f x"
    show "inj_on ?g A"
      using inj \<open>u \<notin> A\<close> by (auto simp: inj_on_def)
    show "?g ` A \<subseteq> B"
      using fim \<open>u \<notin> A\<close> image_subset_iff inj inj_on_image_mem_iff by fastforce
  qed
qed

lemma insert_eqpoll_insertD: "\<lbrakk>insert u A \<approx> insert v B; u \<notin> A; v \<notin> B\<rbrakk> \<Longrightarrow> A \<approx> B"
  by (meson insert_lepoll_insertD eqpoll_imp_lepoll eqpoll_sym lepoll_antisym)

lemma insert_lepoll_cong:
  assumes "A \<lesssim> B" "b \<notin> B" shows "insert a A \<lesssim> insert b B"
proof -
  obtain f where f: "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  let ?f = "\<lambda>u \<in> insert a A. if u=a then b else f u"
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on ?f (insert a A)"
      using f \<open>b \<notin> B\<close> by (auto simp: inj_on_def)
    show "?f ` insert a A \<subseteq> insert b B"
      using f \<open>b \<notin> B\<close> by auto
  qed
qed

lemma insert_eqpoll_cong:
     "\<lbrakk>A \<approx> B; a \<notin> A; b \<notin> B\<rbrakk> \<Longrightarrow> insert a A \<approx> insert b B"
  by (meson eqpoll_imp_lepoll eqpoll_sym insert_lepoll_cong lepoll_antisym)

lemma insert_eqpoll_insert_iff:
     "\<lbrakk>a \<notin> A; b \<notin> B\<rbrakk> \<Longrightarrow> insert a A \<approx> insert b B  \<longleftrightarrow>  A \<approx> B"
  by (meson insert_eqpoll_insertD insert_eqpoll_cong)

lemma insert_lepoll_insert_iff:
     " \<lbrakk>a \<notin> A; b \<notin> B\<rbrakk> \<Longrightarrow> (insert a A \<lesssim> insert b B) \<longleftrightarrow> (A \<lesssim> B)"
  by (meson insert_lepoll_insertD insert_lepoll_cong)

lemma less_imp_insert_lepoll:
  assumes "A \<prec> B" shows "insert a A \<lesssim> B"
proof -
  obtain f where "inj_on f A" "f ` A \<subset> B"
    using assms by (metis bij_betw_def eqpoll_def lepoll_def lesspoll_def psubset_eq)
  then obtain b where b: "b \<in> B" "b \<notin> f ` A"
    by auto
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on (f(a:=b)) (insert a A)"
      using b \<open>inj_on f A\<close> by (auto simp: inj_on_def)
    show "(f(a:=b)) ` insert a A \<subseteq> B"
      using \<open>f ` A \<subset> B\<close>  by (auto simp: b)
  qed
qed

lemma finite_insert_lepoll: "finite A \<Longrightarrow> (insert a A \<lesssim> A) \<longleftrightarrow> (a \<in> A)"
proof (induction A rule: finite_induct)
  case (insert x A)
  then show ?case
    by (metis insertI2 insert_lepoll_insert_iff insert_subsetI lepoll_trans subsetI subset_imp_lepoll)
qed auto


subsection\<open>Binary sums and unions\<close>

lemma Un_lepoll_mono:
  assumes "A \<lesssim> C" "B \<lesssim> D" "disjnt C D" shows "A \<union> B \<lesssim> C \<union> D"
proof -
  obtain f g where inj: "inj_on f A" "inj_on g B" and fg: "f ` A \<subseteq> C" "g ` B \<subseteq> D"
    by (meson assms lepoll_def)
  have "inj_on (\<lambda>x. if x \<in> A then f x else g x) (A \<union> B)"
    using inj \<open>disjnt C D\<close> fg unfolding disjnt_iff
    by (fastforce intro: inj_onI dest: inj_on_contraD split: if_split_asm)
  with fg show ?thesis
    unfolding lepoll_def
    by (rule_tac x="\<lambda>x. if x \<in> A then f x else g x" in exI) auto
qed

lemma Un_eqpoll_cong: "\<lbrakk>A \<approx> C; B \<approx> D; disjnt A B; disjnt C D\<rbrakk> \<Longrightarrow> A \<union> B \<approx> C \<union> D"
  by (meson Un_lepoll_mono eqpoll_imp_lepoll eqpoll_sym lepoll_antisym)

lemma sum_lepoll_mono:
  assumes "A \<lesssim> C" "B \<lesssim> D" shows "A <+> B \<lesssim> C <+> D"
proof -
  obtain f g where "inj_on f A" "f ` A \<subseteq> C" "inj_on g B" "g ` B \<subseteq> D"
    by (meson assms lepoll_def)
  then show ?thesis
    unfolding lepoll_def
    by (rule_tac x="case_sum (Inl \<circ> f) (Inr \<circ> g)" in exI) (force simp: inj_on_def)
qed

lemma sum_eqpoll_cong: "\<lbrakk>A \<approx> C; B \<approx> D\<rbrakk> \<Longrightarrow> A <+> B \<approx> C <+> D"
  by (meson eqpoll_imp_lepoll eqpoll_sym lepoll_antisym sum_lepoll_mono)

subsection\<open>Binary Cartesian products\<close>

lemma times_square_lepoll: "A \<lesssim> A \<times> A"
  unfolding lepoll_def inj_def
proof (intro exI conjI)
  show "inj_on (\<lambda>x. (x,x)) A"
    by (auto simp: inj_on_def)
qed auto

lemma times_commute_eqpoll: "A \<times> B \<approx> B \<times> A"
  unfolding eqpoll_def
  by (force intro: bij_betw_byWitness [where f = "\<lambda>(x,y). (y,x)" and f' = "\<lambda>(x,y). (y,x)"])

lemma times_assoc_eqpoll: "(A \<times> B) \<times> C \<approx> A \<times> (B \<times> C)"
  unfolding eqpoll_def
  by (force intro: bij_betw_byWitness [where f = "\<lambda>((x,y),z). (x,(y,z))" and f' = "\<lambda>(x,(y,z)). ((x,y),z)"])

lemma times_singleton_eqpoll: "{a} \<times> A \<approx> A"
proof -
  have "{a} \<times> A = (\<lambda>x. (a,x)) ` A"
    by auto
  also have "\<dots>  \<approx> A"
    proof (rule inj_on_image_eqpoll_self)
      show "inj_on (Pair a) A"
        by (auto simp: inj_on_def)
    qed
    finally show ?thesis .
qed

lemma times_lepoll_mono:
  assumes "A \<lesssim> C" "B \<lesssim> D" shows "A \<times> B \<lesssim> C \<times> D"
proof -
  obtain f g where "inj_on f A" "f ` A \<subseteq> C" "inj_on g B" "g ` B \<subseteq> D"
    by (meson assms lepoll_def)
  then show ?thesis
    unfolding lepoll_def
    by (rule_tac x="\<lambda>(x,y). (f x, g y)" in exI) (auto simp: inj_on_def)
qed

lemma times_eqpoll_cong: "\<lbrakk>A \<approx> C; B \<approx> D\<rbrakk> \<Longrightarrow> A \<times> B \<approx> C \<times> D"
  by (metis eqpoll_imp_lepoll eqpoll_sym lepoll_antisym times_lepoll_mono)

lemma
  assumes "B \<noteq> {}" shows lepoll_times1: "A \<lesssim> A \<times> B" and lepoll_times2:  "A \<lesssim> B \<times> A"
  using assms lepoll_iff by fastforce+

lemma times_0_eqpoll: "{} \<times> A \<approx> {}"
  by (simp add: eqpoll_iff_bijections)

lemma Sigma_inj_lepoll_mono:
  assumes h: "inj_on h A" "h ` A \<subseteq> C" and "\<And>x. x \<in> A \<Longrightarrow> B x \<lesssim> D (h x)" 
  shows "Sigma A B \<lesssim> Sigma C D"
proof -
  have "\<And>x. x \<in> A \<Longrightarrow> \<exists>f. inj_on f (B x) \<and> f ` (B x) \<subseteq> D (h x)"
    by (meson assms lepoll_def)
  then obtain f where  "\<And>x. x \<in> A \<Longrightarrow> inj_on (f x) (B x) \<and> f x ` B x \<subseteq> D (h x)"
    by metis
  with h show ?thesis
    unfolding lepoll_def inj_on_def
    by (rule_tac x="\<lambda>(x,y). (h x, f x y)" in exI) force
qed

lemma Sigma_lepoll_mono:
  assumes "A \<subseteq> C" "\<And>x. x \<in> A \<Longrightarrow> B x \<lesssim> D x" shows "Sigma A B \<lesssim> Sigma C D"
  using Sigma_inj_lepoll_mono [of id] assms by auto

lemma sum_times_distrib_eqpoll: "(A <+> B) \<times> C \<approx> (A \<times> C) <+> (B \<times> C)"
  unfolding eqpoll_def
proof
  show "bij_betw (\<lambda>(x,z). case_sum(\<lambda>y. Inl(y,z)) (\<lambda>y. Inr(y,z)) x) ((A <+> B) \<times> C) (A \<times> C <+> B \<times> C)"
    by (rule bij_betw_byWitness [where f' = "case_sum (\<lambda>(x,z). (Inl x, z)) (\<lambda>(y,z). (Inr y, z))"]) auto
qed

lemma Sigma_eqpoll_cong:
  assumes h: "bij_betw h A C"  and BD: "\<And>x. x \<in> A \<Longrightarrow> B x \<approx> D (h x)" 
  shows "Sigma A B \<approx> Sigma C D"
proof (intro lepoll_antisym)
  show "Sigma A B \<lesssim> Sigma C D"
    by (metis Sigma_inj_lepoll_mono bij_betw_def eqpoll_imp_lepoll subset_refl assms)
  have "inj_on (inv_into A h) C \<and> inv_into A h ` C \<subseteq> A"
    by (metis bij_betw_def bij_betw_inv_into h set_eq_subset)
  then show "Sigma C D \<lesssim> Sigma A B"
    by (smt (verit, best) BD Sigma_inj_lepoll_mono bij_betw_inv_into_right eqpoll_sym h image_subset_iff lepoll_refl lepoll_trans2)
qed

lemma prod_insert_eqpoll:
  assumes "a \<notin> A" shows "insert a A \<times> B \<approx> B <+> A \<times> B"
  unfolding eqpoll_def
  proof
  show "bij_betw (\<lambda>(x,y). if x=a then Inl y else Inr (x,y)) (insert a A \<times> B) (B <+> A \<times> B)"
    by (rule bij_betw_byWitness [where f' = "case_sum (\<lambda>y. (a,y)) id"]) (auto simp: assms)
qed

subsection\<open>General Unions\<close>

lemma Union_eqpoll_Times:
  assumes B: "\<And>x. x \<in> A \<Longrightarrow> F x \<approx> B" and disj: "pairwise (\<lambda>x y. disjnt (F x) (F y)) A"
  shows "(\<Union>x\<in>A. F x) \<approx> A \<times> B"
proof (rule lepoll_antisym)
  obtain b where b: "\<And>x. x \<in> A \<Longrightarrow> bij_betw (b x) (F x) B"
    using B unfolding eqpoll_def by metis
  show "\<Union>(F ` A) \<lesssim> A \<times> B"
    unfolding lepoll_def
  proof (intro exI conjI)
    define \<chi> where "\<chi> \<equiv> \<lambda>z. THE x. x \<in> A \<and> z \<in> F x"
    have \<chi>: "\<chi> z = x" if "x \<in> A" "z \<in> F x" for x z
      unfolding \<chi>_def
      by (smt (verit, best) disj disjnt_iff pairwiseD that(1,2) theI_unique)
    let ?f = "\<lambda>z. (\<chi> z, b (\<chi> z) z)"
    show "inj_on ?f (\<Union>(F ` A))"
      unfolding inj_on_def
      by clarify (metis \<chi> b bij_betw_inv_into_left)
    show "?f ` \<Union>(F ` A) \<subseteq> A \<times> B"
      using \<chi> b bij_betwE by blast
  qed
  show "A \<times> B \<lesssim> \<Union>(F ` A)"
    unfolding lepoll_def
  proof (intro exI conjI)
    let ?f = "\<lambda>(x,y). inv_into (F x) (b x) y"
    have *: "inv_into (F x) (b x) y \<in> F x" if "x \<in> A" "y \<in> B" for x y
      by (metis b bij_betw_imp_surj_on inv_into_into that)
    then show "inj_on ?f (A \<times> B)"
      unfolding inj_on_def
      by clarsimp (metis (mono_tags, lifting) b bij_betw_inv_into_right disj disjnt_iff pairwiseD)
    show "?f ` (A \<times> B) \<subseteq> \<Union> (F ` A)"
      by clarsimp (metis b bij_betw_imp_surj_on inv_into_into)
  qed
qed

lemma UN_lepoll_UN:
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> B x \<lesssim> C x"
    and disj: "pairwise (\<lambda>x y. disjnt (C x) (C y)) A"
  shows "\<Union> (B`A) \<lesssim> \<Union> (C`A)"
proof -
  obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> inj_on (f x) (B x) \<and> f x ` (B x) \<subseteq> (C x)"
    using A unfolding lepoll_def by metis
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    define \<chi> where "\<chi> \<equiv> \<lambda>z. @x. x \<in> A \<and> z \<in> B x"
    have \<chi>: "\<chi> z \<in> A \<and> z \<in> B (\<chi> z)" if "x \<in> A" "z \<in> B x" for x z
      unfolding \<chi>_def by (metis (mono_tags, lifting) someI_ex that)
    let ?f = "\<lambda>z. (f (\<chi> z) z)"
    show "inj_on ?f (\<Union>(B ` A))"
      using disj f unfolding inj_on_def disjnt_iff pairwise_def image_subset_iff
      by (metis UN_iff \<chi>)
    show "?f ` \<Union> (B ` A) \<subseteq> \<Union> (C ` A)"
      using \<chi> f unfolding image_subset_iff by blast
  qed
qed

lemma UN_eqpoll_UN:
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> B x \<approx> C x"
    and B: "pairwise (\<lambda>x y. disjnt (B x) (B y)) A"
    and C: "pairwise (\<lambda>x y. disjnt (C x) (C y)) A"
  shows "(\<Union>x\<in>A. B x) \<approx> (\<Union>x\<in>A. C x)"
proof (rule lepoll_antisym)
  show "\<Union> (B ` A) \<lesssim> \<Union> (C ` A)"
    by (meson A C UN_lepoll_UN eqpoll_imp_lepoll)
  show "\<Union> (C ` A) \<lesssim> \<Union> (B ` A)"
    by (simp add: A B UN_lepoll_UN eqpoll_imp_lepoll eqpoll_sym)
qed

subsection\<open>General Cartesian products (Pi)\<close>

lemma PiE_sing_eqpoll_self: "({a} \<rightarrow>\<^sub>E B) \<approx> B"
proof -
  have 1: "x = y"
    if "x \<in> {a} \<rightarrow>\<^sub>E B" "y \<in> {a} \<rightarrow>\<^sub>E B" "x a = y a" for x y
    by (metis IntD2 PiE_def extensionalityI singletonD that)
  have 2: "x \<in> (\<lambda>h. h a) ` ({a} \<rightarrow>\<^sub>E B)" if "x \<in> B" for x
    using that by (rule_tac x="\<lambda>z\<in>{a}. x" in image_eqI) auto
  show ?thesis
  unfolding eqpoll_def bij_betw_def inj_on_def
  by (force intro: 1 2)
qed

lemma lepoll_funcset_right:
  assumes "B \<lesssim> B'" shows "A \<rightarrow>\<^sub>E B \<lesssim> A \<rightarrow>\<^sub>E B'"
proof -
  obtain f where f: "inj_on f B" "f ` B \<subseteq> B'"
    by (meson assms lepoll_def)
  let ?G = "\<lambda>g. \<lambda>z \<in> A. f(g z)"
  have "inj_on ?G (A \<rightarrow>\<^sub>E B)"
    using f by (smt (verit, best) PiE_ext PiE_mem inj_on_def restrict_apply')
  moreover have "?G ` (A \<rightarrow>\<^sub>E B) \<subseteq> (A \<rightarrow>\<^sub>E B')"
    using f by fastforce
  ultimately show ?thesis
    by (meson lepoll_def)
qed

lemma lepoll_funcset_left:
  assumes "B \<noteq> {}" "A \<lesssim> A'"
  shows "A \<rightarrow>\<^sub>E B \<lesssim> A' \<rightarrow>\<^sub>E B"
proof -
  obtain b where "b \<in> B"
    using assms by blast
  obtain f where "inj_on f A" and fim: "f ` A \<subseteq> A'"
    using assms by (auto simp: lepoll_def)
  then obtain h where h: "\<And>x. x \<in> A \<Longrightarrow> h (f x) = x"
    using the_inv_into_f_f by fastforce
  let ?F = "\<lambda>g. \<lambda>u \<in> A'. if h u \<in> A then g(h u) else b"
  show ?thesis
    unfolding lepoll_def inj_on_def
  proof (intro exI conjI ballI impI ext)
    fix k l x
    assume k: "k \<in> A \<rightarrow>\<^sub>E B" and l: "l \<in> A \<rightarrow>\<^sub>E B" and "?F k = ?F l"
    then have "?F k (f x) = ?F l (f x)"
      by simp
    then show "k x = l x"
      by (smt (verit, best) PiE_arb fim h image_subset_iff k l restrict_apply')
  next
    show "?F ` (A \<rightarrow>\<^sub>E B) \<subseteq> A' \<rightarrow>\<^sub>E B"
      using \<open>b \<in> B\<close> by force
  qed
qed

lemma lepoll_funcset:
   "\<lbrakk>B \<noteq> {}; A \<lesssim> A'; B \<lesssim> B'\<rbrakk> \<Longrightarrow> A \<rightarrow>\<^sub>E B \<lesssim> A' \<rightarrow>\<^sub>E B'"
  by (rule lepoll_trans [OF lepoll_funcset_right lepoll_funcset_left]) auto

lemma lepoll_PiE:
  assumes "\<And>i. i \<in> A \<Longrightarrow> B i \<lesssim> C i"
  shows "PiE A B \<lesssim> PiE A C"
proof -
  obtain f where f: "\<And>i. i \<in> A \<Longrightarrow> inj_on (f i) (B i) \<and> (f i) ` B i \<subseteq> C i"
    using assms unfolding lepoll_def by metis
  let ?G = "\<lambda>g. \<lambda>i \<in> A. f i (g i)"
  have "inj_on ?G (PiE A B)"
    by (smt (verit, ccfv_SIG) PiE_ext PiE_iff f inj_on_def restrict_apply')
  moreover have "?G ` (PiE A B) \<subseteq> (PiE A C)"
    using f by fastforce
  ultimately show ?thesis
    by (meson lepoll_def)
qed


lemma card_le_PiE_subindex:
  assumes "A \<subseteq> A'" "Pi\<^sub>E A' B \<noteq> {}"
  shows "PiE A B \<lesssim> PiE A' B"
proof -
  have "\<And>x. x \<in> A' \<Longrightarrow> \<exists>y. y \<in> B x"
    using assms by blast
  then obtain g where g: "\<And>x. x \<in> A' \<Longrightarrow> g x \<in> B x"
    by metis
  let ?F = "\<lambda>f x. if x \<in> A then f x else if x \<in> A' then g x else undefined"
  have "Pi\<^sub>E A B \<subseteq> (\<lambda>f. restrict f A) ` Pi\<^sub>E A' B"
  proof
    show "f \<in> Pi\<^sub>E A B \<Longrightarrow> f \<in> (\<lambda>f. restrict f A) ` Pi\<^sub>E A' B" for f
      using \<open>A \<subseteq> A'\<close>
      by (rule_tac x="?F f" in image_eqI) (auto simp: g fun_eq_iff)
  qed
  then have "Pi\<^sub>E A B \<lesssim> (\<lambda>f. \<lambda>i \<in> A. f i) ` Pi\<^sub>E A' B"
    by (simp add: subset_imp_lepoll)
  also have "\<dots> \<lesssim> PiE A' B"
    by (rule image_lepoll)
  finally show ?thesis .
qed


lemma finite_restricted_funspace:
  assumes "finite A" "finite B"
  shows "finite {f. f ` A \<subseteq> B \<and> {x. f x \<noteq> k x} \<subseteq> A}" (is "finite ?F")
proof (rule finite_subset)
  show "finite ((\<lambda>U x. if \<exists>y. (x,y) \<in> U then @y. (x,y) \<in> U else k x) ` Pow(A \<times> B))" (is "finite ?G")
    using assms by auto
  show "?F \<subseteq> ?G"
  proof
    fix f
    assume "f \<in> ?F"
    then show "f \<in> ?G"
      by (rule_tac x="(\<lambda>x. (x,f x)) ` {x. f x \<noteq> k x}" in image_eqI) (auto simp: fun_eq_iff image_def)
  qed
qed


proposition finite_PiE_iff:
   "finite(PiE I S) \<longleftrightarrow> PiE I S = {} \<or> finite {i \<in> I. ~(\<exists>a. S i \<subseteq> {a})} \<and> (\<forall>i \<in> I. finite(S i))"
 (is "?lhs = ?rhs")
proof (cases "PiE I S = {}")
  case False
  define J where "J \<equiv> {i \<in> I. \<nexists>a. S i \<subseteq> {a}}"
  show ?thesis
  proof
    assume L: ?lhs
    have "infinite (Pi\<^sub>E I S)" if "infinite J"
    proof -
      have "(UNIV::nat set) \<lesssim> (UNIV::(nat\<Rightarrow>bool) set)"
      proof -
        have "\<forall>N::nat set. inj_on (=) N"
          by (simp add: inj_on_def)
        then show ?thesis
          by (meson infinite_iff_countable_subset infinite_le_lepoll top.extremum)
      qed
      also have "\<dots> = (UNIV::nat set) \<rightarrow>\<^sub>E (UNIV::bool set)"
        by auto
      also have "\<dots> \<lesssim> J \<rightarrow>\<^sub>E (UNIV::bool set)"
        by (metis empty_not_UNIV infinite_le_lepoll lepoll_funcset_left that)
      also have "\<dots> \<lesssim> Pi\<^sub>E J S"
      proof -
        have *: "(UNIV::bool set) \<lesssim> S i" if "i \<in> I" and \<section>: "\<forall>a. \<not> S i \<subseteq> {a}" for i
        proof -
          obtain a b where "{a,b} \<subseteq> S i" "a \<noteq> b"
            by (metis \<section> empty_subsetI insert_subset subsetI)
          then show ?thesis
            by (metis Set.set_insert UNIV_bool insert_iff insert_lepoll_cong insert_subset singleton_lepoll)
        qed
        show ?thesis
          by (auto simp: * J_def intro: lepoll_PiE)
      qed
      also have "\<dots> \<lesssim> Pi\<^sub>E I S"
        using False by (auto simp: J_def intro: card_le_PiE_subindex)
      finally have "(UNIV::nat set) \<lesssim> Pi\<^sub>E I S" .
      then show ?thesis
        by (simp add: infinite_le_lepoll)
    qed
    moreover have "finite (S i)" if "i \<in> I" for i
    proof (rule finite_subset)
      obtain f where f: "f \<in> PiE I S"
        using False by blast
      show "S i \<subseteq> (\<lambda>f. f i) ` Pi\<^sub>E I S"
      proof
        show "s \<in> (\<lambda>f. f i) ` Pi\<^sub>E I S" if "s \<in> S i" for s
          using that f \<open>i \<in> I\<close>
          by (rule_tac x="\<lambda>j. if j = i then s else f j" in image_eqI) auto
      qed
    next
      show "finite ((\<lambda>x. x i) ` Pi\<^sub>E I S)"
        using L by blast
    qed
    ultimately show ?rhs
      using L
      by (auto simp: J_def False)
  next
    assume R: ?rhs
    have "\<forall>i \<in> I - J. \<exists>a. S i = {a}"
      using False J_def by blast
    then obtain a where a: "\<forall>i \<in> I - J. S i = {a i}"
      by metis
    let ?F = "{f. f ` J \<subseteq> (\<Union>i \<in> J. S i) \<and> {i. f i \<noteq> (if i \<in> I then a i else undefined)} \<subseteq> J}"
    have *: "finite (Pi\<^sub>E I S)"
      if "finite J" and "\<forall>i\<in>I. finite (S i)"
    proof (rule finite_subset)
      have "\<And>f j. \<lbrakk>f \<in> Pi\<^sub>E I S; j \<in> J\<rbrakk> \<Longrightarrow> f j \<in> \<Union> (S ` J)"
        using J_def by blast
      moreover
      have "\<And>f j. \<lbrakk>f \<in> Pi\<^sub>E I S; f j \<noteq> (if j \<in> I then a j else undefined)\<rbrakk> \<Longrightarrow> j \<in> J"
        by (metis DiffI PiE_E a singletonD)
      ultimately show "Pi\<^sub>E I S \<subseteq> ?F" by force
      show "finite ?F"
      proof (rule finite_restricted_funspace [OF \<open>finite J\<close>])
        show "finite (\<Union> (S ` J))"
          using that J_def by blast
      qed
  qed
  show ?lhs
      using R by (auto simp: * J_def)
  qed
qed auto


corollary finite_funcset_iff:
  "finite(I \<rightarrow>\<^sub>E S) \<longleftrightarrow> (\<exists>a. S \<subseteq> {a}) \<or> I = {} \<or> finite I \<and> finite S"
  by (fastforce simp: finite_PiE_iff PiE_eq_empty_iff dest: subset_singletonD)

subsection \<open>Misc other resultd\<close>

lemma lists_lepoll_mono:
  assumes "A \<lesssim> B" shows "lists A \<lesssim> lists B"
proof -
  obtain f where f: "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  moreover have "inj_on (map f) (lists A)"
    using f unfolding inj_on_def
    by clarsimp (metis list.inj_map_strong)
  ultimately show ?thesis
    unfolding lepoll_def by force
qed

lemma lepoll_lists: "A \<lesssim> lists A"
  unfolding lepoll_def inj_on_def by(rule_tac x="\<lambda>x. [x]" in exI) auto

text \<open>Dedekind's definition of infinite set\<close>

lemma infinite_iff_psubset: "infinite A \<longleftrightarrow> (\<exists>B. B \<subset> A \<and> A\<approx>B)"
proof
  assume "infinite A"
  then obtain f :: "nat \<Rightarrow> 'a" where "inj f" and f: "range f \<subseteq> A"
    by (meson infinite_countable_subset)
  define C where "C \<equiv> A - range f"
  have C: "A = range f \<union> C" "range f \<inter> C = {}"
    using f by (auto simp: C_def)
  have *: "range (f \<circ> Suc) \<subset> range f"
    using inj_eq [OF \<open>inj f\<close>] by (fastforce simp: set_eq_iff)
  have "range f \<union> C \<approx> range (f \<circ> Suc) \<union> C"
  proof (intro Un_eqpoll_cong)
    show "range f \<approx> range (f \<circ> Suc)"
      by (meson \<open>inj f\<close> eqpoll_refl inj_Suc inj_compose inj_on_image_eqpoll_2)
    show "disjnt (range f) C"
      by (simp add: C disjnt_def)
    then show "disjnt (range (f \<circ> Suc)) C"
      using "*" disjnt_subset1 by blast
  qed auto
  moreover have "range (f \<circ> Suc) \<union> C \<subset> A"
    using "*" f C_def by blast
  ultimately show "\<exists>B\<subset>A. A \<approx> B"
    by (metis C(1))
next
  assume "\<exists>B\<subset>A. A \<approx> B" then show "infinite A"
    by (metis card_subset_eq eqpoll_finite_iff eqpoll_iff_card psubsetE)
qed

lemma infinite_iff_psubset_le: "infinite A \<longleftrightarrow> (\<exists>B. B \<subset> A \<and> A \<lesssim> B)"
  by (meson eqpoll_imp_lepoll infinite_iff_psubset lepoll_antisym psubsetE subset_imp_lepoll)

end
