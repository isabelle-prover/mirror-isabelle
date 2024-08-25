(*  Title:      HOL/Orderings.thy
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

section \<open>Abstract orderings\<close>

theory Orderings
imports HOL
keywords "print_orders" :: diag
begin

subsection \<open>Abstract ordering\<close>

locale partial_preordering =
  fixes less_eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<le>\<close> 50)
  assumes refl: \<open>a \<^bold>\<le> a\<close> \<comment> \<open>not \<open>iff\<close>: makes problems due to multiple (dual) interpretations\<close>
    and trans: \<open>a \<^bold>\<le> b \<Longrightarrow> b \<^bold>\<le> c \<Longrightarrow> a \<^bold>\<le> c\<close>

locale preordering = partial_preordering +
  fixes less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<^bold><\<close> 50)
  assumes strict_iff_not: \<open>a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> \<not> b \<^bold>\<le> a\<close>
begin

lemma strict_implies_order:
  \<open>a \<^bold>< b \<Longrightarrow> a \<^bold>\<le> b\<close>
  by (simp add: strict_iff_not)

lemma irrefl: \<comment> \<open>not \<open>iff\<close>: makes problems due to multiple (dual) interpretations\<close>
  \<open>\<not> a \<^bold>< a\<close>
  by (simp add: strict_iff_not)

lemma asym:
  \<open>a \<^bold>< b \<Longrightarrow> b \<^bold>< a \<Longrightarrow> False\<close>
  by (auto simp add: strict_iff_not)

lemma strict_trans1:
  \<open>a \<^bold>\<le> b \<Longrightarrow> b \<^bold>< c \<Longrightarrow> a \<^bold>< c\<close>
  by (auto simp add: strict_iff_not intro: trans)

lemma strict_trans2:
  \<open>a \<^bold>< b \<Longrightarrow> b \<^bold>\<le> c \<Longrightarrow> a \<^bold>< c\<close>
  by (auto simp add: strict_iff_not intro: trans)

lemma strict_trans:
  \<open>a \<^bold>< b \<Longrightarrow> b \<^bold>< c \<Longrightarrow> a \<^bold>< c\<close>
  by (auto intro: strict_trans1 strict_implies_order)

end

lemma preordering_strictI: \<comment> \<open>Alternative introduction rule with bias towards strict order\<close>
  fixes less_eq (infix \<open>\<^bold>\<le>\<close> 50)
    and less (infix \<open>\<^bold><\<close> 50)
  assumes less_eq_less: \<open>\<And>a b. a \<^bold>\<le> b \<longleftrightarrow> a \<^bold>< b \<or> a = b\<close>
    assumes asym: \<open>\<And>a b. a \<^bold>< b \<Longrightarrow> \<not> b \<^bold>< a\<close>
  assumes irrefl: \<open>\<And>a. \<not> a \<^bold>< a\<close>
  assumes trans: \<open>\<And>a b c. a \<^bold>< b \<Longrightarrow> b \<^bold>< c \<Longrightarrow> a \<^bold>< c\<close>
  shows \<open>preordering (\<^bold>\<le>) (\<^bold><)\<close>
proof
  fix a b
  show \<open>a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> \<not> b \<^bold>\<le> a\<close>
    by (auto simp add: less_eq_less asym irrefl)
next
  fix a
  show \<open>a \<^bold>\<le> a\<close>
    by (auto simp add: less_eq_less)
next
  fix a b c
  assume \<open>a \<^bold>\<le> b\<close> and \<open>b \<^bold>\<le> c\<close> then show \<open>a \<^bold>\<le> c\<close>
    by (auto simp add: less_eq_less intro: trans)
qed

lemma preordering_dualI:
  fixes less_eq (infix \<open>\<^bold>\<le>\<close> 50)
    and less (infix \<open>\<^bold><\<close> 50)
  assumes \<open>preordering (\<lambda>a b. b \<^bold>\<le> a) (\<lambda>a b. b \<^bold>< a)\<close>
  shows \<open>preordering (\<^bold>\<le>) (\<^bold><)\<close>
proof -
  from assms interpret preordering \<open>\<lambda>a b. b \<^bold>\<le> a\<close> \<open>\<lambda>a b. b \<^bold>< a\<close> .
  show ?thesis
    by standard (auto simp: strict_iff_not refl intro: trans)
qed

locale ordering = partial_preordering +
  fixes less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<^bold><\<close> 50)
  assumes strict_iff_order: \<open>a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b\<close>
  assumes antisym: \<open>a \<^bold>\<le> b \<Longrightarrow> b \<^bold>\<le> a \<Longrightarrow> a = b\<close>
begin

sublocale preordering \<open>(\<^bold>\<le>)\<close> \<open>(\<^bold><)\<close>
proof
  show \<open>a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> \<not> b \<^bold>\<le> a\<close> for a b
    by (auto simp add: strict_iff_order intro: antisym)
qed

lemma strict_implies_not_eq:
  \<open>a \<^bold>< b \<Longrightarrow> a \<noteq> b\<close>
  by (simp add: strict_iff_order)

lemma not_eq_order_implies_strict:
  \<open>a \<noteq> b \<Longrightarrow> a \<^bold>\<le> b \<Longrightarrow> a \<^bold>< b\<close>
  by (simp add: strict_iff_order)

lemma order_iff_strict:
  \<open>a \<^bold>\<le> b \<longleftrightarrow> a \<^bold>< b \<or> a = b\<close>
  by (auto simp add: strict_iff_order refl)

lemma eq_iff: \<open>a = b \<longleftrightarrow> a \<^bold>\<le> b \<and> b \<^bold>\<le> a\<close>
  by (auto simp add: refl intro: antisym)

end

lemma ordering_strictI: \<comment> \<open>Alternative introduction rule with bias towards strict order\<close>
  fixes less_eq (infix \<open>\<^bold>\<le>\<close> 50)
    and less (infix \<open>\<^bold><\<close> 50)
  assumes less_eq_less: \<open>\<And>a b. a \<^bold>\<le> b \<longleftrightarrow> a \<^bold>< b \<or> a = b\<close>
    assumes asym: \<open>\<And>a b. a \<^bold>< b \<Longrightarrow> \<not> b \<^bold>< a\<close>
  assumes irrefl: \<open>\<And>a. \<not> a \<^bold>< a\<close>
  assumes trans: \<open>\<And>a b c. a \<^bold>< b \<Longrightarrow> b \<^bold>< c \<Longrightarrow> a \<^bold>< c\<close>
  shows \<open>ordering (\<^bold>\<le>) (\<^bold><)\<close>
proof
  fix a b
  show \<open>a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b\<close>
    by (auto simp add: less_eq_less asym irrefl)
next
  fix a
  show \<open>a \<^bold>\<le> a\<close>
    by (auto simp add: less_eq_less)
next
  fix a b c
  assume \<open>a \<^bold>\<le> b\<close> and \<open>b \<^bold>\<le> c\<close> then show \<open>a \<^bold>\<le> c\<close>
    by (auto simp add: less_eq_less intro: trans)
next
  fix a b
  assume \<open>a \<^bold>\<le> b\<close> and \<open>b \<^bold>\<le> a\<close> then show \<open>a = b\<close>
    by (auto simp add: less_eq_less asym)
qed

lemma ordering_dualI:
  fixes less_eq (infix \<open>\<^bold>\<le>\<close> 50)
    and less (infix \<open>\<^bold><\<close> 50)
  assumes \<open>ordering (\<lambda>a b. b \<^bold>\<le> a) (\<lambda>a b. b \<^bold>< a)\<close>
  shows \<open>ordering (\<^bold>\<le>) (\<^bold><)\<close>
proof -
  from assms interpret ordering \<open>\<lambda>a b. b \<^bold>\<le> a\<close> \<open>\<lambda>a b. b \<^bold>< a\<close> .
  show ?thesis
    by standard (auto simp: strict_iff_order refl intro: antisym trans)
qed

locale ordering_top = ordering +
  fixes top :: \<open>'a\<close>  (\<open>\<^bold>\<top>\<close>)
  assumes extremum [simp]: \<open>a \<^bold>\<le> \<^bold>\<top>\<close>
begin

lemma extremum_uniqueI:
  \<open>\<^bold>\<top> \<^bold>\<le> a \<Longrightarrow> a = \<^bold>\<top>\<close>
  by (rule antisym) auto

lemma extremum_unique:
  \<open>\<^bold>\<top> \<^bold>\<le> a \<longleftrightarrow> a = \<^bold>\<top>\<close>
  by (auto intro: antisym)

lemma extremum_strict [simp]:
  \<open>\<not> (\<^bold>\<top> \<^bold>< a)\<close>
  using extremum [of a] by (auto simp add: order_iff_strict intro: asym irrefl)

lemma not_eq_extremum:
  \<open>a \<noteq> \<^bold>\<top> \<longleftrightarrow> a \<^bold>< \<^bold>\<top>\<close>
  by (auto simp add: order_iff_strict intro: not_eq_order_implies_strict extremum)

end


subsection \<open>Syntactic orders\<close>

class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)

abbreviation (input)
  greater_eq  (infix "\<ge>" 50)
  where "x \<ge> y \<equiv> y \<le> x"

abbreviation (input)
  greater  (infix ">" 50)
  where "x > y \<equiv> y < x"

notation (ASCII)
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50)

notation (input)
  greater_eq  (infix ">=" 50)

end


subsection \<open>Quasi orders\<close>

class preorder = ord +
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  and order_refl [iff]: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
begin

sublocale order: preordering less_eq less + dual_order: preordering greater_eq greater
proof -
  interpret preordering less_eq less
    by standard (auto intro: order_trans simp add: less_le_not_le)
  show \<open>preordering less_eq less\<close>
    by (fact preordering_axioms)
  then show \<open>preordering greater_eq greater\<close>
    by (rule preordering_dualI)
qed

text \<open>Reflexivity.\<close>

lemma eq_refl: "x = y \<Longrightarrow> x \<le> y"
    \<comment> \<open>This form is useful with the classical reasoner.\<close>
by (erule ssubst) (rule order_refl)

lemma less_irrefl [iff]: "\<not> x < x"
by (simp add: less_le_not_le)

lemma less_imp_le: "x < y \<Longrightarrow> x \<le> y"
by (simp add: less_le_not_le)


text \<open>Asymmetry.\<close>

lemma less_not_sym: "x < y \<Longrightarrow> \<not> (y < x)"
by (simp add: less_le_not_le)

lemma less_asym: "x < y \<Longrightarrow> (\<not> P \<Longrightarrow> y < x) \<Longrightarrow> P"
by (drule less_not_sym, erule contrapos_np) simp


text \<open>Transitivity.\<close>

lemma less_trans: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
by (auto simp add: less_le_not_le intro: order_trans)

lemma le_less_trans: "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
by (auto simp add: less_le_not_le intro: order_trans)

lemma less_le_trans: "x < y \<Longrightarrow> y \<le> z \<Longrightarrow> x < z"
by (auto simp add: less_le_not_le intro: order_trans)


text \<open>Useful for simplification, but too risky to include by default.\<close>

lemma less_imp_not_less: "x < y \<Longrightarrow> (\<not> y < x) \<longleftrightarrow> True"
by (blast elim: less_asym)

lemma less_imp_triv: "x < y \<Longrightarrow> (y < x \<longrightarrow> P) \<longleftrightarrow> True"
by (blast elim: less_asym)


text \<open>Transitivity rules for calculational reasoning\<close>

lemma less_asym': "a < b \<Longrightarrow> b < a \<Longrightarrow> P"
by (rule less_asym)


text \<open>Dual order\<close>

lemma dual_preorder:
  \<open>class.preorder (\<ge>) (>)\<close>
  by standard (auto simp add: less_le_not_le intro: order_trans)

end

lemma preordering_preorderI:
  \<open>class.preorder (\<^bold>\<le>) (\<^bold><)\<close> if \<open>preordering (\<^bold>\<le>) (\<^bold><)\<close>
    for less_eq (infix \<open>\<^bold>\<le>\<close> 50) and less (infix \<open>\<^bold><\<close> 50)
proof -
  from that interpret preordering \<open>(\<^bold>\<le>)\<close> \<open>(\<^bold><)\<close> .
  show ?thesis
    by standard (auto simp add: strict_iff_not refl intro: trans)
qed



subsection \<open>Partial orders\<close>

class order = preorder +
  assumes order_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
begin

lemma less_le: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
  by (auto simp add: less_le_not_le intro: order_antisym)

sublocale order: ordering less_eq less + dual_order: ordering greater_eq greater
proof -
  interpret ordering less_eq less
    by standard (auto intro: order_antisym order_trans simp add: less_le)
  show "ordering less_eq less"
    by (fact ordering_axioms)
  then show "ordering greater_eq greater"
    by (rule ordering_dualI)
qed

text \<open>Reflexivity.\<close>

lemma le_less: "x \<le> y \<longleftrightarrow> x < y \<or> x = y"
    \<comment> \<open>NOT suitable for iff, since it can cause PROOF FAILED.\<close>
by (fact order.order_iff_strict)

lemma le_imp_less_or_eq: "x \<le> y \<Longrightarrow> x < y \<or> x = y"
by (simp add: less_le)


text \<open>Useful for simplification, but too risky to include by default.\<close>

lemma less_imp_not_eq: "x < y \<Longrightarrow> (x = y) \<longleftrightarrow> False"
by auto

lemma less_imp_not_eq2: "x < y \<Longrightarrow> (y = x) \<longleftrightarrow> False"
by auto


text \<open>Transitivity rules for calculational reasoning\<close>

lemma neq_le_trans: "a \<noteq> b \<Longrightarrow> a \<le> b \<Longrightarrow> a < b"
by (fact order.not_eq_order_implies_strict)

lemma le_neq_trans: "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a < b"
by (rule order.not_eq_order_implies_strict)


text \<open>Asymmetry.\<close>

lemma order_eq_iff: "x = y \<longleftrightarrow> x \<le> y \<and> y \<le> x"
  by (fact order.eq_iff)

lemma antisym_conv: "y \<le> x \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y"
  by (simp add: order.eq_iff)

lemma less_imp_neq: "x < y \<Longrightarrow> x \<noteq> y"
  by (fact order.strict_implies_not_eq)

lemma antisym_conv1: "\<not> x < y \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y"
  by (simp add: local.le_less)

lemma antisym_conv2: "x \<le> y \<Longrightarrow> \<not> x < y \<longleftrightarrow> x = y"
  by (simp add: local.less_le)

lemma leD: "y \<le> x \<Longrightarrow> \<not> x < y"
  by (auto simp: less_le order.antisym)

text \<open>Least value operator\<close>

definition (in ord)
  Least :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" (binder "LEAST " 10) where
  "Least P = (THE x. P x \<and> (\<forall>y. P y \<longrightarrow> x \<le> y))"

lemma Least_equality:
  assumes "P x"
    and "\<And>y. P y \<Longrightarrow> x \<le> y"
  shows "Least P = x"
unfolding Least_def by (rule the_equality)
  (blast intro: assms order.antisym)+

lemma LeastI2_order:
  assumes "P x"
    and "\<And>y. P y \<Longrightarrow> x \<le> y"
    and "\<And>x. P x \<Longrightarrow> \<forall>y. P y \<longrightarrow> x \<le> y \<Longrightarrow> Q x"
  shows "Q (Least P)"
unfolding Least_def by (rule theI2)
  (blast intro: assms order.antisym)+

lemma Least_ex1:
  assumes   "\<exists>!x. P x \<and> (\<forall>y. P y \<longrightarrow> x \<le> y)"
  shows     Least1I: "P (Least P)" and Least1_le: "P z \<Longrightarrow> Least P \<le> z"
  using     theI'[OF assms]
  unfolding Least_def
  by        auto

text \<open>Greatest value operator\<close>

definition Greatest :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" (binder "GREATEST " 10) where
"Greatest P = (THE x. P x \<and> (\<forall>y. P y \<longrightarrow> x \<ge> y))"

lemma GreatestI2_order:
  "\<lbrakk> P x;
    \<And>y. P y \<Longrightarrow> x \<ge> y;
    \<And>x. \<lbrakk> P x; \<forall>y. P y \<longrightarrow> x \<ge> y \<rbrakk> \<Longrightarrow> Q x \<rbrakk>
  \<Longrightarrow> Q (Greatest P)"
unfolding Greatest_def
by (rule theI2) (blast intro: order.antisym)+

lemma Greatest_equality:
  "\<lbrakk> P x;  \<And>y. P y \<Longrightarrow> x \<ge> y \<rbrakk> \<Longrightarrow> Greatest P = x"
unfolding Greatest_def
by (rule the_equality) (blast intro: order.antisym)+

end

lemma ordering_orderI:
  fixes less_eq (infix "\<^bold>\<le>" 50)
    and less (infix "\<^bold><" 50)
  assumes "ordering less_eq less"
  shows "class.order less_eq less"
proof -
  from assms interpret ordering less_eq less .
  show ?thesis
    by standard (auto intro: antisym trans simp add: refl strict_iff_order)
qed

lemma order_strictI:
  fixes less (infix "\<^bold><" 50)
    and less_eq (infix "\<^bold>\<le>" 50)
  assumes "\<And>a b. a \<^bold>\<le> b \<longleftrightarrow> a \<^bold>< b \<or> a = b"
    assumes "\<And>a b. a \<^bold>< b \<Longrightarrow> \<not> b \<^bold>< a"
  assumes "\<And>a. \<not> a \<^bold>< a"
  assumes "\<And>a b c. a \<^bold>< b \<Longrightarrow> b \<^bold>< c \<Longrightarrow> a \<^bold>< c"
  shows "class.order less_eq less"
  by (rule ordering_orderI) (rule ordering_strictI, (fact assms)+)

context order
begin

text \<open>Dual order\<close>

lemma dual_order:
  "class.order (\<ge>) (>)"
  using dual_order.ordering_axioms by (rule ordering_orderI)

end


subsection \<open>Linear (total) orders\<close>

class linorder = order +
  assumes linear: "x \<le> y \<or> y \<le> x"
begin

lemma less_linear: "x < y \<or> x = y \<or> y < x"
unfolding less_le using less_le linear by blast

lemma le_less_linear: "x \<le> y \<or> y < x"
by (simp add: le_less less_linear)

lemma le_cases [case_names le ge]:
  "(x \<le> y \<Longrightarrow> P) \<Longrightarrow> (y \<le> x \<Longrightarrow> P) \<Longrightarrow> P"
using linear by blast

lemma (in linorder) le_cases3:
  "\<lbrakk>\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> P; \<lbrakk>y \<le> x; x \<le> z\<rbrakk> \<Longrightarrow> P; \<lbrakk>x \<le> z; z \<le> y\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>z \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> P; \<lbrakk>y \<le> z; z \<le> x\<rbrakk> \<Longrightarrow> P; \<lbrakk>z \<le> x; x \<le> y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (blast intro: le_cases)

lemma linorder_cases [case_names less equal greater]:
  "(x < y \<Longrightarrow> P) \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> (y < x \<Longrightarrow> P) \<Longrightarrow> P"
using less_linear by blast

lemma linorder_wlog[case_names le sym]:
  "(\<And>a b. a \<le> b \<Longrightarrow> P a b) \<Longrightarrow> (\<And>a b. P b a \<Longrightarrow> P a b) \<Longrightarrow> P a b"
  by (cases rule: le_cases[of a b]) blast+

lemma not_less: "\<not> x < y \<longleftrightarrow> y \<le> x"
  unfolding less_le
  using linear by (blast intro: order.antisym)

lemma not_less_iff_gr_or_eq: "\<not>(x < y) \<longleftrightarrow> (x > y \<or> x = y)"
  by (auto simp add:not_less le_less)

lemma not_le: "\<not> x \<le> y \<longleftrightarrow> y < x"
  unfolding less_le
  using linear by (blast intro: order.antisym)

lemma neq_iff: "x \<noteq> y \<longleftrightarrow> x < y \<or> y < x"
by (cut_tac x = x and y = y in less_linear, auto)

lemma neqE: "x \<noteq> y \<Longrightarrow> (x < y \<Longrightarrow> R) \<Longrightarrow> (y < x \<Longrightarrow> R) \<Longrightarrow> R"
by (simp add: neq_iff) blast

lemma antisym_conv3: "\<not> y < x \<Longrightarrow> \<not> x < y \<longleftrightarrow> x = y"
by (blast intro: order.antisym dest: not_less [THEN iffD1])

lemma leI: "\<not> x < y \<Longrightarrow> y \<le> x"
unfolding not_less .

lemma not_le_imp_less: "\<not> y \<le> x \<Longrightarrow> x < y"
unfolding not_le .

lemma linorder_less_wlog[case_names less refl sym]:
     "\<lbrakk>\<And>a b. a < b \<Longrightarrow> P a b;  \<And>a. P a a;  \<And>a b. P b a \<Longrightarrow> P a b\<rbrakk> \<Longrightarrow> P a b"
  using antisym_conv3 by blast

text \<open>Dual order\<close>

lemma dual_linorder:
  "class.linorder (\<ge>) (>)"
by (rule class.linorder.intro, rule dual_order) (unfold_locales, rule linear)

end


text \<open>Alternative introduction rule with bias towards strict order\<close>

lemma linorder_strictI:
  fixes less_eq (infix "\<^bold>\<le>" 50)
    and less (infix "\<^bold><" 50)
  assumes "class.order less_eq less"
  assumes trichotomy: "\<And>a b. a \<^bold>< b \<or> a = b \<or> b \<^bold>< a"
  shows "class.linorder less_eq less"
proof -
  interpret order less_eq less
    by (fact \<open>class.order less_eq less\<close>)
  show ?thesis
  proof
    fix a b
    show "a \<^bold>\<le> b \<or> b \<^bold>\<le> a"
      using trichotomy by (auto simp add: le_less)
  qed
qed


subsection \<open>Reasoning tools setup\<close>

ML_file \<open>~~/src/Provers/order_procedure.ML\<close>
ML_file \<open>~~/src/Provers/order_tac.ML\<close>

ML \<open>
structure Logic_Signature : LOGIC_SIGNATURE = struct
  val mk_Trueprop = HOLogic.mk_Trueprop
  val dest_Trueprop = HOLogic.dest_Trueprop
  val Trueprop_conv = HOLogic.Trueprop_conv
  val Not = HOLogic.Not
  val conj = HOLogic.conj
  val disj = HOLogic.disj
  
  val notI = @{thm notI}
  val ccontr = @{thm ccontr}
  val conjI = @{thm conjI}  
  val conjE = @{thm conjE}
  val disjE = @{thm disjE}

  val not_not_conv = Conv.rewr_conv @{thm eq_reflection[OF not_not]}
  val de_Morgan_conj_conv = Conv.rewr_conv @{thm eq_reflection[OF de_Morgan_conj]}
  val de_Morgan_disj_conv = Conv.rewr_conv @{thm eq_reflection[OF de_Morgan_disj]}
  val conj_disj_distribL_conv = Conv.rewr_conv @{thm eq_reflection[OF conj_disj_distribL]}
  val conj_disj_distribR_conv = Conv.rewr_conv @{thm eq_reflection[OF conj_disj_distribR]}
end

structure HOL_Base_Order_Tac = Base_Order_Tac(
  structure Logic_Sig = Logic_Signature;
  (* Exclude types with specialised solvers. *)
  val excluded_types = [HOLogic.natT, HOLogic.intT, HOLogic.realT]
)

structure HOL_Order_Tac = Order_Tac(structure Base_Tac = HOL_Base_Order_Tac)

fun print_orders ctxt0 =
  let
    val ctxt = Config.put show_sorts true ctxt0
    val orders = HOL_Order_Tac.Data.get (Context.Proof ctxt)
    fun pretty_term t = Pretty.block
      [Pretty.quote (Syntax.pretty_term ctxt t), Pretty.brk 1,
        Pretty.str "::", Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ ctxt (type_of t)), Pretty.brk 1]
    fun pretty_order ({kind = kind, ops = ops, ...}, _) =
      Pretty.block ([Pretty.str (@{make_string} kind), Pretty.str ":", Pretty.brk 1]
                    @ map pretty_term ops)
  in
    Pretty.writeln (Pretty.big_list "order structures:" (map pretty_order orders))
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_orders\<close>
    "print order structures available to order reasoner"
    (Scan.succeed (Toplevel.keep (print_orders o Toplevel.context_of)))

\<close>

method_setup order = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (HOL_Order_Tac.tac [] ctxt))
\<close> "partial and linear order reasoner"

text \<open>                                                                                      
  The method @{method order} allows one to use the order tactic located in
   \<^file>\<open>../Provers/order_tac.ML\<close> in a standalone fashion.
  
  The tactic rearranges the goal to prove \<^const>\<open>False\<close>, then retrieves order literals of partial
  and linear orders (i.e. \<^term>\<open>x = y\<close>, \<^term>\<open>x \<le> y\<close>, \<^term>\<open>x < y\<close>, and their negated versions)
  from the premises and finally tries to derive a contradiction. Its main use case is as a solver to
  @{method simp} (see below), where it e.g. solves premises of conditional rewrite rules.

  The tactic has two configuration attributes that control its behaviour:
  \<^item> @{attribute order_trace} toggles tracing for the solver.
  \<^item> @{attribute order_split_limit} limits the number of order literals of the form
    \<^term>\<open>\<not> (x::'a::order) < y\<close> that are passed to the tactic.
    This is helpful since these literals lead to case splitting and thus exponential runtime.
    This only applies to partial orders.

  We setup the solver for HOL with the structure @{ML_structure HOL_Order_Tac} here but the prover
  is agnostic to the object logic.
  It is possible to register orders with the prover using the functions
  @{ML HOL_Order_Tac.declare_order} and @{ML HOL_Order_Tac.declare_linorder}, which we do below
  for the type classes @{class order} and @{class linorder}.
  If possible, one should instantiate these type classes instead of registering new orders with the
  solver. One can also interpret the type class locales @{locale order} and @{locale linorder}.
  An example can be seen in \<^file>\<open>Library/Sublist.thy\<close>, which contains e.g. the prefix order on lists.

  The diagnostic command @{command print_orders} shows all orders known to the tactic in the current
  context.
\<close>

text \<open>Declarations to set up transitivity reasoner of partial and linear orders.\<close>

context order
begin

lemma nless_le: "(\<not> a < b) \<longleftrightarrow> (\<not> a \<le> b) \<or> a = b"
  using local.dual_order.order_iff_strict by blast

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}, le = @{term \<open>(\<le>)\<close>}, lt = @{term \<open>(<)\<close>}},
    thms = {trans = @{thm order_trans}, refl = @{thm order_refl}, eqD1 = @{thm eq_refl},
            eqD2 = @{thm eq_refl[OF sym]}, antisym = @{thm order_antisym}, contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF less_le]},
                 nless_le = @{thm eq_reflection[OF nless_le]}}
  }
\<close>

end

context linorder
begin

lemma nle_le: "(\<not> a \<le> b) \<longleftrightarrow> b \<le> a \<and> b \<noteq> a"
  using not_le less_le by simp

local_setup \<open>
  HOL_Order_Tac.declare_linorder {
    ops = {eq = @{term \<open>(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}, le = @{term \<open>(\<le>)\<close>}, lt = @{term \<open>(<)\<close>}},
    thms = {trans = @{thm order_trans}, refl = @{thm order_refl}, eqD1 = @{thm eq_refl},
            eqD2 = @{thm eq_refl[OF sym]}, antisym = @{thm order_antisym}, contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF less_le]},
                 nless_le = @{thm eq_reflection[OF not_less]},
                 nle_le = @{thm eq_reflection[OF nle_le]}}
  }
\<close>

end

setup \<open>
  map_theory_simpset (fn ctxt0 => ctxt0 addSolver
    mk_solver "partial and linear orders" (fn ctxt => HOL_Order_Tac.tac (Simplifier.prems_of ctxt) ctxt))
\<close>

ML \<open>
local
  fun prp t thm = Thm.prop_of thm = t;  (* FIXME proper aconv!? *)
in

fun antisym_le_simproc ctxt ct =
  (case Thm.term_of ct of
    (le as Const (_, T)) $ r $ s =>
     (let
        val prems = Simplifier.prems_of ctxt;
        val less = Const (\<^const_name>\<open>less\<close>, T);
        val t = HOLogic.mk_Trueprop(le $ s $ r);
      in
        (case find_first (prp t) prems of
          NONE =>
            let val t = HOLogic.mk_Trueprop(HOLogic.Not $ (less $ r $ s)) in
              (case find_first (prp t) prems of
                NONE => NONE
              | SOME thm => SOME(mk_meta_eq(thm RS @{thm antisym_conv1})))
             end
         | SOME thm => SOME (mk_meta_eq (thm RS @{thm order_class.antisym_conv})))
      end handle THM _ => NONE)
  | _ => NONE);

fun antisym_less_simproc ctxt ct =
  (case Thm.term_of ct of
    NotC $ ((less as Const(_,T)) $ r $ s) =>
     (let
       val prems = Simplifier.prems_of ctxt;
       val le = Const (\<^const_name>\<open>less_eq\<close>, T);
       val t = HOLogic.mk_Trueprop(le $ r $ s);
      in
        (case find_first (prp t) prems of
          NONE =>
            let val t = HOLogic.mk_Trueprop (NotC $ (less $ s $ r)) in
              (case find_first (prp t) prems of
                NONE => NONE
              | SOME thm => SOME (mk_meta_eq(thm RS @{thm linorder_class.antisym_conv3})))
            end
        | SOME thm => SOME (mk_meta_eq (thm RS @{thm antisym_conv2})))
      end handle THM _ => NONE)                           
  | _ => NONE);

end;
\<close>

simproc_setup antisym_le ("(x::'a::order) \<le> y") = "K antisym_le_simproc"
simproc_setup antisym_less ("\<not> (x::'a::linorder) < y") = "K antisym_less_simproc"


subsection \<open>Bounded quantifiers\<close>

syntax (ASCII)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _>=_./ _)" [0, 0, 10] 10)

  "_All_neq" :: "[idt, 'a, bool] => bool"    ("(3ALL _~=_./ _)"  [0, 0, 10] 10)
  "_Ex_neq" :: "[idt, 'a, bool] => bool"    ("(3EX _~=_./ _)"  [0, 0, 10] 10)

syntax
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

  "_All_neq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<noteq>_./ _)"  [0, 0, 10] 10)
  "_Ex_neq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<noteq>_./ _)"  [0, 0, 10] 10)

syntax (input)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3? _<=_./ _)" [0, 0, 10] 10)
  "_All_neq" :: "[idt, 'a, bool] => bool"    ("(3! _~=_./ _)"  [0, 0, 10] 10)
  "_Ex_neq" :: "[idt, 'a, bool] => bool"    ("(3? _~=_./ _)"  [0, 0, 10] 10)

syntax_consts
  "_All_less" "_All_less_eq" "_All_greater" "_All_greater_eq" "_All_neq" \<rightleftharpoons> All and
  "_Ex_less" "_Ex_less_eq" "_Ex_greater" "_Ex_greater_eq" "_Ex_neq" \<rightleftharpoons> Ex

translations
  "\<forall>x<y. P" \<rightharpoonup> "\<forall>x. x < y \<longrightarrow> P"
  "\<exists>x<y. P" \<rightharpoonup> "\<exists>x. x < y \<and> P"
  "\<forall>x\<le>y. P" \<rightharpoonup> "\<forall>x. x \<le> y \<longrightarrow> P"
  "\<exists>x\<le>y. P" \<rightharpoonup> "\<exists>x. x \<le> y \<and> P"
  "\<forall>x>y. P" \<rightharpoonup> "\<forall>x. x > y \<longrightarrow> P"
  "\<exists>x>y. P" \<rightharpoonup> "\<exists>x. x > y \<and> P"
  "\<forall>x\<ge>y. P" \<rightharpoonup> "\<forall>x. x \<ge> y \<longrightarrow> P"
  "\<exists>x\<ge>y. P" \<rightharpoonup> "\<exists>x. x \<ge> y \<and> P"
  "\<forall>x\<noteq>y. P" \<rightharpoonup> "\<forall>x. x \<noteq> y \<longrightarrow> P"
  "\<exists>x\<noteq>y. P" \<rightharpoonup> "\<exists>x. x \<noteq> y \<and> P"

print_translation \<open>
let
  val All_binder = Mixfix.binder_name \<^const_syntax>\<open>All\<close>;
  val Ex_binder = Mixfix.binder_name \<^const_syntax>\<open>Ex\<close>;
  val impl = \<^const_syntax>\<open>HOL.implies\<close>;
  val conj = \<^const_syntax>\<open>HOL.conj\<close>;
  val less = \<^const_syntax>\<open>less\<close>;
  val less_eq = \<^const_syntax>\<open>less_eq\<close>;

  val trans =
   [((All_binder, impl, less),
    (\<^syntax_const>\<open>_All_less\<close>, \<^syntax_const>\<open>_All_greater\<close>)),
    ((All_binder, impl, less_eq),
    (\<^syntax_const>\<open>_All_less_eq\<close>, \<^syntax_const>\<open>_All_greater_eq\<close>)),
    ((Ex_binder, conj, less),
    (\<^syntax_const>\<open>_Ex_less\<close>, \<^syntax_const>\<open>_Ex_greater\<close>)),
    ((Ex_binder, conj, less_eq),
    (\<^syntax_const>\<open>_Ex_less_eq\<close>, \<^syntax_const>\<open>_Ex_greater_eq\<close>))];

  fun matches_bound v t =
    (case t of
      Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (v', _) => v = v'
    | _ => false);
  fun contains_var v = Term.exists_subterm (fn Free (x, _) => x = v | _ => false);
  fun mk x c n P = Syntax.const c $ Syntax_Trans.mark_bound_body x $ n $ P;

  fun tr' q = (q, fn _ =>
    (fn [Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (v, T),
        Const (c, _) $ (Const (d, _) $ t $ u) $ P] =>
        (case AList.lookup (=) trans (q, c, d) of
          NONE => raise Match
        | SOME (l, g) =>
            if matches_bound v t andalso not (contains_var v u) then mk (v, T) l u P
            else if matches_bound v u andalso not (contains_var v t) then mk (v, T) g t P
            else raise Match)
      | _ => raise Match));
in [tr' All_binder, tr' Ex_binder] end
\<close>


subsection \<open>Transitivity reasoning\<close>

context ord
begin

lemma ord_le_eq_trans: "a \<le> b \<Longrightarrow> b = c \<Longrightarrow> a \<le> c"
  by (rule subst)

lemma ord_eq_le_trans: "a = b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  by (rule ssubst)

lemma ord_less_eq_trans: "a < b \<Longrightarrow> b = c \<Longrightarrow> a < c"
  by (rule subst)

lemma ord_eq_less_trans: "a = b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (rule ssubst)

end

lemma order_less_subst2: "(a::'a::order) < b \<Longrightarrow> f b < (c::'c::order) \<Longrightarrow>
  (!!x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> f a < c"
proof -
  assume r: "!!x y. x < y \<Longrightarrow> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b < c"
  finally (less_trans) show ?thesis .
qed

lemma order_less_subst1: "(a::'a::order) < f b \<Longrightarrow> (b::'b::order) < c \<Longrightarrow>
  (!!x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> a < f c"
proof -
  assume r: "!!x y. x < y \<Longrightarrow> f x < f y"
  assume "a < f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (less_trans) show ?thesis .
qed

lemma order_le_less_subst2: "(a::'a::order) <= b \<Longrightarrow> f b < (c::'c::order) \<Longrightarrow>
  (!!x y. x <= y \<Longrightarrow> f x <= f y) \<Longrightarrow> f a < c"
proof -
  assume r: "!!x y. x <= y \<Longrightarrow> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b < c"
  finally (le_less_trans) show ?thesis .
qed

lemma order_le_less_subst1: "(a::'a::order) <= f b \<Longrightarrow> (b::'b::order) < c \<Longrightarrow>
  (!!x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> a < f c"
proof -
  assume r: "!!x y. x < y \<Longrightarrow> f x < f y"
  assume "a <= f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (le_less_trans) show ?thesis .
qed

lemma order_less_le_subst2: "(a::'a::order) < b \<Longrightarrow> f b <= (c::'c::order) \<Longrightarrow>
  (!!x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> f a < c"
proof -
  assume r: "!!x y. x < y \<Longrightarrow> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b <= c"
  finally (less_le_trans) show ?thesis .
qed

lemma order_less_le_subst1: "(a::'a::order) < f b \<Longrightarrow> (b::'b::order) <= c \<Longrightarrow>
  (!!x y. x <= y \<Longrightarrow> f x <= f y) \<Longrightarrow> a < f c"
proof -
  assume r: "!!x y. x <= y \<Longrightarrow> f x <= f y"
  assume "a < f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (less_le_trans) show ?thesis .
qed

lemma order_subst1: "(a::'a::order) <= f b \<Longrightarrow> (b::'b::order) <= c \<Longrightarrow>
  (!!x y. x <= y \<Longrightarrow> f x <= f y) \<Longrightarrow> a <= f c"
proof -
  assume r: "!!x y. x <= y \<Longrightarrow> f x <= f y"
  assume "a <= f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_trans) show ?thesis .
qed

lemma order_subst2: "(a::'a::order) <= b \<Longrightarrow> f b <= (c::'c::order) \<Longrightarrow>
  (!!x y. x <= y \<Longrightarrow> f x <= f y) \<Longrightarrow> f a <= c"
proof -
  assume r: "!!x y. x <= y \<Longrightarrow> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b <= c"
  finally (order_trans) show ?thesis .
qed

lemma ord_le_eq_subst: "a <= b \<Longrightarrow> f b = c \<Longrightarrow>
  (!!x y. x <= y \<Longrightarrow> f x <= f y) \<Longrightarrow> f a <= c"
proof -
  assume r: "!!x y. x <= y \<Longrightarrow> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b = c"
  finally (ord_le_eq_trans) show ?thesis .
qed

lemma ord_eq_le_subst: "a = f b \<Longrightarrow> b <= c \<Longrightarrow>
  (!!x y. x <= y \<Longrightarrow> f x <= f y) \<Longrightarrow> a <= f c"
proof -
  assume r: "!!x y. x <= y \<Longrightarrow> f x <= f y"
  assume "a = f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (ord_eq_le_trans) show ?thesis .
qed

lemma ord_less_eq_subst: "a < b \<Longrightarrow> f b = c \<Longrightarrow>
  (!!x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> f a < c"
proof -
  assume r: "!!x y. x < y \<Longrightarrow> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b = c"
  finally (ord_less_eq_trans) show ?thesis .
qed

lemma ord_eq_less_subst: "a = f b \<Longrightarrow> b < c \<Longrightarrow>
  (!!x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> a < f c"
proof -
  assume r: "!!x y. x < y \<Longrightarrow> f x < f y"
  assume "a = f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (ord_eq_less_trans) show ?thesis .
qed

text \<open>
  Note that this list of rules is in reverse order of priorities.
\<close>

lemmas [trans] =
  order_less_subst2
  order_less_subst1
  order_le_less_subst2
  order_le_less_subst1
  order_less_le_subst2
  order_less_le_subst1
  order_subst2
  order_subst1
  ord_le_eq_subst
  ord_eq_le_subst
  ord_less_eq_subst
  ord_eq_less_subst
  forw_subst
  back_subst
  rev_mp
  mp

lemmas (in order) [trans] =
  neq_le_trans
  le_neq_trans

lemmas (in preorder) [trans] =
  less_trans
  less_asym'
  le_less_trans
  less_le_trans
  order_trans

lemmas (in order) [trans] =
  order.antisym

lemmas (in ord) [trans] =
  ord_le_eq_trans
  ord_eq_le_trans
  ord_less_eq_trans
  ord_eq_less_trans

lemmas [trans] =
  trans

lemmas order_trans_rules =
  order_less_subst2
  order_less_subst1
  order_le_less_subst2
  order_le_less_subst1
  order_less_le_subst2
  order_less_le_subst1
  order_subst2
  order_subst1
  ord_le_eq_subst
  ord_eq_le_subst
  ord_less_eq_subst
  ord_eq_less_subst
  forw_subst
  back_subst
  rev_mp
  mp
  neq_le_trans
  le_neq_trans
  less_trans
  less_asym'
  le_less_trans
  less_le_trans
  order_trans
  order.antisym
  ord_le_eq_trans
  ord_eq_le_trans
  ord_less_eq_trans
  ord_eq_less_trans
  trans

text \<open>These support proving chains of decreasing inequalities
    a \<open>\<ge>\<close> b \<open>\<ge>\<close> c ... in Isar proofs.\<close>

lemma xt1 [no_atp]:
  "a = b \<Longrightarrow> b > c \<Longrightarrow> a > c"
  "a > b \<Longrightarrow> b = c \<Longrightarrow> a > c"
  "a = b \<Longrightarrow> b \<ge> c \<Longrightarrow> a \<ge> c"
  "a \<ge> b \<Longrightarrow> b = c \<Longrightarrow> a \<ge> c"
  "(x::'a::order) \<ge> y \<Longrightarrow> y \<ge> x \<Longrightarrow> x = y"
  "(x::'a::order) \<ge> y \<Longrightarrow> y \<ge> z \<Longrightarrow> x \<ge> z"
  "(x::'a::order) > y \<Longrightarrow> y \<ge> z \<Longrightarrow> x > z"
  "(x::'a::order) \<ge> y \<Longrightarrow> y > z \<Longrightarrow> x > z"
  "(a::'a::order) > b \<Longrightarrow> b > a \<Longrightarrow> P"
  "(x::'a::order) > y \<Longrightarrow> y > z \<Longrightarrow> x > z"
  "(a::'a::order) \<ge> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a > b"
  "(a::'a::order) \<noteq> b \<Longrightarrow> a \<ge> b \<Longrightarrow> a > b"
  "a = f b \<Longrightarrow> b > c \<Longrightarrow> (\<And>x y. x > y \<Longrightarrow> f x > f y) \<Longrightarrow> a > f c"
  "a > b \<Longrightarrow> f b = c \<Longrightarrow> (\<And>x y. x > y \<Longrightarrow> f x > f y) \<Longrightarrow> f a > c"
  "a = f b \<Longrightarrow> b \<ge> c \<Longrightarrow> (\<And>x y. x \<ge> y \<Longrightarrow> f x \<ge> f y) \<Longrightarrow> a \<ge> f c"
  "a \<ge> b \<Longrightarrow> f b = c \<Longrightarrow> (\<And>x y. x \<ge> y \<Longrightarrow> f x \<ge> f y) \<Longrightarrow> f a \<ge> c"
  by auto

lemma xt2 [no_atp]:
  assumes "(a::'a::order) \<ge> f b"
    and "b \<ge> c"
    and "\<And>x y. x \<ge> y \<Longrightarrow> f x \<ge> f y"
  shows  "a \<ge> f c"
  using assms by force

lemma xt3 [no_atp]:
 assumes "(a::'a::order) \<ge> b"
    and "(f b::'b::order) \<ge> c"
    and "\<And>x y. x \<ge> y \<Longrightarrow> f x \<ge> f y"
  shows  "f a \<ge> c"
  using assms by force

lemma xt4 [no_atp]:
 assumes "(a::'a::order) > f b"
    and "(b::'b::order) \<ge> c"
    and "\<And>x y. x \<ge> y \<Longrightarrow> f x \<ge> f y"
  shows  "a > f c"
  using assms by force

lemma xt5 [no_atp]:
 assumes "(a::'a::order) > b"
    and "(f b::'b::order) \<ge> c"
    and "\<And>x y. x > y \<Longrightarrow> f x > f y"
  shows  "f a > c"
  using assms by force

lemma xt6 [no_atp]:
 assumes "(a::'a::order) \<ge> f b" 
    and "b > c"
    and "\<And>x y. x > y \<Longrightarrow> f x > f y"
  shows  "a > f c"
  using assms by force

lemma xt7 [no_atp]:
 assumes "(a::'a::order) \<ge> b"
    and "(f b::'b::order) > c"
    and "\<And>x y. x \<ge> y \<Longrightarrow> f x \<ge> f y"
  shows  "f a > c"
  using assms by force

lemma xt8 [no_atp]:
 assumes "(a::'a::order) > f b"
    and "(b::'b::order) > c"
    and "\<And>x y. x > y \<Longrightarrow> f x > f y"
  shows  "a > f c"
  using assms by force

lemma xt9 [no_atp]:
 assumes "(a::'a::order) > b"
    and "(f b::'b::order) > c"
    and "\<And>x y. x > y \<Longrightarrow> f x > f y"
  shows  "f a > c"
  using assms by force

lemmas xtrans = xt1 xt2 xt3 xt4 xt5 xt6 xt7 xt8 xt9

(*
  Since "a \<ge> b" abbreviates "b \<le> a", the abbreviation "..." stands
  for the wrong thing in an Isar proof.

  The extra transitivity rules can be used as follows:

lemma "(a::'a::order) > z"
proof -
  have "a \<ge> b" (is "_ \<ge> ?rhs")
    sorry
  also have "?rhs \<ge> c" (is "_ \<ge> ?rhs")
    sorry
  also (xtrans) have "?rhs = d" (is "_ = ?rhs")
    sorry
  also (xtrans) have "?rhs \<ge> e" (is "_ \<ge> ?rhs")
    sorry
  also (xtrans) have "?rhs > f" (is "_ > ?rhs")
    sorry
  also (xtrans) have "?rhs > z"
    sorry
  finally (xtrans) show ?thesis .
qed

  Alternatively, one can use "declare xtrans [trans]" and then
  leave out the "(xtrans)" above.
*)


subsection \<open>min and max -- fundamental\<close>

definition (in ord) min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min a b = (if a \<le> b then a else b)"

definition (in ord) max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max a b = (if a \<le> b then b else a)"

lemma min_absorb1: "x \<le> y \<Longrightarrow> min x y = x"
  by (simp add: min_def)

lemma max_absorb2: "x \<le> y \<Longrightarrow> max x y = y"
  by (simp add: max_def)

lemma min_absorb2: "(y::'a::order) \<le> x \<Longrightarrow> min x y = y"
  by (simp add:min_def)

lemma max_absorb1: "(y::'a::order) \<le> x \<Longrightarrow> max x y = x"
  by (simp add: max_def)

lemma max_min_same [simp]:
  fixes x y :: "'a :: linorder"
  shows "max x (min x y) = x" "max (min x y) x = x" "max (min x y) y = y" "max y (min x y) = y"
by(auto simp add: max_def min_def)


subsection \<open>(Unique) top and bottom elements\<close>

class bot =
  fixes bot :: 'a ("\<bottom>")

class order_bot = order + bot +
  assumes bot_least: "\<bottom> \<le> a"
begin

sublocale bot: ordering_top greater_eq greater bot
  by standard (fact bot_least)

lemma le_bot:
  "a \<le> \<bottom> \<Longrightarrow> a = \<bottom>"
  by (fact bot.extremum_uniqueI)

lemma bot_unique:
  "a \<le> \<bottom> \<longleftrightarrow> a = \<bottom>"
  by (fact bot.extremum_unique)

lemma not_less_bot:
  "\<not> a < \<bottom>"
  by (fact bot.extremum_strict)

lemma bot_less:
  "a \<noteq> \<bottom> \<longleftrightarrow> \<bottom> < a"
  by (fact bot.not_eq_extremum)

lemma max_bot[simp]: "max bot x = x"
by(simp add: max_def bot_unique)

lemma max_bot2[simp]: "max x bot = x"
by(simp add: max_def bot_unique)

lemma min_bot[simp]: "min bot x = bot"
by(simp add: min_def bot_unique)

lemma min_bot2[simp]: "min x bot = bot"
by(simp add: min_def bot_unique)

end

class top =
  fixes top :: 'a ("\<top>")

class order_top = order + top +
  assumes top_greatest: "a \<le> \<top>"
begin

sublocale top: ordering_top less_eq less top
  by standard (fact top_greatest)

lemma top_le:
  "\<top> \<le> a \<Longrightarrow> a = \<top>"
  by (fact top.extremum_uniqueI)

lemma top_unique:
  "\<top> \<le> a \<longleftrightarrow> a = \<top>"
  by (fact top.extremum_unique)

lemma not_top_less:
  "\<not> \<top> < a"
  by (fact top.extremum_strict)

lemma less_top:
  "a \<noteq> \<top> \<longleftrightarrow> a < \<top>"
  by (fact top.not_eq_extremum)

lemma max_top[simp]: "max top x = top"
by(simp add: max_def top_unique)

lemma max_top2[simp]: "max x top = top"
by(simp add: max_def top_unique)

lemma min_top[simp]: "min top x = x"
by(simp add: min_def top_unique)

lemma min_top2[simp]: "min x top = x"
by(simp add: min_def top_unique)

end


subsection \<open>Dense orders\<close>

class dense_order = order +
  assumes dense: "x < y \<Longrightarrow> (\<exists>z. x < z \<and> z < y)"

class dense_linorder = linorder + dense_order
begin

lemma dense_le:
  fixes y z :: 'a
  assumes "\<And>x. x < y \<Longrightarrow> x \<le> z"
  shows "y \<le> z"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "z < y" by simp
  from dense[OF this]
  obtain x where "x < y" and "z < x" by safe
  moreover have "x \<le> z" using assms[OF \<open>x < y\<close>] .
  ultimately show False by auto
qed

lemma dense_le_bounded:
  fixes x y z :: 'a
  assumes "x < y"
  assumes *: "\<And>w. \<lbrakk> x < w ; w < y \<rbrakk> \<Longrightarrow> w \<le> z"
  shows "y \<le> z"
proof (rule dense_le)
  fix w assume "w < y"
  from dense[OF \<open>x < y\<close>] obtain u where "x < u" "u < y" by safe
  from linear[of u w]
  show "w \<le> z"
  proof (rule disjE)
    assume "u \<le> w"
    from less_le_trans[OF \<open>x < u\<close> \<open>u \<le> w\<close>] \<open>w < y\<close>
    show "w \<le> z" by (rule *)
  next
    assume "w \<le> u"
    from \<open>w \<le> u\<close> *[OF \<open>x < u\<close> \<open>u < y\<close>]
    show "w \<le> z" by (rule order_trans)
  qed
qed

lemma dense_ge:
  fixes y z :: 'a
  assumes "\<And>x. z < x \<Longrightarrow> y \<le> x"
  shows "y \<le> z"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "z < y" by simp
  from dense[OF this]
  obtain x where "x < y" and "z < x" by safe
  moreover have "y \<le> x" using assms[OF \<open>z < x\<close>] .
  ultimately show False by auto
qed

lemma dense_ge_bounded:
  fixes x y z :: 'a
  assumes "z < x"
  assumes *: "\<And>w. \<lbrakk> z < w ; w < x \<rbrakk> \<Longrightarrow> y \<le> w"
  shows "y \<le> z"
proof (rule dense_ge)
  fix w assume "z < w"
  from dense[OF \<open>z < x\<close>] obtain u where "z < u" "u < x" by safe
  from linear[of u w]
  show "y \<le> w"
  proof (rule disjE)
    assume "w \<le> u"
    from \<open>z < w\<close> le_less_trans[OF \<open>w \<le> u\<close> \<open>u < x\<close>]
    show "y \<le> w" by (rule *)
  next
    assume "u \<le> w"
    from *[OF \<open>z < u\<close> \<open>u < x\<close>] \<open>u \<le> w\<close>
    show "y \<le> w" by (rule order_trans)
  qed
qed

end

class no_top = order +
  assumes gt_ex: "\<exists>y. x < y"

class no_bot = order +
  assumes lt_ex: "\<exists>y. y < x"

class unbounded_dense_linorder = dense_linorder + no_top + no_bot


subsection \<open>Wellorders\<close>

class wellorder = linorder +
  assumes less_induct [case_names less]: "(\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
begin

lemma wellorder_Least_lemma:
  fixes k :: 'a
  assumes "P k"
  shows LeastI: "P (LEAST x. P x)" and Least_le: "(LEAST x. P x) \<le> k"
proof -
  have "P (LEAST x. P x) \<and> (LEAST x. P x) \<le> k"
  using assms proof (induct k rule: less_induct)
    case (less x) then have "P x" by simp
    show ?case proof (rule classical)
      assume assm: "\<not> (P (LEAST a. P a) \<and> (LEAST a. P a) \<le> x)"
      have "\<And>y. P y \<Longrightarrow> x \<le> y"
      proof (rule classical)
        fix y
        assume "P y" and "\<not> x \<le> y"
        with less have "P (LEAST a. P a)" and "(LEAST a. P a) \<le> y"
          by (auto simp add: not_le)
        with assm have "x < (LEAST a. P a)" and "(LEAST a. P a) \<le> y"
          by auto
        then show "x \<le> y" by auto
      qed
      with \<open>P x\<close> have Least: "(LEAST a. P a) = x"
        by (rule Least_equality)
      with \<open>P x\<close> show ?thesis by simp
    qed
  qed
  then show "P (LEAST x. P x)" and "(LEAST x. P x) \<le> k" by auto
qed

\<comment> \<open>The following 3 lemmas are due to Brian Huffman\<close>
lemma LeastI_ex: "\<exists>x. P x \<Longrightarrow> P (Least P)"
  by (erule exE) (erule LeastI)

lemma LeastI2:
  "P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (Least P)"
  by (blast intro: LeastI)

lemma LeastI2_ex:
  "\<exists>a. P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (Least P)"
  by (blast intro: LeastI_ex)

lemma LeastI2_wellorder:
  assumes "P a"
  and "\<And>a. \<lbrakk> P a; \<forall>b. P b \<longrightarrow> a \<le> b \<rbrakk> \<Longrightarrow> Q a"
  shows "Q (Least P)"
proof (rule LeastI2_order)
  show "P (Least P)" using \<open>P a\<close> by (rule LeastI)
next
  fix y assume "P y" thus "Least P \<le> y" by (rule Least_le)
next
  fix x assume "P x" "\<forall>y. P y \<longrightarrow> x \<le> y" thus "Q x" by (rule assms(2))
qed

lemma LeastI2_wellorder_ex:
  assumes "\<exists>x. P x"
  and "\<And>a. \<lbrakk> P a; \<forall>b. P b \<longrightarrow> a \<le> b \<rbrakk> \<Longrightarrow> Q a"
  shows "Q (Least P)"
using assms by clarify (blast intro!: LeastI2_wellorder)

lemma not_less_Least: "k < (LEAST x. P x) \<Longrightarrow> \<not> P k"
apply (simp add: not_le [symmetric])
apply (erule contrapos_nn)
apply (erule Least_le)
done

lemma exists_least_iff: "(\<exists>n. P n) \<longleftrightarrow> (\<exists>n. P n \<and> (\<forall>m < n. \<not> P m))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs thus ?lhs by blast
next
  assume H: ?lhs then obtain n where n: "P n" by blast
  let ?x = "Least P"
  { fix m assume m: "m < ?x"
    from not_less_Least[OF m] have "\<not> P m" . }
  with LeastI_ex[OF H] show ?rhs by blast
qed

end


subsection \<open>Order on \<^typ>\<open>bool\<close>\<close>

instantiation bool :: "{order_bot, order_top, linorder}"
begin

definition
  le_bool_def [simp]: "P \<le> Q \<longleftrightarrow> P \<longrightarrow> Q"

definition
  [simp]: "(P::bool) < Q \<longleftrightarrow> \<not> P \<and> Q"

definition
  [simp]: "\<bottom> \<longleftrightarrow> False"

definition
  [simp]: "\<top> \<longleftrightarrow> True"

instance proof
qed auto

end

lemma le_boolI: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<le> Q"
  by simp

lemma le_boolI': "P \<longrightarrow> Q \<Longrightarrow> P \<le> Q"
  by simp

lemma le_boolE: "P \<le> Q \<Longrightarrow> P \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma le_boolD: "P \<le> Q \<Longrightarrow> P \<longrightarrow> Q"
  by simp

lemma bot_boolE: "\<bottom> \<Longrightarrow> P"
  by simp

lemma top_boolI: \<top>
  by simp

lemma [code]:
  "False \<le> b \<longleftrightarrow> True"
  "True \<le> b \<longleftrightarrow> b"
  "False < b \<longleftrightarrow> b"
  "True < b \<longleftrightarrow> False"
  by simp_all


subsection \<open>Order on \<^typ>\<open>_ \<Rightarrow> _\<close>\<close>

instantiation "fun" :: (type, ord) ord
begin

definition
  le_fun_def: "f \<le> g \<longleftrightarrow> (\<forall>x. f x \<le> g x)"

definition
  "(f::'a \<Rightarrow> 'b) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"

instance ..

end

instance "fun" :: (type, preorder) preorder proof
qed (auto simp add: le_fun_def less_fun_def
  intro: order_trans order.antisym)

instance "fun" :: (type, order) order proof
qed (auto simp add: le_fun_def intro: order.antisym)

instantiation "fun" :: (type, bot) bot
begin

definition
  "\<bottom> = (\<lambda>x. \<bottom>)"

instance ..

end

instantiation "fun" :: (type, order_bot) order_bot
begin

lemma bot_apply [simp, code]:
  "\<bottom> x = \<bottom>"
  by (simp add: bot_fun_def)

instance proof
qed (simp add: le_fun_def)

end

instantiation "fun" :: (type, top) top
begin

definition
  [no_atp]: "\<top> = (\<lambda>x. \<top>)"

instance ..

end

instantiation "fun" :: (type, order_top) order_top
begin

lemma top_apply [simp, code]:
  "\<top> x = \<top>"
  by (simp add: top_fun_def)

instance proof
qed (simp add: le_fun_def)

end

lemma le_funI: "(\<And>x. f x \<le> g x) \<Longrightarrow> f \<le> g"
  unfolding le_fun_def by simp

lemma le_funE: "f \<le> g \<Longrightarrow> (f x \<le> g x \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding le_fun_def by simp

lemma le_funD: "f \<le> g \<Longrightarrow> f x \<le> g x"
  by (rule le_funE)


subsection \<open>Order on unary and binary predicates\<close>

lemma predicate1I:
  assumes PQ: "\<And>x. P x \<Longrightarrow> Q x"
  shows "P \<le> Q"
  apply (rule le_funI)
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate1D:
  "P \<le> Q \<Longrightarrow> P x \<Longrightarrow> Q x"
  apply (erule le_funE)
  apply (erule le_boolE)
  apply assumption+
  done

lemma rev_predicate1D:
  "P x \<Longrightarrow> P \<le> Q \<Longrightarrow> Q x"
  by (rule predicate1D)

lemma predicate2I:
  assumes PQ: "\<And>x y. P x y \<Longrightarrow> Q x y"
  shows "P \<le> Q"
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate2D:
  "P \<le> Q \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  apply (erule le_funE)+
  apply (erule le_boolE)
  apply assumption+
  done

lemma rev_predicate2D:
  "P x y \<Longrightarrow> P \<le> Q \<Longrightarrow> Q x y"
  by (rule predicate2D)

lemma bot1E [no_atp]: "\<bottom> x \<Longrightarrow> P"
  by (simp add: bot_fun_def)

lemma bot2E: "\<bottom> x y \<Longrightarrow> P"
  by (simp add: bot_fun_def)

lemma top1I: "\<top> x"
  by (simp add: top_fun_def)

lemma top2I: "\<top> x y"
  by (simp add: top_fun_def)


subsection \<open>Name duplicates\<close>

lemmas antisym = order.antisym
lemmas eq_iff = order.eq_iff

lemmas order_eq_refl = preorder_class.eq_refl
lemmas order_less_irrefl = preorder_class.less_irrefl
lemmas order_less_imp_le = preorder_class.less_imp_le
lemmas order_less_not_sym = preorder_class.less_not_sym
lemmas order_less_asym = preorder_class.less_asym
lemmas order_less_trans = preorder_class.less_trans
lemmas order_le_less_trans = preorder_class.le_less_trans
lemmas order_less_le_trans = preorder_class.less_le_trans
lemmas order_less_imp_not_less = preorder_class.less_imp_not_less
lemmas order_less_imp_triv = preorder_class.less_imp_triv
lemmas order_less_asym' = preorder_class.less_asym'

lemmas order_less_le = order_class.less_le
lemmas order_le_less = order_class.le_less
lemmas order_le_imp_less_or_eq = order_class.le_imp_less_or_eq
lemmas order_less_imp_not_eq = order_class.less_imp_not_eq
lemmas order_less_imp_not_eq2 = order_class.less_imp_not_eq2
lemmas order_neq_le_trans = order_class.neq_le_trans
lemmas order_le_neq_trans = order_class.le_neq_trans
lemmas order_eq_iff = order_class.order.eq_iff
lemmas order_antisym_conv = order_class.antisym_conv

lemmas linorder_linear = linorder_class.linear
lemmas linorder_less_linear = linorder_class.less_linear
lemmas linorder_le_less_linear = linorder_class.le_less_linear
lemmas linorder_le_cases = linorder_class.le_cases
lemmas linorder_not_less = linorder_class.not_less
lemmas linorder_not_le = linorder_class.not_le
lemmas linorder_neq_iff = linorder_class.neq_iff
lemmas linorder_neqE = linorder_class.neqE

end
