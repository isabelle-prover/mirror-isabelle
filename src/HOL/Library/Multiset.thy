(*  Title:      HOL/Library/Multiset.thy
    Author:     Tobias Nipkow, Markus Wenzel, Lawrence C Paulson, Norbert Voelker
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Mathias Fleury, MPII
    Author:     Martin Desharnais, MPI-INF Saarbruecken
*)

section \<open>(Finite) Multisets\<close>

theory Multiset
  imports Cancellation
begin

subsection \<open>The type of multisets\<close>

typedef 'a multiset = \<open>{f :: 'a \<Rightarrow> nat. finite {x. f x > 0}}\<close>
  morphisms count Abs_multiset
proof
  show \<open>(\<lambda>x. 0::nat) \<in> {f. finite {x. f x > 0}}\<close>
    by simp
qed

setup_lifting type_definition_multiset

lemma count_Abs_multiset:
  \<open>count (Abs_multiset f) = f\<close> if \<open>finite {x. f x > 0}\<close>
  by (rule Abs_multiset_inverse) (simp add: that)

lemma multiset_eq_iff: "M = N \<longleftrightarrow> (\<forall>a. count M a = count N a)"
  by (simp only: count_inject [symmetric] fun_eq_iff)

lemma multiset_eqI: "(\<And>x. count A x = count B x) \<Longrightarrow> A = B"
  using multiset_eq_iff by auto

text \<open>Preservation of the representing set \<^term>\<open>multiset\<close>.\<close>

lemma diff_preserves_multiset:
  \<open>finite {x. 0 < M x - N x}\<close> if \<open>finite {x. 0 < M x}\<close> for M N :: \<open>'a \<Rightarrow> nat\<close>
  using that by (rule rev_finite_subset) auto

lemma filter_preserves_multiset:
  \<open>finite {x. 0 < (if P x then M x else 0)}\<close> if \<open>finite {x. 0 < M x}\<close> for M N :: \<open>'a \<Rightarrow> nat\<close>
  using that by (rule rev_finite_subset) auto

lemmas in_multiset = diff_preserves_multiset filter_preserves_multiset


subsection \<open>Representing multisets\<close>

text \<open>Multiset enumeration\<close>

instantiation multiset :: (type) cancel_comm_monoid_add
begin

lift_definition zero_multiset :: \<open>'a multiset\<close>
  is \<open>\<lambda>a. 0\<close>
  by simp

abbreviation empty_mset :: \<open>'a multiset\<close> (\<open>{#}\<close>)
  where \<open>empty_mset \<equiv> 0\<close>

lift_definition plus_multiset :: \<open>'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close>
  is \<open>\<lambda>M N a. M a + N a\<close>
  by simp

lift_definition minus_multiset :: \<open>'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close>
  is \<open>\<lambda>M N a. M a - N a\<close>
  by (rule diff_preserves_multiset)

instance
  by (standard; transfer) (simp_all add: fun_eq_iff)

end

context
begin

qualified definition is_empty :: "'a multiset \<Rightarrow> bool" where
  [code_abbrev]: "is_empty A \<longleftrightarrow> A = {#}"

end

lemma add_mset_in_multiset:
  \<open>finite {x. 0 < (if x = a then Suc (M x) else M x)}\<close>
  if \<open>finite {x. 0 < M x}\<close>
  using that by (simp add: flip: insert_Collect)

lift_definition add_mset :: "'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" is
  "\<lambda>a M b. if b = a then Suc (M b) else M b"
by (rule add_mset_in_multiset)

syntax
  "_multiset" :: "args \<Rightarrow> 'a multiset"    ("{#(_)#}")
translations
  "{#x, xs#}" == "CONST add_mset x {#xs#}"
  "{#x#}" == "CONST add_mset x {#}"

lemma count_empty [simp]: "count {#} a = 0"
  by (simp add: zero_multiset.rep_eq)

lemma count_add_mset [simp]:
  "count (add_mset b A) a = (if b = a then Suc (count A a) else count A a)"
  by (simp add: add_mset.rep_eq)

lemma count_single: "count {#b#} a = (if b = a then 1 else 0)"
  by simp

lemma
  add_mset_not_empty [simp]: \<open>add_mset a A \<noteq> {#}\<close> and
  empty_not_add_mset [simp]: "{#} \<noteq> add_mset a A"
  by (auto simp: multiset_eq_iff)

lemma add_mset_add_mset_same_iff [simp]:
  "add_mset a A = add_mset a B \<longleftrightarrow> A = B"
  by (auto simp: multiset_eq_iff)

lemma add_mset_commute:
  "add_mset x (add_mset y M) = add_mset y (add_mset x M)"
  by (auto simp: multiset_eq_iff)


subsection \<open>Basic operations\<close>

subsubsection \<open>Conversion to set and membership\<close>

definition set_mset :: \<open>'a multiset \<Rightarrow> 'a set\<close>
  where \<open>set_mset M = {x. count M x > 0}\<close>

abbreviation member_mset :: \<open>'a \<Rightarrow> 'a multiset \<Rightarrow> bool\<close>
  where \<open>member_mset a M \<equiv> a \<in> set_mset M\<close>

notation
  member_mset  (\<open>'(\<in>#')\<close>) and
  member_mset  (\<open>(_/ \<in># _)\<close> [50, 51] 50)

notation  (ASCII)
  member_mset  (\<open>'(:#')\<close>) and
  member_mset  (\<open>(_/ :# _)\<close> [50, 51] 50)

abbreviation not_member_mset :: \<open>'a \<Rightarrow> 'a multiset \<Rightarrow> bool\<close>
  where \<open>not_member_mset a M \<equiv> a \<notin> set_mset M\<close>

notation
  not_member_mset  (\<open>'(\<notin>#')\<close>) and
  not_member_mset  (\<open>(_/ \<notin># _)\<close> [50, 51] 50)

notation  (ASCII)
  not_member_mset  (\<open>'(~:#')\<close>) and
  not_member_mset  (\<open>(_/ ~:# _)\<close> [50, 51] 50)

context
begin

qualified abbreviation Ball :: "'a multiset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ball M \<equiv> Set.Ball (set_mset M)"

qualified abbreviation Bex :: "'a multiset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex M \<equiv> Set.Bex (set_mset M)"

end

syntax
  "_MBall"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>_\<in>#_./ _)" [0, 0, 10] 10)
  "_MBex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>_\<in>#_./ _)" [0, 0, 10] 10)

syntax  (ASCII)
  "_MBall"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>_:#_./ _)" [0, 0, 10] 10)
  "_MBex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>_:#_./ _)" [0, 0, 10] 10)

translations
  "\<forall>x\<in>#A. P" \<rightleftharpoons> "CONST Multiset.Ball A (\<lambda>x. P)"
  "\<exists>x\<in>#A. P" \<rightleftharpoons> "CONST Multiset.Bex A (\<lambda>x. P)"

print_translation \<open>
 [Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>Multiset.Ball\<close> \<^syntax_const>\<open>_MBall\<close>,
  Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>Multiset.Bex\<close> \<^syntax_const>\<open>_MBex\<close>]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

lemma count_eq_zero_iff:
  "count M x = 0 \<longleftrightarrow> x \<notin># M"
  by (auto simp add: set_mset_def)

lemma not_in_iff:
  "x \<notin># M \<longleftrightarrow> count M x = 0"
  by (auto simp add: count_eq_zero_iff)

lemma count_greater_zero_iff [simp]:
  "count M x > 0 \<longleftrightarrow> x \<in># M"
  by (auto simp add: set_mset_def)

lemma count_inI:
  assumes "count M x = 0 \<Longrightarrow> False"
  shows "x \<in># M"
proof (rule ccontr)
  assume "x \<notin># M"
  with assms show False by (simp add: not_in_iff)
qed

lemma in_countE:
  assumes "x \<in># M"
  obtains n where "count M x = Suc n"
proof -
  from assms have "count M x > 0" by simp
  then obtain n where "count M x = Suc n"
    using gr0_conv_Suc by blast
  with that show thesis .
qed

lemma count_greater_eq_Suc_zero_iff [simp]:
  "count M x \<ge> Suc 0 \<longleftrightarrow> x \<in># M"
  by (simp add: Suc_le_eq)

lemma count_greater_eq_one_iff [simp]:
  "count M x \<ge> 1 \<longleftrightarrow> x \<in># M"
  by simp

lemma set_mset_empty [simp]:
  "set_mset {#} = {}"
  by (simp add: set_mset_def)

lemma set_mset_single:
  "set_mset {#b#} = {b}"
  by (simp add: set_mset_def)

lemma set_mset_eq_empty_iff [simp]:
  "set_mset M = {} \<longleftrightarrow> M = {#}"
  by (auto simp add: multiset_eq_iff count_eq_zero_iff)

lemma finite_set_mset [iff]:
  "finite (set_mset M)"
  using count [of M] by simp

lemma set_mset_add_mset_insert [simp]: \<open>set_mset (add_mset a A) = insert a (set_mset A)\<close>
  by (auto simp flip: count_greater_eq_Suc_zero_iff split: if_splits)

lemma multiset_nonemptyE [elim]:
  assumes "A \<noteq> {#}"
  obtains x where "x \<in># A"
proof -
  have "\<exists>x. x \<in># A" by (rule ccontr) (insert assms, auto)
  with that show ?thesis by blast
qed

lemma count_gt_imp_in_mset: "count M x > n \<Longrightarrow> x \<in># M"
  using count_greater_zero_iff by fastforce


subsubsection \<open>Union\<close>

lemma count_union [simp]:
  "count (M + N) a = count M a + count N a"
  by (simp add: plus_multiset.rep_eq)

lemma set_mset_union [simp]:
  "set_mset (M + N) = set_mset M \<union> set_mset N"
  by (simp only: set_eq_iff count_greater_zero_iff [symmetric] count_union) simp

lemma union_mset_add_mset_left [simp]:
  "add_mset a A + B = add_mset a (A + B)"
  by (auto simp: multiset_eq_iff)

lemma union_mset_add_mset_right [simp]:
  "A + add_mset a B = add_mset a (A + B)"
  by (auto simp: multiset_eq_iff)

lemma add_mset_add_single: \<open>add_mset a A = A + {#a#}\<close>
  by (subst union_mset_add_mset_right, subst add.comm_neutral) standard


subsubsection \<open>Difference\<close>

instance multiset :: (type) comm_monoid_diff
  by standard (transfer; simp add: fun_eq_iff)

lemma count_diff [simp]:
  "count (M - N) a = count M a - count N a"
  by (simp add: minus_multiset.rep_eq)

lemma add_mset_diff_bothsides:
  \<open>add_mset a M - add_mset a A = M - A\<close>
  by (auto simp: multiset_eq_iff)

lemma in_diff_count:
  "a \<in># M - N \<longleftrightarrow> count N a < count M a"
  by (simp add: set_mset_def)

lemma count_in_diffI:
  assumes "\<And>n. count N x = n + count M x \<Longrightarrow> False"
  shows "x \<in># M - N"
proof (rule ccontr)
  assume "x \<notin># M - N"
  then have "count N x = (count N x - count M x) + count M x"
    by (simp add: in_diff_count not_less)
  with assms show False by auto
qed

lemma in_diff_countE:
  assumes "x \<in># M - N"
  obtains n where "count M x = Suc n + count N x"
proof -
  from assms have "count M x - count N x > 0" by (simp add: in_diff_count)
  then have "count M x > count N x" by simp
  then obtain n where "count M x = Suc n + count N x"
    using less_iff_Suc_add by auto
  with that show thesis .
qed

lemma in_diffD:
  assumes "a \<in># M - N"
  shows "a \<in># M"
proof -
  have "0 \<le> count N a" by simp
  also from assms have "count N a < count M a"
    by (simp add: in_diff_count)
  finally show ?thesis by simp
qed

lemma set_mset_diff:
  "set_mset (M - N) = {a. count N a < count M a}"
  by (simp add: set_mset_def)

lemma diff_empty [simp]: "M - {#} = M \<and> {#} - M = {#}"
  by rule (fact Groups.diff_zero, fact Groups.zero_diff)

lemma diff_cancel: "A - A = {#}"
  by (fact Groups.diff_cancel)

lemma diff_union_cancelR: "M + N - N = (M::'a multiset)"
  by (fact add_diff_cancel_right')

lemma diff_union_cancelL: "N + M - N = (M::'a multiset)"
  by (fact add_diff_cancel_left')

lemma diff_right_commute:
  fixes M N Q :: "'a multiset"
  shows "M - N - Q = M - Q - N"
  by (fact diff_right_commute)

lemma diff_add:
  fixes M N Q :: "'a multiset"
  shows "M - (N + Q) = M - N - Q"
  by (rule sym) (fact diff_diff_add)

lemma insert_DiffM [simp]: "x \<in># M \<Longrightarrow> add_mset x (M - {#x#}) = M"
  by (clarsimp simp: multiset_eq_iff)

lemma insert_DiffM2: "x \<in># M \<Longrightarrow> (M - {#x#}) + {#x#} = M"
  by simp

lemma diff_union_swap: "a \<noteq> b \<Longrightarrow> add_mset b (M - {#a#}) = add_mset b M - {#a#}"
  by (auto simp add: multiset_eq_iff)

lemma diff_add_mset_swap [simp]: "b \<notin># A \<Longrightarrow> add_mset b M - A = add_mset b (M - A)"
  by (auto simp add: multiset_eq_iff simp: not_in_iff)

lemma diff_union_swap2 [simp]: "y \<in># M \<Longrightarrow> add_mset x M - {#y#} = add_mset x (M - {#y#})"
  by (metis add_mset_diff_bothsides diff_union_swap diff_zero insert_DiffM)

lemma diff_diff_add_mset [simp]: "(M::'a multiset) - N - P = M - (N + P)"
  by (rule diff_diff_add)

lemma diff_union_single_conv:
  "a \<in># J \<Longrightarrow> I + J - {#a#} = I + (J - {#a#})"
  by (simp add: multiset_eq_iff Suc_le_eq)

lemma mset_add [elim?]:
  assumes "a \<in># A"
  obtains B where "A = add_mset a B"
proof -
  from assms have "A = add_mset a (A - {#a#})"
    by simp
  with that show thesis .
qed

lemma union_iff:
  "a \<in># A + B \<longleftrightarrow> a \<in># A \<or> a \<in># B"
  by auto

lemma count_minus_inter_lt_count_minus_inter_iff:
  "count (M2 - M1) y < count (M1 - M2) y \<longleftrightarrow> y \<in># M1 - M2"
  by (meson count_greater_zero_iff gr_implies_not_zero in_diff_count leI order.strict_trans2
      order_less_asym)

lemma minus_inter_eq_minus_inter_iff:
  "(M1 - M2) = (M2 - M1) \<longleftrightarrow> set_mset (M1 - M2) = set_mset (M2 - M1)"
  by (metis add.commute count_diff count_eq_zero_iff diff_add_zero in_diff_countE multiset_eq_iff)


subsubsection \<open>Min and Max\<close>

abbreviation Min_mset :: "'a::linorder multiset \<Rightarrow> 'a" where
"Min_mset m \<equiv> Min (set_mset m)"

abbreviation Max_mset :: "'a::linorder multiset \<Rightarrow> 'a" where
"Max_mset m \<equiv> Max (set_mset m)"

lemma
  Min_in_mset: "M \<noteq> {#} \<Longrightarrow> Min_mset M \<in># M" and
  Max_in_mset: "M \<noteq> {#} \<Longrightarrow> Max_mset M \<in># M"
  by simp+


subsubsection \<open>Equality of multisets\<close>

lemma single_eq_single [simp]: "{#a#} = {#b#} \<longleftrightarrow> a = b"
  by (auto simp add: multiset_eq_iff)

lemma union_eq_empty [iff]: "M + N = {#} \<longleftrightarrow> M = {#} \<and> N = {#}"
  by (auto simp add: multiset_eq_iff)

lemma empty_eq_union [iff]: "{#} = M + N \<longleftrightarrow> M = {#} \<and> N = {#}"
  by (auto simp add: multiset_eq_iff)

lemma multi_self_add_other_not_self [simp]: "M = add_mset x M \<longleftrightarrow> False"
  by (auto simp add: multiset_eq_iff)

lemma add_mset_remove_trivial [simp]: \<open>add_mset x M - {#x#} = M\<close>
  by (auto simp: multiset_eq_iff)

lemma diff_single_trivial: "\<not> x \<in># M \<Longrightarrow> M - {#x#} = M"
  by (auto simp add: multiset_eq_iff not_in_iff)

lemma diff_single_eq_union: "x \<in># M \<Longrightarrow> M - {#x#} = N \<longleftrightarrow> M = add_mset x N"
  by auto

lemma union_single_eq_diff: "add_mset x M = N \<Longrightarrow> M = N - {#x#}"
  unfolding add_mset_add_single[of _ M] by (fact add_implies_diff)

lemma union_single_eq_member: "add_mset x M = N \<Longrightarrow> x \<in># N"
  by auto

lemma add_mset_remove_trivial_If:
  "add_mset a (N - {#a#}) = (if a \<in># N then N else add_mset a N)"
  by (simp add: diff_single_trivial)

lemma add_mset_remove_trivial_eq: \<open>N = add_mset a (N - {#a#}) \<longleftrightarrow> a \<in># N\<close>
  by (auto simp: add_mset_remove_trivial_If)

lemma union_is_single:
  "M + N = {#a#} \<longleftrightarrow> M = {#a#} \<and> N = {#} \<or> M = {#} \<and> N = {#a#}"
  (is "?lhs = ?rhs")
proof
  show ?lhs if ?rhs using that by auto
  show ?rhs if ?lhs
    by (metis Multiset.diff_cancel add.commute add_diff_cancel_left' diff_add_zero diff_single_trivial insert_DiffM that)
qed

lemma single_is_union: "{#a#} = M + N \<longleftrightarrow> {#a#} = M \<and> N = {#} \<or> M = {#} \<and> {#a#} = N"
  by (auto simp add: eq_commute [of "{#a#}" "M + N"] union_is_single)

lemma add_eq_conv_diff:
  "add_mset a M = add_mset b N \<longleftrightarrow> M = N \<and> a = b \<or> M = add_mset b (N - {#a#}) \<and> N = add_mset a (M - {#b#})"
  (is "?lhs \<longleftrightarrow> ?rhs")
(* shorter: by (simp add: multiset_eq_iff) fastforce *)
proof
  show ?lhs if ?rhs
    using that
    by (auto simp add: add_mset_commute[of a b])
  show ?rhs if ?lhs
  proof (cases "a = b")
    case True with \<open>?lhs\<close> show ?thesis by simp
  next
    case False
    from \<open>?lhs\<close> have "a \<in># add_mset b N" by (rule union_single_eq_member)
    with False have "a \<in># N" by auto
    moreover from \<open>?lhs\<close> have "M = add_mset b N - {#a#}" by (rule union_single_eq_diff)
    moreover note False
    ultimately show ?thesis by (auto simp add: diff_right_commute [of _ "{#a#}"])
  qed
qed

lemma add_mset_eq_single [iff]: "add_mset b M = {#a#} \<longleftrightarrow> b = a \<and> M = {#}"
  by (auto simp: add_eq_conv_diff)

lemma single_eq_add_mset [iff]: "{#a#} = add_mset b M \<longleftrightarrow> b = a \<and> M = {#}"
  by (auto simp: add_eq_conv_diff)

lemma insert_noteq_member:
  assumes BC: "add_mset b B = add_mset c C"
   and bnotc: "b \<noteq> c"
  shows "c \<in># B"
proof -
  have "c \<in># add_mset c C" by simp
  have nc: "\<not> c \<in># {#b#}" using bnotc by simp
  then have "c \<in># add_mset b B" using BC by simp
  then show "c \<in># B" using nc by simp
qed

lemma add_eq_conv_ex:
  "(add_mset a M = add_mset b N) =
    (M = N \<and> a = b \<or> (\<exists>K. M = add_mset b K \<and> N = add_mset a K))"
  by (auto simp add: add_eq_conv_diff)

lemma multi_member_split: "x \<in># M \<Longrightarrow> \<exists>A. M = add_mset x A"
  by (rule exI [where x = "M - {#x#}"]) simp

lemma multiset_add_sub_el_shuffle:
  assumes "c \<in># B"
    and "b \<noteq> c"
  shows "add_mset b (B - {#c#}) = add_mset b B - {#c#}"
proof -
  from \<open>c \<in># B\<close> obtain A where B: "B = add_mset c A"
    by (blast dest: multi_member_split)
  have "add_mset b A = add_mset c (add_mset b A) - {#c#}" by simp
  then have "add_mset b A = add_mset b (add_mset c A) - {#c#}"
    by (simp add: \<open>b \<noteq> c\<close>)
  then show ?thesis using B by simp
qed

lemma add_mset_eq_singleton_iff[iff]:
  "add_mset x M = {#y#} \<longleftrightarrow> M = {#} \<and> x = y"
  by auto


subsubsection \<open>Pointwise ordering induced by count\<close>

definition subseteq_mset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"  (infix "\<subseteq>#" 50)
  where "A \<subseteq># B \<longleftrightarrow> (\<forall>a. count A a \<le> count B a)"

definition subset_mset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" (infix "\<subset>#" 50)
  where "A \<subset># B \<longleftrightarrow> A \<subseteq># B \<and> A \<noteq> B"

abbreviation (input) supseteq_mset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"  (infix "\<supseteq>#" 50)
  where "supseteq_mset A B \<equiv> B \<subseteq># A"

abbreviation (input) supset_mset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"  (infix "\<supset>#" 50)
  where "supset_mset A B \<equiv> B \<subset># A"

notation (input)
  subseteq_mset  (infix "\<le>#" 50) and
  supseteq_mset  (infix "\<ge>#" 50)

notation (ASCII)
  subseteq_mset  (infix "<=#" 50) and
  subset_mset  (infix "<#" 50) and
  supseteq_mset  (infix ">=#" 50) and
  supset_mset  (infix ">#" 50)

global_interpretation subset_mset: ordering \<open>(\<subseteq>#)\<close> \<open>(\<subset>#)\<close>
  by standard (auto simp add: subset_mset_def subseteq_mset_def multiset_eq_iff intro: order.trans order.antisym)

interpretation subset_mset: ordered_ab_semigroup_add_imp_le \<open>(+)\<close> \<open>(-)\<close> \<open>(\<subseteq>#)\<close> \<open>(\<subset>#)\<close>
  by standard (auto simp add: subset_mset_def subseteq_mset_def multiset_eq_iff intro: order_trans antisym)
    \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>

interpretation subset_mset: ordered_ab_semigroup_monoid_add_imp_le "(+)" 0 "(-)" "(\<subseteq>#)" "(\<subset>#)"
  by standard
    \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>

lemma mset_subset_eqI:
  "(\<And>a. count A a \<le> count B a) \<Longrightarrow> A \<subseteq># B"
  by (simp add: subseteq_mset_def)

lemma mset_subset_eq_count:
  "A \<subseteq># B \<Longrightarrow> count A a \<le> count B a"
  by (simp add: subseteq_mset_def)

lemma mset_subset_eq_exists_conv: "(A::'a multiset) \<subseteq># B \<longleftrightarrow> (\<exists>C. B = A + C)"
  unfolding subseteq_mset_def
  by (metis add_diff_cancel_left' count_diff count_union le_Suc_ex le_add_same_cancel1 multiset_eq_iff zero_le)

interpretation subset_mset: ordered_cancel_comm_monoid_diff "(+)" 0 "(\<subseteq>#)" "(\<subset>#)" "(-)"
  by standard (simp, fact mset_subset_eq_exists_conv)
    \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>

declare subset_mset.add_diff_assoc[simp] subset_mset.add_diff_assoc2[simp]

lemma mset_subset_eq_mono_add_right_cancel: "(A::'a multiset) + C \<subseteq># B + C \<longleftrightarrow> A \<subseteq># B"
   by (fact subset_mset.add_le_cancel_right)

lemma mset_subset_eq_mono_add_left_cancel: "C + (A::'a multiset) \<subseteq># C + B \<longleftrightarrow> A \<subseteq># B"
   by (fact subset_mset.add_le_cancel_left)

lemma mset_subset_eq_mono_add: "(A::'a multiset) \<subseteq># B \<Longrightarrow> C \<subseteq># D \<Longrightarrow> A + C \<subseteq># B + D"
   by (fact subset_mset.add_mono)

lemma mset_subset_eq_add_left: "(A::'a multiset) \<subseteq># A + B"
   by simp

lemma mset_subset_eq_add_right: "B \<subseteq># (A::'a multiset) + B"
   by simp

lemma single_subset_iff [simp]:
  "{#a#} \<subseteq># M \<longleftrightarrow> a \<in># M"
  by (auto simp add: subseteq_mset_def Suc_le_eq)

lemma mset_subset_eq_single: "a \<in># B \<Longrightarrow> {#a#} \<subseteq># B"
  by simp

lemma mset_subset_eq_add_mset_cancel: \<open>add_mset a A \<subseteq># add_mset a B \<longleftrightarrow> A \<subseteq># B\<close>
  unfolding add_mset_add_single[of _ A] add_mset_add_single[of _ B]
  by (rule mset_subset_eq_mono_add_right_cancel)

lemma multiset_diff_union_assoc:
  fixes A B C D :: "'a multiset"
  shows "C \<subseteq># B \<Longrightarrow> A + B - C = A + (B - C)"
  by (fact subset_mset.diff_add_assoc)

lemma mset_subset_eq_multiset_union_diff_commute:
  fixes A B C D :: "'a multiset"
  shows "B \<subseteq># A \<Longrightarrow> A - B + C = A + C - B"
  by (fact subset_mset.add_diff_assoc2)

lemma diff_subset_eq_self[simp]:
  "(M::'a multiset) - N \<subseteq># M"
  by (simp add: subseteq_mset_def)

lemma mset_subset_eqD:
  assumes "A \<subseteq># B" and "x \<in># A"
  shows "x \<in># B"
proof -
  from \<open>x \<in># A\<close> have "count A x > 0" by simp
  also from \<open>A \<subseteq># B\<close> have "count A x \<le> count B x"
    by (simp add: subseteq_mset_def)
  finally show ?thesis by simp
qed

lemma mset_subsetD:
  "A \<subset># B \<Longrightarrow> x \<in># A \<Longrightarrow> x \<in># B"
  by (auto intro: mset_subset_eqD [of A])

lemma set_mset_mono:
  "A \<subseteq># B \<Longrightarrow> set_mset A \<subseteq> set_mset B"
  by (metis mset_subset_eqD subsetI)

lemma mset_subset_eq_insertD:
  assumes "add_mset x A \<subseteq># B"
  shows "x \<in># B \<and> A \<subset># B"
proof 
  show "x \<in># B"
    using assms by (simp add: mset_subset_eqD)
  have "A \<subseteq># add_mset x A"
    by (metis (no_types) add_mset_add_single mset_subset_eq_add_left)
  then have "A \<subset># add_mset x A"
    by (meson multi_self_add_other_not_self subset_mset.le_imp_less_or_eq)
  then show "A \<subset># B"
    using assms subset_mset.strict_trans2 by blast
qed

lemma mset_subset_insertD:
  "add_mset x A \<subset># B \<Longrightarrow> x \<in># B \<and> A \<subset># B"
  by (rule mset_subset_eq_insertD) simp

lemma mset_subset_of_empty[simp]: "A \<subset># {#} \<longleftrightarrow> False"
  by (simp only: subset_mset.not_less_zero)

lemma empty_subset_add_mset[simp]: "{#} \<subset># add_mset x M"
  by (auto intro: subset_mset.gr_zeroI)

lemma empty_le: "{#} \<subseteq># A"
  by (fact subset_mset.zero_le)

lemma insert_subset_eq_iff:
  "add_mset a A \<subseteq># B \<longleftrightarrow> a \<in># B \<and> A \<subseteq># B - {#a#}"
  using mset_subset_eq_insertD subset_mset.le_diff_conv2 by fastforce

lemma insert_union_subset_iff:
  "add_mset a A \<subset># B \<longleftrightarrow> a \<in># B \<and> A \<subset># B - {#a#}"
  by (auto simp add: insert_subset_eq_iff subset_mset_def)

lemma subset_eq_diff_conv:
  "A - C \<subseteq># B \<longleftrightarrow> A \<subseteq># B + C"
  by (simp add: subseteq_mset_def le_diff_conv)

lemma multi_psub_of_add_self [simp]: "A \<subset># add_mset x A"
  by (auto simp: subset_mset_def subseteq_mset_def)

lemma multi_psub_self: "A \<subset># A = False"
  by simp

lemma mset_subset_add_mset [simp]: "add_mset x N \<subset># add_mset x M \<longleftrightarrow> N \<subset># M"
  unfolding add_mset_add_single[of _ N] add_mset_add_single[of _ M]
  by (fact subset_mset.add_less_cancel_right)

lemma mset_subset_diff_self: "c \<in># B \<Longrightarrow> B - {#c#} \<subset># B"
  by (auto simp: subset_mset_def elim: mset_add)

lemma Diff_eq_empty_iff_mset: "A - B = {#} \<longleftrightarrow> A \<subseteq># B"
  by (auto simp: multiset_eq_iff subseteq_mset_def)

lemma add_mset_subseteq_single_iff[iff]: "add_mset a M \<subseteq># {#b#} \<longleftrightarrow> M = {#} \<and> a = b"
proof
  assume A: "add_mset a M \<subseteq># {#b#}"
  then have \<open>a = b\<close>
    by (auto dest: mset_subset_eq_insertD)
  then show "M={#} \<and> a=b"
    using A by (simp add: mset_subset_eq_add_mset_cancel)
qed simp

lemma nonempty_subseteq_mset_eq_single: "M \<noteq> {#} \<Longrightarrow> M \<subseteq># {#x#} \<Longrightarrow> M = {#x#}"
  by (cases M) (metis single_is_union subset_mset.less_eqE)

lemma nonempty_subseteq_mset_iff_single: "(M \<noteq> {#} \<and> M \<subseteq># {#x#} \<and> P) \<longleftrightarrow> M = {#x#} \<and> P"
  by (cases M) (metis empty_not_add_mset nonempty_subseteq_mset_eq_single subset_mset.order_refl)


subsubsection \<open>Intersection and bounded union\<close>

definition inter_mset :: \<open>'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close>  (infixl \<open>\<inter>#\<close> 70)
  where \<open>A \<inter># B = A - (A - B)\<close>

lemma count_inter_mset [simp]:
  \<open>count (A \<inter># B) x = min (count A x) (count B x)\<close>
  by (simp add: inter_mset_def)

(*global_interpretation subset_mset: semilattice_order \<open>(\<inter>#)\<close> \<open>(\<subseteq>#)\<close> \<open>(\<subset>#)\<close>
  by standard (simp_all add: multiset_eq_iff subseteq_mset_def subset_mset_def min_def)*)

interpretation subset_mset: semilattice_inf \<open>(\<inter>#)\<close> \<open>(\<subseteq>#)\<close> \<open>(\<subset>#)\<close>
  by standard (simp_all add: multiset_eq_iff subseteq_mset_def)
  \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>

definition union_mset :: \<open>'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close>  (infixl \<open>\<union>#\<close> 70)
  where \<open>A \<union># B = A + (B - A)\<close>

lemma count_union_mset [simp]:
  \<open>count (A \<union># B) x = max (count A x) (count B x)\<close>
  by (simp add: union_mset_def)

global_interpretation subset_mset: semilattice_neutr_order \<open>(\<union>#)\<close> \<open>{#}\<close> \<open>(\<supseteq>#)\<close> \<open>(\<supset>#)\<close>
proof 
  show "\<And>a b. (b \<subseteq># a) = (a = a \<union># b)"
    by (simp add: Diff_eq_empty_iff_mset union_mset_def)
  show "\<And>a b. (b \<subset># a) = (a = a \<union># b \<and> a \<noteq> b)"
    by (metis Diff_eq_empty_iff_mset add_cancel_left_right subset_mset_def union_mset_def)
qed (auto simp: multiset_eqI union_mset_def)

interpretation subset_mset: semilattice_sup \<open>(\<union>#)\<close> \<open>(\<subseteq>#)\<close> \<open>(\<subset>#)\<close>
proof -
  have [simp]: "m \<le> n \<Longrightarrow> q \<le> n \<Longrightarrow> m + (q - m) \<le> n" for m n q :: nat
    by arith
  show "class.semilattice_sup (\<union>#) (\<subseteq>#) (\<subset>#)"
    by standard (auto simp add: union_mset_def subseteq_mset_def)
qed \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>

interpretation subset_mset: bounded_lattice_bot "(\<inter>#)" "(\<subseteq>#)" "(\<subset>#)"
  "(\<union>#)" "{#}"
  by standard auto
    \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>


subsubsection \<open>Additional intersection facts\<close>

lemma set_mset_inter [simp]:
  "set_mset (A \<inter># B) = set_mset A \<inter> set_mset B"
  by (simp only: set_mset_def) auto

lemma diff_intersect_left_idem [simp]:
  "M - M \<inter># N = M - N"
  by (simp add: multiset_eq_iff min_def)

lemma diff_intersect_right_idem [simp]:
  "M - N \<inter># M = M - N"
  by (simp add: multiset_eq_iff min_def)

lemma multiset_inter_single[simp]: "a \<noteq> b \<Longrightarrow> {#a#} \<inter># {#b#} = {#}"
  by (rule multiset_eqI) auto

lemma multiset_union_diff_commute:
  assumes "B \<inter># C = {#}"
  shows "A + B - C = A - C + B"
proof (rule multiset_eqI)
  fix x
  from assms have "min (count B x) (count C x) = 0"
    by (auto simp add: multiset_eq_iff)
  then have "count B x = 0 \<or> count C x = 0"
    unfolding min_def by (auto split: if_splits)
  then show "count (A + B - C) x = count (A - C + B) x"
    by auto
qed

lemma disjunct_not_in:
  "A \<inter># B = {#} \<longleftrightarrow> (\<forall>a. a \<notin># A \<or> a \<notin># B)"
  by (metis disjoint_iff set_mset_eq_empty_iff set_mset_inter)

lemma inter_mset_empty_distrib_right: "A \<inter># (B + C) = {#} \<longleftrightarrow> A \<inter># B = {#} \<and> A \<inter># C = {#}"
  by (meson disjunct_not_in union_iff)

lemma inter_mset_empty_distrib_left: "(A + B) \<inter># C = {#} \<longleftrightarrow> A \<inter># C = {#} \<and> B \<inter># C = {#}"
  by (meson disjunct_not_in union_iff)

lemma add_mset_inter_add_mset [simp]:
  "add_mset a A \<inter># add_mset a B = add_mset a (A \<inter># B)"
  by (rule multiset_eqI) simp

lemma add_mset_disjoint [simp]:
  "add_mset a A \<inter># B = {#} \<longleftrightarrow> a \<notin># B \<and> A \<inter># B = {#}"
  "{#} = add_mset a A \<inter># B \<longleftrightarrow> a \<notin># B \<and> {#} = A \<inter># B"
  by (auto simp: disjunct_not_in)

lemma disjoint_add_mset [simp]:
  "B \<inter># add_mset a A = {#} \<longleftrightarrow> a \<notin># B \<and> B \<inter># A = {#}"
  "{#} = A \<inter># add_mset b B \<longleftrightarrow> b \<notin># A \<and> {#} = A \<inter># B"
  by (auto simp: disjunct_not_in)

lemma inter_add_left1: "\<not> x \<in># N \<Longrightarrow> (add_mset x M) \<inter># N = M \<inter># N"
  by (simp add: multiset_eq_iff not_in_iff)

lemma inter_add_left2: "x \<in># N \<Longrightarrow> (add_mset x M) \<inter># N = add_mset x (M \<inter># (N - {#x#}))"
  by (auto simp add: multiset_eq_iff elim: mset_add)

lemma inter_add_right1: "\<not> x \<in># N \<Longrightarrow> N \<inter># (add_mset x M) = N \<inter># M"
  by (simp add: multiset_eq_iff not_in_iff)

lemma inter_add_right2: "x \<in># N \<Longrightarrow> N \<inter># (add_mset x M) = add_mset x ((N - {#x#}) \<inter># M)"
  by (auto simp add: multiset_eq_iff elim: mset_add)

lemma disjunct_set_mset_diff:
  assumes "M \<inter># N = {#}"
  shows "set_mset (M - N) = set_mset M"
proof (rule set_eqI)
  fix a
  from assms have "a \<notin># M \<or> a \<notin># N"
    by (simp add: disjunct_not_in)
  then show "a \<in># M - N \<longleftrightarrow> a \<in># M"
    by (auto dest: in_diffD) (simp add: in_diff_count not_in_iff)
qed

lemma at_most_one_mset_mset_diff:
  assumes "a \<notin># M - {#a#}"
  shows "set_mset (M - {#a#}) = set_mset M - {a}"
  using assms by (auto simp add: not_in_iff in_diff_count set_eq_iff)

lemma more_than_one_mset_mset_diff:
  assumes "a \<in># M - {#a#}"
  shows "set_mset (M - {#a#}) = set_mset M"
proof (rule set_eqI)
  fix b
  have "Suc 0 < count M b \<Longrightarrow> count M b > 0" by arith
  then show "b \<in># M - {#a#} \<longleftrightarrow> b \<in># M"
    using assms by (auto simp add: in_diff_count)
qed

lemma inter_iff:
  "a \<in># A \<inter># B \<longleftrightarrow> a \<in># A \<and> a \<in># B"
  by simp

lemma inter_union_distrib_left:
  "A \<inter># B + C = (A + C) \<inter># (B + C)"
  by (simp add: multiset_eq_iff min_add_distrib_left)

lemma inter_union_distrib_right:
  "C + A \<inter># B = (C + A) \<inter># (C + B)"
  using inter_union_distrib_left [of A B C] by (simp add: ac_simps)

lemma inter_subset_eq_union:
  "A \<inter># B \<subseteq># A + B"
  by (auto simp add: subseteq_mset_def)


subsubsection \<open>Additional bounded union facts\<close>

lemma set_mset_sup [simp]:
  \<open>set_mset (A \<union># B) = set_mset A \<union> set_mset B\<close>
  by (simp only: set_mset_def) (auto simp add: less_max_iff_disj)

lemma sup_union_left1 [simp]: "\<not> x \<in># N \<Longrightarrow> (add_mset x M) \<union># N = add_mset x (M \<union># N)"
  by (simp add: multiset_eq_iff not_in_iff)

lemma sup_union_left2: "x \<in># N \<Longrightarrow> (add_mset x M) \<union># N = add_mset x (M \<union># (N - {#x#}))"
  by (simp add: multiset_eq_iff)

lemma sup_union_right1 [simp]: "\<not> x \<in># N \<Longrightarrow> N \<union># (add_mset x M) = add_mset x (N \<union># M)"
  by (simp add: multiset_eq_iff not_in_iff)

lemma sup_union_right2: "x \<in># N \<Longrightarrow> N \<union># (add_mset x M) = add_mset x ((N - {#x#}) \<union># M)"
  by (simp add: multiset_eq_iff)

lemma sup_union_distrib_left:
  "A \<union># B + C = (A + C) \<union># (B + C)"
  by (simp add: multiset_eq_iff max_add_distrib_left)

lemma union_sup_distrib_right:
  "C + A \<union># B = (C + A) \<union># (C + B)"
  using sup_union_distrib_left [of A B C] by (simp add: ac_simps)

lemma union_diff_inter_eq_sup:
  "A + B - A \<inter># B = A \<union># B"
  by (auto simp add: multiset_eq_iff)

lemma union_diff_sup_eq_inter:
  "A + B - A \<union># B = A \<inter># B"
  by (auto simp add: multiset_eq_iff)

lemma add_mset_union:
  \<open>add_mset a A \<union># add_mset a B = add_mset a (A \<union># B)\<close>
  by (auto simp: multiset_eq_iff max_def)


subsection \<open>Replicate and repeat operations\<close>

definition replicate_mset :: "nat \<Rightarrow> 'a \<Rightarrow> 'a multiset" where
  "replicate_mset n x = (add_mset x ^^ n) {#}"

lemma replicate_mset_0[simp]: "replicate_mset 0 x = {#}"
  unfolding replicate_mset_def by simp

lemma replicate_mset_Suc [simp]: "replicate_mset (Suc n) x = add_mset x (replicate_mset n x)"
  unfolding replicate_mset_def by (induct n) (auto intro: add.commute)

lemma count_replicate_mset[simp]: "count (replicate_mset n x) y = (if y = x then n else 0)"
  unfolding replicate_mset_def by (induct n) auto

lift_definition repeat_mset :: \<open>nat \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close>
  is \<open>\<lambda>n M a. n * M a\<close> by simp

lemma count_repeat_mset [simp]: "count (repeat_mset i A) a = i * count A a"
  by transfer rule

lemma repeat_mset_0 [simp]:
  \<open>repeat_mset 0 M = {#}\<close>
  by transfer simp

lemma repeat_mset_Suc [simp]:
  \<open>repeat_mset (Suc n) M = M + repeat_mset n M\<close>
  by transfer simp

lemma repeat_mset_right [simp]: "repeat_mset a (repeat_mset b A) = repeat_mset (a * b) A"
  by (auto simp: multiset_eq_iff left_diff_distrib')

lemma left_diff_repeat_mset_distrib': \<open>repeat_mset (i - j) u = repeat_mset i u - repeat_mset j u\<close>
  by (auto simp: multiset_eq_iff left_diff_distrib')

lemma left_add_mult_distrib_mset:
  "repeat_mset i u + (repeat_mset j u + k) = repeat_mset (i+j) u + k"
  by (auto simp: multiset_eq_iff add_mult_distrib)

lemma repeat_mset_distrib:
  "repeat_mset (m + n) A = repeat_mset m A + repeat_mset n A"
  by (auto simp: multiset_eq_iff Nat.add_mult_distrib)

lemma repeat_mset_distrib2[simp]:
  "repeat_mset n (A + B) = repeat_mset n A + repeat_mset n B"
  by (auto simp: multiset_eq_iff add_mult_distrib2)

lemma repeat_mset_replicate_mset[simp]:
  "repeat_mset n {#a#} = replicate_mset n a"
  by (auto simp: multiset_eq_iff)

lemma repeat_mset_distrib_add_mset[simp]:
  "repeat_mset n (add_mset a A) = replicate_mset n a + repeat_mset n A"
  by (auto simp: multiset_eq_iff)

lemma repeat_mset_empty[simp]: "repeat_mset n {#} = {#}"
  by transfer simp


subsubsection \<open>Simprocs\<close>

lemma repeat_mset_iterate_add: \<open>repeat_mset n M = iterate_add n M\<close>
  unfolding iterate_add_def by (induction n) auto

lemma mset_subseteq_add_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (repeat_mset i u + m \<subseteq># repeat_mset j u + n) = (repeat_mset (i-j) u + m \<subseteq># n)"
  by (auto simp add: subseteq_mset_def nat_le_add_iff1)

lemma mset_subseteq_add_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (repeat_mset i u + m \<subseteq># repeat_mset j u + n) = (m \<subseteq># repeat_mset (j-i) u + n)"
  by (auto simp add: subseteq_mset_def nat_le_add_iff2)

lemma mset_subset_add_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (repeat_mset i u + m \<subset># repeat_mset j u + n) = (repeat_mset (i-j) u + m \<subset># n)"
  unfolding subset_mset_def repeat_mset_iterate_add
  by (simp add: iterate_add_eq_add_iff1 mset_subseteq_add_iff1[unfolded repeat_mset_iterate_add])

lemma mset_subset_add_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (repeat_mset i u + m \<subset># repeat_mset j u + n) = (m \<subset># repeat_mset (j-i) u + n)"
  unfolding subset_mset_def repeat_mset_iterate_add
  by (simp add: iterate_add_eq_add_iff2 mset_subseteq_add_iff2[unfolded repeat_mset_iterate_add])

ML_file \<open>multiset_simprocs.ML\<close>

lemma add_mset_replicate_mset_safe[cancelation_simproc_pre]: \<open>NO_MATCH {#} M \<Longrightarrow> add_mset a M = {#a#} + M\<close>
  by simp

declare repeat_mset_iterate_add[cancelation_simproc_pre]

declare iterate_add_distrib[cancelation_simproc_pre]
declare repeat_mset_iterate_add[symmetric, cancelation_simproc_post]

declare add_mset_not_empty[cancelation_simproc_eq_elim]
    empty_not_add_mset[cancelation_simproc_eq_elim]
    subset_mset.le_zero_eq[cancelation_simproc_eq_elim]
    empty_not_add_mset[cancelation_simproc_eq_elim]
    add_mset_not_empty[cancelation_simproc_eq_elim]
    subset_mset.le_zero_eq[cancelation_simproc_eq_elim]
    le_zero_eq[cancelation_simproc_eq_elim]

simproc_setup mseteq_cancel
  ("(l::'a multiset) + m = n" | "(l::'a multiset) = m + n" |
   "add_mset a m = n" | "m = add_mset a n" |
   "replicate_mset p a = n" | "m = replicate_mset p a" |
   "repeat_mset p m = n" | "m = repeat_mset p m") =
  \<open>K Cancel_Simprocs.eq_cancel\<close>

simproc_setup msetsubset_cancel
  ("(l::'a multiset) + m \<subset># n" | "(l::'a multiset) \<subset># m + n" |
   "add_mset a m \<subset># n" | "m \<subset># add_mset a n" |
   "replicate_mset p r \<subset># n" | "m \<subset># replicate_mset p r" |
   "repeat_mset p m \<subset># n" | "m \<subset># repeat_mset p m") =
  \<open>K Multiset_Simprocs.subset_cancel_msets\<close>

simproc_setup msetsubset_eq_cancel
  ("(l::'a multiset) + m \<subseteq># n" | "(l::'a multiset) \<subseteq># m + n" |
   "add_mset a m \<subseteq># n" | "m \<subseteq># add_mset a n" |
   "replicate_mset p r \<subseteq># n" | "m \<subseteq># replicate_mset p r" |
   "repeat_mset p m \<subseteq># n" | "m \<subseteq># repeat_mset p m") =
  \<open>K Multiset_Simprocs.subseteq_cancel_msets\<close>

simproc_setup msetdiff_cancel
  ("((l::'a multiset) + m) - n" | "(l::'a multiset) - (m + n)" |
   "add_mset a m - n" | "m - add_mset a n" |
   "replicate_mset p r - n" | "m - replicate_mset p r" |
   "repeat_mset p m - n" | "m - repeat_mset p m") =
  \<open>K Cancel_Simprocs.diff_cancel\<close>


subsubsection \<open>Conditionally complete lattice\<close>

instantiation multiset :: (type) Inf
begin

lift_definition Inf_multiset :: "'a multiset set \<Rightarrow> 'a multiset" is
  "\<lambda>A i. if A = {} then 0 else Inf ((\<lambda>f. f i) ` A)"
proof -
  fix A :: "('a \<Rightarrow> nat) set"
  assume *: "\<And>f. f \<in> A \<Longrightarrow> finite {x. 0 < f x}"
  show \<open>finite {i. 0 < (if A = {} then 0 else INF f\<in>A. f i)}\<close>
  proof (cases "A = {}")
    case False
    then obtain f where "f \<in> A" by blast
    hence "{i. Inf ((\<lambda>f. f i) ` A) > 0} \<subseteq> {i. f i > 0}"
      by (auto intro: less_le_trans[OF _ cInf_lower])
    moreover from \<open>f \<in> A\<close> * have "finite \<dots>" by simp
    ultimately have "finite {i. Inf ((\<lambda>f. f i) ` A) > 0}" by (rule finite_subset)
    with False show ?thesis by simp
  qed simp_all
qed

instance ..

end

lemma Inf_multiset_empty: "Inf {} = {#}"
  by transfer simp_all

lemma count_Inf_multiset_nonempty: "A \<noteq> {} \<Longrightarrow> count (Inf A) x = Inf ((\<lambda>X. count X x) ` A)"
  by transfer simp_all


instantiation multiset :: (type) Sup
begin

definition Sup_multiset :: "'a multiset set \<Rightarrow> 'a multiset" where
  "Sup_multiset A = (if A \<noteq> {} \<and> subset_mset.bdd_above A then
           Abs_multiset (\<lambda>i. Sup ((\<lambda>X. count X i) ` A)) else {#})"

lemma Sup_multiset_empty: "Sup {} = {#}"
  by (simp add: Sup_multiset_def)

lemma Sup_multiset_unbounded: "\<not> subset_mset.bdd_above A \<Longrightarrow> Sup A = {#}"
  by (simp add: Sup_multiset_def)

instance ..

end

lemma bdd_above_multiset_imp_bdd_above_count:
  assumes "subset_mset.bdd_above (A :: 'a multiset set)"
  shows   "bdd_above ((\<lambda>X. count X x) ` A)"
proof -
  from assms obtain Y where Y: "\<forall>X\<in>A. X \<subseteq># Y"
    by (meson subset_mset.bdd_above.E)
  hence "count X x \<le> count Y x" if "X \<in> A" for X
    using that by (auto intro: mset_subset_eq_count)
  thus ?thesis by (intro bdd_aboveI[of _ "count Y x"]) auto
qed

lemma bdd_above_multiset_imp_finite_support:
  assumes "A \<noteq> {}" "subset_mset.bdd_above (A :: 'a multiset set)"
  shows   "finite (\<Union>X\<in>A. {x. count X x > 0})"
proof -
  from assms obtain Y where Y: "\<forall>X\<in>A. X \<subseteq># Y"
    by (meson subset_mset.bdd_above.E)
  hence "count X x \<le> count Y x" if "X \<in> A" for X x
    using that by (auto intro: mset_subset_eq_count)
  hence "(\<Union>X\<in>A. {x. count X x > 0}) \<subseteq> {x. count Y x > 0}"
    by safe (erule less_le_trans)
  moreover have "finite \<dots>" by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma Sup_multiset_in_multiset:
  \<open>finite {i. 0 < (SUP M\<in>A. count M i)}\<close>
  if \<open>A \<noteq> {}\<close> \<open>subset_mset.bdd_above A\<close>
proof -
  have "{i. Sup ((\<lambda>X. count X i) ` A) > 0} \<subseteq> (\<Union>X\<in>A. {i. 0 < count X i})"
  proof safe
    fix i assume pos: "(SUP X\<in>A. count X i) > 0"
    show "i \<in> (\<Union>X\<in>A. {i. 0 < count X i})"
    proof (rule ccontr)
      assume "i \<notin> (\<Union>X\<in>A. {i. 0 < count X i})"
      hence "\<forall>X\<in>A. count X i \<le> 0" by (auto simp: count_eq_zero_iff)
      with that have "(SUP X\<in>A. count X i) \<le> 0"
        by (intro cSup_least bdd_above_multiset_imp_bdd_above_count) auto
      with pos show False by simp
    qed
  qed
  moreover from that have "finite \<dots>"
    by (rule bdd_above_multiset_imp_finite_support)
  ultimately show "finite {i. Sup ((\<lambda>X. count X i) ` A) > 0}"
    by (rule finite_subset)
qed

lemma count_Sup_multiset_nonempty:
  \<open>count (Sup A) x = (SUP X\<in>A. count X x)\<close>
  if \<open>A \<noteq> {}\<close> \<open>subset_mset.bdd_above A\<close>
  using that by (simp add: Sup_multiset_def Sup_multiset_in_multiset count_Abs_multiset)

interpretation subset_mset: conditionally_complete_lattice Inf Sup "(\<inter>#)" "(\<subseteq>#)" "(\<subset>#)" "(\<union>#)"
proof
  fix X :: "'a multiset" and A
  assume "X \<in> A"
  show "Inf A \<subseteq># X"
    by (metis \<open>X \<in> A\<close> count_Inf_multiset_nonempty empty_iff image_eqI mset_subset_eqI wellorder_Inf_le1)
next
  fix X :: "'a multiset" and A
  assume nonempty: "A \<noteq> {}" and le: "\<And>Y. Y \<in> A \<Longrightarrow> X \<subseteq># Y"
  show "X \<subseteq># Inf A"
  proof (rule mset_subset_eqI)
    fix x
    from nonempty have "count X x \<le> (INF X\<in>A. count X x)"
      by (intro cInf_greatest) (auto intro: mset_subset_eq_count le)
    also from nonempty have "\<dots> = count (Inf A) x" by (simp add: count_Inf_multiset_nonempty)
    finally show "count X x \<le> count (Inf A) x" .
  qed
next
  fix X :: "'a multiset" and A
  assume X: "X \<in> A" and bdd: "subset_mset.bdd_above A"
  show "X \<subseteq># Sup A"
  proof (rule mset_subset_eqI)
    fix x
    from X have "A \<noteq> {}" by auto
    have "count X x \<le> (SUP X\<in>A. count X x)"
      by (intro cSUP_upper X bdd_above_multiset_imp_bdd_above_count bdd)
    also from count_Sup_multiset_nonempty[OF \<open>A \<noteq> {}\<close> bdd]
      have "(SUP X\<in>A. count X x) = count (Sup A) x" by simp
    finally show "count X x \<le> count (Sup A) x" .
  qed
next
  fix X :: "'a multiset" and A
  assume nonempty: "A \<noteq> {}" and ge: "\<And>Y. Y \<in> A \<Longrightarrow> Y \<subseteq># X"
  from ge have bdd: "subset_mset.bdd_above A"
    by blast
  show "Sup A \<subseteq># X"
  proof (rule mset_subset_eqI)
    fix x
    from count_Sup_multiset_nonempty[OF \<open>A \<noteq> {}\<close> bdd]
      have "count (Sup A) x = (SUP X\<in>A. count X x)" .
    also from nonempty have "\<dots> \<le> count X x"
      by (intro cSup_least) (auto intro: mset_subset_eq_count ge)
    finally show "count (Sup A) x \<le> count X x" .
  qed
qed \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>

lemma set_mset_Inf:
  assumes "A \<noteq> {}"
  shows   "set_mset (Inf A) = (\<Inter>X\<in>A. set_mset X)"
proof safe
  fix x X assume "x \<in># Inf A" "X \<in> A"
  hence nonempty: "A \<noteq> {}" by (auto simp: Inf_multiset_empty)
  from \<open>x \<in># Inf A\<close> have "{#x#} \<subseteq># Inf A" by auto
  also from \<open>X \<in> A\<close> have "\<dots> \<subseteq># X" by (rule subset_mset.cInf_lower) simp_all
  finally show "x \<in># X" by simp
next
  fix x assume x: "x \<in> (\<Inter>X\<in>A. set_mset X)"
  hence "{#x#} \<subseteq># X" if "X \<in> A" for X using that by auto
  from assms and this have "{#x#} \<subseteq># Inf A" by (rule subset_mset.cInf_greatest)
  thus "x \<in># Inf A" by simp
qed

lemma in_Inf_multiset_iff:
  assumes "A \<noteq> {}"
  shows   "x \<in># Inf A \<longleftrightarrow> (\<forall>X\<in>A. x \<in># X)"
proof -
  from assms have "set_mset (Inf A) = (\<Inter>X\<in>A. set_mset X)" by (rule set_mset_Inf)
  also have "x \<in> \<dots> \<longleftrightarrow> (\<forall>X\<in>A. x \<in># X)" by simp
  finally show ?thesis .
qed

lemma in_Inf_multisetD: "x \<in># Inf A \<Longrightarrow> X \<in> A \<Longrightarrow> x \<in># X"
  by (subst (asm) in_Inf_multiset_iff) auto

lemma set_mset_Sup:
  assumes "subset_mset.bdd_above A"
  shows   "set_mset (Sup A) = (\<Union>X\<in>A. set_mset X)"
proof safe
  fix x assume "x \<in># Sup A"
  hence nonempty: "A \<noteq> {}" by (auto simp: Sup_multiset_empty)
  show "x \<in> (\<Union>X\<in>A. set_mset X)"
  proof (rule ccontr)
    assume x: "x \<notin> (\<Union>X\<in>A. set_mset X)"
    have "count X x \<le> count (Sup A) x" if "X \<in> A" for X x
      using that by (intro mset_subset_eq_count subset_mset.cSup_upper assms)
    with x have "X \<subseteq># Sup A - {#x#}" if "X \<in> A" for X
      using that by (auto simp: subseteq_mset_def algebra_simps not_in_iff)
    hence "Sup A \<subseteq># Sup A - {#x#}" by (intro subset_mset.cSup_least nonempty)
    with \<open>x \<in># Sup A\<close> show False
      using mset_subset_diff_self by fastforce
  qed
next
  fix x X assume "x \<in> set_mset X" "X \<in> A"
  hence "{#x#} \<subseteq># X" by auto
  also have "X \<subseteq># Sup A" by (intro subset_mset.cSup_upper \<open>X \<in> A\<close> assms)
  finally show "x \<in> set_mset (Sup A)" by simp
qed

lemma in_Sup_multiset_iff:
  assumes "subset_mset.bdd_above A"
  shows   "x \<in># Sup A \<longleftrightarrow> (\<exists>X\<in>A. x \<in># X)"
  by (simp add: assms set_mset_Sup)

lemma in_Sup_multisetD:
  assumes "x \<in># Sup A"
  shows   "\<exists>X\<in>A. x \<in># X"
  using Sup_multiset_unbounded assms in_Sup_multiset_iff by fastforce

interpretation subset_mset: distrib_lattice "(\<inter>#)" "(\<subseteq>#)" "(\<subset>#)" "(\<union>#)"
proof
  fix A B C :: "'a multiset"
  show "A \<union># (B \<inter># C) = A \<union># B \<inter># (A \<union># C)"
    by (intro multiset_eqI) simp_all
qed \<comment> \<open>FIXME: avoid junk stemming from type class interpretation\<close>


subsubsection \<open>Filter (with comprehension syntax)\<close>

text \<open>Multiset comprehension\<close>

lift_definition filter_mset :: "('a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset"
is "\<lambda>P M. \<lambda>x. if P x then M x else 0"
by (rule filter_preserves_multiset)

syntax (ASCII)
  "_MCollect" :: "pttrn \<Rightarrow> 'a multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"    ("(1{#_ :# _./ _#})")
syntax
  "_MCollect" :: "pttrn \<Rightarrow> 'a multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"    ("(1{#_ \<in># _./ _#})")
translations
  "{#x \<in># M. P#}" == "CONST filter_mset (\<lambda>x. P) M"

lemma count_filter_mset [simp]:
  "count (filter_mset P M) a = (if P a then count M a else 0)"
  by (simp add: filter_mset.rep_eq)

lemma set_mset_filter [simp]:
  "set_mset (filter_mset P M) = {a \<in> set_mset M. P a}"
  by (simp only: set_eq_iff count_greater_zero_iff [symmetric] count_filter_mset) simp

lemma filter_empty_mset [simp]: "filter_mset P {#} = {#}"
  by (rule multiset_eqI) simp

lemma filter_single_mset: "filter_mset P {#x#} = (if P x then {#x#} else {#})"
  by (rule multiset_eqI) simp

lemma filter_union_mset [simp]: "filter_mset P (M + N) = filter_mset P M + filter_mset P N"
  by (rule multiset_eqI) simp

lemma filter_diff_mset [simp]: "filter_mset P (M - N) = filter_mset P M - filter_mset P N"
  by (rule multiset_eqI) simp

lemma filter_inter_mset [simp]: "filter_mset P (M \<inter># N) = filter_mset P M \<inter># filter_mset P N"
  by (rule multiset_eqI) simp

lemma filter_sup_mset[simp]: "filter_mset P (A \<union># B) = filter_mset P A \<union># filter_mset P B"
  by (rule multiset_eqI) simp

lemma filter_mset_add_mset [simp]:
   "filter_mset P (add_mset x A) =
     (if P x then add_mset x (filter_mset P A) else filter_mset P A)"
   by (auto simp: multiset_eq_iff)

lemma multiset_filter_subset[simp]: "filter_mset f M \<subseteq># M"
  by (simp add: mset_subset_eqI)

lemma multiset_filter_mono:
  assumes "A \<subseteq># B"
  shows "filter_mset f A \<subseteq># filter_mset f B"
  by (metis assms filter_sup_mset subset_mset.order_iff)

lemma filter_mset_eq_conv:
  "filter_mset P M = N \<longleftrightarrow> N \<subseteq># M \<and> (\<forall>b\<in>#N. P b) \<and> (\<forall>a\<in>#M - N. \<not> P a)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P then show ?Q by auto (simp add: multiset_eq_iff in_diff_count)
next
  assume ?Q
  then obtain Q where M: "M = N + Q"
    by (auto simp add: mset_subset_eq_exists_conv)
  then have MN: "M - N = Q" by simp
  show ?P
  proof (rule multiset_eqI)
    fix a
    from \<open>?Q\<close> MN have *: "\<not> P a \<Longrightarrow> a \<notin># N" "P a \<Longrightarrow> a \<notin># Q"
      by auto
    show "count (filter_mset P M) a = count N a"
    proof (cases "a \<in># M")
      case True
      with * show ?thesis
        by (simp add: not_in_iff M)
    next
      case False then have "count M a = 0"
        by (simp add: not_in_iff)
      with M show ?thesis by simp
    qed
  qed
qed

lemma filter_filter_mset: "filter_mset P (filter_mset Q M) = {#x \<in># M. Q x \<and> P x#}"
  by (auto simp: multiset_eq_iff)

lemma
  filter_mset_True[simp]: "{#y \<in># M. True#} = M" and
  filter_mset_False[simp]: "{#y \<in># M. False#} = {#}"
  by (auto simp: multiset_eq_iff)

lemma filter_mset_cong0:
  assumes "\<And>x. x \<in># M \<Longrightarrow> f x \<longleftrightarrow> g x"
  shows "filter_mset f M = filter_mset g M"
proof (rule subset_mset.antisym; unfold subseteq_mset_def; rule allI)
  fix x
  show "count (filter_mset f M) x \<le> count (filter_mset g M) x"
    using assms by (cases "x \<in># M") (simp_all add: not_in_iff)
next
  fix x
  show "count (filter_mset g M) x \<le> count (filter_mset f M) x"
    using assms by (cases "x \<in># M") (simp_all add: not_in_iff)
qed

lemma filter_mset_cong:
  assumes "M = M'" and "\<And>x. x \<in># M' \<Longrightarrow> f x \<longleftrightarrow> g x"
  shows "filter_mset f M = filter_mset g M'"
  unfolding \<open>M = M'\<close>
  using assms by (auto intro: filter_mset_cong0)

lemma filter_eq_replicate_mset: "{#y \<in># D. y = x#} = replicate_mset (count D x) x"
  by (induct D) (simp add: multiset_eqI)


subsubsection \<open>Size\<close>

definition wcount where "wcount f M = (\<lambda>x. count M x * Suc (f x))"

lemma wcount_union: "wcount f (M + N) a = wcount f M a + wcount f N a"
  by (auto simp: wcount_def add_mult_distrib)

lemma wcount_add_mset:
  "wcount f (add_mset x M) a = (if x = a then Suc (f a) else 0) + wcount f M a"
  unfolding add_mset_add_single[of _ M] wcount_union by (auto simp: wcount_def)

definition size_multiset :: "('a \<Rightarrow> nat) \<Rightarrow> 'a multiset \<Rightarrow> nat" where
  "size_multiset f M = sum (wcount f M) (set_mset M)"

lemmas size_multiset_eq = size_multiset_def[unfolded wcount_def]

instantiation multiset :: (type) size
begin

definition size_multiset where
  size_multiset_overloaded_def: "size_multiset = Multiset.size_multiset (\<lambda>_. 0)"
instance ..

end

lemmas size_multiset_overloaded_eq =
  size_multiset_overloaded_def[THEN fun_cong, unfolded size_multiset_eq, simplified]

lemma size_multiset_empty [simp]: "size_multiset f {#} = 0"
  by (simp add: size_multiset_def)

lemma size_empty [simp]: "size {#} = 0"
  by (simp add: size_multiset_overloaded_def)

lemma size_multiset_single : "size_multiset f {#b#} = Suc (f b)"
  by (simp add: size_multiset_eq)

lemma size_single: "size {#b#} = 1"
  by (simp add: size_multiset_overloaded_def size_multiset_single)

lemma sum_wcount_Int:
  "finite A \<Longrightarrow> sum (wcount f N) (A \<inter> set_mset N) = sum (wcount f N) A"
  by (induct rule: finite_induct)
    (simp_all add: Int_insert_left wcount_def count_eq_zero_iff)

lemma size_multiset_union [simp]:
  "size_multiset f (M + N::'a multiset) = size_multiset f M + size_multiset f N"
  apply (simp add: size_multiset_def sum_Un_nat sum.distrib sum_wcount_Int wcount_union)
  by (metis add_implies_diff finite_set_mset inf.commute sum_wcount_Int)

lemma size_multiset_add_mset [simp]:
  "size_multiset f (add_mset a M) = Suc (f a) + size_multiset f M"
  by (metis add.commute add_mset_add_single size_multiset_single size_multiset_union)

lemma size_add_mset [simp]: "size (add_mset a A) = Suc (size A)"
  by (simp add: size_multiset_overloaded_def wcount_add_mset)

lemma size_union [simp]: "size (M + N::'a multiset) = size M + size N"
  by (auto simp add: size_multiset_overloaded_def)

lemma size_multiset_eq_0_iff_empty [iff]:
  "size_multiset f M = 0 \<longleftrightarrow> M = {#}"
  by (auto simp add: size_multiset_eq count_eq_zero_iff)

lemma size_eq_0_iff_empty [iff]: "(size M = 0) = (M = {#})"
by (auto simp add: size_multiset_overloaded_def)

lemma nonempty_has_size: "(S \<noteq> {#}) = (0 < size S)"
  by (metis gr0I gr_implies_not0 size_empty size_eq_0_iff_empty)

lemma size_eq_Suc_imp_elem: "size M = Suc n \<Longrightarrow> \<exists>a. a \<in># M"
  using all_not_in_conv by fastforce

lemma size_eq_Suc_imp_eq_union:
  assumes "size M = Suc n"
  shows "\<exists>a N. M = add_mset a N"
  by (metis assms insert_DiffM size_eq_Suc_imp_elem)

lemma size_mset_mono:
  fixes A B :: "'a multiset"
  assumes "A \<subseteq># B"
  shows "size A \<le> size B"
proof -
  from assms[unfolded mset_subset_eq_exists_conv]
  obtain C where B: "B = A + C" by auto
  show ?thesis unfolding B by (induct C) auto
qed

lemma size_filter_mset_lesseq[simp]: "size (filter_mset f M) \<le> size M"
  by (rule size_mset_mono[OF multiset_filter_subset])

lemma size_Diff_submset:
  "M \<subseteq># M' \<Longrightarrow> size (M' - M) = size M' - size(M::'a multiset)"
by (metis add_diff_cancel_left' size_union mset_subset_eq_exists_conv)

lemma size_lt_imp_ex_count_lt: "size M < size N \<Longrightarrow> \<exists>x \<in># N. count M x < count N x"
  by (metis count_eq_zero_iff leD not_le_imp_less not_less_zero size_mset_mono subseteq_mset_def)


subsection \<open>Induction and case splits\<close>

theorem multiset_induct [case_names empty add, induct type: multiset]:
  assumes empty: "P {#}"
  assumes add: "\<And>x M. P M \<Longrightarrow> P (add_mset x M)"
  shows "P M"
proof (induct "size M" arbitrary: M)
  case 0 thus "P M" by (simp add: empty)
next
  case (Suc k)
  obtain N x where "M = add_mset x N"
    using \<open>Suc k = size M\<close> [symmetric]
    using size_eq_Suc_imp_eq_union by fast
  with Suc add show "P M" by simp
qed

lemma multiset_induct_min[case_names empty add]:
  fixes M :: "'a::linorder multiset"
  assumes
    empty: "P {#}" and
    add: "\<And>x M. P M \<Longrightarrow> (\<forall>y \<in># M. y \<ge> x) \<Longrightarrow> P (add_mset x M)"
  shows "P M"
proof (induct "size M" arbitrary: M)
  case (Suc k)
  note ih = this(1) and Sk_eq_sz_M = this(2)

  let ?y = "Min_mset M"
  let ?N = "M - {#?y#}"

  have M: "M = add_mset ?y ?N"
    by (metis Min_in Sk_eq_sz_M finite_set_mset insert_DiffM lessI not_less_zero
      set_mset_eq_empty_iff size_empty)
  show ?case
    by (subst M, rule add, rule ih, metis M Sk_eq_sz_M nat.inject size_add_mset,
      meson Min_le finite_set_mset in_diffD)
qed (simp add: empty)

lemma multiset_induct_max[case_names empty add]:
  fixes M :: "'a::linorder multiset"
  assumes
    empty: "P {#}" and
    add: "\<And>x M. P M \<Longrightarrow> (\<forall>y \<in># M. y \<le> x) \<Longrightarrow> P (add_mset x M)"
  shows "P M"
proof (induct "size M" arbitrary: M)
  case (Suc k)
  note ih = this(1) and Sk_eq_sz_M = this(2)

  let ?y = "Max_mset M"
  let ?N = "M - {#?y#}"

  have M: "M = add_mset ?y ?N"
    by (metis Max_in Sk_eq_sz_M finite_set_mset insert_DiffM lessI not_less_zero
      set_mset_eq_empty_iff size_empty)
  show ?case
    by (subst M, rule add, rule ih, metis M Sk_eq_sz_M nat.inject size_add_mset,
      meson Max_ge finite_set_mset in_diffD)
qed (simp add: empty)

lemma multi_nonempty_split: "M \<noteq> {#} \<Longrightarrow> \<exists>A a. M = add_mset a A"
  by (induct M) auto

lemma multiset_cases [cases type]:
  obtains (empty) "M = {#}" | (add) x N where "M = add_mset x N"
  by (induct M) simp_all

lemma multi_drop_mem_not_eq: "c \<in># B \<Longrightarrow> B - {#c#} \<noteq> B"
  by (cases "B = {#}") (auto dest: multi_member_split)

lemma union_filter_mset_complement[simp]:
  "\<forall>x. P x = (\<not> Q x) \<Longrightarrow> filter_mset P M + filter_mset Q M = M"
  by (subst multiset_eq_iff) auto

lemma multiset_partition: "M = {#x \<in># M. P x#} + {#x \<in># M. \<not> P x#}"
  by simp

lemma mset_subset_size: "A \<subset># B \<Longrightarrow> size A < size B"
proof (induct A arbitrary: B)
  case empty
  then show ?case
    using nonempty_has_size by auto
next
  case (add x A)
  have "add_mset x A \<subseteq># B"
    by (meson add.prems subset_mset_def)
  then show ?case
    using add.prems subset_mset.less_eqE by fastforce
qed

lemma size_1_singleton_mset: "size M = 1 \<Longrightarrow> \<exists>a. M = {#a#}"
  by (cases M) auto

lemma set_mset_subset_singletonD:
  assumes "set_mset A \<subseteq> {x}"
  shows   "A = replicate_mset (size A) x"
  using assms by (induction A) auto


subsubsection \<open>Strong induction and subset induction for multisets\<close>

text \<open>Well-foundedness of strict subset relation\<close>

lemma wf_subset_mset_rel: "wf {(M, N :: 'a multiset). M \<subset># N}"
  using mset_subset_size wfP_def wfp_if_convertible_to_nat by blast

lemma wfP_subset_mset[simp]: "wfP (\<subset>#)"
  by (rule wf_subset_mset_rel[to_pred])

lemma full_multiset_induct [case_names less]:
  assumes ih: "\<And>B. \<forall>(A::'a multiset). A \<subset># B \<longrightarrow> P A \<Longrightarrow> P B"
  shows "P B"
  apply (rule wf_subset_mset_rel [THEN wf_induct])
  apply (rule ih, auto)
  done

lemma multi_subset_induct [consumes 2, case_names empty add]:
  assumes "F \<subseteq># A"
    and empty: "P {#}"
    and insert: "\<And>a F. a \<in># A \<Longrightarrow> P F \<Longrightarrow> P (add_mset a F)"
  shows "P F"
proof -
  from \<open>F \<subseteq># A\<close>
  show ?thesis
  proof (induct F)
    show "P {#}" by fact
  next
    fix x F
    assume P: "F \<subseteq># A \<Longrightarrow> P F" and i: "add_mset x F \<subseteq># A"
    show "P (add_mset x F)"
    proof (rule insert)
      from i show "x \<in># A" by (auto dest: mset_subset_eq_insertD)
      from i have "F \<subseteq># A" by (auto dest: mset_subset_eq_insertD)
      with P show "P F" .
    qed
  qed
qed


subsection \<open>Least and greatest elements\<close>

context begin

qualified lemma
  assumes
    "M \<noteq> {#}" and
    "transp_on (set_mset M) R" and
    "totalp_on (set_mset M) R"
  shows
    bex_least_element: "(\<exists>l \<in># M. \<forall>x \<in># M. x \<noteq> l \<longrightarrow> R l x)" and
    bex_greatest_element: "(\<exists>g \<in># M. \<forall>x \<in># M. x \<noteq> g \<longrightarrow> R x g)"
  using assms
  by (auto intro: Finite_Set.bex_least_element Finite_Set.bex_greatest_element)

end


subsection \<open>The fold combinator\<close>

definition fold_mset :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a multiset \<Rightarrow> 'b"
where
  "fold_mset f s M = Finite_Set.fold (\<lambda>x. f x ^^ count M x) s (set_mset M)"

lemma fold_mset_empty [simp]: "fold_mset f s {#} = s"
  by (simp add: fold_mset_def)

lemma fold_mset_single [simp]: "fold_mset f s {#x#} = f x s"
  by (simp add: fold_mset_def)

context comp_fun_commute
begin

lemma fold_mset_add_mset [simp]: "fold_mset f s (add_mset x M) = f x (fold_mset f s M)"
proof -
  interpret mset: comp_fun_commute "\<lambda>y. f y ^^ count M y"
    by (fact comp_fun_commute_funpow)
  interpret mset_union: comp_fun_commute "\<lambda>y. f y ^^ count (add_mset x M) y"
    by (fact comp_fun_commute_funpow)
  show ?thesis
  proof (cases "x \<in> set_mset M")
    case False
    then have *: "count (add_mset x M) x = 1"
      by (simp add: not_in_iff)
    from False have "Finite_Set.fold (\<lambda>y. f y ^^ count (add_mset x M) y) s (set_mset M) =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s (set_mset M)"
      by (auto intro!: Finite_Set.fold_cong comp_fun_commute_on_funpow)
    with False * show ?thesis
      by (simp add: fold_mset_def del: count_add_mset)
  next
    case True
    define N where "N = set_mset M - {x}"
    from N_def True have *: "set_mset M = insert x N" "x \<notin> N" "finite N" by auto
    then have "Finite_Set.fold (\<lambda>y. f y ^^ count (add_mset x M) y) s N =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s N"
      by (auto intro!: Finite_Set.fold_cong comp_fun_commute_on_funpow)
    with * show ?thesis by (simp add: fold_mset_def del: count_add_mset) simp
  qed
qed

lemma fold_mset_fun_left_comm: "f x (fold_mset f s M) = fold_mset f (f x s) M"
  by (induct M) (simp_all add: fun_left_comm)

lemma fold_mset_union [simp]: "fold_mset f s (M + N) = fold_mset f (fold_mset f s M) N"
  by (induct M) (simp_all add: fold_mset_fun_left_comm)

lemma fold_mset_fusion:
  assumes "comp_fun_commute g"
    and *: "\<And>x y. h (g x y) = f x (h y)"
  shows "h (fold_mset g w A) = fold_mset f (h w) A"
proof -
  interpret comp_fun_commute g by (fact assms)
  from * show ?thesis by (induct A) auto
qed

end

lemma union_fold_mset_add_mset: "A + B = fold_mset add_mset A B"
proof -
  interpret comp_fun_commute add_mset
    by standard auto
  show ?thesis
    by (induction B) auto
qed

text \<open>
  A note on code generation: When defining some function containing a
  subterm \<^term>\<open>fold_mset F\<close>, code generation is not automatic. When
  interpreting locale \<open>left_commutative\<close> with \<open>F\<close>, the
  would be code thms for \<^const>\<open>fold_mset\<close> become thms like
  \<^term>\<open>fold_mset F z {#} = z\<close> where \<open>F\<close> is not a pattern but
  contains defined symbols, i.e.\ is not a code thm. Hence a separate
  constant with its own code thms needs to be introduced for \<open>F\<close>. See the image operator below.
\<close>


subsection \<open>Image\<close>

definition image_mset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset" where
  "image_mset f = fold_mset (add_mset \<circ> f) {#}"

lemma comp_fun_commute_mset_image: "comp_fun_commute (add_mset \<circ> f)"
  by unfold_locales (simp add: fun_eq_iff)

lemma image_mset_empty [simp]: "image_mset f {#} = {#}"
  by (simp add: image_mset_def)

lemma image_mset_single: "image_mset f {#x#} = {#f x#}"
  by (simp add: comp_fun_commute.fold_mset_add_mset comp_fun_commute_mset_image image_mset_def)

lemma image_mset_union [simp]: "image_mset f (M + N) = image_mset f M + image_mset f N"
proof -
  interpret comp_fun_commute "add_mset \<circ> f"
    by (fact comp_fun_commute_mset_image)
  show ?thesis by (induct N) (simp_all add: image_mset_def)
qed

corollary image_mset_add_mset [simp]:
  "image_mset f (add_mset a M) = add_mset (f a) (image_mset f M)"
  unfolding image_mset_union add_mset_add_single[of a M] by (simp add: image_mset_single)

lemma set_image_mset [simp]: "set_mset (image_mset f M) = image f (set_mset M)"
  by (induct M) simp_all

lemma size_image_mset [simp]: "size (image_mset f M) = size M"
  by (induct M) simp_all

lemma image_mset_is_empty_iff [simp]: "image_mset f M = {#} \<longleftrightarrow> M = {#}"
  by (cases M) auto

lemma image_mset_If:
  "image_mset (\<lambda>x. if P x then f x else g x) A =
     image_mset f (filter_mset P A) + image_mset g (filter_mset (\<lambda>x. \<not>P x) A)"
  by (induction A) auto

lemma image_mset_Diff:
  assumes "B \<subseteq># A"
  shows   "image_mset f (A - B) = image_mset f A - image_mset f B"
proof -
  have "image_mset f (A - B + B) = image_mset f (A - B) + image_mset f B"
    by simp
  also from assms have "A - B + B = A"
    by (simp add: subset_mset.diff_add)
  finally show ?thesis by simp
qed

lemma count_image_mset:
  \<open>count (image_mset f A) x = (\<Sum>y\<in>f -` {x} \<inter> set_mset A. count A y)\<close>
proof (induction A)
  case empty
  then show ?case by simp
next
  case (add x A)
  moreover have *: "(if x = y then Suc n else n) = n + (if x = y then 1 else 0)" for n y
    by simp
  ultimately show ?case
    by (auto simp: sum.distrib intro!: sum.mono_neutral_left)
qed

lemma count_image_mset':
  \<open>count (image_mset f X) y = (\<Sum>x | x \<in># X \<and> y = f x. count X x)\<close>
  by (auto simp add: count_image_mset simp flip: singleton_conv2 simp add: Collect_conj_eq ac_simps)

lemma image_mset_subseteq_mono: "A \<subseteq># B \<Longrightarrow> image_mset f A \<subseteq># image_mset f B"
  by (metis image_mset_union subset_mset.le_iff_add)

lemma image_mset_subset_mono: "M \<subset># N \<Longrightarrow> image_mset f M \<subset># image_mset f N"
  by (metis (no_types) Diff_eq_empty_iff_mset image_mset_Diff image_mset_is_empty_iff
    image_mset_subseteq_mono subset_mset.less_le_not_le)

syntax (ASCII)
  "_comprehension_mset" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> 'a multiset"  ("({#_/. _ :# _#})")
syntax
  "_comprehension_mset" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> 'a multiset"  ("({#_/. _ \<in># _#})")
translations
  "{#e. x \<in># M#}" \<rightleftharpoons> "CONST image_mset (\<lambda>x. e) M"

syntax (ASCII)
  "_comprehension_mset'" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"  ("({#_/ | _ :# _./ _#})")
syntax
  "_comprehension_mset'" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b multiset \<Rightarrow> bool \<Rightarrow> 'a multiset"  ("({#_/ | _ \<in># _./ _#})")
translations
  "{#e | x\<in>#M. P#}" \<rightharpoonup> "{#e. x \<in># {# x\<in>#M. P#}#}"

text \<open>
  This allows to write not just filters like \<^term>\<open>{#x\<in>#M. x<c#}\<close>
  but also images like \<^term>\<open>{#x+x. x\<in>#M #}\<close> and @{term [source]
  "{#x+x|x\<in>#M. x<c#}"}, where the latter is currently displayed as
  \<^term>\<open>{#x+x|x\<in>#M. x<c#}\<close>.
\<close>

lemma in_image_mset: "y \<in># {#f x. x \<in># M#} \<longleftrightarrow> y \<in> f ` set_mset M"
  by simp

functor image_mset: image_mset
proof -
  fix f g show "image_mset f \<circ> image_mset g = image_mset (f \<circ> g)"
  proof
    fix A
    show "(image_mset f \<circ> image_mset g) A = image_mset (f \<circ> g) A"
      by (induct A) simp_all
  qed
  show "image_mset id = id"
  proof
    fix A
    show "image_mset id A = id A"
      by (induct A) simp_all
  qed
qed

declare
  image_mset.id [simp]
  image_mset.identity [simp]

lemma image_mset_id[simp]: "image_mset id x = x"
  unfolding id_def by auto

lemma image_mset_cong: "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> {#f x. x \<in># M#} = {#g x. x \<in># M#}"
  by (induct M) auto

lemma image_mset_cong_pair:
  "(\<forall>x y. (x, y) \<in># M \<longrightarrow> f x y = g x y) \<Longrightarrow> {#f x y. (x, y) \<in># M#} = {#g x y. (x, y) \<in># M#}"
  by (metis image_mset_cong split_cong)

lemma image_mset_const_eq:
  "{#c. a \<in># M#} = replicate_mset (size M) c"
  by (induct M) simp_all

lemma image_mset_filter_mset_swap:
  "image_mset f (filter_mset (\<lambda>x. P (f x)) M) = filter_mset P (image_mset f M)"
  by (induction M rule: multiset_induct) simp_all

lemma image_mset_eq_plusD:
  "image_mset f A = B + C \<Longrightarrow> \<exists>B' C'. A = B' + C' \<and> B = image_mset f B' \<and> C = image_mset f C'"
proof (induction A arbitrary: B C)
  case empty
  thus ?case by simp
next
  case (add x A)
  show ?case
  proof (cases "f x \<in># B")
    case True
    with add.prems have "image_mset f A = (B - {#f x#}) + C"
      by (metis add_mset_remove_trivial image_mset_add_mset mset_subset_eq_single
          subset_mset.add_diff_assoc2)
    thus ?thesis
      using add.IH add.prems by force
  next
    case False
    with add.prems have "image_mset f A = B + (C - {#f x#})"
      by (metis diff_single_eq_union diff_union_single_conv image_mset_add_mset union_iff
          union_single_eq_member)
    then show ?thesis
      using add.IH add.prems by force
  qed
qed

lemma image_mset_eq_image_mset_plusD:
  assumes "image_mset f A = image_mset f B + C" and inj_f: "inj_on f (set_mset A \<union> set_mset B)"
  shows "\<exists>C'. A = B + C' \<and> C = image_mset f C'"
  using assms
proof (induction A arbitrary: B C)
  case empty
  thus ?case by simp
next
  case (add x A)
  show ?case
  proof (cases "x \<in># B")
    case True
    with add.prems have "image_mset f A = image_mset f (B - {#x#}) + C"
      by (smt (verit) add_mset_add_mset_same_iff image_mset_add_mset insert_DiffM union_mset_add_mset_left)
    with add.IH have "\<exists>M3'. A = B - {#x#} + M3' \<and> image_mset f M3' = C"
      by (smt (verit, del_insts) True Un_insert_left Un_insert_right add.prems(2) inj_on_insert
          insert_DiffM set_mset_add_mset_insert)
    with True show ?thesis
      by auto
  next
    case False
    with add.prems(2) have "f x \<notin># image_mset f B"
      by auto
    with add.prems(1) have "image_mset f A = image_mset f B + (C - {#f x#})"
      by (metis (no_types, lifting) diff_union_single_conv image_eqI image_mset_Diff
          image_mset_single mset_subset_eq_single set_image_mset union_iff union_single_eq_diff
          union_single_eq_member)
    with add.prems(2) add.IH have "\<exists>M3'. A = B + M3' \<and> C - {#f x#} = image_mset f M3'"
      by auto
    then show ?thesis
      by (metis add.prems(1) add_diff_cancel_left' image_mset_Diff mset_subset_eq_add_left
          union_mset_add_mset_right)
  qed
qed

lemma image_mset_eq_plus_image_msetD:
  "image_mset f A = B + image_mset f C \<Longrightarrow> inj_on f (set_mset A \<union> set_mset C) \<Longrightarrow>
  \<exists>B'. A = B' + C \<and> B = image_mset f B'"
  unfolding add.commute[of B] add.commute[of _ C]
  by (rule image_mset_eq_image_mset_plusD; assumption)


subsection \<open>Further conversions\<close>

primrec mset :: "'a list \<Rightarrow> 'a multiset" where
  "mset [] = {#}" |
  "mset (a # x) = add_mset a (mset x)"

lemma in_multiset_in_set:
  "x \<in># mset xs \<longleftrightarrow> x \<in> set xs"
  by (induct xs) simp_all

lemma count_mset:
  "count (mset xs) x = length (filter (\<lambda>y. x = y) xs)"
  by (induct xs) simp_all

lemma mset_zero_iff[simp]: "(mset x = {#}) = (x = [])"
  by (induct x) auto

lemma mset_zero_iff_right[simp]: "({#} = mset x) = (x = [])"
by (induct x) auto

lemma count_mset_gt_0: "x \<in> set xs \<Longrightarrow> count (mset xs) x > 0"
  by (induction xs) auto

lemma count_mset_0_iff [simp]: "count (mset xs) x = 0 \<longleftrightarrow> x \<notin> set xs"
  by (induction xs) auto

lemma mset_single_iff[iff]: "mset xs = {#x#} \<longleftrightarrow> xs = [x]"
  by (cases xs) auto

lemma mset_single_iff_right[iff]: "{#x#} = mset xs \<longleftrightarrow> xs = [x]"
  by (cases xs) auto

lemma set_mset_mset[simp]: "set_mset (mset xs) = set xs"
  by (induct xs) auto

lemma set_mset_comp_mset [simp]: "set_mset \<circ> mset = set"
  by (simp add: fun_eq_iff)

lemma size_mset [simp]: "size (mset xs) = length xs"
  by (induct xs) simp_all

lemma mset_append [simp]: "mset (xs @ ys) = mset xs + mset ys"
  by (induct xs arbitrary: ys) auto

lemma mset_filter[simp]: "mset (filter P xs) = {#x \<in># mset xs. P x #}"
  by (induct xs) simp_all

lemma mset_rev [simp]:
  "mset (rev xs) = mset xs"
  by (induct xs) simp_all

lemma surj_mset: "surj mset"
  unfolding surj_def
proof (rule allI)
  fix M
  show "\<exists>xs. M = mset xs"
    by (induction M) (auto intro: exI[of _ "_ # _"])
qed

lemma distinct_count_atmost_1:
  "distinct x = (\<forall>a. count (mset x) a = (if a \<in> set x then 1 else 0))"
proof (induct x)
  case Nil then show ?case by simp
next
  case (Cons x xs) show ?case (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs then show ?rhs using Cons by simp
  next
    assume ?rhs then have "x \<notin> set xs"
      by (simp split: if_splits)
    moreover from \<open>?rhs\<close> have "(\<forall>a. count (mset xs) a =
       (if a \<in> set xs then 1 else 0))"
      by (auto split: if_splits simp add: count_eq_zero_iff)
    ultimately show ?lhs using Cons by simp
  qed
qed

lemma mset_eq_setD:
  assumes "mset xs = mset ys"
  shows "set xs = set ys"
proof -
  from assms have "set_mset (mset xs) = set_mset (mset ys)"
    by simp
  then show ?thesis by simp
qed

lemma set_eq_iff_mset_eq_distinct:
  \<open>distinct x \<Longrightarrow> distinct y \<Longrightarrow> set x = set y \<longleftrightarrow> mset x = mset y\<close>
  by (auto simp: multiset_eq_iff distinct_count_atmost_1)

lemma set_eq_iff_mset_remdups_eq:
  \<open>set x = set y \<longleftrightarrow> mset (remdups x) = mset (remdups y)\<close>
  using set_eq_iff_mset_eq_distinct by fastforce

lemma mset_eq_imp_distinct_iff:
  \<open>distinct xs \<longleftrightarrow> distinct ys\<close> if \<open>mset xs = mset ys\<close>
  using that by (auto simp add: distinct_count_atmost_1 dest: mset_eq_setD)

lemma nth_mem_mset: "i < length ls \<Longrightarrow> (ls ! i) \<in># mset ls"
proof (induct ls arbitrary: i)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases i) auto
qed

lemma mset_remove1[simp]: "mset (remove1 a xs) = mset xs - {#a#}"
  by (induct xs) (auto simp add: multiset_eq_iff)

lemma mset_eq_length:
  assumes "mset xs = mset ys"
  shows "length xs = length ys"
  using assms by (metis size_mset)

lemma mset_eq_length_filter:
  assumes "mset xs = mset ys"
  shows "length (filter (\<lambda>x. z = x) xs) = length (filter (\<lambda>y. z = y) ys)"
  using assms by (metis count_mset)

lemma fold_multiset_equiv:
  \<open>List.fold f xs = List.fold f ys\<close>
    if f: \<open>\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f x \<circ> f y = f y \<circ> f x\<close>
    and \<open>mset xs = mset ys\<close>
using f \<open>mset xs = mset ys\<close> [symmetric] proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have *: \<open>set ys = set (x # xs)\<close>
    by (blast dest: mset_eq_setD)
  have \<open>\<And>x y. x \<in> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x \<circ> f y = f y \<circ> f x\<close>
    by (rule Cons.prems(1)) (simp_all add: *)
  moreover from * have \<open>x \<in> set ys\<close>
    by simp
  ultimately have \<open>List.fold f ys = List.fold f (remove1 x ys) \<circ> f x\<close>
    by (fact fold_remove1_split)
  moreover from Cons.prems have \<open>List.fold f xs = List.fold f (remove1 x ys)\<close>
    by (auto intro: Cons.IH)
  ultimately show ?case
    by simp
qed

lemma fold_permuted_eq:
  \<open>List.fold (\<odot>) xs z = List.fold (\<odot>) ys z\<close>
    if \<open>mset xs = mset ys\<close>
    and \<open>P z\<close> and P: \<open>\<And>x z. x \<in> set xs \<Longrightarrow> P z \<Longrightarrow> P (x \<odot> z)\<close>
    and f: \<open>\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P z \<Longrightarrow> x \<odot> (y \<odot> z) = y \<odot> (x \<odot> z)\<close>
  for f (infixl \<open>\<odot>\<close> 70)
using \<open>P z\<close> P f \<open>mset xs = mset ys\<close> [symmetric] proof (induction xs arbitrary: ys z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have *: \<open>set ys = set (x # xs)\<close>
    by (blast dest: mset_eq_setD)
  have \<open>P z\<close>
    by (fact Cons.prems(1))
  moreover have \<open>\<And>x z. x \<in> set ys \<Longrightarrow> P z \<Longrightarrow> P (x \<odot> z)\<close>
    by (rule Cons.prems(2)) (simp_all add: *)
  moreover have \<open>\<And>x y z. x \<in> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> P z \<Longrightarrow> x \<odot> (y \<odot> z) = y \<odot> (x \<odot> z)\<close>
    by (rule Cons.prems(3)) (simp_all add: *)
  moreover from * have \<open>x \<in> set ys\<close>
    by simp
  ultimately have \<open>fold (\<odot>) ys z = fold (\<odot>) (remove1 x ys) (x \<odot> z)\<close>
    by (induction ys arbitrary: z) auto
  moreover from Cons.prems have \<open>fold (\<odot>) xs (x \<odot> z) = fold (\<odot>) (remove1 x ys) (x \<odot> z)\<close>
    by (auto intro: Cons.IH)
  ultimately show ?case
    by simp
qed

lemma mset_shuffles: "zs \<in> shuffles xs ys \<Longrightarrow> mset zs = mset xs + mset ys"
  by (induction xs ys arbitrary: zs rule: shuffles.induct) auto

lemma mset_insort [simp]: "mset (insort x xs) = add_mset x (mset xs)"
  by (induct xs) simp_all

lemma mset_map[simp]: "mset (map f xs) = image_mset f (mset xs)"
  by (induct xs) simp_all

global_interpretation mset_set: folding add_mset "{#}"
  defines mset_set = "folding_on.F add_mset {#}"
  by standard (simp add: fun_eq_iff)

lemma sum_multiset_singleton [simp]: "sum (\<lambda>n. {#n#}) A = mset_set A"
  by (induction A rule: infinite_finite_induct) auto

lemma count_mset_set [simp]:
  "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> count (mset_set A) x = 1" (is "PROP ?P")
  "\<not> finite A \<Longrightarrow> count (mset_set A) x = 0" (is "PROP ?Q")
  "x \<notin> A \<Longrightarrow> count (mset_set A) x = 0" (is "PROP ?R")
proof -
  have *: "count (mset_set A) x = 0" if "x \<notin> A" for A
  proof (cases "finite A")
    case False then show ?thesis by simp
  next
    case True from True \<open>x \<notin> A\<close> show ?thesis by (induct A) auto
  qed
  then show "PROP ?P" "PROP ?Q" "PROP ?R"
  by (auto elim!: Set.set_insert)
qed \<comment> \<open>TODO: maybe define \<^const>\<open>mset_set\<close> also in terms of \<^const>\<open>Abs_multiset\<close>\<close>

lemma elem_mset_set[simp, intro]: "finite A \<Longrightarrow> x \<in># mset_set A \<longleftrightarrow> x \<in> A"
  by (induct A rule: finite_induct) simp_all

lemma mset_set_Union:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> mset_set (A \<union> B) = mset_set A + mset_set B"
  by (induction A rule: finite_induct) auto

lemma filter_mset_mset_set [simp]:
  "finite A \<Longrightarrow> filter_mset P (mset_set A) = mset_set {x\<in>A. P x}"
proof (induction A rule: finite_induct)
  case (insert x A)
  from insert.hyps have "filter_mset P (mset_set (insert x A)) =
      filter_mset P (mset_set A) + mset_set (if P x then {x} else {})"
    by simp
  also have "filter_mset P (mset_set A) = mset_set {x\<in>A. P x}"
    by (rule insert.IH)
  also from insert.hyps
    have "\<dots> + mset_set (if P x then {x} else {}) =
            mset_set ({x \<in> A. P x} \<union> (if P x then {x} else {}))" (is "_ = mset_set ?A")
     by (intro mset_set_Union [symmetric]) simp_all
  also from insert.hyps have "?A = {y\<in>insert x A. P y}" by auto
  finally show ?case .
qed simp_all

lemma mset_set_Diff:
  assumes "finite A" "B \<subseteq> A"
  shows  "mset_set (A - B) = mset_set A - mset_set B"
proof -
  from assms have "mset_set ((A - B) \<union> B) = mset_set (A - B) + mset_set B"
    by (intro mset_set_Union) (auto dest: finite_subset)
  also from assms have "A - B \<union> B = A" by blast
  finally show ?thesis by simp
qed

lemma mset_set_set: "distinct xs \<Longrightarrow> mset_set (set xs) = mset xs"
  by (induction xs) simp_all

lemma count_mset_set': "count (mset_set A) x = (if finite A \<and> x \<in> A then 1 else 0)"
  by auto

lemma subset_imp_msubset_mset_set: 
  assumes "A \<subseteq> B" "finite B"
  shows   "mset_set A \<subseteq># mset_set B"
proof (rule mset_subset_eqI)
  fix x :: 'a
  from assms have "finite A" by (rule finite_subset)
  with assms show "count (mset_set A) x \<le> count (mset_set B) x"
    by (cases "x \<in> A"; cases "x \<in> B") auto
qed

lemma mset_set_set_mset_msubset: "mset_set (set_mset A) \<subseteq># A"
proof (rule mset_subset_eqI)
  fix x show "count (mset_set (set_mset A)) x \<le> count A x"
    by (cases "x \<in># A") simp_all
qed

lemma mset_set_upto_eq_mset_upto:
  \<open>mset_set {..<n} = mset [0..<n]\<close>
  by (induction n) (auto simp: ac_simps lessThan_Suc)

context linorder
begin

definition sorted_list_of_multiset :: "'a multiset \<Rightarrow> 'a list"
where
  "sorted_list_of_multiset M = fold_mset insort [] M"

lemma sorted_list_of_multiset_empty [simp]:
  "sorted_list_of_multiset {#} = []"
  by (simp add: sorted_list_of_multiset_def)

lemma sorted_list_of_multiset_singleton [simp]:
  "sorted_list_of_multiset {#x#} = [x]"
proof -
  interpret comp_fun_commute insort by (fact comp_fun_commute_insort)
  show ?thesis by (simp add: sorted_list_of_multiset_def)
qed

lemma sorted_list_of_multiset_insert [simp]:
  "sorted_list_of_multiset (add_mset x M) = List.insort x (sorted_list_of_multiset M)"
proof -
  interpret comp_fun_commute insort by (fact comp_fun_commute_insort)
  show ?thesis by (simp add: sorted_list_of_multiset_def)
qed

end

lemma mset_sorted_list_of_multiset[simp]: "mset (sorted_list_of_multiset M) = M"
  by (induct M) simp_all

lemma sorted_list_of_multiset_mset[simp]: "sorted_list_of_multiset (mset xs) = sort xs"
  by (induct xs) simp_all

lemma finite_set_mset_mset_set[simp]: "finite A \<Longrightarrow> set_mset (mset_set A) = A"
  by auto

lemma mset_set_empty_iff: "mset_set A = {#} \<longleftrightarrow> A = {} \<or> infinite A"
  using finite_set_mset_mset_set by fastforce

lemma infinite_set_mset_mset_set: "\<not> finite A \<Longrightarrow> set_mset (mset_set A) = {}"
  by simp

lemma set_sorted_list_of_multiset [simp]:
  "set (sorted_list_of_multiset M) = set_mset M"
  by (induct M) (simp_all add: set_insort_key)

lemma sorted_list_of_mset_set [simp]:
  "sorted_list_of_multiset (mset_set A) = sorted_list_of_set A"
  by (cases "finite A") (induct A rule: finite_induct, simp_all)

lemma mset_upt [simp]: "mset [m..<n] = mset_set {m..<n}"
  by (metis distinct_upt mset_set_set set_upt)

lemma image_mset_map_of:
  "distinct (map fst xs) \<Longrightarrow> {#the (map_of xs i). i \<in># mset (map fst xs)#} = mset (map snd xs)"
proof (induction xs)
  case (Cons x xs)
  have "{#the (map_of (x # xs) i). i \<in># mset (map fst (x # xs))#} =
          add_mset (snd x) {#the (if i = fst x then Some (snd x) else map_of xs i).
             i \<in># mset (map fst xs)#}" (is "_ = add_mset _ ?A") by simp
  also from Cons.prems have "?A = {#the (map_of xs i). i :# mset (map fst xs)#}"
    by (cases x, intro image_mset_cong) (auto simp: in_multiset_in_set)
  also from Cons.prems have "\<dots> = mset (map snd xs)" by (intro Cons.IH) simp_all
  finally show ?case by simp
qed simp_all

lemma msubset_mset_set_iff[simp]:
  assumes "finite A" "finite B"
  shows "mset_set A \<subseteq># mset_set B \<longleftrightarrow> A \<subseteq> B"
  using assms set_mset_mono subset_imp_msubset_mset_set by fastforce

lemma mset_set_eq_iff[simp]:
  assumes "finite A" "finite B"
  shows "mset_set A = mset_set B \<longleftrightarrow> A = B"
  using assms by (fastforce dest: finite_set_mset_mset_set)

lemma image_mset_mset_set: \<^marker>\<open>contributor \<open>Lukas Bulwahn\<close>\<close>
  assumes "inj_on f A"
  shows "image_mset f (mset_set A) = mset_set (f ` A)"
proof cases
  assume "finite A"
  from this \<open>inj_on f A\<close> show ?thesis
    by (induct A) auto
next
  assume "infinite A"
  from this \<open>inj_on f A\<close> have "infinite (f ` A)"
    using finite_imageD by blast
  from \<open>infinite A\<close> \<open>infinite (f ` A)\<close> show ?thesis by simp
qed


subsection \<open>More properties of the replicate, repeat, and image operations\<close>

lemma in_replicate_mset[simp]: "x \<in># replicate_mset n y \<longleftrightarrow> n > 0 \<and> x = y"
  unfolding replicate_mset_def by (induct n) auto

lemma set_mset_replicate_mset_subset[simp]: "set_mset (replicate_mset n x) = (if n = 0 then {} else {x})"
  by auto

lemma size_replicate_mset[simp]: "size (replicate_mset n M) = n"
  by (induct n, simp_all)

lemma size_repeat_mset [simp]: "size (repeat_mset n A) = n * size A"
  by (induction n) auto

lemma size_multiset_sum [simp]: "size (\<Sum>x\<in>A. f x :: 'a multiset) = (\<Sum>x\<in>A. size (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma size_multiset_sum_list [simp]: "size (\<Sum>X\<leftarrow>Xs. X :: 'a multiset) = (\<Sum>X\<leftarrow>Xs. size X)"
  by (induction Xs) auto

lemma count_le_replicate_mset_subset_eq: "n \<le> count M x \<longleftrightarrow> replicate_mset n x \<subseteq># M"
  by (auto simp add: mset_subset_eqI) (metis count_replicate_mset subseteq_mset_def)

lemma replicate_count_mset_eq_filter_eq: "replicate (count (mset xs) k) k = filter (HOL.eq k) xs"
  by (induct xs) auto

lemma replicate_mset_eq_empty_iff [simp]: "replicate_mset n a = {#} \<longleftrightarrow> n = 0"
  by (induct n) simp_all

lemma replicate_mset_eq_iff:
  "replicate_mset m a = replicate_mset n b \<longleftrightarrow> m = 0 \<and> n = 0 \<or> m = n \<and> a = b"
  by (auto simp add: multiset_eq_iff)

lemma repeat_mset_cancel1: "repeat_mset a A = repeat_mset a B \<longleftrightarrow> A = B \<or> a = 0"
  by (auto simp: multiset_eq_iff)

lemma repeat_mset_cancel2: "repeat_mset a A = repeat_mset b A \<longleftrightarrow> a = b \<or> A = {#}"
  by (auto simp: multiset_eq_iff)

lemma repeat_mset_eq_empty_iff: "repeat_mset n A = {#} \<longleftrightarrow> n = 0 \<or> A = {#}"
  by (cases n) auto

lemma image_replicate_mset [simp]:
  "image_mset f (replicate_mset n a) = replicate_mset n (f a)"
  by (induct n) simp_all

lemma replicate_mset_msubseteq_iff:
  "replicate_mset m a \<subseteq># replicate_mset n b \<longleftrightarrow> m = 0 \<or> a = b \<and> m \<le> n"
  by (cases m)
    (auto simp: insert_subset_eq_iff simp flip: count_le_replicate_mset_subset_eq)

lemma msubseteq_replicate_msetE:
  assumes "A \<subseteq># replicate_mset n a"
  obtains m where "m \<le> n" and "A = replicate_mset m a"
proof (cases "n = 0")
  case True
  with assms that show thesis
    by simp
next
  case False
  from assms have "set_mset A \<subseteq> set_mset (replicate_mset n a)"
    by (rule set_mset_mono)
  with False have "set_mset A \<subseteq> {a}"
    by simp
  then have "\<exists>m. A = replicate_mset m a"
  proof (induction A)
    case empty
    then show ?case
      by simp
  next
    case (add b A)
    then obtain m where "A = replicate_mset m a"
      by auto
    with add.prems show ?case
      by (auto intro: exI [of _ "Suc m"])
  qed
  then obtain m where A: "A = replicate_mset m a" ..
  with assms have "m \<le> n"
    by (auto simp add: replicate_mset_msubseteq_iff)
  then show thesis using A ..
qed

lemma count_image_mset_lt_imp_lt_raw:
  assumes
    "finite A" and
    "A = set_mset M \<union> set_mset N" and
    "count (image_mset f M) b < count (image_mset f N) b"
  shows "\<exists>x. f x = b \<and> count M x < count N x"
  using assms
proof (induct A arbitrary: M N b rule: finite_induct)
  case (insert x F)
  note fin = this(1) and x_ni_f = this(2) and ih = this(3) and x_f_eq_m_n = this(4) and
    cnt_b = this(5)

  let ?Ma = "{#y \<in># M. y \<noteq> x#}"
  let ?Mb = "{#y \<in># M. y = x#}"
  let ?Na = "{#y \<in># N. y \<noteq> x#}"
  let ?Nb = "{#y \<in># N. y = x#}"

  have m_part: "M = ?Mb + ?Ma" and n_part: "N = ?Nb + ?Na"
    using multiset_partition by blast+

  have f_eq_ma_na: "F = set_mset ?Ma \<union> set_mset ?Na"
    using x_f_eq_m_n x_ni_f by auto

  show ?case
  proof (cases "count (image_mset f ?Ma) b < count (image_mset f ?Na) b")
    case cnt_ba: True
    obtain xa where "f xa = b" and "count ?Ma xa < count ?Na xa"
      using ih[OF f_eq_ma_na cnt_ba] by blast
    thus ?thesis
      by (metis count_filter_mset not_less0)
  next
    case cnt_ba: False
    have fx_eq_b: "f x = b"
      using cnt_b cnt_ba
      by (subst (asm) m_part, subst (asm) n_part,
          auto simp: filter_eq_replicate_mset split: if_splits)
    moreover have "count M x < count N x"
      using cnt_b cnt_ba
      by (subst (asm) m_part, subst (asm) n_part,
          auto simp: filter_eq_replicate_mset split: if_splits)
    ultimately show ?thesis
      by blast
  qed
qed auto

lemma count_image_mset_lt_imp_lt:
  assumes cnt_b: "count (image_mset f M) b < count (image_mset f N) b"
  shows "\<exists>x. f x = b \<and> count M x < count N x"
  by (rule count_image_mset_lt_imp_lt_raw[of "set_mset M \<union> set_mset N", OF _ refl cnt_b]) auto

lemma count_image_mset_le_imp_lt_raw:
  assumes
    "finite A" and
    "A = set_mset M \<union> set_mset N" and
    "count (image_mset f M) (f a) + count N a < count (image_mset f N) (f a) + count M a"
  shows "\<exists>b. f b = f a \<and> count M b < count N b"
  using assms
proof (induct A arbitrary: M N rule: finite_induct)
  case (insert x F)
  note fin = this(1) and x_ni_f = this(2) and ih = this(3) and x_f_eq_m_n = this(4) and
    cnt_lt = this(5)

  let ?Ma = "{#y \<in># M. y \<noteq> x#}"
  let ?Mb = "{#y \<in># M. y = x#}"
  let ?Na = "{#y \<in># N. y \<noteq> x#}"
  let ?Nb = "{#y \<in># N. y = x#}"

  have m_part: "M = ?Mb + ?Ma" and n_part: "N = ?Nb + ?Na"
    using multiset_partition by blast+

  have f_eq_ma_na: "F = set_mset ?Ma \<union> set_mset ?Na"
    using x_f_eq_m_n x_ni_f by auto

  show ?case
  proof (cases "f x = f a")
    case fx_ne_fa: False

    have cnt_fma_fa: "count (image_mset f ?Ma) (f a) = count (image_mset f M) (f a)"
      using fx_ne_fa by (subst (2) m_part) (auto simp: filter_eq_replicate_mset)
    have cnt_fna_fa: "count (image_mset f ?Na) (f a) = count (image_mset f N) (f a)"
      using fx_ne_fa by (subst (2) n_part) (auto simp: filter_eq_replicate_mset)
    have cnt_ma_a: "count ?Ma a = count M a"
      using fx_ne_fa by (subst (2) m_part) (auto simp: filter_eq_replicate_mset)
    have cnt_na_a: "count ?Na a = count N a"
      using fx_ne_fa by (subst (2) n_part) (auto simp: filter_eq_replicate_mset)

    obtain b where fb_eq_fa: "f b = f a" and cnt_b: "count ?Ma b < count ?Na b"
      using ih[OF f_eq_ma_na] cnt_lt unfolding cnt_fma_fa cnt_fna_fa cnt_ma_a cnt_na_a by blast
    have fx_ne_fb: "f x \<noteq> f b"
      using fb_eq_fa fx_ne_fa by simp

    have cnt_ma_b: "count ?Ma b = count M b"
      using fx_ne_fb by (subst (2) m_part) auto
    have cnt_na_b: "count ?Na b = count N b"
      using fx_ne_fb by (subst (2) n_part) auto

    show ?thesis
      using fb_eq_fa cnt_b unfolding cnt_ma_b cnt_na_b by blast
  next
    case fx_eq_fa: True
    show ?thesis
    proof (cases "x = a")
      case x_eq_a: True
      have "count (image_mset f ?Ma) (f a) + count ?Na a
        < count (image_mset f ?Na) (f a) + count ?Ma a"
        using cnt_lt x_eq_a by (subst (asm) (1 2) m_part, subst (asm) (1 2) n_part,
            auto simp: filter_eq_replicate_mset)
      thus ?thesis
        using ih[OF f_eq_ma_na] by (metis count_filter_mset nat_neq_iff)
    next
      case x_ne_a: False
      show ?thesis
      proof (cases "count M x < count N x")
        case True
        thus ?thesis
          using fx_eq_fa by blast
     next
        case False
        hence cnt_x: "count M x \<ge> count N x"
          by fastforce
        have "count M x + count (image_mset f ?Ma) (f a) + count ?Na a
          < count N x + count (image_mset f ?Na) (f a) + count ?Ma a"
          using cnt_lt x_ne_a fx_eq_fa by (subst (asm) (1 2) m_part, subst (asm) (1 2) n_part,
            auto simp: filter_eq_replicate_mset)
        hence "count (image_mset f ?Ma) (f a) + count ?Na a
          < count (image_mset f ?Na) (f a) + count ?Ma a"
          using cnt_x by linarith
        thus ?thesis
          using ih[OF f_eq_ma_na] by (metis count_filter_mset nat_neq_iff)
      qed
    qed
  qed
qed auto

lemma count_image_mset_le_imp_lt:
  assumes
    "count (image_mset f M) (f a) \<le> count (image_mset f N) (f a)" and
    "count M a > count N a"
  shows "\<exists>b. f b = f a \<and> count M b < count N b"
  using assms by (auto intro: count_image_mset_le_imp_lt_raw[of "set_mset M \<union> set_mset N"])

lemma size_filter_unsat_elem:
  assumes "x \<in># M" and "\<not> P x"
  shows "size {#x \<in># M. P x#} < size M"
proof -
  have "size (filter_mset P M) \<noteq> size M"
    using assms
    by (metis dual_order.strict_iff_order filter_mset_eq_conv mset_subset_size subset_mset.nless_le)
  then show ?thesis
    by (meson leD nat_neq_iff size_filter_mset_lesseq)
qed

lemma size_filter_ne_elem: "x \<in># M \<Longrightarrow> size {#y \<in># M. y \<noteq> x#} < size M"
  by (simp add: size_filter_unsat_elem[of x M "\<lambda>y. y \<noteq> x"])

lemma size_eq_ex_count_lt:
  assumes
    sz_m_eq_n: "size M = size N" and
    m_eq_n: "M \<noteq> N"
  shows "\<exists>x. count M x < count N x"
proof -
  obtain x where "count M x \<noteq> count N x"
    using m_eq_n by (meson multiset_eqI)
  moreover
  {
    assume "count M x < count N x"
    hence ?thesis
      by blast
  }
  moreover
  {
    assume cnt_x: "count M x > count N x"

    have "size {#y \<in># M. y = x#} + size {#y \<in># M. y \<noteq> x#} =
      size {#y \<in># N. y = x#} + size {#y \<in># N. y \<noteq> x#}"
      using sz_m_eq_n multiset_partition by (metis size_union)
    hence sz_m_minus_x: "size {#y \<in># M. y \<noteq> x#} < size {#y \<in># N. y \<noteq> x#}"
      using cnt_x by (simp add: filter_eq_replicate_mset)
    then obtain y where "count {#y \<in># M. y \<noteq> x#} y < count {#y \<in># N. y \<noteq> x#} y"
      using size_lt_imp_ex_count_lt[OF sz_m_minus_x] by blast
    hence "count M y < count N y"
      by (metis count_filter_mset less_asym)
    hence ?thesis
      by blast
  }
  ultimately show ?thesis
    by fastforce
qed


subsection \<open>Big operators\<close>

locale comm_monoid_mset = comm_monoid
begin

interpretation comp_fun_commute f
  by standard (simp add: fun_eq_iff left_commute)

interpretation comp?: comp_fun_commute "f \<circ> g"
  by (fact comp_comp_fun_commute)

context
begin

definition F :: "'a multiset \<Rightarrow> 'a"
  where eq_fold: "F M = fold_mset f \<^bold>1 M"

lemma empty [simp]: "F {#} = \<^bold>1"
  by (simp add: eq_fold)

lemma singleton [simp]: "F {#x#} = x"
proof -
  interpret comp_fun_commute
    by standard (simp add: fun_eq_iff left_commute)
  show ?thesis by (simp add: eq_fold)
qed

lemma union [simp]: "F (M + N) = F M \<^bold>* F N"
proof -
  interpret comp_fun_commute f
    by standard (simp add: fun_eq_iff left_commute)
  show ?thesis
    by (induct N) (simp_all add: left_commute eq_fold)
qed

lemma add_mset [simp]: "F (add_mset x N) = x \<^bold>* F N"
  unfolding add_mset_add_single[of x N] union by (simp add: ac_simps)

lemma insert [simp]:
  shows "F (image_mset g (add_mset x A)) = g x \<^bold>* F (image_mset g A)"
  by (simp add: eq_fold)

lemma remove:
  assumes "x \<in># A"
  shows "F A = x \<^bold>* F (A - {#x#})"
  using multi_member_split[OF assms] by auto

lemma neutral:
  "\<forall>x\<in>#A. x = \<^bold>1 \<Longrightarrow> F A = \<^bold>1"
  by (induct A) simp_all

lemma neutral_const [simp]:
  "F (image_mset (\<lambda>_. \<^bold>1) A) = \<^bold>1"
  by (simp add: neutral)

private lemma F_image_mset_product:
  "F {#g x j \<^bold>* F {#g i j. i \<in># A#}. j \<in># B#} =
    F (image_mset (g x) B) \<^bold>* F {#F {#g i j. i \<in># A#}. j \<in># B#}"
  by (induction B) (simp_all add: left_commute semigroup.assoc semigroup_axioms)

lemma swap:
  "F (image_mset (\<lambda>i. F (image_mset (g i) B)) A) =
    F (image_mset (\<lambda>j. F (image_mset (\<lambda>i. g i j) A)) B)"
  apply (induction A, simp)
  apply (induction B, auto simp add: F_image_mset_product ac_simps)
  done

lemma distrib: "F (image_mset (\<lambda>x. g x \<^bold>* h x) A) = F (image_mset g A) \<^bold>* F (image_mset h A)"
  by (induction A) (auto simp: ac_simps)

lemma union_disjoint:
  "A \<inter># B = {#} \<Longrightarrow> F (image_mset g (A \<union># B)) = F (image_mset g A) \<^bold>* F (image_mset g B)"
  by (induction A) (auto simp: ac_simps)

end
end

lemma comp_fun_commute_plus_mset[simp]: "comp_fun_commute ((+) :: 'a multiset \<Rightarrow> _ \<Rightarrow> _)"
  by standard (simp add: add_ac comp_def)

declare comp_fun_commute.fold_mset_add_mset[OF comp_fun_commute_plus_mset, simp]

lemma in_mset_fold_plus_iff[iff]: "x \<in># fold_mset (+) M NN \<longleftrightarrow> x \<in># M \<or> (\<exists>N. N \<in># NN \<and> x \<in># N)"
  by (induct NN) auto

context comm_monoid_add
begin

sublocale sum_mset: comm_monoid_mset plus 0
  defines sum_mset = sum_mset.F ..

lemma sum_unfold_sum_mset:
  "sum f A = sum_mset (image_mset f (mset_set A))"
  by (cases "finite A") (induct A rule: finite_induct, simp_all)

end

notation sum_mset ("\<Sum>\<^sub>#")

syntax (ASCII)
  "_sum_mset_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"  ("(3SUM _:#_. _)" [0, 51, 10] 10)
syntax
  "_sum_mset_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add"  ("(3\<Sum>_\<in>#_. _)" [0, 51, 10] 10)
translations
  "\<Sum>i \<in># A. b" \<rightleftharpoons> "CONST sum_mset (CONST image_mset (\<lambda>i. b) A)"

context comm_monoid_add
begin

lemma sum_mset_sum_list:
  "sum_mset (mset xs) = sum_list xs"
  by (induction xs) auto

end

context canonically_ordered_monoid_add
begin

lemma sum_mset_0_iff [simp]:
  "sum_mset M = 0  \<longleftrightarrow> (\<forall>x \<in> set_mset M. x = 0)"
  by (induction M) auto

end

context ordered_comm_monoid_add
begin

lemma sum_mset_mono:
  "sum_mset (image_mset f K) \<le> sum_mset (image_mset g K)"
  if "\<And>i. i \<in># K \<Longrightarrow> f i \<le> g i"
  using that by (induction K) (simp_all add: add_mono)

end

context cancel_comm_monoid_add
begin

lemma sum_mset_diff:
  "sum_mset (M - N) = sum_mset M - sum_mset N" if "N \<subseteq># M" for M N :: "'a multiset"
  using that by (auto simp add: subset_mset.le_iff_add)

end

context semiring_0
begin

lemma sum_mset_distrib_left:
  "c * (\<Sum>x \<in># M. f x) = (\<Sum>x \<in># M. c * f(x))"
  by (induction M) (simp_all add: algebra_simps)

lemma sum_mset_distrib_right:
  "(\<Sum>x \<in># M. f x) * c = (\<Sum>x \<in># M. f x * c)"
  by (induction M) (simp_all add: algebra_simps)

end

lemma sum_mset_product:
  fixes f :: "'a::{comm_monoid_add,times} \<Rightarrow> 'b::semiring_0"
  shows "(\<Sum>i \<in># A. f i) * (\<Sum>i \<in># B. g i) = (\<Sum>i\<in>#A. \<Sum>j\<in>#B. f i * g j)"
  by (subst sum_mset.swap) (simp add: sum_mset_distrib_left sum_mset_distrib_right)

context semiring_1
begin

lemma sum_mset_replicate_mset [simp]:
  "sum_mset (replicate_mset n a) = of_nat n * a"
  by (induction n) (simp_all add: algebra_simps)

lemma sum_mset_delta:
  "sum_mset (image_mset (\<lambda>x. if x = y then c else 0) A) = c * of_nat (count A y)"
  by (induction A) (simp_all add: algebra_simps)

lemma sum_mset_delta':
  "sum_mset (image_mset (\<lambda>x. if y = x then c else 0) A) = c * of_nat (count A y)"
  by (induction A) (simp_all add: algebra_simps)

end

lemma of_nat_sum_mset [simp]:
  "of_nat (sum_mset A) = sum_mset (image_mset of_nat A)"
  by (induction A) auto

lemma size_eq_sum_mset:
  "size M = (\<Sum>a\<in>#M. 1)"
  using image_mset_const_eq [of "1::nat" M] by simp

lemma size_mset_set [simp]:
  "size (mset_set A) = card A"
  by (simp only: size_eq_sum_mset card_eq_sum sum_unfold_sum_mset)

lemma sum_mset_constant [simp]:
  fixes y :: "'b::semiring_1"
  shows \<open>(\<Sum>x\<in>#A. y) = of_nat (size A) * y\<close>
  by (induction A) (auto simp: algebra_simps)

lemma set_mset_Union_mset[simp]: "set_mset (\<Sum>\<^sub># MM) = (\<Union>M \<in> set_mset MM. set_mset M)"
  by (induct MM) auto

lemma in_Union_mset_iff[iff]: "x \<in># \<Sum>\<^sub># MM \<longleftrightarrow> (\<exists>M. M \<in># MM \<and> x \<in># M)"
  by (induct MM) auto

lemma count_sum:
  "count (sum f A) x = sum (\<lambda>a. count (f a) x) A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma sum_eq_empty_iff:
  assumes "finite A"
  shows "sum f A = {#} \<longleftrightarrow> (\<forall>a\<in>A. f a = {#})"
  using assms by induct simp_all

lemma Union_mset_empty_conv[simp]: "\<Sum>\<^sub># M = {#} \<longleftrightarrow> (\<forall>i\<in>#M. i = {#})"
  by (induction M) auto

lemma Union_image_single_mset[simp]: "\<Sum>\<^sub># (image_mset (\<lambda>x. {#x#}) m) = m"
  by(induction m) auto

lemma size_multiset_sum_mset [simp]: "size (\<Sum>X\<in>#A. X :: 'a multiset) = (\<Sum>X\<in>#A. size X)"
  by (induction A) auto

context comm_monoid_mult
begin

sublocale prod_mset: comm_monoid_mset times 1
  defines prod_mset = prod_mset.F ..

lemma prod_mset_empty:
  "prod_mset {#} = 1"
  by (fact prod_mset.empty)

lemma prod_mset_singleton:
  "prod_mset {#x#} = x"
  by (fact prod_mset.singleton)

lemma prod_mset_Un:
  "prod_mset (A + B) = prod_mset A * prod_mset B"
  by (fact prod_mset.union)

lemma prod_mset_prod_list:
  "prod_mset (mset xs) = prod_list xs"
  by (induct xs) auto

lemma prod_mset_replicate_mset [simp]:
  "prod_mset (replicate_mset n a) = a ^ n"
  by (induct n) simp_all

lemma prod_unfold_prod_mset:
  "prod f A = prod_mset (image_mset f (mset_set A))"
  by (cases "finite A") (induct A rule: finite_induct, simp_all)

lemma prod_mset_multiplicity:
  "prod_mset M = prod (\<lambda>x. x ^ count M x) (set_mset M)"
  by (simp add: fold_mset_def prod.eq_fold prod_mset.eq_fold funpow_times_power comp_def)

lemma prod_mset_delta: "prod_mset (image_mset (\<lambda>x. if x = y then c else 1) A) = c ^ count A y"
  by (induction A) simp_all

lemma prod_mset_delta': "prod_mset (image_mset (\<lambda>x. if y = x then c else 1) A) = c ^ count A y"
  by (induction A) simp_all

lemma prod_mset_subset_imp_dvd:
  assumes "A \<subseteq># B"
  shows   "prod_mset A dvd prod_mset B"
proof -
  from assms have "B = (B - A) + A" by (simp add: subset_mset.diff_add)
  also have "prod_mset \<dots> = prod_mset (B - A) * prod_mset A" by simp
  also have "prod_mset A dvd \<dots>" by simp
  finally show ?thesis .
qed

lemma dvd_prod_mset:
  assumes "x \<in># A"
  shows "x dvd prod_mset A"
  using assms prod_mset_subset_imp_dvd [of "{#x#}" A] by simp

end

notation prod_mset ("\<Prod>\<^sub>#")

syntax (ASCII)
  "_prod_mset_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"  ("(3PROD _:#_. _)" [0, 51, 10] 10)
syntax
  "_prod_mset_image" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_mult"  ("(3\<Prod>_\<in>#_. _)" [0, 51, 10] 10)
translations
  "\<Prod>i \<in># A. b" \<rightleftharpoons> "CONST prod_mset (CONST image_mset (\<lambda>i. b) A)"

lemma prod_mset_constant [simp]: "(\<Prod>_\<in>#A. c) = c ^ size A"
  by (simp add: image_mset_const_eq)

lemma (in semidom) prod_mset_zero_iff [iff]:
  "prod_mset A = 0 \<longleftrightarrow> 0 \<in># A"
  by (induct A) auto

lemma (in semidom_divide) prod_mset_diff:
  assumes "B \<subseteq># A" and "0 \<notin># B"
  shows "prod_mset (A - B) = prod_mset A div prod_mset B"
proof -
  from assms obtain C where "A = B + C"
    by (metis subset_mset.add_diff_inverse)
  with assms show ?thesis by simp
qed

lemma (in semidom_divide) prod_mset_minus:
  assumes "a \<in># A" and "a \<noteq> 0"
  shows "prod_mset (A - {#a#}) = prod_mset A div a"
  using assms prod_mset_diff [of "{#a#}" A] by auto

lemma (in normalization_semidom) normalize_prod_mset_normalize:
  "normalize (prod_mset (image_mset normalize A)) = normalize (prod_mset A)"
proof (induction A)
  case (add x A)
  have "normalize (prod_mset (image_mset normalize (add_mset x A))) =
          normalize (x * normalize (prod_mset (image_mset normalize A)))"
    by simp
  also note add.IH
  finally show ?case by simp
qed auto

lemma (in algebraic_semidom) is_unit_prod_mset_iff:
  "is_unit (prod_mset A) \<longleftrightarrow> (\<forall>x \<in># A. is_unit x)"
  by (induct A) (auto simp: is_unit_mult_iff)

lemma (in normalization_semidom_multiplicative) normalize_prod_mset:
  "normalize (prod_mset A) = prod_mset (image_mset normalize A)"
  by (induct A) (simp_all add: normalize_mult)

lemma (in normalization_semidom_multiplicative) normalized_prod_msetI:
  assumes "\<And>a. a \<in># A \<Longrightarrow> normalize a = a"
  shows "normalize (prod_mset A) = prod_mset A"
proof -
  from assms have "image_mset normalize A = A"
    by (induct A) simp_all
  then show ?thesis by (simp add: normalize_prod_mset)
qed

lemma image_prod_mset_multiplicity:
  "prod_mset (image_mset f M) = prod (\<lambda>x. f x ^ count M x) (set_mset M)"
proof (induction M)
  case (add x M)
  show ?case
  proof (cases "x \<in> set_mset M")
    case True
    have "(\<Prod>y\<in>set_mset (add_mset x M). f y ^ count (add_mset x M) y) = 
            (\<Prod>y\<in>set_mset M. (if y = x then f x else 1) * f y ^ count M y)"
      using True add by (intro prod.cong) auto
    also have "\<dots> = f x * (\<Prod>y\<in>set_mset M. f y ^ count M y)"
      using True by (subst prod.distrib) auto
    also note add.IH [symmetric]
    finally show ?thesis using True by simp
  next
    case False
    hence "(\<Prod>y\<in>set_mset (add_mset x M). f y ^ count (add_mset x M) y) =
              f x * (\<Prod>y\<in>set_mset M. f y ^ count (add_mset x M) y)"
      by (auto simp: not_in_iff)
    also have "(\<Prod>y\<in>set_mset M. f y ^ count (add_mset x M) y) = 
                 (\<Prod>y\<in>set_mset M. f y ^ count M y)"
      using False by (intro prod.cong) auto
    also note add.IH [symmetric]
    finally show ?thesis by simp
  qed
qed auto

subsection \<open>Multiset as order-ignorant lists\<close>

context linorder
begin

lemma mset_insort [simp]:
  "mset (insort_key k x xs) = add_mset x (mset xs)"
  by (induct xs) simp_all

lemma mset_sort [simp]:
  "mset (sort_key k xs) = mset xs"
  by (induct xs) simp_all

text \<open>
  This lemma shows which properties suffice to show that a function
  \<open>f\<close> with \<open>f xs = ys\<close> behaves like sort.
\<close>

lemma properties_for_sort_key:
  assumes "mset ys = mset xs"
    and "\<And>k. k \<in> set ys \<Longrightarrow> filter (\<lambda>x. f k = f x) ys = filter (\<lambda>x. f k = f x) xs"
    and "sorted (map f ys)"
  shows "sort_key f xs = ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(2) have
    "\<forall>k \<in> set ys. filter (\<lambda>x. f k = f x) (remove1 x ys) = filter (\<lambda>x. f k = f x) xs"
    by (simp add: filter_remove1)
  with Cons.prems have "sort_key f xs = remove1 x ys"
    by (auto intro!: Cons.hyps simp add: sorted_map_remove1)
  moreover from Cons.prems have "x \<in># mset ys"
    by auto
  then have "x \<in> set ys"
    by simp
  ultimately show ?case using Cons.prems by (simp add: insort_key_remove1)
qed

lemma properties_for_sort:
  assumes multiset: "mset ys = mset xs"
    and "sorted ys"
  shows "sort xs = ys"
proof (rule properties_for_sort_key)
  from multiset show "mset ys = mset xs" .
  from \<open>sorted ys\<close> show "sorted (map (\<lambda>x. x) ys)" by simp
  from multiset have "length (filter (\<lambda>y. k = y) ys) = length (filter (\<lambda>x. k = x) xs)" for k
    by (rule mset_eq_length_filter)
  then have "replicate (length (filter (\<lambda>y. k = y) ys)) k =
    replicate (length (filter (\<lambda>x. k = x) xs)) k" for k
    by simp
  then show "k \<in> set ys \<Longrightarrow> filter (\<lambda>y. k = y) ys = filter (\<lambda>x. k = x) xs" for k
    by (simp add: replicate_length_filter)
qed

lemma sort_key_inj_key_eq:
  assumes mset_equal: "mset xs = mset ys"
    and "inj_on f (set xs)"
    and "sorted (map f ys)"
  shows "sort_key f xs = ys"
proof (rule properties_for_sort_key)
  from mset_equal
  show "mset ys = mset xs" by simp
  from \<open>sorted (map f ys)\<close>
  show "sorted (map f ys)" .
  show "[x\<leftarrow>ys . f k = f x] = [x\<leftarrow>xs . f k = f x]" if "k \<in> set ys" for k
  proof -
    from mset_equal
    have set_equal: "set xs = set ys" by (rule mset_eq_setD)
    with that have "insert k (set ys) = set ys" by auto
    with \<open>inj_on f (set xs)\<close> have inj: "inj_on f (insert k (set ys))"
      by (simp add: set_equal)
    from inj have "[x\<leftarrow>ys . f k = f x] = filter (HOL.eq k) ys"
      by (auto intro!: inj_on_filter_key_eq)
    also have "\<dots> = replicate (count (mset ys) k) k"
      by (simp add: replicate_count_mset_eq_filter_eq)
    also have "\<dots> = replicate (count (mset xs) k) k"
      using mset_equal by simp
    also have "\<dots> = filter (HOL.eq k) xs"
      by (simp add: replicate_count_mset_eq_filter_eq)
    also have "\<dots> = [x\<leftarrow>xs . f k = f x]"
      using inj by (auto intro!: inj_on_filter_key_eq [symmetric] simp add: set_equal)
    finally show ?thesis .
  qed
qed

lemma sort_key_eq_sort_key:
  assumes "mset xs = mset ys"
    and "inj_on f (set xs)"
  shows "sort_key f xs = sort_key f ys"
  by (rule sort_key_inj_key_eq) (simp_all add: assms)

lemma sort_key_by_quicksort:
  "sort_key f xs = sort_key f [x\<leftarrow>xs. f x < f (xs ! (length xs div 2))]
    @ [x\<leftarrow>xs. f x = f (xs ! (length xs div 2))]
    @ sort_key f [x\<leftarrow>xs. f x > f (xs ! (length xs div 2))]" (is "sort_key f ?lhs = ?rhs")
proof (rule properties_for_sort_key)
  show "mset ?rhs = mset ?lhs"
    by (rule multiset_eqI) auto
  show "sorted (map f ?rhs)"
    by (auto simp add: sorted_append intro: sorted_map_same)
next
  fix l
  assume "l \<in> set ?rhs"
  let ?pivot = "f (xs ! (length xs div 2))"
  have *: "\<And>x. f l = f x \<longleftrightarrow> f x = f l" by auto
  have "[x \<leftarrow> sort_key f xs . f x = f l] = [x \<leftarrow> xs. f x = f l]"
    unfolding filter_sort by (rule properties_for_sort_key) (auto intro: sorted_map_same)
  with * have **: "[x \<leftarrow> sort_key f xs . f l = f x] = [x \<leftarrow> xs. f l = f x]" by simp
  have "\<And>x P. P (f x) ?pivot \<and> f l = f x \<longleftrightarrow> P (f l) ?pivot \<and> f l = f x" by auto
  then have "\<And>P. [x \<leftarrow> sort_key f xs . P (f x) ?pivot \<and> f l = f x] =
    [x \<leftarrow> sort_key f xs. P (f l) ?pivot \<and> f l = f x]" by simp
  note *** = this [of "(<)"] this [of "(>)"] this [of "(=)"]
  show "[x \<leftarrow> ?rhs. f l = f x] = [x \<leftarrow> ?lhs. f l = f x]"
  proof (cases "f l" ?pivot rule: linorder_cases)
    case less
    then have "f l \<noteq> ?pivot" and "\<not> f l > ?pivot" by auto
    with less show ?thesis
      by (simp add: filter_sort [symmetric] ** ***)
  next
    case equal then show ?thesis
      by (simp add: * less_le)
  next
    case greater
    then have "f l \<noteq> ?pivot" and "\<not> f l < ?pivot" by auto
    with greater show ?thesis
      by (simp add: filter_sort [symmetric] ** ***)
  qed
qed

lemma sort_by_quicksort:
  "sort xs = sort [x\<leftarrow>xs. x < xs ! (length xs div 2)]
    @ [x\<leftarrow>xs. x = xs ! (length xs div 2)]
    @ sort [x\<leftarrow>xs. x > xs ! (length xs div 2)]" (is "sort ?lhs = ?rhs")
  using sort_key_by_quicksort [of "\<lambda>x. x", symmetric] by simp

text \<open>A stable parameterized quicksort\<close>

definition part :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'b list \<times> 'b list \<times> 'b list" where
  "part f pivot xs = ([x \<leftarrow> xs. f x < pivot], [x \<leftarrow> xs. f x = pivot], [x \<leftarrow> xs. pivot < f x])"

lemma part_code [code]:
  "part f pivot [] = ([], [], [])"
  "part f pivot (x # xs) = (let (lts, eqs, gts) = part f pivot xs; x' = f x in
     if x' < pivot then (x # lts, eqs, gts)
     else if x' > pivot then (lts, eqs, x # gts)
     else (lts, x # eqs, gts))"
  by (auto simp add: part_def Let_def split_def)

lemma sort_key_by_quicksort_code [code]:
  "sort_key f xs =
    (case xs of
      [] \<Rightarrow> []
    | [x] \<Rightarrow> xs
    | [x, y] \<Rightarrow> (if f x \<le> f y then xs else [y, x])
    | _ \<Rightarrow>
        let (lts, eqs, gts) = part f (f (xs ! (length xs div 2))) xs
        in sort_key f lts @ eqs @ sort_key f gts)"
proof (cases xs)
  case Nil then show ?thesis by simp
next
  case (Cons _ ys) note hyps = Cons show ?thesis
  proof (cases ys)
    case Nil with hyps show ?thesis by simp
  next
    case (Cons _ zs) note hyps = hyps Cons show ?thesis
    proof (cases zs)
      case Nil with hyps show ?thesis by auto
    next
      case Cons
      from sort_key_by_quicksort [of f xs]
      have "sort_key f xs = (let (lts, eqs, gts) = part f (f (xs ! (length xs div 2))) xs
        in sort_key f lts @ eqs @ sort_key f gts)"
      by (simp only: split_def Let_def part_def fst_conv snd_conv)
      with hyps Cons show ?thesis by (simp only: list.cases)
    qed
  qed
qed

end

hide_const (open) part

lemma mset_remdups_subset_eq: "mset (remdups xs) \<subseteq># mset xs"
  by (induct xs) (auto intro: subset_mset.order_trans)

lemma mset_update:
  "i < length ls \<Longrightarrow> mset (ls[i := v]) = add_mset v (mset ls - {#ls ! i#})"
proof (induct ls arbitrary: i)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0 then show ?thesis by simp
  next
    case (Suc i')
    with Cons show ?thesis
      by (cases \<open>x = xs ! i'\<close>) auto
  qed
qed

lemma mset_swap:
  "i < length ls \<Longrightarrow> j < length ls \<Longrightarrow>
    mset (ls[j := ls ! i, i := ls ! j]) = mset ls"
  by (cases "i = j") (simp_all add: mset_update nth_mem_mset)

lemma mset_eq_finite:
  \<open>finite {ys. mset ys = mset xs}\<close>
proof -
  have \<open>{ys. mset ys = mset xs} \<subseteq> {ys. set ys \<subseteq> set xs \<and> length ys \<le> length xs}\<close>
    by (auto simp add: dest: mset_eq_setD mset_eq_length)
  moreover have \<open>finite {ys. set ys \<subseteq> set xs \<and> length ys \<le> length xs}\<close>
    using finite_lists_length_le by blast
  ultimately show ?thesis
    by (rule finite_subset)
qed


subsection \<open>The multiset order\<close>

definition mult1 :: "('a \<times> 'a) set \<Rightarrow> ('a multiset \<times> 'a multiset) set" where
  "mult1 r = {(N, M). \<exists>a M0 K. M = add_mset a M0 \<and> N = M0 + K \<and>
      (\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r)}"

definition mult :: "('a \<times> 'a) set \<Rightarrow> ('a multiset \<times> 'a multiset) set" where
  "mult r = (mult1 r)\<^sup>+"

definition multp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "multp r M N \<longleftrightarrow> (M, N) \<in> mult {(x, y). r x y}"

declare multp_def[pred_set_conv]

lemma mult1I:
  assumes "M = add_mset a M0" and "N = M0 + K" and "\<And>b. b \<in># K \<Longrightarrow> (b, a) \<in> r"
  shows "(N, M) \<in> mult1 r"
  using assms unfolding mult1_def by blast

lemma mult1E:
  assumes "(N, M) \<in> mult1 r"
  obtains a M0 K where "M = add_mset a M0" "N = M0 + K" "\<And>b. b \<in># K \<Longrightarrow> (b, a) \<in> r"
  using assms unfolding mult1_def by blast

lemma mono_mult1:
  assumes "r \<subseteq> r'" shows "mult1 r \<subseteq> mult1 r'"
  unfolding mult1_def using assms by blast

lemma mono_mult:
  assumes "r \<subseteq> r'" shows "mult r \<subseteq> mult r'"
  unfolding mult_def using mono_mult1[OF assms] trancl_mono by blast

lemma mono_multp[mono]: "r \<le> r' \<Longrightarrow> multp r \<le> multp r'"
  unfolding le_fun_def le_bool_def
proof (intro allI impI)
  fix M N :: "'a multiset"
  assume "\<forall>x xa. r x xa \<longrightarrow> r' x xa"
  hence "{(x, y). r x y} \<subseteq> {(x, y). r' x y}"
    by blast
  thus "multp r M N \<Longrightarrow> multp r' M N"
    unfolding multp_def
    by (fact mono_mult[THEN subsetD, rotated])
qed

lemma not_less_empty [iff]: "(M, {#}) \<notin> mult1 r"
  by (simp add: mult1_def)


subsubsection \<open>Well-foundedness\<close>

lemma less_add:
  assumes mult1: "(N, add_mset a M0) \<in> mult1 r"
  shows
    "(\<exists>M. (M, M0) \<in> mult1 r \<and> N = add_mset a M) \<or>
     (\<exists>K. (\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r) \<and> N = M0 + K)"
proof -
  let ?r = "\<lambda>K a. \<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r"
  let ?R = "\<lambda>N M. \<exists>a M0 K. M = add_mset a M0 \<and> N = M0 + K \<and> ?r K a"
  obtain a' M0' K where M0: "add_mset a M0 = add_mset a' M0'"
    and N: "N = M0' + K"
    and r: "?r K a'"
    using mult1 unfolding mult1_def by auto
  show ?thesis (is "?case1 \<or> ?case2")
  proof -
    from M0 consider "M0 = M0'" "a = a'"
      | K' where "M0 = add_mset a' K'" "M0' = add_mset a K'"
      by atomize_elim (simp only: add_eq_conv_ex)
    then show ?thesis
    proof cases
      case 1
      with N r have "?r K a \<and> N = M0 + K" by simp
      then have ?case2 ..
      then show ?thesis ..
    next
      case 2
      from N 2(2) have n: "N = add_mset a (K' + K)" by simp
      with r 2(1) have "?R (K' + K) M0" by blast
      with n have ?case1 by (simp add: mult1_def)
      then show ?thesis ..
    qed
  qed
qed

lemma all_accessible:
  assumes "wf r"
  shows "\<forall>M. M \<in> Wellfounded.acc (mult1 r)"
proof
  let ?R = "mult1 r"
  let ?W = "Wellfounded.acc ?R"
  {
    fix M M0 a
    assume M0: "M0 \<in> ?W"
      and wf_hyp: "\<And>b. (b, a) \<in> r \<Longrightarrow> (\<forall>M \<in> ?W. add_mset b M \<in> ?W)"
      and acc_hyp: "\<forall>M. (M, M0) \<in> ?R \<longrightarrow> add_mset a M \<in> ?W"
    have "add_mset a M0 \<in> ?W"
    proof (rule accI [of "add_mset a M0"])
      fix N
      assume "(N, add_mset a M0) \<in> ?R"
      then consider M where "(M, M0) \<in> ?R" "N = add_mset a M"
        | K where "\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r" "N = M0 + K"
        by atomize_elim (rule less_add)
      then show "N \<in> ?W"
      proof cases
        case 1
        from acc_hyp have "(M, M0) \<in> ?R \<longrightarrow> add_mset a M \<in> ?W" ..
        from this and \<open>(M, M0) \<in> ?R\<close> have "add_mset a M \<in> ?W" ..
        then show "N \<in> ?W" by (simp only: \<open>N = add_mset a M\<close>)
      next
        case 2
        from this(1) have "M0 + K \<in> ?W"
        proof (induct K)
          case empty
          from M0 show "M0 + {#} \<in> ?W" by simp
        next
          case (add x K)
          from add.prems have "(x, a) \<in> r" by simp
          with wf_hyp have "\<forall>M \<in> ?W. add_mset x M \<in> ?W" by blast
          moreover from add have "M0 + K \<in> ?W" by simp
          ultimately have "add_mset x (M0 + K) \<in> ?W" ..
          then show "M0 + (add_mset x K) \<in> ?W" by simp
        qed
        then show "N \<in> ?W" by (simp only: 2(2))
      qed
    qed
  } note tedious_reasoning = this

  show "M \<in> ?W" for M
  proof (induct M)
    show "{#} \<in> ?W"
    proof (rule accI)
      fix b assume "(b, {#}) \<in> ?R"
      with not_less_empty show "b \<in> ?W" by contradiction
    qed

    fix M a assume "M \<in> ?W"
    from \<open>wf r\<close> have "\<forall>M \<in> ?W. add_mset a M \<in> ?W"
    proof induct
      fix a
      assume r: "\<And>b. (b, a) \<in> r \<Longrightarrow> (\<forall>M \<in> ?W. add_mset b M \<in> ?W)"
      show "\<forall>M \<in> ?W. add_mset a M \<in> ?W"
      proof
        fix M assume "M \<in> ?W"
        then show "add_mset a M \<in> ?W"
          by (rule acc_induct) (rule tedious_reasoning [OF _ r])
      qed
    qed
    from this and \<open>M \<in> ?W\<close> show "add_mset a M \<in> ?W" ..
  qed
qed

lemma wf_mult1: "wf r \<Longrightarrow> wf (mult1 r)"
  by (rule acc_wfI) (rule all_accessible)

lemma wf_mult: "wf r \<Longrightarrow> wf (mult r)"
  unfolding mult_def by (rule wf_trancl) (rule wf_mult1)

lemma wfP_multp: "wfP r \<Longrightarrow> wfP (multp r)"
  unfolding multp_def wfP_def
  by (simp add: wf_mult)


subsubsection \<open>Closure-free presentation\<close>

text \<open>One direction.\<close>
lemma mult_implies_one_step:
  assumes
    trans: "trans r" and
    MN: "(M, N) \<in> mult r"
  shows "\<exists>I J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and> (\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> r)"
  using MN unfolding mult_def mult1_def
proof (induction rule: converse_trancl_induct)
  case (base y)
  then show ?case by force
next
  case (step y z) note yz = this(1) and zN = this(2) and N_decomp = this(3)
  obtain I J K where
    N: "N = I + J" "z = I + K" "J \<noteq> {#}" "\<forall>k\<in>#K. \<exists>j\<in>#J. (k, j) \<in> r"
    using N_decomp by blast
  obtain a M0 K' where
    z: "z = add_mset a M0" and y: "y = M0 + K'" and K: "\<forall>b. b \<in># K' \<longrightarrow> (b, a) \<in> r"
    using yz by blast
  show ?case
  proof (cases "a \<in># K")
    case True
    moreover have "\<exists>j\<in>#J. (k, j) \<in> r" if "k \<in># K'" for k
      using K N trans True by (meson that transE)
    ultimately show ?thesis
      by (rule_tac x = I in exI, rule_tac x = J in exI, rule_tac x = "(K - {#a#}) + K'" in exI)
        (use z y N in \<open>auto simp del: subset_mset.add_diff_assoc2 dest: in_diffD\<close>)
  next
    case False
    then have "a \<in># I" by (metis N(2) union_iff union_single_eq_member z)
    moreover have "M0 = I + K - {#a#}"
      using N(2) z by force
    ultimately show ?thesis
      by (rule_tac x = "I - {#a#}" in exI, rule_tac x = "add_mset a J" in exI,
          rule_tac x = "K + K'" in exI)
        (use z y N False K in \<open>auto simp: add.assoc\<close>)
  qed
qed

lemma multp_implies_one_step:
  "transp R \<Longrightarrow> multp R M N \<Longrightarrow> \<exists>I J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>#K. \<exists>x\<in>#J. R k x)"
  by (rule mult_implies_one_step[to_pred])

lemma one_step_implies_mult:
  assumes
    "J \<noteq> {#}" and
    "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> r"
  shows "(I + K, I + J) \<in> mult r"
  using assms
proof (induction "size J" arbitrary: I J K)
  case 0
  then show ?case by auto
next
  case (Suc n) note IH = this(1) and size_J = this(2)[THEN sym]
  obtain J' a where J: "J = add_mset a J'"
    using size_J by (blast dest: size_eq_Suc_imp_eq_union)
  show ?case
  proof (cases "J' = {#}")
    case True
    then show ?thesis
      using J Suc by (fastforce simp add: mult_def mult1_def)
  next
    case [simp]: False
    have K: "K = {#x \<in># K. (x, a) \<in> r#} + {#x \<in># K. (x, a) \<notin> r#}"
      by simp
    have "(I + K, (I + {# x \<in># K. (x, a) \<in> r #}) + J') \<in> mult r"
      using IH[of J' "{# x \<in># K. (x, a) \<notin> r#}" "I + {# x \<in># K. (x, a) \<in> r#}"]
        J Suc.prems K size_J by (auto simp: ac_simps)
    moreover have "(I + {#x \<in># K. (x, a) \<in> r#} + J', I + J) \<in> mult r"
      by (fastforce simp: J mult1_def mult_def)
    ultimately show ?thesis
      unfolding mult_def by simp
  qed
qed

lemma one_step_implies_multp:
  "J \<noteq> {#} \<Longrightarrow> \<forall>k\<in>#K. \<exists>j\<in>#J. R k j \<Longrightarrow> multp R (I + K) (I + J)"
  by (rule one_step_implies_mult[of _ _ "{(x, y). r x y}" for r, folded multp_def, simplified])

lemma subset_implies_mult:
  assumes sub: "A \<subset># B"
  shows "(A, B) \<in> mult r"
proof -
  have ApBmA: "A + (B - A) = B"
    using sub by simp
  have BmA: "B - A \<noteq> {#}"
    using sub by (simp add: Diff_eq_empty_iff_mset subset_mset.less_le_not_le)
  thus ?thesis
    by (rule one_step_implies_mult[of "B - A" "{#}" _ A, unfolded ApBmA, simplified])
qed

lemma subset_implies_multp: "A \<subset># B \<Longrightarrow> multp r A B"
  by (rule subset_implies_mult[of _ _ "{(x, y). r x y}" for r, folded multp_def])

lemma multp_repeat_mset_repeat_msetI:
  assumes "transp R" and "multp R A B" and "n \<noteq> 0"
  shows "multp R (repeat_mset n A) (repeat_mset n  B)"
proof -
  from \<open>transp R\<close> \<open>multp R A B\<close> obtain I J K where
    "B = I + J" and "A = I + K" and "J \<noteq> {#}" and "\<forall>k \<in># K. \<exists>x \<in># J. R k x"
    by (auto dest: multp_implies_one_step)

  have repeat_n_A_eq: "repeat_mset n A = repeat_mset n I + repeat_mset n K"
    using \<open>A = I + K\<close> by simp

  have repeat_n_B_eq: "repeat_mset n B = repeat_mset n I + repeat_mset n J"
    using \<open>B = I + J\<close> by simp

  show ?thesis
    unfolding repeat_n_A_eq repeat_n_B_eq
  proof (rule one_step_implies_multp)
    from \<open>n \<noteq> 0\<close> show "repeat_mset n J \<noteq> {#}"
      using \<open>J \<noteq> {#}\<close>
      by (simp add: repeat_mset_eq_empty_iff)
  next
    show "\<forall>k \<in># repeat_mset n K. \<exists>j \<in># repeat_mset n J. R k j"
      using \<open>\<forall>k \<in># K. \<exists>x \<in># J. R k x\<close>
      by (metis count_greater_zero_iff nat_0_less_mult_iff repeat_mset.rep_eq)
  qed
qed


subsubsection \<open>Monotonicity\<close>

lemma multp_mono_strong:
  assumes "multp R M1 M2" and "transp R" and
    S_if_R: "\<And>x y. x \<in> set_mset M1 \<Longrightarrow> y \<in> set_mset M2 \<Longrightarrow> R x y \<Longrightarrow> S x y"
  shows "multp S M1 M2"
proof -
  obtain I J K where "M2 = I + J" and "M1 = I + K" and "J \<noteq> {#}" and "\<forall>k\<in>#K. \<exists>x\<in>#J. R k x"
    using multp_implies_one_step[OF \<open>transp R\<close> \<open>multp R M1 M2\<close>] by auto
  show ?thesis
    unfolding \<open>M2 = I + J\<close> \<open>M1 = I + K\<close>
  proof (rule one_step_implies_multp[OF \<open>J \<noteq> {#}\<close>])
    show "\<forall>k\<in>#K. \<exists>j\<in>#J. S k j"
      using S_if_R
      by (metis \<open>M1 = I + K\<close> \<open>M2 = I + J\<close> \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. R k x\<close> union_iff)
  qed
qed

lemma mult_mono_strong:
  assumes "(M1, M2) \<in> mult r" and "trans r" and
    S_if_R: "\<And>x y. x \<in> set_mset M1 \<Longrightarrow> y \<in> set_mset M2 \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (x, y) \<in> s"
  shows "(M1, M2) \<in> mult s"
  using assms multp_mono_strong[of "\<lambda>x y. (x, y) \<in> r" M1 M2 "\<lambda>x y. (x, y) \<in> s",
      unfolded multp_def transp_trans_eq, simplified]
  by blast

lemma monotone_on_multp_multp_image_mset:
  assumes "monotone_on A orda ordb f" and "transp orda"
  shows "monotone_on {M. set_mset M \<subseteq> A} (multp orda) (multp ordb) (image_mset f)"
proof (rule monotone_onI)
  fix M1 M2
  assume
    M1_in: "M1 \<in> {M. set_mset M \<subseteq> A}" and
    M2_in: "M2 \<in> {M. set_mset M \<subseteq> A}" and
    M1_lt_M2: "multp orda M1 M2"

  from multp_implies_one_step[OF \<open>transp orda\<close> M1_lt_M2] obtain I J K where
    M2_eq: "M2 = I + J" and
    M1_eq: "M1 = I + K" and
    J_neq_mempty: "J \<noteq> {#}" and
    ball_K_less: "\<forall>k\<in>#K. \<exists>x\<in>#J. orda k x"
    by metis

  have "multp ordb (image_mset f I + image_mset f K) (image_mset f I + image_mset f J)"
  proof (intro one_step_implies_multp ballI)
    show "image_mset f J \<noteq> {#}"
      using J_neq_mempty by simp
  next
    fix k' assume "k'\<in>#image_mset f K"
    then obtain k where "k' = f k" and k_in: "k \<in># K"
      by auto
    then obtain j where j_in: "j\<in>#J" and "orda k j"
      using ball_K_less by auto

    have "ordb (f k) (f j)"
    proof (rule \<open>monotone_on A orda ordb f\<close>[THEN monotone_onD, OF _ _ \<open>orda k j\<close>])
      show "k \<in> A"
        using M1_eq M1_in k_in by auto
    next
      show "j \<in> A"
        using M2_eq M2_in j_in by auto
    qed
    thus "\<exists>j\<in>#image_mset f J. ordb k' j"
      using \<open>j \<in># J\<close> \<open>k' = f k\<close> by auto
  qed
  thus "multp ordb (image_mset f M1) (image_mset f M2)"
    by (simp add: M1_eq M2_eq)
qed

lemma monotone_multp_multp_image_mset:
  assumes "monotone orda ordb f" and "transp orda"
  shows "monotone (multp orda) (multp ordb) (image_mset f)"
  by (rule monotone_on_multp_multp_image_mset[OF assms, simplified])

lemma multp_image_mset_image_msetI:
  assumes "multp (\<lambda>x y. R (f x) (f y)) M1 M2" and "transp R"
  shows "multp R (image_mset f M1) (image_mset f M2)"
proof -
  from \<open>transp R\<close> have "transp (\<lambda>x y. R (f x) (f y))"
    by (auto intro: transpI dest: transpD)
  with \<open>multp (\<lambda>x y. R (f x) (f y)) M1 M2\<close> obtain I J K where
    "M2 = I + J" and "M1 = I + K" and "J \<noteq> {#}" and "\<forall>k\<in>#K. \<exists>x\<in>#J. R (f k) (f x)"
    using multp_implies_one_step by blast

  have "multp R (image_mset f I + image_mset f K) (image_mset f I + image_mset f J)"
  proof (rule one_step_implies_multp)
    show "image_mset f J \<noteq> {#}"
      by (simp add: \<open>J \<noteq> {#}\<close>)
  next
    show "\<forall>k\<in>#image_mset f K. \<exists>j\<in>#image_mset f J. R k j"
      by (simp add: \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. R (f k) (f x)\<close>)
  qed
  thus ?thesis
    by (simp add: \<open>M1 = I + K\<close> \<open>M2 = I + J\<close>)
qed

lemma multp_image_mset_image_msetD:
  assumes
    "multp R (image_mset f A) (image_mset f B)" and
    "transp R" and
    inj_on_f: "inj_on f (set_mset A \<union> set_mset B)"
  shows "multp (\<lambda>x y. R (f x) (f y)) A B"
proof -
  from assms(1,2) obtain I J K where
    f_B_eq: "image_mset f B = I + J" and
    f_A_eq: "image_mset f A = I + K" and
    J_neq_mempty: "J \<noteq> {#}" and
    ball_K_less: "\<forall>k\<in>#K. \<exists>x\<in>#J. R k x"
    by (auto dest: multp_implies_one_step)

  from f_B_eq obtain I' J' where
    B_def: "B = I' + J'" and I_def: "I = image_mset f I'" and J_def: "J = image_mset f J'"
    using image_mset_eq_plusD by blast

  from inj_on_f have inj_on_f': "inj_on f (set_mset A \<union> set_mset I')"
    by (rule inj_on_subset) (auto simp add: B_def)

  from f_A_eq obtain K' where
    A_def: "A = I' + K'" and K_def: "K = image_mset f K'"
    by (auto simp: I_def dest: image_mset_eq_image_mset_plusD[OF _ inj_on_f'])

  show ?thesis
    unfolding A_def B_def
  proof (intro one_step_implies_multp ballI)
    from J_neq_mempty show "J' \<noteq> {#}"
      by (simp add: J_def)
  next
    fix k assume "k \<in># K'"
    with ball_K_less obtain j' where "j' \<in># J" and "R (f k) j'"
      using K_def by auto
    moreover then obtain j where "j \<in># J'" and "f j = j'"
      using J_def by auto
    ultimately show "\<exists>j\<in>#J'. R (f k) (f j)"
      by blast
  qed
qed


subsubsection \<open>The multiset extension is cancellative for multiset union\<close>

lemma mult_cancel:
  assumes "trans s" and "irrefl_on (set_mset Z) s"
  shows "(X + Z, Y + Z) \<in> mult s \<longleftrightarrow> (X, Y) \<in> mult s" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R
    using \<open>irrefl_on (set_mset Z) s\<close>
  proof (induct Z)
    case (add z Z)
    obtain X' Y' Z' where *: "add_mset z X + Z = Z' + X'" "add_mset z Y + Z = Z' + Y'" "Y' \<noteq> {#}"
      "\<forall>x \<in> set_mset X'. \<exists>y \<in> set_mset Y'. (x, y) \<in> s"
      using mult_implies_one_step[OF \<open>trans s\<close> add(2)] by auto
    consider Z2 where "Z' = add_mset z Z2" | X2 Y2 where "X' = add_mset z X2" "Y' = add_mset z Y2"
      using *(1,2) by (metis add_mset_remove_trivial_If insert_iff set_mset_add_mset_insert union_iff)
    thus ?case
    proof (cases)
      case 1 thus ?thesis
        using * one_step_implies_mult[of Y' X' s Z2] add(3)
        by (auto simp: add.commute[of _ "{#_#}"] add.assoc intro: add(1) elim: irrefl_on_subset)
    next
      case 2 then obtain y where "y \<in> set_mset Y2" "(z, y) \<in> s"
        using *(4) \<open>irrefl_on (set_mset (add_mset z Z)) s\<close>
        by (auto simp: irrefl_on_def)
      moreover from this transD[OF \<open>trans s\<close> _ this(2)]
      have "x' \<in> set_mset X2 \<Longrightarrow> \<exists>y \<in> set_mset Y2. (x', y) \<in> s" for x'
        using 2 *(4)[rule_format, of x'] by auto
      ultimately show ?thesis
        using * one_step_implies_mult[of Y2 X2 s Z'] 2 add(3)
        by (force simp: add.commute[of "{#_#}"] add.assoc[symmetric] intro: add(1)
            elim: irrefl_on_subset)
    qed
  qed auto
next
  assume ?R then obtain I J K
    where "Y = I + J" "X = I + K" "J \<noteq> {#}" "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> s"
    using mult_implies_one_step[OF \<open>trans s\<close>] by blast
  thus ?L using one_step_implies_mult[of J K s "I + Z"] by (auto simp: ac_simps)
qed

lemma multp_cancel:
  "transp R \<Longrightarrow> irreflp_on (set_mset Z) R \<Longrightarrow> multp R (X + Z) (Y + Z) \<longleftrightarrow> multp R X Y"
  by (rule mult_cancel[to_pred])

lemma mult_cancel_add_mset:
  "trans r \<Longrightarrow> irrefl_on {z} r \<Longrightarrow>
    ((add_mset z X, add_mset z Y) \<in> mult r) = ((X, Y) \<in> mult r)"
  by (rule mult_cancel[of _ "{#_#}", simplified])

lemma multp_cancel_add_mset:
  "transp R \<Longrightarrow> irreflp_on {z} R \<Longrightarrow> multp R (add_mset z X) (add_mset z Y) = multp R X Y"
  by (rule mult_cancel_add_mset[to_pred, folded bot_set_def])

lemma mult_cancel_max0:
  assumes "trans s" and "irrefl_on (set_mset X \<inter> set_mset Y) s"
  shows "(X, Y) \<in> mult s \<longleftrightarrow> (X - X \<inter># Y, Y - X \<inter># Y) \<in> mult s" (is "?L \<longleftrightarrow> ?R")
proof -
  have "(X - X \<inter># Y + X \<inter># Y, Y - X \<inter># Y + X \<inter># Y) \<in> mult s \<longleftrightarrow> (X - X \<inter># Y, Y - X \<inter># Y) \<in> mult s"
  proof (rule mult_cancel)
    from assms show "trans s"
      by simp
  next
    from assms show "irrefl_on (set_mset (X \<inter># Y)) s"
      by simp
  qed
  moreover have "X - X \<inter># Y + X \<inter># Y = X" "Y - X \<inter># Y + X \<inter># Y = Y"
    by (auto simp flip: count_inject)
  ultimately show ?thesis
    by simp
qed

lemma mult_cancel_max:
  "trans r \<Longrightarrow> irrefl_on (set_mset X \<inter> set_mset Y) r \<Longrightarrow>
    (X, Y) \<in> mult r \<longleftrightarrow> (X - Y, Y - X) \<in> mult r"
  by (rule mult_cancel_max0[simplified])

lemma multp_cancel_max:
  "transp R \<Longrightarrow> irreflp_on (set_mset X \<inter> set_mset Y) R \<Longrightarrow> multp R X Y \<longleftrightarrow> multp R (X - Y) (Y - X)"
  by (rule mult_cancel_max[to_pred])


subsubsection \<open>Strict partial-order properties\<close>

lemma mult1_lessE:
  assumes "(N, M) \<in> mult1 {(a, b). r a b}" and "asymp r"
  obtains a M0 K where "M = add_mset a M0" "N = M0 + K"
    "a \<notin># K" "\<And>b. b \<in># K \<Longrightarrow> r b a"
proof -
  from assms obtain a M0 K where "M = add_mset a M0" "N = M0 + K" and
    *: "b \<in># K \<Longrightarrow> r b a" for b by (blast elim: mult1E)
  moreover from * [of a] have "a \<notin># K"
    using \<open>asymp r\<close> by (meson asympD)
  ultimately show thesis by (auto intro: that)
qed

lemma trans_on_mult:
  assumes "trans_on A r" and "\<And>M. M \<in> B \<Longrightarrow> set_mset M \<subseteq> A"
  shows "trans_on B (mult r)"
  using assms by (metis mult_def subset_UNIV trans_on_subset trans_trancl)

lemma trans_mult: "trans r \<Longrightarrow> trans (mult r)"
  using trans_on_mult[of UNIV r UNIV, simplified] .

lemma transp_on_multp:
  assumes "transp_on A r" and "\<And>M. M \<in> B \<Longrightarrow> set_mset M \<subseteq> A"
  shows "transp_on B (multp r)"
  by (metis mult_def multp_def transD trans_trancl transp_onI)

lemma transp_multp: "transp r \<Longrightarrow> transp (multp r)"
  using transp_on_multp[of UNIV r UNIV, simplified] .

lemma irrefl_mult:
  assumes "trans r" "irrefl r"
  shows "irrefl (mult r)"
proof (intro irreflI notI)
  fix M
  assume "(M, M) \<in> mult r"
  then obtain I J K where "M = I + J" and "M = I + K"
    and "J \<noteq> {#}" and "(\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset J. (k, j) \<in> r)"
    using mult_implies_one_step[OF \<open>trans r\<close>] by blast
  then have *: "K \<noteq> {#}" and **: "\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset K. (k, j) \<in> r" by auto
  have "finite (set_mset K)" by simp
  hence "set_mset K = {}"
    using **
  proof (induction rule: finite_induct)
    case empty
    thus ?case by simp
  next
    case (insert x F)
    have False
      using \<open>irrefl r\<close>[unfolded irrefl_def, rule_format]
      using \<open>trans r\<close>[THEN transD]
      by (metis equals0D insert.IH insert.prems insertE insertI1 insertI2)
    thus ?case ..
  qed
  with * show False by simp
qed

lemma irreflp_multp: "transp R \<Longrightarrow> irreflp R \<Longrightarrow> irreflp (multp R)"
  by (rule irrefl_mult[of "{(x, y). r x y}" for r,
    folded transp_trans_eq irreflp_irrefl_eq, simplified, folded multp_def])

instantiation multiset :: (preorder) order begin

definition less_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"
  where "M < N \<longleftrightarrow> multp (<) M N"

definition less_eq_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"
  where "less_eq_multiset M N \<longleftrightarrow> M < N \<or> M = N"

instance
proof intro_classes
  fix M N :: "'a multiset"
  show "(M < N) = (M \<le> N \<and> \<not> N \<le> M)"
    unfolding less_eq_multiset_def less_multiset_def
    by (metis irreflp_def irreflp_on_less irreflp_multp transpE transp_on_less transp_multp)
next
  fix M :: "'a multiset"
  show "M \<le> M"
    unfolding less_eq_multiset_def
    by simp
next
  fix M1 M2 M3 :: "'a multiset"
  show "M1 \<le> M2 \<Longrightarrow> M2 \<le> M3 \<Longrightarrow> M1 \<le> M3"
    unfolding less_eq_multiset_def less_multiset_def
    using transp_multp[OF transp_on_less, THEN transpD]
    by blast
next
  fix M N :: "'a multiset"
  show "M \<le> N \<Longrightarrow> N \<le> M \<Longrightarrow> M = N"
    unfolding less_eq_multiset_def less_multiset_def
    using transp_multp[OF transp_on_less, THEN transpD]
    using irreflp_multp[OF transp_on_less irreflp_on_less, unfolded irreflp_def, rule_format]
    by blast
qed

end

lemma mset_le_irrefl [elim!]:
  fixes M :: "'a::preorder multiset"
  shows "M < M \<Longrightarrow> R"
  by simp

lemma wfP_less_multiset[simp]:
  assumes wfP_less: "wfP ((<) :: ('a :: preorder) \<Rightarrow> 'a \<Rightarrow> bool)"
  shows "wfP ((<) :: 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool)"
  unfolding less_multiset_def
  using wfP_multp[OF wfP_less] .


subsubsection \<open>Strict total-order properties\<close>

lemma total_on_mult:
  assumes "total_on A r" and "trans r" and "\<And>M. M \<in> B \<Longrightarrow> set_mset M \<subseteq> A"
  shows "total_on B (mult r)"
proof (rule total_onI)
  fix M1 M2 assume "M1 \<in> B" and "M2 \<in> B" and "M1 \<noteq> M2"
  let ?I = "M1 \<inter># M2"
  show "(M1, M2) \<in> mult r \<or> (M2, M1) \<in> mult r"
  proof (cases "M1 - ?I = {#} \<or> M2 - ?I = {#}")
    case True
    with \<open>M1 \<noteq> M2\<close> show ?thesis
      by (metis Diff_eq_empty_iff_mset diff_intersect_left_idem diff_intersect_right_idem
          subset_implies_mult subset_mset.less_le)
  next
    case False
    from assms(1) have "total_on (set_mset (M1 - ?I)) r"
      by (meson \<open>M1 \<in> B\<close> assms(3) diff_subset_eq_self set_mset_mono total_on_subset)
    with False obtain greatest1 where
      greatest1_in: "greatest1 \<in># M1 - ?I" and
      greatest1_greatest: "\<forall>x \<in># M1 - ?I. greatest1 \<noteq> x \<longrightarrow> (x, greatest1) \<in> r"
      using Multiset.bex_greatest_element[to_set, of "M1 - ?I" r]
      by (metis assms(2) subset_UNIV trans_on_subset)

    from assms(1) have "total_on (set_mset (M2 - ?I)) r"
      by (meson \<open>M2 \<in> B\<close> assms(3) diff_subset_eq_self set_mset_mono total_on_subset)
    with False obtain greatest2 where
      greatest2_in: "greatest2 \<in># M2 - ?I" and
      greatest2_greatest: "\<forall>x \<in># M2 - ?I. greatest2 \<noteq> x \<longrightarrow> (x, greatest2) \<in> r"
      using Multiset.bex_greatest_element[to_set, of "M2 - ?I" r]
      by (metis assms(2) subset_UNIV trans_on_subset)

    have "greatest1 \<noteq> greatest2"
      using greatest1_in \<open>greatest2 \<in># M2 - ?I\<close>
      by (metis diff_intersect_left_idem diff_intersect_right_idem dual_order.eq_iff in_diff_count
          in_diff_countE le_add_same_cancel2 less_irrefl zero_le)
    hence "(greatest1, greatest2) \<in> r \<or> (greatest2, greatest1) \<in> r"
      using \<open>total_on A r\<close>[unfolded total_on_def, rule_format, of greatest1 greatest2]
        \<open>M1 \<in> B\<close> \<open>M2 \<in> B\<close> greatest1_in greatest2_in assms(3)
      by (meson in_diffD in_mono)
    thus ?thesis
    proof (elim disjE)
      assume "(greatest1, greatest2) \<in> r"
      have "(?I + (M1 - ?I), ?I + (M2 - ?I)) \<in> mult r"
      proof (rule one_step_implies_mult[of "M2 - ?I" "M1 - ?I" r ?I])
        show "M2 - ?I \<noteq> {#}"
          using False by force
      next
        show "\<forall>k\<in>#M1 - ?I. \<exists>j\<in>#M2 - ?I. (k, j) \<in> r"
          using \<open>(greatest1, greatest2) \<in> r\<close> greatest2_in greatest1_greatest
          by (metis assms(2) transD)
      qed
      hence "(M1, M2) \<in> mult r"
        by (metis subset_mset.add_diff_inverse subset_mset.inf.cobounded1
            subset_mset.inf.cobounded2)
      thus "(M1, M2) \<in> mult r \<or> (M2, M1) \<in> mult r" ..
    next
      assume "(greatest2, greatest1) \<in> r"
      have "(?I + (M2 - ?I), ?I + (M1 - ?I)) \<in> mult r"
      proof (rule one_step_implies_mult[of "M1 - ?I" "M2 - ?I" r ?I])
        show "M1 - M1 \<inter># M2 \<noteq> {#}"
          using False by force
      next
        show "\<forall>k\<in>#M2 - ?I. \<exists>j\<in>#M1 - ?I. (k, j) \<in> r"
          using \<open>(greatest2, greatest1) \<in> r\<close> greatest1_in greatest2_greatest
          by (metis assms(2) transD)
      qed
      hence "(M2, M1) \<in> mult r"
        by (metis subset_mset.add_diff_inverse subset_mset.inf.cobounded1
            subset_mset.inf.cobounded2)
      thus "(M1, M2) \<in> mult r \<or> (M2, M1) \<in> mult r" ..
    qed
  qed
qed

lemma total_mult: "total r \<Longrightarrow> trans r \<Longrightarrow> total (mult r)"
  by (rule total_on_mult[of UNIV r UNIV, simplified])

lemma totalp_on_multp:
  "totalp_on A R \<Longrightarrow> transp R \<Longrightarrow> (\<And>M. M \<in> B \<Longrightarrow> set_mset M \<subseteq> A) \<Longrightarrow> totalp_on B (multp R)"
  using total_on_mult[of A "{(x,y). R x y}" B, to_pred]
  by (simp add: multp_def total_on_def totalp_on_def)

lemma totalp_multp: "totalp R \<Longrightarrow> transp R \<Longrightarrow> totalp (multp R)"
  by (rule totalp_on_multp[of UNIV R UNIV, simplified])


subsection \<open>Quasi-executable version of the multiset extension\<close>

text \<open>
  Predicate variants of \<open>mult\<close> and the reflexive closure of \<open>mult\<close>, which are
  executable whenever the given predicate \<open>P\<close> is. Together with the standard
  code equations for \<open>(\<inter>#\<close>) and \<open>(-\<close>) this should yield quadratic
  (with respect to calls to \<open>P\<close>) implementations of \<open>multp_code\<close> and \<open>multeqp_code\<close>.
\<close>

definition multp_code :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "multp_code P N M =
    (let Z = M \<inter># N; X = M - Z in
    X \<noteq> {#} \<and> (let Y = N - Z in (\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. P y x)))"

definition multeqp_code :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "multeqp_code P N M =
    (let Z = M \<inter># N; X = M - Z; Y = N - Z in
    (\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. P y x))"

lemma multp_code_iff_mult:
  assumes "irrefl_on (set_mset N \<inter> set_mset M) R" and "trans R" and
    [simp]: "\<And>x y. P x y \<longleftrightarrow> (x, y) \<in> R"
  shows "multp_code P N M \<longleftrightarrow> (N, M) \<in> mult R" (is "?L \<longleftrightarrow> ?R")
proof -
  have *: "M \<inter># N + (N - M \<inter># N) = N" "M \<inter># N + (M - M \<inter># N) = M"
    "(M - M \<inter># N) \<inter># (N - M \<inter># N) = {#}" by (auto simp flip: count_inject)
  show ?thesis
  proof
    assume ?L thus ?R
      using one_step_implies_mult[of "M - M \<inter># N" "N - M \<inter># N" R "M \<inter># N"] *
      by (auto simp: multp_code_def Let_def)
  next
    { fix I J K :: "'a multiset" assume "(I + J) \<inter># (I + K) = {#}"
      then have "I = {#}" by (metis inter_union_distrib_right union_eq_empty)
    } note [dest!] = this
    assume ?R thus ?L
      using mult_cancel_max
      using mult_implies_one_step[OF assms(2), of "N - M \<inter># N" "M - M \<inter># N"]
        mult_cancel_max[OF assms(2,1)] * by (auto simp: multp_code_def)
  qed
qed

lemma multp_code_iff_multp:
  "irreflp_on (set_mset M \<inter> set_mset N) R \<Longrightarrow> transp R \<Longrightarrow> multp_code R M N \<longleftrightarrow> multp R M N"
  using multp_code_iff_mult[simplified, to_pred, of M N R R] by simp

lemma multp_code_eq_multp:
  assumes "irreflp R" and "transp R"
  shows "multp_code R = multp R"
proof (intro ext)
  fix M N
  show "multp_code R M N = multp R M N"
  proof (rule multp_code_iff_multp)
    from assms show "irreflp_on (set_mset M \<inter> set_mset N) R"
      by (auto intro: irreflp_on_subset)
  next
    from assms show "transp R"
      by simp
  qed
qed

lemma multeqp_code_iff_reflcl_mult:
  assumes "irrefl_on (set_mset N \<inter> set_mset M) R" and "trans R" and "\<And>x y. P x y \<longleftrightarrow> (x, y) \<in> R"
  shows "multeqp_code P N M \<longleftrightarrow> (N, M) \<in> (mult R)\<^sup>="
proof -
  { assume "N \<noteq> M" "M - M \<inter># N = {#}"
    then obtain y where "count N y \<noteq> count M y" by (auto simp flip: count_inject)
    then have "\<exists>y. count M y < count N y" using \<open>M - M \<inter># N = {#}\<close>
      by (auto simp flip: count_inject dest!: le_neq_implies_less fun_cong[of _ _ y])
  }
  then have "multeqp_code P N M \<longleftrightarrow> multp_code P N M \<or> N = M"
    by (auto simp: multeqp_code_def multp_code_def Let_def in_diff_count)
  thus ?thesis
    using multp_code_iff_mult[OF assms] by simp
qed

lemma multeqp_code_iff_reflclp_multp:
  "irreflp_on (set_mset M \<inter> set_mset N) R \<Longrightarrow> transp R \<Longrightarrow> multeqp_code R M N \<longleftrightarrow> (multp R)\<^sup>=\<^sup>= M N"
  using multeqp_code_iff_reflcl_mult[simplified, to_pred, of M N R R] by simp

lemma multeqp_code_eq_reflclp_multp:
  assumes "irreflp R" and "transp R"
  shows "multeqp_code R = (multp R)\<^sup>=\<^sup>="
proof (intro ext)
  fix M N
  show "multeqp_code R M N \<longleftrightarrow> (multp R)\<^sup>=\<^sup>= M N"
  proof (rule multeqp_code_iff_reflclp_multp)
    from assms show "irreflp_on (set_mset M \<inter> set_mset N) R"
      by (auto intro: irreflp_on_subset)
  next
    from assms show "transp R"
      by simp
  qed
qed


subsubsection \<open>Monotonicity of multiset union\<close>

lemma mult1_union: "(B, D) \<in> mult1 r \<Longrightarrow> (C + B, C + D) \<in> mult1 r"
  by (force simp: mult1_def)

lemma union_le_mono2: "B < D \<Longrightarrow> C + B < C + (D::'a::preorder multiset)"
  unfolding less_multiset_def multp_def mult_def
  by (induction rule: trancl_induct; blast intro: mult1_union trancl_trans)

lemma union_le_mono1: "B < D \<Longrightarrow> B + C < D + (C::'a::preorder multiset)"
  by (metis add.commute union_le_mono2)

lemma union_less_mono:
  fixes A B C D :: "'a::preorder multiset"
  shows "A < C \<Longrightarrow> B < D \<Longrightarrow> A + B < C + D"
  by (blast intro!: union_le_mono1 union_le_mono2 less_trans)

instantiation multiset :: (preorder) ordered_ab_semigroup_add
begin
instance
  by standard (auto simp add: less_eq_multiset_def intro: union_le_mono2)
end


subsubsection \<open>Termination proofs with multiset orders\<close>

lemma multi_member_skip: "x \<in># XS \<Longrightarrow> x \<in># {# y #} + XS"
  and multi_member_this: "x \<in># {# x #} + XS"
  and multi_member_last: "x \<in># {# x #}"
  by auto

definition "ms_strict = mult pair_less"
definition "ms_weak = ms_strict \<union> Id"

lemma ms_reduction_pair: "reduction_pair (ms_strict, ms_weak)"
  unfolding reduction_pair_def ms_strict_def ms_weak_def pair_less_def
  by (auto intro: wf_mult1 wf_trancl simp: mult_def)

lemma smsI:
  "(set_mset A, set_mset B) \<in> max_strict \<Longrightarrow> (Z + A, Z + B) \<in> ms_strict"
  unfolding ms_strict_def
by (rule one_step_implies_mult) (auto simp add: max_strict_def pair_less_def elim!:max_ext.cases)

lemma wmsI:
  "(set_mset A, set_mset B) \<in> max_strict \<or> A = {#} \<and> B = {#}
  \<Longrightarrow> (Z + A, Z + B) \<in> ms_weak"
unfolding ms_weak_def ms_strict_def
by (auto simp add: pair_less_def max_strict_def elim!:max_ext.cases intro: one_step_implies_mult)

inductive pw_leq
where
  pw_leq_empty: "pw_leq {#} {#}"
| pw_leq_step:  "\<lbrakk>(x,y) \<in> pair_leq; pw_leq X Y \<rbrakk> \<Longrightarrow> pw_leq ({#x#} + X) ({#y#} + Y)"

lemma pw_leq_lstep:
  "(x, y) \<in> pair_leq \<Longrightarrow> pw_leq {#x#} {#y#}"
by (drule pw_leq_step) (rule pw_leq_empty, simp)

lemma pw_leq_split:
  assumes "pw_leq X Y"
  shows "\<exists>A B Z. X = A + Z \<and> Y = B + Z \<and> ((set_mset A, set_mset B) \<in> max_strict \<or> (B = {#} \<and> A = {#}))"
  using assms
proof induct
  case pw_leq_empty thus ?case by auto
next
  case (pw_leq_step x y X Y)
  then obtain A B Z where
    [simp]: "X = A + Z" "Y = B + Z"
      and 1[simp]: "(set_mset A, set_mset B) \<in> max_strict \<or> (B = {#} \<and> A = {#})"
    by auto
  from pw_leq_step consider "x = y" | "(x, y) \<in> pair_less"
    unfolding pair_leq_def by auto
  thus ?case
  proof cases
    case [simp]: 1
    have "{#x#} + X = A + ({#y#}+Z) \<and> {#y#} + Y = B + ({#y#}+Z) \<and>
      ((set_mset A, set_mset B) \<in> max_strict \<or> (B = {#} \<and> A = {#}))"
      by auto
    thus ?thesis by blast
  next
    case 2
    let ?A' = "{#x#} + A" and ?B' = "{#y#} + B"
    have "{#x#} + X = ?A' + Z"
      "{#y#} + Y = ?B' + Z"
      by auto
    moreover have
      "(set_mset ?A', set_mset ?B') \<in> max_strict"
      using 1 2 unfolding max_strict_def
      by (auto elim!: max_ext.cases)
    ultimately show ?thesis by blast
  qed
qed

lemma
  assumes pwleq: "pw_leq Z Z'"
  shows ms_strictI: "(set_mset A, set_mset B) \<in> max_strict \<Longrightarrow> (Z + A, Z' + B) \<in> ms_strict"
    and ms_weakI1:  "(set_mset A, set_mset B) \<in> max_strict \<Longrightarrow> (Z + A, Z' + B) \<in> ms_weak"
    and ms_weakI2:  "(Z + {#}, Z' + {#}) \<in> ms_weak"
proof -
  from pw_leq_split[OF pwleq]
  obtain A' B' Z''
    where [simp]: "Z = A' + Z''" "Z' = B' + Z''"
    and mx_or_empty: "(set_mset A', set_mset B') \<in> max_strict \<or> (A' = {#} \<and> B' = {#})"
    by blast
  {
    assume max: "(set_mset A, set_mset B) \<in> max_strict"
    from mx_or_empty
    have "(Z'' + (A + A'), Z'' + (B + B')) \<in> ms_strict"
    proof
      assume max': "(set_mset A', set_mset B') \<in> max_strict"
      with max have "(set_mset (A + A'), set_mset (B + B')) \<in> max_strict"
        by (auto simp: max_strict_def intro: max_ext_additive)
      thus ?thesis by (rule smsI)
    next
      assume [simp]: "A' = {#} \<and> B' = {#}"
      show ?thesis by (rule smsI) (auto intro: max)
    qed
    thus "(Z + A, Z' + B) \<in> ms_strict" by (simp add: ac_simps)
    thus "(Z + A, Z' + B) \<in> ms_weak" by (simp add: ms_weak_def)
  }
  from mx_or_empty
  have "(Z'' + A', Z'' + B') \<in> ms_weak" by (rule wmsI)
  thus "(Z + {#}, Z' + {#}) \<in> ms_weak" by (simp add: ac_simps)
qed

lemma empty_neutral: "{#} + x = x" "x + {#} = x"
and nonempty_plus: "{# x #} + rs \<noteq> {#}"
and nonempty_single: "{# x #} \<noteq> {#}"
by auto

setup \<open>
  let
    fun msetT T = \<^Type>\<open>multiset T\<close>;

    fun mk_mset T [] = \<^instantiate>\<open>'a = T in term \<open>{#}\<close>\<close>
      | mk_mset T [x] = \<^instantiate>\<open>'a = T and x in term \<open>{#x#}\<close>\<close>
      | mk_mset T (x :: xs) = \<^Const>\<open>plus \<open>msetT T\<close> for \<open>mk_mset T [x]\<close> \<open>mk_mset T xs\<close>\<close>

    fun mset_member_tac ctxt m i =
      if m <= 0 then
        resolve_tac ctxt @{thms multi_member_this} i ORELSE
        resolve_tac ctxt @{thms multi_member_last} i
      else
        resolve_tac ctxt @{thms multi_member_skip} i THEN mset_member_tac ctxt (m - 1) i

    fun mset_nonempty_tac ctxt =
      resolve_tac ctxt @{thms nonempty_plus} ORELSE'
      resolve_tac ctxt @{thms nonempty_single}

    fun regroup_munion_conv ctxt =
      Function_Lib.regroup_conv ctxt \<^const_abbrev>\<open>empty_mset\<close> \<^const_name>\<open>plus\<close>
        (map (fn t => t RS eq_reflection) (@{thms ac_simps} @ @{thms empty_neutral}))

    fun unfold_pwleq_tac ctxt i =
      (resolve_tac ctxt @{thms pw_leq_step} i THEN (fn st => unfold_pwleq_tac ctxt (i + 1) st))
        ORELSE (resolve_tac ctxt @{thms pw_leq_lstep} i)
        ORELSE (resolve_tac ctxt @{thms pw_leq_empty} i)

    val set_mset_simps = [@{thm set_mset_empty}, @{thm set_mset_single}, @{thm set_mset_union},
                        @{thm Un_insert_left}, @{thm Un_empty_left}]
  in
    ScnpReconstruct.multiset_setup (ScnpReconstruct.Multiset
    {
      msetT=msetT, mk_mset=mk_mset, mset_regroup_conv=regroup_munion_conv,
      mset_member_tac=mset_member_tac, mset_nonempty_tac=mset_nonempty_tac,
      mset_pwleq_tac=unfold_pwleq_tac, set_of_simps=set_mset_simps,
      smsI'= @{thm ms_strictI}, wmsI2''= @{thm ms_weakI2}, wmsI1= @{thm ms_weakI1},
      reduction_pair = @{thm ms_reduction_pair}
    })
  end
\<close>


subsection \<open>Legacy theorem bindings\<close>

lemmas multi_count_eq = multiset_eq_iff [symmetric]

lemma union_commute: "M + N = N + (M::'a multiset)"
  by (fact add.commute)

lemma union_assoc: "(M + N) + K = M + (N + (K::'a multiset))"
  by (fact add.assoc)

lemma union_lcomm: "M + (N + K) = N + (M + (K::'a multiset))"
  by (fact add.left_commute)

lemmas union_ac = union_assoc union_commute union_lcomm add_mset_commute

lemma union_right_cancel: "M + K = N + K \<longleftrightarrow> M = (N::'a multiset)"
  by (fact add_right_cancel)

lemma union_left_cancel: "K + M = K + N \<longleftrightarrow> M = (N::'a multiset)"
  by (fact add_left_cancel)

lemma multi_union_self_other_eq: "(A::'a multiset) + X = A + Y \<Longrightarrow> X = Y"
  by (fact add_left_imp_eq)

lemma mset_subset_trans: "(M::'a multiset) \<subset># K \<Longrightarrow> K \<subset># N \<Longrightarrow> M \<subset># N"
  by (fact subset_mset.less_trans)

lemma multiset_inter_commute: "A \<inter># B = B \<inter># A"
  by (fact subset_mset.inf.commute)

lemma multiset_inter_assoc: "A \<inter># (B \<inter># C) = A \<inter># B \<inter># C"
  by (fact subset_mset.inf.assoc [symmetric])

lemma multiset_inter_left_commute: "A \<inter># (B \<inter># C) = B \<inter># (A \<inter># C)"
  by (fact subset_mset.inf.left_commute)

lemmas multiset_inter_ac =
  multiset_inter_commute
  multiset_inter_assoc
  multiset_inter_left_commute

lemma mset_le_not_refl: "\<not> M < (M::'a::preorder multiset)"
  by (fact less_irrefl)

lemma mset_le_trans: "K < M \<Longrightarrow> M < N \<Longrightarrow> K < (N::'a::preorder multiset)"
  by (fact less_trans)

lemma mset_le_not_sym: "M < N \<Longrightarrow> \<not> N < (M::'a::preorder multiset)"
  by (fact less_not_sym)

lemma mset_le_asym: "M < N \<Longrightarrow> (\<not> P \<Longrightarrow> N < (M::'a::preorder multiset)) \<Longrightarrow> P"
  by (fact less_asym)

declaration \<open>
  let
    fun multiset_postproc _ maybe_name all_values (T as Type (_, [elem_T])) (Const _ $ t') =
          let
            val (maybe_opt, ps) =
              Nitpick_Model.dest_plain_fun t'
              ||> (~~)
              ||> map (apsnd (snd o HOLogic.dest_number))
            fun elems_for t =
              (case AList.lookup (=) ps t of
                SOME n => replicate n t
              | NONE => [Const (maybe_name, elem_T --> elem_T) $ t])
          in
            (case maps elems_for (all_values elem_T) @
                 (if maybe_opt then [Const (Nitpick_Model.unrep_mixfix (), elem_T)] else []) of
              [] => \<^Const>\<open>Groups.zero T\<close>
            | ts => foldl1 (fn (s, t) => \<^Const>\<open>add_mset elem_T for s t\<close>) ts)
          end
      | multiset_postproc _ _ _ _ t = t
  in Nitpick_Model.register_term_postprocessor \<^typ>\<open>'a multiset\<close> multiset_postproc end
\<close>


subsection \<open>Naive implementation using lists\<close>

code_datatype mset

lemma [code]: "{#} = mset []"
  by simp

lemma [code]: "add_mset x (mset xs) = mset (x # xs)"
  by simp

lemma [code]: "Multiset.is_empty (mset xs) \<longleftrightarrow> List.null xs"
  by (simp add: Multiset.is_empty_def List.null_def)

lemma union_code [code]: "mset xs + mset ys = mset (xs @ ys)"
  by simp

lemma [code]: "image_mset f (mset xs) = mset (map f xs)"
  by simp

lemma [code]: "filter_mset f (mset xs) = mset (filter f xs)"
  by simp

lemma [code]: "mset xs - mset ys = mset (fold remove1 ys xs)"
  by (rule sym, induct ys arbitrary: xs) (simp_all add: diff_add diff_right_commute diff_diff_add)

lemma [code]:
  "mset xs \<inter># mset ys =
    mset (snd (fold (\<lambda>x (ys, zs).
      if x \<in> set ys then (remove1 x ys, x # zs) else (ys, zs)) xs (ys, [])))"
proof -
  have "\<And>zs. mset (snd (fold (\<lambda>x (ys, zs).
    if x \<in> set ys then (remove1 x ys, x # zs) else (ys, zs)) xs (ys, zs))) =
      (mset xs \<inter># mset ys) + mset zs"
    by (induct xs arbitrary: ys)
      (auto simp add: inter_add_right1 inter_add_right2 ac_simps)
  then show ?thesis by simp
qed

lemma [code]:
  "mset xs \<union># mset ys =
    mset (case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, [])))"
proof -
  have "\<And>zs. mset (case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, zs))) =
      (mset xs \<union># mset ys) + mset zs"
    by (induct xs arbitrary: ys) (simp_all add: multiset_eq_iff)
  then show ?thesis by simp
qed

declare in_multiset_in_set [code_unfold]

lemma [code]: "count (mset xs) x = fold (\<lambda>y. if x = y then Suc else id) xs 0"
proof -
  have "\<And>n. fold (\<lambda>y. if x = y then Suc else id) xs n = count (mset xs) x + n"
    by (induct xs) simp_all
  then show ?thesis by simp
qed

declare set_mset_mset [code]

declare sorted_list_of_multiset_mset [code]

lemma [code]: \<comment> \<open>not very efficient, but representation-ignorant!\<close>
  "mset_set A = mset (sorted_list_of_set A)"
  by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set)

declare size_mset [code]

fun subset_eq_mset_impl :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool option" where
  "subset_eq_mset_impl [] ys = Some (ys \<noteq> [])"
| "subset_eq_mset_impl (Cons x xs) ys = (case List.extract ((=) x) ys of
     None \<Rightarrow> None
   | Some (ys1,_,ys2) \<Rightarrow> subset_eq_mset_impl xs (ys1 @ ys2))"

lemma subset_eq_mset_impl: "(subset_eq_mset_impl xs ys = None \<longleftrightarrow> \<not> mset xs \<subseteq># mset ys) \<and>
  (subset_eq_mset_impl xs ys = Some True \<longleftrightarrow> mset xs \<subset># mset ys) \<and>
  (subset_eq_mset_impl xs ys = Some False \<longrightarrow> mset xs = mset ys)"
proof (induct xs arbitrary: ys)
  case (Nil ys)
  show ?case by (auto simp: subset_mset.zero_less_iff_neq_zero)
next
  case (Cons x xs ys)
  show ?case
  proof (cases "List.extract ((=) x) ys")
    case None
    hence x: "x \<notin> set ys" by (simp add: extract_None_iff)
    {
      assume "mset (x # xs) \<subseteq># mset ys"
      from set_mset_mono[OF this] x have False by simp
    } note nle = this
    moreover
    {
      assume "mset (x # xs) \<subset># mset ys"
      hence "mset (x # xs) \<subseteq># mset ys" by auto
      from nle[OF this] have False .
    }
    ultimately show ?thesis using None by auto
  next
    case (Some res)
    obtain ys1 y ys2 where res: "res = (ys1,y,ys2)" by (cases res, auto)
    note Some = Some[unfolded res]
    from extract_SomeE[OF Some] have "ys = ys1 @ x # ys2" by simp
    hence id: "mset ys = add_mset x (mset (ys1 @ ys2))"
      by auto
    show ?thesis unfolding subset_eq_mset_impl.simps
      by (simp add: Some id Cons)
  qed
qed

lemma [code]: "mset xs \<subseteq># mset ys \<longleftrightarrow> subset_eq_mset_impl xs ys \<noteq> None"
  by (simp add: subset_eq_mset_impl)

lemma [code]: "mset xs \<subset># mset ys \<longleftrightarrow> subset_eq_mset_impl xs ys = Some True"
  using subset_eq_mset_impl by blast

instantiation multiset :: (equal) equal
begin

definition
  [code del]: "HOL.equal A (B :: 'a multiset) \<longleftrightarrow> A = B"
lemma [code]: "HOL.equal (mset xs) (mset ys) \<longleftrightarrow> subset_eq_mset_impl xs ys = Some False"
  unfolding equal_multiset_def
  using subset_eq_mset_impl[of xs ys] by (cases "subset_eq_mset_impl xs ys", auto)

instance
  by standard (simp add: equal_multiset_def)

end

declare sum_mset_sum_list [code]

lemma [code]: "prod_mset (mset xs) = fold times xs 1"
proof -
  have "\<And>x. fold times xs x = prod_mset (mset xs) * x"
    by (induct xs) (simp_all add: ac_simps)
  then show ?thesis by simp
qed

text \<open>
  Exercise for the casual reader: add implementations for \<^term>\<open>(\<le>)\<close>
  and \<^term>\<open>(<)\<close> (multiset order).
\<close>

text \<open>Quickcheck generators\<close>

context
  includes term_syntax
begin

definition
  msetify :: "'a::typerep list \<times> (unit \<Rightarrow> Code_Evaluation.term)
    \<Rightarrow> 'a multiset \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "msetify xs = Code_Evaluation.valtermify mset {\<cdot>} xs"

end

instantiation multiset :: (random) random
begin

context
  includes state_combinator_syntax
begin

definition
  "Quickcheck_Random.random i = Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>xs. Pair (msetify xs))"

instance ..

end

end

instantiation multiset :: (full_exhaustive) full_exhaustive
begin

definition full_exhaustive_multiset :: "('a multiset \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "full_exhaustive_multiset f i = Quickcheck_Exhaustive.full_exhaustive (\<lambda>xs. f (msetify xs)) i"

instance ..

end

hide_const (open) msetify


subsection \<open>BNF setup\<close>

definition rel_mset where
  "rel_mset R X Y \<longleftrightarrow> (\<exists>xs ys. mset xs = X \<and> mset ys = Y \<and> list_all2 R xs ys)"

lemma mset_zip_take_Cons_drop_twice:
  assumes "length xs = length ys" "j \<le> length xs"
  shows "mset (zip (take j xs @ x # drop j xs) (take j ys @ y # drop j ys)) =
    add_mset (x,y) (mset (zip xs ys))"
  using assms
proof (induct xs ys arbitrary: x y j rule: list_induct2)
  case Nil
  thus ?case
    by simp
next
  case (Cons x xs y ys)
  thus ?case
  proof (cases "j = 0")
    case True
    thus ?thesis
      by simp
  next
    case False
    then obtain k where k: "j = Suc k"
      by (cases j) simp
    hence "k \<le> length xs"
      using Cons.prems by auto
    hence "mset (zip (take k xs @ x # drop k xs) (take k ys @ y # drop k ys)) =
      add_mset (x,y) (mset (zip xs ys))"
      by (rule Cons.hyps(2))
    thus ?thesis
      unfolding k by auto
  qed
qed

lemma ex_mset_zip_left:
  assumes "length xs = length ys" "mset xs' = mset xs"
  shows "\<exists>ys'. length ys' = length xs' \<and> mset (zip xs' ys') = mset (zip xs ys)"
using assms
proof (induct xs ys arbitrary: xs' rule: list_induct2)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs y ys xs')
  obtain j where j_len: "j < length xs'" and nth_j: "xs' ! j = x"
    by (metis Cons.prems in_set_conv_nth list.set_intros(1) mset_eq_setD)

  define xsa where "xsa = take j xs' @ drop (Suc j) xs'"
  have "mset xs' = {#x#} + mset xsa"
    unfolding xsa_def using j_len nth_j
    by (metis Cons_nth_drop_Suc union_mset_add_mset_right add_mset_remove_trivial add_diff_cancel_left'
        append_take_drop_id mset.simps(2) mset_append)
  hence ms_x: "mset xsa = mset xs"
    by (simp add: Cons.prems)
  then obtain ysa where
    len_a: "length ysa = length xsa" and ms_a: "mset (zip xsa ysa) = mset (zip xs ys)"
    using Cons.hyps(2) by blast

  define ys' where "ys' = take j ysa @ y # drop j ysa"
  have xs': "xs' = take j xsa @ x # drop j xsa"
    using ms_x j_len nth_j Cons.prems xsa_def
    by (metis append_eq_append_conv append_take_drop_id diff_Suc_Suc Cons_nth_drop_Suc length_Cons
      length_drop size_mset)
  have j_len': "j \<le> length xsa"
    using j_len xs' xsa_def
    by (metis add_Suc_right append_take_drop_id length_Cons length_append less_eq_Suc_le not_less)
  have "length ys' = length xs'"
    unfolding ys'_def using Cons.prems len_a ms_x
    by (metis add_Suc_right append_take_drop_id length_Cons length_append mset_eq_length)
  moreover have "mset (zip xs' ys') = mset (zip (x # xs) (y # ys))"
    unfolding xs' ys'_def
    by (rule trans[OF mset_zip_take_Cons_drop_twice])
      (auto simp: len_a ms_a j_len')
  ultimately show ?case
    by blast
qed

lemma list_all2_reorder_left_invariance:
  assumes rel: "list_all2 R xs ys" and ms_x: "mset xs' = mset xs"
  shows "\<exists>ys'. list_all2 R xs' ys' \<and> mset ys' = mset ys"
proof -
  have len: "length xs = length ys"
    using rel list_all2_conv_all_nth by auto
  obtain ys' where
    len': "length xs' = length ys'" and ms_xy: "mset (zip xs' ys') = mset (zip xs ys)"
    using len ms_x by (metis ex_mset_zip_left)
  have "list_all2 R xs' ys'"
    using assms(1) len' ms_xy unfolding list_all2_iff by (blast dest: mset_eq_setD)
  moreover have "mset ys' = mset ys"
    using len len' ms_xy map_snd_zip mset_map by metis
  ultimately show ?thesis
    by blast
qed

lemma ex_mset: "\<exists>xs. mset xs = X"
  by (induct X) (simp, metis mset.simps(2))

inductive pred_mset :: "('a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> bool" 
where
  "pred_mset P {#}"
| "\<lbrakk>P a; pred_mset P M\<rbrakk> \<Longrightarrow> pred_mset P (add_mset a M)"

lemma pred_mset_iff: \<comment> \<open>TODO: alias for \<^const>\<open>Multiset.Ball\<close>\<close>
  \<open>pred_mset P M \<longleftrightarrow> Multiset.Ball M P\<close>  (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?P
  then show ?Q by induction simp_all
next
  assume ?Q
  then show ?P
    by (induction M) (auto intro: pred_mset.intros)
qed

bnf "'a multiset"
  map: image_mset
  sets: set_mset
  bd: natLeq
  wits: "{#}"
  rel: rel_mset
  pred: pred_mset
proof -
  show "image_mset (g \<circ> f) = image_mset g \<circ> image_mset f" for f g
    unfolding comp_def by (rule ext) (simp add: comp_def image_mset.compositionality)
  show "(\<And>z. z \<in> set_mset X \<Longrightarrow> f z = g z) \<Longrightarrow> image_mset f X = image_mset g X" for f g X
    by (induct X) simp_all
  show "card_order natLeq"
    by (rule natLeq_card_order)
  show "BNF_Cardinal_Arithmetic.cinfinite natLeq"
    by (rule natLeq_cinfinite)
  show "regularCard natLeq"
    by (rule regularCard_natLeq)
  show "ordLess2 (card_of (set_mset X)) natLeq" for X
    by transfer
      (auto simp: finite_iff_ordLess_natLeq[symmetric])
  show "rel_mset R OO rel_mset S \<le> rel_mset (R OO S)" for R S
    unfolding rel_mset_def[abs_def] OO_def
    by (smt (verit, ccfv_SIG) list_all2_reorder_left_invariance list_all2_trans predicate2I)
  show "rel_mset R =
    (\<lambda>x y. \<exists>z. set_mset z \<subseteq> {(x, y). R x y} \<and>
    image_mset fst z = x \<and> image_mset snd z = y)" for R
    unfolding rel_mset_def[abs_def]
    by (metis (no_types, lifting) ex_mset list.in_rel mem_Collect_eq mset_map set_mset_mset)
  show "pred_mset P = (\<lambda>x. Ball (set_mset x) P)" for P
    by (simp add: fun_eq_iff pred_mset_iff)
qed auto

inductive rel_mset' :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset \<Rightarrow> bool\<close>
where
  Zero[intro]: "rel_mset' R {#} {#}"
| Plus[intro]: "\<lbrakk>R a b; rel_mset' R M N\<rbrakk> \<Longrightarrow> rel_mset' R (add_mset a M) (add_mset b N)"

lemma rel_mset_Zero: "rel_mset R {#} {#}"
unfolding rel_mset_def Grp_def by auto

declare multiset.count[simp]
declare count_Abs_multiset[simp]
declare multiset.count_inverse[simp]

lemma rel_mset_Plus:
  assumes ab: "R a b"
    and MN: "rel_mset R M N"
  shows "rel_mset R (add_mset a M) (add_mset b N)"
proof -
  have "\<exists>ya. add_mset a (image_mset fst y) = image_mset fst ya \<and>
    add_mset b (image_mset snd y) = image_mset snd ya \<and>
    set_mset ya \<subseteq> {(x, y). R x y}"
    if "R a b" and "set_mset y \<subseteq> {(x, y). R x y}" for y
    using that by (intro exI[of _ "add_mset (a,b) y"]) auto
  thus ?thesis
  using assms
  unfolding multiset.rel_compp_Grp Grp_def by blast
qed

lemma rel_mset'_imp_rel_mset: "rel_mset' R M N \<Longrightarrow> rel_mset R M N"
  by (induct rule: rel_mset'.induct) (auto simp: rel_mset_Zero rel_mset_Plus)

lemma rel_mset_size: "rel_mset R M N \<Longrightarrow> size M = size N"
  unfolding multiset.rel_compp_Grp Grp_def by auto

lemma rel_mset_Zero_iff [simp]:
  shows "rel_mset rel {#} Y \<longleftrightarrow> Y = {#}" and "rel_mset rel X {#} \<longleftrightarrow> X = {#}"
  by (auto simp add: rel_mset_Zero dest: rel_mset_size)

lemma multiset_induct2[case_names empty addL addR]:
  assumes empty: "P {#} {#}"
    and addL: "\<And>a M N. P M N \<Longrightarrow> P (add_mset a M) N"
    and addR: "\<And>a M N. P M N \<Longrightarrow> P M (add_mset a N)"
  shows "P M N"
  by (induct N rule: multiset_induct; induct M rule: multiset_induct) (auto simp: assms)

lemma multiset_induct2_size[consumes 1, case_names empty add]:
  assumes c: "size M = size N"
    and empty: "P {#} {#}"
    and add: "\<And>a b M N a b. P M N \<Longrightarrow> P (add_mset a M) (add_mset b N)"
  shows "P M N"
  using c
proof (induct M arbitrary: N rule: measure_induct_rule[of size])
  case (less M)
  show ?case
  proof(cases "M = {#}")
    case True hence "N = {#}" using less.prems by auto
    thus ?thesis using True empty by auto
  next
    case False then obtain M1 a where M: "M = add_mset a M1" by (metis multi_nonempty_split)
    have "N \<noteq> {#}" using False less.prems by auto
    then obtain N1 b where N: "N = add_mset b N1" by (metis multi_nonempty_split)
    have "size M1 = size N1" using less.prems unfolding M N by auto
    thus ?thesis using M N less.hyps add by auto
  qed
qed

lemma msed_map_invL:
  assumes "image_mset f (add_mset a M) = N"
  shows "\<exists>N1. N = add_mset (f a) N1 \<and> image_mset f M = N1"
proof -
  have "f a \<in># N"
    using assms multiset.set_map[of f "add_mset a M"] by auto
  then obtain N1 where N: "N = add_mset (f a) N1" using multi_member_split by metis
  have "image_mset f M = N1" using assms unfolding N by simp
  thus ?thesis using N by blast
qed

lemma msed_map_invR:
  assumes "image_mset f M = add_mset b N"
  shows "\<exists>M1 a. M = add_mset a M1 \<and> f a = b \<and> image_mset f M1 = N"
proof -
  obtain a where a: "a \<in># M" and fa: "f a = b"
    using multiset.set_map[of f M] unfolding assms
    by (metis image_iff union_single_eq_member)
  then obtain M1 where M: "M = add_mset a M1" using multi_member_split by metis
  have "image_mset f M1 = N" using assms unfolding M fa[symmetric] by simp
  thus ?thesis using M fa by blast
qed

lemma msed_rel_invL:
  assumes "rel_mset R (add_mset a M) N"
  shows "\<exists>N1 b. N = add_mset b N1 \<and> R a b \<and> rel_mset R M N1"
proof -
  obtain K where KM: "image_mset fst K = add_mset a M"
    and KN: "image_mset snd K = N" and sK: "set_mset K \<subseteq> {(a, b). R a b}"
    using assms
    unfolding multiset.rel_compp_Grp Grp_def by auto
  obtain K1 ab where K: "K = add_mset ab K1" and a: "fst ab = a"
    and K1M: "image_mset fst K1 = M" using msed_map_invR[OF KM] by auto
  obtain N1 where N: "N = add_mset (snd ab) N1" and K1N1: "image_mset snd K1 = N1"
    using msed_map_invL[OF KN[unfolded K]] by auto
  have Rab: "R a (snd ab)" using sK a unfolding K by auto
  have "rel_mset R M N1" using sK K1M K1N1
    unfolding K multiset.rel_compp_Grp Grp_def by auto
  thus ?thesis using N Rab by auto
qed

lemma msed_rel_invR:
  assumes "rel_mset R M (add_mset b N)"
  shows "\<exists>M1 a. M = add_mset a M1 \<and> R a b \<and> rel_mset R M1 N"
proof -
  obtain K where KN: "image_mset snd K = add_mset b N"
    and KM: "image_mset fst K = M" and sK: "set_mset K \<subseteq> {(a, b). R a b}"
    using assms
    unfolding multiset.rel_compp_Grp Grp_def by auto
  obtain K1 ab where K: "K = add_mset ab K1" and b: "snd ab = b"
    and K1N: "image_mset snd K1 = N" using msed_map_invR[OF KN] by auto
  obtain M1 where M: "M = add_mset (fst ab) M1" and K1M1: "image_mset fst K1 = M1"
    using msed_map_invL[OF KM[unfolded K]] by auto
  have Rab: "R (fst ab) b" using sK b unfolding K by auto
  have "rel_mset R M1 N" using sK K1N K1M1
    unfolding K multiset.rel_compp_Grp Grp_def by auto
  thus ?thesis using M Rab by auto
qed

lemma rel_mset_imp_rel_mset':
  assumes "rel_mset R M N"
  shows "rel_mset' R M N"
using assms proof(induct M arbitrary: N rule: measure_induct_rule[of size])
  case (less M)
  have c: "size M = size N" using rel_mset_size[OF less.prems] .
  show ?case
  proof(cases "M = {#}")
    case True hence "N = {#}" using c by simp
    thus ?thesis using True rel_mset'.Zero by auto
  next
    case False then obtain M1 a where M: "M = add_mset a M1" by (metis multi_nonempty_split)
    obtain N1 b where N: "N = add_mset b N1" and R: "R a b" and ms: "rel_mset R M1 N1"
      using msed_rel_invL[OF less.prems[unfolded M]] by auto
    have "rel_mset' R M1 N1" using less.hyps[of M1 N1] ms unfolding M by simp
    thus ?thesis using rel_mset'.Plus[of R a b, OF R] unfolding M N by simp
  qed
qed

lemma rel_mset_rel_mset': "rel_mset R M N = rel_mset' R M N"
  using rel_mset_imp_rel_mset' rel_mset'_imp_rel_mset by auto

text \<open>The main end product for \<^const>\<open>rel_mset\<close>: inductive characterization:\<close>
lemmas rel_mset_induct[case_names empty add, induct pred: rel_mset] =
  rel_mset'.induct[unfolded rel_mset_rel_mset'[symmetric]]


subsection \<open>Size setup\<close>

lemma size_multiset_o_map: "size_multiset g \<circ> image_mset f = size_multiset (g \<circ> f)"
  apply (rule ext)
  subgoal for x by (induct x) auto
  done

setup \<open>
  BNF_LFP_Size.register_size_global \<^type_name>\<open>multiset\<close> \<^const_name>\<open>size_multiset\<close>
    @{thm size_multiset_overloaded_def}
    @{thms size_multiset_empty size_multiset_single size_multiset_union size_empty size_single
      size_union}
    @{thms size_multiset_o_map}
\<close>

subsection \<open>Lemmas about Size\<close>

lemma size_mset_SucE: "size A = Suc n \<Longrightarrow> (\<And>a B. A = {#a#} + B \<Longrightarrow> size B = n \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases A) (auto simp add: ac_simps)

lemma size_Suc_Diff1: "x \<in># M \<Longrightarrow> Suc (size (M - {#x#})) = size M"
  using arg_cong[OF insert_DiffM, of _ _ size] by simp

lemma size_Diff_singleton: "x \<in># M \<Longrightarrow> size (M - {#x#}) = size M - 1"
  by (simp flip: size_Suc_Diff1)

lemma size_Diff_singleton_if: "size (A - {#x#}) = (if x \<in># A then size A - 1 else size A)"
  by (simp add: diff_single_trivial size_Diff_singleton)

lemma size_Un_Int: "size A + size B = size (A \<union># B) + size (A \<inter># B)"
  by (metis inter_subset_eq_union size_union subset_mset.diff_add union_diff_inter_eq_sup)

lemma size_Un_disjoint: "A \<inter># B = {#} \<Longrightarrow> size (A \<union># B) = size A + size B"
  using size_Un_Int[of A B] by simp

lemma size_Diff_subset_Int: "size (M - M') = size M - size (M \<inter># M')"
  by (metis diff_intersect_left_idem size_Diff_submset subset_mset.inf_le1)

lemma diff_size_le_size_Diff: "size (M :: _ multiset) - size M' \<le> size (M - M')"
  by (simp add: diff_le_mono2 size_Diff_subset_Int size_mset_mono)

lemma size_Diff1_less: "x\<in># M \<Longrightarrow> size (M - {#x#}) < size M"
  by (rule Suc_less_SucD) (simp add: size_Suc_Diff1)

lemma size_Diff2_less: "x\<in># M \<Longrightarrow> y\<in># M \<Longrightarrow> size (M - {#x#} - {#y#}) < size M"
  by (metis less_imp_diff_less size_Diff1_less size_Diff_subset_Int)

lemma size_Diff1_le: "size (M - {#x#}) \<le> size M"
  by (cases "x \<in># M") (simp_all add: size_Diff1_less less_imp_le diff_single_trivial)

lemma size_psubset: "M \<subseteq># M' \<Longrightarrow> size M < size M' \<Longrightarrow> M \<subset># M'"
  using less_irrefl subset_mset_def by blast

lifting_update multiset.lifting
lifting_forget multiset.lifting

hide_const (open) wcount

end
