(*  Title:      HOL/Quotient_Examples/Quotient_FSet.thy
    Author:     Cezary Kaliszyk, TU Munich
    Author:     Christian Urban, TU Munich

Type of finite sets.
*)

(********************************************************************
  WARNING: There is a formalization of 'a fset as a subtype of sets in
  HOL/Library/FSet.thy using Lifting/Transfer. The user should use
  that file rather than this file unless there are some very specific
  reasons.
*********************************************************************)

theory Quotient_FSet
imports "HOL-Library.Multiset" "HOL-Library.Quotient_List"
begin

text \<open>
  The type of finite sets is created by a quotient construction
  over lists. The definition of the equivalence:
\<close>

definition
  list_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<approx>" 50)
where
  [simp]: "xs \<approx> ys \<longleftrightarrow> set xs = set ys"

lemma list_eq_reflp:
  "reflp list_eq"
  by (auto intro: reflpI)

lemma list_eq_symp:
  "symp list_eq"
  by (auto intro: sympI)

lemma list_eq_transp:
  "transp list_eq"
  by (auto intro: transpI)

lemma list_eq_equivp:
  "equivp list_eq"
  by (auto intro: equivpI list_eq_reflp list_eq_symp list_eq_transp)

text \<open>The \<open>fset\<close> type\<close>

quotient_type
  'a fset = "'a list" / "list_eq"
  by (rule list_eq_equivp)

text \<open>
  Definitions for sublist, cardinality, 
  intersection, difference and respectful fold over 
  lists.
\<close>

declare List.member_def [simp]

definition
  sub_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where 
  [simp]: "sub_list xs ys \<longleftrightarrow> set xs \<subseteq> set ys"

definition
  card_list :: "'a list \<Rightarrow> nat"
where
  [simp]: "card_list xs = card (set xs)"

definition
  inter_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  [simp]: "inter_list xs ys = [x \<leftarrow> xs. x \<in> set xs \<and> x \<in> set ys]"

definition
  diff_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  [simp]: "diff_list xs ys = [x \<leftarrow> xs. x \<notin> set ys]"

definition
  rsp_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "rsp_fold f \<longleftrightarrow> (\<forall>u v. f u \<circ> f v = f v \<circ> f u)"

lemma rsp_foldI:
  "(\<And>u v. f u \<circ> f v = f v \<circ> f u) \<Longrightarrow> rsp_fold f"
  by (simp add: rsp_fold_def)

lemma rsp_foldE:
  assumes "rsp_fold f"
  obtains "f u \<circ> f v = f v \<circ> f u"
  using assms by (simp add: rsp_fold_def)

definition
  fold_once :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"
where
  "fold_once f xs = (if rsp_fold f then fold f (remdups xs) else id)"

lemma fold_once_default [simp]:
  "\<not> rsp_fold f \<Longrightarrow> fold_once f xs = id"
  by (simp add: fold_once_def)

lemma fold_once_fold_remdups:
  "rsp_fold f \<Longrightarrow> fold_once f xs = fold f (remdups xs)"
  by (simp add: fold_once_def)


section \<open>Quotient composition lemmas\<close>

lemma list_all2_refl':
  assumes q: "equivp R"
  shows "(list_all2 R) r r"
  by (rule list_all2_refl) (metis equivp_def q)

lemma compose_list_refl:
  assumes q: "equivp R"
  shows "(list_all2 R OOO (\<approx>)) r r"
proof
  have *: "r \<approx> r" by (rule equivp_reflp[OF fset_equivp])
  show "list_all2 R r r" by (rule list_all2_refl'[OF q])
  with * show "((\<approx>) OO list_all2 R) r r" ..
qed

lemma map_list_eq_cong: "b \<approx> ba \<Longrightarrow> map f b \<approx> map f ba"
  by (simp only: list_eq_def set_map)

lemma quotient_compose_list_g:
  assumes q: "Quotient3 R Abs Rep"
  and     e: "equivp R"
  shows  "Quotient3 ((list_all2 R) OOO (\<approx>))
    (abs_fset \<circ> (map Abs)) ((map Rep) \<circ> rep_fset)"
  unfolding Quotient3_def comp_def
proof (intro conjI allI)
  fix a r s
  show "abs_fset (map Abs (map Rep (rep_fset a))) = a"
    by (simp add: abs_o_rep[OF q] Quotient3_abs_rep[OF Quotient3_fset] List.map.id)
  have b: "list_all2 R (map Rep (rep_fset a)) (map Rep (rep_fset a))"
    by (rule list_all2_refl'[OF e])
  have c: "((\<approx>) OO list_all2 R) (map Rep (rep_fset a)) (map Rep (rep_fset a))"
    by (rule, rule equivp_reflp[OF fset_equivp]) (rule b)
  show "(list_all2 R OOO (\<approx>)) (map Rep (rep_fset a)) (map Rep (rep_fset a))"
    by (rule, rule list_all2_refl'[OF e]) (rule c)
  show "(list_all2 R OOO (\<approx>)) r s = ((list_all2 R OOO (\<approx>)) r r \<and>
        (list_all2 R OOO (\<approx>)) s s \<and> abs_fset (map Abs r) = abs_fset (map Abs s))"
  proof (intro iffI conjI)
    show "(list_all2 R OOO (\<approx>)) r r" by (rule compose_list_refl[OF e])
    show "(list_all2 R OOO (\<approx>)) s s" by (rule compose_list_refl[OF e])
  next
    assume a: "(list_all2 R OOO (\<approx>)) r s"
    then have b: "map Abs r \<approx> map Abs s"
    proof (elim relcomppE)
      fix b ba
      assume c: "list_all2 R r b"
      assume d: "b \<approx> ba"
      assume e: "list_all2 R ba s"
      have f: "map Abs r = map Abs b"
        using Quotient3_rel[OF list_quotient3[OF q]] c by blast
      have "map Abs ba = map Abs s"
        using Quotient3_rel[OF list_quotient3[OF q]] e by blast
      then have g: "map Abs s = map Abs ba" by simp
      then show "map Abs r \<approx> map Abs s" using d f map_list_eq_cong by simp
    qed
    then show "abs_fset (map Abs r) = abs_fset (map Abs s)"
      using Quotient3_rel[OF Quotient3_fset] by blast
  next
    assume a: "(list_all2 R OOO (\<approx>)) r r \<and> (list_all2 R OOO (\<approx>)) s s
      \<and> abs_fset (map Abs r) = abs_fset (map Abs s)"
    then have s: "(list_all2 R OOO (\<approx>)) s s" by simp
    have d: "map Abs r \<approx> map Abs s"
      by (subst Quotient3_rel [OF Quotient3_fset, symmetric]) (simp add: a)
    have b: "map Rep (map Abs r) \<approx> map Rep (map Abs s)"
      by (rule map_list_eq_cong[OF d])
    have y: "list_all2 R (map Rep (map Abs s)) s"
      by (fact rep_abs_rsp_left[OF list_quotient3[OF q], OF list_all2_refl'[OF e, of s]])
    have c: "((\<approx>) OO list_all2 R) (map Rep (map Abs r)) s"
      by (rule relcomppI) (rule b, rule y)
    have z: "list_all2 R r (map Rep (map Abs r))"
      by (fact rep_abs_rsp[OF list_quotient3[OF q], OF list_all2_refl'[OF e, of r]])
    then show "(list_all2 R OOO (\<approx>)) r s"
      using a c relcomppI by simp
  qed
qed

lemma quotient_compose_list[quot_thm]:
  shows  "Quotient3 ((list_all2 (\<approx>)) OOO (\<approx>))
    (abs_fset \<circ> (map abs_fset)) ((map rep_fset) \<circ> rep_fset)"
  by (rule quotient_compose_list_g, rule Quotient3_fset, rule list_eq_equivp)


section \<open>Quotient definitions for fsets\<close>


subsection \<open>Finite sets are a bounded, distributive lattice with minus\<close>

instantiation fset :: (type) "{bounded_lattice_bot, distrib_lattice, minus}"
begin

quotient_definition
  "bot :: 'a fset" 
  is "Nil :: 'a list" done

abbreviation
  empty_fset  ("{||}")
where
  "{||} \<equiv> bot :: 'a fset"

quotient_definition
  "less_eq_fset :: ('a fset \<Rightarrow> 'a fset \<Rightarrow> bool)"
  is "sub_list :: ('a list \<Rightarrow> 'a list \<Rightarrow> bool)" by simp

abbreviation
  subset_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subseteq>|" 50)
where
  "xs |\<subseteq>| ys \<equiv> xs \<le> ys"

definition
  less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool"
where  
  "xs < ys \<equiv> xs \<le> ys \<and> xs \<noteq> (ys::'a fset)"

abbreviation
  psubset_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subset>|" 50)
where
  "xs |\<subset>| ys \<equiv> xs < ys"

quotient_definition
  "sup :: 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "append :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" by simp

abbreviation
  union_fset (infixl "|\<union>|" 65)
where
  "xs |\<union>| ys \<equiv> sup xs (ys::'a fset)"

quotient_definition
  "inf :: 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "inter_list :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" by simp

abbreviation
  inter_fset (infixl "|\<inter>|" 65)
where
  "xs |\<inter>| ys \<equiv> inf xs (ys::'a fset)"

quotient_definition
  "minus :: 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "diff_list :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" by fastforce

instance
proof
  fix x y z :: "'a fset"
  show "x |\<subset>| y \<longleftrightarrow> x |\<subseteq>| y \<and> \<not> y |\<subseteq>| x"
    by (unfold less_fset_def, descending) auto
  show "x |\<subseteq>| x" by (descending) (simp)
  show "{||} |\<subseteq>| x" by (descending) (simp)
  show "x |\<subseteq>| x |\<union>| y" by (descending) (simp)
  show "y |\<subseteq>| x |\<union>| y" by (descending) (simp)
  show "x |\<inter>| y |\<subseteq>| x" by (descending) (auto)
  show "x |\<inter>| y |\<subseteq>| y" by (descending) (auto)
  show "x |\<union>| (y |\<inter>| z) = x |\<union>| y |\<inter>| (x |\<union>| z)" 
    by (descending) (auto)
next
  fix x y z :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "y |\<subseteq>| z"
  show "x |\<subseteq>| z" using a b by (descending) (simp)
next
  fix x y :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "y |\<subseteq>| x"
  show "x = y" using a b by (descending) (auto)
next
  fix x y z :: "'a fset"
  assume a: "y |\<subseteq>| x"
  assume b: "z |\<subseteq>| x"
  show "y |\<union>| z |\<subseteq>| x" using a b by (descending) (simp)
next
  fix x y z :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "x |\<subseteq>| z"
  show "x |\<subseteq>| y |\<inter>| z" using a b by (descending) (auto)
qed

end


subsection \<open>Other constants for fsets\<close>

quotient_definition
  "insert_fset :: 'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "Cons" by auto

syntax
  "_insert_fset"     :: "args => 'a fset"  ("{|(_)|}")

translations
  "{|x, xs|}" == "CONST insert_fset x {|xs|}"
  "{|x|}"     == "CONST insert_fset x {||}"

quotient_definition
  fset_member
where
  "fset_member :: 'a fset \<Rightarrow> 'a \<Rightarrow> bool" is "List.member" by fastforce

abbreviation
  in_fset :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<in>|" 50)
where
  "x |\<in>| S \<equiv> fset_member S x"

abbreviation
  notin_fset :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<notin>|" 50)
where
  "x |\<notin>| S \<equiv> \<not> (x |\<in>| S)"


subsection \<open>Other constants on the Quotient Type\<close>

quotient_definition
  "card_fset :: 'a fset \<Rightarrow> nat"
  is card_list by simp

quotient_definition
  "map_fset :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset"
  is map by simp

quotient_definition
  "remove_fset :: 'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is removeAll by simp

quotient_definition
  "fset :: 'a fset \<Rightarrow> 'a set"
  is "set" by simp

lemma fold_once_set_equiv:
  assumes "xs \<approx> ys"
  shows "fold_once f xs = fold_once f ys"
proof (cases "rsp_fold f")
  case False then show ?thesis by simp
next
  case True
  then have "\<And>x y. x \<in> set (remdups xs) \<Longrightarrow> y \<in> set (remdups xs) \<Longrightarrow> f x \<circ> f y = f y \<circ> f x"
    by (rule rsp_foldE)
  moreover from assms have "mset (remdups xs) = mset (remdups ys)"
    by (simp add: set_eq_iff_mset_remdups_eq)
  ultimately have "fold f (remdups xs) = fold f (remdups ys)"
    by (rule fold_multiset_equiv)
  with True show ?thesis by (simp add: fold_once_fold_remdups)
qed

quotient_definition
  "fold_fset :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b \<Rightarrow> 'b"
  is fold_once by (rule fold_once_set_equiv)

lemma concat_rsp_pre:
  assumes a: "list_all2 (\<approx>) x x'"
  and     b: "x' \<approx> y'"
  and     c: "list_all2 (\<approx>) y' y"
  and     d: "\<exists>x\<in>set x. xa \<in> set x"
  shows "\<exists>x\<in>set y. xa \<in> set x"
proof -
  obtain xb where e: "xb \<in> set x" and f: "xa \<in> set xb" using d by auto
  have "\<exists>y. y \<in> set x' \<and> xb \<approx> y" by (rule list_all2_find_element[OF e a])
  then obtain ya where h: "ya \<in> set x'" and i: "xb \<approx> ya" by auto
  have "ya \<in> set y'" using b h by simp
  then have "\<exists>yb. yb \<in> set y \<and> ya \<approx> yb" using c by (rule list_all2_find_element)
  then show ?thesis using f i by auto
qed

quotient_definition
  "concat_fset :: ('a fset) fset \<Rightarrow> 'a fset"
  is concat 
proof (elim relcomppE)
fix a b ba bb
  assume a: "list_all2 (\<approx>) a ba"
  with list_symp [OF list_eq_symp] have a': "list_all2 (\<approx>) ba a" by (rule sympE)
  assume b: "ba \<approx> bb"
  with list_eq_symp have b': "bb \<approx> ba" by (rule sympE)
  assume c: "list_all2 (\<approx>) bb b"
  with list_symp [OF list_eq_symp] have c': "list_all2 (\<approx>) b bb" by (rule sympE)
  have "\<forall>x. (\<exists>xa\<in>set a. x \<in> set xa) = (\<exists>xa\<in>set b. x \<in> set xa)" 
  proof
    fix x
    show "(\<exists>xa\<in>set a. x \<in> set xa) = (\<exists>xa\<in>set b. x \<in> set xa)" 
    proof
      assume d: "\<exists>xa\<in>set a. x \<in> set xa"
      show "\<exists>xa\<in>set b. x \<in> set xa" by (rule concat_rsp_pre[OF a b c d])
    next
      assume e: "\<exists>xa\<in>set b. x \<in> set xa"
      show "\<exists>xa\<in>set a. x \<in> set xa" by (rule concat_rsp_pre[OF c' b' a' e])
    qed
  qed
  then show "concat a \<approx> concat b" by auto
qed

quotient_definition
  "filter_fset :: ('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is filter by force


subsection \<open>Compositional respectfulness and preservation lemmas\<close>

lemma Nil_rsp2 [quot_respect]: 
  shows "(list_all2 (\<approx>) OOO (\<approx>)) Nil Nil"
  by (rule compose_list_refl, rule list_eq_equivp)

lemma Cons_rsp2 [quot_respect]:
  shows "((\<approx>) ===> list_all2 (\<approx>) OOO (\<approx>) ===> list_all2 (\<approx>) OOO (\<approx>)) Cons Cons"
  apply (auto intro!: rel_funI)
  apply (rule_tac b="x # b" in relcomppI)
  apply auto
  apply (rule_tac b="x # ba" in relcomppI)
  apply auto
  done

lemma Nil_prs2 [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Abs \<circ> map f) [] = Abs []"
  by simp

lemma Cons_prs2 [quot_preserve]:
  assumes q: "Quotient3 R1 Abs1 Rep1"
  and     r: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep1 ---> (map Rep1 \<circ> Rep2) ---> (Abs2 \<circ> map Abs1)) (#) = (id ---> Rep2 ---> Abs2) (#)"
  by (auto simp add: fun_eq_iff comp_def Quotient3_abs_rep [OF q])

lemma append_prs2 [quot_preserve]:
  assumes q: "Quotient3 R1 Abs1 Rep1"
  and     r: "Quotient3 R2 Abs2 Rep2"
  shows "((map Rep1 \<circ> Rep2) ---> (map Rep1 \<circ> Rep2) ---> (Abs2 \<circ> map Abs1)) (@) =
    (Rep2 ---> Rep2 ---> Abs2) (@)"
  by (simp add: fun_eq_iff abs_o_rep[OF q] List.map.id)

lemma list_all2_app_l:
  assumes a: "reflp R"
  and b: "list_all2 R l r"
  shows "list_all2 R (z @ l) (z @ r)"
  using a b by (induct z) (auto elim: reflpE)

lemma append_rsp2_pre0:
  assumes a:"list_all2 (\<approx>) x x'"
  shows "list_all2 (\<approx>) (x @ z) (x' @ z)"
  using a apply (induct x x' rule: list_induct2')
  by simp_all (rule list_all2_refl'[OF list_eq_equivp])

lemma append_rsp2_pre1:
  assumes a:"list_all2 (\<approx>) x x'"
  shows "list_all2 (\<approx>) (z @ x) (z @ x')"
  using a apply (induct x x' arbitrary: z rule: list_induct2')
  apply (rule list_all2_refl'[OF list_eq_equivp])
  apply (simp_all del: list_eq_def)
  apply (rule list_all2_app_l)
  apply (simp_all add: reflpI)
  done

lemma append_rsp2_pre:
  assumes "list_all2 (\<approx>) x x'"
    and "list_all2 (\<approx>) z z'"
  shows "list_all2 (\<approx>) (x @ z) (x' @ z')"
  using assms by (rule list_all2_appendI)

lemma compositional_rsp3:
  assumes "(R1 ===> R2 ===> R3) C C" and "(R4 ===> R5 ===> R6) C C"
  shows "(R1 OOO R4 ===> R2 OOO R5 ===> R3 OOO R6) C C"
  by (auto intro!: rel_funI)
     (metis (full_types) assms rel_funE relcomppI)

lemma append_rsp2 [quot_respect]:
  "(list_all2 (\<approx>) OOO (\<approx>) ===> list_all2 (\<approx>) OOO (\<approx>) ===> list_all2 (\<approx>) OOO (\<approx>)) append append"
  by (intro compositional_rsp3)
     (auto intro!: rel_funI simp add: append_rsp2_pre)

lemma map_rsp2 [quot_respect]:
  "(((\<approx>) ===> (\<approx>)) ===> list_all2 (\<approx>) OOO (\<approx>) ===> list_all2 (\<approx>) OOO (\<approx>)) map map"
proof (auto intro!: rel_funI)
  fix f f' :: "'a list \<Rightarrow> 'b list"
  fix xa ya x y :: "'a list list"
  assume fs: "((\<approx>) ===> (\<approx>)) f f'" and x: "list_all2 (\<approx>) xa x" and xy: "set x = set y" and y: "list_all2 (\<approx>) y ya"
  have a: "(list_all2 (\<approx>)) (map f xa) (map f x)"
    using x
    by (induct xa x rule: list_induct2')
       (simp_all, metis fs rel_funE list_eq_def)
  have b: "set (map f x) = set (map f y)"
    using xy fs
    by (induct x y rule: list_induct2')
       (simp_all, metis image_insert)
  have c: "(list_all2 (\<approx>)) (map f y) (map f' ya)"
    using y fs
    by (induct y ya rule: list_induct2')
       (simp_all, metis apply_rsp' list_eq_def)
  show "(list_all2 (\<approx>) OOO (\<approx>)) (map f xa) (map f' ya)"
    by (metis a b c list_eq_def relcomppI)
qed

lemma map_prs2 [quot_preserve]:
  shows "((abs_fset ---> rep_fset) ---> (map rep_fset \<circ> rep_fset) ---> abs_fset \<circ> map abs_fset) map = (id ---> rep_fset ---> abs_fset) map"
  by (auto simp add: fun_eq_iff)
     (simp only: map_map[symmetric] map_prs_aux[OF Quotient3_fset Quotient3_fset])

section \<open>Lifted theorems\<close>

subsection \<open>fset\<close>

lemma fset_simps [simp]:
  shows "fset {||} = {}"
  and   "fset (insert_fset x S) = insert x (fset S)"
  by (descending, simp)+

lemma finite_fset [simp]: 
  shows "finite (fset S)"
  by (descending) (simp)

lemma fset_cong:
  shows "fset S = fset T \<longleftrightarrow> S = T"
  by (descending) (simp)

lemma filter_fset [simp]:
  shows "fset (filter_fset P xs) = Collect P \<inter> fset xs"
  by (descending) (auto)

lemma remove_fset [simp]: 
  shows "fset (remove_fset x xs) = fset xs - {x}"
  by (descending) (simp)

lemma inter_fset [simp]: 
  shows "fset (xs |\<inter>| ys) = fset xs \<inter> fset ys"
  by (descending) (auto)

lemma union_fset [simp]: 
  shows "fset (xs |\<union>| ys) = fset xs \<union> fset ys"
  by (lifting set_append)

lemma minus_fset [simp]: 
  shows "fset (xs - ys) = fset xs - fset ys"
  by (descending) (auto)


subsection \<open>in_fset\<close>

lemma in_fset: 
  shows "x |\<in>| S \<longleftrightarrow> x \<in> fset S"
  by descending simp

lemma notin_fset: 
  shows "x |\<notin>| S \<longleftrightarrow> x \<notin> fset S"
  by (simp add: in_fset)

lemma notin_empty_fset: 
  shows "x |\<notin>| {||}"
  by (simp add: in_fset)

lemma fset_eq_iff:
  shows "S = T \<longleftrightarrow> (\<forall>x. (x |\<in>| S) = (x |\<in>| T))"
  by descending auto

lemma none_in_empty_fset:
  shows "(\<forall>x. x |\<notin>| S) \<longleftrightarrow> S = {||}"
  by descending simp


subsection \<open>insert_fset\<close>

lemma in_insert_fset_iff [simp]:
  shows "x |\<in>| insert_fset y S \<longleftrightarrow> x = y \<or> x |\<in>| S"
  by descending simp

lemma
  shows insert_fsetI1: "x |\<in>| insert_fset x S"
  and   insert_fsetI2: "x |\<in>| S \<Longrightarrow> x |\<in>| insert_fset y S"
  by simp_all

lemma insert_absorb_fset [simp]:
  shows "x |\<in>| S \<Longrightarrow> insert_fset x S = S"
  by (descending) (auto)

lemma empty_not_insert_fset[simp]:
  shows "{||} \<noteq> insert_fset x S"
  and   "insert_fset x S \<noteq> {||}"
  by (descending, simp)+

lemma insert_fset_left_comm:
  shows "insert_fset x (insert_fset y S) = insert_fset y (insert_fset x S)"
  by (descending) (auto)

lemma insert_fset_left_idem:
  shows "insert_fset x (insert_fset x S) = insert_fset x S"
  by (descending) (auto)

lemma singleton_fset_eq[simp]:
  shows "{|x|} = {|y|} \<longleftrightarrow> x = y"
  by (descending) (auto)

lemma in_fset_mdef:
  shows "x |\<in>| F \<longleftrightarrow> x |\<notin>| (F - {|x|}) \<and> F = insert_fset x (F - {|x|})"
  by (descending) (auto)


subsection \<open>union_fset\<close>

lemmas [simp] =
  sup_bot_left[where 'a="'a fset"]
  sup_bot_right[where 'a="'a fset"]

lemma union_insert_fset [simp]:
  shows "insert_fset x S |\<union>| T = insert_fset x (S |\<union>| T)"
  by (lifting append.simps(2))

lemma singleton_union_fset_left:
  shows "{|a|} |\<union>| S = insert_fset a S"
  by simp

lemma singleton_union_fset_right:
  shows "S |\<union>| {|a|} = insert_fset a S"
  by (subst sup.commute) simp

lemma in_union_fset:
  shows "x |\<in>| S |\<union>| T \<longleftrightarrow> x |\<in>| S \<or> x |\<in>| T"
  by (descending) (simp)


subsection \<open>minus_fset\<close>

lemma minus_in_fset: 
  shows "x |\<in>| (xs - ys) \<longleftrightarrow> x |\<in>| xs \<and> x |\<notin>| ys"
  by (descending) (simp)

lemma minus_insert_fset: 
  shows "insert_fset x xs - ys = (if x |\<in>| ys then xs - ys else insert_fset x (xs - ys))"
  by (descending) (auto)

lemma minus_insert_in_fset[simp]: 
  shows "x |\<in>| ys \<Longrightarrow> insert_fset x xs - ys = xs - ys"
  by (simp add: minus_insert_fset)

lemma minus_insert_notin_fset[simp]: 
  shows "x |\<notin>| ys \<Longrightarrow> insert_fset x xs - ys = insert_fset x (xs - ys)"
  by (simp add: minus_insert_fset)

lemma in_minus_fset: 
  shows "x |\<in>| F - S \<Longrightarrow> x |\<notin>| S"
  unfolding in_fset minus_fset
  by blast

lemma notin_minus_fset: 
  shows "x |\<in>| S \<Longrightarrow> x |\<notin>| F - S"
  unfolding in_fset minus_fset
  by blast


subsection \<open>remove_fset\<close>

lemma in_remove_fset:
  shows "x |\<in>| remove_fset y S \<longleftrightarrow> x |\<in>| S \<and> x \<noteq> y"
  by (descending) (simp)

lemma notin_remove_fset:
  shows "x |\<notin>| remove_fset x S"
  by (descending) (simp)

lemma notin_remove_ident_fset:
  shows "x |\<notin>| S \<Longrightarrow> remove_fset x S = S"
  by (descending) (simp)

lemma remove_fset_cases:
  shows "S = {||} \<or> (\<exists>x. x |\<in>| S \<and> S = insert_fset x (remove_fset x S))"
  by (descending) (auto simp add: insert_absorb)
  

subsection \<open>inter_fset\<close>

lemma inter_empty_fset_l:
  shows "{||} |\<inter>| S = {||}"
  by simp

lemma inter_empty_fset_r:
  shows "S |\<inter>| {||} = {||}"
  by simp

lemma inter_insert_fset:
  shows "insert_fset x S |\<inter>| T = (if x |\<in>| T then insert_fset x (S |\<inter>| T) else S |\<inter>| T)"
  by (descending) (auto)

lemma in_inter_fset:
  shows "x |\<in>| (S |\<inter>| T) \<longleftrightarrow> x |\<in>| S \<and> x |\<in>| T"
  by (descending) (simp)


subsection \<open>subset_fset and psubset_fset\<close>

lemma subset_fset: 
  shows "xs |\<subseteq>| ys \<longleftrightarrow> fset xs \<subseteq> fset ys"
  by (descending) (simp)

lemma psubset_fset: 
  shows "xs |\<subset>| ys \<longleftrightarrow> fset xs \<subset> fset ys"
  unfolding less_fset_def 
  by (descending) (auto)

lemma subset_insert_fset:
  shows "(insert_fset x xs) |\<subseteq>| ys \<longleftrightarrow> x |\<in>| ys \<and> xs |\<subseteq>| ys"
  by (descending) (simp)

lemma subset_in_fset: 
  shows "xs |\<subseteq>| ys = (\<forall>x. x |\<in>| xs \<longrightarrow> x |\<in>| ys)"
  by (descending) (auto)

lemma subset_empty_fset:
  shows "xs |\<subseteq>| {||} \<longleftrightarrow> xs = {||}"
  by (descending) (simp)

lemma not_psubset_empty_fset: 
  shows "\<not> xs |\<subset>| {||}"
  by (metis fset_simps(1) psubset_fset not_psubset_empty)


subsection \<open>map_fset\<close>

lemma map_fset_simps [simp]:
   shows "map_fset f {||} = {||}"
  and   "map_fset f (insert_fset x S) = insert_fset (f x) (map_fset f S)"
  by (descending, simp)+

lemma map_fset_image [simp]:
  shows "fset (map_fset f S) = f ` (fset S)"
  by (descending) (simp)

lemma inj_map_fset_cong:
  shows "inj f \<Longrightarrow> map_fset f S = map_fset f T \<longleftrightarrow> S = T"
  by (descending) (metis inj_vimage_image_eq list_eq_def set_map)

lemma map_union_fset: 
  shows "map_fset f (S |\<union>| T) = map_fset f S |\<union>| map_fset f T"
  by (descending) (simp)

lemma in_fset_map_fset[simp]: "a |\<in>| map_fset f X = (\<exists>b. b |\<in>| X \<and> a = f b)"
  by descending auto


subsection \<open>card_fset\<close>

lemma card_fset: 
  shows "card_fset xs = card (fset xs)"
  by (descending) (simp)

lemma card_insert_fset_iff [simp]:
  shows "card_fset (insert_fset x S) = (if x |\<in>| S then card_fset S else Suc (card_fset S))"
  by (descending) (simp add: insert_absorb)

lemma card_fset_0[simp]:
  shows "card_fset S = 0 \<longleftrightarrow> S = {||}"
  by (descending) (simp)

lemma card_empty_fset[simp]:
  shows "card_fset {||} = 0"
  by (simp add: card_fset)

lemma card_fset_1:
  shows "card_fset S = 1 \<longleftrightarrow> (\<exists>x. S = {|x|})"
  by (descending) (auto simp add: card_Suc_eq)

lemma card_fset_gt_0:
  shows "x \<in> fset S \<Longrightarrow> 0 < card_fset S"
  by (descending) (auto simp add: card_gt_0_iff)
  
lemma card_notin_fset:
  shows "(x |\<notin>| S) = (card_fset (insert_fset x S) = Suc (card_fset S))"
  by simp

lemma card_fset_Suc: 
  shows "card_fset S = Suc n \<Longrightarrow> \<exists>x T. x |\<notin>| T \<and> S = insert_fset x T \<and> card_fset T = n"
  apply(descending)
  apply(auto dest!: card_eq_SucD)
  by (metis Diff_insert_absorb set_removeAll)

lemma card_remove_fset_iff [simp]:
  shows "card_fset (remove_fset y S) = (if y |\<in>| S then card_fset S - 1 else card_fset S)"
  by (descending) (simp)

lemma card_Suc_exists_in_fset: 
  shows "card_fset S = Suc n \<Longrightarrow> \<exists>a. a |\<in>| S"
  by (drule card_fset_Suc) (auto)

lemma in_card_fset_not_0: 
  shows "a |\<in>| A \<Longrightarrow> card_fset A \<noteq> 0"
  by (descending) (auto)

lemma card_fset_mono: 
  shows "xs |\<subseteq>| ys \<Longrightarrow> card_fset xs \<le> card_fset ys"
  unfolding card_fset psubset_fset
  by (simp add: card_mono subset_fset)

lemma card_subset_fset_eq: 
  shows "xs |\<subseteq>| ys \<Longrightarrow> card_fset ys \<le> card_fset xs \<Longrightarrow> xs = ys"
  unfolding card_fset subset_fset
  by (auto dest: card_seteq[OF finite_fset] simp add: fset_cong)

lemma psubset_card_fset_mono: 
  shows "xs |\<subset>| ys \<Longrightarrow> card_fset xs < card_fset ys"
  unfolding card_fset subset_fset
  by (metis finite_fset psubset_fset psubset_card_mono)

lemma card_union_inter_fset: 
  shows "card_fset xs + card_fset ys = card_fset (xs |\<union>| ys) + card_fset (xs |\<inter>| ys)"
  unfolding card_fset union_fset inter_fset
  by (rule card_Un_Int[OF finite_fset finite_fset])

lemma card_union_disjoint_fset: 
  shows "xs |\<inter>| ys = {||} \<Longrightarrow> card_fset (xs |\<union>| ys) = card_fset xs + card_fset ys"
  unfolding card_fset union_fset 
  apply (rule card_Un_disjoint[OF finite_fset finite_fset])
  by (metis inter_fset fset_simps(1))

lemma card_remove_fset_less1: 
  shows "x |\<in>| xs \<Longrightarrow> card_fset (remove_fset x xs) < card_fset xs"
  unfolding card_fset in_fset remove_fset 
  by (rule card_Diff1_less[OF finite_fset])

lemma card_remove_fset_less2: 
  shows "x |\<in>| xs \<Longrightarrow> y |\<in>| xs \<Longrightarrow> card_fset (remove_fset y (remove_fset x xs)) < card_fset xs"
  unfolding card_fset remove_fset in_fset
  by (rule card_Diff2_less[OF finite_fset])

lemma card_remove_fset_le1: 
  shows "card_fset (remove_fset x xs) \<le> card_fset xs"
  by simp

lemma card_psubset_fset: 
  shows "ys |\<subseteq>| xs \<Longrightarrow> card_fset ys < card_fset xs \<Longrightarrow> ys |\<subset>| xs"
  unfolding card_fset psubset_fset subset_fset
  by (rule card_psubset[OF finite_fset])

lemma card_map_fset_le: 
  shows "card_fset (map_fset f xs) \<le> card_fset xs"
  unfolding card_fset map_fset_image
  by (rule card_image_le[OF finite_fset])

lemma card_minus_insert_fset[simp]:
  assumes "a |\<in>| A" and "a |\<notin>| B"
  shows "card_fset (A - insert_fset a B) = card_fset (A - B) - 1"
  using assms  by (simp add: in_fset card_fset)

lemma card_minus_subset_fset:
  assumes "B |\<subseteq>| A"
  shows "card_fset (A - B) = card_fset A - card_fset B"
  using assms 
  by (simp add: subset_fset card_fset card_Diff_subset)

lemma card_minus_fset:
  shows "card_fset (A - B) = card_fset A - card_fset (A |\<inter>| B)"
  by (simp add: card_fset card_Diff_subset_Int)


subsection \<open>concat_fset\<close>

lemma concat_empty_fset [simp]:
  shows "concat_fset {||} = {||}"
  by descending simp

lemma concat_insert_fset [simp]:
  shows "concat_fset (insert_fset x S) = x |\<union>| concat_fset S"
  by descending simp

lemma concat_union_fset [simp]:
  shows "concat_fset (xs |\<union>| ys) = concat_fset xs |\<union>| concat_fset ys"
  by descending simp

lemma map_concat_fset:
  shows "map_fset f (concat_fset xs) = concat_fset (map_fset (map_fset f) xs)"
  by (lifting map_concat)

subsection \<open>filter_fset\<close>

lemma subset_filter_fset: 
  "filter_fset P xs |\<subseteq>| filter_fset Q xs = (\<forall> x. x |\<in>| xs \<longrightarrow> P x \<longrightarrow> Q x)"
  by descending auto

lemma eq_filter_fset: 
  "(filter_fset P xs = filter_fset Q xs) = (\<forall>x. x |\<in>| xs \<longrightarrow> P x = Q x)"
  by descending auto

lemma psubset_filter_fset:
  "(\<And>x. x |\<in>| xs \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> (x |\<in>| xs & \<not> P x & Q x) \<Longrightarrow> 
    filter_fset P xs |\<subset>| filter_fset Q xs"
  unfolding less_fset_def by (auto simp add: subset_filter_fset eq_filter_fset)


subsection \<open>fold_fset\<close>

lemma fold_empty_fset: 
  "fold_fset f {||} = id"
  by descending (simp add: fold_once_def)

lemma fold_insert_fset: "fold_fset f (insert_fset a A) =
  (if rsp_fold f then if a |\<in>| A then fold_fset f A else fold_fset f A \<circ> f a else id)"
  by descending (simp add: fold_once_fold_remdups)

lemma remdups_removeAll:
  "remdups (removeAll x xs) = remove1 x (remdups xs)"
  by (induct xs) auto

lemma member_commute_fold_once:
  assumes "rsp_fold f"
    and "x \<in> set xs"
  shows "fold_once f xs = fold_once f (removeAll x xs) \<circ> f x"
proof -
  from assms have "fold f (remdups xs) = fold f (remove1 x (remdups xs)) \<circ> f x"
    by (auto intro!: fold_remove1_split elim: rsp_foldE)
  then show ?thesis using \<open>rsp_fold f\<close> by (simp add: fold_once_fold_remdups remdups_removeAll)
qed

lemma in_commute_fold_fset:
  "rsp_fold f \<Longrightarrow> h |\<in>| b \<Longrightarrow> fold_fset f b = fold_fset f (remove_fset h b) \<circ> f h"
  by descending (simp add: member_commute_fold_once)


subsection \<open>Choice in fsets\<close>

lemma fset_choice: 
  assumes a: "\<forall>x. x |\<in>| A \<longrightarrow> (\<exists>y. P x y)"
  shows "\<exists>f. \<forall>x. x |\<in>| A \<longrightarrow> P x (f x)"
  using a
  apply(descending)
  using finite_set_choice
  by (auto simp add: Ball_def)


section \<open>Induction and Cases rules for fsets\<close>

lemma fset_exhaust [case_names empty insert, cases type: fset]:
  assumes empty_fset_case: "S = {||} \<Longrightarrow> P" 
  and     insert_fset_case: "\<And>x S'. S = insert_fset x S' \<Longrightarrow> P"
  shows "P"
  using assms by (lifting list.exhaust)

lemma fset_induct [case_names empty insert]:
  assumes empty_fset_case: "P {||}"
  and     insert_fset_case: "\<And>x S. P S \<Longrightarrow> P (insert_fset x S)"
  shows "P S"
  using assms 
  by (descending) (blast intro: list.induct)

lemma fset_induct_stronger [case_names empty insert, induct type: fset]:
  assumes empty_fset_case: "P {||}"
  and     insert_fset_case: "\<And>x S. \<lbrakk>x |\<notin>| S; P S\<rbrakk> \<Longrightarrow> P (insert_fset x S)"
  shows "P S"
proof(induct S rule: fset_induct)
  case empty
  show "P {||}" using empty_fset_case by simp
next
  case (insert x S)
  have "P S" by fact
  then show "P (insert_fset x S)" using insert_fset_case 
    by (cases "x |\<in>| S") (simp_all)
qed

lemma fset_card_induct:
  assumes empty_fset_case: "P {||}"
  and     card_fset_Suc_case: "\<And>S T. Suc (card_fset S) = (card_fset T) \<Longrightarrow> P S \<Longrightarrow> P T"
  shows "P S"
proof (induct S)
  case empty
  show "P {||}" by (rule empty_fset_case)
next
  case (insert x S)
  have h: "P S" by fact
  have "x |\<notin>| S" by fact
  then have "Suc (card_fset S) = card_fset (insert_fset x S)" 
    using card_fset_Suc by auto
  then show "P (insert_fset x S)" 
    using h card_fset_Suc_case by simp
qed

lemma fset_raw_strong_cases:
  obtains "xs = []"
    | ys x where "\<not> List.member ys x" and "xs \<approx> x # ys"
proof (induct xs)
  case Nil
  then show thesis by simp
next
  case (Cons a xs)
  have a: "\<lbrakk>xs = [] \<Longrightarrow> thesis; \<And>x ys. \<lbrakk>\<not> List.member ys x; xs \<approx> x # ys\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
    by (rule Cons(1))
  have b: "\<And>x' ys'. \<lbrakk>\<not> List.member ys' x'; a # xs \<approx> x' # ys'\<rbrakk> \<Longrightarrow> thesis" by fact
  have c: "xs = [] \<Longrightarrow> thesis" using b 
    apply(simp)
    by (metis list.set(1) emptyE empty_subsetI)
  have "\<And>x ys. \<lbrakk>\<not> List.member ys x; xs \<approx> x # ys\<rbrakk> \<Longrightarrow> thesis"
  proof -
    fix x :: 'a
    fix ys :: "'a list"
    assume d:"\<not> List.member ys x"
    assume e:"xs \<approx> x # ys"
    show thesis
    proof (cases "x = a")
      assume h: "x = a"
      then have f: "\<not> List.member ys a" using d by simp
      have g: "a # xs \<approx> a # ys" using e h by auto
      show thesis using b f g by simp
    next
      assume h: "x \<noteq> a"
      then have f: "\<not> List.member (a # ys) x" using d by auto
      have g: "a # xs \<approx> x # (a # ys)" using e h by auto
      show thesis using b f g by (simp del: List.member_def) 
    qed
  qed
  then show thesis using a c by blast
qed


lemma fset_strong_cases:
  obtains "xs = {||}"
    | ys x where "x |\<notin>| ys" and "xs = insert_fset x ys"
  by (lifting fset_raw_strong_cases)


lemma fset_induct2:
  "P {||} {||} \<Longrightarrow>
  (\<And>x xs. x |\<notin>| xs \<Longrightarrow> P (insert_fset x xs) {||}) \<Longrightarrow>
  (\<And>y ys. y |\<notin>| ys \<Longrightarrow> P {||} (insert_fset y ys)) \<Longrightarrow>
  (\<And>x xs y ys. \<lbrakk>P xs ys; x |\<notin>| xs; y |\<notin>| ys\<rbrakk> \<Longrightarrow> P (insert_fset x xs) (insert_fset y ys)) \<Longrightarrow>
  P xsa ysa"
  apply (induct xsa arbitrary: ysa)
  apply (induct_tac x rule: fset_induct_stronger)
  apply simp_all
  apply (induct_tac xa rule: fset_induct_stronger)
  apply simp_all
  done

text \<open>Extensionality\<close>

lemma fset_eqI:
  assumes "\<And>x. x \<in> fset A \<longleftrightarrow> x \<in> fset B"
  shows "A = B"
using assms proof (induct A arbitrary: B)
  case empty then show ?case
    by (auto simp add: in_fset none_in_empty_fset [symmetric] sym)
next
  case (insert x A)
  from insert.prems insert.hyps(1) have "\<And>z. z \<in> fset A \<longleftrightarrow> z \<in> fset (B - {|x|})"
    by (auto simp add: in_fset)
  then have A: "A = B - {|x|}" by (rule insert.hyps(2))
  with insert.prems [symmetric, of x] have "x |\<in>| B" by (simp add: in_fset)
  with A show ?case by (metis in_fset_mdef)
qed

subsection \<open>alternate formulation with a different decomposition principle
  and a proof of equivalence\<close>

inductive
  list_eq2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<approx>2 _")
where
  "(a # b # xs) \<approx>2 (b # a # xs)"
| "[] \<approx>2 []"
| "xs \<approx>2 ys \<Longrightarrow> ys \<approx>2 xs"
| "(a # a # xs) \<approx>2 (a # xs)"
| "xs \<approx>2 ys \<Longrightarrow> (a # xs) \<approx>2 (a # ys)"
| "xs1 \<approx>2 xs2 \<Longrightarrow> xs2 \<approx>2 xs3 \<Longrightarrow> xs1 \<approx>2 xs3"

lemma list_eq2_refl:
  shows "xs \<approx>2 xs"
  by (induct xs) (auto intro: list_eq2.intros)

lemma cons_delete_list_eq2:
  shows "(a # (removeAll a A)) \<approx>2 (if List.member A a then A else a # A)"
  apply (induct A)
  apply (simp add: list_eq2_refl)
  apply (case_tac "List.member (aa # A) a")
  apply (simp_all)
  apply (case_tac [!] "a = aa")
  apply (simp_all)
  apply (case_tac "List.member A a")
  apply (auto)[2]
  apply (metis list_eq2.intros(3) list_eq2.intros(4) list_eq2.intros(5) list_eq2.intros(6))
  apply (metis list_eq2.intros(1) list_eq2.intros(5) list_eq2.intros(6))
  apply (auto simp add: list_eq2_refl)
  done

lemma member_delete_list_eq2:
  assumes a: "List.member r e"
  shows "(e # removeAll e r) \<approx>2 r"
  using a cons_delete_list_eq2[of e r]
  by simp

lemma list_eq2_equiv:
  "(l \<approx> r) \<longleftrightarrow> (list_eq2 l r)"
proof
  show "list_eq2 l r \<Longrightarrow> l \<approx> r" by (induct rule: list_eq2.induct) auto
next
  {
    fix n
    assume a: "card_list l = n" and b: "l \<approx> r"
    have "l \<approx>2 r"
      using a b
    proof (induct n arbitrary: l r)
      case 0
      have "card_list l = 0" by fact
      then have "\<forall>x. \<not> List.member l x" by auto
      then have z: "l = []" by auto
      then have "r = []" using \<open>l \<approx> r\<close> by simp
      then show ?case using z list_eq2_refl by simp
    next
      case (Suc m)
      have b: "l \<approx> r" by fact
      have d: "card_list l = Suc m" by fact
      then have "\<exists>a. List.member l a" 
        apply(simp)
        apply(drule card_eq_SucD)
        apply(blast)
        done
      then obtain a where e: "List.member l a" by auto
      then have e': "List.member r a" using list_eq_def [simplified List.member_def [symmetric], of l r] b 
        by auto
      have f: "card_list (removeAll a l) = m" using e d by (simp)
      have g: "removeAll a l \<approx> removeAll a r" using remove_fset.rsp b by simp
      have "(removeAll a l) \<approx>2 (removeAll a r)" by (rule Suc.hyps[OF f g])
      then have h: "(a # removeAll a l) \<approx>2 (a # removeAll a r)" by (rule list_eq2.intros(5))
      have i: "l \<approx>2 (a # removeAll a l)"
        by (rule list_eq2.intros(3)[OF member_delete_list_eq2[OF e]])
      have "l \<approx>2 (a # removeAll a r)" by (rule list_eq2.intros(6)[OF i h])
      then show ?case using list_eq2.intros(6)[OF _ member_delete_list_eq2[OF e']] by simp
    qed
    }
  then show "l \<approx> r \<Longrightarrow> l \<approx>2 r" by blast
qed


(* We cannot write it as "assumes .. shows" since Isabelle changes
   the quantifiers to schematic variables and reintroduces them in
   a different order *)
lemma fset_eq_cases:
 "\<lbrakk>a1 = a2;
   \<And>a b xs. \<lbrakk>a1 = insert_fset a (insert_fset b xs); a2 = insert_fset b (insert_fset a xs)\<rbrakk> \<Longrightarrow> P;
   \<lbrakk>a1 = {||}; a2 = {||}\<rbrakk> \<Longrightarrow> P; \<And>xs ys. \<lbrakk>a1 = ys; a2 = xs; xs = ys\<rbrakk> \<Longrightarrow> P;
   \<And>a xs. \<lbrakk>a1 = insert_fset a (insert_fset a xs); a2 = insert_fset a xs\<rbrakk> \<Longrightarrow> P;
   \<And>xs ys a. \<lbrakk>a1 = insert_fset a xs; a2 = insert_fset a ys; xs = ys\<rbrakk> \<Longrightarrow> P;
   \<And>xs1 xs2 xs3. \<lbrakk>a1 = xs1; a2 = xs3; xs1 = xs2; xs2 = xs3\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  by (lifting list_eq2.cases[simplified list_eq2_equiv[symmetric]])

lemma fset_eq_induct:
  assumes "x1 = x2"
  and "\<And>a b xs. P (insert_fset a (insert_fset b xs)) (insert_fset b (insert_fset a xs))"
  and "P {||} {||}"
  and "\<And>xs ys. \<lbrakk>xs = ys; P xs ys\<rbrakk> \<Longrightarrow> P ys xs"
  and "\<And>a xs. P (insert_fset a (insert_fset a xs)) (insert_fset a xs)"
  and "\<And>xs ys a. \<lbrakk>xs = ys; P xs ys\<rbrakk> \<Longrightarrow> P (insert_fset a xs) (insert_fset a ys)"
  and "\<And>xs1 xs2 xs3. \<lbrakk>xs1 = xs2; P xs1 xs2; xs2 = xs3; P xs2 xs3\<rbrakk> \<Longrightarrow> P xs1 xs3"
  shows "P x1 x2"
  using assms
  by (lifting list_eq2.induct[simplified list_eq2_equiv[symmetric]])

ML \<open>
fun dest_fsetT \<^Type>\<open>fset T\<close> = T
  | dest_fsetT T = raise TYPE ("dest_fsetT: fset type expected", [T], []);
\<close>

no_notation
  list_eq (infix "\<approx>" 50) and 
  list_eq2 (infix "\<approx>2" 50)

end
