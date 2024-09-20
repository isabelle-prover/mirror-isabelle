(*  Title:      HOL/HOLCF/Fixrec.thy
    Author:     Amber Telfer and Brian Huffman
*)

section "Package for defining recursive functions in HOLCF"

theory Fixrec
imports Cprod Sprod Ssum Up One Tr Fix
keywords "fixrec" :: thy_defn
begin

subsection \<open>Pattern-match monad\<close>

default_sort cpo

pcpodef 'a match = "UNIV::(one ++ 'a u) set"
by simp_all

definition
  fail :: "'a match" where
  "fail = Abs_match (sinl\<cdot>ONE)"

definition
  succeed :: "'a \<rightarrow> 'a match" where
  "succeed = (\<Lambda> x. Abs_match (sinr\<cdot>(up\<cdot>x)))"

lemma matchE [case_names bottom fail succeed, cases type: match]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = fail \<Longrightarrow> Q; \<And>x. p = succeed\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding fail_def succeed_def
apply (cases p, rename_tac r)
apply (rule_tac p=r in ssumE, simp add: Abs_match_strict)
apply (rule_tac p=x in oneE, simp, simp)
apply (rule_tac p=y in upE, simp, simp add: cont_Abs_match)
done

lemma succeed_defined [simp]: "succeed\<cdot>x \<noteq> \<bottom>"
by (simp add: succeed_def cont_Abs_match Abs_match_bottom_iff)

lemma fail_defined [simp]: "fail \<noteq> \<bottom>"
by (simp add: fail_def Abs_match_bottom_iff)

lemma succeed_eq [simp]: "(succeed\<cdot>x = succeed\<cdot>y) = (x = y)"
by (simp add: succeed_def cont_Abs_match Abs_match_inject)

lemma succeed_neq_fail [simp]:
  "succeed\<cdot>x \<noteq> fail" "fail \<noteq> succeed\<cdot>x"
by (simp_all add: succeed_def fail_def cont_Abs_match Abs_match_inject)

subsubsection \<open>Run operator\<close>

definition
  run :: "'a match \<rightarrow> 'a::pcpo" where
  "run = (\<Lambda> m. sscase\<cdot>\<bottom>\<cdot>(fup\<cdot>ID)\<cdot>(Rep_match m))"

text \<open>rewrite rules for run\<close>

lemma run_strict [simp]: "run\<cdot>\<bottom> = \<bottom>"
unfolding run_def
by (simp add: cont_Rep_match Rep_match_strict)

lemma run_fail [simp]: "run\<cdot>fail = \<bottom>"
unfolding run_def fail_def
by (simp add: cont_Rep_match Abs_match_inverse)

lemma run_succeed [simp]: "run\<cdot>(succeed\<cdot>x) = x"
unfolding run_def succeed_def
by (simp add: cont_Rep_match cont_Abs_match Abs_match_inverse)

subsubsection \<open>Monad plus operator\<close>

definition
  mplus :: "'a match \<rightarrow> 'a match \<rightarrow> 'a match" where
  "mplus = (\<Lambda> m1 m2. sscase\<cdot>(\<Lambda> _. m2)\<cdot>(\<Lambda> _. m1)\<cdot>(Rep_match m1))"

abbreviation
  mplus_syn :: "['a match, 'a match] \<Rightarrow> 'a match"  (infixr \<open>+++\<close> 65)  where
  "m1 +++ m2 == mplus\<cdot>m1\<cdot>m2"

text \<open>rewrite rules for mplus\<close>

lemma mplus_strict [simp]: "\<bottom> +++ m = \<bottom>"
unfolding mplus_def
by (simp add: cont_Rep_match Rep_match_strict)

lemma mplus_fail [simp]: "fail +++ m = m"
unfolding mplus_def fail_def
by (simp add: cont_Rep_match Abs_match_inverse)

lemma mplus_succeed [simp]: "succeed\<cdot>x +++ m = succeed\<cdot>x"
unfolding mplus_def succeed_def
by (simp add: cont_Rep_match cont_Abs_match Abs_match_inverse)

lemma mplus_fail2 [simp]: "m +++ fail = m"
by (cases m, simp_all)

lemma mplus_assoc: "(x +++ y) +++ z = x +++ (y +++ z)"
by (cases x, simp_all)

subsection \<open>Match functions for built-in types\<close>

default_sort pcpo

definition
  match_bottom :: "'a \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_bottom = (\<Lambda> x k. seq\<cdot>x\<cdot>fail)"

definition
  match_Pair :: "'a::cpo \<times> 'b::cpo \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_Pair = (\<Lambda> x k. csplit\<cdot>k\<cdot>x)"

definition
  match_spair :: "'a \<otimes> 'b \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_spair = (\<Lambda> x k. ssplit\<cdot>k\<cdot>x)"

definition
  match_sinl :: "'a \<oplus> 'b \<rightarrow> ('a \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_sinl = (\<Lambda> x k. sscase\<cdot>k\<cdot>(\<Lambda> b. fail)\<cdot>x)"

definition
  match_sinr :: "'a \<oplus> 'b \<rightarrow> ('b \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_sinr = (\<Lambda> x k. sscase\<cdot>(\<Lambda> a. fail)\<cdot>k\<cdot>x)"

definition
  match_up :: "'a::cpo u \<rightarrow> ('a \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_up = (\<Lambda> x k. fup\<cdot>k\<cdot>x)"

definition
  match_ONE :: "one \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_ONE = (\<Lambda> ONE k. k)"

definition
  match_TT :: "tr \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_TT = (\<Lambda> x k. If x then k else fail)"

definition
  match_FF :: "tr \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_FF = (\<Lambda> x k. If x then fail else k)"

lemma match_bottom_simps [simp]:
  "match_bottom\<cdot>x\<cdot>k = (if x = \<bottom> then \<bottom> else fail)"
by (simp add: match_bottom_def)

lemma match_Pair_simps [simp]:
  "match_Pair\<cdot>(x, y)\<cdot>k = k\<cdot>x\<cdot>y"
by (simp_all add: match_Pair_def)

lemma match_spair_simps [simp]:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> match_spair\<cdot>(:x, y:)\<cdot>k = k\<cdot>x\<cdot>y"
  "match_spair\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_spair_def)

lemma match_sinl_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinl\<cdot>x)\<cdot>k = k\<cdot>x"
  "y \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinr\<cdot>y)\<cdot>k = fail"
  "match_sinl\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_sinl_def)

lemma match_sinr_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinl\<cdot>x)\<cdot>k = fail"
  "y \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinr\<cdot>y)\<cdot>k = k\<cdot>y"
  "match_sinr\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_sinr_def)

lemma match_up_simps [simp]:
  "match_up\<cdot>(up\<cdot>x)\<cdot>k = k\<cdot>x"
  "match_up\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_up_def)

lemma match_ONE_simps [simp]:
  "match_ONE\<cdot>ONE\<cdot>k = k"
  "match_ONE\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_ONE_def)

lemma match_TT_simps [simp]:
  "match_TT\<cdot>TT\<cdot>k = k"
  "match_TT\<cdot>FF\<cdot>k = fail"
  "match_TT\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_TT_def)

lemma match_FF_simps [simp]:
  "match_FF\<cdot>FF\<cdot>k = k"
  "match_FF\<cdot>TT\<cdot>k = fail"
  "match_FF\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_FF_def)

subsection \<open>Mutual recursion\<close>

text \<open>
  The following rules are used to prove unfolding theorems from
  fixed-point definitions of mutually recursive functions.
\<close>

lemma Pair_equalI: "\<lbrakk>x \<equiv> fst p; y \<equiv> snd p\<rbrakk> \<Longrightarrow> (x, y) \<equiv> p"
by simp

lemma Pair_eqD1: "(x, y) = (x', y') \<Longrightarrow> x = x'"
by simp

lemma Pair_eqD2: "(x, y) = (x', y') \<Longrightarrow> y = y'"
by simp

lemma def_cont_fix_eq:
  "\<lbrakk>f \<equiv> fix\<cdot>(Abs_cfun F); cont F\<rbrakk> \<Longrightarrow> f = F f"
by (simp, subst fix_eq, simp)

lemma def_cont_fix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>(Abs_cfun F); cont F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F x)\<rbrakk> \<Longrightarrow> P f"
by (simp add: fix_ind)

text \<open>lemma for proving rewrite rules\<close>

lemma ssubst_lhs: "\<lbrakk>t = s; P s = Q\<rbrakk> \<Longrightarrow> P t = Q"
by simp


subsection \<open>Initializing the fixrec package\<close>

ML_file \<open>Tools/holcf_library.ML\<close>
ML_file \<open>Tools/fixrec.ML\<close>

method_setup fixrec_simp = \<open>
  Scan.succeed (SIMPLE_METHOD' o Fixrec.fixrec_simp_tac)
\<close> "pattern prover for fixrec constants"

setup \<open>
  Fixrec.add_matchers
    [ (\<^const_name>\<open>up\<close>, \<^const_name>\<open>match_up\<close>),
      (\<^const_name>\<open>sinl\<close>, \<^const_name>\<open>match_sinl\<close>),
      (\<^const_name>\<open>sinr\<close>, \<^const_name>\<open>match_sinr\<close>),
      (\<^const_name>\<open>spair\<close>, \<^const_name>\<open>match_spair\<close>),
      (\<^const_name>\<open>Pair\<close>, \<^const_name>\<open>match_Pair\<close>),
      (\<^const_name>\<open>ONE\<close>, \<^const_name>\<open>match_ONE\<close>),
      (\<^const_name>\<open>TT\<close>, \<^const_name>\<open>match_TT\<close>),
      (\<^const_name>\<open>FF\<close>, \<^const_name>\<open>match_FF\<close>),
      (\<^const_name>\<open>bottom\<close>, \<^const_name>\<open>match_bottom\<close>) ]
\<close>

hide_const (open) succeed fail run

end
