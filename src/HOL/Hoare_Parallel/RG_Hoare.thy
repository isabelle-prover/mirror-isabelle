section \<open>The Proof System\<close>

theory RG_Hoare imports RG_Tran begin

subsection \<open>Proof System for Component Programs\<close>

declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

definition stable :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "stable \<equiv> \<lambda>f g. (\<forall>x y. x \<in> f \<longrightarrow> (x, y) \<in> g \<longrightarrow> y \<in> f)"

inductive
  rghoare :: "['a com, 'a set, ('a \<times> 'a) set, ('a \<times> 'a) set, 'a set] \<Rightarrow> bool"
    (\<open>\<turnstile> _ sat [_, _, _, _]\<close> [60,0,0,0,0] 45)
where
  Basic: "\<lbrakk> pre \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> pre \<and> (t=f s \<or> t=s)} \<subseteq> guar;
            stable pre rely; stable post rely \<rbrakk>
           \<Longrightarrow> \<turnstile> Basic f sat [pre, rely, guar, post]"

| Seq: "\<lbrakk> \<turnstile> P sat [pre, rely, guar, mid]; \<turnstile> Q sat [mid, rely, guar, post] \<rbrakk>
           \<Longrightarrow> \<turnstile> Seq P Q sat [pre, rely, guar, post]"

| Cond: "\<lbrakk> stable pre rely; \<turnstile> P1 sat [pre \<inter> b, rely, guar, post];
           \<turnstile> P2 sat [pre \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile> Cond b P1 P2 sat [pre, rely, guar, post]"

| While: "\<lbrakk> stable pre rely; (pre \<inter> -b) \<subseteq> post; stable post rely;
            \<turnstile> P sat [pre \<inter> b, rely, guar, pre]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile> While b P sat [pre, rely, guar, post]"

| Await: "\<lbrakk> stable pre rely; stable post rely;
            \<forall>V. \<turnstile> P sat [pre \<inter> b \<inter> {V}, {(s, t). s = t},
                UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
           \<Longrightarrow> \<turnstile> Await b P sat [pre, rely, guar, post]"

| Conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
             \<turnstile> P sat [pre', rely', guar', post'] \<rbrakk>
            \<Longrightarrow> \<turnstile> P sat [pre, rely, guar, post]"

definition Pre :: "'a rgformula \<Rightarrow> 'a set" where
  "Pre x \<equiv> fst(snd x)"

definition Post :: "'a rgformula \<Rightarrow> 'a set" where
  "Post x \<equiv> snd(snd(snd(snd x)))"

definition Rely :: "'a rgformula \<Rightarrow> ('a \<times> 'a) set" where
  "Rely x \<equiv> fst(snd(snd x))"

definition Guar :: "'a rgformula \<Rightarrow> ('a \<times> 'a) set" where
  "Guar x \<equiv> fst(snd(snd(snd x)))"

definition Com :: "'a rgformula \<Rightarrow> 'a com" where
  "Com x \<equiv> fst x"

subsection \<open>Proof System for Parallel Programs\<close>

type_synonym 'a par_rgformula =
  "('a rgformula) list \<times> 'a set \<times> ('a \<times> 'a) set \<times> ('a \<times> 'a) set \<times> 'a set"

inductive
  par_rghoare :: "('a rgformula) list \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> bool"
    (\<open>\<turnstile> _ SAT [_, _, _, _]\<close> [60,0,0,0,0] 45)
where
  Parallel:
  "\<lbrakk> \<forall>i<length xs. rely \<union> (\<Union>j\<in>{j. j<length xs \<and> j\<noteq>i}. Guar(xs!j)) \<subseteq> Rely(xs!i);
    (\<Union>j\<in>{j. j<length xs}. Guar(xs!j)) \<subseteq> guar;
     pre \<subseteq> (\<Inter>i\<in>{i. i<length xs}. Pre(xs!i));
    (\<Inter>i\<in>{i. i<length xs}. Post(xs!i)) \<subseteq> post;
    \<forall>i<length xs. \<turnstile> Com(xs!i) sat [Pre(xs!i),Rely(xs!i),Guar(xs!i),Post(xs!i)] \<rbrakk>
   \<Longrightarrow>  \<turnstile> xs SAT [pre, rely, guar, post]"

section \<open>Soundness\<close>

subsubsection \<open>Some previous lemmas\<close>

lemma tl_of_assum_in_assum:
  "(P, s) # (P, t) # xs \<in> assum (pre, rely) \<Longrightarrow> stable pre rely
  \<Longrightarrow> (P, t) # xs \<in> assum (pre, rely)"
apply(simp add:assum_def)
apply clarify
apply(rule conjI)
 apply(erule_tac x=0 in allE)
 apply(simp (no_asm_use)only:stable_def)
 apply(erule allE,erule allE,erule impE,assumption,erule mp)
 apply(simp add:Env)
apply clarify
apply(erule_tac x="Suc i" in allE)
apply simp
done

lemma etran_in_comm:
  "(P, t) # xs \<in> comm(guar, post) \<Longrightarrow> (P, s) # (P, t) # xs \<in> comm(guar, post)"
apply(simp add:comm_def)
apply clarify
apply(case_tac i,simp+)
done

lemma ctran_in_comm:
  "\<lbrakk>(s, s) \<in> guar; (Q, s) # xs \<in> comm(guar, post)\<rbrakk>
  \<Longrightarrow> (P, s) # (Q, s) # xs \<in> comm(guar, post)"
apply(simp add:comm_def)
apply clarify
apply(case_tac i,simp+)
done

lemma takecptn_is_cptn [rule_format, elim!]:
  "\<forall>j. c \<in> cptn \<longrightarrow> take (Suc j) c \<in> cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j)
 apply simp
 apply(rule CptnOne)
apply simp
apply(force intro:cptn.intros elim:cptn.cases)
done

lemma dropcptn_is_cptn [rule_format,elim!]:
  "\<forall>j<length c. c \<in> cptn \<longrightarrow> drop j c \<in> cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule cptn.cases)
  apply simp
 apply force
apply force
done

lemma takepar_cptn_is_par_cptn [rule_format,elim]:
  "\<forall>j. c \<in> par_cptn \<longrightarrow> take (Suc j) c \<in> par_cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j,simp)
 apply(rule ParCptnOne)
apply(force intro:par_cptn.intros elim:par_cptn.cases)
done

lemma droppar_cptn_is_par_cptn [rule_format]:
  "\<forall>j<length c. c \<in> par_cptn \<longrightarrow> drop j c \<in> par_cptn"
apply(induct "c")
 apply(force elim: par_cptn.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule par_cptn.cases)
  apply simp
 apply force
apply force
done

lemma tl_of_cptn_is_cptn: "\<lbrakk>x # xs \<in> cptn; xs \<noteq> []\<rbrakk> \<Longrightarrow> xs  \<in> cptn"
apply(subgoal_tac "1 < length (x # xs)")
 apply(drule dropcptn_is_cptn,simp+)
done

lemma not_ctran_None [rule_format]:
  "\<forall>s. (None, s)#xs \<in> cptn \<longrightarrow> (\<forall>i<length xs. ((None, s)#xs)!i -e\<rightarrow> xs!i)"
apply(induct xs,simp+)
apply clarify
apply(erule cptn.cases,simp)
 apply simp
 apply(case_tac i,simp)
  apply(rule Env)
 apply simp
apply(force elim:ctran.cases)
done

lemma cptn_not_empty [simp]:"[] \<notin> cptn"
apply(force elim:cptn.cases)
done

lemma etran_or_ctran [rule_format]:
  "\<forall>m i. x\<in>cptn \<longrightarrow> m \<le> length x
   \<longrightarrow> (\<forall>i. Suc i < m \<longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i) \<longrightarrow> Suc i < m
   \<longrightarrow> x!i -e\<rightarrow> x!Suc i"
  supply [[simproc del: defined_all]]
apply(induct x,simp)
apply clarify
apply(erule cptn.cases,simp)
 apply(case_tac i,simp)
  apply(rule Env)
 apply simp
 apply(erule_tac x="m - 1" in allE)
 apply(case_tac m,simp,simp)
 apply(subgoal_tac "(\<forall>i. Suc i < nata \<longrightarrow> (((P, t) # xs) ! i, xs ! i) \<notin> ctran)")
  apply force
 apply clarify
   apply(erule_tac x="Suc ia" in allE,simp)
apply(erule_tac x="0" and P="\<lambda>j. H j \<longrightarrow> (J j) \<notin> ctran" for H J in allE,simp)
done

lemma etran_or_ctran2 [rule_format]:
  "\<forall>i. Suc i<length x \<longrightarrow> x\<in>cptn \<longrightarrow> (x!i -c\<rightarrow> x!Suc i \<longrightarrow> \<not> x!i -e\<rightarrow> x!Suc i)
  \<or> (x!i -e\<rightarrow> x!Suc i \<longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i)"
apply(induct x)
 apply simp
apply clarify
apply(erule cptn.cases,simp)
 apply(case_tac i,simp+)
apply(case_tac i,simp)
 apply(force elim:etran.cases)
apply simp
done

lemma etran_or_ctran2_disjI1:
  "\<lbrakk> x\<in>cptn; Suc i<length x; x!i -c\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> \<not> x!i -e\<rightarrow> x!Suc i"
by(drule etran_or_ctran2,simp_all)

lemma etran_or_ctran2_disjI2:
  "\<lbrakk> x\<in>cptn; Suc i<length x; x!i -e\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> \<not> x!i -c\<rightarrow> x!Suc i"
by(drule etran_or_ctran2,simp_all)

lemma not_ctran_None2 [rule_format]:
  "\<lbrakk> (None, s) # xs \<in>cptn; i<length xs\<rbrakk> \<Longrightarrow> \<not> ((None, s) # xs) ! i -c\<rightarrow> xs ! i"
apply(frule not_ctran_None,simp)
apply(case_tac i,simp)
 apply(force elim:etranE)
apply simp
apply(rule etran_or_ctran2_disjI2,simp_all)
apply(force intro:tl_of_cptn_is_cptn)
done

lemma Ex_first_occurrence [rule_format]: "P (n::nat) \<longrightarrow> (\<exists>m. P m \<and> (\<forall>i<m. \<not> P i))"
apply(rule nat_less_induct)
apply clarify
apply(case_tac "\<forall>m. m<n \<longrightarrow> \<not> P m")
apply auto
done

lemma stability [rule_format]:
  "\<forall>j k. x \<in> cptn \<longrightarrow> stable p rely \<longrightarrow> j\<le>k \<longrightarrow> k<length x \<longrightarrow> snd(x!j)\<in>p  \<longrightarrow>
  (\<forall>i. (Suc i)<length x \<longrightarrow>
          (x!i -e\<rightarrow> x!(Suc i)) \<longrightarrow> (snd(x!i), snd(x!(Suc i))) \<in> rely) \<longrightarrow>
  (\<forall>i. j\<le>i \<and> i<k \<longrightarrow> x!i -e\<rightarrow> x!Suc i) \<longrightarrow> snd(x!k)\<in>p \<and> fst(x!j)=fst(x!k)"
  supply [[simproc del: defined_all]]
apply(induct x)
 apply clarify
 apply(force elim:cptn.cases)
apply clarify
apply(erule cptn.cases,simp)
 apply simp
 apply(case_tac k,simp,simp)
 apply(case_tac j,simp)
  apply(erule_tac x=0 in allE)
  apply(erule_tac x="nat" and P="\<lambda>j. (0\<le>j) \<longrightarrow> (J j)" for J in allE,simp)
  apply(subgoal_tac "t\<in>p")
   apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((P, t) # xs) ! i -e\<rightarrow> xs ! i \<longrightarrow> (snd (((P, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
    apply clarify
    apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>etran" for H J in allE,simp)
   apply clarify
   apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
  apply(erule_tac x=0 and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>etran \<longrightarrow> T j" for H J T in allE,simp)
  apply(simp(no_asm_use) only:stable_def)
  apply(erule_tac x=s in allE)
  apply(erule_tac x=t in allE)
  apply simp
  apply(erule mp)
  apply(erule mp)
  apply(rule Env)
 apply simp
 apply(erule_tac x="nata" in allE)
 apply(erule_tac x="nat" and P="\<lambda>j. (s\<le>j) \<longrightarrow> (J j)" for s J in allE,simp)
 apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((P, t) # xs) ! i -e\<rightarrow> xs ! i \<longrightarrow> (snd (((P, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
  apply clarify
  apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>etran" for H J in allE,simp)
 apply clarify
 apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
apply(case_tac k,simp,simp)
apply(case_tac j)
 apply(erule_tac x=0 and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>etran" for H J in allE,simp)
 apply(erule etran.cases,simp)
apply(erule_tac x="nata" in allE)
apply(erule_tac x="nat" and P="\<lambda>j. (s\<le>j) \<longrightarrow> (J j)" for s J in allE,simp)
apply(subgoal_tac "(\<forall>i. i < length xs \<longrightarrow> ((Q, t) # xs) ! i -e\<rightarrow> xs ! i \<longrightarrow> (snd (((Q, t) # xs) ! i), snd (xs ! i)) \<in> rely)")
 apply clarify
 apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j)\<in>etran" for H J in allE,simp)
apply clarify
apply(erule_tac x="Suc i" and P="\<lambda>j. (H j) \<longrightarrow> (J j) \<longrightarrow> (T j)\<in>rely" for H J T in allE,simp)
done

subsection \<open>Soundness of the System for Component Programs\<close>

subsubsection \<open>Soundness of the Basic rule\<close>

lemma unique_ctran_Basic [rule_format]:
  "\<forall>s i. x \<in> cptn \<longrightarrow> x ! 0 = (Some (Basic f), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -e\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cptn.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule Env)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ctran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (Basic f), sa), Q, t) \<in> ctran" for sa Q t)
apply simp
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule etranE,simp)
done

lemma exists_ctran_Basic_None [rule_format]:
  "\<forall>s i. x \<in> cptn \<longrightarrow> x ! 0 = (Some (Basic f), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp)
apply simp
apply clarify
apply(erule cptn.cases,simp)
 apply(case_tac i,simp,simp)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
done

lemma Basic_sound:
  " \<lbrakk>pre \<subseteq> {s. f s \<in> post}; {(s, t). s \<in> pre \<and> t = f s} \<subseteq> guar;
  stable pre rely; stable post rely\<rbrakk>
  \<Longrightarrow> \<Turnstile> Basic f sat [pre, rely, guar, post]"
  supply [[simproc del: defined_all]]
apply(unfold com_validity_def)
apply clarify
apply(simp add:comm_def)
apply(rule conjI)
 apply clarify
 apply(simp add:cp_def assum_def)
 apply clarify
 apply(frule_tac j=0 and k=i and p=pre in stability)
       apply simp_all
   apply(erule_tac x=ia in allE,simp)
  apply(erule_tac i=i and f=f in unique_ctran_Basic,simp_all)
 apply(erule subsetD,simp)
 apply(case_tac "x!i")
 apply clarify
 apply(drule_tac s="Some (Basic f)" in sym,simp)
 apply(thin_tac "\<forall>j. H j" for H)
 apply(force elim:ctran.cases)
apply clarify
apply(simp add:cp_def)
apply clarify
apply(frule_tac i="length x - 1" and f=f in exists_ctran_Basic_None,simp+)
  apply(case_tac x,simp+)
  apply(rule last_fst_esp,simp add:last_length)
 apply (case_tac x,simp+)
apply(simp add:assum_def)
apply clarify
apply(frule_tac j=0 and k="j" and p=pre in stability)
      apply simp_all
  apply(erule_tac x=i in allE,simp)
 apply(erule_tac i=j and f=f in unique_ctran_Basic,simp_all)
apply(case_tac "x!j")
apply clarify
apply simp
apply(drule_tac s="Some (Basic f)" in sym,simp)
apply(case_tac "x!Suc j",simp)
apply(rule ctran.cases,simp)
apply(simp_all)
apply(drule_tac c=sa in subsetD,simp)
apply clarify
apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
 apply(case_tac x,simp+)
 apply(erule_tac x=i in allE)
apply(erule_tac i=j and f=f in unique_ctran_Basic,simp_all)
  apply arith+
apply(case_tac x)
apply(simp add:last_length)+
done

subsubsection\<open>Soundness of the Await rule\<close>

lemma unique_ctran_Await [rule_format]:
  "\<forall>s i. x \<in> cptn \<longrightarrow> x ! 0 = (Some (Await b c), s) \<longrightarrow>
  Suc i<length x \<longrightarrow> x!i -c\<rightarrow> x!Suc i \<longrightarrow>
  (\<forall>j. Suc j<length x \<longrightarrow> i\<noteq>j \<longrightarrow> x!j -e\<rightarrow> x!Suc j)"
apply(induct x,simp+)
apply clarify
apply(erule cptn.cases,simp)
 apply(case_tac i,simp+)
 apply clarify
 apply(case_tac j,simp)
  apply(rule Env)
 apply simp
apply clarify
apply simp
apply(case_tac i)
 apply(case_tac j,simp,simp)
 apply(erule ctran.cases,simp_all)
 apply(force elim: not_ctran_None)
apply(ind_cases "((Some (Await b c), sa), Q, t) \<in> ctran" for sa Q t,simp)
apply(drule_tac i=nat in not_ctran_None,simp)
apply(erule etranE,simp)
done

lemma exists_ctran_Await_None [rule_format]:
  "\<forall>s i.  x \<in> cptn \<longrightarrow> x ! 0 = (Some (Await b c), s)
  \<longrightarrow> i<length x \<longrightarrow> fst(x!i)=None \<longrightarrow> (\<exists>j<i. x!j -c\<rightarrow> x!Suc j)"
apply(induct x,simp+)
apply clarify
apply(erule cptn.cases,simp)
 apply(case_tac i,simp+)
 apply(erule_tac x=nat in allE,simp)
 apply clarify
 apply(rule_tac x="Suc j" in exI,simp,simp)
apply clarify
apply(case_tac i,simp,simp)
apply(rule_tac x=0 in exI,simp)
done

lemma Star_imp_cptn:
  "(P, s) -c*\<rightarrow> (R, t) \<Longrightarrow> \<exists>l \<in> cp P s. (last l)=(R, t)
  \<and> (\<forall>i. Suc i<length l \<longrightarrow> l!i -c\<rightarrow> l!Suc i)"
apply (erule converse_rtrancl_induct2)
 apply(rule_tac x="[(R,t)]" in bexI)
  apply simp
 apply(simp add:cp_def)
 apply(rule CptnOne)
apply clarify
apply(rule_tac x="(a, b)#l" in bexI)
 apply (rule conjI)
  apply(case_tac l,simp add:cp_def)
  apply(simp add:last_length)
 apply clarify
apply(case_tac i,simp)
apply(simp add:cp_def)
apply force
apply(simp add:cp_def)
 apply(case_tac l)
 apply(force elim:cptn.cases)
apply simp
apply(erule CptnComp)
apply clarify
done

lemma Await_sound:
  "\<lbrakk>stable pre rely; stable post rely;
  \<forall>V. \<turnstile> P sat [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<and>
  \<Turnstile> P sat [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
  \<Longrightarrow> \<Turnstile> Await b P sat [pre, rely, guar, post]"
apply(unfold com_validity_def)
apply clarify
apply(simp add:comm_def)
apply(rule conjI)
 apply clarify
 apply(simp add:cp_def assum_def)
 apply clarify
 apply(frule_tac j=0 and k=i and p=pre in stability,simp_all)
   apply(erule_tac x=ia in allE,simp)
  apply(subgoal_tac "x\<in> cp (Some(Await b P)) s")
  apply(erule_tac i=i in unique_ctran_Await,force,simp_all)
  apply(simp add:cp_def)
\<comment> \<open>here starts the different part.\<close>
 apply(erule ctran.cases,simp_all)
 apply(drule Star_imp_cptn)
 apply clarify
 apply(erule_tac x=sa in allE)
 apply clarify
 apply(erule_tac x=sa in allE)
 apply(drule_tac c=l in subsetD)
  apply (simp add:cp_def)
  apply clarify
  apply(erule_tac x=ia and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ctran" for H J I in allE,simp)
  apply(erule etranE,simp)
 apply simp
apply clarify
apply(simp add:cp_def)
apply clarify
apply(frule_tac i="length x - 1" in exists_ctran_Await_None,force)
  apply (case_tac x,simp+)
 apply(rule last_fst_esp,simp add:last_length)
 apply(case_tac x, simp+)
apply clarify
apply(simp add:assum_def)
apply clarify
apply(frule_tac j=0 and k="j" and p=pre in stability,simp_all)
  apply(erule_tac x=i in allE,simp)
 apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
apply(case_tac "x!j")
apply clarify
apply simp
apply(drule_tac s="Some (Await b P)" in sym,simp)
apply(case_tac "x!Suc j",simp)
apply(rule ctran.cases,simp)
apply(simp_all)
apply(drule Star_imp_cptn)
apply clarify
apply(erule_tac x=sa in allE)
apply clarify
apply(erule_tac x=sa in allE)
apply(drule_tac c=l in subsetD)
 apply (simp add:cp_def)
 apply clarify
 apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ctran" for H J I in allE,simp)
 apply(erule etranE,simp)
apply simp
apply clarify
apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
 apply(case_tac x,simp+)
 apply(erule_tac x=i in allE)
apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
 apply arith+
apply(case_tac x)
apply(simp add:last_length)+
done

subsubsection\<open>Soundness of the Conditional rule\<close>

lemma Cond_sound:
  "\<lbrakk> stable pre rely; \<Turnstile> P1 sat [pre \<inter> b, rely, guar, post];
  \<Turnstile> P2 sat [pre \<inter> - b, rely, guar, post]; \<forall>s. (s,s)\<in>guar\<rbrakk>
  \<Longrightarrow> \<Turnstile> (Cond b P1 P2) sat [pre, rely, guar, post]"
apply(unfold com_validity_def)
apply clarify
apply(simp add:cp_def comm_def)
apply(case_tac "\<exists>i. Suc i<length x \<and> x!i -c\<rightarrow> x!Suc i")
 prefer 2
 apply simp
 apply clarify
 apply(frule_tac j="0" and k="length x - 1" and p=pre in stability,simp+)
     apply(case_tac x,simp+)
    apply(simp add:assum_def)
   apply(simp add:assum_def)
  apply(erule_tac m="length x" in etran_or_ctran,simp+)
 apply(case_tac x, (simp add:last_length)+)
apply(erule exE)
apply(drule_tac n=i and P="\<lambda>i. H i \<and> (J i, I i) \<in> ctran" for H J I in Ex_first_occurrence)
apply clarify
apply (simp add:assum_def)
apply(frule_tac j=0 and k="m" and p=pre in stability,simp+)
 apply(erule_tac m="Suc m" in etran_or_ctran,simp+)
apply(erule ctran.cases,simp_all)
 apply(erule_tac x="sa" in allE)
 apply(drule_tac c="drop (Suc m) x" in subsetD)
  apply simp
  apply clarify
 apply simp
 apply clarify
 apply(case_tac "i\<le>m")
  apply(drule le_imp_less_or_eq)
  apply(erule disjE)
   apply(erule_tac x=i in allE, erule impE, assumption)
   apply simp+
 apply(erule_tac x="i - (Suc m)" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> (I j)\<in>guar" for H J I in allE)
 apply(subgoal_tac "(Suc m)+(i - Suc m) \<le> length x")
  apply(subgoal_tac "(Suc m)+Suc (i - Suc m) \<le> length x")
   apply(rotate_tac -2)
   apply simp
  apply arith
 apply arith
apply(case_tac "length (drop (Suc m) x)",simp)
apply(erule_tac x="sa" in allE)
back
apply(drule_tac c="drop (Suc m) x" in subsetD,simp)
 apply clarify
apply simp
apply clarify
apply(case_tac "i\<le>m")
 apply(drule le_imp_less_or_eq)
 apply(erule disjE)
  apply(erule_tac x=i in allE, erule impE, assumption)
  apply simp
 apply simp
apply(erule_tac x="i - (Suc m)" and P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> (I j)\<in>guar" for H J I in allE)
apply(subgoal_tac "(Suc m)+(i - Suc m) \<le> length x")
 apply(subgoal_tac "(Suc m)+Suc (i - Suc m) \<le> length x")
  apply(rotate_tac -2)
  apply simp
 apply arith
apply arith
done

subsubsection\<open>Soundness of the Sequential rule\<close>

inductive_cases Seq_cases [elim!]: "(Some (Seq P Q), s) -c\<rightarrow> t"

lemma last_lift_not_None: "fst ((lift Q) ((x#xs)!(length xs))) \<noteq> None"
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
done

lemma Seq_sound1 [rule_format]:
  "x\<in> cptn_mod \<Longrightarrow> \<forall>s P. x !0=(Some (Seq P Q), s) \<longrightarrow>
  (\<forall>i<length x. fst(x!i)\<noteq>Some Q) \<longrightarrow>
  (\<exists>xs\<in> cp (Some P) s. x=map (lift Q) xs)"
  supply [[simproc del: defined_all]]
apply(erule cptn_mod.induct)
apply(unfold cp_def)
apply safe
apply simp_all
    apply(simp add:lift_def)
    apply(rule_tac x="[(Some Pa, sa)]" in exI,simp add:CptnOne)
   apply(subgoal_tac "(\<forall>i < Suc (length xs). fst (((Some (Seq Pa Q), t) # xs) ! i) \<noteq> Some Q)")
    apply clarify
    apply(rule_tac x="(Some Pa, sa) #(Some Pa, t) # zs" in exI,simp)
    apply(rule conjI,erule CptnEnv)
    apply(simp (no_asm_use) add:lift_def)
   apply clarify
   apply(erule_tac x="Suc i" in allE, simp)
  apply(ind_cases "((Some (Seq Pa Q), sa), None, t) \<in> ctran" for Pa sa t)
 apply(rule_tac x="(Some P, sa) # xs" in exI, simp add:cptn_iff_cptn_mod lift_def)
apply(erule_tac x="length xs" in allE, simp)
apply(simp only:Cons_lift_append)
apply(subgoal_tac "length xs < length ((Some P, sa) # xs)")
 apply(simp only :nth_append length_map last_length nth_map)
 apply(case_tac "last((Some P, sa) # xs)")
 apply(simp add:lift_def)
apply simp
done

lemma Seq_sound2 [rule_format]:
  "x \<in> cptn \<Longrightarrow> \<forall>s P i. x!0=(Some (Seq P Q), s) \<longrightarrow> i<length x
  \<longrightarrow> fst(x!i)=Some Q \<longrightarrow>
  (\<forall>j<i. fst(x!j)\<noteq>(Some Q)) \<longrightarrow>
  (\<exists>xs ys. xs \<in> cp (Some P) s \<and> length xs=Suc i
   \<and> ys \<in> cp (Some Q) (snd(xs !i)) \<and> x=(map (lift Q) xs)@tl ys)"
  supply [[simproc del: defined_all]]
apply(erule cptn.induct)
apply(unfold cp_def)
apply safe
apply simp_all
 apply(case_tac i,simp+)
 apply(erule allE,erule impE,assumption,simp)
 apply clarify
 apply(subgoal_tac "(\<forall>j < nat. fst (((Some (Seq Pa Q), t) # xs) ! j) \<noteq> Some Q)",clarify)
  prefer 2
  apply force
 apply(case_tac xsa,simp,simp)
 apply(rename_tac list)
 apply(rule_tac x="(Some Pa, sa) #(Some Pa, t) # list" in exI,simp)
 apply(rule conjI,erule CptnEnv)
 apply(simp (no_asm_use) add:lift_def)
 apply(rule_tac x=ys in exI,simp)
apply(ind_cases "((Some (Seq Pa Q), sa), t) \<in> ctran" for Pa sa t)
 apply simp
 apply(rule_tac x="(Some Pa, sa)#[(None, ta)]" in exI,simp)
 apply(rule conjI)
  apply(drule_tac xs="[]" in CptnComp,force simp add:CptnOne,simp)
 apply(case_tac i, simp+)
 apply(case_tac nat,simp+)
 apply(rule_tac x="(Some Q,ta)#xs" in exI,simp add:lift_def)
 apply(case_tac nat,simp+)
 apply(force)
apply(case_tac i, simp+)
apply(case_tac nat,simp+)
apply(erule_tac x="Suc nata" in allE,simp)
apply clarify
apply(subgoal_tac "(\<forall>j<Suc nata. fst (((Some (Seq P2 Q), ta) # xs) ! j) \<noteq> Some Q)",clarify)
 prefer 2
 apply clarify
 apply force
apply(rule_tac x="(Some Pa, sa)#(Some P2, ta)#(tl xsa)" in exI,simp)
apply(rule conjI,erule CptnComp)
apply(rule nth_tl_if,force,simp+)
apply(rule_tac x=ys in exI,simp)
apply(rule conjI)
apply(rule nth_tl_if,force,simp+)
 apply(rule tl_zero,simp+)
 apply force
apply(rule conjI,simp add:lift_def)
apply(subgoal_tac "lift Q (Some P2, ta) =(Some (Seq P2 Q), ta)")
 apply(simp add:Cons_lift del:list.map)
 apply(rule nth_tl_if)
   apply force
  apply simp+
apply(simp add:lift_def)
done
(*
lemma last_lift_not_None3: "fst (last (map (lift Q) (x#xs))) \<noteq> None"
apply(simp only:last_length [THEN sym])
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
done
*)

lemma last_lift_not_None2: "fst ((lift Q) (last (x#xs))) \<noteq> None"
apply(simp only:last_length [THEN sym])
apply(subgoal_tac "length xs<length (x # xs)")
 apply(drule_tac Q=Q in  lift_nth)
 apply(erule ssubst)
 apply (simp add:lift_def)
 apply(case_tac "(x # xs) ! length xs",simp)
apply simp
done

lemma Seq_sound:
  "\<lbrakk>\<Turnstile> P sat [pre, rely, guar, mid]; \<Turnstile> Q sat [mid, rely, guar, post]\<rbrakk>
  \<Longrightarrow> \<Turnstile> Seq P Q sat [pre, rely, guar, post]"
apply(unfold com_validity_def)
apply clarify
apply(case_tac "\<exists>i<length x. fst(x!i)=Some Q")
 prefer 2
 apply (simp add:cp_def cptn_iff_cptn_mod)
 apply clarify
 apply(frule_tac Seq_sound1,force)
  apply force
 apply clarify
 apply(erule_tac x=s in allE,simp)
 apply(drule_tac c=xs in subsetD,simp add:cp_def cptn_iff_cptn_mod)
  apply(simp add:assum_def)
  apply clarify
  apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
  apply(simp add:snd_lift)
  apply(erule mp)
  apply(force elim:etranE intro:Env simp add:lift_def)
 apply(simp add:comm_def)
 apply(rule conjI)
  apply clarify
  apply(erule_tac P="\<lambda>j. H j \<longrightarrow> J j \<longrightarrow> I j" for H J I in allE,erule impE, assumption)
  apply(simp add:snd_lift)
  apply(erule mp)
  apply(case_tac "(xs!i)")
  apply(case_tac "(xs! Suc i)")
  apply(case_tac "fst(xs!i)")
   apply(erule_tac x=i in allE, simp add:lift_def)
  apply(case_tac "fst(xs!Suc i)")
   apply(force simp add:lift_def)
  apply(force simp add:lift_def)
 apply clarify
 apply(case_tac xs,simp add:cp_def)
 apply clarify
 apply (simp del:list.map)
 apply (rename_tac list)
 apply(subgoal_tac "(map (lift Q) ((a, b) # list))\<noteq>[]")
  apply(drule last_conv_nth)
  apply (simp del:list.map)
  apply(simp only:last_lift_not_None)
 apply simp
\<comment> \<open>\<open>\<exists>i<length x. fst (x ! i) = Some Q\<close>\<close>
apply(erule exE)
apply(drule_tac n=i and P="\<lambda>i. i < length x \<and> fst (x ! i) = Some Q" in Ex_first_occurrence)
apply clarify
apply (simp add:cp_def)
 apply clarify
 apply(frule_tac i=m in Seq_sound2,force)
  apply simp+
apply clarify
apply(simp add:comm_def)
apply(erule_tac x=s in allE)
apply(drule_tac c=xs in subsetD,simp)
 apply(case_tac "xs=[]",simp)
 apply(simp add:cp_def assum_def nth_append)
 apply clarify
 apply(erule_tac x=i in allE)
  back
 apply(simp add:snd_lift)
 apply(erule mp)
 apply(force elim:etranE intro:Env simp add:lift_def)
apply simp
apply clarify
apply(erule_tac x="snd(xs!m)" in allE)
apply(drule_tac c=ys in subsetD,simp add:cp_def assum_def)
 apply(case_tac "xs\<noteq>[]")
 apply(drule last_conv_nth,simp)
 apply(rule conjI)
  apply(erule mp)
  apply(case_tac "xs!m")
  apply(case_tac "fst(xs!m)",simp)
  apply(simp add:lift_def nth_append)
 apply clarify
 apply(erule_tac x="m+i" in allE)
 back
 back
 apply(case_tac ys,(simp add:nth_append)+)
 apply (case_tac i, (simp add:snd_lift)+)
  apply(erule mp)
  apply(case_tac "xs!m")
  apply(force elim:etran.cases intro:Env simp add:lift_def)
 apply simp
apply simp
apply clarify
apply(rule conjI,clarify)
 apply(case_tac "i<m",simp add:nth_append)
  apply(simp add:snd_lift)
  apply(erule allE, erule impE, assumption, erule mp)
  apply(case_tac "(xs ! i)")
  apply(case_tac "(xs ! Suc i)")
  apply(case_tac "fst(xs ! i)",force simp add:lift_def)
  apply(case_tac "fst(xs ! Suc i)")
   apply (force simp add:lift_def)
  apply (force simp add:lift_def)
 apply(erule_tac x="i-m" in allE)
 back
 back
 apply(subgoal_tac "Suc (i - m) < length ys",simp)
  prefer 2
  apply arith
 apply(simp add:nth_append snd_lift)
 apply(rule conjI,clarify)
  apply(subgoal_tac "i=m")
   prefer 2
   apply arith
  apply clarify
  apply(simp add:cp_def)
  apply(rule tl_zero)
    apply(erule mp)
    apply(case_tac "lift Q (xs!m)",simp add:snd_lift)
    apply(case_tac "xs!m",case_tac "fst(xs!m)",simp add:lift_def snd_lift)
     apply(case_tac ys,simp+)
    apply(simp add:lift_def)
   apply simp
  apply force
 apply clarify
 apply(rule tl_zero)
   apply(rule tl_zero)
     apply (subgoal_tac "i-m=Suc(i-Suc m)")
      apply simp
      apply(erule mp)
      apply(case_tac ys,simp+)
   apply force
  apply arith
 apply force
apply clarify
apply(case_tac "(map (lift Q) xs @ tl ys)\<noteq>[]")
 apply(drule last_conv_nth)
 apply(simp add: snd_lift nth_append)
 apply(rule conjI,clarify)
  apply(case_tac ys,simp+)
 apply clarify
 apply(case_tac ys,simp+)
done

subsubsection\<open>Soundness of the While rule\<close>

lemma last_append[rule_format]:
  "\<forall>xs. ys\<noteq>[] \<longrightarrow> ((xs@ys)!(length (xs@ys) - (Suc 0)))=(ys!(length ys - (Suc 0)))"
apply(induct ys)
 apply simp
apply clarify
apply (simp add:nth_append)
done

lemma assum_after_body:
  "\<lbrakk> \<Turnstile> P sat [pre \<inter> b, rely, guar, pre];
  (Some P, s) # xs \<in> cptn_mod; fst (last ((Some P, s) # xs)) = None; s \<in> b;
  (Some (While b P), s) # (Some (Seq P (While b P)), s) #
   map (lift (While b P)) xs @ ys \<in> assum (pre, rely)\<rbrakk>
  \<Longrightarrow> (Some (While b P), snd (last ((Some P, s) # xs))) # ys \<in> assum (pre, rely)"
apply(simp add:assum_def com_validity_def cp_def cptn_iff_cptn_mod)
apply clarify
apply(erule_tac x=s in allE)
apply(drule_tac c="(Some P, s) # xs" in subsetD,simp)
 apply clarify
 apply(erule_tac x="Suc i" in allE)
 apply simp
 apply(simp add:Cons_lift_append nth_append snd_lift del:list.map)
 apply(erule mp)
 apply(erule etranE,simp)
 apply(case_tac "fst(((Some P, s) # xs) ! i)")
  apply(force intro:Env simp add:lift_def)
 apply(force intro:Env simp add:lift_def)
apply(rule conjI)
 apply clarify
 apply(simp add:comm_def last_length)
apply clarify
apply(rule conjI)
 apply(simp add:comm_def)
apply clarify
apply(erule_tac x="Suc(length xs + i)" in allE,simp)
apply(case_tac i, simp add:nth_append Cons_lift_append snd_lift last_conv_nth lift_def split_def)
apply(simp add:Cons_lift_append nth_append snd_lift)
done

lemma While_sound_aux [rule_format]:
  "\<lbrakk> pre \<inter> - b \<subseteq> post; \<Turnstile> P sat [pre \<inter> b, rely, guar, pre]; \<forall>s. (s, s) \<in> guar;
   stable pre rely;  stable post rely; x \<in> cptn_mod \<rbrakk>
  \<Longrightarrow>  \<forall>s xs. x=(Some(While b P),s)#xs \<longrightarrow> x\<in>assum(pre, rely) \<longrightarrow> x \<in> comm (guar, post)"
  supply [[simproc del: defined_all]]
apply(erule cptn_mod.induct)
apply safe
apply (simp_all del:last.simps)
\<comment> \<open>5 subgoals left\<close>
apply(simp add:comm_def)
\<comment> \<open>4 subgoals left\<close>
apply(rule etran_in_comm)
apply(erule mp)
apply(erule tl_of_assum_in_assum,simp)
\<comment> \<open>While-None\<close>
apply(ind_cases "((Some (While b P), s), None, t) \<in> ctran" for s t)
apply(simp add:comm_def)
apply(simp add:cptn_iff_cptn_mod [THEN sym])
apply(rule conjI,clarify)
 apply(force simp add:assum_def)
apply clarify
apply(rule conjI, clarify)
 apply(case_tac i,simp,simp)
 apply(force simp add:not_ctran_None2)
apply(subgoal_tac "\<forall>i. Suc i < length ((None, t) # xs) \<longrightarrow> (((None, t) # xs) ! i, ((None, t) # xs) ! Suc i)\<in> etran")
 prefer 2
 apply clarify
 apply(rule_tac m="length ((None, s) # xs)" in etran_or_ctran,simp+)
 apply(erule not_ctran_None2,simp)
 apply simp+
apply(frule_tac j="0" and k="length ((None, s) # xs) - 1" and p=post in stability,simp+)
   apply(force simp add:assum_def subsetD)
  apply(simp add:assum_def)
  apply clarify
  apply(erule_tac x="i" in allE,simp)
  apply(erule_tac x="Suc i" in allE,simp)
 apply simp
apply clarify
apply (simp add:last_length)
\<comment> \<open>WhileOne\<close>
apply(rule ctran_in_comm,simp)
apply(simp add:Cons_lift del:list.map)
apply(simp add:comm_def del:list.map)
apply(rule conjI)
 apply clarify
 apply(case_tac "fst(((Some P, sa) # xs) ! i)")
  apply(case_tac "((Some P, sa) # xs) ! i")
  apply (simp add:lift_def)
  apply(ind_cases "(Some (While b P), ba) -c\<rightarrow> t" for ba t)
   apply simp
  apply simp
 apply(simp add:snd_lift del:list.map)
 apply(simp only:com_validity_def cp_def cptn_iff_cptn_mod)
 apply(erule_tac x=sa in allE)
 apply(drule_tac c="(Some P, sa) # xs" in subsetD)
  apply (simp add:assum_def del:list.map)
  apply clarify
  apply(erule_tac x="Suc ia" in allE,simp add:snd_lift del:list.map)
  apply(erule mp)
  apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
   apply(erule etranE,simp add:lift_def)
   apply(rule Env)
  apply(erule etranE,simp add:lift_def)
  apply(rule Env)
 apply (simp add:comm_def del:list.map)
 apply clarify
 apply(erule allE,erule impE,assumption)
 apply(erule mp)
 apply(case_tac "((Some P, sa) # xs) ! i")
 apply(case_tac "xs!i")
 apply(simp add:lift_def)
 apply(case_tac "fst(xs!i)")
  apply force
 apply force
\<comment> \<open>last=None\<close>
apply clarify
apply(subgoal_tac "(map (lift (While b P)) ((Some P, sa) # xs))\<noteq>[]")
 apply(drule last_conv_nth)
 apply (simp del:list.map)
 apply(simp only:last_lift_not_None)
apply simp
\<comment> \<open>WhileMore\<close>
apply(rule ctran_in_comm,simp del:last.simps)
\<comment> \<open>metiendo la hipotesis antes de dividir la conclusion.\<close>
apply(subgoal_tac "(Some (While b P), snd (last ((Some P, sa) # xs))) # ys \<in> assum (pre, rely)")
 apply (simp del:last.simps)
 prefer 2
 apply(erule assum_after_body)
  apply (simp del:last.simps)+
\<comment> \<open>lo de antes.\<close>
apply(simp add:comm_def del:list.map last.simps)
apply(rule conjI)
 apply clarify
 apply(simp only:Cons_lift_append)
 apply(case_tac "i<length xs")
  apply(simp add:nth_append del:list.map last.simps)
  apply(case_tac "fst(((Some P, sa) # xs) ! i)")
   apply(case_tac "((Some P, sa) # xs) ! i")
   apply (simp add:lift_def del:last.simps)
   apply(ind_cases "(Some (While b P), ba) -c\<rightarrow> t" for ba t)
    apply simp
   apply simp
  apply(simp add:snd_lift del:list.map last.simps)
  apply(thin_tac " \<forall>i. i < length ys \<longrightarrow> P i" for P)
  apply(simp only:com_validity_def cp_def cptn_iff_cptn_mod)
  apply(erule_tac x=sa in allE)
  apply(drule_tac c="(Some P, sa) # xs" in subsetD)
   apply (simp add:assum_def del:list.map last.simps)
   apply clarify
   apply(erule_tac x="Suc ia" in allE,simp add:nth_append snd_lift del:list.map last.simps, erule mp)
   apply(case_tac "fst(((Some P, sa) # xs) ! ia)")
    apply(erule etranE,simp add:lift_def)
    apply(rule Env)
   apply(erule etranE,simp add:lift_def)
   apply(rule Env)
  apply (simp add:comm_def del:list.map)
  apply clarify
  apply(erule allE,erule impE,assumption)
  apply(erule mp)
  apply(case_tac "((Some P, sa) # xs) ! i")
  apply(case_tac "xs!i")
  apply(simp add:lift_def)
  apply(case_tac "fst(xs!i)")
   apply force
 apply force
\<comment> \<open>\<open>i \<ge> length xs\<close>\<close>
apply(subgoal_tac "i-length xs <length ys")
 prefer 2
 apply arith
apply(erule_tac x="i-length xs" in allE,clarify)
apply(case_tac "i=length xs")
 apply (simp add:nth_append snd_lift del:list.map last.simps)
 apply(simp add:last_length del:last.simps)
 apply(erule mp)
 apply(case_tac "last((Some P, sa) # xs)")
 apply(simp add:lift_def del:last.simps)
\<comment> \<open>\<open>i>length xs\<close>\<close>
apply(case_tac "i-length xs")
 apply arith
apply(simp add:nth_append del:list.map last.simps)
apply(rotate_tac -3)
apply(subgoal_tac "i- Suc (length xs)=nat")
 prefer 2
 apply arith
apply simp
\<comment> \<open>last=None\<close>
apply clarify
apply(case_tac ys)
 apply(simp add:Cons_lift del:list.map last.simps)
 apply(subgoal_tac "(map (lift (While b P)) ((Some P, sa) # xs))\<noteq>[]")
  apply(drule last_conv_nth)
  apply (simp del:list.map)
  apply(simp only:last_lift_not_None)
 apply simp
apply(subgoal_tac "((Some (Seq P (While b P)), sa) # map (lift (While b P)) xs @ ys)\<noteq>[]")
 apply(drule last_conv_nth)
 apply (simp del:list.map last.simps)
 apply(simp add:nth_append del:last.simps)
 apply(rename_tac a list)
 apply(subgoal_tac "((Some (While b P), snd (last ((Some P, sa) # xs))) # a # list)\<noteq>[]")
  apply(drule last_conv_nth)
  apply (simp del:list.map last.simps)
 apply simp
apply simp
done

lemma While_sound:
  "\<lbrakk>stable pre rely; pre \<inter> - b \<subseteq> post; stable post rely;
    \<Turnstile> P sat [pre \<inter> b, rely, guar, pre]; \<forall>s. (s,s)\<in>guar\<rbrakk>
  \<Longrightarrow> \<Turnstile> While b P sat [pre, rely, guar, post]"
apply(unfold com_validity_def)
apply clarify
apply(erule_tac xs="tl x" in While_sound_aux)
 apply(simp add:com_validity_def)
 apply force
 apply simp_all
apply(simp add:cptn_iff_cptn_mod cp_def)
apply(simp add:cp_def)
apply clarify
apply(rule nth_equalityI)
 apply simp_all
 apply(case_tac x,simp+)
apply(case_tac i,simp+)
apply(case_tac x,simp+)
done

subsubsection\<open>Soundness of the Rule of Consequence\<close>

lemma Conseq_sound:
  "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
  \<Turnstile> P sat [pre', rely', guar', post']\<rbrakk>
  \<Longrightarrow> \<Turnstile> P sat [pre, rely, guar, post]"
apply(simp add:com_validity_def assum_def comm_def)
apply clarify
apply(erule_tac x=s in allE)
apply(drule_tac c=x in subsetD)
 apply force
apply force
done

subsubsection \<open>Soundness of the system for sequential component programs\<close>

theorem rgsound:
  "\<turnstile> P sat [pre, rely, guar, post] \<Longrightarrow> \<Turnstile> P sat [pre, rely, guar, post]"
apply(erule rghoare.induct)
 apply(force elim:Basic_sound)
 apply(force elim:Seq_sound)
 apply(force elim:Cond_sound)
 apply(force elim:While_sound)
 apply(force elim:Await_sound)
apply(erule Conseq_sound,simp+)
done

subsection \<open>Soundness of the System for Parallel Programs\<close>

definition ParallelCom :: "('a rgformula) list \<Rightarrow> 'a par_com" where
  "ParallelCom Ps \<equiv> map (Some \<circ> fst) Ps"

lemma two:
  "\<lbrakk> \<forall>i<length xs. rely \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Guar (xs ! j))
     \<subseteq> Rely (xs ! i);
   pre \<subseteq> (\<Inter>i\<in>{i. i < length xs}. Pre (xs ! i));
   \<forall>i<length xs.
   \<Turnstile> Com (xs ! i) sat [Pre (xs ! i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i)];
   length xs=length clist; x \<in> par_cp (ParallelCom xs) s; x\<in>par_assum(pre, rely);
  \<forall>i<length clist. clist!i\<in>cp (Some(Com(xs!i))) s; x \<propto> clist \<rbrakk>
  \<Longrightarrow> \<forall>j i. i<length clist \<and> Suc j<length x \<longrightarrow> (clist!i!j) -c\<rightarrow> (clist!i!Suc j)
  \<longrightarrow> (snd(clist!i!j), snd(clist!i!Suc j)) \<in> Guar(xs!i)"
apply(unfold par_cp_def)
apply (rule ccontr)
\<comment> \<open>By contradiction:\<close>
apply simp
apply(erule exE)
\<comment> \<open>the first c-tran that does not satisfy the guarantee-condition is from \<open>\<sigma>_i\<close> at step \<open>m\<close>.\<close>
apply(drule_tac n=j and P="\<lambda>j. \<exists>i. H i j" for H in Ex_first_occurrence)
apply(erule exE)
apply clarify
\<comment> \<open>\<open>\<sigma>_i \<in> A(pre, rely_1)\<close>\<close>
apply(subgoal_tac "take (Suc (Suc m)) (clist!i) \<in> assum(Pre(xs!i), Rely(xs!i))")
\<comment> \<open>but this contradicts \<open>\<Turnstile> \<sigma>_i sat [pre_i,rely_i,guar_i,post_i]\<close>\<close>
 apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> \<Turnstile> (J i) sat [I i,K i,M i,N i]" for H J I K M N in allE,erule impE,assumption)
 apply(simp add:com_validity_def)
 apply(erule_tac x=s in allE)
 apply(simp add:cp_def comm_def)
 apply(drule_tac c="take (Suc (Suc m)) (clist ! i)" in subsetD)
  apply simp
  apply (blast intro: takecptn_is_cptn)
 apply simp
 apply clarify
 apply(erule_tac x=m and P="\<lambda>j. I j \<and> J j \<longrightarrow> H j" for I J H in allE)
 apply (simp add:conjoin_def same_length_def)
apply(simp add:assum_def)
apply(rule conjI)
 apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> I j \<in>cp (K j) (J j)" for H I K J in allE)
 apply(simp add:cp_def par_assum_def)
 apply(drule_tac c="s" in subsetD,simp)
 apply simp
apply clarify
apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> M \<union> \<Union>((T j) ` (S j)) \<subseteq> (L j)" for H M S T L in allE)
apply simp
apply(erule subsetD)
apply simp
apply(simp add:conjoin_def compat_label_def)
apply clarify
apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (P j) \<or> Q j" for H P Q in allE,simp)
\<comment> \<open>each etran in \<open>\<sigma>_1[0\<dots>m]\<close> corresponds to\<close>
apply(erule disjE)
\<comment> \<open>a c-tran in some \<open>\<sigma>_{ib}\<close>\<close>
 apply clarify
 apply(case_tac "i=ib",simp)
  apply(erule etranE,simp)
 apply(erule_tac x="ib" and P="\<lambda>i. H i \<longrightarrow> (I i) \<or> (J i)" for H I J in allE)
 apply (erule etranE)
 apply(case_tac "ia=m",simp)
 apply simp
 apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (\<forall>i. P i j)" for H P in allE)
 apply(subgoal_tac "ia<m",simp)
  prefer 2
  apply arith
 apply(erule_tac x=ib and P="\<lambda>j. (I j, H j) \<in> ctran \<longrightarrow> P i j" for I H P in allE,simp)
 apply(simp add:same_state_def)
 apply(erule_tac x=i and P="\<lambda>j. (T j) \<longrightarrow> (\<forall>i. (H j i) \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in all_dupE)
 apply(erule_tac x=ib and P="\<lambda>j. (T j) \<longrightarrow> (\<forall>i. (H j i) \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in allE,simp)
\<comment> \<open>or an e-tran in \<open>\<sigma>\<close>,
therefore it satisfies \<open>rely \<or> guar_{ib}\<close>\<close>
apply (force simp add:par_assum_def same_state_def)
done


lemma three [rule_format]:
  "\<lbrakk> xs\<noteq>[]; \<forall>i<length xs. rely \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Guar (xs ! j))
   \<subseteq> Rely (xs ! i);
   pre \<subseteq> (\<Inter>i\<in>{i. i < length xs}. Pre (xs ! i));
   \<forall>i<length xs.
    \<Turnstile> Com (xs ! i) sat [Pre (xs ! i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i)];
   length xs=length clist; x \<in> par_cp (ParallelCom xs) s; x \<in> par_assum(pre, rely);
  \<forall>i<length clist. clist!i\<in>cp (Some(Com(xs!i))) s; x \<propto> clist \<rbrakk>
  \<Longrightarrow> \<forall>j i. i<length clist \<and> Suc j<length x \<longrightarrow> (clist!i!j) -e\<rightarrow> (clist!i!Suc j)
  \<longrightarrow> (snd(clist!i!j), snd(clist!i!Suc j)) \<in> rely \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Guar (xs ! j))"
apply(drule two)
 apply simp_all
apply clarify
apply(simp add:conjoin_def compat_label_def)
apply clarify
apply(erule_tac x=j and P="\<lambda>j. H j \<longrightarrow> (J j \<and> (\<exists>i. P i j)) \<or> I j" for H J P I in allE,simp)
apply(erule disjE)
 prefer 2
 apply(force simp add:same_state_def par_assum_def)
apply clarify
apply(case_tac "i=ia",simp)
 apply(erule etranE,simp)
apply(erule_tac x="ia" and P="\<lambda>i. H i \<longrightarrow> (I i) \<or> (J i)" for H I J in allE,simp)
apply(erule_tac x=j and P="\<lambda>j. \<forall>i. S j i \<longrightarrow> (I j i, H j i) \<in> ctran \<longrightarrow> P i j" for S I H P in allE)
apply(erule_tac x=ia and P="\<lambda>j. S j \<longrightarrow> (I j, H j) \<in> ctran \<longrightarrow> P j" for S I H P in allE)
apply(simp add:same_state_def)
apply(erule_tac x=i and P="\<lambda>j. T j \<longrightarrow> (\<forall>i. H j i \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in all_dupE)
apply(erule_tac x=ia and P="\<lambda>j. T j \<longrightarrow> (\<forall>i. H j i \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in allE,simp)
done

lemma four:
  "\<lbrakk>xs\<noteq>[]; \<forall>i < length xs. rely \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Guar (xs ! j))
    \<subseteq> Rely (xs ! i);
   (\<Union>j\<in>{j. j < length xs}. Guar (xs ! j)) \<subseteq> guar;
   pre \<subseteq> (\<Inter>i\<in>{i. i < length xs}. Pre (xs ! i));
   \<forall>i < length xs.
    \<Turnstile> Com (xs ! i) sat [Pre (xs ! i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i)];
   x \<in> par_cp (ParallelCom xs) s; x \<in> par_assum (pre, rely); Suc i < length x;
   x ! i -pc\<rightarrow> x ! Suc i\<rbrakk>
  \<Longrightarrow> (snd (x ! i), snd (x ! Suc i)) \<in> guar"
apply(simp add: ParallelCom_def)
apply(subgoal_tac "(map (Some \<circ> fst) xs)\<noteq>[]")
 prefer 2
 apply simp
apply(frule rev_subsetD)
 apply(erule one [THEN equalityD1])
apply(erule subsetD)
apply simp
apply clarify
apply(drule_tac pre=pre and rely=rely and  x=x and s=s and xs=xs and clist=clist in two)
apply(assumption+)
     apply(erule sym)
    apply(simp add:ParallelCom_def)
   apply assumption
  apply(simp add:Com_def)
 apply assumption
apply(simp add:conjoin_def same_program_def)
apply clarify
apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> fst(I j)=(J j)" for H I J in all_dupE)
apply(erule_tac x="Suc i" and P="\<lambda>j. H j \<longrightarrow> fst(I j)=(J j)" for H I J in allE)
apply(erule par_ctranE,simp)
apply(erule_tac x=i and P="\<lambda>j. \<forall>i. S j i \<longrightarrow> (I j i, H j i) \<in> ctran \<longrightarrow> P i j" for S I H P in allE)
apply(erule_tac x=ia and P="\<lambda>j. S j \<longrightarrow> (I j, H j) \<in> ctran \<longrightarrow> P j" for S I H P in allE)
apply(rule_tac x=ia in exI)
apply(simp add:same_state_def)
apply(erule_tac x=ia and P="\<lambda>j. T j \<longrightarrow> (\<forall>i. H j i \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in all_dupE,simp)
apply(erule_tac x=ia and P="\<lambda>j. T j \<longrightarrow> (\<forall>i. H j i \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in allE,simp)
apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in all_dupE)
apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in all_dupE,simp)
apply(erule_tac x="Suc i" and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
apply(erule mp)
apply(subgoal_tac "r=fst(clist ! ia ! Suc i)",simp)
apply(drule_tac i=ia in list_eq_if)
back
apply simp_all
done

lemma parcptn_not_empty [simp]:"[] \<notin> par_cptn"
apply(force elim:par_cptn.cases)
done

lemma five:
  "\<lbrakk>xs\<noteq>[]; \<forall>i<length xs. rely \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Guar (xs ! j))
   \<subseteq> Rely (xs ! i);
   pre \<subseteq> (\<Inter>i\<in>{i. i < length xs}. Pre (xs ! i));
   (\<Inter>i\<in>{i. i < length xs}. Post (xs ! i)) \<subseteq> post;
   \<forall>i < length xs.
    \<Turnstile> Com (xs ! i) sat [Pre (xs ! i), Rely (xs ! i), Guar (xs ! i), Post (xs ! i)];
    x \<in> par_cp (ParallelCom xs) s; x \<in> par_assum (pre, rely);
   All_None (fst (last x)) \<rbrakk> \<Longrightarrow> snd (last x) \<in> post"
apply(simp add: ParallelCom_def)
apply(subgoal_tac "(map (Some \<circ> fst) xs)\<noteq>[]")
 prefer 2
 apply simp
apply(frule rev_subsetD)
 apply(erule one [THEN equalityD1])
apply(erule subsetD)
apply simp
apply clarify
apply(subgoal_tac "\<forall>i<length clist. clist!i\<in>assum(Pre(xs!i), Rely(xs!i))")
 apply(erule_tac x=xa and P="\<lambda>i. H i \<longrightarrow> \<Turnstile> (J i) sat [I i,K i,M i,N i]" for H J I K M N in allE,erule impE,assumption)
 apply(simp add:com_validity_def)
 apply(erule_tac x=s in allE)
 apply(erule_tac x=xa and P="\<lambda>j. H j \<longrightarrow> (I j) \<in> cp (J j) s" for H I J in allE,simp)
 apply(drule_tac c="clist!xa" in subsetD)
  apply (force simp add:Com_def)
 apply(simp add:comm_def conjoin_def same_program_def del:last.simps)
 apply clarify
 apply(erule_tac x="length x - 1" and P="\<lambda>j. H j \<longrightarrow> fst(I j)=(J j)" for H I J in allE)
 apply (simp add:All_None_def same_length_def)
 apply(erule_tac x=xa and P="\<lambda>j. H j \<longrightarrow> length(J j)=(K j)" for H J K in allE)
 apply(subgoal_tac "length x - 1 < length x",simp)
  apply(case_tac "x\<noteq>[]")
   apply(simp add: last_conv_nth)
   apply(erule_tac x="clist!xa" in ballE)
    apply(simp add:same_state_def)
    apply(subgoal_tac "clist!xa\<noteq>[]")
     apply(simp add: last_conv_nth)
    apply(case_tac x)
     apply (force simp add:par_cp_def)
    apply (force simp add:par_cp_def)
   apply force
  apply (force simp add:par_cp_def)
 apply(case_tac x)
  apply (force simp add:par_cp_def)
 apply (force simp add:par_cp_def)
apply clarify
apply(simp add:assum_def)
apply(rule conjI)
 apply(simp add:conjoin_def same_state_def par_cp_def)
 apply clarify
 apply(erule_tac x=i and P="\<lambda>j. T j \<longrightarrow> (\<forall>i. H j i \<longrightarrow> (snd (d j i))=(snd (e j i)))" for T H d e in allE,simp)
 apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
 apply(case_tac x,simp+)
 apply (simp add:par_assum_def)
 apply clarify
 apply(drule_tac c="snd (clist ! i ! 0)" in subsetD)
 apply assumption
 apply simp
apply clarify
apply(erule_tac x=i in all_dupE)
apply(rule subsetD, erule mp, assumption)
apply(erule_tac pre=pre and rely=rely and x=x and s=s in  three)
 apply(erule_tac x=ib in allE,erule mp)
 apply simp_all
 apply(simp add:ParallelCom_def)
 apply(force simp add:Com_def)
apply(simp add:conjoin_def same_length_def)
done

lemma ParallelEmpty [rule_format]:
  "\<forall>i s. x \<in> par_cp (ParallelCom []) s \<longrightarrow>
  Suc i < length x \<longrightarrow> (x ! i, x ! Suc i) \<notin> par_ctran"
apply(induct_tac x)
 apply(simp add:par_cp_def ParallelCom_def)
apply clarify
apply(case_tac list,simp,simp)
apply(case_tac i)
 apply(simp add:par_cp_def ParallelCom_def)
 apply(erule par_ctranE,simp)
apply(simp add:par_cp_def ParallelCom_def)
apply clarify
apply(erule par_cptn.cases,simp)
 apply simp
apply(erule par_ctranE)
back
apply simp
done

theorem par_rgsound:
  "\<turnstile> c SAT [pre, rely, guar, post] \<Longrightarrow>
   \<Turnstile> (ParallelCom c) SAT [pre, rely, guar, post]"
apply(erule par_rghoare.induct)
apply(case_tac xs,simp)
 apply(simp add:par_com_validity_def par_comm_def)
 apply clarify
 apply(case_tac "post=UNIV",simp)
  apply clarify
  apply(drule ParallelEmpty)
   apply assumption
  apply simp
 apply clarify
 apply simp
apply(subgoal_tac "xs\<noteq>[]")
 prefer 2
 apply simp
apply(rename_tac a list)
apply(thin_tac "xs = a # list")
apply(simp add:par_com_validity_def par_comm_def)
apply clarify
apply(rule conjI)
 apply clarify
 apply(erule_tac pre=pre and rely=rely and guar=guar and x=x and s=s and xs=xs in four)
        apply(assumption+)
     apply clarify
     apply (erule allE, erule impE, assumption,erule rgsound)
    apply(assumption+)
apply clarify
apply(erule_tac pre=pre and rely=rely and post=post and x=x and s=s and xs=xs in five)
      apply(assumption+)
   apply clarify
   apply (erule allE, erule impE, assumption,erule rgsound)
  apply(assumption+)
done

end
