section \<open>Operational Semantics\<close>

theory RG_Tran
imports RG_Com
begin

subsection \<open>Semantics of Component Programs\<close>

subsubsection \<open>Environment transitions\<close>

type_synonym 'a conf = "(('a com) option) \<times> 'a"

inductive_set
  etran :: "('a conf \<times> 'a conf) set" 
  and etran' :: "'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"  (\<open>_ -e\<rightarrow> _\<close> [81,81] 80)
where
  "P -e\<rightarrow> Q \<equiv> (P,Q) \<in> etran"
| Env: "(P, s) -e\<rightarrow> (P, t)"

lemma etranE: "c -e\<rightarrow> c' \<Longrightarrow> (\<And>P s t. c = (P, s) \<Longrightarrow> c' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct c, induct c', erule etran.cases, blast)

subsubsection \<open>Component transitions\<close>

inductive_set
  ctran :: "('a conf \<times> 'a conf) set"
  and ctran' :: "'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"   (\<open>_ -c\<rightarrow> _\<close> [81,81] 80)
  and ctrans :: "'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"   (\<open>_ -c*\<rightarrow> _\<close> [81,81] 80)
where
  "P -c\<rightarrow> Q \<equiv> (P,Q) \<in> ctran"
| "P -c*\<rightarrow> Q \<equiv> (P,Q) \<in> ctran\<^sup>*"

| Basic:  "(Some(Basic f), s) -c\<rightarrow> (None, f s)"

| Seq1:   "(Some P0, s) -c\<rightarrow> (None, t) \<Longrightarrow> (Some(Seq P0 P1), s) -c\<rightarrow> (Some P1, t)"

| Seq2:   "(Some P0, s) -c\<rightarrow> (Some P2, t) \<Longrightarrow> (Some(Seq P0 P1), s) -c\<rightarrow> (Some(Seq P2 P1), t)"

| CondT: "s\<in>b  \<Longrightarrow> (Some(Cond b P1 P2), s) -c\<rightarrow> (Some P1, s)"
| CondF: "s\<notin>b \<Longrightarrow> (Some(Cond b P1 P2), s) -c\<rightarrow> (Some P2, s)"

| WhileF: "s\<notin>b \<Longrightarrow> (Some(While b P), s) -c\<rightarrow> (None, s)"
| WhileT: "s\<in>b  \<Longrightarrow> (Some(While b P), s) -c\<rightarrow> (Some(Seq P (While b P)), s)"

| Await:  "\<lbrakk>s\<in>b; (Some P, s) -c*\<rightarrow> (None, t)\<rbrakk> \<Longrightarrow> (Some(Await b P), s) -c\<rightarrow> (None, t)" 

monos "rtrancl_mono"

subsection \<open>Semantics of Parallel Programs\<close>

type_synonym 'a par_conf = "('a par_com) \<times> 'a"

inductive_set
  par_etran :: "('a par_conf \<times> 'a par_conf) set"
  and par_etran' :: "['a par_conf,'a par_conf] \<Rightarrow> bool" (\<open>_ -pe\<rightarrow> _\<close> [81,81] 80)
where
  "P -pe\<rightarrow> Q \<equiv> (P,Q) \<in> par_etran"
| ParEnv:  "(Ps, s) -pe\<rightarrow> (Ps, t)"

inductive_set
  par_ctran :: "('a par_conf \<times> 'a par_conf) set"
  and par_ctran' :: "['a par_conf,'a par_conf] \<Rightarrow> bool" (\<open>_ -pc\<rightarrow> _\<close> [81,81] 80)
where
  "P -pc\<rightarrow> Q \<equiv> (P,Q) \<in> par_ctran"
| ParComp: "\<lbrakk>i<length Ps; (Ps!i, s) -c\<rightarrow> (r, t)\<rbrakk> \<Longrightarrow> (Ps, s) -pc\<rightarrow> (Ps[i:=r], t)"

lemma par_ctranE: "c -pc\<rightarrow> c' \<Longrightarrow>
  (\<And>i Ps s r t. c = (Ps, s) \<Longrightarrow> c' = (Ps[i := r], t) \<Longrightarrow> i < length Ps \<Longrightarrow>
     (Ps ! i, s) -c\<rightarrow> (r, t) \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct c, induct c', erule par_ctran.cases, blast)

subsection \<open>Computations\<close>

subsubsection \<open>Sequential computations\<close>

type_synonym 'a confs = "'a conf list"

inductive_set cptn :: "'a confs set"
where
  CptnOne: "[(P,s)] \<in> cptn"
| CptnEnv: "(P, t)#xs \<in> cptn \<Longrightarrow> (P,s)#(P,t)#xs \<in> cptn"
| CptnComp: "\<lbrakk>(P,s) -c\<rightarrow> (Q,t); (Q, t)#xs \<in> cptn \<rbrakk> \<Longrightarrow> (P,s)#(Q,t)#xs \<in> cptn"

definition cp :: "('a com) option \<Rightarrow> 'a \<Rightarrow> ('a confs) set" where
  "cp P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cptn}"  

subsubsection \<open>Parallel computations\<close>

type_synonym 'a par_confs = "'a par_conf list"

inductive_set par_cptn :: "'a par_confs set"
where
  ParCptnOne: "[(P,s)] \<in> par_cptn"
| ParCptnEnv: "(P,t)#xs \<in> par_cptn \<Longrightarrow> (P,s)#(P,t)#xs \<in> par_cptn"
| ParCptnComp: "\<lbrakk> (P,s) -pc\<rightarrow> (Q,t); (Q,t)#xs \<in> par_cptn \<rbrakk> \<Longrightarrow> (P,s)#(Q,t)#xs \<in> par_cptn"

definition par_cp :: "'a par_com \<Rightarrow> 'a \<Rightarrow> ('a par_confs) set" where
  "par_cp P s \<equiv> {l. l!0=(P,s) \<and> l \<in> par_cptn}"  

subsection\<open>Modular Definition of Computation\<close>

definition lift :: "'a com \<Rightarrow> 'a conf \<Rightarrow> 'a conf" where
  "lift Q \<equiv> \<lambda>(P, s). (if P=None then (Some Q,s) else (Some(Seq (the P) Q), s))"

inductive_set cptn_mod :: "('a confs) set"
where
  CptnModOne: "[(P, s)] \<in> cptn_mod"
| CptnModEnv: "(P, t)#xs \<in> cptn_mod \<Longrightarrow> (P, s)#(P, t)#xs \<in> cptn_mod"
| CptnModNone: "\<lbrakk>(Some P, s) -c\<rightarrow> (None, t); (None, t)#xs \<in> cptn_mod \<rbrakk> \<Longrightarrow> (Some P,s)#(None, t)#xs \<in>cptn_mod"
| CptnModCondT: "\<lbrakk>(Some P0, s)#ys \<in> cptn_mod; s \<in> b \<rbrakk> \<Longrightarrow> (Some(Cond b P0 P1), s)#(Some P0, s)#ys \<in> cptn_mod"
| CptnModCondF: "\<lbrakk>(Some P1, s)#ys \<in> cptn_mod; s \<notin> b \<rbrakk> \<Longrightarrow> (Some(Cond b P0 P1), s)#(Some P1, s)#ys \<in> cptn_mod"
| CptnModSeq1: "\<lbrakk>(Some P0, s)#xs \<in> cptn_mod; zs=map (lift P1) xs \<rbrakk>
                 \<Longrightarrow> (Some(Seq P0 P1), s)#zs \<in> cptn_mod"
| CptnModSeq2: 
  "\<lbrakk>(Some P0, s)#xs \<in> cptn_mod; fst(last ((Some P0, s)#xs)) = None; 
  (Some P1, snd(last ((Some P0, s)#xs)))#ys \<in> cptn_mod; 
  zs=(map (lift P1) xs)@ys \<rbrakk> \<Longrightarrow> (Some(Seq P0 P1), s)#zs \<in> cptn_mod"

| CptnModWhile1: 
  "\<lbrakk> (Some P, s)#xs \<in> cptn_mod; s \<in> b; zs=map (lift (While b P)) xs \<rbrakk> 
  \<Longrightarrow> (Some(While b P), s)#(Some(Seq P (While b P)), s)#zs \<in> cptn_mod"
| CptnModWhile2: 
  "\<lbrakk> (Some P, s)#xs \<in> cptn_mod; fst(last ((Some P, s)#xs))=None; s \<in> b; 
  zs=(map (lift (While b P)) xs)@ys; 
  (Some(While b P), snd(last ((Some P, s)#xs)))#ys \<in> cptn_mod\<rbrakk> 
  \<Longrightarrow> (Some(While b P), s)#(Some(Seq P (While b P)), s)#zs \<in> cptn_mod"

subsection \<open>Equivalence of Both Definitions.\<close>

lemma last_length: "((a#xs)!(length xs))=last (a#xs)"
  by (induct xs) auto

lemma div_seq [rule_format]: "list \<in> cptn_mod \<Longrightarrow>
 (\<forall>s P Q zs. list=(Some (Seq P Q), s)#zs \<longrightarrow>
  (\<exists>xs. (Some P, s)#xs \<in> cptn_mod  \<and> (zs=(map (lift Q) xs) \<or>
  ( fst(((Some P, s)#xs)!length xs)=None \<and> 
  (\<exists>ys. (Some Q, snd(((Some P, s)#xs)!length xs))#ys \<in> cptn_mod  
  \<and> zs=(map (lift (Q)) xs)@ys)))))"
apply(erule cptn_mod.induct)
apply simp_all
    apply clarify
    apply(force intro:CptnModOne)
   apply clarify
   apply(erule_tac x=Pa in allE)
   apply(erule_tac x=Q in allE)
   apply simp
   apply clarify
   apply(erule disjE)
    apply(rule_tac x="(Some Pa,t)#xsa" in exI)
    apply(rule conjI)
     apply clarify
     apply(erule CptnModEnv)
    apply(rule disjI1)
    apply(simp add:lift_def)
   apply clarify
   apply(rule_tac x="(Some Pa,t)#xsa" in exI)
   apply(rule conjI)
    apply(erule CptnModEnv)
   apply(rule disjI2)
   apply(rule conjI)
    apply(case_tac xsa,simp,simp)
   apply(rule_tac x="ys" in exI)
   apply(rule conjI)
    apply simp
   apply(simp add:lift_def)
  apply clarify
  apply(erule ctran.cases,simp_all)
 apply clarify
 apply(rule_tac x="xs" in exI)
 apply simp
 apply clarify
apply(rule_tac x="xs" in exI)
apply(simp add: last_length)
done

lemma cptn_onlyif_cptn_mod_aux [rule_format]:
  "\<forall>s Q t xs.((Some a, s), Q, t) \<in> ctran \<longrightarrow> (Q, t) # xs \<in> cptn_mod 
  \<longrightarrow> (Some a, s) # (Q, t) # xs \<in> cptn_mod"
  supply [[simproc del: defined_all]]
apply(induct a)
apply simp_all
\<comment> \<open>basic\<close>
apply clarify
apply(erule ctran.cases,simp_all)
apply(rule CptnModNone,rule Basic,simp)
apply clarify
apply(erule ctran.cases,simp_all)
\<comment> \<open>Seq1\<close>
apply(rule_tac xs="[(None,ta)]" in CptnModSeq2)
  apply(erule CptnModNone)
  apply(rule CptnModOne)
 apply simp
apply simp
apply(simp add:lift_def)
\<comment> \<open>Seq2\<close>
apply(erule_tac x=sa in allE)
apply(erule_tac x="Some P2" in allE)
apply(erule allE,erule impE, assumption)
apply(drule div_seq,simp)
apply clarify
apply(erule disjE)
 apply clarify
 apply(erule allE,erule impE, assumption)
 apply(erule_tac CptnModSeq1)
 apply(simp add:lift_def)
apply clarify 
apply(erule allE,erule impE, assumption)
apply(erule_tac CptnModSeq2)
  apply (simp add:last_length)
 apply (simp add:last_length)
apply(simp add:lift_def)
\<comment> \<open>Cond\<close>
apply clarify
apply(erule ctran.cases,simp_all)
apply(force elim: CptnModCondT)
apply(force elim: CptnModCondF)
\<comment> \<open>While\<close>
apply  clarify
apply(erule ctran.cases,simp_all)
apply(rule CptnModNone,erule WhileF,simp)
apply(drule div_seq,force)
apply clarify
apply (erule disjE)
 apply(force elim:CptnModWhile1)
apply clarify
apply(force simp add:last_length elim:CptnModWhile2)
\<comment> \<open>await\<close>
apply clarify
apply(erule ctran.cases,simp_all)
apply(rule CptnModNone,erule Await,simp+)
done

lemma cptn_onlyif_cptn_mod [rule_format]: "c \<in> cptn \<Longrightarrow> c \<in> cptn_mod"
apply(erule cptn.induct)
  apply(rule CptnModOne)
 apply(erule CptnModEnv)
apply(case_tac P)
 apply simp
 apply(erule ctran.cases,simp_all)
apply(force elim:cptn_onlyif_cptn_mod_aux)
done

lemma lift_is_cptn: "c\<in>cptn \<Longrightarrow> map (lift P) c \<in> cptn"
apply(erule cptn.induct)
  apply(force simp add:lift_def CptnOne)
 apply(force intro:CptnEnv simp add:lift_def)
apply(force simp add:lift_def intro:CptnComp Seq2 Seq1 elim:ctran.cases)
done

lemma cptn_append_is_cptn [rule_format]: 
 "\<forall>b a. b#c1\<in>cptn \<longrightarrow>  a#c2\<in>cptn \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> b#c1@c2\<in>cptn"
apply(induct c1)
 apply simp
apply clarify
apply(erule cptn.cases,simp_all)
 apply(force intro:CptnEnv)
apply(force elim:CptnComp)
done

lemma last_lift: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=None\<rbrakk> 
 \<Longrightarrow> fst((map (lift P) xs)!(length (map (lift P) xs)- (Suc 0)))=(Some P)"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp add:lift_def)

lemma last_fst [rule_format]: "P((a#x)!length x) \<longrightarrow> \<not>P a \<longrightarrow> P (x!(length x - (Suc 0)))" 
  by (induct x) simp_all

lemma last_fst_esp: 
 "fst(((Some a,s)#xs)!(length xs))=None \<Longrightarrow> fst(xs!(length xs - (Suc 0)))=None" 
apply(erule last_fst)
apply simp
done

lemma last_snd: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift P) xs))!(length (map (lift P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp_all add:lift_def)

lemma Cons_lift: "(Some (Seq P Q), s) # (map (lift Q) xs) = map (lift Q) ((Some P, s) # xs)"
  by (simp add:lift_def)

lemma Cons_lift_append: 
  "(Some (Seq P Q), s) # (map (lift Q) xs) @ ys = map (lift Q) ((Some P, s) # xs)@ ys "
  by (simp add:lift_def)

lemma lift_nth: "i<length xs \<Longrightarrow> map (lift Q) xs ! i = lift Q  (xs! i)"
  by (simp add:lift_def)

lemma snd_lift: "i< length xs \<Longrightarrow> snd(lift Q (xs ! i))= snd (xs ! i)"
  by (cases "xs!i") (simp add:lift_def)

lemma cptn_if_cptn_mod: "c \<in> cptn_mod \<Longrightarrow> c \<in> cptn"
apply(erule cptn_mod.induct)
        apply(rule CptnOne)
       apply(erule CptnEnv)
      apply(erule CptnComp,simp)
     apply(rule CptnComp)
      apply(erule CondT,simp)
    apply(rule CptnComp)
     apply(erule CondF,simp)
\<comment> \<open>Seq1\<close>
apply(erule cptn.cases,simp_all)
  apply(rule CptnOne)
 apply clarify
 apply(drule_tac P=P1 in lift_is_cptn)
 apply(simp add:lift_def)
 apply(rule CptnEnv,simp)
apply clarify
apply(simp add:lift_def)
apply(rule conjI)
 apply clarify
 apply(rule CptnComp)
  apply(rule Seq1,simp)
 apply(drule_tac P=P1 in lift_is_cptn)
 apply(simp add:lift_def)
apply clarify
apply(rule CptnComp)
 apply(rule Seq2,simp)
apply(drule_tac P=P1 in lift_is_cptn)
apply(simp add:lift_def)
\<comment> \<open>Seq2\<close>
apply(rule cptn_append_is_cptn)
  apply(drule_tac P=P1 in lift_is_cptn)
  apply(simp add:lift_def)
 apply simp
apply(simp split: if_split_asm)
apply(frule_tac P=P1 in last_lift)
 apply(rule last_fst_esp)
 apply (simp add:last_length)
apply(simp add:Cons_lift lift_def split_def last_conv_nth)
\<comment> \<open>While1\<close>
apply(rule CptnComp)
 apply(rule WhileT,simp)
apply(drule_tac P="While b P" in lift_is_cptn)
apply(simp add:lift_def)
\<comment> \<open>While2\<close>
apply(rule CptnComp)
 apply(rule WhileT,simp)
apply(rule cptn_append_is_cptn)
  apply(drule_tac P="While b P" in lift_is_cptn)
  apply(simp add:lift_def)
 apply simp
apply(simp split: if_split_asm)
apply(frule_tac P="While b P" in last_lift)
 apply(rule last_fst_esp,simp add:last_length)
apply(simp add:Cons_lift lift_def split_def last_conv_nth)
done

theorem cptn_iff_cptn_mod: "(c \<in> cptn) = (c \<in> cptn_mod)"
apply(rule iffI)
 apply(erule cptn_onlyif_cptn_mod)
apply(erule cptn_if_cptn_mod)
done

section \<open>Validity  of Correctness Formulas\<close>

subsection \<open>Validity for Component Programs.\<close>

type_synonym 'a rgformula =
  "'a com \<times> 'a set \<times> ('a \<times> 'a) set \<times> ('a \<times> 'a) set \<times> 'a set"

definition assum :: "('a set \<times> ('a \<times> 'a) set) \<Rightarrow> ('a confs) set" where
  "assum \<equiv> \<lambda>(pre, rely). {c. snd(c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -e\<rightarrow> c!(Suc i) \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> rely)}"

definition comm :: "(('a \<times> 'a) set \<times> 'a set) \<Rightarrow> ('a confs) set" where
  "comm \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -c\<rightarrow> c!(Suc i) \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> guar) \<and> 
               (fst (last c) = None \<longrightarrow> snd (last c) \<in> post)}"

definition com_validity :: "'a com \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> bool" 
                 (\<open>\<Turnstile> _ sat [_, _, _, _]\<close> [60,0,0,0,0] 45) where
  "\<Turnstile> P sat [pre, rely, guar, post] \<equiv> 
   \<forall>s. cp (Some P) s \<inter> assum(pre, rely) \<subseteq> comm(guar, post)"

subsection \<open>Validity for Parallel Programs.\<close>

definition All_None :: "(('a com) option) list \<Rightarrow> bool" where
  "All_None xs \<equiv> \<forall>c\<in>set xs. c=None"

definition par_assum :: "('a set \<times> ('a \<times> 'a) set) \<Rightarrow> ('a par_confs) set" where
  "par_assum \<equiv> \<lambda>(pre, rely). {c. snd(c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
             c!i -pe\<rightarrow> c!Suc i \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> rely)}"

definition par_comm :: "(('a \<times> 'a) set \<times> 'a set) \<Rightarrow> ('a par_confs) set" where
  "par_comm \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow>   
        c!i -pc\<rightarrow> c!Suc i \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> guar) \<and> 
         (All_None (fst (last c)) \<longrightarrow> snd( last c) \<in> post)}"

definition par_com_validity :: "'a  par_com \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set 
\<Rightarrow> 'a set \<Rightarrow> bool"  (\<open>\<Turnstile> _ SAT [_, _, _, _]\<close> [60,0,0,0,0] 45) where
  "\<Turnstile> Ps SAT [pre, rely, guar, post] \<equiv> 
   \<forall>s. par_cp Ps s \<inter> par_assum(pre, rely) \<subseteq> par_comm(guar, post)"

subsection \<open>Compositionality of the Semantics\<close>

subsubsection \<open>Definition of the conjoin operator\<close>

definition same_length :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool" where
  "same_length c clist \<equiv> (\<forall>i<length clist. length(clist!i)=length c)"
 
definition same_state :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool" where
  "same_state c clist \<equiv> (\<forall>i <length clist. \<forall>j<length c. snd(c!j) = snd((clist!i)!j))"

definition same_program :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool" where
  "same_program c clist \<equiv> (\<forall>j<length c. fst(c!j) = map (\<lambda>x. fst(nth x j)) clist)"

definition compat_label :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool" where
  "compat_label c clist \<equiv> (\<forall>j. Suc j<length c \<longrightarrow> 
         (c!j -pc\<rightarrow> c!Suc j \<and> (\<exists>i<length clist. (clist!i)!j -c\<rightarrow> (clist!i)! Suc j \<and> 
                       (\<forall>l<length clist. l\<noteq>i \<longrightarrow> (clist!l)!j -e\<rightarrow> (clist!l)! Suc j))) \<or> 
         (c!j -pe\<rightarrow> c!Suc j \<and> (\<forall>i<length clist. (clist!i)!j -e\<rightarrow> (clist!i)! Suc j)))"

definition conjoin :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool"  (\<open>_ \<propto> _\<close> [65,65] 64) where
  "c \<propto> clist \<equiv> (same_length c clist) \<and> (same_state c clist) \<and> (same_program c clist) \<and> (compat_label c clist)"

subsubsection \<open>Some previous lemmas\<close>

lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
  by (induct xs) auto

lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
  by (cases ys) simp_all

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
  by (induct ys) simp_all

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
  by (induct ys) simp_all

lemma seq_not_eq1: "Seq c1 c2\<noteq>c1"
  by (induct c1) auto

lemma seq_not_eq2: "Seq c1 c2\<noteq>c2"
  by (induct c2) auto

lemma if_not_eq1: "Cond b c1 c2 \<noteq>c1"
  by (induct c1) auto

lemma if_not_eq2: "Cond b c1 c2\<noteq>c2"
  by (induct c2) auto

lemmas seq_and_if_not_eq [simp] = seq_not_eq1 seq_not_eq2 
seq_not_eq1 [THEN not_sym] seq_not_eq2 [THEN not_sym] 
if_not_eq1 if_not_eq2 if_not_eq1 [THEN not_sym] if_not_eq2 [THEN not_sym]

lemma prog_not_eq_in_ctran_aux:
  assumes c: "(P,s) -c\<rightarrow> (Q,t)"
  shows "P\<noteq>Q" using c
  by (induct x1 \<equiv> "(P,s)" x2 \<equiv> "(Q,t)" arbitrary: P s Q t) auto

lemma prog_not_eq_in_ctran [simp]: "\<not> (P,s) -c\<rightarrow> (P,t)"
apply clarify
apply(drule prog_not_eq_in_ctran_aux)
apply simp
done

lemma prog_not_eq_in_par_ctran_aux [rule_format]: "(P,s) -pc\<rightarrow> (Q,t) \<Longrightarrow> (P\<noteq>Q)"
apply(erule par_ctran.induct)
apply(drule prog_not_eq_in_ctran_aux)
apply clarify
apply(drule list_eq_if)
 apply simp_all
apply force
done

lemma prog_not_eq_in_par_ctran [simp]: "\<not> (P,s) -pc\<rightarrow> (P,t)"
apply clarify
apply(drule prog_not_eq_in_par_ctran_aux)
apply simp
done

lemma tl_in_cptn: "\<lbrakk> a#xs \<in>cptn; xs\<noteq>[] \<rbrakk> \<Longrightarrow> xs\<in>cptn"
  by (force elim: cptn.cases)

lemma tl_zero[rule_format]: 
  "P (ys!Suc j) \<longrightarrow> Suc j<length ys \<longrightarrow> ys\<noteq>[] \<longrightarrow> P (tl(ys)!j)"
  by (induct ys) simp_all

subsection \<open>The Semantics is Compositional\<close>

lemma aux_if [rule_format]: 
  "\<forall>xs s clist. (length clist = length xs \<and> (\<forall>i<length xs. (xs!i,s)#clist!i \<in> cptn) 
  \<and> ((xs, s)#ys \<propto> map (\<lambda>i. (fst i,s)#snd i) (zip xs clist)) 
   \<longrightarrow> (xs, s)#ys \<in> par_cptn)"
apply(induct ys)
 apply(clarify)
 apply(rule ParCptnOne)
apply(clarify)
apply(simp add:conjoin_def compat_label_def)
apply clarify
apply(erule_tac x="0" and P="\<lambda>j. H j \<longrightarrow> (P j \<or> Q j)" for H P Q in all_dupE, simp)
apply(erule disjE)
\<comment> \<open>first step is a Component step\<close>
 apply clarify 
 apply simp
 apply(subgoal_tac "a=(xs[i:=(fst(clist!i!0))])")
  apply(subgoal_tac "b=snd(clist!i!0)",simp)
   prefer 2
   apply(simp add: same_state_def)
   apply(erule_tac x=i in allE,erule impE,assumption, 
         erule_tac x=1 and P="\<lambda>j. (H j) \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE, simp)
  prefer 2
  apply(simp add:same_program_def)
  apply(erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (fst (s j))=(t j)" for H s t in allE,simp)
  apply(rule nth_equalityI,simp)
  apply clarify
  apply(case_tac "i=ia",simp,simp)
  apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE)
  apply(drule_tac t=i in not_sym,simp)
  apply(erule etranE,simp)
 apply(rule ParCptnComp)
  apply(erule ParComp,simp)
\<comment> \<open>applying the induction hypothesis\<close>
 apply(erule_tac x="xs[i := fst (clist ! i ! 0)]" in allE)
 apply(erule_tac x="snd (clist ! i ! 0)" in allE)
 apply(erule mp)
 apply(rule_tac x="map tl clist" in exI,simp)
 apply(rule conjI,clarify)
  apply(case_tac "i=ia",simp)
   apply(rule nth_tl_if)
     apply(force simp add:same_length_def length_Suc_conv)
    apply simp
   apply(erule allE,erule impE,assumption,erule tl_in_cptn)
   apply(force simp add:same_length_def length_Suc_conv)
  apply(rule nth_tl_if)
    apply(force simp add:same_length_def length_Suc_conv)
   apply(simp add:same_state_def)
   apply(erule_tac x=ia in allE, erule impE, assumption, 
     erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
   apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE)
   apply(drule_tac t=i  in not_sym,simp)
   apply(erule etranE,simp)
  apply(erule allE,erule impE,assumption,erule tl_in_cptn)
  apply(force simp add:same_length_def length_Suc_conv)
 apply(simp add:same_length_def same_state_def)
 apply(rule conjI)
  apply clarify
  apply(case_tac j,simp,simp)
  apply(erule_tac x=ia in allE, erule impE, assumption,
        erule_tac x="Suc(Suc nat)" and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
  apply(force simp add:same_length_def length_Suc_conv)
 apply(rule conjI)
  apply(simp add:same_program_def)
  apply clarify
  apply(case_tac j,simp)
   apply(rule nth_equalityI,simp)
   apply clarify
   apply(case_tac "i=ia",simp,simp)
  apply(erule_tac x="Suc(Suc nat)" and P="\<lambda>j. H j \<longrightarrow> (fst (s j))=(t j)" for H s t in allE,simp)
  apply(rule nth_equalityI,simp,simp)
  apply(force simp add:length_Suc_conv)
 apply(rule allI,rule impI)
 apply(erule_tac x="Suc j" and P="\<lambda>j. H j \<longrightarrow> (I j \<or> J j)" for H I J in allE,simp)
 apply(erule disjE) 
  apply clarify
  apply(rule_tac x=ia in exI,simp)
  apply(case_tac "i=ia",simp)
   apply(rule conjI)
    apply(force simp add: length_Suc_conv)
   apply clarify
   apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE,erule impE,assumption)
   apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE,erule impE,assumption)
   apply simp
   apply(case_tac j,simp)
    apply(rule tl_zero)
      apply(erule_tac x=l in allE, erule impE, assumption, 
            erule_tac x=1 and P="\<lambda>j.  (H j) \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
      apply(force elim:etranE intro:Env)
     apply force
    apply force
   apply simp
   apply(rule tl_zero)
     apply(erule tl_zero)
      apply force
     apply force
    apply force
   apply force
  apply(rule conjI,simp)
   apply(rule nth_tl_if)
     apply force
    apply(erule_tac x=ia  in allE, erule impE, assumption,
          erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
    apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE)
    apply(drule_tac t=i  in not_sym,simp)
    apply(erule etranE,simp)
   apply(erule tl_zero)
    apply force
   apply force
  apply clarify
  apply(case_tac "i=l",simp)
   apply(rule nth_tl_if)
     apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
    apply simp
   apply(erule_tac P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE,erule impE,assumption,erule impE,assumption)
   apply(erule tl_zero,force)
   apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
   apply(rule nth_tl_if)
     apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
    apply(erule_tac x=l  in allE, erule impE, assumption,
          erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
    apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE,erule impE, assumption,simp)
    apply(erule etranE,simp)
   apply(rule tl_zero)
    apply force
   apply force
  apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
 apply(rule disjI2)
 apply(case_tac j,simp)
  apply clarify
  apply(rule tl_zero)
    apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> I j\<in>etran" for H I in allE,erule impE, assumption)
    apply(case_tac "i=ia",simp,simp)
    apply(erule_tac x=ia  in allE, erule impE, assumption,
    erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
    apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE,erule impE, assumption,simp)
    apply(force elim:etranE intro:Env)
   apply force
  apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
 apply simp
 apply clarify
 apply(rule tl_zero)
   apply(rule tl_zero,force)
    apply force
   apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
  apply force
 apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
\<comment> \<open>first step is an environmental step\<close>
apply clarify
apply(erule par_etran.cases)
apply simp
apply(rule ParCptnEnv)
apply(erule_tac x="Ps" in allE)
apply(erule_tac x="t" in allE)
apply(erule mp)
apply(rule_tac x="map tl clist" in exI,simp)
apply(rule conjI)
 apply clarify
 apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> I j \<in> cptn" for H I in allE,simp)
 apply(erule cptn.cases)
   apply(simp add:same_length_def)
   apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
  apply(simp add:same_state_def)
  apply(erule_tac x=i  in allE, erule impE, assumption,
   erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
 apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> J j \<in>etran" for H J in allE,simp)
 apply(erule etranE,simp)
apply(simp add:same_state_def same_length_def)
apply(rule conjI,clarify)
 apply(case_tac j,simp,simp)
 apply(erule_tac x=i  in allE, erule impE, assumption,
       erule_tac x="Suc(Suc nat)" and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
 apply(rule tl_zero)
   apply(simp)
  apply force
 apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
apply(rule conjI)
 apply(simp add:same_program_def)
 apply clarify
 apply(case_tac j,simp)
  apply(rule nth_equalityI,simp)
  apply clarify
  apply simp
 apply(erule_tac x="Suc(Suc nat)" and P="\<lambda>j. H j \<longrightarrow> (fst (s j))=(t j)" for H s t in allE,simp)
 apply(rule nth_equalityI,simp,simp)
 apply(force simp add:length_Suc_conv)
apply(rule allI,rule impI)
apply(erule_tac x="Suc j" and P="\<lambda>j. H j \<longrightarrow> (I j \<or> J j)" for H I J in allE,simp)
apply(erule disjE) 
 apply clarify
 apply(rule_tac x=i in exI,simp)
 apply(rule conjI)
  apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> J i \<in>etran" for H J in allE, erule impE, assumption)
  apply(erule etranE,simp)
  apply(erule_tac x=i  in allE, erule impE, assumption,
        erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
  apply(rule nth_tl_if)
   apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
  apply simp
 apply(erule tl_zero,force) 
  apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
 apply clarify
 apply(erule_tac x=l and P="\<lambda>i. H i \<longrightarrow> J i \<in>etran" for H J in allE, erule impE, assumption)
 apply(erule etranE,simp)
 apply(erule_tac x=l  in allE, erule impE, assumption,
       erule_tac x=1 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
 apply(rule nth_tl_if)
   apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
  apply simp
  apply(rule tl_zero,force)
  apply force
 apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
apply(rule disjI2)
apply simp
apply clarify
apply(case_tac j,simp)
 apply(rule tl_zero)
   apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> J i \<in>etran" for H J in allE, erule impE, assumption)
   apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> J i \<in>etran" for H J in allE, erule impE, assumption)
   apply(force elim:etranE intro:Env)
  apply force
 apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
apply simp
apply(rule tl_zero)
  apply(rule tl_zero,force)
   apply force
  apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
 apply force
apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
done

lemma aux_onlyif [rule_format]: "\<forall>xs s. (xs, s)#ys \<in> par_cptn \<longrightarrow> 
  (\<exists>clist. (length clist = length xs) \<and> 
  (xs, s)#ys \<propto> map (\<lambda>i. (fst i,s)#(snd i)) (zip xs clist) \<and> 
  (\<forall>i<length xs. (xs!i,s)#(clist!i) \<in> cptn))"
  supply [[simproc del: defined_all]]
apply(induct ys)
 apply(clarify)
 apply(rule_tac x="map (\<lambda>i. []) [0..<length xs]" in exI)
 apply(simp add: conjoin_def same_length_def same_state_def same_program_def compat_label_def)
 apply(rule conjI)
  apply(rule nth_equalityI,simp,simp)
 apply(force intro: cptn.intros)
apply(clarify)
apply(erule par_cptn.cases,simp)
 apply simp
 apply(erule_tac x="xs" in allE)
 apply(erule_tac x="t" in allE,simp)
 apply clarify
 apply(rule_tac x="(map (\<lambda>j. (P!j, t)#(clist!j)) [0..<length P])" in exI,simp)
 apply(rule conjI)
  prefer 2
  apply clarify
  apply(rule CptnEnv,simp)
 apply(simp add:conjoin_def same_length_def same_state_def)
 apply (rule conjI)
  apply clarify
  apply(case_tac j,simp,simp)
 apply(rule conjI)
  apply(simp add:same_program_def)
  apply clarify
  apply(case_tac j,simp)
   apply(rule nth_equalityI,simp,simp)
  apply simp
  apply(rule nth_equalityI,simp,simp)
 apply(simp add:compat_label_def)
 apply clarify
 apply(case_tac j,simp)
  apply(simp add:ParEnv)
  apply clarify
  apply(simp add:Env)
 apply simp
 apply(erule_tac x=nat in allE,erule impE, assumption)
 apply(erule disjE,simp)
  apply clarify
  apply(rule_tac x=i in exI,simp)
 apply force
apply(erule par_ctran.cases,simp)
apply(erule_tac x="Ps[i:=r]" in allE)
apply(erule_tac x="ta" in allE,simp)
apply clarify
apply(rule_tac x="(map (\<lambda>j. (Ps!j, ta)#(clist!j)) [0..<length Ps]) [i:=((r, ta)#(clist!i))]" in exI,simp)
apply(rule conjI)
 prefer 2
 apply clarify
 apply(case_tac "i=ia",simp)
  apply(erule CptnComp)
  apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (I j \<in> cptn)" for H I in allE,simp)
 apply simp
 apply(erule_tac x=ia in allE)
 apply(rule CptnEnv,simp)
apply(simp add:conjoin_def)
apply (rule conjI)
 apply(simp add:same_length_def)
 apply clarify
 apply(case_tac "i=ia",simp,simp)
apply(rule conjI)
 apply(simp add:same_state_def)
 apply clarify
 apply(case_tac j, simp, simp (no_asm_simp))
 apply(case_tac "i=ia",simp,simp)
apply(rule conjI)
 apply(simp add:same_program_def)
 apply clarify
 apply(case_tac j,simp)
  apply(rule nth_equalityI,simp,simp)
 apply simp
 apply(rule nth_equalityI,simp,simp)
 apply(erule_tac x=nat and P="\<lambda>j. H j \<longrightarrow> (fst (a j))=((b j))" for H a b in allE)
 apply(case_tac nat)
  apply clarify
  apply(case_tac "i=ia",simp,simp)
 apply clarify
 apply(case_tac "i=ia",simp,simp)
apply(simp add:compat_label_def)
apply clarify
apply(case_tac j)
 apply(rule conjI,simp)
  apply(erule ParComp,assumption)
  apply clarify
  apply(rule_tac x=i in exI,simp)
 apply clarify
 apply(rule Env)
apply simp
apply(erule_tac x=nat and P="\<lambda>j. H j \<longrightarrow> (P j \<or> Q j)" for H P Q in allE,simp)
apply(erule disjE)
 apply clarify
 apply(rule_tac x=ia in exI,simp)
 apply(rule conjI)
  apply(case_tac "i=ia",simp,simp)
 apply clarify
 apply(case_tac "i=l",simp)
  apply(case_tac "l=ia",simp,simp)
  apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
 apply simp
 apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
apply clarify
apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (P j)\<in>etran" for H P in allE, erule impE, assumption)
apply(case_tac "i=ia",simp,simp)
done

lemma one_iff_aux: "xs\<noteq>[] \<Longrightarrow> (\<forall>ys. ((xs, s)#ys \<in> par_cptn) = 
 (\<exists>clist. length clist= length xs \<and> 
 ((xs, s)#ys \<propto> map (\<lambda>i. (fst i,s)#(snd i)) (zip xs clist)) \<and> 
 (\<forall>i<length xs. (xs!i,s)#(clist!i) \<in> cptn))) = 
 (par_cp (xs) s = {c. \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. (clist!i) \<in> cp(xs!i) s) \<and> c \<propto> clist})" 
apply (rule iffI)
 apply(rule subset_antisym)
  apply(rule subsetI) 
  apply(clarify)
  apply(simp add:par_cp_def cp_def)
  apply(case_tac x)
   apply(force elim:par_cptn.cases)
  apply simp
  apply(rename_tac a list)
  apply(erule_tac x="list" in allE)
  apply clarify
  apply simp
  apply(rule_tac x="map (\<lambda>i. (fst i, s) # snd i) (zip xs clist)" in exI,simp)
 apply(rule subsetI) 
 apply(clarify)
 apply(case_tac x)
  apply(erule_tac x=0 in allE)
  apply(simp add:cp_def conjoin_def same_length_def same_program_def same_state_def compat_label_def)
  apply clarify
  apply(erule cptn.cases,force,force,force)
 apply(simp add:par_cp_def conjoin_def  same_length_def same_program_def same_state_def compat_label_def)
 apply clarify
 apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in all_dupE)
 apply(subgoal_tac "a = xs")
  apply(subgoal_tac "b = s",simp)
   prefer 3
   apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (fst (s j))=((t j))" for H s t in allE)
   apply (simp add:cp_def)
   apply(rule nth_equalityI,simp,simp)
  prefer 2
  apply(erule_tac x=0 in allE)
  apply (simp add:cp_def)
  apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (\<forall>i. T i \<longrightarrow> (snd (d j i))=(snd (e j i)))" for H T d e in allE,simp)
  apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
 apply(erule_tac x=list in allE)
 apply(rule_tac x="map tl clist" in exI,simp) 
 apply(rule conjI)
  apply clarify
  apply(case_tac j,simp)
   apply(erule_tac x=i  in allE, erule impE, assumption,
        erule_tac x="0" and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE,simp)
  apply(erule_tac x=i  in allE, erule impE, assumption,
        erule_tac x="Suc nat" and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
  apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
  apply(case_tac "clist!i",simp,simp)
 apply(rule conjI)
  apply clarify
  apply(rule nth_equalityI,simp,simp)
  apply(case_tac j)
   apply clarify
   apply(erule_tac x=i in allE)
   apply(simp add:cp_def)
  apply clarify
  apply simp
  apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
  apply(case_tac "clist!i",simp,simp)
 apply(thin_tac "H = (\<exists>i. J i)" for H J)
 apply(rule conjI)
  apply clarify
  apply(erule_tac x=j in allE,erule impE, assumption,erule disjE)
   apply clarify
   apply(rule_tac x=i in exI,simp)
   apply(case_tac j,simp)
    apply(rule conjI)
     apply(erule_tac x=i in allE)
     apply(simp add:cp_def)
     apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
     apply(case_tac "clist!i",simp,simp)
    apply clarify
    apply(erule_tac x=l in allE)
    apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE)
    apply clarify
    apply(simp add:cp_def)
    apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
    apply(case_tac "clist!l",simp,simp)
   apply simp
   apply(rule conjI)
    apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
    apply(case_tac "clist!i",simp,simp)
   apply clarify
   apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE)
   apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
   apply(case_tac "clist!l",simp,simp)
  apply clarify
  apply(erule_tac x=i in allE)
  apply(simp add:cp_def)
  apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
  apply(case_tac "clist!i",simp)
  apply(rule nth_tl_if,simp,simp)
  apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (P j)\<in>etran" for H P in allE, erule impE, assumption,simp)
  apply(simp add:cp_def)
  apply clarify
  apply(rule nth_tl_if)
   apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
   apply(case_tac "clist!i",simp,simp)
  apply force
 apply force
apply clarify
apply(rule iffI)
 apply(simp add:par_cp_def)
 apply(erule_tac c="(xs, s) # ys" in equalityCE)
  apply simp
  apply clarify
  apply(rule_tac x="map tl clist" in exI)
  apply simp
  apply (rule conjI)
   apply(simp add:conjoin_def cp_def)
   apply(rule conjI)
    apply clarify
    apply(unfold same_length_def)
    apply clarify
    apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,simp)
   apply(rule conjI)
    apply(simp add:same_state_def)
    apply clarify
    apply(erule_tac x=i in allE, erule impE, assumption,
       erule_tac x=j and P="\<lambda>j. H j \<longrightarrow> (snd (d j))=(snd (e j))" for H d e in allE)
    apply(case_tac j,simp)
    apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
    apply(case_tac "clist!i",simp,simp)
   apply(rule conjI)
    apply(simp add:same_program_def)
    apply clarify
    apply(rule nth_equalityI,simp,simp)
    apply(case_tac j,simp)
    apply clarify
    apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
    apply(case_tac "clist!i",simp,simp)
   apply clarify
   apply(simp add:compat_label_def)
   apply(rule allI,rule impI)
   apply(erule_tac x=j in allE,erule impE, assumption)
   apply(erule disjE)
    apply clarify
    apply(rule_tac x=i in exI,simp)
    apply(rule conjI)
     apply(erule_tac x=i in allE)
     apply(case_tac j,simp)
      apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
      apply(case_tac "clist!i",simp,simp)
     apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
     apply(case_tac "clist!i",simp,simp)
    apply clarify
    apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> I j \<longrightarrow> J j" for H I J in allE)
    apply(erule_tac x=l and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE)
    apply(case_tac "clist!l",simp,simp)
    apply(erule_tac x=l in allE,simp)
   apply(rule disjI2)
   apply clarify
   apply(rule tl_zero)
     apply(case_tac j,simp,simp)
     apply(rule tl_zero,force)   
      apply force
     apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
    apply force
   apply(erule_tac x=i and P="\<lambda>j. H j \<longrightarrow> (length (s j) = t)" for H s t in allE,force)
  apply clarify
  apply(erule_tac x=i in allE)
  apply(simp add:cp_def)
  apply(rule nth_tl_if)
    apply(simp add:conjoin_def)
    apply clarify
    apply(simp add:same_length_def)
    apply(erule_tac x=i in allE,simp)
   apply simp
  apply simp
 apply simp
apply clarify
apply(erule_tac c="(xs, s) # ys" in equalityCE)
 apply(simp add:par_cp_def)
apply simp
apply(erule_tac x="map (\<lambda>i. (fst i, s) # snd i) (zip xs clist)" in allE)
apply simp
apply clarify
apply(simp add:cp_def)
done

theorem one: "xs\<noteq>[] \<Longrightarrow> 
 par_cp xs s = {c. \<exists>clist. (length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp(xs!i) s) \<and> c \<propto> clist}"
apply(frule one_iff_aux)
apply(drule sym)
apply(erule iffD2)
apply clarify
apply(rule iffI)
 apply(erule aux_onlyif)
apply clarify
apply(force intro:aux_if)
done

end
