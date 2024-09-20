(*  Title:      HOL/NanoJava/Example.thy
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

section "Example"

theory Example
imports Equivalence
begin

text \<open>

\begin{verbatim}
class Nat {

  Nat pred;

  Nat suc() 
    { Nat n = new Nat(); n.pred = this; return n; }

  Nat eq(Nat n)
    { if (this.pred != null) if (n.pred != null) return this.pred.eq(n.pred);
                             else return n.pred; // false
      else if (n.pred != null) return this.pred; // false
           else return this.suc(); // true
    }

  Nat add(Nat n)
    { if (this.pred != null) return this.pred.add(n.suc()); else return n; }

  public static void main(String[] args) // test x+1=1+x
    {
        Nat one = new Nat().suc();
        Nat x   = new Nat().suc().suc().suc().suc();
        Nat ok = x.suc().eq(x.add(one));
        System.out.println(ok != null);
    }
}
\end{verbatim}

\<close>

axiomatization where
  This_neq_Par [simp]: "This \<noteq> Par" and
  Res_neq_This [simp]: "Res  \<noteq> This"


subsection "Program representation"

axiomatization 
  N    :: cname (\<open>Nat\<close>) (* with mixfix because of clash with NatDef.Nat *)
  and pred :: fname
  and suc add :: mname
  and any  :: vname

abbreviation
  dummy :: expr (\<open><>\<close>)
  where "<> == LAcc any"

abbreviation
  one :: expr
  where "one == {Nat}new Nat..suc(<>)"

text \<open>The following properties could be derived from a more complete
        program model, which we leave out for laziness.\<close>

axiomatization where Nat_no_subclasses [simp]: "D \<preceq>C Nat = (D=Nat)"

axiomatization where method_Nat_add [simp]: "method Nat add = Some 
  \<lparr> par=Class Nat, res=Class Nat, lcl=[], 
   bdy= If((LAcc This..pred)) 
          (Res :== {Nat}(LAcc This..pred)..add({Nat}LAcc Par..suc(<>))) 
        Else Res :== LAcc Par \<rparr>"

axiomatization where method_Nat_suc [simp]: "method Nat suc = Some 
  \<lparr> par=NT, res=Class Nat, lcl=[], 
   bdy= Res :== new Nat;; LAcc Res..pred :== LAcc This \<rparr>"

axiomatization where field_Nat [simp]: "field Nat = Map.empty(pred\<mapsto>Class Nat)"

lemma init_locs_Nat_add [simp]: "init_locs Nat add s = s"
by (simp add: init_locs_def init_vars_def)

lemma init_locs_Nat_suc [simp]: "init_locs Nat suc s = s"
by (simp add: init_locs_def init_vars_def)

lemma upd_obj_new_obj_Nat [simp]: 
  "upd_obj a pred v (new_obj a Nat s) = hupd(a\<mapsto>(Nat, Map.empty(pred\<mapsto>v))) s"
by (simp add: new_obj_def init_vars_def upd_obj_def Let_def)


subsection "``atleast'' relation for interpretation of Nat ``values''"

primrec Nat_atleast :: "state \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> bool" (\<open>_:_ \<ge> _\<close> [51, 51, 51] 50) where
  "s:x\<ge>0     = (x\<noteq>Null)"
| "s:x\<ge>Suc n = (\<exists>a. x=Addr a \<and> heap s a \<noteq> None \<and> s:get_field s a pred\<ge>n)"

lemma Nat_atleast_lupd [rule_format, simp]: 
 "\<forall>s v::val. lupd(x\<mapsto>y) s:v \<ge> n = (s:v \<ge> n)"
apply (induct n)
by  auto

lemma Nat_atleast_set_locs [rule_format, simp]: 
 "\<forall>s v::val. set_locs l s:v \<ge> n = (s:v \<ge> n)"
apply (induct n)
by auto

lemma Nat_atleast_del_locs [rule_format, simp]: 
 "\<forall>s v::val. del_locs s:v \<ge> n = (s:v \<ge> n)"
apply (induct n)
by auto

lemma Nat_atleast_NullD [rule_format]: "s:Null \<ge> n \<longrightarrow> False"
apply (induct n)
by auto

lemma Nat_atleast_pred_NullD [rule_format]: 
"Null = get_field s a pred \<Longrightarrow> s:Addr a \<ge> n \<longrightarrow> n = 0"
apply (induct n)
by (auto dest: Nat_atleast_NullD)

lemma Nat_atleast_mono [rule_format]: 
"\<forall>a. s:get_field s a pred \<ge> n \<longrightarrow> heap s a \<noteq> None \<longrightarrow> s:Addr a \<ge> n"
apply (induct n)
by auto

lemma Nat_atleast_newC [rule_format]: 
  "heap s aa = None \<Longrightarrow> \<forall>v::val. s:v \<ge> n \<longrightarrow> hupd(aa\<mapsto>obj) s:v \<ge> n"
apply (induct n)
apply  auto
apply  (case_tac "aa=a")
apply   auto
apply (tactic "smp_tac \<^context> 1 1")
apply (case_tac "aa=a")
apply  auto
done


subsection "Proof(s) using the Hoare logic"

theorem add_homomorph_lb: 
  "{} \<turnstile> {\<lambda>s. s:s<This> \<ge> X \<and> s:s<Par> \<ge> Y} Meth(Nat,add) {\<lambda>s. s:s<Res> \<ge> X+Y}"
apply (rule hoare_ehoare.Meth) (* 1 *)
apply clarsimp
apply (rule_tac P'= "\<lambda>Z s. (s:s<This> \<ge> fst Z \<and> s:s<Par> \<ge> snd Z) \<and> D=Nat" and 
        Q'= "\<lambda>Z s. s:s<Res> \<ge> fst Z+snd Z" in AxSem.Conseq)
prefer 2
apply  (clarsimp simp add: init_locs_def init_vars_def)
apply rule
apply (case_tac "D = Nat", simp_all, rule_tac [2] cFalse)
apply (rule_tac P = "\<lambda>Z Cm s. s:s<This> \<ge> fst Z \<and> s:s<Par> \<ge> snd Z" in AxSem.Impl1)
apply (clarsimp simp add: body_def)  (* 4 *)
apply (rename_tac n m)
apply (rule_tac Q = "\<lambda>v s. (s:s<This> \<ge> n \<and> s:s<Par> \<ge> m) \<and> 
        (\<exists>a. s<This> = Addr a \<and> v = get_field s a pred)" in hoare_ehoare.Cond)
apply  (rule hoare_ehoare.FAcc)
apply  (rule eConseq1)
apply   (rule hoare_ehoare.LAcc)
apply  fast
apply auto
prefer 2
apply  (rule hoare_ehoare.LAss)
apply  (rule eConseq1)
apply   (rule hoare_ehoare.LAcc)
apply  (auto dest: Nat_atleast_pred_NullD)
apply (rule hoare_ehoare.LAss)
apply (rule_tac 
    Q = "\<lambda>v   s. (\<forall>m. n = Suc m \<longrightarrow> s:v \<ge> m) \<and> s:s<Par> \<ge> m" and 
    R = "\<lambda>T P s. (\<forall>m. n = Suc m \<longrightarrow> s:T \<ge> m) \<and> s:P  \<ge> Suc m" 
    in hoare_ehoare.Call) (* 13 *)
apply   (rule hoare_ehoare.FAcc)
apply   (rule eConseq1)
apply    (rule hoare_ehoare.LAcc)
apply   clarify
apply   (drule sym, rotate_tac -1, frule (1) trans)
apply   simp
prefer 2
apply  clarsimp
apply  (rule hoare_ehoare.Meth) (* 17 *)
apply  clarsimp
apply  (case_tac "D = Nat", simp_all, rule_tac [2] cFalse)
apply  (rule AxSem.Conseq)
apply   rule
apply   (rule hoare_ehoare.Asm) (* 20 *)
apply   (rule_tac a = "((case n of 0 \<Rightarrow> 0 | Suc m \<Rightarrow> m),m+1)" in UN_I, rule+)
apply  (clarsimp split: nat.split_asm dest!: Nat_atleast_mono)
apply rule
apply (rule hoare_ehoare.Call) (* 21 *)
apply   (rule hoare_ehoare.LAcc)
apply  rule
apply  (rule hoare_ehoare.LAcc)
apply clarify
apply (rule hoare_ehoare.Meth) (* 24 *)
apply clarsimp
apply  (case_tac "D = Nat", simp_all, rule_tac [2] cFalse)
apply (rule AxSem.Impl1)
apply (clarsimp simp add: body_def)
apply (rule hoare_ehoare.Comp) (* 26 *)
prefer 2
apply  (rule hoare_ehoare.FAss)
prefer 2
apply   rule
apply   (rule hoare_ehoare.LAcc)
apply  (rule hoare_ehoare.LAcc)
apply (rule hoare_ehoare.LAss)
apply (rule eConseq1)
apply  (rule hoare_ehoare.NewC) (* 32 *)
apply (auto dest!: new_AddrD elim: Nat_atleast_newC)
done


end
