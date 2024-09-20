(*  Title:      HOL/MicroJava/JVM/JVMDefensive.thy
    Author:     Gerwin Klein
*)

section \<open>A Defensive JVM\<close>

theory JVMDefensive
imports JVMExec
begin

text \<open>
  Extend the state space by one element indicating a type error (or
  other abnormal termination)\<close>
datatype 'a type_error = TypeError | Normal 'a


abbreviation
  fifth :: "'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e \<times> 'f \<Rightarrow> 'e"
  where "fifth x == fst(snd(snd(snd(snd x))))"

fun isAddr :: "val \<Rightarrow> bool" where
  "isAddr (Addr loc) = True"
| "isAddr v          = False"

fun isIntg :: "val \<Rightarrow> bool" where
  "isIntg (Intg i) = True"
| "isIntg v        = False"

definition isRef :: "val \<Rightarrow> bool" where
  "isRef v \<equiv> v = Null \<or> isAddr v"

primrec check_instr :: "[instr, jvm_prog, aheap, opstack, locvars, 
                  cname, sig, p_count, nat, frame list] \<Rightarrow> bool" where
  "check_instr (Load idx) G hp stk vars C sig pc mxs frs = 
  (idx < length vars \<and> size stk < mxs)"

| "check_instr (Store idx) G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk \<and> idx < length vars)"

| "check_instr (LitPush v) G hp stk vars Cl sig pc mxs frs = 
  (\<not>isAddr v \<and> size stk < mxs)"

| "check_instr (New C) G hp stk vars Cl sig pc mxs frs = 
  (is_class G C \<and> size stk < mxs)"

| "check_instr (Getfield F C) G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk \<and> is_class G C \<and> field (G,C) F \<noteq> None \<and> 
  (let (C', T) = the (field (G,C) F); ref = hd stk in 
    C' = C \<and> isRef ref \<and> (ref \<noteq> Null \<longrightarrow> 
      hp (the_Addr ref) \<noteq> None \<and> 
      (let (D,vs) = the (hp (the_Addr ref)) in 
        G \<turnstile> D \<preceq>C C \<and> vs (F,C) \<noteq> None \<and> G,hp \<turnstile> the (vs (F,C)) ::\<preceq> T))))" 

| "check_instr (Putfield F C) G hp stk vars Cl sig pc mxs frs = 
  (1 < length stk \<and> is_class G C \<and> field (G,C) F \<noteq> None \<and> 
  (let (C', T) = the (field (G,C) F); v = hd stk; ref = hd (tl stk) in 
    C' = C \<and> isRef ref \<and> (ref \<noteq> Null \<longrightarrow> 
      hp (the_Addr ref) \<noteq> None \<and> 
      (let (D,vs) = the (hp (the_Addr ref)) in 
        G \<turnstile> D \<preceq>C C \<and> G,hp \<turnstile> v ::\<preceq> T))))" 

| "check_instr (Checkcast C) G hp stk vars Cl sig pc mxs frs =
  (0 < length stk \<and> is_class G C \<and> isRef (hd stk))"

| "check_instr (Invoke C mn ps) G hp stk vars Cl sig pc mxs frs =
  (length ps < length stk \<and> 
  (let n = length ps; v = stk!n in
  isRef v \<and> (v \<noteq> Null \<longrightarrow> 
    hp (the_Addr v) \<noteq> None \<and>
    method (G,cname_of hp v) (mn,ps) \<noteq> None \<and>
    list_all2 (\<lambda>v T. G,hp \<turnstile> v ::\<preceq> T) (rev (take n stk)) ps)))"
  
| "check_instr Return G hp stk0 vars Cl sig0 pc mxs frs =
  (0 < length stk0 \<and> (0 < length frs \<longrightarrow> 
    method (G,Cl) sig0 \<noteq> None \<and>    
    (let v = hd stk0;  (C, rT, body) = the (method (G,Cl) sig0) in
    Cl = C \<and> G,hp \<turnstile> v ::\<preceq> rT)))"
 
| "check_instr Pop G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk)"

| "check_instr Dup G hp stk vars Cl sig pc mxs frs = 
  (0 < length stk \<and> size stk < mxs)"

| "check_instr Dup_x1 G hp stk vars Cl sig pc mxs frs = 
  (1 < length stk \<and> size stk < mxs)"

| "check_instr Dup_x2 G hp stk vars Cl sig pc mxs frs = 
  (2 < length stk \<and> size stk < mxs)"

| "check_instr Swap G hp stk vars Cl sig pc mxs frs =
  (1 < length stk)"

| "check_instr IAdd G hp stk vars Cl sig pc mxs frs =
  (1 < length stk \<and> isIntg (hd stk) \<and> isIntg (hd (tl stk)))"

| "check_instr (Ifcmpeq b) G hp stk vars Cl sig pc mxs frs =
  (1 < length stk \<and> 0 \<le> int pc+b)"

| "check_instr (Goto b) G hp stk vars Cl sig pc mxs frs =
  (0 \<le> int pc+b)"

| "check_instr Throw G hp stk vars Cl sig pc mxs frs =
  (0 < length stk \<and> isRef (hd stk))"

definition check :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> bool" where
  "check G s \<equiv> let (xcpt, hp, frs) = s in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,sig,pc)#frs' \<Rightarrow> 
                (let  (C',rt,mxs,mxl,ins,et) = the (method (G,C) sig); i = ins!pc in
                 pc < size ins \<and> 
                 check_instr i G hp stk loc C sig pc mxs frs'))"


definition exec_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state option type_error" where
  "exec_d G s \<equiv> case s of 
      TypeError \<Rightarrow> TypeError 
    | Normal s' \<Rightarrow> if check G s' then Normal (exec (G, s')) else TypeError"


definition
  exec_all_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   (\<open>_ \<turnstile> _ \<midarrow>jvmd\<rightarrow> _\<close> [61,61,61]60) where
  "G \<turnstile> s \<midarrow>jvmd\<rightarrow> t \<longleftrightarrow>
         (s,t) \<in> ({(s,t). exec_d G s = TypeError \<and> t = TypeError} \<union>
                  {(s,t). \<exists>t'. exec_d G s = Normal (Some t') \<and> t = Normal t'})\<^sup>*"


declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

lemma [dest!]:
  "(if P then A else B) \<noteq> B \<Longrightarrow> P"
  by (cases P, auto)

lemma exec_d_no_errorI [intro]:
  "check G s \<Longrightarrow> exec_d G (Normal s) \<noteq> TypeError"
  by (unfold exec_d_def) simp

theorem no_type_error_commutes:
  "exec_d G (Normal s) \<noteq> TypeError \<Longrightarrow> 
  exec_d G (Normal s) = Normal (exec (G, s))"
  by (unfold exec_d_def, auto)


lemma defensive_imp_aggressive:
  "G \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> (Normal t) \<Longrightarrow> G \<turnstile> s \<midarrow>jvm\<rightarrow> t"
proof -
  have "\<And>x y. G \<turnstile> x \<midarrow>jvmd\<rightarrow> y \<Longrightarrow> \<forall>s t. x = Normal s \<longrightarrow> y = Normal t \<longrightarrow>  G \<turnstile> s \<midarrow>jvm\<rightarrow> t"
    apply (unfold exec_all_d_def)
    apply (erule rtrancl_induct)
     apply (simp add: exec_all_def)
    apply (fold exec_all_d_def)
    apply simp
    apply (intro allI impI)
    apply (erule disjE, simp)
    apply (elim exE conjE)
    apply (erule allE, erule impE, assumption)
    apply (simp add: exec_all_def exec_d_def split: type_error.splits if_split_asm)
    apply (rule rtrancl_trans, assumption)
    apply blast
    done
  moreover
  assume "G \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> (Normal t)" 
  ultimately
  show "G \<turnstile> s \<midarrow>jvm\<rightarrow> t" by blast
qed

end
