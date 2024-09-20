(*  Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Correctness of the LBV\<close>

theory LBVCorrect
imports LBVSpec Typing_Framework
begin

locale lbvs = lbv +
  fixes s0  :: 'a (\<open>s\<^sub>0\<close>)
  fixes c   :: "'a list"
  fixes ins :: "'b list"
  fixes phi :: "'a list" (\<open>\<phi>\<close>)
  defines phi_def:
  "\<phi> \<equiv> map (\<lambda>pc. if c!pc = \<bottom> then wtl (take pc ins) c 0 s0 else c!pc) 
       [0..<length ins]"

  assumes bounded: "bounded step (length ins)"
  assumes cert: "cert_ok c (length ins) \<top> \<bottom> A"
  assumes pres: "pres_type step (length ins) A"


lemma (in lbvs) phi_None [intro?]:
  "\<lbrakk> pc < length ins; c!pc = \<bottom> \<rbrakk> \<Longrightarrow> \<phi> ! pc = wtl (take pc ins) c 0 s0"
  by (simp add: phi_def)

lemma (in lbvs) phi_Some [intro?]:
  "\<lbrakk> pc < length ins; c!pc \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> \<phi> ! pc = c ! pc"
  by (simp add: phi_def)

lemma (in lbvs) phi_len [simp]:
  "length \<phi> = length ins"
  by (simp add: phi_def)


lemma (in lbvs) wtl_suc_pc:
  assumes all: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" 
  assumes pc:  "pc+1 < length ins"
  shows "wtl (take (pc+1) ins) c 0 s0 \<sqsubseteq>\<^sub>r \<phi>!(pc+1)"
proof -
  from all pc
  have "wtc c (pc+1) (wtl (take (pc+1) ins) c 0 s0) \<noteq> T" by (rule wtl_all)
  with pc show ?thesis by (simp add: phi_def wtc split: if_split_asm)
qed


lemma (in lbvs) wtl_stable:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>" 
  assumes s0:  "s0 \<in> A" 
  assumes pc:  "pc < length ins" 
  shows "stable r step \<phi> pc"
proof (unfold stable_def, clarify)
  fix pc' s' assume step: "(pc',s') \<in> set (step pc (\<phi> ! pc))" 
                      (is "(pc',s') \<in> set (?step pc)")
  
  from bounded pc step have pc': "pc' < length ins" by (rule boundedD)

  from wtl have tkpc: "wtl (take pc ins) c 0 s0 \<noteq> \<top>" (is "?s1 \<noteq> _") by (rule wtl_take)
  from wtl have s2: "wtl (take (pc+1) ins) c 0 s0 \<noteq> \<top>" (is "?s2 \<noteq> _") by (rule wtl_take)
  
  from wtl pc have wt_s1: "wtc c pc ?s1 \<noteq> \<top>" by (rule wtl_all)

  have c_Some: "\<forall>pc t. pc < length ins \<longrightarrow> c!pc \<noteq> \<bottom> \<longrightarrow> \<phi>!pc = c!pc" 
    by (simp add: phi_def)
  from pc have c_None: "c!pc = \<bottom> \<Longrightarrow> \<phi>!pc = ?s1" ..

  from wt_s1 pc c_None c_Some
  have inst: "wtc c pc ?s1  = wti c pc (\<phi>!pc)"
    by (simp add: wtc split: if_split_asm)

  from pres cert s0 wtl pc have "?s1 \<in> A" by (rule wtl_pres)
  with pc c_Some cert c_None
  have "\<phi>!pc \<in> A" by (cases "c!pc = \<bottom>") (auto dest: cert_okD1)
  with pc pres
  have step_in_A: "snd`set (?step pc) \<subseteq> A" by (auto dest: pres_typeD2)

  show "s' <=_r \<phi>!pc'" 
  proof (cases "pc' = pc+1")
    case True
    with pc' cert
    have cert_in_A: "c!(pc+1) \<in> A" by (auto dest: cert_okD1)
    from True pc' have pc1: "pc+1 < length ins" by simp
    with tkpc have "?s2 = wtc c pc ?s1" by - (rule wtl_Suc)
    with inst 
    have merge: "?s2 = merge c pc (?step pc) (c!(pc+1))" by (simp add: wti)
    also    
    from s2 merge have "\<dots> \<noteq> \<top>" (is "?merge \<noteq> _") by simp
    with cert_in_A step_in_A
    have "?merge = (map snd [(p',t') \<leftarrow> ?step pc. p'=pc+1] ++_f (c!(pc+1)))"
      by (rule merge_not_top_s) 
    finally
    have "s' <=_r ?s2" using step_in_A cert_in_A True step 
      by (auto intro: pp_ub1')
    also 
    from wtl pc1 have "?s2 <=_r \<phi>!(pc+1)" by (rule wtl_suc_pc)
    also note True [symmetric]
    finally show ?thesis by simp    
  next
    case False
    from wt_s1 inst
    have "merge c pc (?step pc) (c!(pc+1)) \<noteq> \<top>" by (simp add: wti)
    with step_in_A
    have "\<forall>(pc', s')\<in>set (?step pc). pc'\<noteq>pc+1 \<longrightarrow> s' <=_r c!pc'" 
      by - (rule merge_not_top)
    with step False 
    have ok: "s' <=_r c!pc'" by blast
    moreover
    from ok
    have "c!pc' = \<bottom> \<Longrightarrow> s' = \<bottom>" by simp
    moreover
    from c_Some pc'
    have "c!pc' \<noteq> \<bottom> \<Longrightarrow> \<phi>!pc' = c!pc'" by auto
    ultimately
    show ?thesis by (cases "c!pc' = \<bottom>") auto 
  qed
qed

  
lemma (in lbvs) phi_not_top:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>"
  assumes pc:  "pc < length ins"
  shows "\<phi>!pc \<noteq> \<top>"
proof (cases "c!pc = \<bottom>")
  case False with pc
  have "\<phi>!pc = c!pc" ..
  also from cert pc have "\<dots> \<noteq> \<top>" by (rule cert_okD4)
  finally show ?thesis .
next
  case True with pc
  have "\<phi>!pc = wtl (take pc ins) c 0 s0" ..
  also from wtl have "\<dots> \<noteq> \<top>" by (rule wtl_take)
  finally show ?thesis .
qed

lemma (in lbvs) phi_in_A:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>"
  assumes s0:  "s0 \<in> A"
  shows "\<phi> \<in> list (length ins) A"
proof -
  { fix x assume "x \<in> set \<phi>"
    then obtain xs ys where "\<phi> = xs @ x # ys" 
      by (auto simp add: in_set_conv_decomp)
    then obtain pc where pc: "pc < length \<phi>" and x: "\<phi>!pc = x"
      by (simp add: that [of "length xs"] nth_append)
    
    from pres cert wtl s0 pc
    have "wtl (take pc ins) c 0 s0 \<in> A" by (auto intro!: wtl_pres)
    moreover
    from pc have "pc < length ins" by simp
    with cert have "c!pc \<in> A" ..
    ultimately
    have "\<phi>!pc \<in> A" using pc by (simp add: phi_def)
    hence "x \<in> A" using x by simp
  } 
  hence "set \<phi> \<subseteq> A" ..
  thus ?thesis by (unfold list_def) simp
qed


lemma (in lbvs) phi0:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>"
  assumes 0:   "0 < length ins"
  shows "s0 <=_r \<phi>!0"
proof (cases "c!0 = \<bottom>")
  case True
  with 0 have "\<phi>!0 = wtl (take 0 ins) c 0 s0" ..
  moreover have "wtl (take 0 ins) c 0 s0 = s0" by simp
  ultimately have "\<phi>!0 = s0" by simp
  thus ?thesis by simp
next
  case False
  with 0 have "phi!0 = c!0" ..
  moreover 
  from wtl have "wtl (take 1 ins) c 0 s0 \<noteq> \<top>"  by (rule wtl_take)
  with 0 False 
  have "s0 <=_r c!0" by (auto simp add: neq_Nil_conv wtc split: if_split_asm)
  ultimately
  show ?thesis by simp
qed


theorem (in lbvs) wtl_sound:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>" 
  assumes s0: "s0 \<in> A" 
  shows "\<exists>ts. wt_step r \<top> step ts"
proof -
  have "wt_step r \<top> step \<phi>"
  proof (unfold wt_step_def, intro strip conjI)
    fix pc assume "pc < length \<phi>"
    then have pc: "pc < length ins" by simp
    with wtl show "\<phi>!pc \<noteq> \<top>" by (rule phi_not_top)
    from wtl s0 pc show "stable r step \<phi> pc" by (rule wtl_stable)
  qed
  thus ?thesis ..
qed


theorem (in lbvs) wtl_sound_strong:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>" 
  assumes s0: "s0 \<in> A" 
  assumes nz: "0 < length ins"
  shows "\<exists>ts \<in> list (length ins) A. wt_step r \<top> step ts \<and> s0 <=_r ts!0"
proof -
  from wtl s0 have "\<phi> \<in> list (length ins) A" by (rule phi_in_A)
  moreover
  have "wt_step r \<top> step \<phi>"
  proof (unfold wt_step_def, intro strip conjI)
    fix pc assume "pc < length \<phi>"
    then have pc: "pc < length ins" by simp
    with wtl show "\<phi>!pc \<noteq> \<top>" by (rule phi_not_top)
    from wtl s0 pc show "stable r step \<phi> pc" by (rule wtl_stable)
  qed
  moreover
  from wtl nz have "s0 <=_r \<phi>!0" by (rule phi0)
  ultimately
  show ?thesis by fast
qed

end
