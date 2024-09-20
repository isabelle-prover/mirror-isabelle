(*  Title:      HOL/MicroJava/BV/BVNoTypeError.thy
    Author:     Gerwin Klein
*)

section \<open>Welltyped Programs produce no Type Errors\<close>

theory BVNoTypeError
imports "../JVM/JVMDefensive" BVSpecTypeSafe
begin

text \<open>
  Some simple lemmas about the type testing functions of the
  defensive JVM:
\<close>
lemma typeof_NoneD [simp,dest]:
  "typeof (\<lambda>v. None) v = Some x \<Longrightarrow> \<not>isAddr v"
  by (cases v) auto

lemma isRef_def2:
  "isRef v = (v = Null \<or> (\<exists>loc. v = Addr loc))"
  by (cases v) (auto simp add: isRef_def)

lemma app'Store[simp]:
  "app' (Store idx, G, pc, maxs, rT, (ST,LT)) = (\<exists>T ST'. ST = T#ST' \<and> idx < length LT)"
  by (cases ST) auto

lemma app'GetField[simp]:
  "app' (Getfield F C, G, pc, maxs, rT, (ST,LT)) =  
  (\<exists>oT vT ST'. ST = oT#ST' \<and> is_class G C \<and>  
  field (G,C) F = Some (C,vT) \<and> G \<turnstile> oT \<preceq> Class C)"
  by (cases ST) auto

lemma app'PutField[simp]:
"app' (Putfield F C, G,  pc, maxs, rT, (ST,LT)) = 
 (\<exists>vT vT' oT ST'. ST = vT#oT#ST' \<and> is_class G C \<and> 
  field (G,C) F = Some (C, vT') \<and> 
  G \<turnstile> oT \<preceq> Class C \<and> G \<turnstile> vT \<preceq> vT')"
  apply rule
  defer
  apply clarsimp
  apply (cases ST)
  apply simp
  apply (cases "tl ST")
  apply auto
  done

lemma app'Checkcast[simp]:
"app' (Checkcast C, G, pc, maxs, rT, (ST,LT)) =
 (\<exists>rT ST'. ST = RefT rT#ST' \<and> is_class G C)"
apply rule
defer
apply clarsimp
apply (cases ST)
apply simp
apply (cases "hd ST")
defer 
apply simp
apply simp
done


lemma app'Pop[simp]: 
  "app' (Pop, G, pc, maxs, rT, (ST,LT)) = (\<exists>T ST'. ST = T#ST')"
  by (cases ST) auto


lemma app'Dup[simp]:
  "app' (Dup, G, pc, maxs, rT, (ST,LT)) =
  (\<exists>T ST'. ST = T#ST' \<and> length ST < maxs)"
  by (cases ST) auto
 

lemma app'Dup_x1[simp]:
  "app' (Dup_x1, G, pc, maxs, rT, (ST,LT)) = 
  (\<exists>T1 T2 ST'. ST = T1#T2#ST' \<and> length ST < maxs)"
  by (cases ST, simp, cases "tl ST", auto)

  
lemma app'Dup_x2[simp]:
  "app' (Dup_x2, G, pc, maxs, rT, (ST,LT)) = 
  (\<exists>T1 T2 T3 ST'. ST = T1#T2#T3#ST' \<and> length ST < maxs)"
  by (cases ST, simp, cases "tl ST", simp, cases "tl (tl ST)", auto)


lemma app'Swap[simp]:
  "app' (Swap, G, pc, maxs, rT, (ST,LT)) = (\<exists>T1 T2 ST'. ST = T1#T2#ST')" 
  by (cases ST, simp, cases "tl ST", auto)

  
lemma app'IAdd[simp]:
  "app' (IAdd, G, pc, maxs, rT, (ST,LT)) = 
  (\<exists>ST'. ST = PrimT Integer#PrimT Integer#ST')"
  apply (cases ST)
  apply simp
  apply simp
  apply (case_tac a)
  apply auto
  apply (rename_tac prim_ty, case_tac prim_ty)
  apply auto
  apply (rename_tac prim_ty, case_tac prim_ty)
  apply auto
  apply (case_tac list)
  apply auto
  apply (case_tac a)
  apply auto
  apply (rename_tac prim_ty, case_tac prim_ty)
  apply auto
  done
 

lemma app'Ifcmpeq[simp]:
  "app' (Ifcmpeq b, G, pc, maxs, rT, (ST,LT)) =
  (\<exists>T1 T2 ST'. ST = T1#T2#ST' \<and> 0 \<le> b + int pc \<and> 
  ((\<exists>p. T1 = PrimT p \<and> T1 = T2) \<or> 
  (\<exists>r r'. T1 = RefT r \<and> T2 = RefT r')))" 
  apply auto
  apply (cases ST)
  apply simp
  apply (cases "tl ST")
  apply (case_tac a)
  apply auto
  done
  

lemma app'Return[simp]:
  "app' (Return, G, pc, maxs, rT, (ST,LT)) = 
  (\<exists>T ST'. ST = T#ST'\<and> G \<turnstile> T \<preceq> rT)" 
  by (cases ST) auto


lemma app'Throw[simp]:
  "app' (Throw, G, pc, maxs, rT, (ST,LT)) = 
  (\<exists>ST' r. ST = RefT r#ST')"
  apply (cases ST)
  apply simp
  apply (cases "hd ST")
  apply auto
  done

  
lemma app'Invoke[simp]:
"app' (Invoke C mn fpTs, G, pc, maxs, rT, ST, LT) = 
 (\<exists>apTs X ST' mD' rT' b'.
  ST = (rev apTs) @ X # ST' \<and> 
  length apTs = length fpTs \<and> is_class G C \<and>
  (\<forall>(aT,fT)\<in>set(zip apTs fpTs). G \<turnstile> aT \<preceq> fT) \<and> 
  method (G,C) (mn,fpTs) = Some (mD', rT', b') \<and> G \<turnstile> X \<preceq> Class C)"
  (is "?app ST LT = ?P ST LT")
proof
  assume "?P ST LT" thus "?app ST LT" by (auto simp add: list_all2_iff)
next  
  assume app: "?app ST LT"
  hence l: "length fpTs < length ST" by simp
  obtain xs ys where xs: "ST = xs @ ys" "length xs = length fpTs"
  proof -
    have "ST = take (length fpTs) ST @ drop (length fpTs) ST" by simp
    moreover from l have "length (take (length fpTs) ST) = length fpTs"
      by simp
    ultimately show ?thesis ..
  qed
  obtain apTs where
    "ST = (rev apTs) @ ys" and "length apTs = length fpTs"
  proof -
    from xs(1) have "ST = rev (rev xs) @ ys" by simp
    then show thesis by (rule that) (simp add: xs(2))
  qed
  moreover
  from l xs obtain X ST' where "ys = X#ST'" by (auto simp add: neq_Nil_conv)
  ultimately
  have "ST = (rev apTs) @ X # ST'" "length apTs = length fpTs" by auto
  with app
  show "?P ST LT"
    apply (clarsimp simp add: list_all2_iff)
    apply (intro exI conjI)
    apply auto
    done
qed

lemma approx_loc_len [simp]:
  "approx_loc G hp loc LT \<Longrightarrow> length loc = length LT"
  by (simp add: approx_loc_def list_all2_iff)

lemma approx_stk_len [simp]:
  "approx_stk G hp stk ST \<Longrightarrow> length stk = length ST"
  by (simp add: approx_stk_def)

lemma isRefI [intro, simp]: "G,hp \<turnstile> v ::\<preceq> RefT T \<Longrightarrow> isRef v"
  apply (drule conf_RefTD)
  apply (auto simp add: isRef_def)
  done

lemma isIntgI [intro, simp]: "G,hp \<turnstile> v ::\<preceq> PrimT Integer \<Longrightarrow> isIntg v"
  apply (unfold conf_def)
  apply auto
  apply (erule widen.cases)
  apply auto
  apply (cases v)
  apply auto
  done

lemma list_all2_approx:
  "list_all2 (approx_val G hp) s (map OK S) = list_all2 (conf G hp) s S"
  apply (induct S arbitrary: s)
  apply (auto simp add: list_all2_Cons2 approx_val_def)
  done

lemma list_all2_conf_widen:
  "wf_prog mb G \<Longrightarrow>
  list_all2 (conf G hp) a b \<Longrightarrow>
  list_all2 (\<lambda>x y. G \<turnstile> x \<preceq> y) b c \<Longrightarrow>
  list_all2 (conf G hp) a c"
  apply (rule list_all2_trans)
  defer
  apply assumption
  apply assumption
  apply (drule conf_widen, assumption+)
  done


text \<open>
  The main theorem: welltyped programs do not produce type errors if they
  are started in a conformant state.
\<close>
theorem no_type_error:
  assumes welltyped: "wt_jvm_prog G Phi" and conforms: "G,Phi \<turnstile>JVM s \<surd>"
  shows "exec_d G (Normal s) \<noteq> TypeError"
proof -
  from welltyped obtain mb where wf: "wf_prog mb G" by (fast dest: wt_jvm_progD)
  
  obtain xcp hp frs where s [simp]: "s = (xcp, hp, frs)" by (cases s)

  from conforms have "xcp \<noteq> None \<or> frs = [] \<Longrightarrow> check G s" 
    by (unfold correct_state_def check_def) auto
  moreover {
    assume "\<not>(xcp \<noteq> None \<or> frs = [])"
    then obtain stk loc C sig pc frs' where
      xcp [simp]: "xcp = None" and
      frs [simp]: "frs = (stk,loc,C,sig,pc)#frs'" 
      by (clarsimp simp add: neq_Nil_conv)

    from conforms obtain  ST LT rT maxs maxl ins et where
      hconf:  "G \<turnstile>h hp \<surd>" and
      "class":  "is_class G C" and
      meth:   "method (G, C) sig = Some (C, rT, maxs, maxl, ins, et)" and
      phi:    "Phi C sig ! pc = Some (ST,LT)" and
      frame:  "correct_frame G hp (ST,LT) maxl ins (stk,loc,C,sig,pc)" and
      frames: "correct_frames G hp Phi rT sig frs'"
      by (auto simp add: correct_state_def)

    from frame obtain
      stk: "approx_stk G hp stk ST" and
      loc: "approx_loc G hp loc LT" and
      pc:  "pc < length ins" and
      len: "length loc = length (snd sig) + maxl + 1"
      by (auto simp add: correct_frame_def)

    note approx_val_def [simp]

    from welltyped meth conforms
    have "wt_instr (ins!pc) G rT (Phi C sig) maxs (length ins) et pc"
      by simp (rule wt_jvm_prog_impl_wt_instr_cor)    
    then obtain
      app': "app (ins!pc) G maxs rT pc et (Phi C sig!pc) " and
      eff: "\<forall>(pc', s')\<in>set (eff (ins ! pc) G pc et (Phi C sig ! pc)). pc' < length ins"
      by (simp add: wt_instr_def phi) blast

    from eff 
    have pc': "\<forall>pc' \<in> set (succs (ins!pc) pc). pc' < length ins"
      by (simp add: eff_def) blast

    from app' phi
    have app:
      "xcpt_app (ins!pc) G pc et \<and> app' (ins!pc, G, pc, maxs, rT, (ST,LT))"
      by (clarsimp simp add: app_def)

    with eff stk loc pc'
    have "check_instr (ins!pc) G hp stk loc C sig pc maxs frs'"
    proof (cases "ins!pc")
      case (Getfield F C) 
      with app stk loc phi obtain v vT stk' where
        "class": "is_class G C" and
        field: "field (G, C) F = Some (C, vT)" and
        stk:   "stk = v # stk'" and
        conf:  "G,hp \<turnstile> v ::\<preceq> Class C"
        apply clarsimp
        apply (blast dest: conf_widen [OF wf])
        done
      from conf have isRef: "isRef v" ..
      moreover {
        assume "v \<noteq> Null" 
        with conf field isRef wf
        have "\<exists>D vs. hp (the_Addr v) = Some (D,vs) \<and> G \<turnstile> D \<preceq>C C" 
          by (auto dest!: non_np_objD)
      }
      ultimately show ?thesis using Getfield field "class" stk hconf wf
        apply clarsimp
        apply (fastforce dest!: hconfD widen_cfs_fields oconf_objD)
        done
    next
      case (Putfield F C)
      with app stk loc phi obtain v ref vT stk' where
        "class": "is_class G C" and
        field: "field (G, C) F = Some (C, vT)" and
        stk:   "stk = v # ref # stk'" and
        confv: "G,hp \<turnstile> v ::\<preceq> vT" and
        confr: "G,hp \<turnstile> ref ::\<preceq> Class C"
        apply clarsimp
        apply (blast dest: conf_widen [OF wf])
        done
      from confr have isRef: "isRef ref" ..
      moreover {
        assume "ref \<noteq> Null" 
        with confr field isRef wf
        have "\<exists>D vs. hp (the_Addr ref) = Some (D,vs) \<and> G \<turnstile> D \<preceq>C C"
          by (auto dest: non_np_objD)
      }
      ultimately show ?thesis using Putfield field "class" stk confv
        by clarsimp
    next      
      case (Invoke C mn ps)
      with app
      obtain apTs X ST' where
        ST: "ST = rev apTs @ X # ST'" and
        ps: "length apTs = length ps" and
        w:   "\<forall>(x, y)\<in>set (zip apTs ps). G \<turnstile> x \<preceq> y" and
        C:   "G \<turnstile> X \<preceq> Class C" and
        mth: "method (G, C) (mn, ps) \<noteq> None"
        by (simp del: app'.simps) blast
        
      from ST stk
      obtain aps x stk' where
        stk': "stk = aps @ x # stk'" and
        aps: "approx_stk G hp aps (rev apTs)" and
        x: "G,hp \<turnstile> x ::\<preceq> X" and        
        l: "length aps = length apTs"
        by (auto dest!: approx_stk_append)
      
      from stk' l ps 
      have [simp]: "stk!length ps = x" by (simp add: nth_append)
      from stk' l ps
      have [simp]: "take (length ps) stk = aps" by simp
      from w ps
      have widen: "list_all2 (\<lambda>x y. G \<turnstile> x \<preceq> y) apTs ps"
        by (simp add: list_all2_iff) 

      from stk' l ps have "length ps < length stk" by simp
      moreover
      from wf x C 
      have x: "G,hp \<turnstile> x ::\<preceq> Class C" by (rule conf_widen) 
      hence "isRef x" by simp
      moreover
      { assume "x \<noteq> Null"
        with x
        obtain D fs where
          hp: "hp (the_Addr x) = Some (D,fs)" and
          D:  "G \<turnstile> D \<preceq>C C"
          by (auto dest: non_npD)
        hence "hp (the_Addr x) \<noteq> None" (is ?P1) by simp
        moreover
        from wf mth hp D
        have "method (G, cname_of hp x) (mn, ps) \<noteq> None" (is ?P2)
          by (auto dest: subcls_widen_methd)
        moreover
        from aps have "list_all2 (conf G hp) aps (rev apTs)"
          by (simp add: list_all2_approx approx_stk_def approx_loc_def)        
        hence "list_all2 (conf G hp) (rev aps) (rev (rev apTs))"
          by (simp only: list_all2_rev)
        hence "list_all2 (conf G hp) (rev aps) apTs" by simp
        from wf this widen
        have "list_all2 (conf G hp) (rev aps) ps" (is ?P3)
          by (rule list_all2_conf_widen) 
        ultimately
        have "?P1 \<and> ?P2 \<and> ?P3" by blast
      }
      moreover 
      note Invoke
      ultimately
      show ?thesis by simp
    next
      case Return with stk app phi meth frames 
      show ?thesis        
        apply clarsimp
        apply (drule conf_widen [OF wf], assumption)
        apply (clarsimp simp add: neq_Nil_conv isRef_def2)
        done
    qed auto
    hence "check G s" by (simp add: check_def meth pc)
  } ultimately
  have "check G s" by blast
  thus "exec_d G (Normal s) \<noteq> TypeError" ..
qed


text \<open>
  The theorem above tells us that, in welltyped programs, the
  defensive machine reaches the same result as the aggressive
  one (after arbitrarily many steps).
\<close>
theorem welltyped_aggressive_imp_defensive:
  "wt_jvm_prog G Phi \<Longrightarrow> G,Phi \<turnstile>JVM s \<surd> \<Longrightarrow> G \<turnstile> s \<midarrow>jvm\<rightarrow> t 
  \<Longrightarrow> G \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> (Normal t)"
  apply (unfold exec_all_def) 
  apply (erule rtrancl_induct)
   apply (simp add: exec_all_d_def)
  apply simp
  apply (fold exec_all_def)
  apply (frule BV_correct, assumption+)
  apply (drule no_type_error, assumption, drule no_type_error_commutes, simp)
  apply (simp add: exec_all_d_def)
  apply (rule rtrancl_trans, assumption)
  apply blast
  done


lemma neq_TypeError_eq [simp]: "s \<noteq> TypeError = (\<exists>s'. s = Normal s')"
  by (cases s, auto)

theorem no_type_errors:
  "wt_jvm_prog G Phi \<Longrightarrow> G,Phi \<turnstile>JVM s \<surd>
  \<Longrightarrow> G \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> t \<Longrightarrow> t \<noteq> TypeError"
  apply (unfold exec_all_d_def)   
  apply (erule rtrancl_induct)
   apply simp
  apply (fold exec_all_d_def)
  apply (auto dest: defensive_imp_aggressive BV_correct no_type_error)
  done

corollary no_type_errors_initial:
  fixes G (\<open>\<Gamma>\<close>) and Phi (\<open>\<Phi>\<close>)
  assumes wt: "wt_jvm_prog \<Gamma> \<Phi>"  
  assumes is_class: "is_class \<Gamma> C"
    and "method": "method (\<Gamma>,C) (m,[]) = Some (C, b)"
    and m: "m \<noteq> init"
  defines start: "s \<equiv> start_state \<Gamma> C m"

  assumes s: "\<Gamma> \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> t" 
  shows "t \<noteq> TypeError"
proof -
  from wt is_class "method" have "\<Gamma>,\<Phi> \<turnstile>JVM s \<surd>"
    unfolding start by (rule BV_correct_initial)
  from wt this s show ?thesis by (rule no_type_errors)
qed

text \<open>
  As corollary we get that the aggressive and the defensive machine
  are equivalent for welltyped programs (if started in a conformant
  state or in the canonical start state)
\<close> 
corollary welltyped_commutes:
  fixes G (\<open>\<Gamma>\<close>) and Phi (\<open>\<Phi>\<close>)
  assumes wt: "wt_jvm_prog \<Gamma> \<Phi>" and *: "\<Gamma>,\<Phi> \<turnstile>JVM s \<surd>" 
  shows "\<Gamma> \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> (Normal t) = \<Gamma> \<turnstile> s \<midarrow>jvm\<rightarrow> t"
  apply rule
   apply (erule defensive_imp_aggressive, rule welltyped_aggressive_imp_defensive)
    apply (rule wt)
   apply (rule *)
  apply assumption
  done

corollary welltyped_initial_commutes:
  fixes G (\<open>\<Gamma>\<close>) and Phi (\<open>\<Phi>\<close>)
  assumes wt: "wt_jvm_prog \<Gamma> \<Phi>"  
  assumes is_class: "is_class \<Gamma> C"
    and "method": "method (\<Gamma>,C) (m,[]) = Some (C, b)"
    and m: "m \<noteq> init"
  defines start: "s \<equiv> start_state \<Gamma> C m"
  shows "\<Gamma> \<turnstile> (Normal s) \<midarrow>jvmd\<rightarrow> (Normal t) = \<Gamma> \<turnstile> s \<midarrow>jvm\<rightarrow> t"
proof -
  from wt is_class "method" have "\<Gamma>,\<Phi> \<turnstile>JVM s \<surd>"
    unfolding start by (rule BV_correct_initial)
  with wt show ?thesis by (rule welltyped_commutes)
qed
 
end  
