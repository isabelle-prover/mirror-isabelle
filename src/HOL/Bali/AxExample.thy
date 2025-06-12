(*  Title:      HOL/Bali/AxExample.thy
    Author:     David von Oheimb
*)

subsection \<open>Example of a proof based on the Bali axiomatic semantics\<close>

theory AxExample
imports AxSem Example
begin

definition
  arr_inv :: "st \<Rightarrow> bool" where
 "arr_inv = (\<lambda>s. \<exists>obj a T el. globs s (Stat Base) = Some obj \<and>
                              values obj (Inl (arr, Base)) = Some (Addr a) \<and>
                              heap s a = Some \<lparr>tag=Arr T 2,values=el\<rparr>)"

lemma arr_inv_new_obj: 
"\<And>a. \<lbrakk>arr_inv s; new_Addr (heap s)=Some a\<rbrakk> \<Longrightarrow> arr_inv (gupd(Inl a\<mapsto>x) s)"
apply (unfold arr_inv_def)
apply (force dest!: new_AddrD2)
done

lemma arr_inv_set_locals [simp]: "arr_inv (set_locals l s) = arr_inv s"
apply (unfold arr_inv_def)
apply (simp (no_asm))
done

lemma arr_inv_gupd_Stat [simp]: 
  "Base \<noteq> C \<Longrightarrow> arr_inv (gupd(Stat C\<mapsto>obj) s) = arr_inv s"
apply (unfold arr_inv_def)
apply (simp (no_asm_simp))
done

lemma ax_inv_lupd [simp]: "arr_inv (lupd(x\<mapsto>y) s) = arr_inv s"
apply (unfold arr_inv_def)
apply (simp (no_asm))
done


declare if_split_asm [split del]
declare lvar_def [simp]

ML \<open>
fun inst1_tac ctxt s t xs st =
  (case AList.lookup (op =) (rev (Term.add_var_names (Thm.prop_of st) [])) s of
    SOME i => PRIMITIVE (Rule_Insts.read_instantiate ctxt [(((s, i), Position.none), t)] xs) st
  | NONE => Seq.empty);

fun ax_tac ctxt =
  REPEAT o resolve_tac ctxt [allI] THEN'
  resolve_tac ctxt
    @{thms ax_Skip ax_StatRef ax_MethdN ax_Alloc ax_Alloc_Arr ax_SXAlloc_Normal ax_derivs.intros(8-)};
\<close>


theorem ax_test: "tprg,({}::'a triple set)\<turnstile> 
  {Normal (\<lambda>Y s Z::'a. heap_free four s \<and> \<not>initd Base s \<and> \<not> initd Ext s)} 
  .test [Class Base]. 
  {\<lambda>Y s Z. abrupt s = Some (Xcpt (Std IndOutBound))}"
apply (unfold test_def arr_viewed_from_def)
apply (tactic "ax_tac \<^context> 1" (*;;*))
defer (* We begin with the last assertion, to synthesise the intermediate
         assertions, like in the fashion of the weakest
         precondition. *)
apply  (tactic "ax_tac \<^context> 1" (* Try *))
defer
apply    (tactic \<open>inst1_tac \<^context> "Q" 
                 "\<lambda>Y s Z. arr_inv (snd s) \<and> tprg,s\<turnstile>catch SXcpt NullPointer" []\<close>)
prefer 2
apply    simp
apply   (rule_tac P' = "Normal (\<lambda>Y s Z. arr_inv (snd s))" in conseq1)
prefer 2
apply    clarsimp
apply   (rule_tac Q' = "(\<lambda>Y s Z. Q Y s Z)\<leftarrow>=False\<down>=\<diamondsuit>" and Q = Q for Q in conseq2)
prefer 2
apply    simp
apply   (tactic "ax_tac \<^context> 1" (* While *))
prefer 2
apply    (rule ax_impossible [THEN conseq1], clarsimp)
apply   (rule_tac P' = "Normal P" and P = P for P in conseq1)
prefer 2
apply    clarsimp
apply   (tactic "ax_tac \<^context> 1")
apply   (tactic "ax_tac \<^context> 1" (* AVar *))
prefer 2
apply    (rule ax_subst_Val_allI)
apply    (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>a. Normal (PP a\<leftarrow>x)" ["PP", "x"]\<close>)
apply    (simp del: avar_def2 peek_and_def2)
apply    (tactic "ax_tac \<^context> 1")
apply   (tactic "ax_tac \<^context> 1")
      (* just for clarification: *)
apply   (rule_tac Q' = "Normal (\<lambda>Var:(v, f) u ua. fst (snd (avar tprg (Intg 2) v u)) = Some (Xcpt (Std IndOutBound)))" in conseq2)
prefer 2
apply    (clarsimp simp add: split_beta)
apply   (tactic "ax_tac \<^context> 1" (* FVar *))
apply    (tactic "ax_tac \<^context> 2" (* StatRef *))
apply   (rule ax_derivs.Done [THEN conseq1])
apply   (clarsimp simp add: arr_inv_def inited_def in_bounds_def)
defer
apply  (rule ax_SXAlloc_catch_SXcpt)
apply  (rule_tac Q' = "(\<lambda>Y (x, s) Z. x = Some (Xcpt (Std NullPointer)) \<and> arr_inv s) \<and>. heap_free two" in conseq2)
prefer 2
apply   (simp add: arr_inv_new_obj)
apply  (tactic "ax_tac \<^context> 1") 
apply  (rule_tac C = "Ext" in ax_Call_known_DynT)
apply     (unfold DynT_prop_def)
apply     (simp (no_asm))
apply    (intro strip)
apply    (rule_tac P' = "Normal P" and P = P for P in conseq1)
apply     (tactic "ax_tac \<^context> 1" (* Methd *))
apply     (rule ax_thin [OF _ empty_subsetI])
apply     (simp (no_asm) add: body_def2)
apply     (tactic "ax_tac \<^context> 1" (* Body *))
(* apply       (rule_tac [2] ax_derivs.Abrupt) *)
defer
apply      (simp (no_asm))
apply      (tactic "ax_tac \<^context> 1") (* Comp *)
            (* The first statement in the  composition 
                 ((Ext)z).vee = 1; Return Null 
                will throw an exception (since z is null). So we can handle
                Return Null with the Abrupt rule *)
apply       (rule_tac [2] ax_derivs.Abrupt)
             
apply      (rule ax_derivs.Expr) (* Expr *)
apply      (tactic "ax_tac \<^context> 1") (* Ass *)
prefer 2
apply       (rule ax_subst_Var_allI)
apply       (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>a vs l vf. PP a vs l vf\<leftarrow>x \<and>. p" ["PP", "x", "p"]\<close>)
apply       (rule allI)
apply       (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac" |> Simplifier.del_simps [@{thm peek_and_def2}, @{thm heap_def2}, @{thm subst_res_def2}, @{thm normal_def2}]) 1\<close>)
apply       (rule ax_derivs.Abrupt)
apply      (simp (no_asm))
apply      (tactic "ax_tac \<^context> 1" (* FVar *))
apply       (tactic "ax_tac \<^context> 2", tactic "ax_tac \<^context> 2", tactic "ax_tac \<^context> 2")
apply      (tactic "ax_tac \<^context> 1")
apply     (tactic \<open>inst1_tac \<^context> "R" "\<lambda>a'. Normal ((\<lambda>Vals:vs (x, s) Z. arr_inv s \<and> inited Ext (globs s) \<and> a' \<noteq> Null \<and> vs = [Null]) \<and>. heap_free two)" []\<close>)
apply     fastforce
prefer 4
apply    (rule ax_derivs.Done [THEN conseq1],force)
apply   (rule ax_subst_Val_allI)
apply   (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>a. Normal (PP a\<leftarrow>x)" ["PP", "x"]\<close>)
apply   (simp (no_asm) del: peek_and_def2 heap_free_def2 normal_def2 o_apply)
apply   (tactic "ax_tac \<^context> 1")
prefer 2
apply   (rule ax_subst_Val_allI)
apply    (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>aa v. Normal (QQ aa v\<leftarrow>y)" ["QQ", "y"]\<close>)
apply    (simp del: peek_and_def2 heap_free_def2 normal_def2)
apply    (tactic "ax_tac \<^context> 1")
apply   (tactic "ax_tac \<^context> 1")
apply  (tactic "ax_tac \<^context> 1")
apply  (tactic "ax_tac \<^context> 1")
(* end method call *)
apply (simp (no_asm))
    (* just for clarification: *)
apply (rule_tac Q' = "Normal ((\<lambda>Y (x, s) Z. arr_inv s \<and> (\<exists>a. the (locals s (VName e)) = Addr a \<and> obj_class (the (globs s (Inl a))) = Ext \<and> 
 invocation_declclass tprg IntVir s (the (locals s (VName e))) (ClassT Base)  
     \<lparr>name = foo, parTs = [Class Base]\<rparr> = Ext)) \<and>. initd Ext \<and>. heap_free two)"
  in conseq2)
prefer 2
apply  clarsimp
apply (tactic "ax_tac \<^context> 1")
apply (tactic "ax_tac \<^context> 1")
defer
apply  (rule ax_subst_Var_allI)
apply  (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>vf. Normal (PP vf \<and>. p)" ["PP", "p"]\<close>)
apply  (simp (no_asm) del: split_paired_All peek_and_def2 initd_def2 heap_free_def2 normal_def2)
apply  (tactic "ax_tac \<^context> 1" (* NewC *))
apply  (tactic "ax_tac \<^context> 1" (* ax_Alloc *))
     (* just for clarification: *)
apply  (rule_tac Q' = "Normal ((\<lambda>Y s Z. arr_inv (store s) \<and> vf=lvar (VName e) (store s)) \<and>. heap_free three \<and>. initd Ext)" in conseq2)
prefer 2
apply   (simp add: invocation_declclass_def dynmethd_def)
apply   (unfold dynlookup_def)
apply   (simp add: dynmethd_Ext_foo)
apply   (force elim!: arr_inv_new_obj atleast_free_SucD atleast_free_weaken)
     (* begin init *)
apply  (rule ax_InitS)
apply     force
apply    (simp (no_asm))
apply   (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac") 1\<close>)
apply   (rule ax_Init_Skip_lemma)
apply  (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac") 1\<close>)
apply  (rule ax_InitS [THEN conseq1] (* init Base *))
apply      force
apply     (simp (no_asm))
apply    (unfold arr_viewed_from_def)
apply    (rule allI)
apply    (rule_tac P' = "Normal P" and P = P for P in conseq1)
apply     (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac") 1\<close>)
apply     (tactic "ax_tac \<^context> 1")
apply     (tactic "ax_tac \<^context> 1")
apply     (rule_tac [2] ax_subst_Var_allI)
apply      (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>vf l vfa. Normal (P vf l vfa)" ["P"]\<close>)
apply     (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac" |> Simplifier.del_simps [@{thm split_paired_All}, @{thm peek_and_def2}, @{thm heap_free_def2}, @{thm initd_def2}, @{thm normal_def2}, @{thm supd_lupd}]) 2\<close>)
apply      (tactic "ax_tac \<^context> 2" (* NewA *))
apply       (tactic "ax_tac \<^context> 3" (* ax_Alloc_Arr *))
apply       (tactic "ax_tac \<^context> 3")
apply      (tactic \<open>inst1_tac \<^context> "P" "\<lambda>vf l vfa. Normal (P vf l vfa\<leftarrow>\<diamondsuit>)" ["P"]\<close>)
apply      (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac") 2\<close>)
apply      (tactic "ax_tac \<^context> 2")
apply     (tactic "ax_tac \<^context> 1" (* FVar *))
apply      (tactic "ax_tac \<^context> 2" (* StatRef *))
apply     (rule ax_derivs.Done [THEN conseq1])
apply     (tactic \<open>inst1_tac \<^context> "Q" "\<lambda>vf. Normal ((\<lambda>Y s Z. vf=lvar (VName e) (snd s)) \<and>. heap_free four \<and>. initd Base \<and>. initd Ext)" []\<close>)
apply     (clarsimp split del: if_split)
apply     (frule atleast_free_weaken [THEN atleast_free_weaken])
apply     (drule initedD)
apply     (clarsimp elim!: atleast_free_SucD simp add: arr_inv_def)
apply    force
apply   (tactic \<open>simp_tac (\<^context> |> Simplifier.del_loop "split_all_tac") 1\<close>)
apply   (rule ax_triv_Init_Object [THEN peek_and_forget2, THEN conseq1])
apply     (rule wf_tprg)
apply    clarsimp
apply   (tactic \<open>inst1_tac \<^context> "P" "\<lambda>vf. Normal ((\<lambda>Y s Z. vf = lvar (VName e) (snd s)) \<and>. heap_free four \<and>. initd Ext)" []\<close>)
apply   clarsimp
apply  (tactic \<open>inst1_tac \<^context> "PP" "\<lambda>vf. Normal ((\<lambda>Y s Z. vf = lvar (VName e) (snd s)) \<and>. heap_free four \<and>. Not \<circ> initd Base)" []\<close>)
apply  clarsimp
     (* end init *)
apply (rule conseq1)
apply (tactic "ax_tac \<^context> 1")
apply clarsimp
done

(*
while (true) {
  if (i) {throw xcpt;}
  else i=j
}
*)
lemma Loop_Xcpt_benchmark: 
 "Q = (\<lambda>Y (x,s) Z. x \<noteq> None \<longrightarrow> the_Bool (the (locals s i))) \<Longrightarrow>  
  G,({}::'a triple set)\<turnstile>{Normal (\<lambda>Y s Z::'a. True)}  
  .lab1\<bullet> While(Lit (Bool True)) (If(Acc (LVar i)) (Throw (Acc (LVar xcpt))) Else
        (Expr (Ass (LVar i) (Acc (LVar j))))). {Q}"
apply (rule_tac P' = "Q" and Q' = "Q\<leftarrow>=False\<down>=\<diamondsuit>" in conseq12)
apply  safe
apply  (tactic "ax_tac \<^context> 1" (* Loop *))
apply   (rule ax_Normal_cases)
prefer 2
apply    (rule ax_derivs.Abrupt [THEN conseq1], clarsimp simp add: Let_def)
apply   (rule conseq1)
apply    (tactic "ax_tac \<^context> 1")
apply   clarsimp
prefer 2
apply  clarsimp
apply (tactic "ax_tac \<^context> 1" (* If *))
apply  (tactic 
  \<open>inst1_tac \<^context> "P'" "Normal (\<lambda>s.. (\<lambda>Y s Z. True)\<down>=Val (the (locals s i)))" []\<close>)
apply  (tactic "ax_tac \<^context> 1")
apply  (rule conseq1)
apply   (tactic "ax_tac \<^context> 1")
apply  clarsimp
apply (rule allI)
apply (rule ax_escape)
apply auto
apply  (rule conseq1)
apply   (tactic "ax_tac \<^context> 1" (* Throw *))
apply   (tactic "ax_tac \<^context> 1")
apply   (tactic "ax_tac \<^context> 1")
apply  clarsimp
apply (rule_tac Q' = "Normal (\<lambda>Y s Z. True)" in conseq2)
prefer 2
apply  clarsimp
apply (rule conseq1)
apply  (tactic "ax_tac \<^context> 1")
apply  (tactic "ax_tac \<^context> 1")
prefer 2
apply   (rule ax_subst_Var_allI)
apply   (tactic \<open>inst1_tac \<^context> "P'" "\<lambda>b Y ba Z vf. \<lambda>Y (x,s) Z. x=None \<and> snd vf = snd (lvar i s)" []\<close>)
apply   (rule allI)
apply   (rule_tac P' = "Normal P" and P = P for P in conseq1)
prefer 2
apply    clarsimp
apply   (tactic "ax_tac \<^context> 1")
apply   (rule conseq1)
apply    (tactic "ax_tac \<^context> 1")
apply   clarsimp
apply  (tactic "ax_tac \<^context> 1")
apply clarsimp
done

end

