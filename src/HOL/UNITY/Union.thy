(*  Title:      HOL/UNITY/Union.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Partly from Misra's Chapter 5: Asynchronous Compositions of Programs.
*)

section\<open>Unions of Programs\<close>

theory Union imports SubstAx FP begin

  (*FIXME: conjoin Init F \<inter> Init G \<noteq> {} *) 
definition
  ok :: "['a program, 'a program] => bool"      (infixl "ok" 65)
  where "F ok G == Acts F \<subseteq> AllowedActs G &
               Acts G \<subseteq> AllowedActs F"

  (*FIXME: conjoin (\<Inter>i \<in> I. Init (F i)) \<noteq> {} *) 
definition
  OK  :: "['a set, 'a => 'b program] => bool"
  where "OK I F = (\<forall>i \<in> I. \<forall>j \<in> I-{i}. Acts (F i) \<subseteq> AllowedActs (F j))"

definition
  JOIN  :: "['a set, 'a => 'b program] => 'b program"
  where "JOIN I F = mk_program (\<Inter>i \<in> I. Init (F i), \<Union>i \<in> I. Acts (F i),
                             \<Inter>i \<in> I. AllowedActs (F i))"

definition
  Join :: "['a program, 'a program] => 'a program"      (infixl "\<squnion>" 65)
  where "F \<squnion> G = mk_program (Init F \<inter> Init G, Acts F \<union> Acts G,
                             AllowedActs F \<inter> AllowedActs G)"

definition SKIP :: "'a program"  ("\<bottom>")
  where "\<bottom> = mk_program (UNIV, {}, UNIV)"

  (*Characterizes safety properties.  Used with specifying Allowed*)
definition
  safety_prop :: "'a program set => bool"
  where "safety_prop X \<longleftrightarrow> SKIP \<in> X \<and> (\<forall>G. Acts G \<subseteq> \<Union>(Acts ` X) \<longrightarrow> G \<in> X)"

syntax
  "_JOIN1" :: "[pttrns, 'b set] => 'b set"              ("(3\<Squnion>_./ _)" 10)
  "_JOIN"  :: "[pttrn, 'a set, 'b set] => 'b set"       ("(3\<Squnion>_\<in>_./ _)" 10)
syntax_consts
  "_JOIN1" "_JOIN" == JOIN
translations
  "\<Squnion>x \<in> A. B" == "CONST JOIN A (\<lambda>x. B)"
  "\<Squnion>x y. B" == "\<Squnion>x. \<Squnion>y. B"
  "\<Squnion>x. B" == "CONST JOIN (CONST UNIV) (\<lambda>x. B)"


subsection\<open>SKIP\<close>

lemma Init_SKIP [simp]: "Init SKIP = UNIV"
by (simp add: SKIP_def)

lemma Acts_SKIP [simp]: "Acts SKIP = {Id}"
by (simp add: SKIP_def)

lemma AllowedActs_SKIP [simp]: "AllowedActs SKIP = UNIV"
by (auto simp add: SKIP_def)

lemma reachable_SKIP [simp]: "reachable SKIP = UNIV"
by (force elim: reachable.induct intro: reachable.intros)

subsection\<open>SKIP and safety properties\<close>

lemma SKIP_in_constrains_iff [iff]: "(SKIP \<in> A co B) = (A \<subseteq> B)"
by (unfold constrains_def, auto)

lemma SKIP_in_Constrains_iff [iff]: "(SKIP \<in> A Co B) = (A \<subseteq> B)"
by (unfold Constrains_def, auto)

lemma SKIP_in_stable [iff]: "SKIP \<in> stable A"
by (unfold stable_def, auto)

declare SKIP_in_stable [THEN stable_imp_Stable, iff]


subsection\<open>Join\<close>

lemma Init_Join [simp]: "Init (F\<squnion>G) = Init F \<inter> Init G"
by (simp add: Join_def)

lemma Acts_Join [simp]: "Acts (F\<squnion>G) = Acts F \<union> Acts G"
by (auto simp add: Join_def)

lemma AllowedActs_Join [simp]:
     "AllowedActs (F\<squnion>G) = AllowedActs F \<inter> AllowedActs G"
by (auto simp add: Join_def)


subsection\<open>JN\<close>

lemma JN_empty [simp]: "(\<Squnion>i\<in>{}. F i) = SKIP"
by (unfold JOIN_def SKIP_def, auto)

lemma JN_insert [simp]: "(\<Squnion>i \<in> insert a I. F i) = (F a)\<squnion>(\<Squnion>i \<in> I. F i)"
apply (rule program_equalityI)
apply (auto simp add: JOIN_def Join_def)
done

lemma Init_JN [simp]: "Init (\<Squnion>i \<in> I. F i) = (\<Inter>i \<in> I. Init (F i))"
by (simp add: JOIN_def)

lemma Acts_JN [simp]: "Acts (\<Squnion>i \<in> I. F i) = insert Id (\<Union>i \<in> I. Acts (F i))"
by (auto simp add: JOIN_def)

lemma AllowedActs_JN [simp]:
     "AllowedActs (\<Squnion>i \<in> I. F i) = (\<Inter>i \<in> I. AllowedActs (F i))"
by (auto simp add: JOIN_def)


lemma JN_cong [cong]: 
    "[| I=J;  !!i. i \<in> J ==> F i = G i |] ==> (\<Squnion>i \<in> I. F i) = (\<Squnion>i \<in> J. G i)"
by (simp add: JOIN_def)


subsection\<open>Algebraic laws\<close>

lemma Join_commute: "F\<squnion>G = G\<squnion>F"
by (simp add: Join_def Un_commute Int_commute)

lemma Join_assoc: "(F\<squnion>G)\<squnion>H = F\<squnion>(G\<squnion>H)"
by (simp add: Un_ac Join_def Int_assoc insert_absorb)
 
lemma Join_left_commute: "A\<squnion>(B\<squnion>C) = B\<squnion>(A\<squnion>C)"
by (simp add: Un_ac Int_ac Join_def insert_absorb)

lemma Join_SKIP_left [simp]: "SKIP\<squnion>F = F"
apply (unfold Join_def SKIP_def)
apply (rule program_equalityI)
apply (simp_all (no_asm) add: insert_absorb)
done

lemma Join_SKIP_right [simp]: "F\<squnion>SKIP = F"
apply (unfold Join_def SKIP_def)
apply (rule program_equalityI)
apply (simp_all (no_asm) add: insert_absorb)
done

lemma Join_absorb [simp]: "F\<squnion>F = F"
apply (unfold Join_def)
apply (rule program_equalityI, auto)
done

lemma Join_left_absorb: "F\<squnion>(F\<squnion>G) = F\<squnion>G"
apply (unfold Join_def)
apply (rule program_equalityI, auto)
done

(*Join is an AC-operator*)
lemmas Join_ac = Join_assoc Join_left_absorb Join_commute Join_left_commute


subsection\<open>Laws Governing \<open>\<Squnion>\<close>\<close>

(*Also follows by JN_insert and insert_absorb, but the proof is longer*)
lemma JN_absorb: "k \<in> I ==> F k\<squnion>(\<Squnion>i \<in> I. F i) = (\<Squnion>i \<in> I. F i)"
by (auto intro!: program_equalityI)

lemma JN_Un: "(\<Squnion>i \<in> I \<union> J. F i) = ((\<Squnion>i \<in> I. F i)\<squnion>(\<Squnion>i \<in> J. F i))"
by (auto intro!: program_equalityI)

lemma JN_constant: "(\<Squnion>i \<in> I. c) = (if I={} then SKIP else c)"
by (rule program_equalityI, auto)

lemma JN_Join_distrib:
     "(\<Squnion>i \<in> I. F i\<squnion>G i) = (\<Squnion>i \<in> I. F i) \<squnion> (\<Squnion>i \<in> I. G i)"
by (auto intro!: program_equalityI)

lemma JN_Join_miniscope:
     "i \<in> I ==> (\<Squnion>i \<in> I. F i\<squnion>G) = ((\<Squnion>i \<in> I. F i)\<squnion>G)"
by (auto simp add: JN_Join_distrib JN_constant)

(*Used to prove guarantees_JN_I*)
lemma JN_Join_diff: "i \<in> I ==> F i\<squnion>JOIN (I - {i}) F = JOIN I F"
apply (unfold JOIN_def Join_def)
apply (rule program_equalityI, auto)
done


subsection\<open>Safety: co, stable, FP\<close>

(*Fails if I={} because it collapses to SKIP \<in> A co B, i.e. to A \<subseteq> B.  So an
  alternative precondition is A \<subseteq> B, but most proofs using this rule require
  I to be nonempty for other reasons anyway.*)
lemma JN_constrains: 
    "i \<in> I ==> (\<Squnion>i \<in> I. F i) \<in> A co B = (\<forall>i \<in> I. F i \<in> A co B)"
by (simp add: constrains_def JOIN_def, blast)

lemma Join_constrains [simp]:
     "(F\<squnion>G \<in> A co B) = (F \<in> A co B & G \<in> A co B)"
by (auto simp add: constrains_def Join_def)

lemma Join_unless [simp]:
     "(F\<squnion>G \<in> A unless B) = (F \<in> A unless B & G \<in> A unless B)"
by (simp add: unless_def)

(*Analogous weak versions FAIL; see Misra [1994] 5.4.1, Substitution Axiom.
  reachable (F\<squnion>G) could be much bigger than reachable F, reachable G
*)


lemma Join_constrains_weaken:
     "[| F \<in> A co A';  G \<in> B co B' |]  
      ==> F\<squnion>G \<in> (A \<inter> B) co (A' \<union> B')"
by (simp, blast intro: constrains_weaken)

(*If I={}, it degenerates to SKIP \<in> UNIV co {}, which is false.*)
lemma JN_constrains_weaken:
     "[| \<forall>i \<in> I. F i \<in> A i co A' i;  i \<in> I |]  
      ==> (\<Squnion>i \<in> I. F i) \<in> (\<Inter>i \<in> I. A i) co (\<Union>i \<in> I. A' i)"
apply (simp (no_asm_simp) add: JN_constrains)
apply (blast intro: constrains_weaken)
done

lemma JN_stable: "(\<Squnion>i \<in> I. F i) \<in> stable A = (\<forall>i \<in> I. F i \<in> stable A)"
by (simp add: stable_def constrains_def JOIN_def)

lemma invariant_JN_I:
     "[| !!i. i \<in> I ==> F i \<in> invariant A;  i \<in> I |]   
       ==> (\<Squnion>i \<in> I. F i) \<in> invariant A"
by (simp add: invariant_def JN_stable, blast)

lemma Join_stable [simp]:
     "(F\<squnion>G \<in> stable A) =  
      (F \<in> stable A & G \<in> stable A)"
by (simp add: stable_def)

lemma Join_increasing [simp]:
     "(F\<squnion>G \<in> increasing f) =  
      (F \<in> increasing f & G \<in> increasing f)"
by (auto simp add: increasing_def)

lemma invariant_JoinI:
     "[| F \<in> invariant A; G \<in> invariant A |]   
      ==> F\<squnion>G \<in> invariant A"
by (auto simp add: invariant_def)

lemma FP_JN: "FP (\<Squnion>i \<in> I. F i) = (\<Inter>i \<in> I. FP (F i))"
by (simp add: FP_def JN_stable INTER_eq)


subsection\<open>Progress: transient, ensures\<close>

lemma JN_transient:
     "i \<in> I ==>  
    (\<Squnion>i \<in> I. F i) \<in> transient A = (\<exists>i \<in> I. F i \<in> transient A)"
by (auto simp add: transient_def JOIN_def)

lemma Join_transient [simp]:
     "F\<squnion>G \<in> transient A =  
      (F \<in> transient A | G \<in> transient A)"
by (auto simp add: bex_Un transient_def Join_def)

lemma Join_transient_I1: "F \<in> transient A ==> F\<squnion>G \<in> transient A"
by simp

lemma Join_transient_I2: "G \<in> transient A ==> F\<squnion>G \<in> transient A"
by simp

(*If I={} it degenerates to (SKIP \<in> A ensures B) = False, i.e. to ~(A \<subseteq> B) *)
lemma JN_ensures:
     "i \<in> I ==>  
      (\<Squnion>i \<in> I. F i) \<in> A ensures B =  
      ((\<forall>i \<in> I. F i \<in> (A-B) co (A \<union> B)) & (\<exists>i \<in> I. F i \<in> A ensures B))"
by (auto simp add: ensures_def JN_constrains JN_transient)

lemma Join_ensures: 
     "F\<squnion>G \<in> A ensures B =      
      (F \<in> (A-B) co (A \<union> B) & G \<in> (A-B) co (A \<union> B) &  
       (F \<in> transient (A-B) | G \<in> transient (A-B)))"
by (auto simp add: ensures_def)

lemma stable_Join_constrains: 
    "[| F \<in> stable A;  G \<in> A co A' |]  
     ==> F\<squnion>G \<in> A co A'"
apply (unfold stable_def constrains_def Join_def)
apply (simp add: ball_Un, blast)
done

(*Premise for G cannot use Always because  F \<in> Stable A  is weaker than
  G \<in> stable A *)
lemma stable_Join_Always1:
     "[| F \<in> stable A;  G \<in> invariant A |] ==> F\<squnion>G \<in> Always A"
apply (simp (no_asm_use) add: Always_def invariant_def Stable_eq_stable)
apply (force intro: stable_Int)
done

(*As above, but exchanging the roles of F and G*)
lemma stable_Join_Always2:
     "[| F \<in> invariant A;  G \<in> stable A |] ==> F\<squnion>G \<in> Always A"
apply (subst Join_commute)
apply (blast intro: stable_Join_Always1)
done

lemma stable_Join_ensures1:
     "[| F \<in> stable A;  G \<in> A ensures B |] ==> F\<squnion>G \<in> A ensures B"
apply (simp (no_asm_simp) add: Join_ensures)
apply (simp add: stable_def ensures_def)
apply (erule constrains_weaken, auto)
done

(*As above, but exchanging the roles of F and G*)
lemma stable_Join_ensures2:
     "[| F \<in> A ensures B;  G \<in> stable A |] ==> F\<squnion>G \<in> A ensures B"
apply (subst Join_commute)
apply (blast intro: stable_Join_ensures1)
done


subsection\<open>the ok and OK relations\<close>

lemma ok_SKIP1 [iff]: "SKIP ok F"
by (simp add: ok_def)

lemma ok_SKIP2 [iff]: "F ok SKIP"
by (simp add: ok_def)

lemma ok_Join_commute:
     "(F ok G & (F\<squnion>G) ok H) = (G ok H & F ok (G\<squnion>H))"
by (auto simp add: ok_def)

lemma ok_commute: "(F ok G) = (G ok F)"
by (auto simp add: ok_def)

lemmas ok_sym = ok_commute [THEN iffD1]

lemma ok_iff_OK:
     "OK {(0::int,F),(1,G),(2,H)} snd = (F ok G & (F\<squnion>G) ok H)"
apply (simp add: Ball_def conj_disj_distribR ok_def Join_def OK_def insert_absorb
              all_conj_distrib)
apply blast
done

lemma ok_Join_iff1 [iff]: "F ok (G\<squnion>H) = (F ok G & F ok H)"
by (auto simp add: ok_def)

lemma ok_Join_iff2 [iff]: "(G\<squnion>H) ok F = (G ok F & H ok F)"
by (auto simp add: ok_def)

(*useful?  Not with the previous two around*)
lemma ok_Join_commute_I: "[| F ok G; (F\<squnion>G) ok H |] ==> F ok (G\<squnion>H)"
by (auto simp add: ok_def)

lemma ok_JN_iff1 [iff]: "F ok (JOIN I G) = (\<forall>i \<in> I. F ok G i)"
by (auto simp add: ok_def)

lemma ok_JN_iff2 [iff]: "(JOIN I G) ok F =  (\<forall>i \<in> I. G i ok F)"
by (auto simp add: ok_def)

lemma OK_iff_ok: "OK I F = (\<forall>i \<in> I. \<forall>j \<in> I-{i}. (F i) ok (F j))"
by (auto simp add: ok_def OK_def)

lemma OK_imp_ok: "[| OK I F; i \<in> I; j \<in> I; i \<noteq> j|] ==> (F i) ok (F j)"
by (auto simp add: OK_iff_ok)


subsection\<open>Allowed\<close>

lemma Allowed_SKIP [simp]: "Allowed SKIP = UNIV"
by (auto simp add: Allowed_def)

lemma Allowed_Join [simp]: "Allowed (F\<squnion>G) = Allowed F \<inter> Allowed G"
by (auto simp add: Allowed_def)

lemma Allowed_JN [simp]: "Allowed (JOIN I F) = (\<Inter>i \<in> I. Allowed (F i))"
by (auto simp add: Allowed_def)

lemma ok_iff_Allowed: "F ok G = (F \<in> Allowed G & G \<in> Allowed F)"
by (simp add: ok_def Allowed_def)

lemma OK_iff_Allowed: "OK I F = (\<forall>i \<in> I. \<forall>j \<in> I-{i}. F i \<in> Allowed(F j))"
by (auto simp add: OK_iff_ok ok_iff_Allowed)

subsection\<open>\<^term>\<open>safety_prop\<close>, for reasoning about
 given instances of "ok"\<close>

lemma safety_prop_Acts_iff:
     "safety_prop X ==> (Acts G \<subseteq> insert Id (\<Union>(Acts ` X))) = (G \<in> X)"
by (auto simp add: safety_prop_def)

lemma safety_prop_AllowedActs_iff_Allowed:
     "safety_prop X ==> (\<Union>(Acts ` X) \<subseteq> AllowedActs F) = (X \<subseteq> Allowed F)"
by (auto simp add: Allowed_def safety_prop_Acts_iff [symmetric])

lemma Allowed_eq:
     "safety_prop X ==> Allowed (mk_program (init, acts, \<Union>(Acts ` X))) = X"
by (simp add: Allowed_def safety_prop_Acts_iff)

(*For safety_prop to hold, the property must be satisfiable!*)
lemma safety_prop_constrains [iff]: "safety_prop (A co B) = (A \<subseteq> B)"
by (simp add: safety_prop_def constrains_def, blast)

lemma safety_prop_stable [iff]: "safety_prop (stable A)"
by (simp add: stable_def)

lemma safety_prop_Int [simp]:
  "safety_prop X \<Longrightarrow> safety_prop Y \<Longrightarrow> safety_prop (X \<inter> Y)"
proof (clarsimp simp add: safety_prop_def)
  fix G
  assume "\<forall>G. Acts G \<subseteq> (\<Union>x\<in>X. Acts x) \<longrightarrow> G \<in> X"
  then have X: "Acts G \<subseteq> (\<Union>x\<in>X. Acts x) \<Longrightarrow> G \<in> X" by blast
  assume "\<forall>G. Acts G \<subseteq> (\<Union>x\<in>Y. Acts x) \<longrightarrow> G \<in> Y"
  then have Y: "Acts G \<subseteq> (\<Union>x\<in>Y. Acts x) \<Longrightarrow> G \<in> Y" by blast
  assume Acts: "Acts G \<subseteq> (\<Union>x\<in>X \<inter> Y. Acts x)"
  with X and Y show "G \<in> X \<and> G \<in> Y" by auto
qed  

lemma safety_prop_INTER [simp]:
  "(\<And>i. i \<in> I \<Longrightarrow> safety_prop (X i)) \<Longrightarrow> safety_prop (\<Inter>i\<in>I. X i)"
proof (clarsimp simp add: safety_prop_def)
  fix G and i
  assume "\<And>i. i \<in> I \<Longrightarrow> \<bottom> \<in> X i \<and>
    (\<forall>G. Acts G \<subseteq> (\<Union>x\<in>X i. Acts x) \<longrightarrow> G \<in> X i)"
  then have *: "i \<in> I \<Longrightarrow> Acts G \<subseteq> (\<Union>x\<in>X i. Acts x) \<Longrightarrow> G \<in> X i"
    by blast
  assume "i \<in> I"
  moreover assume "Acts G \<subseteq> (\<Union>j\<in>\<Inter>i\<in>I. X i. Acts j)"
  ultimately have "Acts G \<subseteq> (\<Union>i\<in>X i. Acts i)"
    by auto
  with * \<open>i \<in> I\<close> show "G \<in> X i" by blast
qed

lemma safety_prop_INTER1 [simp]:
  "(\<And>i. safety_prop (X i)) \<Longrightarrow> safety_prop (\<Inter>i. X i)"
  by (rule safety_prop_INTER) simp

lemma def_prg_Allowed:
     "[| F == mk_program (init, acts, \<Union>(Acts ` X)) ; safety_prop X |]  
      ==> Allowed F = X"
by (simp add: Allowed_eq)

lemma Allowed_totalize [simp]: "Allowed (totalize F) = Allowed F"
by (simp add: Allowed_def) 

lemma def_total_prg_Allowed:
     "[| F = mk_total_program (init, acts, \<Union>(Acts ` X)) ; safety_prop X |]  
      ==> Allowed F = X"
by (simp add: mk_total_program_def def_prg_Allowed) 

lemma def_UNION_ok_iff:
     "[| F = mk_program(init,acts,\<Union>(Acts ` X)); safety_prop X |]  
      ==> F ok G = (G \<in> X & acts \<subseteq> AllowedActs G)"
by (auto simp add: ok_def safety_prop_Acts_iff)

text\<open>The union of two total programs is total.\<close>
lemma totalize_Join: "totalize F\<squnion>totalize G = totalize (F\<squnion>G)"
by (simp add: program_equalityI totalize_def Join_def image_Un)

lemma all_total_Join: "[|all_total F; all_total G|] ==> all_total (F\<squnion>G)"
by (simp add: all_total_def, blast)

lemma totalize_JN: "(\<Squnion>i \<in> I. totalize (F i)) = totalize(\<Squnion>i \<in> I. F i)"
by (simp add: program_equalityI totalize_def JOIN_def image_UN)

lemma all_total_JN: "(!!i. i\<in>I ==> all_total (F i)) ==> all_total(\<Squnion>i\<in>I. F i)"
by (simp add: all_total_iff_totalize totalize_JN [symmetric])

end
