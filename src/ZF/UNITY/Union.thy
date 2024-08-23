(*  Title:      ZF/UNITY/Union.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Unions of programs

Partly from Misra's Chapter 5 \<in> Asynchronous Compositions of Programs

Theory ported form HOL..

*)

theory Union imports SubstAx FP
begin

definition
  (*FIXME: conjoin Init(F) \<inter> Init(G) \<noteq> 0 *)
  ok :: "[i, i] \<Rightarrow> o"     (infixl \<open>ok\<close> 65)  where
    "F ok G \<equiv> Acts(F) \<subseteq> AllowedActs(G) \<and>
               Acts(G) \<subseteq> AllowedActs(F)"

definition
  (*FIXME: conjoin (\<Inter>i \<in> I. Init(F(i))) \<noteq> 0 *)
  OK  :: "[i, i\<Rightarrow>i] \<Rightarrow> o"  where
    "OK(I,F) \<equiv> (\<forall>i \<in> I. \<forall>j \<in> I-{i}. Acts(F(i)) \<subseteq> AllowedActs(F(j)))"

definition
  JOIN  :: "[i, i\<Rightarrow>i] \<Rightarrow> i"  where
  "JOIN(I,F) \<equiv> if I = 0 then SKIP else
                 mk_program(\<Inter>i \<in> I. Init(F(i)), \<Union>i \<in> I. Acts(F(i)),
                 \<Inter>i \<in> I. AllowedActs(F(i)))"

definition
  Join :: "[i, i] \<Rightarrow> i"  (infixl \<open>\<squnion>\<close> 65)  where
  "F \<squnion> G \<equiv> mk_program (Init(F) \<inter> Init(G), Acts(F) \<union> Acts(G),
                                AllowedActs(F) \<inter> AllowedActs(G))"
definition
  (*Characterizes safety properties.  Used with specifying AllowedActs*)
  safety_prop :: "i \<Rightarrow> o"  where
  "safety_prop(X) \<equiv> X\<subseteq>program \<and>
      SKIP \<in> X \<and> (\<forall>G \<in> program. Acts(G) \<subseteq> (\<Union>F \<in> X. Acts(F)) \<longrightarrow> G \<in> X)"

syntax
  "_JOIN1"  :: "[pttrns, i] \<Rightarrow> i"     (\<open>(3\<Squnion>_./ _)\<close> 10)
  "_JOIN"   :: "[pttrn, i, i] \<Rightarrow> i"   (\<open>(3\<Squnion>_ \<in> _./ _)\<close> 10)
translations
  "\<Squnion>x \<in> A. B" == "CONST JOIN(A, (\<lambda>x. B))"
  "\<Squnion>x y. B"   == "\<Squnion>x. \<Squnion>y. B"
  "\<Squnion>x. B"     == "CONST JOIN(CONST state, (\<lambda>x. B))"
syntax_consts
  "_JOIN1" "_JOIN" == JOIN


subsection\<open>SKIP\<close>

lemma reachable_SKIP [simp]: "reachable(SKIP) = state"
by (force elim: reachable.induct intro: reachable.intros)

text\<open>Elimination programify from ok and \<squnion>\<close>

lemma ok_programify_left [iff]: "programify(F) ok G \<longleftrightarrow> F ok G"
by (simp add: ok_def)

lemma ok_programify_right [iff]: "F ok programify(G) \<longleftrightarrow> F ok G"
by (simp add: ok_def)

lemma Join_programify_left [simp]: "programify(F) \<squnion> G = F \<squnion> G"
by (simp add: Join_def)

lemma Join_programify_right [simp]: "F \<squnion> programify(G) = F \<squnion> G"
by (simp add: Join_def)

subsection\<open>SKIP and safety properties\<close>

lemma SKIP_in_constrains_iff [iff]: "(SKIP \<in> A co B) \<longleftrightarrow> (A\<subseteq>B \<and> st_set(A))"
by (unfold constrains_def st_set_def, auto)

lemma SKIP_in_Constrains_iff [iff]: "(SKIP \<in> A Co B)\<longleftrightarrow> (state \<inter> A\<subseteq>B)"
by (unfold Constrains_def, auto)

lemma SKIP_in_stable [iff]: "SKIP \<in> stable(A) \<longleftrightarrow> st_set(A)"
by (auto simp add: stable_def)

lemma SKIP_in_Stable [iff]: "SKIP \<in> Stable(A)"
by (unfold Stable_def, auto)

subsection\<open>Join and JOIN types\<close>

lemma Join_in_program [iff,TC]: "F \<squnion> G \<in> program"
by (unfold Join_def, auto)

lemma JOIN_in_program [iff,TC]: "JOIN(I,F) \<in> program"
by (unfold JOIN_def, auto)

subsection\<open>Init, Acts, and AllowedActs of Join and JOIN\<close>
lemma Init_Join [simp]: "Init(F \<squnion> G) = Init(F) \<inter> Init(G)"
by (simp add: Int_assoc Join_def)

lemma Acts_Join [simp]: "Acts(F \<squnion> G) = Acts(F) \<union> Acts(G)"
by (simp add: Int_Un_distrib2 cons_absorb Join_def)

lemma AllowedActs_Join [simp]: "AllowedActs(F \<squnion> G) =
  AllowedActs(F) \<inter> AllowedActs(G)"
apply (simp add: Int_assoc cons_absorb Join_def)
done

subsection\<open>Join's algebraic laws\<close>

lemma Join_commute: "F \<squnion> G = G \<squnion> F"
by (simp add: Join_def Un_commute Int_commute)

lemma Join_left_commute: "A \<squnion> (B \<squnion> C) = B \<squnion> (A \<squnion> C)"
apply (simp add: Join_def Int_Un_distrib2 cons_absorb)
apply (simp add: Un_ac Int_ac Int_Un_distrib2 cons_absorb)
done

lemma Join_assoc: "(F \<squnion> G) \<squnion> H = F \<squnion> (G \<squnion> H)"
by (simp add: Un_ac Join_def cons_absorb Int_assoc Int_Un_distrib2)

subsection\<open>Needed below\<close>
lemma cons_id [simp]: "cons(id(state), Pow(state * state)) = Pow(state*state)"
by auto

lemma Join_SKIP_left [simp]: "SKIP \<squnion> F = programify(F)"
  unfolding Join_def SKIP_def
apply (auto simp add: Int_absorb cons_eq)
done

lemma Join_SKIP_right [simp]: "F \<squnion> SKIP =  programify(F)"
apply (subst Join_commute)
apply (simp add: Join_SKIP_left)
done

lemma Join_absorb [simp]: "F \<squnion> F = programify(F)"
by (rule program_equalityI, auto)

lemma Join_left_absorb: "F \<squnion> (F \<squnion> G) = F \<squnion> G"
by (simp add: Join_assoc [symmetric])

subsection\<open>Join is an AC-operator\<close>
lemmas Join_ac = Join_assoc Join_left_absorb Join_commute Join_left_commute

subsection\<open>Eliminating programify form JOIN and OK expressions\<close>

lemma OK_programify [iff]: "OK(I, \<lambda>x. programify(F(x))) \<longleftrightarrow> OK(I, F)"
by (simp add: OK_def)

lemma JOIN_programify [iff]: "JOIN(I, \<lambda>x. programify(F(x))) = JOIN(I, F)"
by (simp add: JOIN_def)


subsection\<open>JOIN\<close>

lemma JOIN_empty [simp]: "JOIN(0, F) = SKIP"
by (unfold JOIN_def, auto)

lemma Init_JOIN [simp]:
     "Init(\<Squnion>i \<in> I. F(i)) = (if I=0 then state else (\<Inter>i \<in> I. Init(F(i))))"
by (simp add: JOIN_def INT_extend_simps del: INT_simps)

lemma Acts_JOIN [simp]:
     "Acts(JOIN(I,F)) = cons(id(state), \<Union>i \<in> I.  Acts(F(i)))"
  unfolding JOIN_def
apply (auto simp del: INT_simps UN_simps)
apply (rule equalityI)
apply (auto dest: Acts_type [THEN subsetD])
done

lemma AllowedActs_JOIN [simp]:
     "AllowedActs(\<Squnion>i \<in> I. F(i)) =
      (if I=0 then Pow(state*state) else (\<Inter>i \<in> I. AllowedActs(F(i))))"
apply (unfold JOIN_def, auto)
apply (rule equalityI)
apply (auto elim!: not_emptyE dest: AllowedActs_type [THEN subsetD])
done

lemma JOIN_cons [simp]: "(\<Squnion>i \<in> cons(a,I). F(i)) = F(a) \<squnion> (\<Squnion>i \<in> I. F(i))"
by (rule program_equalityI, auto)

lemma JOIN_cong [cong]:
    "\<lbrakk>I=J;  \<And>i. i \<in> J \<Longrightarrow> F(i) = G(i)\<rbrakk> \<Longrightarrow>
     (\<Squnion>i \<in> I. F(i)) = (\<Squnion>i \<in> J. G(i))"
by (simp add: JOIN_def)



subsection\<open>JOIN laws\<close>
lemma JOIN_absorb: "k \<in> I \<Longrightarrow>F(k) \<squnion> (\<Squnion>i \<in> I. F(i)) = (\<Squnion>i \<in> I. F(i))"
apply (subst JOIN_cons [symmetric])
apply (auto simp add: cons_absorb)
done

lemma JOIN_Un: "(\<Squnion>i \<in> I \<union> J. F(i)) = ((\<Squnion>i \<in> I. F(i)) \<squnion> (\<Squnion>i \<in> J. F(i)))"
apply (rule program_equalityI)
apply (simp_all add: UN_Un INT_Un)
apply (simp_all del: INT_simps add: INT_extend_simps, blast)
done

lemma JOIN_constant: "(\<Squnion>i \<in> I. c) = (if I=0 then SKIP else programify(c))"
by (rule program_equalityI, auto)

lemma JOIN_Join_distrib:
     "(\<Squnion>i \<in> I. F(i) \<squnion> G(i)) = (\<Squnion>i \<in> I. F(i))  \<squnion>  (\<Squnion>i \<in> I. G(i))"
apply (rule program_equalityI)
apply (simp_all add: INT_Int_distrib, blast)
done

lemma JOIN_Join_miniscope: "(\<Squnion>i \<in> I. F(i) \<squnion> G) = ((\<Squnion>i \<in> I. F(i) \<squnion> G))"
by (simp add: JOIN_Join_distrib JOIN_constant)

text\<open>Used to prove guarantees_JOIN_I\<close>
lemma JOIN_Join_diff: "i \<in> I\<Longrightarrow>F(i) \<squnion> JOIN(I - {i}, F) = JOIN(I, F)"
apply (rule program_equalityI)
apply (auto elim!: not_emptyE)
done

subsection\<open>Safety: co, stable, FP\<close>


(*Fails if I=0 because it collapses to SKIP \<in> A co B, i.e. to A\<subseteq>B.  So an
  alternative precondition is A\<subseteq>B, but most proofs using this rule require
  I to be nonempty for other reasons anyway.*)

lemma JOIN_constrains:
 "i \<in> I\<Longrightarrow>(\<Squnion>i \<in> I. F(i)) \<in> A co B \<longleftrightarrow> (\<forall>i \<in> I. programify(F(i)) \<in> A co B)"

apply (unfold constrains_def JOIN_def st_set_def, auto)
prefer 2 apply blast
apply (rename_tac j act y z)
apply (cut_tac F = "F (j) " in Acts_type)
apply (drule_tac x = act in bspec, auto)
done

lemma Join_constrains [iff]:
     "(F \<squnion> G \<in> A co B) \<longleftrightarrow> (programify(F) \<in> A co B \<and> programify(G) \<in> A co B)"
by (auto simp add: constrains_def)

lemma Join_unless [iff]:
     "(F \<squnion> G \<in> A unless B) \<longleftrightarrow>
    (programify(F) \<in> A unless B \<and> programify(G) \<in> A unless B)"
by (simp add: Join_constrains unless_def)


(*Analogous weak versions FAIL; see Misra [1994] 5.4.1, Substitution Axiom.
  reachable (F \<squnion> G) could be much bigger than reachable F, reachable G
*)

lemma Join_constrains_weaken:
     "\<lbrakk>F \<in> A co A';  G \<in> B co B'\<rbrakk>
      \<Longrightarrow> F \<squnion> G \<in> (A \<inter> B) co (A' \<union> B')"
apply (subgoal_tac "st_set (A) \<and> st_set (B) \<and> F \<in> program \<and> G \<in> program")
prefer 2 apply (blast dest: constrainsD2, simp)
apply (blast intro: constrains_weaken)
done

(*If I=0, it degenerates to SKIP \<in> state co 0, which is false.*)
lemma JOIN_constrains_weaken:
  assumes major: "(\<And>i. i \<in> I \<Longrightarrow> F(i) \<in> A(i) co A'(i))"
      and minor: "i \<in> I"
  shows "(\<Squnion>i \<in> I. F(i)) \<in> (\<Inter>i \<in> I. A(i)) co (\<Union>i \<in> I. A'(i))"
apply (cut_tac minor)
apply (simp (no_asm_simp) add: JOIN_constrains)
apply clarify
apply (rename_tac "j")
apply (frule_tac i = j in major)
apply (frule constrainsD2, simp)
apply (blast intro: constrains_weaken)
done

lemma JOIN_stable:
     "(\<Squnion>i \<in> I. F(i)) \<in>  stable(A) \<longleftrightarrow> ((\<forall>i \<in> I. programify(F(i)) \<in> stable(A)) \<and> st_set(A))"
apply (auto simp add: stable_def constrains_def JOIN_def)
apply (cut_tac F = "F (i) " in Acts_type)
apply (drule_tac x = act in bspec, auto)
done

lemma initially_JOIN_I:
  assumes major: "(\<And>i. i \<in> I \<Longrightarrow>F(i) \<in> initially(A))"
      and minor: "i \<in> I"
  shows  "(\<Squnion>i \<in> I. F(i)) \<in> initially(A)"
apply (cut_tac minor)
apply (auto elim!: not_emptyE simp add: Inter_iff initially_def)
apply (frule_tac i = x in major)
apply (auto simp add: initially_def)
done

lemma invariant_JOIN_I:
  assumes major: "(\<And>i. i \<in> I \<Longrightarrow> F(i) \<in> invariant(A))"
      and minor: "i \<in> I"
  shows "(\<Squnion>i \<in> I. F(i)) \<in> invariant(A)"
apply (cut_tac minor)
apply (auto intro!: initially_JOIN_I dest: major simp add: invariant_def JOIN_stable)
apply (erule_tac V = "i \<in> I" in thin_rl)
apply (frule major)
apply (drule_tac [2] major)
apply (auto simp add: invariant_def)
apply (frule stableD2, force)+
done

lemma Join_stable [iff]:
     " (F \<squnion> G \<in> stable(A)) \<longleftrightarrow>
      (programify(F) \<in> stable(A) \<and> programify(G) \<in>  stable(A))"
by (simp add: stable_def)

lemma initially_JoinI [intro!]:
     "\<lbrakk>F \<in> initially(A); G \<in> initially(A)\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> initially(A)"
by (unfold initially_def, auto)

lemma invariant_JoinI:
     "\<lbrakk>F \<in> invariant(A); G \<in> invariant(A)\<rbrakk>
      \<Longrightarrow> F \<squnion> G \<in> invariant(A)"
apply (subgoal_tac "F \<in> program\<and>G \<in> program")
prefer 2 apply (blast dest: invariantD2)
apply (simp add: invariant_def)
apply (auto intro: Join_in_program)
done


(* Fails if I=0 because \<Inter>i \<in> 0. A(i) = 0 *)
lemma FP_JOIN: "i \<in> I \<Longrightarrow> FP(\<Squnion>i \<in> I. F(i)) = (\<Inter>i \<in> I. FP (programify(F(i))))"
by (auto simp add: FP_def Inter_def st_set_def JOIN_stable)

subsection\<open>Progress: transient, ensures\<close>

lemma JOIN_transient:
     "i \<in> I \<Longrightarrow>
      (\<Squnion>i \<in> I. F(i)) \<in> transient(A) \<longleftrightarrow> (\<exists>i \<in> I. programify(F(i)) \<in> transient(A))"
apply (auto simp add: transient_def JOIN_def)
  unfolding st_set_def
apply (drule_tac [2] x = act in bspec)
apply (auto dest: Acts_type [THEN subsetD])
done

lemma Join_transient [iff]:
     "F \<squnion> G \<in> transient(A) \<longleftrightarrow>
      (programify(F) \<in> transient(A) | programify(G) \<in> transient(A))"
apply (auto simp add: transient_def Join_def Int_Un_distrib2)
done

lemma Join_transient_I1: "F \<in> transient(A) \<Longrightarrow> F \<squnion> G \<in> transient(A)"
by (simp add: Join_transient transientD2)


lemma Join_transient_I2: "G \<in> transient(A) \<Longrightarrow> F \<squnion> G \<in> transient(A)"
by (simp add: Join_transient transientD2)

(*If I=0 it degenerates to (SKIP \<in> A ensures B) = False, i.e. to \<not>(A\<subseteq>B) *)
lemma JOIN_ensures:
     "i \<in> I \<Longrightarrow>
      (\<Squnion>i \<in> I. F(i)) \<in> A ensures B \<longleftrightarrow>
      ((\<forall>i \<in> I. programify(F(i)) \<in> (A-B) co (A \<union> B)) \<and>
      (\<exists>i \<in> I. programify(F(i)) \<in> A ensures B))"
by (auto simp add: ensures_def JOIN_constrains JOIN_transient)


lemma Join_ensures:
     "F \<squnion> G \<in> A ensures B  \<longleftrightarrow>
      (programify(F) \<in> (A-B) co (A \<union> B) \<and> programify(G) \<in> (A-B) co (A \<union> B) \<and>
       (programify(F) \<in>  transient (A-B) | programify(G) \<in> transient (A-B)))"

  unfolding ensures_def
apply (auto simp add: Join_transient)
done

lemma stable_Join_constrains:
    "\<lbrakk>F \<in> stable(A);  G \<in> A co A'\<rbrakk>
     \<Longrightarrow> F \<squnion> G \<in> A co A'"
  unfolding stable_def constrains_def Join_def st_set_def
apply (cut_tac F = F in Acts_type)
apply (cut_tac F = G in Acts_type, force)
done

(*Premise for G cannot use Always because  F \<in> Stable A  is
   weaker than G \<in> stable A *)
lemma stable_Join_Always1:
     "\<lbrakk>F \<in> stable(A);  G \<in> invariant(A)\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> Always(A)"
apply (subgoal_tac "F \<in> program \<and> G \<in> program \<and> st_set (A) ")
prefer 2 apply (blast dest: invariantD2 stableD2)
apply (simp add: Always_def invariant_def initially_def Stable_eq_stable)
apply (force intro: stable_Int)
done

(*As above, but exchanging the roles of F and G*)
lemma stable_Join_Always2:
     "\<lbrakk>F \<in> invariant(A);  G \<in> stable(A)\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> Always(A)"
apply (subst Join_commute)
apply (blast intro: stable_Join_Always1)
done



lemma stable_Join_ensures1:
     "\<lbrakk>F \<in> stable(A);  G \<in> A ensures B\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> A ensures B"
apply (subgoal_tac "F \<in> program \<and> G \<in> program \<and> st_set (A) ")
prefer 2 apply (blast dest: stableD2 ensures_type [THEN subsetD])
apply (simp (no_asm_simp) add: Join_ensures)
apply (simp add: stable_def ensures_def)
apply (erule constrains_weaken, auto)
done


(*As above, but exchanging the roles of F and G*)
lemma stable_Join_ensures2:
     "\<lbrakk>F \<in> A ensures B;  G \<in> stable(A)\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> A ensures B"
apply (subst Join_commute)
apply (blast intro: stable_Join_ensures1)
done

subsection\<open>The ok and OK relations\<close>

lemma ok_SKIP1 [iff]: "SKIP ok F"
by (auto dest: Acts_type [THEN subsetD] simp add: ok_def)

lemma ok_SKIP2 [iff]: "F ok SKIP"
by (auto dest: Acts_type [THEN subsetD] simp add: ok_def)

lemma ok_Join_commute:
     "(F ok G \<and> (F \<squnion> G) ok H) \<longleftrightarrow> (G ok H \<and> F ok (G \<squnion> H))"
by (auto simp add: ok_def)

lemma ok_commute: "(F ok G) \<longleftrightarrow>(G ok F)"
by (auto simp add: ok_def)

lemmas ok_sym = ok_commute [THEN iffD1]

lemma ok_iff_OK: "OK({\<langle>0,F\<rangle>,\<langle>1,G\<rangle>,\<langle>2,H\<rangle>}, snd) \<longleftrightarrow> (F ok G \<and> (F \<squnion> G) ok H)"
by (simp add: ok_def Join_def OK_def Int_assoc cons_absorb
                 Int_Un_distrib2 Ball_def,  safe, force+)

lemma ok_Join_iff1 [iff]: "F ok (G \<squnion> H) \<longleftrightarrow> (F ok G \<and> F ok H)"
by (auto simp add: ok_def)

lemma ok_Join_iff2 [iff]: "(G \<squnion> H) ok F \<longleftrightarrow> (G ok F \<and> H ok F)"
by (auto simp add: ok_def)

(*useful?  Not with the previous two around*)
lemma ok_Join_commute_I: "\<lbrakk>F ok G; (F \<squnion> G) ok H\<rbrakk> \<Longrightarrow> F ok (G \<squnion> H)"
by (auto simp add: ok_def)

lemma ok_JOIN_iff1 [iff]: "F ok JOIN(I,G) \<longleftrightarrow> (\<forall>i \<in> I. F ok G(i))"
by (force dest: Acts_type [THEN subsetD] elim!: not_emptyE simp add: ok_def)

lemma ok_JOIN_iff2 [iff]: "JOIN(I,G) ok F   \<longleftrightarrow>  (\<forall>i \<in> I. G(i) ok F)"
apply (auto elim!: not_emptyE simp add: ok_def)
apply (blast dest: Acts_type [THEN subsetD])
done

lemma OK_iff_ok: "OK(I,F) \<longleftrightarrow> (\<forall>i \<in> I. \<forall>j \<in> I-{i}. F(i) ok (F(j)))"
by (auto simp add: ok_def OK_def)

lemma OK_imp_ok: "\<lbrakk>OK(I,F); i \<in> I; j \<in> I; i\<noteq>j\<rbrakk> \<Longrightarrow> F(i) ok F(j)"
by (auto simp add: OK_iff_ok)


lemma OK_0 [iff]: "OK(0,F)"
by (simp add: OK_def)

lemma OK_cons_iff:
     "OK(cons(i, I), F) \<longleftrightarrow>
      (i \<in> I \<and> OK(I, F)) | (i\<notin>I \<and> OK(I, F) \<and> F(i) ok JOIN(I,F))"
apply (simp add: OK_iff_ok)
apply (blast intro: ok_sym)
done


subsection\<open>Allowed\<close>

lemma Allowed_SKIP [simp]: "Allowed(SKIP) = program"
by (auto dest: Acts_type [THEN subsetD] simp add: Allowed_def)

lemma Allowed_Join [simp]:
     "Allowed(F \<squnion> G) =
   Allowed(programify(F)) \<inter> Allowed(programify(G))"
apply (auto simp add: Allowed_def)
done

lemma Allowed_JOIN [simp]:
     "i \<in> I \<Longrightarrow>
   Allowed(JOIN(I,F)) = (\<Inter>i \<in> I. Allowed(programify(F(i))))"
apply (auto simp add: Allowed_def, blast)
done

lemma ok_iff_Allowed:
     "F ok G \<longleftrightarrow> (programify(F) \<in> Allowed(programify(G)) \<and>
   programify(G) \<in> Allowed(programify(F)))"
by (simp add: ok_def Allowed_def)


lemma OK_iff_Allowed:
     "OK(I,F) \<longleftrightarrow>
  (\<forall>i \<in> I. \<forall>j \<in> I-{i}. programify(F(i)) \<in> Allowed(programify(F(j))))"
apply (auto simp add: OK_iff_ok ok_iff_Allowed)
done

subsection\<open>safety_prop, for reasoning about given instances of "ok"\<close>

lemma safety_prop_Acts_iff:
     "safety_prop(X) \<Longrightarrow> (Acts(G) \<subseteq> cons(id(state), (\<Union>F \<in> X. Acts(F)))) \<longleftrightarrow> (programify(G) \<in> X)"
apply (simp (no_asm_use) add: safety_prop_def)
apply clarify
apply (case_tac "G \<in> program", simp_all, blast, safe)
prefer 2 apply force
apply (force simp add: programify_def)
done

lemma safety_prop_AllowedActs_iff_Allowed:
     "safety_prop(X) \<Longrightarrow>
  (\<Union>G \<in> X. Acts(G)) \<subseteq> AllowedActs(F) \<longleftrightarrow> (X \<subseteq> Allowed(programify(F)))"
apply (simp add: Allowed_def safety_prop_Acts_iff [THEN iff_sym]
                 safety_prop_def, blast)
done


lemma Allowed_eq:
     "safety_prop(X) \<Longrightarrow> Allowed(mk_program(init, acts, \<Union>F \<in> X. Acts(F))) = X"
apply (subgoal_tac "cons (id (state), \<Union>(RepFun (X, Acts)) \<inter> Pow (state * state)) = \<Union>(RepFun (X, Acts))")
apply (rule_tac [2] equalityI)
  apply (simp del: UN_simps add: Allowed_def safety_prop_Acts_iff safety_prop_def, auto)
apply (force dest: Acts_type [THEN subsetD] simp add: safety_prop_def)+
done

lemma def_prg_Allowed:
     "\<lbrakk>F \<equiv> mk_program (init, acts, \<Union>F \<in> X. Acts(F)); safety_prop(X)\<rbrakk>
      \<Longrightarrow> Allowed(F) = X"
by (simp add: Allowed_eq)

(*For safety_prop to hold, the property must be satisfiable!*)
lemma safety_prop_constrains [iff]:
     "safety_prop(A co B) \<longleftrightarrow> (A \<subseteq> B \<and> st_set(A))"
by (simp add: safety_prop_def constrains_def st_set_def, blast)

(* To be used with resolution *)
lemma safety_prop_constrainsI [iff]:
     "\<lbrakk>A\<subseteq>B; st_set(A)\<rbrakk> \<Longrightarrow>safety_prop(A co B)"
by auto

lemma safety_prop_stable [iff]: "safety_prop(stable(A)) \<longleftrightarrow> st_set(A)"
by (simp add: stable_def)

lemma safety_prop_stableI: "st_set(A) \<Longrightarrow> safety_prop(stable(A))"
by auto

lemma safety_prop_Int [simp]:
     "\<lbrakk>safety_prop(X) ; safety_prop(Y)\<rbrakk> \<Longrightarrow> safety_prop(X \<inter> Y)"
apply (simp add: safety_prop_def, safe, blast)
apply (drule_tac [2] B = "\<Union>(RepFun (X \<inter> Y, Acts))" and C = "\<Union>(RepFun (Y, Acts))" in subset_trans)
apply (drule_tac B = "\<Union>(RepFun (X \<inter> Y, Acts))" and C = "\<Union>(RepFun (X, Acts))" in subset_trans)
apply blast+
done

(* If I=0 the conclusion becomes safety_prop(0) which is false *)
lemma safety_prop_Inter:
  assumes major: "(\<And>i. i \<in> I \<Longrightarrow>safety_prop(X(i)))"
      and minor: "i \<in> I"
  shows "safety_prop(\<Inter>i \<in> I. X(i))"
apply (simp add: safety_prop_def)
apply (cut_tac minor, safe)
apply (simp (no_asm_use) add: Inter_iff)
apply clarify
apply (frule major)
apply (drule_tac [2] i = xa in major)
apply (frule_tac [4] i = xa in major)
apply (auto simp add: safety_prop_def)
apply (drule_tac B = "\<Union>(RepFun (\<Inter>(RepFun (I, X)), Acts))" and C = "\<Union>(RepFun (X (xa), Acts))" in subset_trans)
apply blast+
done

lemma def_UNION_ok_iff:
"\<lbrakk>F \<equiv> mk_program(init,acts, \<Union>G \<in> X. Acts(G)); safety_prop(X)\<rbrakk>
      \<Longrightarrow> F ok G \<longleftrightarrow> (programify(G) \<in> X \<and> acts \<inter> Pow(state*state) \<subseteq> AllowedActs(G))"
  unfolding ok_def
apply (drule_tac G = G in safety_prop_Acts_iff)
apply (cut_tac F = G in AllowedActs_type)
apply (cut_tac F = G in Acts_type, auto)
done

end
