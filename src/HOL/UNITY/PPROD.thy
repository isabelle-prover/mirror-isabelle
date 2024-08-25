(*  Title:      HOL/UNITY/PPROD.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Abstraction over replicated components (PLam)
General products of programs (Pi operation)

Some dead wood here!
*)

theory PPROD imports Lift_prog begin

definition PLam :: "[nat set, nat => ('b * ((nat=>'b) * 'c)) program]
            => ((nat=>'b) * 'c) program" where
    "PLam I F == \<Squnion>i \<in> I. lift i (F i)"

syntax
  "_PLam" :: "[pttrn, nat set, 'b set] => (nat => 'b) set"  ("(3plam _:_./ _)" 10)
syntax_consts
  "_PLam" == PLam
translations
  "plam x : A. B" == "CONST PLam A (%x. B)"


(*** Basic properties ***)

lemma Init_PLam [simp]: "Init (PLam I F) = (\<Inter>i \<in> I. lift_set i (Init (F i)))"
by (simp add: PLam_def lift_def lift_set_def)

lemma PLam_empty [simp]: "PLam {} F = SKIP"
by (simp add: PLam_def)

lemma PLam_SKIP [simp]: "(plam i : I. SKIP) = SKIP"
by (simp add: PLam_def JN_constant)

lemma PLam_insert: "PLam (insert i I) F = (lift i (F i)) \<squnion> (PLam I F)"
by (unfold PLam_def, auto)

lemma PLam_component_iff: "((PLam I F) \<le> H) = (\<forall>i \<in> I. lift i (F i) \<le> H)"
by (simp add: PLam_def JN_component_iff)

lemma component_PLam: "i \<in> I ==> lift i (F i) \<le> (PLam I F)"
apply (unfold PLam_def)
(*blast_tac doesn't use HO unification*)
apply (fast intro: component_JN)
done


(** Safety & Progress: but are they used anywhere? **)

lemma PLam_constrains:
     "[| i \<in> I;  \<forall>j. F j \<in> preserves snd |]
      ==> (PLam I F \<in> (lift_set i (A \<times> UNIV)) co
                      (lift_set i (B \<times> UNIV)))  =
          (F i \<in> (A \<times> UNIV) co (B \<times> UNIV))"
apply (simp add: PLam_def JN_constrains)
apply (subst insert_Diff [symmetric], assumption)
apply (simp add: lift_constrains)
apply (blast intro: constrains_imp_lift_constrains)
done

lemma PLam_stable:
     "[| i \<in> I;  \<forall>j. F j \<in> preserves snd |]
      ==> (PLam I F \<in> stable (lift_set i (A \<times> UNIV))) =
          (F i \<in> stable (A \<times> UNIV))"
by (simp add: stable_def PLam_constrains)

lemma PLam_transient:
     "i \<in> I ==>
    PLam I F \<in> transient A = (\<exists>i \<in> I. lift i (F i) \<in> transient A)"
by (simp add: JN_transient PLam_def)

text\<open>This holds because the \<^term>\<open>F j\<close> cannot change \<^term>\<open>lift_set i\<close>\<close>
lemma PLam_ensures:
     "[| i \<in> I;  F i \<in> (A \<times> UNIV) ensures (B \<times> UNIV);
         \<forall>j. F j \<in> preserves snd |]
      ==> PLam I F \<in> lift_set i (A \<times> UNIV) ensures lift_set i (B \<times> UNIV)"
apply (simp add: ensures_def PLam_constrains PLam_transient
              lift_set_Un_distrib [symmetric] lift_set_Diff_distrib [symmetric]
              Times_Un_distrib1 [symmetric] Times_Diff_distrib1 [symmetric])
apply (rule rev_bexI, assumption)
apply (simp add: lift_transient)
done

lemma PLam_leadsTo_Basis:
     "[| i \<in> I;
         F i \<in> ((A \<times> UNIV) - (B \<times> UNIV)) co
               ((A \<times> UNIV) \<union> (B \<times> UNIV));
         F i \<in> transient ((A \<times> UNIV) - (B \<times> UNIV));
         \<forall>j. F j \<in> preserves snd |]
      ==> PLam I F \<in> lift_set i (A \<times> UNIV) leadsTo lift_set i (B \<times> UNIV)"
by (rule PLam_ensures [THEN leadsTo_Basis], rule_tac [2] ensuresI)



(** invariant **)

lemma invariant_imp_PLam_invariant:
     "[| F i \<in> invariant (A \<times> UNIV);  i \<in> I;
         \<forall>j. F j \<in> preserves snd |]
      ==> PLam I F \<in> invariant (lift_set i (A \<times> UNIV))"
by (auto simp add: PLam_stable invariant_def)


lemma PLam_preserves_fst [simp]:
     "\<forall>j. F j \<in> preserves snd
      ==> (PLam I F \<in> preserves (v o sub j o fst)) =
          (if j \<in> I then F j \<in> preserves (v o fst) else True)"
by (simp add: PLam_def lift_preserves_sub)

lemma PLam_preserves_snd [simp,intro]:
     "\<forall>j. F j \<in> preserves snd ==> PLam I F \<in> preserves snd"
by (simp add: PLam_def lift_preserves_snd_I)



(*** guarantees properties ***)

text\<open>This rule looks unsatisfactory because it refers to \<^term>\<open>lift\<close>. 
  One must use
  \<open>lift_guarantees_eq_lift_inv\<close> to rewrite the first subgoal and
  something like \<open>lift_preserves_sub\<close> to rewrite the third.  However
  there's no obvious alternative for the third premise.\<close>
lemma guarantees_PLam_I:
    "[| lift i (F i) \<in> X guarantees Y;  i \<in> I;
        OK I (\<lambda>i. lift i (F i)) |]
     ==> (PLam I F) \<in> X guarantees Y"
apply (unfold PLam_def)
apply (simp add: guarantees_JN_I)
done

lemma Allowed_PLam [simp]:
     "Allowed (PLam I F) = (\<Inter>i \<in> I. lift i ` Allowed(F i))"
by (simp add: PLam_def)


lemma PLam_preserves [simp]:
     "(PLam I F) \<in> preserves v = (\<forall>i \<in> I. F i \<in> preserves (v o lift_map i))"
by (simp add: PLam_def lift_def rename_preserves)


(**UNUSED
    (*The f0 premise ensures that the product is well-defined.*)
    lemma PLam_invariant_imp_invariant:
     "[| PLam I F \<in> invariant (lift_set i A);  i \<in> I;
             f0: Init (PLam I F) |] ==> F i \<in> invariant A"
    apply (auto simp add: invariant_def)
    apply (drule_tac c = "f0 (i:=x) " in subsetD)
    apply auto
    done

    lemma PLam_invariant:
     "[| i \<in> I;  f0: Init (PLam I F) |]
          ==> (PLam I F \<in> invariant (lift_set i A)) = (F i \<in> invariant A)"
    apply (blast intro: invariant_imp_PLam_invariant PLam_invariant_imp_invariant)
    done

    (*The f0 premise isn't needed if F is a constant program because then
      we get an initial state by replicating that of F*)
    lemma reachable_PLam:
     "i \<in> I
          ==> ((plam x \<in> I. F) \<in> invariant (lift_set i A)) = (F \<in> invariant A)"
    apply (auto simp add: invariant_def)
    done
**)


(**UNUSED
    (** Reachability **)

    Goal "[| f \<in> reachable (PLam I F);  i \<in> I |] ==> f i \<in> reachable (F i)"
    apply (erule reachable.induct)
    apply (auto intro: reachable.intrs)
    done

    (*Result to justify a re-organization of this file*)
    lemma "{f. \<forall>i \<in> I. f i \<in> R i} = (\<Inter>i \<in> I. lift_set i (R i))"
    by auto

    lemma reachable_PLam_subset1:
     "reachable (PLam I F) \<subseteq> (\<Inter>i \<in> I. lift_set i (reachable (F i)))"
    apply (force dest!: reachable_PLam)
    done

    (*simplify using reachable_lift??*)
    lemma reachable_lift_Join_PLam [rule_format]:
      "[| i \<notin> I;  A \<in> reachable (F i) |]
       ==> \<forall>f. f \<in> reachable (PLam I F)
                  --> f(i:=A) \<in> reachable (lift i (F i) \<squnion> PLam I F)"
    apply (erule reachable.induct)
    apply (ALLGOALS Clarify_tac)
    apply (erule reachable.induct)
    (*Init, Init case*)
    apply (force intro: reachable.intrs)
    (*Init of F, action of PLam F case*)
    apply (rule_tac act = act in reachable.Acts)
    apply force
    apply assumption
    apply (force intro: ext)
    (*induction over the 2nd "reachable" assumption*)
    apply (erule_tac xa = f in reachable.induct)
    (*Init of PLam F, action of F case*)
    apply (rule_tac act = "lift_act i act" in reachable.Acts)
    apply force
    apply (force intro: reachable.Init)
    apply (force intro: ext simp add: lift_act_def)
    (*last case: an action of PLam I F*)
    apply (rule_tac act = acta in reachable.Acts)
    apply force
    apply assumption
    apply (force intro: ext)
    done


    (*The index set must be finite: otherwise infinitely many copies of F can
      perform actions, and PLam can never catch up in finite time.*)
    lemma reachable_PLam_subset2:
     "finite I
          ==> (\<Inter>i \<in> I. lift_set i (reachable (F i))) \<subseteq> reachable (PLam I F)"
    apply (erule finite_induct)
    apply (simp (no_asm))
    apply (force dest: reachable_lift_Join_PLam simp add: PLam_insert)
    done

    lemma reachable_PLam_eq:
     "finite I ==>
          reachable (PLam I F) = (\<Inter>i \<in> I. lift_set i (reachable (F i)))"
    apply (REPEAT_FIRST (ares_tac [equalityI, reachable_PLam_subset1, reachable_PLam_subset2]))
    done


    (** Co **)

    lemma Constrains_imp_PLam_Constrains:
     "[| F i \<in> A Co B;  i \<in> I;  finite I |]
          ==> PLam I F \<in> (lift_set i A) Co (lift_set i B)"
    apply (auto simp add: Constrains_def Collect_conj_eq [symmetric] reachable_PLam_eq)
    apply (auto simp add: constrains_def PLam_def)
    apply (REPEAT (blast intro: reachable.intrs))
    done



    lemma PLam_Constrains:
     "[| i \<in> I;  finite I;  f0: Init (PLam I F) |]
          ==> (PLam I F \<in> (lift_set i A) Co (lift_set i B)) =
              (F i \<in> A Co B)"
    apply (blast intro: Constrains_imp_PLam_Constrains PLam_Constrains_imp_Constrains)
    done

    lemma PLam_Stable:
     "[| i \<in> I;  finite I;  f0: Init (PLam I F) |]
          ==> (PLam I F \<in> Stable (lift_set i A)) = (F i \<in> Stable A)"
    apply (simp del: Init_PLam add: Stable_def PLam_Constrains)
    done


    (** const_PLam (no dependence on i) doesn't require the f0 premise **)

    lemma const_PLam_Constrains:
     "[| i \<in> I;  finite I |]
          ==> ((plam x \<in> I. F) \<in> (lift_set i A) Co (lift_set i B)) =
              (F \<in> A Co B)"
    apply (blast intro: Constrains_imp_PLam_Constrains const_PLam_Constrains_imp_Constrains)
    done

    lemma const_PLam_Stable:
     "[| i \<in> I;  finite I |]
          ==> ((plam x \<in> I. F) \<in> Stable (lift_set i A)) = (F \<in> Stable A)"
    apply (simp add: Stable_def const_PLam_Constrains)
    done

    lemma const_PLam_Increasing:
         "[| i \<in> I;  finite I |]
          ==> ((plam x \<in> I. F) \<in> Increasing (f o sub i)) = (F \<in> Increasing f)"
    apply (unfold Increasing_def)
    apply (subgoal_tac "\<forall>z. {s. z \<subseteq> (f o sub i) s} = lift_set i {s. z \<subseteq> f s}")
    apply (asm_simp_tac (simpset () add: lift_set_sub) 2)
    apply (simp add: finite_lessThan const_PLam_Stable)
    done
**)


end
