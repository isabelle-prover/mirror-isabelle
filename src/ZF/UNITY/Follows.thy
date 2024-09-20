(*  Title:      ZF/UNITY/Follows.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Theory ported from HOL.
*)

section\<open>The "Follows" relation of Charpentier and Sivilotte\<close>

theory Follows imports SubstAx Increasing begin

definition
  Follows :: "[i, i, i\<Rightarrow>i, i\<Rightarrow>i] \<Rightarrow> i"  where
  "Follows(A, r, f, g) \<equiv>
            Increasing(A, r, g) Int
            Increasing(A, r,f) Int
            Always({s \<in> state. <f(s), g(s)>:r}) Int
           (\<Inter>k \<in> A. {s \<in> state. <k, g(s)>:r} \<longmapsto>w {s \<in> state. <k,f(s)>:r})"

abbreviation
  Incr :: "[i\<Rightarrow>i]\<Rightarrow>i" where
  "Incr(f) \<equiv> Increasing(list(nat), prefix(nat), f)"

abbreviation
  n_Incr :: "[i\<Rightarrow>i]\<Rightarrow>i" where
  "n_Incr(f) \<equiv> Increasing(nat, Le, f)"

abbreviation
  s_Incr :: "[i\<Rightarrow>i]\<Rightarrow>i" where
  "s_Incr(f) \<equiv> Increasing(Pow(nat), SetLe(nat), f)"

abbreviation
  m_Incr :: "[i\<Rightarrow>i]\<Rightarrow>i" where
  "m_Incr(f) \<equiv> Increasing(Mult(nat), MultLe(nat, Le), f)"

abbreviation
  n_Fols :: "[i\<Rightarrow>i, i\<Rightarrow>i]\<Rightarrow>i"   (infixl \<open>n'_Fols\<close> 65)  where
  "f n_Fols g \<equiv> Follows(nat, Le, f, g)"

abbreviation
  Follows' :: "[i\<Rightarrow>i, i\<Rightarrow>i, i, i] \<Rightarrow> i"
        (\<open>(\<open>notation=\<open>mixfix Fols Wrt\<close>\<close>_ /Fols _ /Wrt (_ /'/ _))\<close> [60, 0, 0, 60] 60)  where
  "f Fols g Wrt r/A \<equiv> Follows(A,r,f,g)"


(*Does this hold for "invariant"?*)

lemma Follows_cong:
     "\<lbrakk>A=A'; r=r'; \<And>x. x \<in> state \<Longrightarrow> f(x)=f'(x); \<And>x. x \<in> state \<Longrightarrow> g(x)=g'(x)\<rbrakk> \<Longrightarrow> Follows(A, r, f, g) = Follows(A', r', f', g')"
by (simp add: Increasing_def Follows_def)


lemma subset_Always_comp:
"\<lbrakk>mono1(A, r, B, s, h); \<forall>x \<in> state. f(x):A \<and> g(x):A\<rbrakk> \<Longrightarrow>
   Always({x \<in> state. <f(x), g(x)> \<in> r})<=Always({x \<in> state. <(h comp f)(x), (h comp g)(x)> \<in> s})"
  unfolding mono1_def metacomp_def
apply (auto simp add: Always_eq_includes_reachable)
done

lemma imp_Always_comp:
"\<lbrakk>F \<in> Always({x \<in> state. <f(x), g(x)> \<in> r});
    mono1(A, r, B, s, h); \<forall>x \<in> state. f(x):A \<and> g(x):A\<rbrakk> \<Longrightarrow>
    F \<in> Always({x \<in> state. <(h comp f)(x), (h comp g)(x)> \<in> s})"
by (blast intro: subset_Always_comp [THEN subsetD])


lemma imp_Always_comp2:
"\<lbrakk>F \<in> Always({x \<in> state. <f1(x), f(x)> \<in> r});
    F \<in> Always({x \<in> state. <g1(x), g(x)> \<in> s});
    mono2(A, r, B, s, C, t, h);
    \<forall>x \<in> state. f1(x):A \<and> f(x):A \<and> g1(x):B \<and> g(x):B\<rbrakk>
  \<Longrightarrow> F \<in> Always({x \<in> state. <h(f1(x), g1(x)), h(f(x), g(x))> \<in> t})"
apply (auto simp add: Always_eq_includes_reachable mono2_def)
apply (auto dest!: subsetD)
done

(* comp LeadsTo *)

lemma subset_LeadsTo_comp:
"\<lbrakk>mono1(A, r, B, s, h); refl(A,r); trans[B](s);
        \<forall>x \<in> state. f(x):A \<and> g(x):A\<rbrakk> \<Longrightarrow>
  (\<Inter>j \<in> A. {s \<in> state. <j, g(s)> \<in> r} \<longmapsto>w {s \<in> state. <j,f(s)> \<in> r}) <=
 (\<Inter>k \<in> B. {x \<in> state. <k, (h comp g)(x)> \<in> s} \<longmapsto>w {x \<in> state. <k, (h comp f)(x)> \<in> s})"

apply (unfold mono1_def metacomp_def, clarify)
apply (simp_all (no_asm_use) add: INT_iff)
apply auto
apply (rule single_LeadsTo_I)
prefer 2 apply (blast dest: LeadsTo_type [THEN subsetD], auto)
apply (rotate_tac 5)
apply (drule_tac x = "g (sa) " in bspec)
apply (erule_tac [2] LeadsTo_weaken)
apply (auto simp add: part_order_def refl_def)
apply (rule_tac b = "h (g (sa))" in trans_onD)
apply blast
apply auto
done

lemma imp_LeadsTo_comp:
"\<lbrakk>F:(\<Inter>j \<in> A. {s \<in> state. <j, g(s)> \<in> r} \<longmapsto>w {s \<in> state. <j,f(s)> \<in> r});
    mono1(A, r, B, s, h); refl(A,r); trans[B](s);
    \<forall>x \<in> state. f(x):A \<and> g(x):A\<rbrakk> \<Longrightarrow>
   F:(\<Inter>k \<in> B. {x \<in> state. <k, (h comp g)(x)> \<in> s} \<longmapsto>w {x \<in> state. <k, (h comp f)(x)> \<in> s})"
apply (rule subset_LeadsTo_comp [THEN subsetD], auto)
done

lemma imp_LeadsTo_comp_right:
"\<lbrakk>F \<in> Increasing(B, s, g);
  \<forall>j \<in> A. F: {s \<in> state. <j, f(s)> \<in> r} \<longmapsto>w {s \<in> state. <j,f1(s)> \<in> r};
  mono2(A, r, B, s, C, t, h); refl(A, r); refl(B, s); trans[C](t);
  \<forall>x \<in> state. f1(x):A \<and> f(x):A \<and> g(x):B; k \<in> C\<rbrakk> \<Longrightarrow>
  F:{x \<in> state. <k, h(f(x), g(x))> \<in> t} \<longmapsto>w {x \<in> state. <k, h(f1(x), g(x))> \<in> t}"
  unfolding mono2_def Increasing_def
apply (rule single_LeadsTo_I, auto)
apply (drule_tac x = "g (sa) " and A = B in bspec)
apply auto
apply (drule_tac x = "f (sa) " and P = "\<lambda>j. F \<in> X(j) \<longmapsto>w Y(j)" for X Y in bspec)
apply auto
apply (rule PSP_Stable [THEN LeadsTo_weaken], blast, blast)
apply auto
apply (force simp add: part_order_def refl_def)
apply (force simp add: part_order_def refl_def)
apply (drule_tac x = "f1 (x)" and x1 = "f (sa) " and P2 = "\<lambda>x y. \<forall>u\<in>B. P (x,y,u)" for P in bspec [THEN bspec])
apply (drule_tac [3] x = "g (x) " and x1 = "g (sa) " and P2 = "\<lambda>x y. P (x,y) \<longrightarrow> d (x,y) \<in> t" for P d in bspec [THEN bspec])
apply auto
apply (rule_tac b = "h (f (sa), g (sa))" and A = C in trans_onD)
apply (auto simp add: part_order_def)
done

lemma imp_LeadsTo_comp_left:
"\<lbrakk>F \<in> Increasing(A, r, f);
  \<forall>j \<in> B. F: {x \<in> state. <j, g(x)> \<in> s} \<longmapsto>w {x \<in> state. <j,g1(x)> \<in> s};
  mono2(A, r, B, s, C, t, h); refl(A,r); refl(B, s); trans[C](t);
  \<forall>x \<in> state. f(x):A \<and> g1(x):B \<and> g(x):B; k \<in> C\<rbrakk> \<Longrightarrow>
  F:{x \<in> state. <k, h(f(x), g(x))> \<in> t} \<longmapsto>w {x \<in> state. <k, h(f(x), g1(x))> \<in> t}"
  unfolding mono2_def Increasing_def
apply (rule single_LeadsTo_I, auto)
apply (drule_tac x = "f (sa) " and P = "\<lambda>k. F \<in> Stable (X (k))" for X in bspec)
apply auto
apply (drule_tac x = "g (sa) " in bspec)
apply auto
apply (rule PSP_Stable [THEN LeadsTo_weaken], blast, blast)
apply auto
apply (force simp add: part_order_def refl_def)
apply (force simp add: part_order_def refl_def)
apply (drule_tac x = "f (x) " and x1 = "f (sa) " in bspec [THEN bspec])
apply (drule_tac [3] x = "g1 (x) " and x1 = "g (sa) " and P2 = "\<lambda>x y. P (x,y) \<longrightarrow> d (x,y) \<in> t" for P d in bspec [THEN bspec])
apply auto
apply (rule_tac b = "h (f (sa), g (sa))" and A = C in trans_onD)
apply (auto simp add: part_order_def)
done

(**  This general result is used to prove Follows Un, munion, etc. **)
lemma imp_LeadsTo_comp2:
"\<lbrakk>F \<in> Increasing(A, r, f1) \<inter>  Increasing(B, s, g);
  \<forall>j \<in> A. F: {s \<in> state. <j, f(s)> \<in> r} \<longmapsto>w {s \<in> state. <j,f1(s)> \<in> r};
  \<forall>j \<in> B. F: {x \<in> state. <j, g(x)> \<in> s} \<longmapsto>w {x \<in> state. <j,g1(x)> \<in> s};
  mono2(A, r, B, s, C, t, h); refl(A,r); refl(B, s); trans[C](t);
  \<forall>x \<in> state. f(x):A \<and> g1(x):B \<and> f1(x):A \<and>g(x):B; k \<in> C\<rbrakk>
  \<Longrightarrow> F:{x \<in> state. <k, h(f(x), g(x))> \<in> t} \<longmapsto>w {x \<in> state. <k, h(f1(x), g1(x))> \<in> t}"
apply (rule_tac B = "{x \<in> state. <k, h (f1 (x), g (x))> \<in> t}" in LeadsTo_Trans)
apply (blast intro: imp_LeadsTo_comp_right)
apply (blast intro: imp_LeadsTo_comp_left)
done

(* Follows type *)
lemma Follows_type: "Follows(A, r, f, g)<=program"
  unfolding Follows_def
apply (blast dest: Increasing_type [THEN subsetD])
done

lemma Follows_into_program [TC]: "F \<in> Follows(A, r, f, g) \<Longrightarrow> F \<in> program"
by (blast dest: Follows_type [THEN subsetD])

lemma FollowsD:
"F \<in> Follows(A, r, f, g)\<Longrightarrow>
  F \<in> program \<and> (\<exists>a. a \<in> A) \<and> (\<forall>x \<in> state. f(x):A \<and> g(x):A)"
  unfolding Follows_def
apply (blast dest: IncreasingD)
done

lemma Follows_constantI:
 "\<lbrakk>F \<in> program; c \<in> A; refl(A, r)\<rbrakk> \<Longrightarrow> F \<in> Follows(A, r, \<lambda>x. c, \<lambda>x. c)"
apply (unfold Follows_def, auto)
apply (auto simp add: refl_def)
done

lemma subset_Follows_comp:
"\<lbrakk>mono1(A, r, B, s, h); refl(A, r); trans[B](s)\<rbrakk>
   \<Longrightarrow> Follows(A, r, f, g) \<subseteq> Follows(B, s,  h comp f, h comp g)"
apply (unfold Follows_def, clarify)
apply (frule_tac f = g in IncreasingD)
apply (frule_tac f = f in IncreasingD)
apply (rule IntI)
apply (rule_tac [2] h = h in imp_LeadsTo_comp)
prefer 5 apply assumption
apply (auto intro: imp_Increasing_comp imp_Always_comp simp del: INT_simps)
done

lemma imp_Follows_comp:
"\<lbrakk>F \<in> Follows(A, r, f, g);  mono1(A, r, B, s, h); refl(A, r); trans[B](s)\<rbrakk>
  \<Longrightarrow>  F \<in> Follows(B, s,  h comp f, h comp g)"
apply (blast intro: subset_Follows_comp [THEN subsetD])
done

(* 2-place monotone operation \<in> this general result is used to prove Follows_Un, Follows_munion *)

(* 2-place monotone operation \<in> this general result is
   used to prove Follows_Un, Follows_munion *)
lemma imp_Follows_comp2:
"\<lbrakk>F \<in> Follows(A, r, f1, f);  F \<in> Follows(B, s, g1, g);
   mono2(A, r, B, s, C, t, h); refl(A,r); refl(B, s); trans[C](t)\<rbrakk>
   \<Longrightarrow> F \<in> Follows(C, t, \<lambda>x. h(f1(x), g1(x)), \<lambda>x. h(f(x), g(x)))"
apply (unfold Follows_def, clarify)
apply (frule_tac f = g in IncreasingD)
apply (frule_tac f = f in IncreasingD)
apply (rule IntI, safe)
apply (rule_tac [3] h = h in imp_Always_comp2)
prefer 5 apply assumption
apply (rule_tac [2] h = h in imp_Increasing_comp2)
prefer 4 apply assumption
apply (rule_tac h = h in imp_Increasing_comp2)
prefer 3 apply assumption
apply simp_all
apply (blast dest!: IncreasingD)
apply (rule_tac h = h in imp_LeadsTo_comp2)
prefer 4 apply assumption
apply auto
  prefer 3 apply (simp add: mono2_def)
apply (blast dest: IncreasingD)+
done


lemma Follows_trans:
     "\<lbrakk>F \<in> Follows(A, r, f, g);  F \<in> Follows(A,r, g, h);
         trans[A](r)\<rbrakk> \<Longrightarrow> F \<in> Follows(A, r, f, h)"
apply (frule_tac f = f in FollowsD)
apply (frule_tac f = g in FollowsD)
apply (simp add: Follows_def)
apply (simp add: Always_eq_includes_reachable INT_iff, auto)
apply (rule_tac [2] B = "{s \<in> state. <k, g (s) > \<in> r}" in LeadsTo_Trans)
apply (rule_tac b = "g (x) " in trans_onD)
apply blast+
done

(** Destruction rules for Follows **)

lemma Follows_imp_Increasing_left:
     "F \<in> Follows(A, r, f,g) \<Longrightarrow> F \<in> Increasing(A, r, f)"
by (unfold Follows_def, blast)

lemma Follows_imp_Increasing_right:
     "F \<in> Follows(A, r, f,g) \<Longrightarrow> F \<in> Increasing(A, r, g)"
by (unfold Follows_def, blast)

lemma Follows_imp_Always:
 "F :Follows(A, r, f, g) \<Longrightarrow> F \<in> Always({s \<in> state. <f(s),g(s)> \<in> r})"
by (unfold Follows_def, blast)

lemma Follows_imp_LeadsTo:
 "\<lbrakk>F \<in> Follows(A, r, f, g); k \<in> A\<rbrakk>  \<Longrightarrow>
  F: {s \<in> state. <k,g(s)> \<in> r } \<longmapsto>w {s \<in> state. <k,f(s)> \<in> r}"
by (unfold Follows_def, blast)

lemma Follows_LeadsTo_pfixLe:
     "\<lbrakk>F \<in> Follows(list(nat), gen_prefix(nat, Le), f, g); k \<in> list(nat)\<rbrakk>
   \<Longrightarrow> F \<in> {s \<in> state. k pfixLe g(s)} \<longmapsto>w {s \<in> state. k pfixLe f(s)}"
by (blast intro: Follows_imp_LeadsTo)

lemma Follows_LeadsTo_pfixGe:
     "\<lbrakk>F \<in> Follows(list(nat), gen_prefix(nat, Ge), f, g); k \<in> list(nat)\<rbrakk>
   \<Longrightarrow> F \<in> {s \<in> state. k pfixGe g(s)} \<longmapsto>w {s \<in> state. k pfixGe f(s)}"
by (blast intro: Follows_imp_LeadsTo)

lemma Always_Follows1:
"\<lbrakk>F \<in> Always({s \<in> state. f(s) = g(s)}); F \<in> Follows(A, r, f, h);
    \<forall>x \<in> state. g(x):A\<rbrakk> \<Longrightarrow> F \<in> Follows(A, r, g, h)"
  unfolding Follows_def Increasing_def Stable_def
apply (simp add: INT_iff, auto)
apply (rule_tac [3] C = "{s \<in> state. f(s)=g(s)}"
        and A = "{s \<in> state. <k, h (s)> \<in> r}"
        and A' = "{s \<in> state. <k, f(s)> \<in> r}" in Always_LeadsTo_weaken)
apply (erule_tac A = "{s \<in> state. <k,f(s) > \<in> r}"
           and A' = "{s \<in> state. <k,f(s) > \<in> r}" in Always_Constrains_weaken)
apply auto
apply (drule Always_Int_I, assumption)
apply (erule_tac A = "{s \<in> state. f(s)=g(s)} \<inter> {s \<in> state. <f(s), h(s)> \<in> r}"
       in Always_weaken)
apply auto
done


lemma Always_Follows2:
"\<lbrakk>F \<in> Always({s \<in> state. g(s) = h(s)});
  F \<in> Follows(A, r, f, g); \<forall>x \<in> state. h(x):A\<rbrakk> \<Longrightarrow> F \<in> Follows(A, r, f, h)"
  unfolding Follows_def Increasing_def Stable_def
apply (simp add: INT_iff, auto)
apply (rule_tac [3] C = "{s \<in> state. g (s) =h (s) }"
            and A = "{s \<in> state. <k, g (s) > \<in> r}"
            and A' = "{s \<in> state. <k, f (s) > \<in> r}" in Always_LeadsTo_weaken)
apply (erule_tac A = "{s \<in> state. <k, g(s)> \<in> r}"
         and A' = "{s \<in> state. <k, g(s)> \<in> r}" in Always_Constrains_weaken)
apply auto
apply (drule Always_Int_I, assumption)
apply (erule_tac A = "{s \<in> state. g(s)=h(s)} \<inter> {s \<in> state. <f(s), g(s)> \<in> r}"
       in Always_weaken)
apply auto
done

(** Union properties (with the subset ordering) **)

lemma refl_SetLe [simp]: "refl(Pow(A), SetLe(A))"
by (unfold refl_def SetLe_def, auto)

lemma trans_on_SetLe [simp]: "trans[Pow(A)](SetLe(A))"
by (unfold trans_on_def SetLe_def, auto)

lemma antisym_SetLe [simp]: "antisym(SetLe(A))"
by (unfold antisym_def SetLe_def, auto)

lemma part_order_SetLe [simp]: "part_order(Pow(A), SetLe(A))"
by (unfold part_order_def, auto)

lemma increasing_Un:
     "\<lbrakk>F \<in> Increasing.increasing(Pow(A), SetLe(A), f);
         F \<in> Increasing.increasing(Pow(A), SetLe(A), g)\<rbrakk>
     \<Longrightarrow> F \<in> Increasing.increasing(Pow(A), SetLe(A), \<lambda>x. f(x) \<union> g(x))"
by (rule_tac h = "(Un)" in imp_increasing_comp2, auto)

lemma Increasing_Un:
     "\<lbrakk>F \<in> Increasing(Pow(A), SetLe(A), f);
         F \<in> Increasing(Pow(A), SetLe(A), g)\<rbrakk>
     \<Longrightarrow> F \<in> Increasing(Pow(A), SetLe(A), \<lambda>x. f(x) \<union> g(x))"
by (rule_tac h = "(Un)" in imp_Increasing_comp2, auto)

lemma Always_Un:
     "\<lbrakk>F \<in> Always({s \<in> state. f1(s) \<subseteq> f(s)});
     F \<in> Always({s \<in> state. g1(s) \<subseteq> g(s)})\<rbrakk>
      \<Longrightarrow> F \<in> Always({s \<in> state. f1(s) \<union> g1(s) \<subseteq> f(s) \<union> g(s)})"
by (simp add: Always_eq_includes_reachable, blast)

lemma Follows_Un:
"\<lbrakk>F \<in> Follows(Pow(A), SetLe(A), f1, f);
     F \<in> Follows(Pow(A), SetLe(A), g1, g)\<rbrakk>
     \<Longrightarrow> F \<in> Follows(Pow(A), SetLe(A), \<lambda>s. f1(s) \<union> g1(s), \<lambda>s. f(s) \<union> g(s))"
by (rule_tac h = "(Un)" in imp_Follows_comp2, auto)

(** Multiset union properties (with the MultLe ordering) **)

lemma refl_MultLe [simp]: "refl(Mult(A), MultLe(A,r))"
by (unfold MultLe_def refl_def, auto)

lemma MultLe_refl1 [simp]:
 "\<lbrakk>multiset(M); mset_of(M)<=A\<rbrakk> \<Longrightarrow> \<langle>M, M\<rangle> \<in> MultLe(A, r)"
  unfolding MultLe_def id_def lam_def
apply (auto simp add: Mult_iff_multiset)
done

lemma MultLe_refl2 [simp]: "M \<in> Mult(A) \<Longrightarrow> \<langle>M, M\<rangle> \<in> MultLe(A, r)"
by (unfold MultLe_def id_def lam_def, auto)


lemma trans_on_MultLe [simp]: "trans[Mult(A)](MultLe(A,r))"
  unfolding MultLe_def trans_on_def
apply (auto intro: trancl_trans simp add: multirel_def)
done

lemma MultLe_type: "MultLe(A, r)<= (Mult(A) * Mult(A))"
apply (unfold MultLe_def, auto)
apply (drule multirel_type [THEN subsetD], auto)
done

lemma MultLe_trans:
     "\<lbrakk>\<langle>M,K\<rangle> \<in> MultLe(A,r); \<langle>K,N\<rangle> \<in> MultLe(A,r)\<rbrakk> \<Longrightarrow> \<langle>M,N\<rangle> \<in> MultLe(A,r)"
apply (cut_tac A=A in trans_on_MultLe)
apply (drule trans_onD, assumption)
apply (auto dest: MultLe_type [THEN subsetD])
done

lemma part_order_imp_part_ord:
     "part_order(A, r) \<Longrightarrow> part_ord(A, r-id(A))"
  unfolding part_order_def part_ord_def
apply (simp add: refl_def id_def lam_def irrefl_def, auto)
apply (simp (no_asm) add: trans_on_def)
apply auto
apply (blast dest: trans_onD)
apply (simp (no_asm_use) add: antisym_def)
apply auto
done

lemma antisym_MultLe [simp]:
  "part_order(A, r) \<Longrightarrow> antisym(MultLe(A,r))"
  unfolding MultLe_def antisym_def
apply (drule part_order_imp_part_ord, auto)
apply (drule irrefl_on_multirel)
apply (frule multirel_type [THEN subsetD])
apply (drule multirel_trans)
apply (auto simp add: irrefl_def)
done

lemma part_order_MultLe [simp]:
     "part_order(A, r) \<Longrightarrow>  part_order(Mult(A), MultLe(A, r))"
apply (frule antisym_MultLe)
apply (auto simp add: part_order_def)
done

lemma empty_le_MultLe [simp]:
"\<lbrakk>multiset(M); mset_of(M)<= A\<rbrakk> \<Longrightarrow> \<langle>0, M\<rangle> \<in> MultLe(A, r)"
  unfolding MultLe_def
apply (case_tac "M=0")
apply (auto simp add: FiniteFun.intros)
apply (subgoal_tac "<0 +# 0, 0 +# M> \<in> multirel (A, r - id (A))")
apply (rule_tac [2] one_step_implies_multirel)
apply (auto simp add: Mult_iff_multiset)
done

lemma empty_le_MultLe2 [simp]: "M \<in> Mult(A) \<Longrightarrow> \<langle>0, M\<rangle> \<in> MultLe(A, r)"
by (simp add: Mult_iff_multiset)

lemma munion_mono:
"\<lbrakk>\<langle>M, N\<rangle> \<in> MultLe(A, r); \<langle>K, L\<rangle> \<in> MultLe(A, r)\<rbrakk> \<Longrightarrow>
  <M +# K, N +# L> \<in> MultLe(A, r)"
  unfolding MultLe_def
apply (auto intro: munion_multirel_mono1 munion_multirel_mono2
       munion_multirel_mono multiset_into_Mult simp add: Mult_iff_multiset)
done

lemma increasing_munion:
     "\<lbrakk>F \<in> Increasing.increasing(Mult(A), MultLe(A,r), f);
         F \<in> Increasing.increasing(Mult(A), MultLe(A,r), g)\<rbrakk>
     \<Longrightarrow> F \<in> Increasing.increasing(Mult(A),MultLe(A,r), \<lambda>x. f(x) +# g(x))"
by (rule_tac h = munion in imp_increasing_comp2, auto)

lemma Increasing_munion:
     "\<lbrakk>F \<in> Increasing(Mult(A), MultLe(A,r), f);
         F \<in> Increasing(Mult(A), MultLe(A,r), g)\<rbrakk>
     \<Longrightarrow> F \<in> Increasing(Mult(A),MultLe(A,r), \<lambda>x. f(x) +# g(x))"
by (rule_tac h = munion in imp_Increasing_comp2, auto)

lemma Always_munion:
"\<lbrakk>F \<in> Always({s \<in> state. <f1(s),f(s)> \<in> MultLe(A,r)});
          F \<in> Always({s \<in> state. <g1(s), g(s)> \<in> MultLe(A,r)});
  \<forall>x \<in> state. f1(x):Mult(A)\<and>f(x):Mult(A) \<and> g1(x):Mult(A) \<and> g(x):Mult(A)\<rbrakk>
      \<Longrightarrow> F \<in> Always({s \<in> state. <f1(s) +# g1(s), f(s) +# g(s)> \<in> MultLe(A,r)})"
apply (rule_tac h = munion in imp_Always_comp2, simp_all)
apply (blast intro: munion_mono, simp_all)
done

lemma Follows_munion:
"\<lbrakk>F \<in> Follows(Mult(A), MultLe(A, r), f1, f);
    F \<in> Follows(Mult(A), MultLe(A, r), g1, g)\<rbrakk>
  \<Longrightarrow> F \<in> Follows(Mult(A), MultLe(A, r), \<lambda>s. f1(s) +# g1(s), \<lambda>s. f(s) +# g(s))"
by (rule_tac h = munion in imp_Follows_comp2, auto)

(** Used in ClientImp **)

lemma Follows_msetsum_UN:
"\<And>f. \<lbrakk>\<forall>i \<in> I. F \<in> Follows(Mult(A), MultLe(A, r), f'(i), f(i));
  \<forall>s. \<forall>i \<in> I. multiset(f'(i, s)) \<and> mset_of(f'(i, s))<=A \<and>
                        multiset(f(i, s)) \<and> mset_of(f(i, s))<=A ;
   Finite(I); F \<in> program\<rbrakk>
        \<Longrightarrow> F \<in> Follows(Mult(A),
                        MultLe(A, r), \<lambda>x. msetsum(\<lambda>i. f'(i, x), I, A),
                                      \<lambda>x. msetsum(\<lambda>i. f(i,  x), I, A))"
apply (erule rev_mp)
apply (drule Finite_into_Fin)
apply (erule Fin_induct)
apply (simp (no_asm_simp))
apply (rule Follows_constantI)
apply (simp_all (no_asm_simp) add: FiniteFun.intros)
apply auto
apply (rule Follows_munion, auto)
done

end
