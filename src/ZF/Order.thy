(*  Title:      ZF/Order.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Results from the book "Set Theory: an Introduction to Independence Proofs"
        by Kenneth Kunen.  Chapter 1, section 6.
Additional definitions and lemmas for reflexive orders.
*)

section\<open>Partial and Total Orderings: Basic Definitions and Properties\<close>

theory Order imports WF Perm begin

text \<open>We adopt the following convention: \<open>ord\<close> is used for
  strict orders and \<open>order\<close> is used for their reflexive
  counterparts.\<close>

definition
  part_ord :: "[i,i]\<Rightarrow>o"                (*Strict partial ordering*)  where
   "part_ord(A,r) \<equiv> irrefl(A,r) \<and> trans[A](r)"

definition
  linear   :: "[i,i]\<Rightarrow>o"                (*Strict total ordering*)  where
   "linear(A,r) \<equiv> (\<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle>:r | x=y | \<langle>y,x\<rangle>:r)"

definition
  tot_ord  :: "[i,i]\<Rightarrow>o"                (*Strict total ordering*)  where
   "tot_ord(A,r) \<equiv> part_ord(A,r) \<and> linear(A,r)"

definition
  "preorder_on(A, r) \<equiv> refl(A, r) \<and> trans[A](r)"

definition                              (*Partial ordering*)
  "partial_order_on(A, r) \<equiv> preorder_on(A, r) \<and> antisym(r)"

abbreviation
  "Preorder(r) \<equiv> preorder_on(field(r), r)"

abbreviation
  "Partial_order(r) \<equiv> partial_order_on(field(r), r)"

definition
  well_ord :: "[i,i]\<Rightarrow>o"                (*Well-ordering*)  where
   "well_ord(A,r) \<equiv> tot_ord(A,r) \<and> wf[A](r)"

definition
  mono_map :: "[i,i,i,i]\<Rightarrow>i"            (*Order-preserving maps*)  where
   "mono_map(A,r,B,s) \<equiv>
              {f \<in> A->B. \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle>:r \<longrightarrow> <f`x,f`y>:s}"

definition
  ord_iso  :: "[i,i,i,i]\<Rightarrow>i"  (\<open>(\<open>notation=\<open>infix ord_iso\<close>\<close>\<langle>_, _\<rangle> \<cong>/ \<langle>_, _\<rangle>)\<close> 51)  (*Order isomorphisms*)  where
   "\<langle>A,r\<rangle> \<cong> \<langle>B,s\<rangle> \<equiv>
              {f \<in> bij(A,B). \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle>:r \<longleftrightarrow> <f`x,f`y>:s}"

definition
  pred     :: "[i,i,i]\<Rightarrow>i"              (*Set of predecessors*)  where
   "pred(A,x,r) \<equiv> {y \<in> A. \<langle>y,x\<rangle>:r}"

definition
  ord_iso_map :: "[i,i,i,i]\<Rightarrow>i"         (*Construction for linearity theorem*)  where
   "ord_iso_map(A,r,B,s) \<equiv>
     \<Union>x\<in>A. \<Union>y\<in>B. \<Union>f \<in> ord_iso(pred(A,x,r), r, pred(B,y,s), s). {\<langle>x,y\<rangle>}"

definition
  first :: "[i, i, i] \<Rightarrow> o"  where
    "first(u, X, R) \<equiv> u \<in> X \<and> (\<forall>v\<in>X. v\<noteq>u \<longrightarrow> \<langle>u,v\<rangle> \<in> R)"

subsection\<open>Immediate Consequences of the Definitions\<close>

lemma part_ord_Imp_asym:
    "part_ord(A,r) \<Longrightarrow> asym(r \<inter> A*A)"
by (unfold part_ord_def irrefl_def trans_on_def asym_def, blast)

lemma linearE:
    "\<lbrakk>linear(A,r);  x \<in> A;  y \<in> A;
        \<langle>x,y\<rangle>:r \<Longrightarrow> P;  x=y \<Longrightarrow> P;  \<langle>y,x\<rangle>:r \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
by (simp add: linear_def, blast)


(** General properties of well_ord **)

lemma well_ordI:
    "\<lbrakk>wf[A](r); linear(A,r)\<rbrakk> \<Longrightarrow> well_ord(A,r)"
apply (simp add: irrefl_def part_ord_def tot_ord_def
                 trans_on_def well_ord_def wf_on_not_refl)
apply (fast elim: linearE wf_on_asym wf_on_chain3)
done

lemma well_ord_is_wf:
    "well_ord(A,r) \<Longrightarrow> wf[A](r)"
by (unfold well_ord_def, safe)

lemma well_ord_is_trans_on:
    "well_ord(A,r) \<Longrightarrow> trans[A](r)"
by (unfold well_ord_def tot_ord_def part_ord_def, safe)

lemma well_ord_is_linear: "well_ord(A,r) \<Longrightarrow> linear(A,r)"
by (unfold well_ord_def tot_ord_def, blast)


(** Derived rules for pred(A,x,r) **)

lemma pred_iff: "y \<in> pred(A,x,r) \<longleftrightarrow> \<langle>y,x\<rangle>:r \<and> y \<in> A"
by (unfold pred_def, blast)

lemmas predI = conjI [THEN pred_iff [THEN iffD2]]

lemma predE: "\<lbrakk>y \<in> pred(A,x,r);  \<lbrakk>y \<in> A; \<langle>y,x\<rangle>:r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (simp add: pred_def)

lemma pred_subset_under: "pred(A,x,r) \<subseteq> r -`` {x}"
by (simp add: pred_def, blast)

lemma pred_subset: "pred(A,x,r) \<subseteq> A"
by (simp add: pred_def, blast)

lemma pred_pred_eq:
    "pred(pred(A,x,r), y, r) = pred(A,x,r) \<inter> pred(A,y,r)"
by (simp add: pred_def, blast)

lemma trans_pred_pred_eq:
    "\<lbrakk>trans[A](r);  \<langle>y,x\<rangle>:r;  x \<in> A;  y \<in> A\<rbrakk>
     \<Longrightarrow> pred(pred(A,x,r), y, r) = pred(A,y,r)"
by (unfold trans_on_def pred_def, blast)


subsection\<open>Restricting an Ordering's Domain\<close>

(** The ordering's properties hold over all subsets of its domain
    [including initial segments of the form pred(A,x,r) **)

(*Note: a relation s such that s<=r need not be a partial ordering*)
lemma part_ord_subset:
    "\<lbrakk>part_ord(A,r);  B<=A\<rbrakk> \<Longrightarrow> part_ord(B,r)"
by (unfold part_ord_def irrefl_def trans_on_def, blast)

lemma linear_subset:
    "\<lbrakk>linear(A,r);  B<=A\<rbrakk> \<Longrightarrow> linear(B,r)"
by (unfold linear_def, blast)

lemma tot_ord_subset:
    "\<lbrakk>tot_ord(A,r);  B<=A\<rbrakk> \<Longrightarrow> tot_ord(B,r)"
  unfolding tot_ord_def
apply (fast elim!: part_ord_subset linear_subset)
done

lemma well_ord_subset:
    "\<lbrakk>well_ord(A,r);  B<=A\<rbrakk> \<Longrightarrow> well_ord(B,r)"
  unfolding well_ord_def
apply (fast elim!: tot_ord_subset wf_on_subset_A)
done


(** Relations restricted to a smaller domain, by Krzysztof Grabczewski **)

lemma irrefl_Int_iff: "irrefl(A,r \<inter> A*A) \<longleftrightarrow> irrefl(A,r)"
by (unfold irrefl_def, blast)

lemma trans_on_Int_iff: "trans[A](r \<inter> A*A) \<longleftrightarrow> trans[A](r)"
by (unfold trans_on_def, blast)

lemma part_ord_Int_iff: "part_ord(A,r \<inter> A*A) \<longleftrightarrow> part_ord(A,r)"
  unfolding part_ord_def
apply (simp add: irrefl_Int_iff trans_on_Int_iff)
done

lemma linear_Int_iff: "linear(A,r \<inter> A*A) \<longleftrightarrow> linear(A,r)"
by (unfold linear_def, blast)

lemma tot_ord_Int_iff: "tot_ord(A,r \<inter> A*A) \<longleftrightarrow> tot_ord(A,r)"
  unfolding tot_ord_def
apply (simp add: part_ord_Int_iff linear_Int_iff)
done

lemma wf_on_Int_iff: "wf[A](r \<inter> A*A) \<longleftrightarrow> wf[A](r)"
apply (unfold wf_on_def wf_def, fast) (*10 times faster than blast!*)
done

lemma well_ord_Int_iff: "well_ord(A,r \<inter> A*A) \<longleftrightarrow> well_ord(A,r)"
  unfolding well_ord_def
apply (simp add: tot_ord_Int_iff wf_on_Int_iff)
done


subsection\<open>Empty and Unit Domains\<close>

(*The empty relation is well-founded*)
lemma wf_on_any_0: "wf[A](0)"
by (simp add: wf_on_def wf_def, fast)

subsubsection\<open>Relations over the Empty Set\<close>

lemma irrefl_0: "irrefl(0,r)"
by (unfold irrefl_def, blast)

lemma trans_on_0: "trans[0](r)"
by (unfold trans_on_def, blast)

lemma part_ord_0: "part_ord(0,r)"
  unfolding part_ord_def
apply (simp add: irrefl_0 trans_on_0)
done

lemma linear_0: "linear(0,r)"
by (unfold linear_def, blast)

lemma tot_ord_0: "tot_ord(0,r)"
  unfolding tot_ord_def
apply (simp add: part_ord_0 linear_0)
done

lemma wf_on_0: "wf[0](r)"
by (unfold wf_on_def wf_def, blast)

lemma well_ord_0: "well_ord(0,r)"
  unfolding well_ord_def
apply (simp add: tot_ord_0 wf_on_0)
done


subsubsection\<open>The Empty Relation Well-Orders the Unit Set\<close>

text\<open>by Grabczewski\<close>

lemma tot_ord_unit: "tot_ord({a},0)"
by (simp add: irrefl_def trans_on_def part_ord_def linear_def tot_ord_def)

lemma well_ord_unit: "well_ord({a},0)"
  unfolding well_ord_def
apply (simp add: tot_ord_unit wf_on_any_0)
done


subsection\<open>Order-Isomorphisms\<close>

text\<open>Suppes calls them "similarities"\<close>

(** Order-preserving (monotone) maps **)

lemma mono_map_is_fun: "f \<in> mono_map(A,r,B,s) \<Longrightarrow> f \<in> A->B"
by (simp add: mono_map_def)

lemma mono_map_is_inj:
    "\<lbrakk>linear(A,r);  wf[B](s);  f \<in> mono_map(A,r,B,s)\<rbrakk> \<Longrightarrow> f \<in> inj(A,B)"
apply (unfold mono_map_def inj_def, clarify)
apply (erule_tac x=w and y=x in linearE, assumption+)
apply (force intro: apply_type dest: wf_on_not_refl)+
done

lemma ord_isoI:
    "\<lbrakk>f \<in> bij(A, B);
        \<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> <f`x, f`y> \<in> s\<rbrakk>
     \<Longrightarrow> f \<in> ord_iso(A,r,B,s)"
by (simp add: ord_iso_def)

lemma ord_iso_is_mono_map:
    "f \<in> ord_iso(A,r,B,s) \<Longrightarrow> f \<in> mono_map(A,r,B,s)"
apply (simp add: ord_iso_def mono_map_def)
apply (blast dest!: bij_is_fun)
done

lemma ord_iso_is_bij:
    "f \<in> ord_iso(A,r,B,s) \<Longrightarrow> f \<in> bij(A,B)"
by (simp add: ord_iso_def)

(*Needed?  But ord_iso_converse is!*)
lemma ord_iso_apply:
    "\<lbrakk>f \<in> ord_iso(A,r,B,s);  \<langle>x,y\<rangle>: r;  x \<in> A;  y \<in> A\<rbrakk> \<Longrightarrow> <f`x, f`y> \<in> s"
by (simp add: ord_iso_def)

lemma ord_iso_converse:
    "\<lbrakk>f \<in> ord_iso(A,r,B,s);  \<langle>x,y\<rangle>: s;  x \<in> B;  y \<in> B\<rbrakk>
     \<Longrightarrow> <converse(f) ` x, converse(f) ` y> \<in> r"
apply (simp add: ord_iso_def, clarify)
apply (erule bspec [THEN bspec, THEN iffD2])
apply (erule asm_rl bij_converse_bij [THEN bij_is_fun, THEN apply_type])+
apply (auto simp add: right_inverse_bij)
done


(** Symmetry and Transitivity Rules **)

(*Reflexivity of similarity*)
lemma ord_iso_refl: "id(A): ord_iso(A,r,A,r)"
by (rule id_bij [THEN ord_isoI], simp)

(*Symmetry of similarity*)
lemma ord_iso_sym: "f \<in> ord_iso(A,r,B,s) \<Longrightarrow> converse(f): ord_iso(B,s,A,r)"
apply (simp add: ord_iso_def)
apply (auto simp add: right_inverse_bij bij_converse_bij
                      bij_is_fun [THEN apply_funtype])
done

(*Transitivity of similarity*)
lemma mono_map_trans:
    "\<lbrakk>g \<in> mono_map(A,r,B,s);  f \<in> mono_map(B,s,C,t)\<rbrakk>
     \<Longrightarrow> (f O g): mono_map(A,r,C,t)"
  unfolding mono_map_def
apply (auto simp add: comp_fun)
done

(*Transitivity of similarity: the order-isomorphism relation*)
lemma ord_iso_trans:
    "\<lbrakk>g \<in> ord_iso(A,r,B,s);  f \<in> ord_iso(B,s,C,t)\<rbrakk>
     \<Longrightarrow> (f O g): ord_iso(A,r,C,t)"
apply (unfold ord_iso_def, clarify)
apply (frule bij_is_fun [of f])
apply (frule bij_is_fun [of g])
apply (auto simp add: comp_bij)
done

(** Two monotone maps can make an order-isomorphism **)

lemma mono_ord_isoI:
    "\<lbrakk>f \<in> mono_map(A,r,B,s);  g \<in> mono_map(B,s,A,r);
        f O g = id(B);  g O f = id(A)\<rbrakk> \<Longrightarrow> f \<in> ord_iso(A,r,B,s)"
apply (simp add: ord_iso_def mono_map_def, safe)
apply (intro fg_imp_bijective, auto)
apply (subgoal_tac "<g` (f`x), g` (f`y) > \<in> r")
apply (simp add: comp_eq_id_iff [THEN iffD1])
apply (blast intro: apply_funtype)
done

lemma well_ord_mono_ord_isoI:
     "\<lbrakk>well_ord(A,r);  well_ord(B,s);
         f \<in> mono_map(A,r,B,s);  converse(f): mono_map(B,s,A,r)\<rbrakk>
      \<Longrightarrow> f \<in> ord_iso(A,r,B,s)"
apply (intro mono_ord_isoI, auto)
apply (frule mono_map_is_fun [THEN fun_is_rel])
apply (erule converse_converse [THEN subst], rule left_comp_inverse)
apply (blast intro: left_comp_inverse mono_map_is_inj well_ord_is_linear
                    well_ord_is_wf)+
done


(** Order-isomorphisms preserve the ordering's properties **)

lemma part_ord_ord_iso:
    "\<lbrakk>part_ord(B,s);  f \<in> ord_iso(A,r,B,s)\<rbrakk> \<Longrightarrow> part_ord(A,r)"
apply (simp add: part_ord_def irrefl_def trans_on_def ord_iso_def)
apply (fast intro: bij_is_fun [THEN apply_type])
done

lemma linear_ord_iso:
    "\<lbrakk>linear(B,s);  f \<in> ord_iso(A,r,B,s)\<rbrakk> \<Longrightarrow> linear(A,r)"
apply (simp add: linear_def ord_iso_def, safe)
apply (drule_tac x1 = "f`x" and x = "f`y" in bspec [THEN bspec])
apply (safe elim!: bij_is_fun [THEN apply_type])
apply (drule_tac t = "(`) (converse (f))" in subst_context)
apply (simp add: left_inverse_bij)
done

lemma wf_on_ord_iso:
    "\<lbrakk>wf[B](s);  f \<in> ord_iso(A,r,B,s)\<rbrakk> \<Longrightarrow> wf[A](r)"
apply (simp add: wf_on_def wf_def ord_iso_def, safe)
apply (drule_tac x = "{f`z. z \<in> Z \<inter> A}" in spec)
apply (safe intro!: equalityI)
apply (blast dest!: equalityD1 intro: bij_is_fun [THEN apply_type])+
done

lemma well_ord_ord_iso:
    "\<lbrakk>well_ord(B,s);  f \<in> ord_iso(A,r,B,s)\<rbrakk> \<Longrightarrow> well_ord(A,r)"
  unfolding well_ord_def tot_ord_def
apply (fast elim!: part_ord_ord_iso linear_ord_iso wf_on_ord_iso)
done


subsection\<open>Main results of Kunen, Chapter 1 section 6\<close>

(*Inductive argument for Kunen's Lemma 6.1, etc.
  Simple proof from Halmos, page 72*)
lemma well_ord_iso_subset_lemma:
     "\<lbrakk>well_ord(A,r);  f \<in> ord_iso(A,r, A',r);  A'<= A;  y \<in> A\<rbrakk>
      \<Longrightarrow> \<not> <f`y, y>: r"
apply (simp add: well_ord_def ord_iso_def)
apply (elim conjE CollectE)
apply (rule_tac a=y in wf_on_induct, assumption+)
apply (blast dest: bij_is_fun [THEN apply_type])
done

(*Kunen's Lemma 6.1 \<in> there's no order-isomorphism to an initial segment
                     of a well-ordering*)
lemma well_ord_iso_predE:
     "\<lbrakk>well_ord(A,r);  f \<in> ord_iso(A, r, pred(A,x,r), r);  x \<in> A\<rbrakk> \<Longrightarrow> P"
apply (insert well_ord_iso_subset_lemma [of A r f "pred(A,x,r)" x])
apply (simp add: pred_subset)
(*Now we know  f`x < x *)
apply (drule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], assumption)
(*Now we also know @{term"f`x \<in> pred(A,x,r)"}: contradiction! *)
apply (simp add: well_ord_def pred_def)
done

(*Simple consequence of Lemma 6.1*)
lemma well_ord_iso_pred_eq:
     "\<lbrakk>well_ord(A,r);  f \<in> ord_iso(pred(A,a,r), r, pred(A,c,r), r);
         a \<in> A;  c \<in> A\<rbrakk> \<Longrightarrow> a=c"
apply (frule well_ord_is_trans_on)
apply (frule well_ord_is_linear)
apply (erule_tac x=a and y=c in linearE, assumption+)
apply (drule ord_iso_sym)
(*two symmetric cases*)
apply (auto elim!: well_ord_subset [OF _ pred_subset, THEN well_ord_iso_predE]
            intro!: predI
            simp add: trans_pred_pred_eq)
done

(*Does not assume r is a wellordering!*)
lemma ord_iso_image_pred:
     "\<lbrakk>f \<in> ord_iso(A,r,B,s);  a \<in> A\<rbrakk> \<Longrightarrow> f `` pred(A,a,r) = pred(B, f`a, s)"
  unfolding ord_iso_def pred_def
apply (erule CollectE)
apply (simp (no_asm_simp) add: image_fun [OF bij_is_fun Collect_subset])
apply (rule equalityI)
apply (safe elim!: bij_is_fun [THEN apply_type])
apply (rule RepFun_eqI)
apply (blast intro!: right_inverse_bij [symmetric])
apply (auto simp add: right_inverse_bij  bij_is_fun [THEN apply_funtype])
done

lemma ord_iso_restrict_image:
     "\<lbrakk>f \<in> ord_iso(A,r,B,s);  C<=A\<rbrakk>
      \<Longrightarrow> restrict(f,C) \<in> ord_iso(C, r, f``C, s)"
apply (simp add: ord_iso_def)
apply (blast intro: bij_is_inj restrict_bij)
done

(*But in use, A and B may themselves be initial segments.  Then use
  trans_pred_pred_eq to simplify the pred(pred...) terms.  See just below.*)
lemma ord_iso_restrict_pred:
   "\<lbrakk>f \<in> ord_iso(A,r,B,s);   a \<in> A\<rbrakk>
    \<Longrightarrow> restrict(f, pred(A,a,r)) \<in> ord_iso(pred(A,a,r), r, pred(B, f`a, s), s)"
apply (simp add: ord_iso_image_pred [symmetric])
apply (blast intro: ord_iso_restrict_image elim: predE)
done

(*Tricky; a lot of forward proof!*)
lemma well_ord_iso_preserving:
     "\<lbrakk>well_ord(A,r);  well_ord(B,s);  \<langle>a,c\<rangle>: r;
         f \<in> ord_iso(pred(A,a,r), r, pred(B,b,s), s);
         g \<in> ord_iso(pred(A,c,r), r, pred(B,d,s), s);
         a \<in> A;  c \<in> A;  b \<in> B;  d \<in> B\<rbrakk> \<Longrightarrow> \<langle>b,d\<rangle>: s"
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], (erule asm_rl predI predE)+)
apply (subgoal_tac "b = g`a")
apply (simp (no_asm_simp))
apply (rule well_ord_iso_pred_eq, auto)
apply (frule ord_iso_restrict_pred, (erule asm_rl predI)+)
apply (simp add: well_ord_is_trans_on trans_pred_pred_eq)
apply (erule ord_iso_sym [THEN ord_iso_trans], assumption)
done

(*See Halmos, page 72*)
lemma well_ord_iso_unique_lemma:
     "\<lbrakk>well_ord(A,r);
         f \<in> ord_iso(A,r, B,s);  g \<in> ord_iso(A,r, B,s);  y \<in> A\<rbrakk>
      \<Longrightarrow> \<not> <g`y, f`y> \<in> s"
apply (frule well_ord_iso_subset_lemma)
apply (rule_tac f = "converse (f) " and g = g in ord_iso_trans)
apply auto
apply (blast intro: ord_iso_sym)
apply (frule ord_iso_is_bij [of f])
apply (frule ord_iso_is_bij [of g])
apply (frule ord_iso_converse)
apply (blast intro!: bij_converse_bij
             intro: bij_is_fun apply_funtype)+
apply (erule notE)
apply (simp add: left_inverse_bij bij_is_fun comp_fun_apply [of _ A B])
done


(*Kunen's Lemma 6.2: Order-isomorphisms between well-orderings are unique*)
lemma well_ord_iso_unique: "\<lbrakk>well_ord(A,r);
         f \<in> ord_iso(A,r, B,s);  g \<in> ord_iso(A,r, B,s)\<rbrakk> \<Longrightarrow> f = g"
apply (rule fun_extension)
apply (erule ord_iso_is_bij [THEN bij_is_fun])+
apply (subgoal_tac "f`x \<in> B \<and> g`x \<in> B \<and> linear(B,s)")
 apply (simp add: linear_def)
 apply (blast dest: well_ord_iso_unique_lemma)
apply (blast intro: ord_iso_is_bij bij_is_fun apply_funtype
                    well_ord_is_linear well_ord_ord_iso ord_iso_sym)
done

subsection\<open>Towards Kunen's Theorem 6.3: Linearity of the Similarity Relation\<close>

lemma ord_iso_map_subset: "ord_iso_map(A,r,B,s) \<subseteq> A*B"
by (unfold ord_iso_map_def, blast)

lemma domain_ord_iso_map: "domain(ord_iso_map(A,r,B,s)) \<subseteq> A"
by (unfold ord_iso_map_def, blast)

lemma range_ord_iso_map: "range(ord_iso_map(A,r,B,s)) \<subseteq> B"
by (unfold ord_iso_map_def, blast)

lemma converse_ord_iso_map:
    "converse(ord_iso_map(A,r,B,s)) = ord_iso_map(B,s,A,r)"
  unfolding ord_iso_map_def
apply (blast intro: ord_iso_sym)
done

lemma function_ord_iso_map:
    "well_ord(B,s) \<Longrightarrow> function(ord_iso_map(A,r,B,s))"
  unfolding ord_iso_map_def function_def
apply (blast intro: well_ord_iso_pred_eq ord_iso_sym ord_iso_trans)
done

lemma ord_iso_map_fun: "well_ord(B,s) \<Longrightarrow> ord_iso_map(A,r,B,s)
           \<in> domain(ord_iso_map(A,r,B,s)) -> range(ord_iso_map(A,r,B,s))"
by (simp add: Pi_iff function_ord_iso_map
                 ord_iso_map_subset [THEN domain_times_range])

lemma ord_iso_map_mono_map:
    "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk>
     \<Longrightarrow> ord_iso_map(A,r,B,s)
           \<in> mono_map(domain(ord_iso_map(A,r,B,s)), r,
                      range(ord_iso_map(A,r,B,s)), s)"
  unfolding mono_map_def
apply (simp (no_asm_simp) add: ord_iso_map_fun)
apply safe
apply (subgoal_tac "x \<in> A \<and> ya:A \<and> y \<in> B \<and> yb:B")
 apply (simp add: apply_equality [OF _  ord_iso_map_fun])
   unfolding ord_iso_map_def
 apply (blast intro: well_ord_iso_preserving, blast)
done

lemma ord_iso_map_ord_iso:
    "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk> \<Longrightarrow> ord_iso_map(A,r,B,s)
           \<in> ord_iso(domain(ord_iso_map(A,r,B,s)), r,
                      range(ord_iso_map(A,r,B,s)), s)"
apply (rule well_ord_mono_ord_isoI)
   prefer 4
   apply (rule converse_ord_iso_map [THEN subst])
   apply (simp add: ord_iso_map_mono_map
                    ord_iso_map_subset [THEN converse_converse])
apply (blast intro!: domain_ord_iso_map range_ord_iso_map
             intro: well_ord_subset ord_iso_map_mono_map)+
done


(*One way of saying that domain(ord_iso_map(A,r,B,s)) is downwards-closed*)
lemma domain_ord_iso_map_subset:
     "\<lbrakk>well_ord(A,r);  well_ord(B,s);
         a \<in> A;  a \<notin> domain(ord_iso_map(A,r,B,s))\<rbrakk>
      \<Longrightarrow>  domain(ord_iso_map(A,r,B,s)) \<subseteq> pred(A, a, r)"
  unfolding ord_iso_map_def
apply (safe intro!: predI)
(*Case analysis on  xa vs a in r *)
apply (simp (no_asm_simp))
apply (frule_tac A = A in well_ord_is_linear)
apply (rename_tac b y f)
apply (erule_tac x=b and y=a in linearE, assumption+)
(*Trivial case: b=a*)
apply clarify
apply blast
(*Harder case: \<langle>a, xa\<rangle>: r*)
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type],
       (erule asm_rl predI predE)+)
apply (frule ord_iso_restrict_pred)
 apply (simp add: pred_iff)
apply (simp split: split_if_asm
          add: well_ord_is_trans_on trans_pred_pred_eq domain_UN domain_Union, blast)
done

(*For the 4-way case analysis in the main result*)
lemma domain_ord_iso_map_cases:
     "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk>
      \<Longrightarrow> domain(ord_iso_map(A,r,B,s)) = A |
          (\<exists>x\<in>A. domain(ord_iso_map(A,r,B,s)) = pred(A,x,r))"
apply (frule well_ord_is_wf)
  unfolding wf_on_def wf_def
apply (drule_tac x = "A-domain (ord_iso_map (A,r,B,s))" in spec)
apply safe
(*The first case: the domain equals A*)
apply (rule domain_ord_iso_map [THEN equalityI])
apply (erule Diff_eq_0_iff [THEN iffD1])
(*The other case: the domain equals an initial segment*)
apply (blast del: domainI subsetI
             elim!: predE
             intro!: domain_ord_iso_map_subset
             intro: subsetI)+
done

(*As above, by duality*)
lemma range_ord_iso_map_cases:
    "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk>
     \<Longrightarrow> range(ord_iso_map(A,r,B,s)) = B |
         (\<exists>y\<in>B. range(ord_iso_map(A,r,B,s)) = pred(B,y,s))"
apply (rule converse_ord_iso_map [THEN subst])
apply (simp add: domain_ord_iso_map_cases)
done

text\<open>Kunen's Theorem 6.3: Fundamental Theorem for Well-Ordered Sets\<close>
theorem well_ord_trichotomy:
   "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk>
    \<Longrightarrow> ord_iso_map(A,r,B,s) \<in> ord_iso(A, r, B, s) |
        (\<exists>x\<in>A. ord_iso_map(A,r,B,s) \<in> ord_iso(pred(A,x,r), r, B, s)) |
        (\<exists>y\<in>B. ord_iso_map(A,r,B,s) \<in> ord_iso(A, r, pred(B,y,s), s))"
apply (frule_tac B = B in domain_ord_iso_map_cases, assumption)
apply (frule_tac B = B in range_ord_iso_map_cases, assumption)
apply (drule ord_iso_map_ord_iso, assumption)
apply (elim disjE bexE)
   apply (simp_all add: bexI)
apply (rule wf_on_not_refl [THEN notE])
  apply (erule well_ord_is_wf)
 apply assumption
apply (subgoal_tac "\<langle>x,y\<rangle>: ord_iso_map (A,r,B,s) ")
 apply (drule rangeI)
 apply (simp add: pred_def)
apply (unfold ord_iso_map_def, blast)
done


subsection\<open>Miscellaneous Results by Krzysztof Grabczewski\<close>

(** Properties of converse(r) **)

lemma irrefl_converse: "irrefl(A,r) \<Longrightarrow> irrefl(A,converse(r))"
by (unfold irrefl_def, blast)

lemma trans_on_converse: "trans[A](r) \<Longrightarrow> trans[A](converse(r))"
by (unfold trans_on_def, blast)

lemma part_ord_converse: "part_ord(A,r) \<Longrightarrow> part_ord(A,converse(r))"
  unfolding part_ord_def
apply (blast intro!: irrefl_converse trans_on_converse)
done

lemma linear_converse: "linear(A,r) \<Longrightarrow> linear(A,converse(r))"
by (unfold linear_def, blast)

lemma tot_ord_converse: "tot_ord(A,r) \<Longrightarrow> tot_ord(A,converse(r))"
  unfolding tot_ord_def
apply (blast intro!: part_ord_converse linear_converse)
done


(** By Krzysztof Grabczewski.
    Lemmas involving the first element of a well ordered set **)

lemma first_is_elem: "first(b,B,r) \<Longrightarrow> b \<in> B"
by (unfold first_def, blast)

lemma well_ord_imp_ex1_first:
        "\<lbrakk>well_ord(A,r); B<=A; B\<noteq>0\<rbrakk> \<Longrightarrow> (\<exists>!b. first(b,B,r))"
  unfolding well_ord_def wf_on_def wf_def first_def
apply (elim conjE allE disjE, blast)
apply (erule bexE)
apply (rule_tac a = x in ex1I, auto)
apply (unfold tot_ord_def linear_def, blast)
done

lemma the_first_in:
     "\<lbrakk>well_ord(A,r); B<=A; B\<noteq>0\<rbrakk> \<Longrightarrow> (THE b. first(b,B,r)) \<in> B"
apply (drule well_ord_imp_ex1_first, assumption+)
apply (rule first_is_elem)
apply (erule theI)
done


subsection \<open>Lemmas for the Reflexive Orders\<close>

lemma subset_vimage_vimage_iff:
  "\<lbrakk>Preorder(r); A \<subseteq> field(r); B \<subseteq> field(r)\<rbrakk> \<Longrightarrow>
  r -`` A \<subseteq> r -`` B \<longleftrightarrow> (\<forall>a\<in>A. \<exists>b\<in>B. \<langle>a, b\<rangle> \<in> r)"
  apply (auto simp: subset_def preorder_on_def refl_def vimage_def image_def)
   apply blast
  unfolding trans_on_def
  apply (erule_tac P = "(\<lambda>x. \<forall>y\<in>field(r).
          \<forall>z\<in>field(r). \<langle>x, y\<rangle> \<in> r \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r)" for r in rev_ballE)
    (* instance obtained from proof term generated by best *)
   apply best
  apply blast
  done

lemma subset_vimage1_vimage1_iff:
  "\<lbrakk>Preorder(r); a \<in> field(r); b \<in> field(r)\<rbrakk> \<Longrightarrow>
  r -`` {a} \<subseteq> r -`` {b} \<longleftrightarrow> \<langle>a, b\<rangle> \<in> r"
  by (simp add: subset_vimage_vimage_iff)

lemma Refl_antisym_eq_Image1_Image1_iff:
  "\<lbrakk>refl(field(r), r); antisym(r); a \<in> field(r); b \<in> field(r)\<rbrakk> \<Longrightarrow>
  r `` {a} = r `` {b} \<longleftrightarrow> a = b"
  apply rule
   apply (frule equality_iffD)
   apply (drule equality_iffD)
   apply (simp add: antisym_def refl_def)
   apply best
  apply (simp add: antisym_def refl_def)
  done

lemma Partial_order_eq_Image1_Image1_iff:
  "\<lbrakk>Partial_order(r); a \<in> field(r); b \<in> field(r)\<rbrakk> \<Longrightarrow>
  r `` {a} = r `` {b} \<longleftrightarrow> a = b"
  by (simp add: partial_order_on_def preorder_on_def
    Refl_antisym_eq_Image1_Image1_iff)

lemma Refl_antisym_eq_vimage1_vimage1_iff:
  "\<lbrakk>refl(field(r), r); antisym(r); a \<in> field(r); b \<in> field(r)\<rbrakk> \<Longrightarrow>
  r -`` {a} = r -`` {b} \<longleftrightarrow> a = b"
  apply rule
   apply (frule equality_iffD)
   apply (drule equality_iffD)
   apply (simp add: antisym_def refl_def)
   apply best
  apply (simp add: antisym_def refl_def)
  done

lemma Partial_order_eq_vimage1_vimage1_iff:
  "\<lbrakk>Partial_order(r); a \<in> field(r); b \<in> field(r)\<rbrakk> \<Longrightarrow>
  r -`` {a} = r -`` {b} \<longleftrightarrow> a = b"
  by (simp add: partial_order_on_def preorder_on_def
    Refl_antisym_eq_vimage1_vimage1_iff)

end
