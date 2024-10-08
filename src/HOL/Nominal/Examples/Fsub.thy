(*<*)
theory Fsub
imports "HOL-Nominal.Nominal" 
begin
(*>*)

text\<open>Authors: Christian Urban,
                Benjamin Pierce,
                Dimitrios Vytiniotis
                Stephanie Weirich
                Steve Zdancewic
                Julien Narboux
                Stefan Berghofer

       with great help from Markus Wenzel.\<close>

section \<open>Types for Names, Nominal Datatype Declaration for Types and Terms\<close>

text \<open>The main point of this solution is to use names everywhere (be they bound, 
  binding or free). In System \FSUB{} there are two kinds of names corresponding to 
  type-variables and to term-variables. These two kinds of names are represented in 
  the nominal datatype package as atom-types \<open>tyvrs\<close> and \<open>vrs\<close>:\<close>

atom_decl tyvrs vrs

text\<open>There are numerous facts that come with this declaration: for example that 
  there are infinitely many elements in \<open>tyvrs\<close> and \<open>vrs\<close>.\<close>

text\<open>The constructors for types and terms in System \FSUB{} contain abstractions 
  over type-variables and term-variables. The nominal datatype package uses 
  \<open>\<guillemotleft>\<dots>\<guillemotright>\<dots>\<close> to indicate where abstractions occur.\<close>

nominal_datatype ty = 
    Tvar   "tyvrs"
  | Top
  | Arrow  "ty" "ty"         (infixr \<open>\<rightarrow>\<close> 200)
  | Forall "\<guillemotleft>tyvrs\<guillemotright>ty" "ty" 

nominal_datatype trm = 
    Var   "vrs"
  | Abs   "\<guillemotleft>vrs\<guillemotright>trm" "ty" 
  | TAbs  "\<guillemotleft>tyvrs\<guillemotright>trm" "ty"
  | App   "trm" "trm" (infixl \<open>\<cdot>\<close> 200)
  | TApp  "trm" "ty"  (infixl \<open>\<cdot>\<^sub>\<tau>\<close> 200)

text \<open>To be polite to the eye, some more familiar notation is introduced. 
  Because of the change in the order of arguments, one needs to use 
  translation rules, instead of syntax annotations at the term-constructors
  as given above for \<^term>\<open>Arrow\<close>.\<close>

abbreviation
  Forall_syn :: "tyvrs \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"  (\<open>(3\<forall>_<:_./ _)\<close> [0, 0, 10] 10) 
where
  "\<forall>X<:T\<^sub>1. T\<^sub>2 \<equiv> ty.Forall X T\<^sub>2 T\<^sub>1"

abbreviation
  Abs_syn    :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"  (\<open>(3\<lambda>_:_./ _)\<close> [0, 0, 10] 10) 
where
  "\<lambda>x:T. t \<equiv> trm.Abs x t T"

abbreviation
  TAbs_syn   :: "tyvrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" (\<open>(3\<lambda>_<:_./ _)\<close> [0, 0, 10] 10) 
where
  "\<lambda>X<:T. t \<equiv> trm.TAbs X t T"

text \<open>Again there are numerous facts that are proved automatically for \<^typ>\<open>ty\<close> 
  and \<^typ>\<open>trm\<close>: for example that the set of free variables, i.e.~the \<open>support\<close>, 
  is finite. However note that nominal-datatype declarations do \emph{not} define 
  ``classical" constructor-based datatypes, but rather define $\alpha$-equivalence 
  classes---we can for example show that $\alpha$-equivalent \<^typ>\<open>ty\<close>s 
  and \<^typ>\<open>trm\<close>s are equal:\<close>

lemma alpha_illustration:
  shows "(\<forall>X<:T. Tvar X) = (\<forall>Y<:T. Tvar Y)"
  and   "(\<lambda>x:T. Var x) = (\<lambda>y:T. Var y)"
  by (simp_all add: ty.inject trm.inject alpha calc_atm fresh_atm)

section \<open>SubTyping Contexts\<close>

nominal_datatype binding = 
    VarB vrs ty 
  | TVarB tyvrs ty

type_synonym env = "binding list"

text \<open>Typing contexts are represented as lists that ``grow" on the left; we
  thereby deviating from the convention in the POPLmark-paper. The lists contain
  pairs of type-variables and types (this is sufficient for Part 1A).\<close>

text \<open>In order to state validity-conditions for typing-contexts, the notion of
  a \<open>dom\<close> of a typing-context is handy.\<close>

nominal_primrec
  "tyvrs_of" :: "binding \<Rightarrow> tyvrs set"
where
  "tyvrs_of (VarB  x y) = {}"
| "tyvrs_of (TVarB x y) = {x}"
by auto

nominal_primrec
  "vrs_of" :: "binding \<Rightarrow> vrs set"
where
  "vrs_of (VarB  x y) = {x}"
| "vrs_of (TVarB x y) = {}"
by auto

primrec
  "ty_dom" :: "env \<Rightarrow> tyvrs set"
where
  "ty_dom [] = {}"
| "ty_dom (X#\<Gamma>) = (tyvrs_of X)\<union>(ty_dom \<Gamma>)" 

primrec
  "trm_dom" :: "env \<Rightarrow> vrs set"
where
  "trm_dom [] = {}"
| "trm_dom (X#\<Gamma>) = (vrs_of X)\<union>(trm_dom \<Gamma>)" 

lemma vrs_of_eqvt[eqvt]:
  fixes pi ::"tyvrs prm"
  and   pi'::"vrs   prm"
  shows "pi \<bullet>(tyvrs_of x) = tyvrs_of (pi\<bullet>x)"
  and   "pi'\<bullet>(tyvrs_of x) = tyvrs_of (pi'\<bullet>x)"
  and   "pi \<bullet>(vrs_of x)   = vrs_of   (pi\<bullet>x)"
  and   "pi'\<bullet>(vrs_of x)   = vrs_of   (pi'\<bullet>x)"
by (nominal_induct x rule: binding.strong_induct) (simp_all add: tyvrs_of.simps eqvts)

lemma doms_eqvt[eqvt]:
  fixes pi::"tyvrs prm"
  and   pi'::"vrs prm"
  shows "pi \<bullet>(ty_dom \<Gamma>)  = ty_dom  (pi\<bullet>\<Gamma>)"
  and   "pi'\<bullet>(ty_dom \<Gamma>)  = ty_dom  (pi'\<bullet>\<Gamma>)"
  and   "pi \<bullet>(trm_dom \<Gamma>) = trm_dom (pi\<bullet>\<Gamma>)"
  and   "pi'\<bullet>(trm_dom \<Gamma>) = trm_dom (pi'\<bullet>\<Gamma>)"
by (induct \<Gamma>) (simp_all add: eqvts)

lemma finite_vrs:
  shows "finite (tyvrs_of x)"
  and   "finite (vrs_of x)"
by (nominal_induct rule:binding.strong_induct) auto
 
lemma finite_doms:
  shows "finite (ty_dom \<Gamma>)"
  and   "finite (trm_dom \<Gamma>)"
by (induct \<Gamma>) (auto simp: finite_vrs)

lemma ty_dom_supp:
  shows "(supp (ty_dom  \<Gamma>)) = (ty_dom  \<Gamma>)"
  and   "(supp (trm_dom \<Gamma>)) = (trm_dom \<Gamma>)"
by (simp only: at_fin_set_supp at_tyvrs_inst at_vrs_inst finite_doms)+

lemma ty_dom_inclusion:
  assumes a: "(TVarB X T)\<in>set \<Gamma>" 
  shows "X\<in>(ty_dom \<Gamma>)"
using a by (induct \<Gamma>) (auto)

lemma ty_binding_existence:
  assumes "X \<in> (tyvrs_of a)"
  shows "\<exists>T.(TVarB X T=a)"
  using assms
by (nominal_induct a rule: binding.strong_induct) (auto)

lemma ty_dom_existence:
  assumes a: "X\<in>(ty_dom \<Gamma>)" 
  shows "\<exists>T.(TVarB X T)\<in>set \<Gamma>"
  using a 
proof (induction \<Gamma>)
  case Nil then show ?case by simp
next
  case (Cons a \<Gamma>) then show ?case
    using ty_binding_existence by fastforce
qed

lemma doms_append:
  shows "ty_dom (\<Gamma>@\<Delta>) = ((ty_dom \<Gamma>) \<union> (ty_dom \<Delta>))"
  and   "trm_dom (\<Gamma>@\<Delta>) = ((trm_dom \<Gamma>) \<union> (trm_dom \<Delta>))"
  by (induct \<Gamma>) (auto)

lemma ty_vrs_prm_simp:
  fixes pi::"vrs prm"
  and   S::"ty"
  shows "pi\<bullet>S = S"
by (induct S rule: ty.induct) (auto simp: calc_atm)

lemma fresh_ty_dom_cons:
  fixes X::"tyvrs"
  shows "X\<sharp>(ty_dom (Y#\<Gamma>)) = (X\<sharp>(tyvrs_of Y) \<and> X\<sharp>(ty_dom \<Gamma>))"
proof (nominal_induct rule:binding.strong_induct)
  case (VarB vrs ty)
  then show ?case by auto
next
  case (TVarB tyvrs ty)
  then show ?case
    by (simp add: at_fin_set_supp at_tyvrs_inst finite_doms(1) fresh_def supp_atm(1))
qed

lemma tyvrs_fresh:
  fixes   X::"tyvrs"
  assumes "X \<sharp> a" 
  shows   "X \<sharp> tyvrs_of a"
  and     "X \<sharp> vrs_of a"
  using assms
  by (nominal_induct a rule:binding.strong_induct) (force simp: fresh_singleton)+

lemma fresh_dom:
  fixes X::"tyvrs"
  assumes a: "X\<sharp>\<Gamma>" 
  shows "X\<sharp>(ty_dom \<Gamma>)"
using a
proof (induct \<Gamma>)
  case Nil then show ?case by auto
next
  case (Cons a \<Gamma>) then show ?case
    by (meson fresh_list_cons fresh_ty_dom_cons tyvrs_fresh(1))
qed

text \<open>Not all lists of type \<^typ>\<open>env\<close> are well-formed. One condition
  requires that in \<^term>\<open>TVarB X S#\<Gamma>\<close> all free variables of \<^term>\<open>S\<close> must be 
  in the \<^term>\<open>ty_dom\<close> of \<^term>\<open>\<Gamma>\<close>, that is \<^term>\<open>S\<close> must be \<open>closed\<close> 
  in \<^term>\<open>\<Gamma>\<close>. The set of free variables of \<^term>\<open>S\<close> is the 
  \<open>support\<close> of \<^term>\<open>S\<close>.\<close>

definition "closed_in" :: "ty \<Rightarrow> env \<Rightarrow> bool" (\<open>_ closed'_in _\<close> [100,100] 100) where
  "S closed_in \<Gamma> \<equiv> (supp S)\<subseteq>(ty_dom \<Gamma>)"

lemma closed_in_eqvt[eqvt]:
  fixes pi::"tyvrs prm"
  assumes a: "S closed_in \<Gamma>" 
  shows "(pi\<bullet>S) closed_in (pi\<bullet>\<Gamma>)"
  using a
proof -
  from a have "pi\<bullet>(S closed_in \<Gamma>)" by (simp add: perm_bool)
  then show "(pi\<bullet>S) closed_in (pi\<bullet>\<Gamma>)" by (simp add: closed_in_def eqvts)
qed

lemma tyvrs_vrs_prm_simp:
  fixes pi::"vrs prm"
  shows "tyvrs_of (pi\<bullet>a) = tyvrs_of a"
  by (nominal_induct rule:binding.strong_induct) (auto simp: vrs_prm_tyvrs_def)

lemma ty_vrs_fresh:
  fixes x::"vrs"
  and   T::"ty"
  shows "x \<sharp> T"
by (simp add: fresh_def supp_def ty_vrs_prm_simp)

lemma ty_dom_vrs_prm_simp:
  fixes pi::"vrs prm"
  and   \<Gamma>::"env"
  shows "(ty_dom (pi\<bullet>\<Gamma>)) = (ty_dom \<Gamma>)"
by (induct \<Gamma>) (auto simp: tyvrs_vrs_prm_simp)

lemma closed_in_eqvt'[eqvt]:
  fixes pi::"vrs prm"
  assumes a: "S closed_in \<Gamma>" 
  shows "(pi\<bullet>S) closed_in (pi\<bullet>\<Gamma>)"
  using assms closed_in_def ty_dom_vrs_prm_simp ty_vrs_prm_simp by force

lemma fresh_vrs_of: 
  fixes x::"vrs"
  shows "x\<sharp>vrs_of b = x\<sharp>b"
  by (nominal_induct b rule: binding.strong_induct)
    (simp_all add: fresh_singleton fresh_set_empty ty_vrs_fresh fresh_atm)

lemma fresh_trm_dom: 
  fixes x::"vrs"
  shows "x\<sharp> trm_dom \<Gamma> = x\<sharp>\<Gamma>"
  by (induct \<Gamma>)
    (simp_all add: fresh_list_cons
     fresh_fin_union [OF pt_vrs_inst at_vrs_inst fs_vrs_inst]
     finite_doms finite_vrs fresh_vrs_of)

lemma closed_in_fresh: "(X::tyvrs) \<sharp> ty_dom \<Gamma> \<Longrightarrow> T closed_in \<Gamma> \<Longrightarrow> X \<sharp> T"
  by (auto simp: closed_in_def fresh_def ty_dom_supp)

text \<open>Now validity of a context is a straightforward inductive definition.\<close>
  
inductive
  valid_rel :: "env \<Rightarrow> bool" (\<open>\<turnstile> _ ok\<close> [100] 100)
where
  valid_nil[simp]:   "\<turnstile> [] ok"
| valid_consT[simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; X\<sharp>(ty_dom  \<Gamma>); T closed_in \<Gamma>\<rbrakk>  \<Longrightarrow>  \<turnstile> (TVarB X T#\<Gamma>) ok"
| valid_cons [simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; x\<sharp>(trm_dom \<Gamma>); T closed_in \<Gamma>\<rbrakk>  \<Longrightarrow>  \<turnstile> (VarB  x T#\<Gamma>) ok"

equivariance valid_rel

declare binding.inject [simp add]
declare trm.inject     [simp add]

inductive_cases validE[elim]: 
  "\<turnstile> (TVarB X T#\<Gamma>) ok" 
  "\<turnstile> (VarB  x T#\<Gamma>) ok" 
  "\<turnstile> (b#\<Gamma>) ok" 

declare binding.inject [simp del]
declare trm.inject     [simp del]

lemma validE_append:
  assumes a: "\<turnstile> (\<Delta>@\<Gamma>) ok" 
  shows "\<turnstile> \<Gamma> ok"
  using a 
proof (induct \<Delta>)
  case (Cons a \<Gamma>')
  then show ?case 
    by (nominal_induct a rule:binding.strong_induct) auto
qed (auto)

lemma replace_type:
  assumes a: "\<turnstile> (\<Delta>@(TVarB X T)#\<Gamma>) ok"
  and     b: "S closed_in \<Gamma>"
  shows "\<turnstile> (\<Delta>@(TVarB X S)#\<Gamma>) ok"
using a b
proof(induct \<Delta>)
  case Nil
  then show ?case by (auto intro: valid_cons simp add: doms_append closed_in_def)
next
  case (Cons a \<Gamma>')
  then show ?case 
    by (nominal_induct a rule:binding.strong_induct)
       (auto intro!: valid_cons simp add: doms_append closed_in_def)
qed

text \<open>Well-formed contexts have a unique type-binding for a type-variable.\<close> 

lemma uniqueness_of_ctxt:
  fixes \<Gamma>::"env"
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "(TVarB X T)\<in>set \<Gamma>"
  and     c: "(TVarB X S)\<in>set \<Gamma>"
  shows "T=S"
using a b c
proof (induct)
  case (valid_consT \<Gamma> X' T')
  moreover
  { fix \<Gamma>'::"env"
    assume a: "X'\<sharp>(ty_dom \<Gamma>')" 
    have "\<not>(\<exists>T.(TVarB X' T)\<in>(set \<Gamma>'))" using a 
    proof (induct \<Gamma>')
      case (Cons Y \<Gamma>')
      thus "\<not> (\<exists>T.(TVarB X' T)\<in>set(Y#\<Gamma>'))"
        by (simp add:  fresh_ty_dom_cons 
                       fresh_fin_union[OF pt_tyvrs_inst  at_tyvrs_inst fs_tyvrs_inst]  
                       finite_vrs finite_doms, 
            auto simp: fresh_atm fresh_singleton)
    qed (simp)
  }
  ultimately show "T=S" by (auto simp: binding.inject)
qed (auto)

lemma uniqueness_of_ctxt':
  fixes \<Gamma>::"env"
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "(VarB x T)\<in>set \<Gamma>"
  and     c: "(VarB x S)\<in>set \<Gamma>"
  shows "T=S"
using a b c
proof (induct)
  case (valid_cons \<Gamma> x' T')
  moreover
  { fix \<Gamma>'::"env"
    assume a: "x'\<sharp>(trm_dom \<Gamma>')" 
    have "\<not>(\<exists>T.(VarB x' T)\<in>(set \<Gamma>'))" using a 
    proof (induct \<Gamma>')
      case (Cons y \<Gamma>')
      thus "\<not> (\<exists>T.(VarB x' T)\<in>set(y#\<Gamma>'))" 
        by (simp add:  fresh_fin_union[OF pt_vrs_inst  at_vrs_inst fs_vrs_inst]  
                       finite_vrs finite_doms, 
            auto simp: fresh_atm fresh_singleton)
    qed (simp)
  }
  ultimately show "T=S" by (auto simp: binding.inject)
qed (auto)

section \<open>Size and Capture-Avoiding Substitution for Types\<close>

nominal_primrec
  size_ty :: "ty \<Rightarrow> nat"
where
  "size_ty (Tvar X) = 1"
| "size_ty (Top) = 1"
| "size_ty (T1 \<rightarrow> T2) = (size_ty T1) + (size_ty T2) + 1"
| "X \<sharp> T1 \<Longrightarrow> size_ty (\<forall>X<:T1. T2) = (size_ty T1) + (size_ty T2) + 1"
  by (finite_guess | fresh_guess | simp)+

nominal_primrec
  subst_ty :: "ty \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> ty" (\<open>_[_ \<leadsto> _]\<^sub>\<tau>\<close> [300, 0, 0] 300)
where
  "(Tvar X)[Y \<leadsto> T]\<^sub>\<tau> = (if X=Y then T else Tvar X)"
| "(Top)[Y \<leadsto> T]\<^sub>\<tau> = Top"
| "(T\<^sub>1 \<rightarrow> T\<^sub>2)[Y \<leadsto> T]\<^sub>\<tau> = T\<^sub>1[Y \<leadsto> T]\<^sub>\<tau> \<rightarrow> T\<^sub>2[Y \<leadsto> T]\<^sub>\<tau>"
| "X\<sharp>(Y,T,T\<^sub>1) \<Longrightarrow> (\<forall>X<:T\<^sub>1. T\<^sub>2)[Y \<leadsto> T]\<^sub>\<tau> = (\<forall>X<:T\<^sub>1[Y \<leadsto> T]\<^sub>\<tau>. T\<^sub>2[Y \<leadsto> T]\<^sub>\<tau>)"
  by (finite_guess | fresh_guess | simp add: abs_fresh)+

lemma subst_eqvt[eqvt]:
  fixes pi::"tyvrs prm" 
  and   T::"ty"
  shows "pi\<bullet>(T[X \<leadsto> T']\<^sub>\<tau>) = (pi\<bullet>T)[(pi\<bullet>X) \<leadsto> (pi\<bullet>T')]\<^sub>\<tau>"
  by (nominal_induct T avoiding: X T' rule: ty.strong_induct)
     (perm_simp add: fresh_bij)+

lemma subst_eqvt'[eqvt]:
  fixes pi::"vrs prm" 
  and   T::"ty"
  shows "pi\<bullet>(T[X \<leadsto> T']\<^sub>\<tau>) = (pi\<bullet>T)[(pi\<bullet>X) \<leadsto> (pi\<bullet>T')]\<^sub>\<tau>"
  by (nominal_induct T avoiding: X T' rule: ty.strong_induct)
     (perm_simp add: fresh_left)+

lemma type_subst_fresh:
  fixes X::"tyvrs"
  assumes "X\<sharp>T" and "X\<sharp>P"
  shows   "X\<sharp>T[Y \<leadsto> P]\<^sub>\<tau>"
  using assms
  by (nominal_induct T avoiding: X Y P rule:ty.strong_induct)
    (auto simp: abs_fresh)

lemma fresh_type_subst_fresh:
  assumes "X\<sharp>T'"
  shows "X\<sharp>T[X \<leadsto> T']\<^sub>\<tau>"
  using assms 
  by (nominal_induct T avoiding: X T' rule: ty.strong_induct)
     (auto simp: fresh_atm abs_fresh) 

lemma type_subst_identity: 
  "X\<sharp>T \<Longrightarrow> T[X \<leadsto> U]\<^sub>\<tau> = T"
  by (nominal_induct T avoiding: X U rule: ty.strong_induct)
    (simp_all add: fresh_atm abs_fresh)

lemma type_substitution_lemma:  
  "X \<noteq> Y \<Longrightarrow> X\<sharp>L \<Longrightarrow> M[X \<leadsto> N]\<^sub>\<tau>[Y \<leadsto> L]\<^sub>\<tau> = M[Y \<leadsto> L]\<^sub>\<tau>[X \<leadsto> N[Y \<leadsto> L]\<^sub>\<tau>]\<^sub>\<tau>"
  by (nominal_induct M avoiding: X Y N L rule: ty.strong_induct)
    (auto simp: type_subst_fresh type_subst_identity)

lemma type_subst_rename:
  "Y\<sharp>T \<Longrightarrow> ([(Y,X)]\<bullet>T)[Y \<leadsto> U]\<^sub>\<tau> = T[X \<leadsto> U]\<^sub>\<tau>"
  by (nominal_induct T avoiding: X Y U rule: ty.strong_induct)
    (simp_all add: fresh_atm calc_atm abs_fresh fresh_aux)

nominal_primrec
  subst_tyb :: "binding \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> binding" (\<open>_[_ \<leadsto> _]\<^sub>b\<close> [100,100,100] 100)
where
  "(TVarB X U)[Y \<leadsto> T]\<^sub>b = TVarB X (U[Y \<leadsto> T]\<^sub>\<tau>)"
| "(VarB  X U)[Y \<leadsto> T]\<^sub>b =  VarB X (U[Y \<leadsto> T]\<^sub>\<tau>)"
by auto

lemma binding_subst_fresh:
  fixes X::"tyvrs"
  assumes "X\<sharp>a"
  and     "X\<sharp>P"
  shows "X\<sharp>a[Y \<leadsto> P]\<^sub>b"
using assms
by (nominal_induct a rule: binding.strong_induct)
   (auto simp: type_subst_fresh)

lemma binding_subst_identity: 
  shows "X\<sharp>B \<Longrightarrow> B[X \<leadsto> U]\<^sub>b = B"
by (induct B rule: binding.induct)
   (simp_all add: fresh_atm type_subst_identity)

primrec subst_tyc :: "env \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> env" (\<open>_[_ \<leadsto> _]\<^sub>e\<close> [100,100,100] 100) where
  "([])[Y \<leadsto> T]\<^sub>e= []"
| "(B#\<Gamma>)[Y \<leadsto> T]\<^sub>e = (B[Y \<leadsto> T]\<^sub>b)#(\<Gamma>[Y \<leadsto> T]\<^sub>e)"

lemma ctxt_subst_fresh':
  fixes X::"tyvrs"
  assumes "X\<sharp>\<Gamma>"
  and     "X\<sharp>P"
  shows   "X\<sharp>\<Gamma>[Y \<leadsto> P]\<^sub>e"
using assms
by (induct \<Gamma>)
   (auto simp: fresh_list_cons binding_subst_fresh)

lemma ctxt_subst_mem_TVarB: "TVarB X T \<in> set \<Gamma> \<Longrightarrow> TVarB X (T[Y \<leadsto> U]\<^sub>\<tau>) \<in> set (\<Gamma>[Y \<leadsto> U]\<^sub>e)"
  by (induct \<Gamma>) auto

lemma ctxt_subst_mem_VarB: "VarB x T \<in> set \<Gamma> \<Longrightarrow> VarB x (T[Y \<leadsto> U]\<^sub>\<tau>) \<in> set (\<Gamma>[Y \<leadsto> U]\<^sub>e)"
  by (induct \<Gamma>) auto

lemma ctxt_subst_identity: "X\<sharp>\<Gamma> \<Longrightarrow> \<Gamma>[X \<leadsto> U]\<^sub>e = \<Gamma>"
  by (induct \<Gamma>) (simp_all add: fresh_list_cons binding_subst_identity)

lemma ctxt_subst_append: "(\<Delta> @ \<Gamma>)[X \<leadsto> T]\<^sub>e = \<Delta>[X \<leadsto> T]\<^sub>e @ \<Gamma>[X \<leadsto> T]\<^sub>e"
  by (induct \<Delta>) simp_all

nominal_primrec
   subst_trm :: "trm \<Rightarrow> vrs \<Rightarrow> trm \<Rightarrow> trm"  (\<open>_[_ \<leadsto> _]\<close> [300, 0, 0] 300)
where
  "(Var x)[y \<leadsto> t'] = (if x=y then t' else (Var x))"
| "(t1 \<cdot> t2)[y \<leadsto> t'] = t1[y \<leadsto> t'] \<cdot> t2[y \<leadsto> t']"
| "(t \<cdot>\<^sub>\<tau> T)[y \<leadsto> t'] = t[y \<leadsto> t'] \<cdot>\<^sub>\<tau> T"
| "X\<sharp>(T,t') \<Longrightarrow> (\<lambda>X<:T. t)[y \<leadsto> t'] = (\<lambda>X<:T. t[y \<leadsto> t'])" 
| "x\<sharp>(y,t') \<Longrightarrow> (\<lambda>x:T. t)[y \<leadsto> t'] = (\<lambda>x:T. t[y \<leadsto> t'])"
  by (finite_guess | simp add: abs_fresh | fresh_guess add: ty_vrs_fresh abs_fresh)+

lemma subst_trm_fresh_tyvar:
  fixes X::"tyvrs"
  shows "X\<sharp>t \<Longrightarrow> X\<sharp>u \<Longrightarrow> X\<sharp>t[x \<leadsto> u]"
  by (nominal_induct t avoiding: x u rule: trm.strong_induct)
    (auto simp: abs_fresh)

lemma subst_trm_fresh_var: 
  "x\<sharp>u \<Longrightarrow> x\<sharp>t[x \<leadsto> u]"
  by (nominal_induct t avoiding: x u rule: trm.strong_induct)
    (simp_all add: abs_fresh fresh_atm ty_vrs_fresh)

lemma subst_trm_eqvt[eqvt]:
  fixes pi::"tyvrs prm" 
  and   t::"trm"
  shows "pi\<bullet>(t[x \<leadsto> u]) = (pi\<bullet>t)[(pi\<bullet>x) \<leadsto> (pi\<bullet>u)]"
  by (nominal_induct t avoiding: x u rule: trm.strong_induct)
     (perm_simp add: fresh_left)+

lemma subst_trm_eqvt'[eqvt]:
  fixes pi::"vrs prm" 
  and   t::"trm"
  shows "pi\<bullet>(t[x \<leadsto> u]) = (pi\<bullet>t)[(pi\<bullet>x) \<leadsto> (pi\<bullet>u)]"
  by (nominal_induct t avoiding: x u rule: trm.strong_induct)
     (perm_simp add: fresh_left)+

lemma subst_trm_rename:
  "y\<sharp>t \<Longrightarrow> ([(y, x)] \<bullet> t)[y \<leadsto> u] = t[x \<leadsto> u]"
  by (nominal_induct t avoiding: x y u rule: trm.strong_induct)
    (simp_all add: fresh_atm calc_atm abs_fresh fresh_aux ty_vrs_fresh perm_fresh_fresh)

nominal_primrec (freshness_context: "T2::ty")
  subst_trm_ty :: "trm \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> trm"  (\<open>_[_ \<leadsto>\<^sub>\<tau> _]\<close> [300, 0, 0] 300)
where
  "(Var x)[Y \<leadsto>\<^sub>\<tau> T2] = Var x"
| "(t1 \<cdot> t2)[Y \<leadsto>\<^sub>\<tau> T2] = t1[Y \<leadsto>\<^sub>\<tau> T2] \<cdot> t2[Y \<leadsto>\<^sub>\<tau> T2]"
| "(t1 \<cdot>\<^sub>\<tau> T)[Y \<leadsto>\<^sub>\<tau> T2] = t1[Y \<leadsto>\<^sub>\<tau> T2] \<cdot>\<^sub>\<tau> T[Y \<leadsto> T2]\<^sub>\<tau>"
| "X\<sharp>(Y,T,T2) \<Longrightarrow> (\<lambda>X<:T. t)[Y \<leadsto>\<^sub>\<tau> T2] = (\<lambda>X<:T[Y \<leadsto> T2]\<^sub>\<tau>. t[Y \<leadsto>\<^sub>\<tau> T2])" 
| "(\<lambda>x:T. t)[Y \<leadsto>\<^sub>\<tau> T2] = (\<lambda>x:T[Y \<leadsto> T2]\<^sub>\<tau>. t[Y \<leadsto>\<^sub>\<tau> T2])"
apply(finite_guess | simp add: abs_fresh ty_vrs_fresh type_subst_fresh)+
apply(fresh_guess add: ty_vrs_fresh abs_fresh)+
done

lemma subst_trm_ty_fresh:
  fixes X::"tyvrs"
  shows "X\<sharp>t \<Longrightarrow> X\<sharp>T \<Longrightarrow> X\<sharp>t[Y \<leadsto>\<^sub>\<tau> T]"
  by (nominal_induct t avoiding: Y T rule: trm.strong_induct)
    (auto simp: abs_fresh type_subst_fresh)

lemma subst_trm_ty_fresh':
  "X\<sharp>T \<Longrightarrow> X\<sharp>t[X \<leadsto>\<^sub>\<tau> T]"
  by (nominal_induct t avoiding: X T rule: trm.strong_induct)
    (simp_all add: abs_fresh fresh_type_subst_fresh fresh_atm)

lemma subst_trm_ty_eqvt[eqvt]:
  fixes pi::"tyvrs prm" 
  and   t::"trm"
  shows "pi\<bullet>(t[X \<leadsto>\<^sub>\<tau> T]) = (pi\<bullet>t)[(pi\<bullet>X) \<leadsto>\<^sub>\<tau> (pi\<bullet>T)]"
  by (nominal_induct t avoiding: X T rule: trm.strong_induct)
     (perm_simp add: fresh_bij subst_eqvt)+

lemma subst_trm_ty_eqvt'[eqvt]:
  fixes pi::"vrs prm" 
  and   t::"trm"
  shows "pi\<bullet>(t[X \<leadsto>\<^sub>\<tau> T]) = (pi\<bullet>t)[(pi\<bullet>X) \<leadsto>\<^sub>\<tau> (pi\<bullet>T)]"
  by (nominal_induct t avoiding: X T rule: trm.strong_induct)
     (perm_simp add: fresh_left subst_eqvt')+

lemma subst_trm_ty_rename:
  "Y\<sharp>t \<Longrightarrow> ([(Y, X)] \<bullet> t)[Y \<leadsto>\<^sub>\<tau> U] = t[X \<leadsto>\<^sub>\<tau> U]"
  by (nominal_induct t avoiding: X Y U rule: trm.strong_induct)
    (simp_all add: fresh_atm calc_atm abs_fresh fresh_aux type_subst_rename)

section \<open>Subtyping-Relation\<close>

text \<open>The definition for the subtyping-relation follows quite closely what is written 
  in the POPLmark-paper, except for the premises dealing with well-formed contexts and 
  the freshness constraint \<^term>\<open>X\<sharp>\<Gamma>\<close> in the \<open>S_Forall\<close>-rule. (The freshness
  constraint is specific to the \emph{nominal approach}. Note, however, that the constraint
  does \emph{not} make the subtyping-relation ``partial"\ldots because we work over
  $\alpha$-equivalence classes.)\<close>

inductive 
  subtype_of :: "env \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"   (\<open>_\<turnstile>_<:_\<close> [100,100,100] 100)
where
  SA_Top[intro]:    "\<lbrakk>\<turnstile> \<Gamma> ok; S closed_in \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar[intro]:   "\<lbrakk>\<turnstile> \<Gamma> ok; X \<in> ty_dom \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Tvar X <: Tvar X"
| SA_trans_TVar[intro]:    "\<lbrakk>(TVarB X S) \<in> set \<Gamma>; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Tvar X) <: T"
| SA_arrow[intro]:  "\<lbrakk>\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (S\<^sub>1 \<rightarrow> S\<^sub>2) <: (T\<^sub>1 \<rightarrow> T\<^sub>2)" 
| SA_all[intro]: "\<lbrakk>\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1; ((TVarB X T\<^sub>1)#\<Gamma>) \<turnstile> S\<^sub>2 <: T\<^sub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: (\<forall>X<:T\<^sub>1. T\<^sub>2)"

lemma subtype_implies_ok:
  fixes X::"tyvrs"
  assumes a: "\<Gamma> \<turnstile> S <: T"
  shows "\<turnstile> \<Gamma> ok"  
using a by (induct) (auto)

lemma subtype_implies_closed:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  shows "S closed_in \<Gamma> \<and> T closed_in \<Gamma>"
using a
proof (induct)
  case (SA_Top \<Gamma> S)
  have "Top closed_in \<Gamma>" by (simp add: closed_in_def ty.supp)
  moreover
  have "S closed_in \<Gamma>" by fact
  ultimately show "S closed_in \<Gamma> \<and> Top closed_in \<Gamma>" by simp
next
  case (SA_trans_TVar X S \<Gamma> T)
  have "(TVarB X S)\<in>set \<Gamma>" by fact
  hence "X \<in> ty_dom \<Gamma>" by (rule ty_dom_inclusion)
  hence "(Tvar X) closed_in \<Gamma>" by (simp add: closed_in_def ty.supp supp_atm)
  moreover
  have "S closed_in \<Gamma> \<and> T closed_in \<Gamma>" by fact
  hence "T closed_in \<Gamma>" by force
  ultimately show "(Tvar X) closed_in \<Gamma> \<and> T closed_in \<Gamma>" by simp
qed (auto simp: closed_in_def ty.supp supp_atm abs_supp)

lemma subtype_implies_fresh:
  fixes X::"tyvrs"
  assumes a1: "\<Gamma> \<turnstile> S <: T"
  and     a2: "X\<sharp>\<Gamma>"
  shows "X\<sharp>S \<and> X\<sharp>T"  
proof -
  from a1 have "\<turnstile> \<Gamma> ok" by (rule subtype_implies_ok)
  with a2 have "X\<sharp>ty_dom(\<Gamma>)" by (simp add: fresh_dom)
  moreover
  from a1 have "S closed_in \<Gamma> \<and> T closed_in \<Gamma>" by (rule subtype_implies_closed)
  hence "supp S \<subseteq> ((supp (ty_dom \<Gamma>))::tyvrs set)" 
    and "supp T \<subseteq> ((supp (ty_dom \<Gamma>))::tyvrs set)" by (simp_all add: ty_dom_supp closed_in_def)
  ultimately show "X\<sharp>S \<and> X\<sharp>T" by (force simp: supp_prod fresh_def)
qed

lemma valid_ty_dom_fresh:
  fixes X::"tyvrs"
  assumes valid: "\<turnstile> \<Gamma> ok"
  shows "X\<sharp>(ty_dom \<Gamma>) = X\<sharp>\<Gamma>" 
  using valid
proof induct
  case valid_nil
  then show ?case by auto
next
  case (valid_consT \<Gamma> X T)
  then show ?case
    by (auto simp: fresh_list_cons closed_in_fresh
     fresh_fin_insert [OF pt_tyvrs_inst at_tyvrs_inst fs_tyvrs_inst] finite_doms)
next
  case (valid_cons \<Gamma> x T)
  then show ?case
    using fresh_atm by (auto simp: fresh_list_cons closed_in_fresh)
qed

equivariance subtype_of

nominal_inductive subtype_of
  apply (simp_all add: abs_fresh)
  apply (fastforce simp: valid_ty_dom_fresh dest: subtype_implies_ok)
  apply (force simp: closed_in_fresh dest: subtype_implies_closed subtype_implies_ok)+
  done

section \<open>Reflexivity of Subtyping\<close>

lemma subtype_reflexivity:
  assumes a: "\<turnstile> \<Gamma> ok"
  and b: "T closed_in \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
using a b
proof(nominal_induct T avoiding: \<Gamma> rule: ty.strong_induct)
  case (Forall X T\<^sub>1 T\<^sub>2)
  have ih_T\<^sub>1: "\<And>\<Gamma>. \<lbrakk>\<turnstile> \<Gamma> ok; T\<^sub>1 closed_in \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>1 <: T\<^sub>1" by fact 
  have ih_T\<^sub>2: "\<And>\<Gamma>. \<lbrakk>\<turnstile> \<Gamma> ok; T\<^sub>2 closed_in \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>2" by fact
  have fresh_cond: "X\<sharp>\<Gamma>" by fact
  hence fresh_ty_dom: "X\<sharp>(ty_dom \<Gamma>)" by (simp add: fresh_dom)
  have "(\<forall>X<:T\<^sub>2. T\<^sub>1) closed_in \<Gamma>" by fact
  hence closed\<^sub>T2: "T\<^sub>2 closed_in \<Gamma>" and closed\<^sub>T1: "T\<^sub>1 closed_in ((TVarB  X T\<^sub>2)#\<Gamma>)" 
    by (auto simp: closed_in_def ty.supp abs_supp)
  have ok: "\<turnstile> \<Gamma> ok" by fact  
  hence ok': "\<turnstile> ((TVarB X T\<^sub>2)#\<Gamma>) ok" using closed\<^sub>T2 fresh_ty_dom by simp
  have "\<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>2" using ih_T\<^sub>2 closed\<^sub>T2 ok by simp
  moreover
  have "((TVarB X T\<^sub>2)#\<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>1" using ih_T\<^sub>1 closed\<^sub>T1 ok' by simp
  ultimately show "\<Gamma> \<turnstile> (\<forall>X<:T\<^sub>2. T\<^sub>1) <: (\<forall>X<:T\<^sub>2. T\<^sub>1)" using fresh_cond 
    by (simp add: subtype_of.SA_all)
qed (auto simp: closed_in_def ty.supp supp_atm)

lemma subtype_reflexivity_semiautomated:
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "T closed_in \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
using a b
apply(nominal_induct T avoiding: \<Gamma> rule: ty.strong_induct)
apply(auto simp: ty.supp abs_supp supp_atm closed_in_def)
  \<comment> \<open>Too bad that this instantiation cannot be found automatically by
  \isakeyword{auto}; \isakeyword{blast} would find it if we had not used 
  an explicit definition for \<open>closed_in_def\<close>.\<close>
apply(drule_tac x="(TVarB tyvrs ty2)#\<Gamma>" in meta_spec)
apply(force dest: fresh_dom simp add: closed_in_def)
done

section \<open>Weakening\<close>

text \<open>In order to prove weakening we introduce the notion of a type-context extending 
  another. This generalization seems to make the proof for weakening to be
  smoother than if we had strictly adhered to the version in the POPLmark-paper.\<close>

definition extends :: "env \<Rightarrow> env \<Rightarrow> bool" (\<open>_ extends _\<close> [100,100] 100) where
  "\<Delta> extends \<Gamma> \<equiv> \<forall>X Q. (TVarB X Q)\<in>set \<Gamma> \<longrightarrow> (TVarB X Q)\<in>set \<Delta>"

lemma extends_ty_dom:
  assumes "\<Delta> extends \<Gamma>"
  shows "ty_dom \<Gamma> \<subseteq> ty_dom \<Delta>"
  using assms
  by (meson extends_def subsetI ty_dom_existence ty_dom_inclusion) 

lemma extends_closed:
  assumes "T closed_in \<Gamma>" and "\<Delta> extends \<Gamma>"
  shows "T closed_in \<Delta>"
  by (meson assms closed_in_def extends_ty_dom order.trans)

lemma extends_memb:
  assumes a: "\<Delta> extends \<Gamma>"
  and b: "(TVarB X T) \<in> set \<Gamma>"
  shows "(TVarB X T) \<in> set \<Delta>"
  using a b by (simp add: extends_def)

lemma weakening:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and b: "\<turnstile> \<Delta> ok"
  and c: "\<Delta> extends \<Gamma>"
  shows "\<Delta> \<turnstile> S <: T"
  using a b c 
proof (nominal_induct \<Gamma> S T avoiding: \<Delta> rule: subtype_of.strong_induct)
  case (SA_Top \<Gamma> S) 
  have lh_drv_prem: "S closed_in \<Gamma>" by fact
  have "\<turnstile> \<Delta> ok" by fact
  moreover
  have "\<Delta> extends \<Gamma>" by fact
  hence "S closed_in \<Delta>" using lh_drv_prem by (simp only: extends_closed)
  ultimately show "\<Delta> \<turnstile> S <: Top" by force
next 
  case (SA_trans_TVar X S \<Gamma> T)
  have lh_drv_prem: "(TVarB X S) \<in> set \<Gamma>" by fact
  have ih: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> S <: T" by fact
  have ok: "\<turnstile> \<Delta> ok" by fact
  have extends: "\<Delta> extends \<Gamma>" by fact
  have "(TVarB X S) \<in> set \<Delta>" using lh_drv_prem extends by (simp only: extends_memb)
  moreover
  have "\<Delta> \<turnstile> S <: T" using ok extends ih by simp
  ultimately show "\<Delta> \<turnstile> Tvar X <: T" using ok by force
next
  case (SA_refl_TVar \<Gamma> X)
  have lh_drv_prem: "X \<in> ty_dom \<Gamma>" by fact
  have "\<turnstile> \<Delta> ok" by fact
  moreover
  have "\<Delta> extends \<Gamma>" by fact
  hence "X \<in> ty_dom \<Delta>" using lh_drv_prem by (force dest: extends_ty_dom)
  ultimately show "\<Delta> \<turnstile> Tvar X <: Tvar X" by force
next 
  case (SA_arrow \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2) thus "\<Delta> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2" by blast
next
  case (SA_all \<Gamma> T\<^sub>1 S\<^sub>1 X S\<^sub>2 T\<^sub>2)
  have fresh_cond: "X\<sharp>\<Delta>" by fact
  hence fresh_dom: "X\<sharp>(ty_dom \<Delta>)" by (simp add: fresh_dom)
  have ih\<^sub>1: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> T\<^sub>1 <: S\<^sub>1" by fact
  have ih\<^sub>2: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends ((TVarB X T\<^sub>1)#\<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> S\<^sub>2 <: T\<^sub>2" by fact
  have lh_drv_prem: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1" by fact
  hence closed\<^sub>T1: "T\<^sub>1 closed_in \<Gamma>" by (simp add: subtype_implies_closed) 
  have ok: "\<turnstile> \<Delta> ok" by fact
  have ext: "\<Delta> extends \<Gamma>" by fact
  have "T\<^sub>1 closed_in \<Delta>" using ext closed\<^sub>T1 by (simp only: extends_closed)
  hence "\<turnstile> ((TVarB X T\<^sub>1)#\<Delta>) ok" using fresh_dom ok by force   
  moreover 
  have "((TVarB X T\<^sub>1)#\<Delta>) extends ((TVarB X T\<^sub>1)#\<Gamma>)" using ext by (force simp: extends_def)
  ultimately have "((TVarB X T\<^sub>1)#\<Delta>) \<turnstile> S\<^sub>2 <: T\<^sub>2" using ih\<^sub>2 by simp
  moreover
  have "\<Delta> \<turnstile> T\<^sub>1 <: S\<^sub>1" using ok ext ih\<^sub>1 by simp 
  ultimately show "\<Delta> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: (\<forall>X<:T\<^sub>1. T\<^sub>2)" using ok by (force intro: SA_all)
qed

text \<open>In fact all ``non-binding" cases can be solved automatically:\<close>

lemma weakening_more_automated:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and b: "\<turnstile> \<Delta> ok"
  and c: "\<Delta> extends \<Gamma>"
  shows "\<Delta> \<turnstile> S <: T"
  using a b c 
proof (nominal_induct \<Gamma> S T avoiding: \<Delta> rule: subtype_of.strong_induct)
  case (SA_all \<Gamma> T\<^sub>1 S\<^sub>1 X S\<^sub>2 T\<^sub>2)
  have fresh_cond: "X\<sharp>\<Delta>" by fact
  hence fresh_dom: "X\<sharp>(ty_dom \<Delta>)" by (simp add: fresh_dom)
  have ih\<^sub>1: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> T\<^sub>1 <: S\<^sub>1" by fact
  have ih\<^sub>2: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends ((TVarB X T\<^sub>1)#\<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> S\<^sub>2 <: T\<^sub>2" by fact
  have lh_drv_prem: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1" by fact
  hence closed\<^sub>T1: "T\<^sub>1 closed_in \<Gamma>" by (simp add: subtype_implies_closed) 
  have ok: "\<turnstile> \<Delta> ok" by fact
  have ext: "\<Delta> extends \<Gamma>" by fact
  have "T\<^sub>1 closed_in \<Delta>" using ext closed\<^sub>T1 by (simp only: extends_closed)
  hence "\<turnstile> ((TVarB X T\<^sub>1)#\<Delta>) ok" using fresh_dom ok by force   
  moreover
  have "((TVarB X T\<^sub>1)#\<Delta>) extends ((TVarB X T\<^sub>1)#\<Gamma>)" using ext by (force simp: extends_def)
  ultimately have "((TVarB X T\<^sub>1)#\<Delta>) \<turnstile> S\<^sub>2 <: T\<^sub>2" using ih\<^sub>2 by simp
  moreover
  have "\<Delta> \<turnstile> T\<^sub>1 <: S\<^sub>1" using ok ext ih\<^sub>1 by simp 
  ultimately show "\<Delta> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: (\<forall>X<:T\<^sub>1. T\<^sub>2)" using ok by (force intro: SA_all)
qed (blast intro: extends_closed extends_memb dest: extends_ty_dom)+

section \<open>Transitivity and Narrowing\<close>

text \<open>Some inversion lemmas that are needed in the transitivity and narrowing proof.\<close>

declare ty.inject [simp add]

inductive_cases S_TopE: "\<Gamma> \<turnstile> Top <: T"
inductive_cases S_ArrowE_left: "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T" 

declare ty.inject [simp del]

lemma S_ForallE_left:
  shows "\<lbrakk>\<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: T; X\<sharp>\<Gamma>; X\<sharp>S\<^sub>1; X\<sharp>T\<rbrakk>
         \<Longrightarrow> T = Top \<or> (\<exists>T\<^sub>1 T\<^sub>2. T = (\<forall>X<:T\<^sub>1. T\<^sub>2) \<and> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<and> ((TVarB X T\<^sub>1)#\<Gamma>) \<turnstile> S\<^sub>2 <: T\<^sub>2)"
  using subtype_of.strong_cases[where X="X"]
  by(force simp: abs_fresh ty.inject alpha)

text \<open>Next we prove the transitivity and narrowing for the subtyping-relation. 
The POPLmark-paper says the following:

\begin{quote}
\begin{lemma}[Transitivity and Narrowing] \
\begin{enumerate}
\item If \<^term>\<open>\<Gamma> \<turnstile> S<:Q\<close> and \<^term>\<open>\<Gamma> \<turnstile> Q<:T\<close>, then \<^term>\<open>\<Gamma> \<turnstile> S<:T\<close>.
\item If \<open>\<Gamma>,X<:Q,\<Delta> \<turnstile> M<:N\<close> and \<^term>\<open>\<Gamma> \<turnstile> P<:Q\<close> then \<open>\<Gamma>,X<:P,\<Delta> \<turnstile> M<:N\<close>.
\end{enumerate}
\end{lemma}

The two parts are proved simultaneously, by induction on the size
of \<^term>\<open>Q\<close>.  The argument for part (2) assumes that part (1) has 
been established already for the \<^term>\<open>Q\<close> in question; part (1) uses 
part (2) only for strictly smaller \<^term>\<open>Q\<close>.
\end{quote}

For the induction on the size of \<^term>\<open>Q\<close>, we use the induction-rule 
\<open>measure_induct_rule\<close>:

\begin{center}
@{thm measure_induct_rule[of "size_ty",no_vars]}
\end{center}

That means in order to show a property \<^term>\<open>P a\<close> for all \<^term>\<open>a\<close>, 
the induct-rule requires to prove that for all \<^term>\<open>x\<close> \<^term>\<open>P x\<close> holds using the 
assumption that for all \<^term>\<open>y\<close> whose size is strictly smaller than 
that of \<^term>\<open>x\<close> the property \<^term>\<open>P y\<close> holds.\<close>

lemma 
  shows subtype_transitivity: "\<Gamma>\<turnstile>S<:Q \<Longrightarrow> \<Gamma>\<turnstile>Q<:T \<Longrightarrow> \<Gamma>\<turnstile>S<:T" 
  and subtype_narrow: "(\<Delta>@[(TVarB X Q)]@\<Gamma>)\<turnstile>M<:N \<Longrightarrow> \<Gamma>\<turnstile>P<:Q \<Longrightarrow> (\<Delta>@[(TVarB X P)]@\<Gamma>)\<turnstile>M<:N"
proof (induct Q arbitrary: \<Gamma> S T \<Delta> X P M N taking: "size_ty" rule: measure_induct_rule)
  case (less Q)
  have IH_trans:  
    "\<And>Q' \<Gamma> S T. \<lbrakk>size_ty Q' < size_ty Q; \<Gamma>\<turnstile>S<:Q'; \<Gamma>\<turnstile>Q'<:T\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>S<:T" by fact
  have IH_narrow:
    "\<And>Q' \<Delta> \<Gamma> X M N P. \<lbrakk>size_ty Q' < size_ty Q; (\<Delta>@[(TVarB X Q')]@\<Gamma>)\<turnstile>M<:N; \<Gamma>\<turnstile>P<:Q'\<rbrakk> 
    \<Longrightarrow> (\<Delta>@[(TVarB X P)]@\<Gamma>)\<turnstile>M<:N" by fact

  { fix \<Gamma> S T
    have "\<lbrakk>\<Gamma> \<turnstile> S <: Q; \<Gamma> \<turnstile> Q <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T" 
    proof (induct \<Gamma> S Q\<equiv>Q rule: subtype_of.induct) 
      case (SA_Top \<Gamma> S) 
      then have rh_drv: "\<Gamma> \<turnstile> Top <: T" by simp
      then have T_inst: "T = Top" by (auto elim: S_TopE)
      from \<open>\<turnstile> \<Gamma> ok\<close> and \<open>S closed_in \<Gamma>\<close>
      have "\<Gamma> \<turnstile> S <: Top" by auto
      then show "\<Gamma> \<turnstile> S <: T" using T_inst by simp 
    next
      case (SA_trans_TVar Y U \<Gamma>) 
      then have IH_inner: "\<Gamma> \<turnstile> U <: T" by simp
      have "(TVarB Y U) \<in> set \<Gamma>" by fact
      with IH_inner show "\<Gamma> \<turnstile> Tvar Y <: T" by auto
    next
      case (SA_refl_TVar \<Gamma> X) 
      then show "\<Gamma> \<turnstile> Tvar X <: T" by simp
    next
      case (SA_arrow \<Gamma> Q\<^sub>1 S\<^sub>1 S\<^sub>2 Q\<^sub>2) 
      then have rh_drv: "\<Gamma> \<turnstile> Q\<^sub>1 \<rightarrow> Q\<^sub>2 <: T" by simp
      from \<open>Q\<^sub>1 \<rightarrow> Q\<^sub>2 = Q\<close> 
      have Q\<^sub>12_less: "size_ty Q\<^sub>1 < size_ty Q" "size_ty Q\<^sub>2 < size_ty Q" by auto
      have lh_drv_prm\<^sub>1: "\<Gamma> \<turnstile> Q\<^sub>1 <: S\<^sub>1" by fact
      have lh_drv_prm\<^sub>2: "\<Gamma> \<turnstile> S\<^sub>2 <: Q\<^sub>2" by fact      
      from rh_drv have "T=Top \<or> (\<exists>T\<^sub>1 T\<^sub>2. T=T\<^sub>1\<rightarrow>T\<^sub>2 \<and> \<Gamma>\<turnstile>T\<^sub>1<:Q\<^sub>1 \<and> \<Gamma>\<turnstile>Q\<^sub>2<:T\<^sub>2)" 
        by (auto elim: S_ArrowE_left)
      moreover
      have "S\<^sub>1 closed_in \<Gamma>" and "S\<^sub>2 closed_in \<Gamma>" 
        using lh_drv_prm\<^sub>1 lh_drv_prm\<^sub>2 by (simp_all add: subtype_implies_closed)
      hence "(S\<^sub>1 \<rightarrow> S\<^sub>2) closed_in \<Gamma>" by (simp add: closed_in_def ty.supp)
      moreover
      have "\<turnstile> \<Gamma> ok" using rh_drv by (rule subtype_implies_ok)
      moreover
      { assume "\<exists>T\<^sub>1 T\<^sub>2. T = T\<^sub>1\<rightarrow>T\<^sub>2 \<and> \<Gamma> \<turnstile> T\<^sub>1 <: Q\<^sub>1 \<and> \<Gamma> \<turnstile> Q\<^sub>2 <: T\<^sub>2"
        then obtain T\<^sub>1 T\<^sub>2 
          where T_inst: "T = T\<^sub>1 \<rightarrow> T\<^sub>2" 
          and   rh_drv_prm\<^sub>1: "\<Gamma> \<turnstile> T\<^sub>1 <: Q\<^sub>1"
          and   rh_drv_prm\<^sub>2: "\<Gamma> \<turnstile> Q\<^sub>2 <: T\<^sub>2" by force
        from IH_trans[of "Q\<^sub>1"] 
        have "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1" using Q\<^sub>12_less rh_drv_prm\<^sub>1 lh_drv_prm\<^sub>1 by simp 
        moreover
        from IH_trans[of "Q\<^sub>2"] 
        have "\<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2" using Q\<^sub>12_less rh_drv_prm\<^sub>2 lh_drv_prm\<^sub>2 by simp
        ultimately have "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2" by auto
        then have "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T" using T_inst by simp
      }
      ultimately show "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T" by blast
    next
      case (SA_all \<Gamma> Q\<^sub>1 S\<^sub>1 X S\<^sub>2 Q\<^sub>2) 
      then have rh_drv: "\<Gamma> \<turnstile> (\<forall>X<:Q\<^sub>1. Q\<^sub>2) <: T" by simp
      have lh_drv_prm\<^sub>1: "\<Gamma> \<turnstile> Q\<^sub>1 <: S\<^sub>1" by fact
      have lh_drv_prm\<^sub>2: "((TVarB X Q\<^sub>1)#\<Gamma>) \<turnstile> S\<^sub>2 <: Q\<^sub>2" by fact
      then have "X\<sharp>\<Gamma>" by (force dest: subtype_implies_ok simp add: valid_ty_dom_fresh)
      then have fresh_cond: "X\<sharp>\<Gamma>" "X\<sharp>Q\<^sub>1" "X\<sharp>T" using rh_drv lh_drv_prm\<^sub>1 
        by (simp_all add: subtype_implies_fresh)
      from rh_drv 
      have "T = Top \<or> 
          (\<exists>T\<^sub>1 T\<^sub>2. T = (\<forall>X<:T\<^sub>1. T\<^sub>2) \<and> \<Gamma> \<turnstile> T\<^sub>1 <: Q\<^sub>1 \<and> ((TVarB X T\<^sub>1)#\<Gamma>) \<turnstile> Q\<^sub>2 <: T\<^sub>2)" 
        using fresh_cond by (simp add: S_ForallE_left)
      moreover
      have "S\<^sub>1 closed_in \<Gamma>" and "S\<^sub>2 closed_in ((TVarB X Q\<^sub>1)#\<Gamma>)" 
        using lh_drv_prm\<^sub>1 lh_drv_prm\<^sub>2 by (simp_all add: subtype_implies_closed)
      then have "(\<forall>X<:S\<^sub>1. S\<^sub>2) closed_in \<Gamma>" by (force simp: closed_in_def ty.supp abs_supp)
      moreover
      have "\<turnstile> \<Gamma> ok" using rh_drv by (rule subtype_implies_ok)
      moreover
      { assume "\<exists>T\<^sub>1 T\<^sub>2. T=(\<forall>X<:T\<^sub>1. T\<^sub>2) \<and> \<Gamma>\<turnstile>T\<^sub>1<:Q\<^sub>1 \<and> ((TVarB X T\<^sub>1)#\<Gamma>)\<turnstile>Q\<^sub>2<:T\<^sub>2"
        then obtain T\<^sub>1 T\<^sub>2 
          where T_inst: "T = (\<forall>X<:T\<^sub>1. T\<^sub>2)" 
          and   rh_drv_prm\<^sub>1: "\<Gamma> \<turnstile> T\<^sub>1 <: Q\<^sub>1" 
          and   rh_drv_prm\<^sub>2:"((TVarB X T\<^sub>1)#\<Gamma>) \<turnstile> Q\<^sub>2 <: T\<^sub>2" by force
        have "(\<forall>X<:Q\<^sub>1. Q\<^sub>2) = Q" by fact 
        then have Q\<^sub>12_less: "size_ty Q\<^sub>1 < size_ty Q" "size_ty Q\<^sub>2 < size_ty Q" 
          using fresh_cond by auto
        from IH_trans[of "Q\<^sub>1"] 
        have "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1" using lh_drv_prm\<^sub>1 rh_drv_prm\<^sub>1 Q\<^sub>12_less by blast
        moreover
        from IH_narrow[of "Q\<^sub>1" "[]"] 
        have "((TVarB X T\<^sub>1)#\<Gamma>) \<turnstile> S\<^sub>2 <: Q\<^sub>2" using Q\<^sub>12_less lh_drv_prm\<^sub>2 rh_drv_prm\<^sub>1 by simp
        with IH_trans[of "Q\<^sub>2"] 
        have "((TVarB X T\<^sub>1)#\<Gamma>) \<turnstile> S\<^sub>2 <: T\<^sub>2" using Q\<^sub>12_less rh_drv_prm\<^sub>2 by simp
        ultimately have "\<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: (\<forall>X<:T\<^sub>1. T\<^sub>2)"
          using fresh_cond by (simp add: subtype_of.SA_all)
        hence "\<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: T" using T_inst by simp
      }
      ultimately show "\<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. S\<^sub>2) <: T" by blast
    qed
  } note transitivity_lemma = this  

  { \<comment> \<open>The transitivity proof is now by the auxiliary lemma.\<close>
    case 1 
    from \<open>\<Gamma> \<turnstile> S <: Q\<close> and \<open>\<Gamma> \<turnstile> Q <: T\<close>
    show "\<Gamma> \<turnstile> S <: T" by (rule transitivity_lemma) 
  next 
    case 2
    from \<open>(\<Delta>@[(TVarB X Q)]@\<Gamma>) \<turnstile> M <: N\<close> 
      and \<open>\<Gamma> \<turnstile> P<:Q\<close> 
    show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> M <: N" 
    proof (induct "\<Delta>@[(TVarB X Q)]@\<Gamma>" M N arbitrary: \<Gamma> X \<Delta> rule: subtype_of.induct) 
      case (SA_Top S \<Gamma> X \<Delta>)
      from \<open>\<Gamma> \<turnstile> P <: Q\<close>
      have "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      with \<open>\<turnstile> (\<Delta>@[(TVarB X Q)]@\<Gamma>) ok\<close> have "\<turnstile> (\<Delta>@[(TVarB X P)]@\<Gamma>) ok"
        by (simp add: replace_type)
      moreover
      from \<open>S closed_in (\<Delta>@[(TVarB X Q)]@\<Gamma>)\<close> have "S closed_in (\<Delta>@[(TVarB X P)]@\<Gamma>)" 
        by (simp add: closed_in_def doms_append)
      ultimately show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> S <: Top" by (simp add: subtype_of.SA_Top)
    next
      case (SA_trans_TVar Y S N \<Gamma> X \<Delta>) 
      then have IH_inner: "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> S <: N"
        and lh_drv_prm: "(TVarB Y S) \<in> set (\<Delta>@[(TVarB X Q)]@\<Gamma>)"
        and rh_drv: "\<Gamma> \<turnstile> P<:Q"
        and ok\<^sub>Q: "\<turnstile> (\<Delta>@[(TVarB X Q)]@\<Gamma>) ok" by (simp_all add: subtype_implies_ok)
      then have ok\<^sub>P: "\<turnstile> (\<Delta>@[(TVarB X P)]@\<Gamma>) ok" by (simp add: subtype_implies_ok) 
      show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> Tvar Y <: N"
      proof (cases "X=Y")
        case False
        have "X\<noteq>Y" by fact
        hence "(TVarB Y S)\<in>set (\<Delta>@[(TVarB X P)]@\<Gamma>)" using lh_drv_prm by (simp add:binding.inject)
        with IH_inner show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> Tvar Y <: N" by (simp add: subtype_of.SA_trans_TVar)
      next
        case True
        have memb\<^sub>XQ: "(TVarB X Q)\<in>set (\<Delta>@[(TVarB X Q)]@\<Gamma>)" by simp
        have memb\<^sub>XP: "(TVarB X P)\<in>set (\<Delta>@[(TVarB X P)]@\<Gamma>)" by simp
        have eq: "X=Y" by fact 
        hence "S=Q" using ok\<^sub>Q lh_drv_prm memb\<^sub>XQ by (simp only: uniqueness_of_ctxt)
        hence "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> Q <: N" using IH_inner by simp
        moreover
        have "(\<Delta>@[(TVarB X P)]@\<Gamma>) extends \<Gamma>" by (simp add: extends_def)
        hence "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> P <: Q" using rh_drv ok\<^sub>P by (simp only: weakening)
        ultimately have "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> P <: N" by (simp add: transitivity_lemma) 
        then show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> Tvar Y <: N" using memb\<^sub>XP eq by auto
      qed
    next
      case (SA_refl_TVar Y \<Gamma> X \<Delta>)
      from \<open>\<Gamma> \<turnstile> P <: Q\<close>
      have "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      with \<open>\<turnstile> (\<Delta>@[(TVarB X Q)]@\<Gamma>) ok\<close> have "\<turnstile> (\<Delta>@[(TVarB X P)]@\<Gamma>) ok"
        by (simp add: replace_type)
      moreover
      from \<open>Y \<in> ty_dom (\<Delta>@[(TVarB X Q)]@\<Gamma>)\<close> have "Y \<in> ty_dom (\<Delta>@[(TVarB X P)]@\<Gamma>)"
        by (simp add: doms_append)
      ultimately show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> Tvar Y <: Tvar Y" by (simp add: subtype_of.SA_refl_TVar)
    next
      case (SA_arrow S\<^sub>1 Q\<^sub>1 Q\<^sub>2 S\<^sub>2 \<Gamma> X \<Delta>) 
      then show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> Q\<^sub>1 \<rightarrow> Q\<^sub>2 <: S\<^sub>1 \<rightarrow> S\<^sub>2" by blast 
    next
      case (SA_all T\<^sub>1 S\<^sub>1 Y S\<^sub>2 T\<^sub>2 \<Gamma> X \<Delta>)
      have IH_inner\<^sub>1: "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> T\<^sub>1 <: S\<^sub>1" 
        and IH_inner\<^sub>2: "(((TVarB Y T\<^sub>1)#\<Delta>)@[(TVarB X P)]@\<Gamma>) \<turnstile> S\<^sub>2 <: T\<^sub>2"
        by (fastforce intro: SA_all)+
      then show "(\<Delta>@[(TVarB X P)]@\<Gamma>) \<turnstile> (\<forall>Y<:S\<^sub>1. S\<^sub>2) <: (\<forall>Y<:T\<^sub>1. T\<^sub>2)" by auto
    qed
  } 
qed

section \<open>Typing\<close>

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" (\<open>_ \<turnstile> _ : _\<close> [60,60,60] 60) 
where
  T_Var[intro]: "\<lbrakk> VarB x T \<in> set \<Gamma>; \<turnstile> \<Gamma> ok \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| T_App[intro]: "\<lbrakk> \<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1 \<rightarrow> T\<^sub>2; \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 \<cdot> t\<^sub>2 : T\<^sub>2"
| T_Abs[intro]: "\<lbrakk> VarB x T\<^sub>1 # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>x:T\<^sub>1. t\<^sub>2) : T\<^sub>1 \<rightarrow> T\<^sub>2"
| T_Sub[intro]: "\<lbrakk> \<Gamma> \<turnstile> t : S; \<Gamma> \<turnstile> S <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t : T"
| T_TAbs[intro]:"\<lbrakk> TVarB X T\<^sub>1 # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>X<:T\<^sub>1. t\<^sub>2) : (\<forall>X<:T\<^sub>1. T\<^sub>2)"
| T_TApp[intro]:"\<lbrakk>X\<sharp>(\<Gamma>,t\<^sub>1,T\<^sub>2); \<Gamma> \<turnstile> t\<^sub>1 : (\<forall>X<:T\<^sub>11. T\<^sub>12); \<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>11\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 \<cdot>\<^sub>\<tau> T\<^sub>2 : (T\<^sub>12[X \<leadsto> T\<^sub>2]\<^sub>\<tau>)" 

equivariance typing

lemma better_T_TApp:
  assumes H1: "\<Gamma> \<turnstile> t\<^sub>1 : (\<forall>X<:T11. T12)"
  and H2: "\<Gamma> \<turnstile> T2 <: T11"
  shows "\<Gamma> \<turnstile> t\<^sub>1 \<cdot>\<^sub>\<tau> T2 : (T12[X \<leadsto> T2]\<^sub>\<tau>)"
proof -
  obtain Y::tyvrs where Y: "Y \<sharp> (X, T12, \<Gamma>, t\<^sub>1, T2)"
    by (rule exists_fresh) (rule fin_supp)
  then have "Y \<sharp> (\<Gamma>, t\<^sub>1, T2)" by simp
  moreover from Y have "(\<forall>X<:T11. T12) = (\<forall>Y<:T11. [(Y, X)] \<bullet> T12)"
    by (auto simp: ty.inject alpha' fresh_prod fresh_atm)
  with H1 have "\<Gamma> \<turnstile> t\<^sub>1 : (\<forall>Y<:T11. [(Y, X)] \<bullet> T12)" by simp
  ultimately have "\<Gamma> \<turnstile> t\<^sub>1 \<cdot>\<^sub>\<tau> T2 : (([(Y, X)] \<bullet> T12)[Y \<leadsto> T2]\<^sub>\<tau>)" using H2
    by (rule T_TApp)
  with Y show ?thesis by (simp add: type_subst_rename)
qed

lemma typing_ok:
  assumes "\<Gamma> \<turnstile> t : T"
  shows   "\<turnstile> \<Gamma> ok"
using assms by (induct) (auto)

nominal_inductive typing
by (auto dest!: typing_ok intro: closed_in_fresh fresh_dom type_subst_fresh
    simp: abs_fresh fresh_type_subst_fresh ty_vrs_fresh valid_ty_dom_fresh fresh_trm_dom)

lemma ok_imp_VarB_closed_in:
  assumes ok: "\<turnstile> \<Gamma> ok"
  shows "VarB x T \<in> set \<Gamma> \<Longrightarrow> T closed_in \<Gamma>" using ok
  by induct (auto simp: binding.inject closed_in_def)

lemma tyvrs_of_subst: "tyvrs_of (B[X \<leadsto> T]\<^sub>b) = tyvrs_of B"
  by (nominal_induct B rule: binding.strong_induct) simp_all

lemma ty_dom_subst: "ty_dom (\<Gamma>[X \<leadsto> T]\<^sub>e) = ty_dom \<Gamma>"
  by (induct \<Gamma>) (simp_all add: tyvrs_of_subst)

lemma vrs_of_subst: "vrs_of (B[X \<leadsto> T]\<^sub>b) = vrs_of B"
  by (nominal_induct B rule: binding.strong_induct) simp_all

lemma trm_dom_subst: "trm_dom (\<Gamma>[X \<leadsto> T]\<^sub>e) = trm_dom \<Gamma>"
  by (induct \<Gamma>) (simp_all add: vrs_of_subst)

lemma subst_closed_in:
  "T closed_in (\<Delta> @ TVarB X S # \<Gamma>) \<Longrightarrow> U closed_in \<Gamma> \<Longrightarrow> T[X \<leadsto> U]\<^sub>\<tau> closed_in (\<Delta>[X \<leadsto> U]\<^sub>e @ \<Gamma>)"
proof (nominal_induct T avoiding: X U \<Gamma> rule: ty.strong_induct)
  case (Tvar tyvrs)
  then show ?case
    by (auto simp add: closed_in_def ty.supp supp_atm doms_append ty_dom_subst)
next
  case Top
  then show ?case
    using closed_in_def fresh_def by fastforce
next
  case (Arrow ty1 ty2)
  then show ?case
    by (simp add: closed_in_def ty.supp)
next
  case (Forall tyvrs ty1 ty2)
  then have "supp (ty1[X \<leadsto> U]\<^sub>\<tau>) \<subseteq> ty_dom (\<Delta>[X \<leadsto> U]\<^sub>e @ TVarB tyvrs ty2 # \<Gamma>)"
    apply (simp add: closed_in_def ty.supp abs_supp)
    by (metis Diff_subset_conv Un_left_commute doms_append(1) le_supI2 ty_dom.simps(2) tyvrs_of.simps(2))
  with Forall show ?case
    by (auto simp add: closed_in_def ty.supp abs_supp doms_append)
qed

lemmas subst_closed_in' = subst_closed_in [where \<Delta>="[]", simplified]

lemma typing_closed_in:
  assumes "\<Gamma> \<turnstile> t : T"
  shows   "T closed_in \<Gamma>"
using assms
proof induct
  case (T_Var x T \<Gamma>)
  from \<open>\<turnstile> \<Gamma> ok\<close> and \<open>VarB x T \<in> set \<Gamma>\<close>
  show ?case by (rule ok_imp_VarB_closed_in)
next
  case (T_App \<Gamma> t\<^sub>1 T\<^sub>1 T\<^sub>2 t\<^sub>2)
  then show ?case by (auto simp: ty.supp closed_in_def)
next
  case (T_Abs x T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>VarB x T\<^sub>1 # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close>
  have "T\<^sub>1 closed_in \<Gamma>" by (auto dest: typing_ok)
  with T_Abs show ?case by (auto simp: ty.supp closed_in_def)
next
  case (T_Sub \<Gamma> t S T)
  from \<open>\<Gamma> \<turnstile> S <: T\<close> show ?case by (simp add: subtype_implies_closed)
next
  case (T_TAbs X T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>TVarB X T\<^sub>1 # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close>
  have "T\<^sub>1 closed_in \<Gamma>" by (auto dest: typing_ok)
  with T_TAbs show ?case by (auto simp: ty.supp closed_in_def abs_supp)
next
  case (T_TApp X \<Gamma> t\<^sub>1 T2 T11 T12)
  then have "T12 closed_in (TVarB X T11 # \<Gamma>)"
    by (auto simp: closed_in_def ty.supp abs_supp)
  moreover from T_TApp have "T2 closed_in \<Gamma>"
    by (simp add: subtype_implies_closed)
  ultimately show ?case by (rule subst_closed_in')
qed


subsection \<open>Evaluation\<close>

inductive
  val :: "trm \<Rightarrow> bool"
where
  Abs[intro]:  "val (\<lambda>x:T. t)"
| TAbs[intro]: "val (\<lambda>X<:T. t)"

equivariance val

inductive_cases val_inv_auto[elim]: 
  "val (Var x)" 
  "val (t1 \<cdot> t2)" 
  "val (t1 \<cdot>\<^sub>\<tau> t2)"

inductive 
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool" (\<open>_ \<longmapsto> _\<close> [60,60] 60)
where
  E_Abs         : "\<lbrakk> x \<sharp> v\<^sub>2; val v\<^sub>2 \<rbrakk> \<Longrightarrow> (\<lambda>x:T\<^sub>11. t\<^sub>12) \<cdot> v\<^sub>2 \<longmapsto> t\<^sub>12[x \<leadsto> v\<^sub>2]"
| E_App1 [intro]: "t \<longmapsto> t' \<Longrightarrow> t \<cdot> u \<longmapsto> t' \<cdot> u"
| E_App2 [intro]: "\<lbrakk> val v; t \<longmapsto> t' \<rbrakk> \<Longrightarrow> v \<cdot> t \<longmapsto> v \<cdot> t'"
| E_TAbs        : "X \<sharp> (T\<^sub>11, T\<^sub>2) \<Longrightarrow> (\<lambda>X<:T\<^sub>11. t\<^sub>12) \<cdot>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t\<^sub>12[X \<leadsto>\<^sub>\<tau> T\<^sub>2]"
| E_TApp [intro]: "t \<longmapsto> t' \<Longrightarrow> t \<cdot>\<^sub>\<tau> T \<longmapsto> t' \<cdot>\<^sub>\<tau> T"

lemma better_E_Abs[intro]:
  assumes H: "val v2"
  shows "(\<lambda>x:T11. t12) \<cdot> v2 \<longmapsto> t12[x \<leadsto> v2]"
proof -
  obtain y::vrs where y: "y \<sharp> (x, t12, v2)" by (rule exists_fresh) (rule fin_supp)
  then have "y \<sharp> v2" by simp
  then have "(\<lambda>y:T11. [(y, x)] \<bullet> t12) \<cdot> v2 \<longmapsto> ([(y, x)] \<bullet> t12)[y \<leadsto> v2]" using H
    by (rule E_Abs)
  moreover from y have "(\<lambda>x:T11. t12) \<cdot> v2 = (\<lambda>y:T11. [(y, x)] \<bullet> t12) \<cdot> v2"
    by (auto simp: trm.inject alpha' fresh_prod fresh_atm)
  ultimately have "(\<lambda>x:T11. t12) \<cdot> v2 \<longmapsto> ([(y, x)] \<bullet> t12)[y \<leadsto> v2]"
    by simp
  with y show ?thesis by (simp add: subst_trm_rename)
qed

lemma better_E_TAbs[intro]: "(\<lambda>X<:T11. t12) \<cdot>\<^sub>\<tau> T2 \<longmapsto> t12[X \<leadsto>\<^sub>\<tau> T2]"
proof -
  obtain Y::tyvrs where Y: "Y \<sharp> (X, t12, T11, T2)" by (rule exists_fresh) (rule fin_supp)
  then have "Y \<sharp> (T11, T2)" by simp
  then have "(\<lambda>Y<:T11. [(Y, X)] \<bullet> t12) \<cdot>\<^sub>\<tau> T2 \<longmapsto> ([(Y, X)] \<bullet> t12)[Y \<leadsto>\<^sub>\<tau> T2]"
    by (rule E_TAbs)
  moreover from Y have "(\<lambda>X<:T11. t12) \<cdot>\<^sub>\<tau> T2 = (\<lambda>Y<:T11. [(Y, X)] \<bullet> t12) \<cdot>\<^sub>\<tau> T2"
    by (auto simp: trm.inject alpha' fresh_prod fresh_atm)
  ultimately have "(\<lambda>X<:T11. t12) \<cdot>\<^sub>\<tau> T2 \<longmapsto> ([(Y, X)] \<bullet> t12)[Y \<leadsto>\<^sub>\<tau> T2]"
    by simp
  with Y show ?thesis by (simp add: subst_trm_ty_rename)
qed

equivariance eval

nominal_inductive eval
  by (simp_all add: abs_fresh ty_vrs_fresh subst_trm_fresh_tyvar
    subst_trm_fresh_var subst_trm_ty_fresh')

inductive_cases eval_inv_auto[elim]: 
  "Var x \<longmapsto> t'" 
  "(\<lambda>x:T. t) \<longmapsto> t'" 
  "(\<lambda>X<:T. t) \<longmapsto> t'" 

lemma ty_dom_cons:
  shows "ty_dom (\<Gamma>@[VarB X Q]@\<Delta>) = ty_dom (\<Gamma>@\<Delta>)"
by (induct \<Gamma>) (auto)

lemma closed_in_cons: 
  assumes "S closed_in (\<Gamma> @ VarB X Q # \<Delta>)"
  shows "S closed_in (\<Gamma>@\<Delta>)"
using assms ty_dom_cons closed_in_def by auto

lemma closed_in_weaken: "T closed_in (\<Delta> @ \<Gamma>) \<Longrightarrow> T closed_in (\<Delta> @ B # \<Gamma>)"
  by (auto simp: closed_in_def doms_append)

lemma closed_in_weaken': "T closed_in \<Gamma> \<Longrightarrow> T closed_in (\<Delta> @ \<Gamma>)"
  by (auto simp: closed_in_def doms_append)

lemma valid_subst:
  assumes ok: "\<turnstile> (\<Delta> @ TVarB X Q # \<Gamma>) ok"
  and closed: "P closed_in \<Gamma>"
  shows "\<turnstile> (\<Delta>[X \<leadsto> P]\<^sub>e @ \<Gamma>) ok" using ok closed
proof (induct \<Delta>)
  case Nil
  then show ?case
    by auto
next
  case (Cons a \<Delta>)
  then have *: "\<turnstile> (a # \<Delta> @ TVarB X Q # \<Gamma>) ok"
    by fastforce
  then show ?case
    apply (rule validE)
    using Cons
     apply (simp add: at_tyvrs_inst closed doms_append(1) finite_doms(1) fresh_fin_insert fs_tyvrs_inst pt_tyvrs_inst subst_closed_in ty_dom_subst)
    by (simp add: doms_append(2) subst_closed_in Cons.hyps closed trm_dom_subst)
qed

lemma ty_dom_vrs:
  shows "ty_dom (G @ [VarB x Q] @ D) = ty_dom (G @ D)"
  by (induct G) (auto)

lemma valid_cons':
  assumes "\<turnstile> (\<Gamma> @ VarB x Q # \<Delta>) ok"
  shows "\<turnstile> (\<Gamma> @ \<Delta>) ok"
  using assms
proof (induct "\<Gamma> @ VarB x Q # \<Delta>" arbitrary: \<Gamma> \<Delta>)
  case valid_nil
  have "[] = \<Gamma> @ VarB x Q # \<Delta>" by fact
  then have "False" by auto
  then show ?case by auto
next
  case (valid_consT G X T)
  then show ?case
  proof (cases \<Gamma>)
    case Nil
    with valid_consT show ?thesis by simp
  next
    case (Cons b bs)
    with valid_consT
    have "\<turnstile> (bs @ \<Delta>) ok" by simp
    moreover from Cons and valid_consT have "X \<sharp> ty_dom (bs @ \<Delta>)"
      by (simp add: doms_append)
    moreover from Cons and valid_consT have "T closed_in (bs @ \<Delta>)"
      by (simp add: closed_in_def doms_append)
    ultimately have "\<turnstile> (TVarB X T # bs @ \<Delta>) ok"
      by (rule valid_rel.valid_consT)
    with Cons and valid_consT show ?thesis by simp
  qed
next
  case (valid_cons G x T)
  then show ?case
  proof (cases \<Gamma>)
    case Nil
    with valid_cons show ?thesis by simp
  next
    case (Cons b bs)
    with valid_cons
    have "\<turnstile> (bs @ \<Delta>) ok" by simp
    moreover from Cons and valid_cons have "x \<sharp> trm_dom (bs @ \<Delta>)"
      by (simp add: doms_append finite_doms
        fresh_fin_insert [OF pt_vrs_inst at_vrs_inst fs_vrs_inst])
    moreover from Cons and valid_cons have "T closed_in (bs @ \<Delta>)"
      by (simp add: closed_in_def doms_append)
    ultimately have "\<turnstile> (VarB x T # bs @ \<Delta>) ok"
      by (rule valid_rel.valid_cons)
    with Cons and valid_cons show ?thesis by simp
  qed
qed
  
text \<open>A.5(6)\<close>

lemma type_weaken:
  assumes "(\<Delta>@\<Gamma>) \<turnstile> t : T"
  and     "\<turnstile> (\<Delta> @ B # \<Gamma>) ok"
  shows   "(\<Delta> @ B # \<Gamma>) \<turnstile> t : T"
using assms
proof(nominal_induct "\<Delta> @ \<Gamma>" t T avoiding: \<Delta> \<Gamma> B rule: typing.strong_induct)
  case (T_Var x T)
  then show ?case by auto
next
  case (T_App X t\<^sub>1 T\<^sub>2 T\<^sub>11 T\<^sub>12)
  then show ?case by force
next
  case (T_Abs y T\<^sub>1 t\<^sub>2 T\<^sub>2 \<Delta> \<Gamma>)
  then have "VarB y T\<^sub>1 # \<Delta> @ \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2" by simp
  then have closed: "T\<^sub>1 closed_in (\<Delta> @ \<Gamma>)"
    by (auto dest: typing_ok)
  have "\<turnstile> (VarB y T\<^sub>1 # \<Delta> @ B # \<Gamma>) ok"
    by (simp add: T_Abs closed closed_in_weaken fresh_list_append fresh_list_cons fresh_trm_dom)
  then have "\<turnstile> ((VarB y T\<^sub>1 # \<Delta>) @ B # \<Gamma>) ok" by simp
  with _ have "(VarB y T\<^sub>1 # \<Delta>) @ B # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2"
    by (rule T_Abs) simp
  then have "VarB y T\<^sub>1 # \<Delta> @ B # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2" by simp
  then show ?case by (rule typing.T_Abs)
next
  case (T_Sub t S T \<Delta> \<Gamma>)
  from refl and \<open>\<turnstile> (\<Delta> @ B # \<Gamma>) ok\<close>
  have "\<Delta> @ B # \<Gamma> \<turnstile> t : S" by (rule T_Sub)
  moreover from  \<open>(\<Delta> @ \<Gamma>)\<turnstile>S<:T\<close> and \<open>\<turnstile> (\<Delta> @ B # \<Gamma>) ok\<close>
  have "(\<Delta> @ B # \<Gamma>)\<turnstile>S<:T"
    by (rule weakening) (simp add: extends_def T_Sub)
  ultimately show ?case by (rule typing.T_Sub)
next
  case (T_TAbs X T\<^sub>1 t\<^sub>2 T\<^sub>2 \<Delta> \<Gamma>)
  from \<open>TVarB X T\<^sub>1 # \<Delta> @ \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close>
  have closed: "T\<^sub>1 closed_in (\<Delta> @ \<Gamma>)"
    by (auto dest: typing_ok)
  have "\<turnstile> (TVarB X T\<^sub>1 # \<Delta> @ B # \<Gamma>) ok"
    by (simp add: T_TAbs at_tyvrs_inst closed closed_in_weaken doms_append finite_doms finite_vrs
        fresh_dom fresh_fin_union fs_tyvrs_inst pt_tyvrs_inst tyvrs_fresh)
  then have "\<turnstile> ((TVarB X T\<^sub>1 # \<Delta>) @ B # \<Gamma>) ok" by simp
  with _ have "(TVarB X T\<^sub>1 # \<Delta>) @ B # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2"
    by (rule T_TAbs) simp
  then have "TVarB X T\<^sub>1 # \<Delta> @ B # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2" by simp
  then show ?case by (rule typing.T_TAbs)
next
  case (T_TApp X t\<^sub>1 T2 T11 T12 \<Delta> \<Gamma>)
  have "\<Delta> @ B # \<Gamma> \<turnstile> t\<^sub>1 : (\<forall>X<:T11. T12)"
    by (rule T_TApp refl)+
  moreover from \<open>(\<Delta> @ \<Gamma>)\<turnstile>T2<:T11\<close> and \<open>\<turnstile> (\<Delta> @ B # \<Gamma>) ok\<close>
  have "(\<Delta> @ B # \<Gamma>)\<turnstile>T2<:T11"
    by (rule weakening) (simp add: extends_def T_TApp)
  ultimately show ?case by (rule better_T_TApp)
qed

lemma type_weaken':
 "\<Gamma> \<turnstile> t : T \<Longrightarrow>  \<turnstile> (\<Delta>@\<Gamma>) ok \<Longrightarrow> (\<Delta>@\<Gamma>) \<turnstile> t : T"
proof (induct \<Delta>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Delta>)
  then show ?case
    by (metis append_Cons append_Nil type_weaken validE(3))
qed

text \<open>A.6\<close>

lemma strengthening:
  assumes "(\<Gamma> @ VarB x Q # \<Delta>) \<turnstile> S <: T"
  shows  "(\<Gamma>@\<Delta>) \<turnstile> S <: T"
  using assms
proof (induct "\<Gamma> @ VarB x Q # \<Delta>" S T arbitrary: \<Gamma>)
  case (SA_Top S)
  then have "\<turnstile> (\<Gamma> @ \<Delta>) ok" by (auto dest: valid_cons')
  moreover have "S closed_in (\<Gamma> @ \<Delta>)" using SA_Top by (auto dest: closed_in_cons)
  ultimately show ?case using subtype_of.SA_Top by auto
next
  case (SA_refl_TVar X)
  from \<open>\<turnstile> (\<Gamma> @ VarB x Q # \<Delta>) ok\<close>
  have h1:"\<turnstile> (\<Gamma> @ \<Delta>) ok" by (auto dest: valid_cons')
  have "X \<in> ty_dom (\<Gamma> @ VarB x Q # \<Delta>)" using SA_refl_TVar by auto
  then have h2:"X \<in> ty_dom (\<Gamma> @ \<Delta>)" using ty_dom_vrs by auto
  show ?case using h1 h2 by auto
next
  case (SA_all T1 S1 X S2 T2)
  have h1:"((TVarB X T1 # \<Gamma>) @ \<Delta>)\<turnstile>S2<:T2" by (fastforce intro: SA_all)
  have h2:"(\<Gamma> @ \<Delta>)\<turnstile>T1<:S1" using SA_all by auto
  then show ?case using h1 h2 by auto
qed (auto)

lemma narrow_type: \<comment> \<open>A.7\<close>
  assumes H: "\<Delta> @ (TVarB X Q) # \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ (TVarB X P) # \<Gamma> \<turnstile> t : T"
  using H
  proof (nominal_induct "\<Delta> @ (TVarB X Q) # \<Gamma>" t T avoiding: P arbitrary: \<Delta> rule: typing.strong_induct)
    case (T_Var x T P D)
    then have "VarB x T \<in> set (D @ TVarB X P # \<Gamma>)" 
      and "\<turnstile>  (D @ TVarB X P # \<Gamma>) ok"
      by (auto intro: replace_type dest!: subtype_implies_closed)
    then show ?case by auto
  next
    case (T_App t1 T1 T2 t2 P D)
    then show ?case by force
  next
    case (T_Abs x T1 t2 T2 P D)
    then show ?case by (fastforce dest: typing_ok)
  next
    case (T_Sub t S T P D)
    then show ?case using subtype_narrow by fastforce
  next
    case (T_TAbs X' T1 t2 T2 P D)
    then show ?case by (fastforce dest: typing_ok)
  next
    case (T_TApp X' t1 T2 T11 T12 P D)
    then have "D @ TVarB X P # \<Gamma> \<turnstile> t1 : Forall X' T12 T11" by fastforce
    moreover have "(D @ [TVarB X Q] @ \<Gamma>) \<turnstile> T2<:T11" using T_TApp by auto
    then have "(D @ [TVarB X P] @ \<Gamma>) \<turnstile> T2<:T11" using \<open>\<Gamma>\<turnstile>P<:Q\<close>
      by (rule subtype_narrow)
    moreover from T_TApp have "X' \<sharp> (D @ TVarB X P # \<Gamma>, t1, T2)"
      by (simp add: fresh_list_append fresh_list_cons fresh_prod)
    ultimately show ?case by auto
qed

subsection \<open>Substitution lemmas\<close>

subsubsection \<open>Substition Preserves Typing\<close>

theorem subst_type: \<comment> \<open>A.8\<close>
  assumes H: "(\<Delta> @ (VarB x U) # \<Gamma>) \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> u : U \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> t[x \<leadsto> u] : T" using H
 proof (nominal_induct "\<Delta> @ (VarB x U) # \<Gamma>" t T avoiding: x u arbitrary: \<Delta> rule: typing.strong_induct)
   case (T_Var y T x u D)
   show ?case
   proof (cases "x = y")
     assume eq:"x=y"
     then have "T=U" using T_Var uniqueness_of_ctxt' by auto
     then show ?case using eq T_Var
       by (auto intro: type_weaken' dest: valid_cons')
   next
     assume "x\<noteq>y"
     then show ?case using T_Var
       by (auto simp:binding.inject dest: valid_cons')
   qed
 next
   case (T_App t1 T1 T2 t2 x u D)
   then show ?case by force
 next
   case (T_Abs y T1 t2 T2 x u D)
   then show ?case by force
 next
   case (T_Sub t S T x u D)
   then have "D @ \<Gamma> \<turnstile> t[x \<leadsto> u] : S" by auto
   moreover have "(D @ \<Gamma>) \<turnstile> S<:T" using T_Sub by (auto dest: strengthening)
   ultimately show ?case by auto 
 next
   case (T_TAbs X T1 t2 T2 x u D)
   from \<open>TVarB X T1 # D @ VarB x U # \<Gamma> \<turnstile> t2 : T2\<close> have "X \<sharp> T1"
     by (auto simp: valid_ty_dom_fresh dest: typing_ok intro!: closed_in_fresh)
   with \<open>X \<sharp> u\<close> and T_TAbs show ?case by fastforce
 next
   case (T_TApp X t1 T2 T11 T12 x u D)
   then have "(D@\<Gamma>) \<turnstile>T2<:T11" using T_TApp by (auto dest: strengthening)
   then show "((D @ \<Gamma>) \<turnstile> ((t1 \<cdot>\<^sub>\<tau> T2)[x \<leadsto> u]) : (T12[X \<leadsto> T2]\<^sub>\<tau>))" using T_TApp
     by (force simp: fresh_prod fresh_list_append fresh_list_cons subst_trm_fresh_tyvar)
qed

subsubsection \<open>Type Substitution Preserves Subtyping\<close>

lemma substT_subtype: \<comment> \<open>A.10\<close>
  assumes H: "(\<Delta> @ ((TVarB X Q) # \<Gamma>)) \<turnstile> S <: T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> (\<Delta>[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> S[X \<leadsto> P]\<^sub>\<tau> <: T[X \<leadsto> P]\<^sub>\<tau>" 
  using H
proof (nominal_induct "\<Delta> @ TVarB X Q # \<Gamma>" S T avoiding: X P arbitrary: \<Delta> rule: subtype_of.strong_induct)
  case (SA_Top S X P D)
  then have "\<turnstile> (D @ TVarB X Q # \<Gamma>) ok" by simp
  moreover have closed: "P closed_in \<Gamma>" using SA_Top subtype_implies_closed by auto 
  ultimately have "\<turnstile> (D[X \<leadsto> P]\<^sub>e @ \<Gamma>) ok" by (rule valid_subst)
  moreover from SA_Top have "S closed_in (D @ TVarB X Q # \<Gamma>)" by simp
  then have "S[X \<leadsto> P]\<^sub>\<tau> closed_in  (D[X \<leadsto> P]\<^sub>e @ \<Gamma>)" using closed by (rule subst_closed_in)
  ultimately show ?case by auto
next
  case (SA_trans_TVar Y S T X P D)
  have h:"(D @ TVarB X Q # \<Gamma>)\<turnstile>S<:T" by fact
  then have ST: "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> S[X \<leadsto> P]\<^sub>\<tau> <: T[X \<leadsto> P]\<^sub>\<tau>" using SA_trans_TVar by auto
  from h have G_ok: "\<turnstile> (D @ TVarB X Q # \<Gamma>) ok" by (rule subtype_implies_ok)
  from G_ok and SA_trans_TVar have X_\<Gamma>_ok: "\<turnstile> (TVarB X Q # \<Gamma>) ok"
    by (auto intro: validE_append)
  show "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> Tvar Y[X \<leadsto> P]\<^sub>\<tau><:T[X \<leadsto> P]\<^sub>\<tau>"
  proof (cases "X = Y")
    assume eq: "X = Y"
    from eq and SA_trans_TVar have "TVarB Y Q \<in> set (D @ TVarB X Q # \<Gamma>)" by simp
    with G_ok have QS: "Q = S" using \<open>TVarB Y S \<in> set (D @ TVarB X Q # \<Gamma>)\<close>
      by (rule uniqueness_of_ctxt)
    from X_\<Gamma>_ok have "X \<sharp> ty_dom \<Gamma>" and "Q closed_in \<Gamma>" by auto
    then have XQ: "X \<sharp> Q" by (rule closed_in_fresh)
    note \<open>\<Gamma>\<turnstile>P<:Q\<close>
    moreover from ST have "\<turnstile> (D[X \<leadsto> P]\<^sub>e @ \<Gamma>) ok" by (rule subtype_implies_ok)
    moreover have "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) extends \<Gamma>" by (simp add: extends_def)
    ultimately have "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> P<:Q" by (rule weakening)
    with QS have "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> P<:S" by simp
    moreover from XQ and ST and QS have "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> S<:T[X \<leadsto> P]\<^sub>\<tau>"
      by (simp add: type_subst_identity)
    ultimately have "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>) \<turnstile> P<:T[X \<leadsto> P]\<^sub>\<tau>"
      by (rule subtype_transitivity)
    with eq show ?case by simp
  next
    assume neq: "X \<noteq> Y"
    with SA_trans_TVar have "TVarB Y S \<in> set D \<or> TVarB Y S \<in> set \<Gamma>"
      by (simp add: binding.inject)
    then show ?case
    proof
      assume "TVarB Y S \<in> set D"
      then have "TVarB Y (S[X \<leadsto> P]\<^sub>\<tau>) \<in> set (D[X \<leadsto> P]\<^sub>e)"
        by (rule ctxt_subst_mem_TVarB)
      then have "TVarB Y (S[X \<leadsto> P]\<^sub>\<tau>) \<in> set (D[X \<leadsto> P]\<^sub>e @ \<Gamma>)" by simp
      with neq and ST show ?thesis by auto
    next
      assume Y: "TVarB Y S \<in> set \<Gamma>"
      from X_\<Gamma>_ok have "X \<sharp> ty_dom \<Gamma>" and "\<turnstile> \<Gamma> ok" by auto
      then have "X \<sharp> \<Gamma>" by (simp add: valid_ty_dom_fresh)
      with Y have "X \<sharp> S"
        by (induct \<Gamma>) (auto simp: fresh_list_nil fresh_list_cons)
      with ST have "(D[X \<leadsto> P]\<^sub>e @ \<Gamma>)\<turnstile>S<:T[X \<leadsto> P]\<^sub>\<tau>"
        by (simp add: type_subst_identity)
      moreover from Y have "TVarB Y S \<in> set (D[X \<leadsto> P]\<^sub>e @ \<Gamma>)" by simp
      ultimately show ?thesis using neq by auto
    qed
  qed
next
  case (SA_refl_TVar Y X P D)
  note \<open>\<turnstile> (D @ TVarB X Q # \<Gamma>) ok\<close>
  moreover from SA_refl_TVar have closed: "P closed_in \<Gamma>"
    by (auto dest: subtype_implies_closed)
  ultimately have ok: "\<turnstile> (D[X \<leadsto> P]\<^sub>e @ \<Gamma>) ok" using valid_subst by auto
  from closed have closed': "P closed_in (D[X \<leadsto> P]\<^sub>e @ \<Gamma>)"
    by (simp add: closed_in_weaken')
  show ?case
  proof (cases "X = Y")
    assume "X = Y"
    with closed' and ok show ?thesis
      by (auto intro: subtype_reflexivity)
  next
    assume neq: "X \<noteq> Y"
    with SA_refl_TVar have "Y \<in> ty_dom (D[X \<leadsto> P]\<^sub>e @ \<Gamma>)"
      by (simp add: ty_dom_subst doms_append)
    with neq and ok show ?thesis by auto
  qed
next
  case (SA_arrow T1 S1 S2 T2 X P D)
  then have h1:"(D[X \<leadsto> P]\<^sub>e @ \<Gamma>)\<turnstile>T1[X \<leadsto> P]\<^sub>\<tau><:S1[X \<leadsto> P]\<^sub>\<tau>" using SA_arrow by auto
  from SA_arrow have h2:"(D[X \<leadsto> P]\<^sub>e @ \<Gamma>)\<turnstile>S2[X \<leadsto> P]\<^sub>\<tau><:T2[X \<leadsto> P]\<^sub>\<tau>" using SA_arrow by auto
  show ?case using subtype_of.SA_arrow h1 h2 by auto
next
  case (SA_all T1 S1 Y S2 T2 X P D)
  then have Y: "Y \<sharp> ty_dom (D @ TVarB X Q # \<Gamma>)"
    by (auto dest: subtype_implies_ok intro: fresh_dom)
  moreover from SA_all have "S1 closed_in (D @ TVarB X Q # \<Gamma>)"
    by (auto dest: subtype_implies_closed)
  ultimately have S1: "Y \<sharp> S1" by (rule closed_in_fresh)
  from SA_all have "T1 closed_in (D @ TVarB X Q # \<Gamma>)"
    by (auto dest: subtype_implies_closed)
  with Y have T1: "Y \<sharp> T1" by (rule closed_in_fresh)
  with SA_all and S1 show ?case by force
qed

subsubsection \<open>Type Substitution Preserves Typing\<close>

theorem substT_type: \<comment> \<open>A.11\<close>
  assumes H: "(D @ TVarB X Q # G) \<turnstile> t : T"
  shows "G \<turnstile> P <: Q \<Longrightarrow>
    (D[X \<leadsto> P]\<^sub>e @ G) \<turnstile> t[X \<leadsto>\<^sub>\<tau> P] : T[X \<leadsto> P]\<^sub>\<tau>" using H
proof (nominal_induct "D @ TVarB X Q # G" t T avoiding: X P arbitrary: D rule: typing.strong_induct)
  case (T_Var x T X P D')
  have "G\<turnstile>P<:Q" by fact
  then have "P closed_in G" using subtype_implies_closed by auto
  moreover note \<open>\<turnstile> (D' @ TVarB X Q # G) ok\<close>
  ultimately have "\<turnstile> (D'[X \<leadsto> P]\<^sub>e @ G) ok" using valid_subst by auto
  moreover note \<open>VarB x T \<in> set (D' @ TVarB X Q # G)\<close>
  then have "VarB x T \<in> set D' \<or> VarB x T \<in> set G" by simp
  then have "(VarB x (T[X \<leadsto> P]\<^sub>\<tau>)) \<in> set (D'[X \<leadsto> P]\<^sub>e @ G)"
  proof
    assume "VarB x T \<in> set D'"
    then have "VarB x (T[X \<leadsto> P]\<^sub>\<tau>) \<in> set (D'[X \<leadsto> P]\<^sub>e)"
      by (rule ctxt_subst_mem_VarB)
    then show ?thesis by simp
  next
    assume x: "VarB x T \<in> set G"
    from T_Var have ok: "\<turnstile> G ok" by (auto dest: subtype_implies_ok)
    then have "X \<sharp> ty_dom G" using T_Var by (auto dest: validE_append)
    with ok have "X \<sharp> G" by (simp add: valid_ty_dom_fresh)
    moreover from x have "VarB x T \<in> set (D' @ G)" by simp
    then have "VarB x (T[X \<leadsto> P]\<^sub>\<tau>) \<in> set ((D' @ G)[X \<leadsto> P]\<^sub>e)"
      by (rule ctxt_subst_mem_VarB)
    ultimately show ?thesis
      by (simp add: ctxt_subst_append ctxt_subst_identity)
  qed
  ultimately show ?case by auto
next
  case (T_App t1 T1 T2 t2 X P D')
  then have "D'[X \<leadsto> P]\<^sub>e @ G \<turnstile> t1[X \<leadsto>\<^sub>\<tau> P] : (T1 \<rightarrow> T2)[X \<leadsto> P]\<^sub>\<tau>" by auto
  moreover from T_App have "D'[X \<leadsto> P]\<^sub>e @ G \<turnstile> t2[X \<leadsto>\<^sub>\<tau> P] : T1[X \<leadsto> P]\<^sub>\<tau>" by auto
  ultimately show ?case by auto
next
  case (T_Abs x T1 t2 T2 X P D')
  then show ?case by force
next
  case (T_Sub t S T X P D')
  then show ?case using substT_subtype by force
next
  case (T_TAbs X' T1 t2 T2 X P D')
  then have "X' \<sharp> ty_dom (D' @ TVarB X Q # G)"
  and "T1 closed_in (D' @ TVarB X Q # G)"
    by (auto dest: typing_ok)
  then have "X' \<sharp> T1" by (rule closed_in_fresh)
  with T_TAbs show ?case by force
next
  case (T_TApp X' t1 T2 T11 T12 X P D')
  then have "X' \<sharp> ty_dom (D' @ TVarB X Q # G)"
    by (simp add: fresh_dom)
  moreover from T_TApp have "T11 closed_in (D' @ TVarB X Q # G)"
    by (auto dest: subtype_implies_closed)
  ultimately have X': "X' \<sharp> T11" by (rule closed_in_fresh)
  from T_TApp have "D'[X \<leadsto> P]\<^sub>e @ G \<turnstile> t1[X \<leadsto>\<^sub>\<tau> P] : (\<forall>X'<:T11. T12)[X \<leadsto> P]\<^sub>\<tau>"
    by simp
  with X' and T_TApp show ?case
    by (auto simp: fresh_atm type_substitution_lemma
      fresh_list_append fresh_list_cons
      ctxt_subst_fresh' type_subst_fresh subst_trm_ty_fresh
      intro: substT_subtype)
qed

lemma Abs_type: \<comment> \<open>A.13(1)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda>x:S. s) : T"
  and H': "\<Gamma> \<turnstile> T <: U \<rightarrow> U'"
  and H'': "x \<sharp> \<Gamma>"
  obtains S' where "\<Gamma> \<turnstile> U <: S"
             and   "(VarB x S) # \<Gamma> \<turnstile> s : S'"
             and   "\<Gamma> \<turnstile> S' <: U'"
  using H H' H''
proof (nominal_induct \<Gamma> t \<equiv> "\<lambda>x:S. s" T avoiding: x arbitrary: U U' S s rule: typing.strong_induct)
  case (T_Abs y T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> T\<^sub>1 \<rightarrow> T\<^sub>2 <: U \<rightarrow> U'\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: S" and ty2: "\<Gamma> \<turnstile> T\<^sub>2 <: U'" using T_Abs
    by cases (simp_all add: ty.inject trm.inject alpha fresh_atm)
  from T_Abs have "VarB y S # \<Gamma> \<turnstile> [(y, x)] \<bullet> s : T\<^sub>2"
    by (simp add: trm.inject alpha fresh_atm)
  then have "[(y, x)] \<bullet> (VarB y S # \<Gamma>) \<turnstile> [(y, x)] \<bullet> [(y, x)] \<bullet> s : [(y, x)] \<bullet> T\<^sub>2"
    by (rule typing.eqvt)
  moreover from T_Abs have "y \<sharp> \<Gamma>"
    by (auto dest!: typing_ok simp add: fresh_trm_dom)
  ultimately have "VarB x S # \<Gamma> \<turnstile> s : T\<^sub>2" using T_Abs
    by (perm_simp add: ty_vrs_prm_simp)
  with ty1 show ?case using ty2 by (rule T_Abs)
next
  case (T_Sub \<Gamma> t S T)
  then show ?case using subtype_transitivity by blast
qed simp_all

lemma subtype_reflexivity_from_typing:
  assumes "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> T <: T"
using assms subtype_reflexivity typing_ok typing_closed_in by simp

lemma Abs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda>x:S. s) : U \<rightarrow> U'"
  and H': "x \<sharp> \<Gamma>"
  obtains S'
  where "\<Gamma> \<turnstile> U <: S"
  and "(VarB x S) # \<Gamma> \<turnstile> s : S'"
  and "\<Gamma> \<turnstile> S' <: U'"
  using H subtype_reflexivity_from_typing [OF H] H'
  by (rule Abs_type)

lemma TAbs_type: \<comment> \<open>A.13(2)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda>X<:S. s) : T"
  and H': "\<Gamma> \<turnstile> T <: (\<forall>X<:U. U')"
  and fresh: "X \<sharp> \<Gamma>" "X \<sharp> S" "X \<sharp> U"
  obtains S'
  where "\<Gamma> \<turnstile> U <: S"
  and   "(TVarB X U # \<Gamma>) \<turnstile> s : S'"
  and   "(TVarB X U # \<Gamma>) \<turnstile> S' <: U'"
  using H H' fresh
proof (nominal_induct \<Gamma> t \<equiv> "\<lambda>X<:S. s" T avoiding: X U U' S arbitrary: s rule: typing.strong_induct)
  case (T_TAbs Y T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>TVarB Y T\<^sub>1 # \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close> have Y: "Y \<sharp> \<Gamma>"
    by (auto dest!: typing_ok simp add: valid_ty_dom_fresh)
  from \<open>Y \<sharp> U'\<close> and \<open>Y \<sharp> X\<close>
  have "(\<forall>X<:U. U') = (\<forall>Y<:U. [(Y, X)] \<bullet> U')"
    by (simp add: ty.inject alpha' fresh_atm)
  with T_TAbs have "\<Gamma> \<turnstile> (\<forall>Y<:S. T\<^sub>2) <: (\<forall>Y<:U. [(Y, X)] \<bullet> U')" by (simp add: trm.inject)
  then obtain ty1: "\<Gamma> \<turnstile> U <: S" and ty2: "(TVarB Y U # \<Gamma>) \<turnstile> T\<^sub>2 <: ([(Y, X)] \<bullet> U')" using T_TAbs Y
    by (cases rule: subtype_of.strong_cases [where X=Y]) (simp_all add: ty.inject alpha abs_fresh)
  note ty1
  moreover from T_TAbs have "TVarB Y S # \<Gamma> \<turnstile> ([(Y, X)] \<bullet> s) : T\<^sub>2"
    by (simp add: trm.inject alpha fresh_atm)
  then have "[(Y, X)] \<bullet> (TVarB Y S # \<Gamma>) \<turnstile> [(Y, X)] \<bullet> [(Y, X)] \<bullet> s : [(Y, X)] \<bullet> T\<^sub>2"
    by (rule typing.eqvt)
  with \<open>X \<sharp> \<Gamma>\<close> \<open>X \<sharp> S\<close> Y \<open>Y \<sharp> S\<close> have "TVarB X S # \<Gamma> \<turnstile> s : [(Y, X)] \<bullet> T\<^sub>2"
    by perm_simp
  then have "TVarB X U # \<Gamma> \<turnstile> s : [(Y, X)] \<bullet> T\<^sub>2" using ty1
    by (rule narrow_type [of "[]", simplified])
  moreover from ty2 have "([(Y, X)] \<bullet> (TVarB Y U # \<Gamma>)) \<turnstile> ([(Y, X)] \<bullet> T\<^sub>2) <: ([(Y, X)] \<bullet> [(Y, X)] \<bullet> U')"
    by (rule subtype_of.eqvt)
  with \<open>X \<sharp> \<Gamma>\<close> \<open>X \<sharp> U\<close> Y \<open>Y \<sharp> U\<close> have "(TVarB X U # \<Gamma>) \<turnstile> ([(Y, X)] \<bullet> T\<^sub>2) <: U'"
    by perm_simp
  ultimately show ?case by (rule T_TAbs)
next
  case (T_Sub \<Gamma> t S T)
  then show ?case using subtype_transitivity by blast 
qed simp_all

lemma TAbs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda>X<:S. s) : (\<forall>X<:U. U')"
  and fresh: "X \<sharp> \<Gamma>" "X \<sharp> S" "X \<sharp> U"
  obtains S'
  where "\<Gamma> \<turnstile> U <: S"
  and "(TVarB X U # \<Gamma>) \<turnstile> s : S'"
  and "(TVarB X U # \<Gamma>) \<turnstile> S' <: U'"
  using H subtype_reflexivity_from_typing [OF H] fresh
  by (rule TAbs_type)

theorem preservation: \<comment> \<open>A.20\<close>
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t \<longmapsto> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : T" using H
proof (nominal_induct avoiding: t' rule: typing.strong_induct)
  case (T_App \<Gamma> t\<^sub>1 T\<^sub>11 T\<^sub>12 t\<^sub>2 t')
  obtain x::vrs where x_fresh: "x \<sharp> (\<Gamma>, t\<^sub>1 \<cdot> t\<^sub>2, t')"
    by (rule exists_fresh) (rule fin_supp)
  obtain X::tyvrs where "X \<sharp> (t\<^sub>1 \<cdot> t\<^sub>2, t')"
    by (rule exists_fresh) (rule fin_supp)
  with \<open>t\<^sub>1 \<cdot> t\<^sub>2 \<longmapsto> t'\<close> show ?case
  proof (cases rule: eval.strong_cases [where x=x and X=X])
    case (E_Abs v\<^sub>2 T\<^sub>11' t\<^sub>12)
    with T_App and x_fresh have h: "\<Gamma> \<turnstile> (\<lambda>x:T\<^sub>11'. t\<^sub>12) : T\<^sub>11 \<rightarrow> T\<^sub>12"
      by (simp add: trm.inject fresh_prod)
    moreover from x_fresh have "x \<sharp> \<Gamma>" by simp
    ultimately obtain S'
      where T\<^sub>11: "\<Gamma> \<turnstile> T\<^sub>11 <: T\<^sub>11'"
      and t\<^sub>12: "(VarB x T\<^sub>11') # \<Gamma> \<turnstile> t\<^sub>12 : S'"
      and S': "\<Gamma> \<turnstile> S' <: T\<^sub>12"
      by (rule Abs_type') blast
    from \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>11\<close>
    have "\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>11'" using T\<^sub>11 by (rule T_Sub)
    with t\<^sub>12 have "\<Gamma> \<turnstile> t\<^sub>12[x \<leadsto> t\<^sub>2] : S'" 
      by (rule subst_type [where \<Delta>="[]", simplified])
    hence "\<Gamma> \<turnstile> t\<^sub>12[x \<leadsto> t\<^sub>2] : T\<^sub>12" using S' by (rule T_Sub)
    with E_Abs and x_fresh show ?thesis by (simp add: trm.inject fresh_prod)
  next
    case (E_App1 t''' t'' u)
    hence "t\<^sub>1 \<longmapsto> t''" by (simp add:trm.inject) 
    hence "\<Gamma> \<turnstile> t'' : T\<^sub>11 \<rightarrow> T\<^sub>12" by (rule T_App)
    hence "\<Gamma> \<turnstile> t'' \<cdot> t\<^sub>2 : T\<^sub>12" using \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>11\<close>
      by (rule typing.T_App)
    with E_App1 show ?thesis by (simp add:trm.inject)
  next
    case (E_App2 v t''' t'')
    hence "t\<^sub>2 \<longmapsto> t''" by (simp add:trm.inject) 
    hence "\<Gamma> \<turnstile> t'' : T\<^sub>11" by (rule T_App)
    with T_App(1) have "\<Gamma> \<turnstile> t\<^sub>1 \<cdot> t'' : T\<^sub>12"
      by (rule typing.T_App)
    with E_App2 show ?thesis by (simp add:trm.inject) 
  qed (simp_all add: fresh_prod)
next
  case (T_TApp X \<Gamma> t\<^sub>1 T\<^sub>2  T\<^sub>11  T\<^sub>12 t')
  obtain x::vrs where "x \<sharp> (t\<^sub>1 \<cdot>\<^sub>\<tau> T\<^sub>2, t')"
    by (rule exists_fresh) (rule fin_supp)
  with \<open>t\<^sub>1 \<cdot>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof (cases rule: eval.strong_cases [where X=X and x=x])
    case (E_TAbs T\<^sub>11' T\<^sub>2' t\<^sub>12)
    with T_TApp have "\<Gamma> \<turnstile> (\<lambda>X<:T\<^sub>11'. t\<^sub>12) : (\<forall>X<:T\<^sub>11. T\<^sub>12)" and "X \<sharp> \<Gamma>" and "X \<sharp> T\<^sub>11'"
      by (simp_all add: trm.inject)
    moreover from \<open>\<Gamma>\<turnstile>T\<^sub>2<:T\<^sub>11\<close> and \<open>X \<sharp> \<Gamma>\<close> have "X \<sharp> T\<^sub>11"
      by (blast intro: closed_in_fresh fresh_dom dest: subtype_implies_closed)
    ultimately obtain S'
      where "TVarB X T\<^sub>11 # \<Gamma> \<turnstile> t\<^sub>12 : S'"
      and "(TVarB X T\<^sub>11 # \<Gamma>) \<turnstile> S' <: T\<^sub>12"
      by (rule TAbs_type') blast
    hence "TVarB X T\<^sub>11 # \<Gamma> \<turnstile> t\<^sub>12 : T\<^sub>12" by (rule T_Sub)
    hence "\<Gamma> \<turnstile> t\<^sub>12[X \<leadsto>\<^sub>\<tau> T\<^sub>2] : T\<^sub>12[X \<leadsto> T\<^sub>2]\<^sub>\<tau>" using \<open>\<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>11\<close>
      by (rule substT_type [where D="[]", simplified])
    with T_TApp and E_TAbs show ?thesis by (simp add: trm.inject)
  next
    case (E_TApp t''' t'' T)
    from E_TApp have "t\<^sub>1 \<longmapsto> t''" by (simp add: trm.inject)
    then have "\<Gamma> \<turnstile> t'' : (\<forall>X<:T\<^sub>11. T\<^sub>12)" by (rule T_TApp)
    then have "\<Gamma> \<turnstile> t'' \<cdot>\<^sub>\<tau> T\<^sub>2 : T\<^sub>12[X \<leadsto> T\<^sub>2]\<^sub>\<tau>" using \<open>\<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>11\<close>
      by (rule better_T_TApp)
    with E_TApp show ?thesis by (simp add: trm.inject)
  qed (simp_all add: fresh_prod)
next
  case (T_Sub \<Gamma> t S T t')
  have "t \<longmapsto> t'" by fact
  hence "\<Gamma> \<turnstile> t' : S" by (rule T_Sub)
  moreover have "\<Gamma> \<turnstile> S <: T" by fact
  ultimately show ?case by (rule typing.T_Sub)
qed (auto)

lemma Fun_canonical: \<comment> \<open>A.14(1)\<close>
  assumes ty: "[] \<turnstile> v : T\<^sub>1 \<rightarrow> T\<^sub>2"
  shows "val v \<Longrightarrow> \<exists>x t S. v = (\<lambda>x:S. t)" using ty
proof (induct "[]::env" v "T\<^sub>1 \<rightarrow> T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2)
  case (T_Sub t S)
  from \<open>[] \<turnstile> S <: T\<^sub>1 \<rightarrow> T\<^sub>2\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = S\<^sub>1 \<rightarrow> S\<^sub>2" 
    by cases (auto simp: T_Sub)
  then show ?case using \<open>val t\<close> by (rule T_Sub)
qed (auto)

lemma TyAll_canonical: \<comment> \<open>A.14(3)\<close>
  fixes X::tyvrs
  assumes ty: "[] \<turnstile> v : (\<forall>X<:T\<^sub>1. T\<^sub>2)"
  shows "val v \<Longrightarrow> \<exists>X t S. v = (\<lambda>X<:S. t)" using ty
proof (induct "[]::env" v "\<forall>X<:T\<^sub>1. T\<^sub>2" arbitrary: X T\<^sub>1 T\<^sub>2)
  case (T_Sub t S)
  from \<open>[] \<turnstile> S <: (\<forall>X<:T\<^sub>1. T\<^sub>2)\<close>
  obtain X S\<^sub>1 S\<^sub>2 where S: "S = (\<forall>X<:S\<^sub>1. S\<^sub>2)"
    by cases (auto simp: T_Sub)
  then show ?case using T_Sub by auto 
qed (auto)

theorem progress:
  assumes "[] \<turnstile> t : T"
  shows "val t \<or> (\<exists>t'. t \<longmapsto> t')" 
using assms
proof (induct "[]::env" t T)
  case (T_App t\<^sub>1 T\<^sub>11  T\<^sub>12 t\<^sub>2)
  hence "val t\<^sub>1 \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^sub>1_val: "val t\<^sub>1"
    with T_App obtain x t3 S where t\<^sub>1: "t\<^sub>1 = (\<lambda>x:S. t3)"
      by (auto dest!: Fun_canonical)
    from T_App have "val t\<^sub>2 \<or> (\<exists>t'. t\<^sub>2 \<longmapsto> t')" by simp
    thus ?case
    proof
      assume "val t\<^sub>2"
      with t\<^sub>1 have "t\<^sub>1 \<cdot> t\<^sub>2 \<longmapsto> t3[x \<leadsto> t\<^sub>2]" by auto
      thus ?case by auto
    next
      assume "\<exists>t'. t\<^sub>2 \<longmapsto> t'"
      then obtain t' where "t\<^sub>2 \<longmapsto> t'" by auto
      with t\<^sub>1_val have "t\<^sub>1 \<cdot> t\<^sub>2 \<longmapsto> t\<^sub>1 \<cdot> t'" by auto
      thus ?case by auto
    qed
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" by auto
    hence "t\<^sub>1 \<cdot> t\<^sub>2 \<longmapsto> t' \<cdot> t\<^sub>2" by auto
    thus ?case by auto
  qed
next
  case (T_TApp X t\<^sub>1 T\<^sub>2 T\<^sub>11 T\<^sub>12)
  hence "val t\<^sub>1 \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume "val t\<^sub>1"
    with T_TApp obtain x t S where "t\<^sub>1 = (\<lambda>x<:S. t)"
      by (auto dest!: TyAll_canonical)
    hence "t\<^sub>1 \<cdot>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t[x \<leadsto>\<^sub>\<tau> T\<^sub>2]" by auto
    thus ?case by auto
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'" thus ?case by auto
  qed
qed (auto)

end
