subsection \<open>Definite Assignment\<close>

theory DefiniteAssignment imports WellType begin 

text \<open>Definite Assignment Analysis (cf. 16)

The definite assignment analysis approximates the sets of local 
variables that will be assigned at a certain point of evaluation, and ensures
that we will only read variables which previously were assigned.
It should conform to the following idea:
 If the evaluation of a term completes normally (no abruption (exception, 
break, continue, return) appeared) , the set of local variables calculated 
by the analysis is a subset of the
variables that were actually assigned during evaluation.

To get more precise information about the sets of assigned variables the 
analysis includes the following optimisations:
\begin{itemize}
  \item Inside of a while loop we also take care of the variables assigned
        before break statements, since the break causes the while loop to
        continue normally.
  \item For conditional statements we take care of constant conditions to 
        statically determine the path of evaluation.
  \item Inside a distinct path of a conditional statements we know to which
        boolean value the condition has evaluated to, and so can retrieve more
        information about the variables assigned during evaluation of the
        boolean condition.
\end{itemize}

Since in our model of Java the return values of methods are stored in a local
variable we also ensure that every path of (normal) evaluation will assign the
result variable, or in the sense of real Java every path ends up in and 
return instruction. 

Not covered yet:
\begin{itemize} 
  \item analysis of definite unassigned
  \item special treatment of final fields
\end{itemize}
\<close>

subsubsection \<open>Correct nesting of jump statements\<close>

text \<open>For definite assignment it becomes crucial, that jumps (break, 
continue, return) are nested correctly i.e. a continue jump is nested in a
matching while statement, a break jump is nested in a proper label statement,
a class initialiser does not terminate abruptly with a return. With this we 
can for example ensure that evaluation of an expression will never end up 
with a jump, since no breaks, continues or returns are allowed in an 
expression.\<close>

primrec jumpNestingOkS :: "jump set \<Rightarrow> stmt \<Rightarrow> bool"
where
  "jumpNestingOkS jmps (Skip)   = True"
| "jumpNestingOkS jmps (Expr e) = True"
| "jumpNestingOkS jmps (j\<bullet> s) = jumpNestingOkS ({j} \<union> jmps) s"
| "jumpNestingOkS jmps (c1;;c2) = (jumpNestingOkS jmps c1 \<and> 
                                   jumpNestingOkS jmps c2)"
| "jumpNestingOkS jmps (If(e) c1 Else c2) = (jumpNestingOkS jmps c1 \<and>  
                                             jumpNestingOkS jmps c2)"
| "jumpNestingOkS jmps (l\<bullet> While(e) c) = jumpNestingOkS ({Cont l} \<union> jmps) c"
\<comment> \<open>The label of the while loop only handles continue jumps. Breaks are only
     handled by \<^term>\<open>Lab\<close>\<close>
| "jumpNestingOkS jmps (Jmp j) = (j \<in> jmps)"
| "jumpNestingOkS jmps (Throw e) = True"
| "jumpNestingOkS jmps (Try c1 Catch(C vn) c2) = (jumpNestingOkS jmps c1 \<and> 
                                                  jumpNestingOkS jmps c2)"
| "jumpNestingOkS jmps (c1 Finally c2) = (jumpNestingOkS jmps c1 \<and> 
                                          jumpNestingOkS jmps c2)"
| "jumpNestingOkS jmps (Init C) = True" 
 \<comment> \<open>wellformedness of the program must enshure that for all initializers 
      jumpNestingOkS {} holds\<close> 
\<comment> \<open>Dummy analysis for intermediate smallstep term \<^term>\<open>FinA\<close>\<close>
| "jumpNestingOkS jmps (FinA a c) = False"


definition jumpNestingOk :: "jump set \<Rightarrow> term \<Rightarrow> bool" where
"jumpNestingOk jmps t = (case t of
                      In1 se \<Rightarrow> (case se of
                                   Inl e \<Rightarrow> True
                                 | Inr s \<Rightarrow> jumpNestingOkS jmps s)
                    | In2  v \<Rightarrow> True
                    | In3  es \<Rightarrow> True)"

lemma jumpNestingOk_expr_simp [simp]: "jumpNestingOk jmps (In1l e) = True"
by (simp add: jumpNestingOk_def)

lemma jumpNestingOk_expr_simp1 [simp]: "jumpNestingOk jmps \<langle>e::expr\<rangle> = True"
by (simp add: inj_term_simps)

lemma jumpNestingOk_stmt_simp [simp]: 
  "jumpNestingOk jmps (In1r s) = jumpNestingOkS jmps s"
by (simp add: jumpNestingOk_def)

lemma jumpNestingOk_stmt_simp1 [simp]: 
   "jumpNestingOk jmps \<langle>s::stmt\<rangle> = jumpNestingOkS jmps s"
by (simp add: inj_term_simps)

lemma jumpNestingOk_var_simp [simp]: "jumpNestingOk jmps (In2 v) = True"
by (simp add: jumpNestingOk_def)

lemma jumpNestingOk_var_simp1 [simp]: "jumpNestingOk jmps \<langle>v::var\<rangle> = True"
by (simp add: inj_term_simps)

lemma jumpNestingOk_expr_list_simp [simp]: "jumpNestingOk jmps (In3 es) = True"
by (simp add: jumpNestingOk_def)

lemma jumpNestingOk_expr_list_simp1 [simp]: 
  "jumpNestingOk jmps \<langle>es::expr list\<rangle> = True"
by (simp add: inj_term_simps)



subsubsection \<open>Calculation of assigned variables for boolean expressions\<close>


subsection \<open>Very restricted calculation fallback calculation\<close>

primrec the_LVar_name :: "var \<Rightarrow> lname"
  where "the_LVar_name (LVar n) = n"

primrec assignsE :: "expr \<Rightarrow> lname set" 
  and assignsV :: "var \<Rightarrow> lname set"
  and assignsEs:: "expr list \<Rightarrow> lname set"
where
  "assignsE (NewC c)            = {}" 
| "assignsE (NewA t e)          = assignsE e"
| "assignsE (Cast t e)          = assignsE e"
| "assignsE (e InstOf r)        = assignsE e"
| "assignsE (Lit val)           = {}"
| "assignsE (UnOp unop e)       = assignsE e"
| "assignsE (BinOp binop e1 e2) = (if binop=CondAnd \<or> binop=CondOr
                                       then (assignsE e1)
                                       else (assignsE e1) \<union> (assignsE e2))" 
| "assignsE (Super)             = {}"
| "assignsE (Acc v)             = assignsV v"
| "assignsE (v:=e)              = (assignsV v) \<union> (assignsE e) \<union> 
                                   (if \<exists> n. v=(LVar n) then {the_LVar_name v} 
                                                       else {})"
| "assignsE (b? e1 : e2) = (assignsE b) \<union> ((assignsE e1) \<inter> (assignsE e2))"
| "assignsE ({accC,statT,mode}objRef\<cdot>mn({pTs}args)) 
                            = (assignsE objRef) \<union> (assignsEs args)"
\<comment> \<open>Only dummy analysis for intermediate expressions  
      \<^term>\<open>Methd\<close>, \<^term>\<open>Body\<close>, \<^term>\<open>InsInitE\<close> and \<^term>\<open>Callee\<close>\<close>
| "assignsE (Methd C sig)   = {}" 
| "assignsE (Body  C s)     = {}"   
| "assignsE (InsInitE s e)  = {}"  
| "assignsE (Callee l e)    = {}" 

| "assignsV (LVar n)       = {}"
| "assignsV ({accC,statDeclC,stat}objRef..fn) = assignsE objRef"
| "assignsV (e1.[e2])      = assignsE e1 \<union> assignsE e2"

| "assignsEs     [] = {}"
| "assignsEs (e#es) = assignsE e \<union> assignsEs es"

definition assigns :: "term \<Rightarrow> lname set" where
"assigns t = (case t of
                In1 se \<Rightarrow> (case se of
                             Inl e \<Rightarrow> assignsE e
                           | Inr s \<Rightarrow> {})
              | In2  v \<Rightarrow> assignsV v
              | In3  es \<Rightarrow> assignsEs es)"

lemma assigns_expr_simp [simp]: "assigns (In1l e) = assignsE e"
by (simp add: assigns_def)

lemma assigns_expr_simp1 [simp]: "assigns (\<langle>e\<rangle>) = assignsE e"
by (simp add: inj_term_simps)

lemma assigns_stmt_simp [simp]: "assigns (In1r s) = {}"
by (simp add: assigns_def)

lemma assigns_stmt_simp1 [simp]: "assigns (\<langle>s::stmt\<rangle>) = {}"
by (simp add: inj_term_simps)

lemma assigns_var_simp [simp]: "assigns (In2 v) = assignsV v"
by (simp add: assigns_def)

lemma assigns_var_simp1 [simp]: "assigns (\<langle>v\<rangle>) = assignsV v"
by (simp add: inj_term_simps)

lemma assigns_expr_list_simp [simp]: "assigns (In3 es) = assignsEs es"
by (simp add: assigns_def)

lemma assigns_expr_list_simp1 [simp]: "assigns (\<langle>es\<rangle>) = assignsEs es"
by (simp add: inj_term_simps)

subsection "Analysis of constant expressions"

primrec constVal :: "expr \<Rightarrow> val option"
where
  "constVal (NewC c)      = None"
| "constVal (NewA t e)    = None"
| "constVal (Cast t e)    = None"
| "constVal (Inst e r)    = None"
| "constVal (Lit val)     = Some val"
| "constVal (UnOp unop e) = (case (constVal e) of
                               None   \<Rightarrow> None
                             | Some v \<Rightarrow> Some (eval_unop unop v))" 
| "constVal (BinOp binop e1 e2) = (case (constVal e1) of
                                     None    \<Rightarrow> None
                                   | Some v1 \<Rightarrow> (case (constVal e2) of 
                                                  None    \<Rightarrow> None
                                                | Some v2 \<Rightarrow> Some (eval_binop 
                                                                   binop v1 v2)))"
| "constVal (Super)         = None"
| "constVal (Acc v)         = None"
| "constVal (Ass v e)       = None"
| "constVal (Cond b e1 e2)  = (case (constVal b) of
                                 None   \<Rightarrow> None
                               | Some bv\<Rightarrow> (case the_Bool bv of
                                              True \<Rightarrow> (case (constVal e2) of
                                                         None   \<Rightarrow> None
                                                       | Some v \<Rightarrow> constVal e1)
                                            | False\<Rightarrow> (case (constVal e1) of
                                                         None   \<Rightarrow> None
                                                       | Some v \<Rightarrow> constVal e2)))"
\<comment> \<open>Note that \<open>constVal (Cond b e1 e2)\<close> is stricter as it could be.
     It requires that all tree expressions are constant even if we can decide
     which branch to choose, provided the constant value of \<^term>\<open>b\<close>\<close>
| "constVal (Call accC statT mode objRef mn pTs args) = None"
| "constVal (Methd C sig)   = None" 
| "constVal (Body  C s)     = None"   
| "constVal (InsInitE s e)  = None"  
| "constVal (Callee l e)    = None" 

lemma constVal_Some_induct [consumes 1, case_names Lit UnOp BinOp CondL CondR]: 
  assumes const: "constVal e = Some v" and
        hyp_Lit: "\<And> v. P (Lit v)" and
       hyp_UnOp: "\<And> unop e'. P e' \<Longrightarrow> P (UnOp unop e')" and
      hyp_BinOp: "\<And> binop e1 e2. \<lbrakk>P e1; P e2\<rbrakk> \<Longrightarrow> P (BinOp binop e1 e2)" and
      hyp_CondL: "\<And> b bv e1 e2. \<lbrakk>constVal b = Some bv; the_Bool bv; P b; P e1\<rbrakk> 
                              \<Longrightarrow> P (b? e1 : e2)" and
      hyp_CondR: "\<And> b bv e1 e2. \<lbrakk>constVal b = Some bv; \<not>the_Bool bv; P b; P e2\<rbrakk>
                              \<Longrightarrow> P (b? e1 : e2)"
  shows "P e"
proof -
  have "\<And> v. constVal e = Some v \<Longrightarrow> P e"
  proof (induct e)
    case Lit
    show ?case by (rule hyp_Lit)
  next
    case UnOp
    thus ?case
      by (auto intro: hyp_UnOp)
  next
    case BinOp
    thus ?case
      by (auto intro: hyp_BinOp)
  next
    case (Cond b e1 e2)
    then obtain v where   v: "constVal (b ? e1 : e2) = Some v"
      by blast
    then obtain bv where bv: "constVal b = Some bv"
      by simp
    show ?case
    proof (cases "the_Bool bv")
      case True
      with Cond show ?thesis using v bv
        by (auto intro: hyp_CondL)
    next
      case False
      with Cond show ?thesis using v bv
        by (auto intro: hyp_CondR)
    qed
  qed (simp_all add: hyp_Lit)
  with const 
  show ?thesis
    by blast  
qed

lemma assignsE_const_simp: "constVal e = Some v \<Longrightarrow> assignsE e = {}"
  by (induct rule: constVal_Some_induct) simp_all


subsection \<open>Main analysis for boolean expressions\<close>

text \<open>Assigned local variables after evaluating the expression if it evaluates
to a specific boolean value. If the expression cannot evaluate to a 
\<^term>\<open>Boolean\<close> value UNIV is returned. If we expect true/false the opposite 
constant false/true will also lead to UNIV.\<close>
primrec assigns_if :: "bool \<Rightarrow> expr \<Rightarrow> lname set"
where
  "assigns_if b (NewC c)            = UNIV" \<comment> \<open>can never evaluate to Boolean\<close> 
| "assigns_if b (NewA t e)          = UNIV" \<comment> \<open>can never evaluate to Boolean\<close>
| "assigns_if b (Cast t e)          = assigns_if b e" 
| "assigns_if b (Inst e r)          = assignsE e" \<comment> \<open>Inst has type Boolean but
                                                       e is a reference type\<close>
| "assigns_if b (Lit val)           = (if val=Bool b then {} else UNIV)"  
| "assigns_if b (UnOp unop e)       = (case constVal (UnOp unop e) of
                                           None   \<Rightarrow> (if unop = UNot 
                                                         then assigns_if (\<not>b) e
                                                         else UNIV)
                                         | Some v \<Rightarrow> (if v=Bool b 
                                                         then {} 
                                                         else UNIV))"
| "assigns_if b (BinOp binop e1 e2) 
    = (case constVal (BinOp binop e1 e2) of
         None \<Rightarrow> (if binop=CondAnd then
                     (case b of 
                         True  \<Rightarrow> assigns_if True  e1 \<union> assigns_if True e2
                      |  False \<Rightarrow> assigns_if False e1 \<inter> 
                                  (assigns_if True e1 \<union> assigns_if False e2))
                  else
                 (if binop=CondOr then
                     (case b of 
                         True  \<Rightarrow> assigns_if True e1 \<inter> 
                                  (assigns_if False e1 \<union> assigns_if True e2)
                      |  False \<Rightarrow> assigns_if False  e1 \<union> assigns_if False e2)
                  else assignsE e1 \<union> assignsE e2))
       | Some v \<Rightarrow> (if v=Bool b then {} else UNIV))"

| "assigns_if b (Super)      = UNIV" \<comment> \<open>can never evaluate to Boolean\<close>
| "assigns_if b (Acc v)      = (assignsV v)"
| "assigns_if b (v := e)     = (assignsE (Ass v e))"
| "assigns_if b (c? e1 : e2) = (assignsE c) \<union>
                                 (case (constVal c) of
                                    None    \<Rightarrow> (assigns_if b e1) \<inter> 
                                               (assigns_if b e2)
                                  | Some bv \<Rightarrow> (case the_Bool bv of
                                                  True  \<Rightarrow> assigns_if b e1
                                                | False \<Rightarrow> assigns_if b e2))"
| "assigns_if b ({accC,statT,mode}objRef\<cdot>mn({pTs}args))  
            = assignsE ({accC,statT,mode}objRef\<cdot>mn({pTs}args)) "
\<comment> \<open>Only dummy analysis for intermediate expressions  
      \<^term>\<open>Methd\<close>, \<^term>\<open>Body\<close>, \<^term>\<open>InsInitE\<close> and \<^term>\<open>Callee\<close>\<close>
| "assigns_if b (Methd C sig)   = {}" 
| "assigns_if b (Body  C s)     = {}"   
| "assigns_if b (InsInitE s e)  = {}"  
| "assigns_if b (Callee l e)    = {}" 

lemma assigns_if_const_b_simp:
  assumes boolConst: "constVal e = Some (Bool b)" (is "?Const b e")
  shows   "assigns_if b e = {}" (is "?Ass b e")
proof -
  have "\<And> b. ?Const b e \<Longrightarrow> ?Ass b e"
  proof (induct e)
    case Lit
    thus ?case by simp
  next
    case UnOp 
    thus ?case by simp
  next 
    case (BinOp binop)
    thus ?case
      by (cases binop) (simp_all)
  next
    case (Cond c e1 e2 b)
    note hyp_c = \<open>\<And> b. ?Const b c \<Longrightarrow> ?Ass b c\<close>
    note hyp_e1 = \<open>\<And> b. ?Const b e1 \<Longrightarrow> ?Ass b e1\<close>
    note hyp_e2 = \<open>\<And> b. ?Const b e2 \<Longrightarrow> ?Ass b e2\<close>
    note const = \<open>constVal (c ? e1 : e2) = Some (Bool b)\<close>
    then obtain bv where bv: "constVal c = Some bv"
      by simp
    hence emptyC: "assignsE c = {}" by (rule assignsE_const_simp)
    show ?case
    proof (cases "the_Bool bv")
      case True
      with const bv  
      have "?Const b e1" by simp
      hence "?Ass b e1" by (rule hyp_e1)
      with emptyC bv True
      show ?thesis
        by simp
    next
      case False
      with const bv  
      have "?Const b e2" by simp
      hence "?Ass b e2" by (rule hyp_e2)
      with emptyC bv False
      show ?thesis
        by simp
    qed
  qed (simp_all)
  with boolConst
  show ?thesis
    by blast
qed

lemma assigns_if_const_not_b_simp:
  assumes boolConst: "constVal e = Some (Bool b)"        (is "?Const b e")  
  shows "assigns_if (\<not>b) e = UNIV"                  (is "?Ass b e")
proof -
  have "\<And> b. ?Const b e \<Longrightarrow> ?Ass b e"
  proof (induct e)
    case Lit
    thus ?case by simp
  next
    case UnOp 
    thus ?case by simp
  next 
    case (BinOp binop)
    thus ?case
      by (cases binop) (simp_all)
  next
    case (Cond c e1 e2 b)
    note hyp_c = \<open>\<And> b. ?Const b c \<Longrightarrow> ?Ass b c\<close>
    note hyp_e1 = \<open>\<And> b. ?Const b e1 \<Longrightarrow> ?Ass b e1\<close>
    note hyp_e2 = \<open>\<And> b. ?Const b e2 \<Longrightarrow> ?Ass b e2\<close>
    note const = \<open>constVal (c ? e1 : e2) = Some (Bool b)\<close>
    then obtain bv where bv: "constVal c = Some bv"
      by simp
    show ?case
    proof (cases "the_Bool bv")
      case True
      with const bv  
      have "?Const b e1" by simp
      hence "?Ass b e1" by (rule hyp_e1)
      with bv True
      show ?thesis
        by simp
    next
      case False
      with const bv  
      have "?Const b e2" by simp
      hence "?Ass b e2" by (rule hyp_e2)
      with bv False 
      show ?thesis
        by simp
    qed
  qed (simp_all)
  with boolConst
  show ?thesis
    by blast
qed

subsection \<open>Lifting set operations to range of tables (map to a set)\<close>

definition
  union_ts :: "('a,'b) tables \<Rightarrow> ('a,'b) tables \<Rightarrow> ('a,'b) tables" (\<open>_ \<Rightarrow>\<union> _\<close> [67,67] 65)
  where "A \<Rightarrow>\<union> B = (\<lambda> k. A k \<union> B k)"

definition
  intersect_ts :: "('a,'b) tables \<Rightarrow> ('a,'b) tables \<Rightarrow> ('a,'b) tables" (\<open>_ \<Rightarrow>\<inter>  _\<close> [72,72] 71)
  where "A \<Rightarrow>\<inter>  B = (\<lambda>k. A k \<inter> B k)"

definition
  all_union_ts :: "('a,'b) tables \<Rightarrow> 'b set \<Rightarrow> ('a,'b) tables" (infixl \<open>\<Rightarrow>\<union>\<^sub>\<forall>\<close> 40)
  where "(A \<Rightarrow>\<union>\<^sub>\<forall> B) = (\<lambda> k. A k \<union> B)"
  
subsubsection \<open>Binary union of tables\<close>

lemma union_ts_iff [simp]: "(c \<in> (A \<Rightarrow>\<union> B) k) = (c \<in> A k \<or>  c \<in> B k)"
  by (unfold union_ts_def) blast

lemma union_tsI1 [elim?]: "c \<in> A k \<Longrightarrow> c \<in> (A \<Rightarrow>\<union> B) k"
  by simp

lemma union_tsI2 [elim?]: "c \<in> B k \<Longrightarrow> c \<in> (A \<Rightarrow>\<union> B) k"
  by simp

lemma union_tsCI [intro!]: "(c \<notin> B k \<Longrightarrow> c \<in> A k) \<Longrightarrow> c \<in> (A \<Rightarrow>\<union> B) k"
  by auto

lemma union_tsE [elim!]: 
 "\<lbrakk>c \<in> (A \<Rightarrow>\<union> B) k; (c \<in> A k \<Longrightarrow> P); (c \<in> B k \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by (unfold union_ts_def) blast

subsubsection \<open>Binary intersection of tables\<close>

lemma intersect_ts_iff [simp]: "c \<in> (A \<Rightarrow>\<inter> B) k = (c \<in> A k \<and> c \<in> B k)"
  by (unfold intersect_ts_def) blast

lemma intersect_tsI [intro!]: "\<lbrakk>c \<in> A k; c \<in> B k\<rbrakk> \<Longrightarrow> c \<in>  (A \<Rightarrow>\<inter> B) k"
  by simp

lemma intersect_tsD1: "c \<in> (A \<Rightarrow>\<inter> B) k \<Longrightarrow> c \<in> A k"
  by simp

lemma intersect_tsD2: "c \<in> (A \<Rightarrow>\<inter> B) k \<Longrightarrow> c \<in> B k"
  by simp

lemma intersect_tsE [elim!]: 
   "\<lbrakk>c \<in> (A \<Rightarrow>\<inter> B) k; \<lbrakk>c \<in> A k; c \<in> B k\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp


subsubsection \<open>All-Union of tables and set\<close>

lemma all_union_ts_iff [simp]: "(c \<in> (A \<Rightarrow>\<union>\<^sub>\<forall> B) k) = (c \<in> A k \<or>  c \<in> B)"
  by (unfold all_union_ts_def) blast

lemma all_union_tsI1 [elim?]: "c \<in> A k \<Longrightarrow> c \<in> (A \<Rightarrow>\<union>\<^sub>\<forall> B) k"
  by simp

lemma all_union_tsI2 [elim?]: "c \<in> B \<Longrightarrow> c \<in> (A \<Rightarrow>\<union>\<^sub>\<forall> B) k"
  by simp

lemma all_union_tsCI [intro!]: "(c \<notin> B \<Longrightarrow> c \<in> A k) \<Longrightarrow> c \<in> (A \<Rightarrow>\<union>\<^sub>\<forall> B) k"
  by auto

lemma all_union_tsE [elim!]: 
 "\<lbrakk>c \<in> (A \<Rightarrow>\<union>\<^sub>\<forall> B) k; (c \<in> A k \<Longrightarrow> P); (c \<in> B \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by (unfold all_union_ts_def) blast


subsubsection "The rules of definite assignment"

 
type_synonym breakass = "(label, lname) tables" 
\<comment> \<open>Mapping from a break label, to the set of variables that will be assigned 
     if the evaluation terminates with this break\<close>
    
record assigned = 
         nrm :: "lname set" \<comment> \<open>Definetly assigned variables 
                                 for normal completion\<close>
         brk :: "breakass" \<comment> \<open>Definetly assigned variables for 
                                abrupt completion with a break\<close>

definition
  rmlab :: "'a \<Rightarrow> ('a,'b) tables \<Rightarrow> ('a,'b) tables"
  where "rmlab k A = (\<lambda>x. if x=k then UNIV else A x)"
 
(*
definition
  setbrk :: "breakass \<Rightarrow> assigned \<Rightarrow> breakass set" where
  "setbrk b A = {b} \<union> {a| a. a\<in> brk A \<and> lab a \<noteq> lab b}"
*)

definition
  range_inter_ts :: "('a,'b) tables \<Rightarrow> 'b set" (\<open>\<Rightarrow>\<Inter>_\<close> 80)
  where "\<Rightarrow>\<Inter>A = {x |x. \<forall> k. x \<in> A k}"

text \<open>
In \<open>E\<turnstile> B \<guillemotright>t\<guillemotright> A\<close>,
\<open>B\<close> denotes the ''assigned'' variables before evaluating term \<open>t\<close>,
whereas \<open>A\<close> denotes the ''assigned'' variables after evaluating term \<open>t\<close>.
The environment \<^term>\<open>E\<close> is only needed for the conditional \<open>_ ? _ : _\<close>.
The definite assignment rules refer to the typing rules here to
distinguish boolean and other expressions.
\<close>

inductive
  da :: "env \<Rightarrow> lname set \<Rightarrow> term \<Rightarrow> assigned \<Rightarrow> bool" (\<open>_\<turnstile> _ \<guillemotright>_\<guillemotright> _\<close> [65,65,65,65] 71)
where
  Skip: "Env\<turnstile> B \<guillemotright>\<langle>Skip\<rangle>\<guillemotright> \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr>"

| Expr: "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> A 
         \<Longrightarrow>  
         Env\<turnstile> B \<guillemotright>\<langle>Expr e\<rangle>\<guillemotright> A"
| Lab:  "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>c\<rangle>\<guillemotright> C; nrm A = nrm C \<inter> (brk C) l; brk A = rmlab l (brk C)\<rbrakk>
         \<Longrightarrow> 
         Env\<turnstile> B \<guillemotright>\<langle>Break l\<bullet> c\<rangle>\<guillemotright> A" 

| Comp: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1; Env\<turnstile> nrm C1 \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2; 
         nrm A = nrm C2; brk A = (brk C1) \<Rightarrow>\<inter> (brk C2)\<rbrakk> 
         \<Longrightarrow>  
         Env\<turnstile> B \<guillemotright>\<langle>c1;; c2\<rangle>\<guillemotright> A"

| If:   "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E;
          Env\<turnstile> (B \<union> assigns_if True  e) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1;
          Env\<turnstile> (B \<union> assigns_if False e) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2;
          nrm A = nrm C1 \<inter> nrm C2;
          brk A = brk C1 \<Rightarrow>\<inter> brk C2 \<rbrakk>  
          \<Longrightarrow>
          Env\<turnstile> B \<guillemotright>\<langle>If(e) c1 Else c2\<rangle>\<guillemotright> A"

\<comment> \<open>Note that \<^term>\<open>E\<close> is not further used, because we take the specialized
     sets that also consider if the expression evaluates to true or false. 
     Inside of \<^term>\<open>e\<close> there is no {\tt break} or {\tt finally}, so the break
     map of \<^term>\<open>E\<close> will be the trivial one. So 
     \<^term>\<open>Env\<turnstile>B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E\<close> is just used to ensure the definite assignment in
     expression \<^term>\<open>e\<close>.
     Notice the implicit analysis of a constant boolean expression \<^term>\<open>e\<close>
     in this rule. For example, if \<^term>\<open>e\<close> is constantly \<^term>\<open>True\<close> then 
     \<^term>\<open>assigns_if False e = UNIV\<close> and therefor \<^term>\<open>nrm C2=UNIV\<close>.
     So finally \<^term>\<open>nrm A = nrm C1\<close>. For the break maps this trick 
     workd too, because the trivial break map will map all labels to 
     \<^term>\<open>UNIV\<close>. In the example, if no break occurs in \<^term>\<open>c2\<close> the break
     maps will trivially map to \<^term>\<open>UNIV\<close> and if a break occurs it will map
     to \<^term>\<open>UNIV\<close> too, because \<^term>\<open>assigns_if False e = UNIV\<close>. So
     in the intersection of the break maps the path \<^term>\<open>c2\<close> will have no
     contribution.\<close>

| Loop: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E; 
          Env\<turnstile> (B \<union> assigns_if True e) \<guillemotright>\<langle>c\<rangle>\<guillemotright> C;
          nrm A = nrm C \<inter> (B \<union> assigns_if False e);
          brk A = brk C\<rbrakk>  
          \<Longrightarrow>
          Env\<turnstile> B \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<guillemotright> A"
\<comment> \<open>The \<open>Loop\<close> rule resembles some of the ideas of the \<open>If\<close> rule.
     For the \<^term>\<open>nrm A\<close> the set \<^term>\<open>B \<union> assigns_if False e\<close> 
     will be \<^term>\<open>UNIV\<close> if the condition is constantly true. To normally exit
     the while loop, we must consider the body \<^term>\<open>c\<close> to be completed 
     normally (\<^term>\<open>nrm C\<close>) or with a break. But in this model, 
     the label \<^term>\<open>l\<close> of the loop
     only handles continue labels, not break labels. The break label will be
     handled by an enclosing \<^term>\<open>Lab\<close> statement. So we don't have to
     handle the breaks specially.\<close>

| Jmp: "\<lbrakk>jump=Ret \<longrightarrow> Result \<in> B;
         nrm A = UNIV;
         brk A = (case jump of
                    Break l \<Rightarrow> \<lambda> k. if k=l then B else UNIV     
                  | Cont l  \<Rightarrow> \<lambda> k. UNIV
                  | Ret     \<Rightarrow> \<lambda> k. UNIV)\<rbrakk> 
        \<Longrightarrow> 
        Env\<turnstile> B \<guillemotright>\<langle>Jmp jump\<rangle>\<guillemotright> A"
\<comment> \<open>In case of a break to label \<^term>\<open>l\<close> the corresponding break set is all
     variables assigned before the break. The assigned variables for normal
     completion of the \<^term>\<open>Jmp\<close> is \<^term>\<open>UNIV\<close>, because the statement will
     never complete normally. For continue and return the break map is the 
     trivial one. In case of a return we enshure that the result value is
     assigned.\<close>

| Throw: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E; nrm A = UNIV; brk A = (\<lambda> l. UNIV)\<rbrakk> 
         \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>Throw e\<rangle>\<guillemotright> A"

| Try:  "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1; 
          Env\<lparr>lcl := (lcl Env)(VName vn\<mapsto>Class C)\<rparr>\<turnstile> (B \<union> {VName vn}) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2;  
          nrm A = nrm C1 \<inter> nrm C2;
          brk A = brk C1 \<Rightarrow>\<inter> brk C2\<rbrakk> 
         \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>Try c1 Catch(C vn) c2\<rangle>\<guillemotright> A"

| Fin:  "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1;
          Env\<turnstile> B \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2;
          nrm A = nrm C1 \<union> nrm C2;
          brk A = ((brk C1) \<Rightarrow>\<union>\<^sub>\<forall> (nrm C2)) \<Rightarrow>\<inter> (brk C2)\<rbrakk>  
          \<Longrightarrow>
          Env\<turnstile> B \<guillemotright>\<langle>c1 Finally c2\<rangle>\<guillemotright> A" 
\<comment> \<open>The set of assigned variables before execution \<^term>\<open>c2\<close> are the same
     as before execution \<^term>\<open>c1\<close>, because \<^term>\<open>c1\<close> could throw an exception
     and so we can't guarantee that any variable will be assigned in \<^term>\<open>c1\<close>.
     The \<open>Finally\<close> statement completes
     normally if both \<^term>\<open>c1\<close> and \<^term>\<open>c2\<close> complete normally. If \<^term>\<open>c1\<close>
     completes abruptly with a break, then \<^term>\<open>c2\<close> also will be executed 
     and may terminate normally or with a break. The overall break map then is
     the intersection of the maps of both paths. If \<^term>\<open>c2\<close> terminates 
     normally we have to extend all break sets in \<^term>\<open>brk C1\<close> with 
     \<^term>\<open>nrm C2\<close> (\<open>\<Rightarrow>\<union>\<^sub>\<forall>\<close>). If \<^term>\<open>c2\<close> exits with a break this
     break will appear in the overall result state. We don't know if 
     \<^term>\<open>c1\<close> completed normally or abruptly (maybe with an exception not only
     a break) so \<^term>\<open>c1\<close> has no contribution to the break map following this
     path.\<close>

\<comment> \<open>Evaluation of expressions and the break sets of definite assignment:
     Thinking of a Java expression we assume that we can never have
     a break statement inside of a expression. So for all expressions the
     break sets could be set to the trivial one: \<^term>\<open>\<lambda> l. UNIV\<close>. 
     But we can't
     trivially proof, that evaluating an expression will never result in a 
     break, allthough Java expressions allready syntactically don't allow
     nested stetements in them. The reason are the nested class initialzation 
     statements which are inserted by the evaluation rules. So to proof the
     absence of a break we need to ensure, that the initialization statements
     will never end up in a break. In a wellfromed initialization statement, 
     of course, were breaks are nested correctly inside of \<^term>\<open>Lab\<close> 
     or \<^term>\<open>Loop\<close> statements evaluation of the whole initialization 
     statement will never result in a break, because this break will be 
     handled inside of the statement. But for simplicity we haven't added
     the analysis of the correct nesting of breaks in the typing judgments 
     right now. So we have decided to adjust the rules of definite assignment
     to fit to these circumstances. If an initialization is involved during
     evaluation of the expression (evaluation rules \<open>FVar\<close>, \<open>NewC\<close> 
     and \<open>NewA\<close>\<close>

| Init: "Env\<turnstile> B \<guillemotright>\<langle>Init C\<rangle>\<guillemotright> \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr>"
\<comment> \<open>Wellformedness of a program will ensure, that every static initialiser 
     is definetly assigned and the jumps are nested correctly. The case here
     for \<^term>\<open>Init\<close> is just for convenience, to get a proper precondition 
     for the induction hypothesis in various proofs, so that we don't have to
     expand the initialisation on every point where it is triggerred by the
     evaluation rules.\<close>   
| NewC: "Env\<turnstile> B \<guillemotright>\<langle>NewC C\<rangle>\<guillemotright> \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr>" 

| NewA: "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> A 
         \<Longrightarrow>
         Env\<turnstile> B \<guillemotright>\<langle>New T[e]\<rangle>\<guillemotright> A"

| Cast: "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> A
         \<Longrightarrow>
         Env\<turnstile> B \<guillemotright>\<langle>Cast T e\<rangle>\<guillemotright> A"

| Inst: "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> A 
         \<Longrightarrow> 
         Env\<turnstile> B \<guillemotright>\<langle>e InstOf T\<rangle>\<guillemotright> A"

| Lit:  "Env\<turnstile> B \<guillemotright>\<langle>Lit v\<rangle>\<guillemotright> \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr>"

| UnOp: "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> A
         \<Longrightarrow> 
         Env\<turnstile> B \<guillemotright>\<langle>UnOp unop e\<rangle>\<guillemotright> A"

| CondAnd: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1; Env\<turnstile> (B \<union> assigns_if True e1) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2; 
             nrm A = B \<union> (assigns_if True (BinOp CondAnd e1 e2) \<inter> 
                             assigns_if False (BinOp CondAnd e1 e2));
             brk A = (\<lambda> l. UNIV) \<rbrakk>
            \<Longrightarrow>
            Env\<turnstile> B \<guillemotright>\<langle>BinOp CondAnd e1 e2\<rangle>\<guillemotright> A"

| CondOr: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1; Env\<turnstile> (B \<union> assigns_if False e1) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2; 
            nrm A = B \<union> (assigns_if True (BinOp CondOr e1 e2) \<inter> 
                              assigns_if False (BinOp CondOr e1 e2));
            brk A = (\<lambda> l. UNIV) \<rbrakk>
            \<Longrightarrow>
            Env\<turnstile> B \<guillemotright>\<langle>BinOp CondOr e1 e2\<rangle>\<guillemotright> A"

| BinOp: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1; Env\<turnstile> nrm E1 \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A; 
           binop \<noteq> CondAnd; binop \<noteq> CondOr\<rbrakk>
          \<Longrightarrow>
          Env\<turnstile> B \<guillemotright>\<langle>BinOp binop e1 e2\<rangle>\<guillemotright> A"

| Super: "This \<in> B 
          \<Longrightarrow> 
          Env\<turnstile> B \<guillemotright>\<langle>Super\<rangle>\<guillemotright> \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr>"

| AccLVar: "\<lbrakk>vn \<in> B;
             nrm A = B; brk A = (\<lambda> k. UNIV)\<rbrakk> 
             \<Longrightarrow> 
             Env\<turnstile> B \<guillemotright>\<langle>Acc (LVar vn)\<rangle>\<guillemotright> A"
\<comment> \<open>To properly access a local variable we have to test the definite 
     assignment here. The variable must occur in the set \<^term>\<open>B\<close>\<close>

| Acc: "\<lbrakk>\<forall> vn. v \<noteq> LVar vn;
         Env\<turnstile> B \<guillemotright>\<langle>v\<rangle>\<guillemotright> A\<rbrakk>
         \<Longrightarrow>
         Env\<turnstile> B \<guillemotright>\<langle>Acc v\<rangle>\<guillemotright> A"

| AssLVar: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E; nrm A = nrm E \<union> {vn}; brk A = brk E\<rbrakk> 
            \<Longrightarrow> 
            Env\<turnstile> B \<guillemotright>\<langle>(LVar vn) := e\<rangle>\<guillemotright> A"

| Ass: "\<lbrakk>\<forall> vn. v \<noteq> LVar vn; Env\<turnstile> B \<guillemotright>\<langle>v\<rangle>\<guillemotright> V; Env\<turnstile> nrm V \<guillemotright>\<langle>e\<rangle>\<guillemotright> A\<rbrakk>
         \<Longrightarrow>
         Env\<turnstile> B \<guillemotright>\<langle>v := e\<rangle>\<guillemotright> A"

| CondBool: "\<lbrakk>Env\<turnstile>(c ? e1 : e2)\<Colon>-(PrimT Boolean);
              Env\<turnstile> B \<guillemotright>\<langle>c\<rangle>\<guillemotright> C;
              Env\<turnstile> (B \<union> assigns_if True  c) \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1;
              Env\<turnstile> (B \<union> assigns_if False c) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2;
              nrm A = B \<union> (assigns_if True  (c ? e1 : e2) \<inter> 
                               assigns_if False (c ? e1 : e2));
              brk A = (\<lambda> l. UNIV)\<rbrakk>
              \<Longrightarrow> 
              Env\<turnstile> B \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A" 

| Cond: "\<lbrakk>\<not> Env\<turnstile>(c ? e1 : e2)\<Colon>-(PrimT Boolean);
          Env\<turnstile> B \<guillemotright>\<langle>c\<rangle>\<guillemotright> C;
          Env\<turnstile> (B \<union> assigns_if True  c) \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1;
          Env\<turnstile> (B \<union> assigns_if False c) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2;
          nrm A = nrm E1 \<inter> nrm E2; brk A = (\<lambda> l. UNIV)\<rbrakk>
          \<Longrightarrow> 
          Env\<turnstile> B \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A" 

| Call: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E; Env\<turnstile> nrm E \<guillemotright>\<langle>args\<rangle>\<guillemotright> A\<rbrakk> 
         \<Longrightarrow>  
         Env\<turnstile> B \<guillemotright>\<langle>{accC,statT,mode}e\<cdot>mn({pTs}args)\<rangle>\<guillemotright> A"

\<comment> \<open>The interplay of \<^term>\<open>Call\<close>, \<^term>\<open>Methd\<close> and \<^term>\<open>Body\<close>:
      Why rules for \<^term>\<open>Methd\<close> and \<^term>\<open>Body\<close> at all? Note that a
      Java source program will not include bare  \<^term>\<open>Methd\<close> or \<^term>\<open>Body\<close>
      terms. These terms are just introduced during evaluation. So definite
      assignment of \<^term>\<open>Call\<close> does not consider \<^term>\<open>Methd\<close> or 
      \<^term>\<open>Body\<close> at all. So for definite assignment alone we could omit the
      rules for \<^term>\<open>Methd\<close> and \<^term>\<open>Body\<close>. 
      But since evaluation of the method invocation is
      split up into three rules we must ensure that we have enough information
      about the call even in the \<^term>\<open>Body\<close> term to make sure that we can
      proof type safety. Also we must be able transport this information 
      from \<^term>\<open>Call\<close> to \<^term>\<open>Methd\<close> and then further to \<^term>\<open>Body\<close> 
      during evaluation to establish the definite assignment of \<^term>\<open>Methd\<close>
      during evaluation of \<^term>\<open>Call\<close>, and of \<^term>\<open>Body\<close> during evaluation
      of \<^term>\<open>Methd\<close>. This is necessary since definite assignment will be
      a precondition for each induction hypothesis coming out of the evaluation
      rules, and therefor we have to establish the definite assignment of the
      sub-evaluation during the type-safety proof. Note that well-typedness is
      also a precondition for type-safety and so we can omit some assertion 
      that are already ensured by well-typedness.\<close>
| Methd: "\<lbrakk>methd (prg Env) D sig = Some m;
           Env\<turnstile> B \<guillemotright>\<langle>Body (declclass m) (stmt (mbody (mthd m)))\<rangle>\<guillemotright> A
          \<rbrakk>
          \<Longrightarrow>
          Env\<turnstile> B \<guillemotright>\<langle>Methd D sig\<rangle>\<guillemotright> A" 

| Body: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>c\<rangle>\<guillemotright> C; jumpNestingOkS {Ret} c; Result \<in> nrm C;
          nrm A = B; brk A = (\<lambda> l. UNIV)\<rbrakk>
         \<Longrightarrow>
         Env\<turnstile> B \<guillemotright>\<langle>Body D c\<rangle>\<guillemotright> A"
\<comment> \<open>Note that \<^term>\<open>A\<close> is not correlated to  \<^term>\<open>C\<close>. If the body
      statement returns abruptly with return, evaluation of  \<^term>\<open>Body\<close>
      will absorb this return and complete normally. So we cannot trivially
      get the assigned variables of the body statement since it has not 
      completed normally or with a break.
      If the body completes normally we guarantee that the result variable
      is set with this rule. But if the body completes abruptly with a return
      we can't guarantee that the result variable is set here, since 
      definite assignment only talks about normal completion and breaks. So
      for a return the \<^term>\<open>Jump\<close> rule ensures that the result variable is
      set and then this information must be carried over to the \<^term>\<open>Body\<close>
      rule by the conformance predicate of the state.\<close>
| LVar: "Env\<turnstile> B \<guillemotright>\<langle>LVar vn\<rangle>\<guillemotright> \<lparr>nrm=B, brk=\<lambda> l. UNIV\<rparr>" 

| FVar: "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> A 
         \<Longrightarrow> 
         Env\<turnstile> B \<guillemotright>\<langle>{accC,statDeclC,stat}e..fn\<rangle>\<guillemotright> A" 

| AVar: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1; Env\<turnstile> nrm E1 \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A\<rbrakk>
          \<Longrightarrow> 
          Env\<turnstile> B \<guillemotright>\<langle>e1.[e2]\<rangle>\<guillemotright> A" 

| Nil: "Env\<turnstile> B \<guillemotright>\<langle>[]::expr list\<rangle>\<guillemotright> \<lparr>nrm=B, brk=\<lambda> l. UNIV\<rparr>" 

| Cons: "\<lbrakk>Env\<turnstile> B \<guillemotright>\<langle>e::expr\<rangle>\<guillemotright> E; Env\<turnstile> nrm E \<guillemotright>\<langle>es\<rangle>\<guillemotright> A\<rbrakk>
         \<Longrightarrow> 
         Env\<turnstile> B \<guillemotright>\<langle>e#es\<rangle>\<guillemotright> A" 


declare inj_term_sym_simps [simp]
declare assigns_if.simps [simp del]
declare split_paired_All [simp del] split_paired_Ex [simp del]
setup \<open>map_theory_simpset (fn ctxt => ctxt |> Simplifier.del_loop "split_all_tac")\<close>

inductive_cases da_elim_cases [cases set]:
  "Env\<turnstile> B \<guillemotright>\<langle>Skip\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In1r Skip\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>Expr e\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (Expr e)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>l\<bullet> c\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (l\<bullet> c)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>c1;; c2\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (c1;; c2)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>If(e) c1 Else c2\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In1r (If(e) c1 Else c2)\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (l\<bullet> While(e) c)\<guillemotright> A"  
  "Env\<turnstile> B \<guillemotright>\<langle>Jmp jump\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (Jmp jump)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Throw e\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (Throw e)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Try c1 Catch(C vn) c2\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (Try c1 Catch(C vn) c2)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>c1 Finally c2\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In1r (c1 Finally c2)\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>Init C\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1r (Init C)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>NewC C\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (NewC C)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>New T[e]\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (New T[e])\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Cast T e\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (Cast T e)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>e InstOf T\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (e InstOf T)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Lit v\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (Lit v)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>UnOp unop e\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (UnOp unop e)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>BinOp binop e1 e2\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (BinOp binop e1 e2)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Super\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (Super)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Acc v\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (Acc v)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>v := e\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l (v := e)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In1l (c ? e1 : e2)\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>{accC,statT,mode}e\<cdot>mn({pTs}args)\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In1l ({accC,statT,mode}e\<cdot>mn({pTs}args))\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Methd C sig\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In1l (Methd C sig)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>Body D c\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In1l (Body D c)\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>LVar vn\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In2 (LVar vn)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>{accC,statDeclC,stat}e..fn\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In2 ({accC,statDeclC,stat}e..fn)\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>e1.[e2]\<rangle>\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>In2 (e1.[e2])\<guillemotright> A" 
  "Env\<turnstile> B \<guillemotright>\<langle>[]::expr list\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In3 ([]::expr list)\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>\<langle>e#es\<rangle>\<guillemotright> A"
  "Env\<turnstile> B \<guillemotright>In3 (e#es)\<guillemotright> A"
declare inj_term_sym_simps [simp del]
declare assigns_if.simps [simp]
declare split_paired_All [simp] split_paired_Ex [simp]
setup \<open>map_theory_simpset (fn ctxt => ctxt |> Simplifier.add_loop ("split_all_tac", split_all_tac))\<close>

(* To be able to eliminate both the versions with the overloaded brackets: 
   (B \<guillemotright>\<langle>Skip\<rangle>\<guillemotright> A) and with the explicit constructor (B \<guillemotright>In1r Skip\<guillemotright> A), 
   every rule appears in both versions
 *)

lemma da_Skip: "A = \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr> \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>Skip\<rangle>\<guillemotright> A"
  by (auto intro: da.Skip)

lemma da_NewC: "A = \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr> \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>NewC C\<rangle>\<guillemotright> A"
  by (auto intro: da.NewC)
 
lemma da_Lit:  "A = \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr> \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>Lit v\<rangle>\<guillemotright> A"
  by (auto intro: da.Lit)

lemma da_Super: "\<lbrakk>This \<in> B;A = \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr>\<rbrakk> \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>Super\<rangle>\<guillemotright> A"
  by (auto intro: da.Super)

lemma da_Init: "A = \<lparr>nrm=B,brk=\<lambda> l. UNIV\<rparr> \<Longrightarrow> Env\<turnstile> B \<guillemotright>\<langle>Init C\<rangle>\<guillemotright> A"
  by (auto intro: da.Init)


(*
For boolean expressions:

The following holds: "assignsE e \<subseteq> assigns_if True e \<inter> assigns_if False e"
but not vice versa:
 "assigns_if True e \<inter> assigns_if False e \<subseteq> assignsE e"

Example: 
 e = ((x < 5) || (y = true)) && (y = true)

   =  (   a    ||    b     ) &&    c

assigns_if True  a = {}
assigns_if False a = {}

assigns_if True  b = {y}
assigns_if False b = {y}

assigns_if True  c = {y}
assigns_if False c = {y}

assigns_if True (a || b) = assigns_if True a \<inter> 
                                (assigns_if False a \<union> assigns_if True b)
                           = {} \<inter> ({} \<union> {y}) = {}
assigns_if False (a || b) = assigns_if False a \<union> assigns_if False b
                            = {} \<union> {y} = {y}



assigns_ifE True e =  assigns_if True (a || b) \<union> assigns_if True c
                    = {} \<union> {y} = {y}
assigns_ifE False e = assigns_if False (a || b) \<inter> 
                       (assigns_if True (a || b) \<union> assigns_if False c)
                     = {y} \<inter> ({} \<union> {y}) = {y}

assignsE e = {}
*)  

lemma assignsE_subseteq_assigns_ifs:
 assumes boolEx: "E\<turnstile>e\<Colon>-PrimT Boolean" (is "?Boolean e")
   shows "assignsE e \<subseteq> assigns_if True e \<inter> assigns_if False e" (is "?Incl e")
proof -
  obtain vv where ex_lit: "E\<turnstile>Lit vv\<Colon>- PrimT Boolean"
    using typeof.simps(2) wt.Lit by blast
  have "?Boolean e \<Longrightarrow> ?Incl e"
  proof (induct e)
    case (Cast T e)
    have "E\<turnstile>e\<Colon>- (PrimT Boolean)"
    proof -
      from \<open>E\<turnstile>(Cast T e)\<Colon>- (PrimT Boolean)\<close>
      obtain Te where "E\<turnstile>e\<Colon>-Te"
                           "prg E\<turnstile>Te\<preceq>? PrimT Boolean"
        by cases simp
      thus ?thesis
        by - (drule cast_Boolean2,simp)
    qed
    with Cast.hyps
    show ?case
      by simp
  next  
    case (Lit val) 
    thus ?case
      by - (erule wt_elim_cases, cases "val", auto simp add: empty_dt_def)
  next
    case (UnOp unop e) 
    thus ?case
      by - (erule wt_elim_cases,cases unop,
            (fastforce simp add: assignsE_const_simp)+)
  next
    case (BinOp binop e1 e2)
    from BinOp.prems obtain e1T e2T
      where "E\<turnstile>e1\<Colon>-e1T" and "E\<turnstile>e2\<Colon>-e2T" and "wt_binop (prg E) binop e1T e2T"
            and "(binop_type binop) = Boolean"
      by (elim wt_elim_cases) simp
    with BinOp.hyps
    show ?case
      by (cases binop) (auto simp add: assignsE_const_simp)
  next
    case (Cond c e1 e2)
    note hyp_c = \<open>?Boolean c \<Longrightarrow> ?Incl c\<close>
    note hyp_e1 = \<open>?Boolean e1 \<Longrightarrow> ?Incl e1\<close>
    note hyp_e2 = \<open>?Boolean e2 \<Longrightarrow> ?Incl e2\<close>
    note wt = \<open>E\<turnstile>(c ? e1 : e2)\<Colon>-PrimT Boolean\<close>
    then obtain
      boolean_c:  "E\<turnstile>c\<Colon>-PrimT Boolean" and
      boolean_e1: "E\<turnstile>e1\<Colon>-PrimT Boolean" and
      boolean_e2: "E\<turnstile>e2\<Colon>-PrimT Boolean"
      by (elim wt_elim_cases) (auto dest: widen_Boolean2)
    show ?case
    proof (cases "constVal c")
      case None
      with boolean_e1 boolean_e2
      show ?thesis
        using hyp_e1 hyp_e2 
        by (auto)
    next
      case (Some bv)
      show ?thesis
      proof (cases "the_Bool bv")
        case True
        with Some show ?thesis using hyp_e1 boolean_e1 by auto
      next
        case False
        with Some show ?thesis using hyp_e2 boolean_e2 by auto
      qed
    qed
  next
    show "\<And>x. E\<turnstile>Lit vv\<Colon>-PrimT Boolean"
      by (rule ex_lit)
  qed (simp_all add: ex_lit)
  with boolEx 
  show ?thesis
    by blast
qed
  

(* Trick:
   If you have a rule with the abstract term injections:
   e.g:  da.Skip "B \<guillemotright>\<langle>Skip\<rangle>\<guillemotright> A"
   and the current goal state as an concrete injection:
   e.g: "B \<guillemotright>In1r Skip\<guillemotright> A"
   you can convert the rule by: da.Skip [simplified]
   if inj_term_simps is in the simpset

*)

lemma rmlab_same_label [simp]: "(rmlab l A) l = UNIV"
  by (simp add: rmlab_def)

lemma rmlab_same_label1 [simp]: "l=l' \<Longrightarrow> (rmlab l A) l' = UNIV"
  by (simp add: rmlab_def)

lemma rmlab_other_label [simp]: "l\<noteq>l'\<Longrightarrow> (rmlab l A) l' = A l'"
  by (auto simp add: rmlab_def)

lemma range_inter_ts_subseteq [intro]: "\<forall> k. A k \<subseteq> B k \<Longrightarrow> \<Rightarrow>\<Inter>A \<subseteq> \<Rightarrow>\<Inter>B"
  by (auto simp add: range_inter_ts_def)

lemma range_inter_ts_subseteq': "\<forall> k. A k \<subseteq> B k \<Longrightarrow> x \<in> \<Rightarrow>\<Inter>A \<Longrightarrow> x \<in> \<Rightarrow>\<Inter>B"
  by (auto simp add: range_inter_ts_def)

lemma da_monotone: 
  assumes da: "Env\<turnstile> B  \<guillemotright>t\<guillemotright> A" and
    "B \<subseteq> B'" and
    da': "Env\<turnstile> B' \<guillemotright>t\<guillemotright> A'" 
  shows "(nrm A \<subseteq> nrm A') \<and> (\<forall> l. (brk A l \<subseteq> brk A' l))"
proof -
  from da
  have "\<And> B' A'. \<lbrakk>Env\<turnstile> B' \<guillemotright>t\<guillemotright> A'; B \<subseteq> B'\<rbrakk> 
                  \<Longrightarrow> (nrm A \<subseteq> nrm A') \<and> (\<forall> l. (brk A l \<subseteq> brk A' l))"
       (is "PROP ?Hyp Env B t A")  
  proof (induct)
    case Skip 
    then show ?case by cases simp
  next
    case Expr 
    from Expr.prems Expr.hyps 
    show ?case by cases simp
  next
    case (Lab Env B c C A l B' A')
    note A = \<open>nrm A = nrm C \<inter> brk C l\<close> \<open>brk A = rmlab l (brk C)\<close>
    note \<open>PROP ?Hyp Env B \<langle>c\<rangle> C\<close>
    moreover
    note \<open>B \<subseteq> B'\<close>
    moreover
    obtain C'
      where "Env\<turnstile> B' \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'"
        and A': "nrm A' = nrm C' \<inter> brk C' l" "brk A' = rmlab l (brk C')"
      using Lab.prems
      by cases simp
    ultimately
    have "nrm C \<subseteq> nrm C'" and hyp_brk: "(\<forall>l. brk C l \<subseteq> brk C' l)" by auto
    then 
    have "nrm C \<inter> brk C l \<subseteq> nrm C' \<inter> brk C' l" by auto
    moreover
    from hyp_brk
    have "rmlab l (brk C) l'  \<subseteq> rmlab l (brk C') l'" for l'
      by  (cases "l=l'") simp_all
    moreover note A A'
    ultimately show ?case
      by simp
  next
    case (Comp Env B c1 C1 c2 C2 A B' A')
    note A = \<open>nrm A = nrm C2\<close> \<open>brk A = brk C1 \<Rightarrow>\<inter>  brk C2\<close>
    from \<open>Env\<turnstile> B' \<guillemotright>\<langle>c1;; c2\<rangle>\<guillemotright> A'\<close>
    obtain  C1' C2'
      where da_c1: "Env\<turnstile> B' \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'" and
            da_c2: "Env\<turnstile> nrm C1' \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'"  and
            A': "nrm A' = nrm C2'" "brk A' = brk C1' \<Rightarrow>\<inter>  brk C2'"
      by cases auto
    note \<open>PROP ?Hyp Env B \<langle>c1\<rangle> C1\<close>
    moreover note \<open>B \<subseteq> B'\<close>
    moreover note da_c1
    ultimately have C1': "nrm C1 \<subseteq> nrm C1'" "(\<forall>l. brk C1 l \<subseteq> brk C1' l)"
      by auto
    note \<open>PROP ?Hyp Env (nrm C1) \<langle>c2\<rangle> C2\<close>
    with da_c2 C1' 
    have C2': "nrm C2 \<subseteq> nrm C2'" "(\<forall>l. brk C2 l \<subseteq> brk C2' l)"
      by auto
    with A A' C1'
    show ?case
      by auto
  next
    case (If Env B e E c1 C1 c2 C2 A B' A')
    note A = \<open>nrm A = nrm C1 \<inter> nrm C2\<close> \<open>brk A = brk C1 \<Rightarrow>\<inter>  brk C2\<close>
    from \<open>Env\<turnstile> B' \<guillemotright>\<langle>If(e) c1 Else c2\<rangle>\<guillemotright> A'\<close>
    obtain C1' C2'
      where da_c1: "Env\<turnstile> B' \<union> assigns_if True e \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'" and
            da_c2: "Env\<turnstile> B' \<union> assigns_if False e \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'" and
               A': "nrm A' = nrm C1' \<inter> nrm C2'" "brk A' = brk C1' \<Rightarrow>\<inter>  brk C2'"
      by cases auto
    note \<open>PROP ?Hyp Env (B \<union> assigns_if True e) \<langle>c1\<rangle> C1\<close>
    moreover note B' = \<open>B \<subseteq> B'\<close>
    moreover note da_c1 
    ultimately obtain C1': "nrm C1 \<subseteq> nrm C1'" "(\<forall>l. brk C1 l \<subseteq> brk C1' l)"
      by blast
    note \<open>PROP ?Hyp Env (B \<union> assigns_if False e) \<langle>c2\<rangle> C2\<close>
    with da_c2 B'
    obtain C2': "nrm C2 \<subseteq> nrm C2'" "(\<forall>l. brk C2 l \<subseteq> brk C2' l)"
      by blast
    with A A' C1'
    show ?case
      by auto
  next
    case (Loop Env B e E c C A l B' A')
    note A = \<open>nrm A = nrm C \<inter> (B \<union> assigns_if False e)\<close> \<open>brk A = brk C\<close>
    from \<open>Env\<turnstile> B' \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<guillemotright> A'\<close>
    obtain C'
      where 
       da_c': "Env\<turnstile> B' \<union> assigns_if True e \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'" and
          A': "nrm A' = nrm C' \<inter> (B' \<union> assigns_if False e)"
              "brk A' = brk C'" 
      by cases auto
    note \<open>PROP ?Hyp Env (B \<union> assigns_if True e) \<langle>c\<rangle> C\<close>
    moreover note B' = \<open>B \<subseteq> B'\<close>
    moreover note da_c'
    ultimately obtain C': "nrm C \<subseteq> nrm C'" "(\<forall>l. brk C l \<subseteq> brk C' l)"
      by blast
    with A A' B'
    have "nrm A \<subseteq> nrm A'"
      by blast
    moreover
    have  "brk A l' \<subseteq> brk A' l'" for l'
    proof (cases "constVal e")
      case None
      with A A' C' 
      show ?thesis
        by (cases "l=l'") auto
    next
      case (Some bv)
      with A A' C'
      show ?thesis
        by (cases "the_Bool bv", cases "l=l'") auto
    qed
    ultimately show ?case
      by auto
  next
    case (Jmp jump B A Env B' A')
    thus ?case by (elim da_elim_cases) (auto split: jump.splits)
  next
    case Throw thus ?case by (elim da_elim_cases) auto
  next
    case (Try Env B c1 C1 vn C c2 C2 A B' A')
    note A = \<open>nrm A = nrm C1 \<inter> nrm C2\<close> \<open>brk A = brk C1 \<Rightarrow>\<inter>  brk C2\<close>
    from \<open>Env\<turnstile> B' \<guillemotright>\<langle>Try c1 Catch(C vn) c2\<rangle>\<guillemotright> A'\<close>
    obtain C1' C2'
      where da_c1': "Env\<turnstile> B' \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'" and
            da_c2': "Env\<lparr>lcl := (lcl Env)(VName vn\<mapsto>Class C)\<rparr>\<turnstile> B' \<union> {VName vn} 
                      \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'" and
            A': "nrm A' = nrm C1' \<inter> nrm C2'"
                "brk A' = brk C1' \<Rightarrow>\<inter>  brk C2'" 
      by cases auto
    note \<open>PROP ?Hyp Env B \<langle>c1\<rangle> C1\<close>
    moreover note B' = \<open>B \<subseteq> B'\<close>
    moreover note da_c1'
    ultimately obtain C1': "nrm C1 \<subseteq> nrm C1'" "(\<forall>l. brk C1 l \<subseteq> brk C1' l)"
      by blast
    note \<open>PROP ?Hyp (Env\<lparr>lcl := (lcl Env)(VName vn\<mapsto>Class C)\<rparr>)
                    (B \<union> {VName vn}) \<langle>c2\<rangle> C2\<close>
    with B' da_c2'
    obtain "nrm C2 \<subseteq> nrm C2'" "(\<forall>l. brk C2 l \<subseteq> brk C2' l)"
      by blast
    with C1' A A'
    show ?case
      by auto
  next
    case (Fin Env B c1 C1 c2 C2 A B' A')
    note A = \<open>nrm A = nrm C1 \<union> nrm C2\<close>
      \<open>brk A = (brk C1 \<Rightarrow>\<union>\<^sub>\<forall> nrm C2) \<Rightarrow>\<inter> (brk C2)\<close>
    from \<open>Env\<turnstile> B' \<guillemotright>\<langle>c1 Finally c2\<rangle>\<guillemotright> A'\<close>
    obtain C1' C2'
      where  da_c1': "Env\<turnstile> B' \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'" and
             da_c2': "Env\<turnstile> B' \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'" and
             A':  "nrm A' = nrm C1' \<union> nrm C2'"
                  "brk A' = (brk C1' \<Rightarrow>\<union>\<^sub>\<forall> nrm C2') \<Rightarrow>\<inter> (brk C2')"
      by cases auto
    note \<open>PROP ?Hyp Env B \<langle>c1\<rangle> C1\<close>
    moreover note B' = \<open>B \<subseteq> B'\<close>
    moreover note da_c1'
    ultimately obtain C1': "nrm C1 \<subseteq> nrm C1'" "(\<forall>l. brk C1 l \<subseteq> brk C1' l)"
      by blast
    note hyp_c2 = \<open>PROP ?Hyp Env B \<langle>c2\<rangle> C2\<close>
    from da_c2' B' 
    obtain "nrm C2 \<subseteq> nrm C2'" "(\<forall>l. brk C2 l \<subseteq> brk C2' l)"
      by - (drule hyp_c2,auto)
    with A A' C1'
    show ?case
      by auto
   next
     case Init thus ?case by (elim da_elim_cases) auto
   next
     case NewC thus ?case by (elim da_elim_cases) auto
   next
     case NewA thus ?case by (elim da_elim_cases) auto
   next
     case Cast thus ?case by (elim da_elim_cases) auto
   next
     case Inst thus ?case by (elim da_elim_cases) auto
   next
     case Lit thus ?case by (elim da_elim_cases) auto
   next
     case UnOp thus ?case by (elim da_elim_cases) auto
   next
     case (CondAnd Env B e1 E1 e2 E2 A B' A')
     note A = \<open>nrm A = B \<union>
                       assigns_if True (BinOp CondAnd e1 e2) \<inter>
                       assigns_if False (BinOp CondAnd e1 e2)\<close>
             \<open>brk A = (\<lambda>l. UNIV)\<close>
     from \<open>Env\<turnstile> B' \<guillemotright>\<langle>BinOp CondAnd e1 e2\<rangle>\<guillemotright> A'\<close>
     obtain  A': "nrm A' = B' \<union>
                                 assigns_if True (BinOp CondAnd e1 e2) \<inter>
                                 assigns_if False (BinOp CondAnd e1 e2)"
                      "brk A' = (\<lambda>l. UNIV)" 
       by cases auto
     note B' = \<open>B \<subseteq> B'\<close>
     with A A' show ?case 
       by auto 
   next
     case CondOr thus ?case by (elim da_elim_cases) auto
   next
     case BinOp thus ?case by (elim da_elim_cases) auto
   next
     case Super thus ?case by (elim da_elim_cases) auto
   next
     case AccLVar thus ?case by (elim da_elim_cases) auto
   next
     case Acc thus ?case by (elim da_elim_cases) auto
   next
     case AssLVar thus ?case by (elim da_elim_cases) auto
   next
     case Ass thus ?case by (elim da_elim_cases) auto
   next
     case (CondBool Env c e1 e2 B C E1 E2 A B' A')
     note A = \<open>nrm A = B \<union> 
                        assigns_if True (c ? e1 : e2) \<inter> 
                        assigns_if False (c ? e1 : e2)\<close>
             \<open>brk A = (\<lambda>l. UNIV)\<close>
     note \<open>Env\<turnstile> (c ? e1 : e2)\<Colon>- (PrimT Boolean)\<close>
     moreover
     note \<open>Env\<turnstile> B' \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A'\<close>
     ultimately
     obtain A': "nrm A' = B' \<union> 
                                  assigns_if True (c ? e1 : e2) \<inter> 
                                  assigns_if False (c ? e1 : e2)"
                     "brk A' = (\<lambda>l. UNIV)"
       by (elim da_elim_cases) (auto simp add: inj_term_simps) 
       (* inj_term_simps needed to handle wt (defined without \<langle>\<rangle>) *)
     note B' = \<open>B \<subseteq> B'\<close>
     with A A' show ?case 
       by auto 
   next
     case (Cond Env c e1 e2 B C E1 E2 A B' A')  
     note A = \<open>nrm A = nrm E1 \<inter> nrm E2\<close> \<open>brk A = (\<lambda>l. UNIV)\<close>
     note not_bool = \<open>\<not> Env\<turnstile> (c ? e1 : e2)\<Colon>- (PrimT Boolean)\<close>
     from \<open>Env\<turnstile> B' \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A'\<close>
     obtain E1' E2'
       where da_e1': "Env\<turnstile> B' \<union> assigns_if True c \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'" and
             da_e2': "Env\<turnstile> B' \<union> assigns_if False c \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2'" and
                 A': "nrm A' = nrm E1' \<inter> nrm E2'"
                     "brk A' = (\<lambda>l. UNIV)"
       using not_bool
       by (elim da_elim_cases) (auto simp add: inj_term_simps)
       (* inj_term_simps needed to handle wt (defined without \<langle>\<rangle>) *)
     note \<open>PROP ?Hyp Env (B \<union> assigns_if True c) \<langle>e1\<rangle> E1\<close>
     moreover note B' = \<open>B \<subseteq> B'\<close>
     moreover note da_e1'
     ultimately obtain E1': "nrm E1 \<subseteq> nrm E1'" "(\<forall>l. brk E1 l \<subseteq> brk E1' l)"
       by blast
     note \<open>PROP ?Hyp Env (B \<union> assigns_if False c) \<langle>e2\<rangle> E2\<close>
     with B' da_e2'
     obtain "nrm E2 \<subseteq> nrm E2'" "(\<forall>l. brk E2 l \<subseteq> brk E2' l)"
       by blast
    with E1' A A'
    show ?case
      by auto
  next
    case Call
    from Call.prems and Call.hyps
    show ?case by cases auto
  next
    case Methd thus ?case by (elim da_elim_cases) auto
  next
    case Body thus ?case by (elim da_elim_cases) auto
  next
    case LVar thus ?case by (elim da_elim_cases) auto
  next
    case FVar thus ?case by (elim da_elim_cases) auto
  next
    case AVar thus ?case by (elim da_elim_cases) auto
  next
    case Nil thus ?case by (elim da_elim_cases) auto
  next
    case Cons thus ?case by (elim da_elim_cases) auto
  qed
  from this [OF da' \<open>B \<subseteq> B'\<close>] show ?thesis .
qed
  
lemma da_weaken:     
  assumes da: "Env\<turnstile> B \<guillemotright>t\<guillemotright> A" and "B \<subseteq> B'" 
  shows "\<exists> A'. Env \<turnstile> B' \<guillemotright>t\<guillemotright> A'"
proof -
  note assigned.select_convs [Pure.intro]
  from da  
  have "\<And> B'. B \<subseteq> B' \<Longrightarrow> \<exists> A'. Env\<turnstile> B' \<guillemotright>t\<guillemotright> A'" (is "PROP ?Hyp Env B t")
  proof (induct) 
    case Skip thus ?case by (iprover intro: da.Skip)
  next
    case Expr thus ?case by (iprover intro: da.Expr)
  next
    case (Lab Env B c C A l B')  
    note \<open>PROP ?Hyp Env B \<langle>c\<rangle>\<close>
    moreover
    note B' = \<open>B \<subseteq> B'\<close>
    ultimately obtain C' where "Env\<turnstile> B' \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'"
      by iprover
    then obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>Break l\<bullet> c\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Lab)
    thus ?case ..
  next
    case (Comp Env B c1 C1 c2 C2 A B')
    note da_c1 = \<open>Env\<turnstile> B \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1\<close>
    note \<open>PROP ?Hyp Env B \<langle>c1\<rangle>\<close>
    moreover
    note B' = \<open>B \<subseteq> B'\<close>
    ultimately obtain C1' where da_c1': "Env\<turnstile> B' \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'"
      by iprover
    with da_c1 B'
    have
      "nrm C1 \<subseteq> nrm C1'"
      by (rule da_monotone [elim_format]) simp
    moreover
    note \<open>PROP ?Hyp Env (nrm C1) \<langle>c2\<rangle>\<close>
    ultimately obtain C2' where "Env\<turnstile> nrm C1' \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'"
      by iprover
    with da_c1' obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>c1;; c2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Comp)
    thus ?case ..
  next
    case (If Env B e E c1 C1 c2 C2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain  E' where "Env\<turnstile> B' \<guillemotright>\<langle>e\<rangle>\<guillemotright> E'"
    proof -
      have "PROP ?Hyp Env B \<langle>e\<rangle>" by (rule If.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain C1' where "Env\<turnstile> (B' \<union> assigns_if True e) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'"
    proof -
      from B'
      have "(B \<union> assigns_if True e) \<subseteq> (B' \<union> assigns_if True e)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if True e) \<langle>c1\<rangle>" by (rule If.hyps)
      ultimately 
      show ?thesis using that by iprover
    qed
    moreover
    obtain C2' where "Env\<turnstile> (B' \<union> assigns_if False e) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'"
    proof - 
      from B' have "(B \<union> assigns_if False e) \<subseteq> (B' \<union> assigns_if False e)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if False e) \<langle>c2\<rangle>" by (rule If.hyps)
      ultimately
      show ?thesis using that by iprover
    qed
    ultimately
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>If(e) c1 Else c2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.If)
    thus ?case ..
  next  
    case (Loop Env B e E c C A l B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E' where "Env\<turnstile> B' \<guillemotright>\<langle>e\<rangle>\<guillemotright> E'"
    proof -
      have "PROP ?Hyp Env B \<langle>e\<rangle>" by (rule Loop.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain C' where "Env\<turnstile> (B' \<union> assigns_if True e) \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'"
    proof -
      from B'
      have "(B \<union> assigns_if True e) \<subseteq> (B' \<union> assigns_if True e)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if True e) \<langle>c\<rangle>" by (rule Loop.hyps)
      ultimately 
      show ?thesis using that by iprover
    qed
    ultimately
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Loop )
    thus ?case ..
  next
    case (Jmp jump B A Env B') 
    note B' = \<open>B \<subseteq> B'\<close>
    with Jmp.hyps have "jump = Ret \<longrightarrow> Result \<in> B' "
      by auto
    moreover
    obtain A'::assigned 
              where  "nrm A' = UNIV"
                     "brk A' = (case jump of 
                                  Break l \<Rightarrow> \<lambda>k. if k = l then B' else UNIV 
                                | Cont l \<Rightarrow> \<lambda>k. UNIV
                                | Ret \<Rightarrow> \<lambda>k. UNIV)"
                     
      by  iprover
    ultimately have "Env\<turnstile> B' \<guillemotright>\<langle>Jmp jump\<rangle>\<guillemotright> A'"
      by (rule da.Jmp)
    thus ?case ..
  next
    case Throw thus ?case by (iprover intro: da.Throw )
  next
    case (Try Env B c1 C1 vn C c2 C2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain C1' where "Env\<turnstile> B' \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'"
    proof -
      have "PROP ?Hyp Env B \<langle>c1\<rangle>" by (rule Try.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain C2' where 
      "Env\<lparr>lcl := (lcl Env)(VName vn\<mapsto>Class C)\<rparr>\<turnstile> B' \<union> {VName vn} \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'"
    proof -
      from B' have "B \<union> {VName vn} \<subseteq> B' \<union> {VName vn}" by blast
      moreover
      have "PROP ?Hyp (Env\<lparr>lcl := (lcl Env)(VName vn\<mapsto>Class C)\<rparr>) 
                      (B \<union> {VName vn}) \<langle>c2\<rangle>" 
        by (rule Try.hyps)
      ultimately
      show ?thesis using that by iprover
    qed
    ultimately
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>Try c1 Catch(C vn) c2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Try )
    thus ?case ..
  next
    case (Fin Env B c1 C1 c2 C2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain C1' where C1': "Env\<turnstile> B' \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'"
    proof -
      have "PROP ?Hyp Env B \<langle>c1\<rangle>" by (rule Fin.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain C2' where "Env\<turnstile> B' \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'"
    proof -
      have "PROP ?Hyp Env B \<langle>c2\<rangle>" by (rule Fin.hyps)
      with B'
      show ?thesis using that by iprover
    qed
    ultimately
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>c1 Finally c2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Fin )
    thus ?case ..
  next
    case Init thus ?case by (iprover intro: da.Init)
  next
    case NewC thus ?case by (iprover intro: da.NewC)
  next
    case NewA thus ?case by (iprover intro: da.NewA)
  next
    case Cast thus ?case by (iprover intro: da.Cast)
  next
    case Inst thus ?case by (iprover intro: da.Inst)
  next
    case Lit thus ?case by (iprover intro: da.Lit)
  next
    case UnOp thus ?case by (iprover intro: da.UnOp)
  next
    case (CondAnd Env B e1 E1 e2 E2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E1' where "Env\<turnstile> B' \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'"
    proof -
      have "PROP ?Hyp Env B \<langle>e1\<rangle>" by (rule CondAnd.hyps)
      with B'
      show ?thesis using that by iprover
    qed
    moreover
    obtain E2' where "Env\<turnstile> B' \<union>  assigns_if True e1 \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2'"
    proof -
      from B' have "B \<union> assigns_if True e1 \<subseteq> B' \<union>  assigns_if True e1"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if True e1) \<langle>e2\<rangle>" by (rule CondAnd.hyps)
      ultimately show ?thesis using that by iprover
    qed
    ultimately
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>BinOp CondAnd e1 e2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.CondAnd)
    thus ?case ..
  next
    case (CondOr Env B e1 E1 e2 E2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E1' where "Env\<turnstile> B' \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'"
    proof -
      have "PROP ?Hyp Env B \<langle>e1\<rangle>" by (rule CondOr.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain E2' where "Env\<turnstile> B' \<union> assigns_if False e1 \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2'"
    proof -
      from B' have "B \<union> assigns_if False e1 \<subseteq> B' \<union>  assigns_if False e1"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if False e1) \<langle>e2\<rangle>" by (rule CondOr.hyps)
      ultimately show ?thesis using that by iprover
    qed
    ultimately
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>BinOp CondOr e1 e2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.CondOr)
    thus ?case ..
  next
    case (BinOp Env B e1 E1 e2 A binop B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E1' where E1': "Env\<turnstile> B' \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'"
    proof -
      have "PROP ?Hyp Env B \<langle>e1\<rangle>" by (rule BinOp.hyps)
      with B'
      show ?thesis using that by iprover
    qed
    moreover
    obtain A' where "Env\<turnstile> nrm E1' \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A'"
    proof -
      have "Env\<turnstile> B \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1" by (rule BinOp.hyps)
      from this B' E1'
      have "nrm E1 \<subseteq> nrm E1'"
        by (rule da_monotone [THEN conjE])
      moreover 
      have "PROP ?Hyp Env (nrm E1) \<langle>e2\<rangle>" by (rule BinOp.hyps)
      ultimately show ?thesis using that by iprover
    qed
    ultimately
    have "Env\<turnstile> B' \<guillemotright>\<langle>BinOp binop e1 e2\<rangle>\<guillemotright> A'"
      using BinOp.hyps by (iprover intro: da.BinOp)
    thus ?case ..
  next
    case (Super B Env B')
    note B' = \<open>B \<subseteq> B'\<close>
    with Super.hyps have "This \<in> B'"
      by auto
    thus ?case by (iprover intro: da.Super)
  next
    case (AccLVar vn B A Env B')
    note \<open>vn \<in> B\<close>
    moreover
    note \<open>B \<subseteq> B'\<close>
    ultimately have "vn \<in> B'" by auto
    thus ?case by (iprover intro: da.AccLVar)
  next
    case Acc thus ?case by (iprover intro: da.Acc)
  next 
    case (AssLVar Env B e E A vn B')
    note B' = \<open>B \<subseteq> B'\<close>
    then obtain E' where "Env\<turnstile> B' \<guillemotright>\<langle>e\<rangle>\<guillemotright> E'"
      by (rule AssLVar.hyps [elim_format]) iprover
    then obtain A' where  
      "Env\<turnstile> B' \<guillemotright>\<langle>LVar vn:=e\<rangle>\<guillemotright> A'"
      by (iprover intro: da.AssLVar)
    thus ?case ..
  next
    case (Ass v Env B V e A B') 
    note B' = \<open>B \<subseteq> B'\<close>
    note \<open>\<forall>vn. v \<noteq> LVar vn\<close>
    moreover
    obtain V' where V': "Env\<turnstile> B' \<guillemotright>\<langle>v\<rangle>\<guillemotright> V'"
    proof -
      have "PROP ?Hyp Env B \<langle>v\<rangle>" by (rule Ass.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain A' where "Env\<turnstile> nrm V' \<guillemotright>\<langle>e\<rangle>\<guillemotright> A'"
    proof -
      have "Env\<turnstile> B \<guillemotright>\<langle>v\<rangle>\<guillemotright> V" by (rule Ass.hyps)
      from this B' V'
      have "nrm V \<subseteq> nrm V'"
        by (rule da_monotone [THEN conjE])
      moreover 
      have "PROP ?Hyp Env (nrm V) \<langle>e\<rangle>" by (rule Ass.hyps)
      ultimately show ?thesis using that by iprover
    qed  
    ultimately
    have "Env\<turnstile> B' \<guillemotright>\<langle>v := e\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Ass)
    thus ?case ..
  next
    case (CondBool Env c e1 e2 B C E1 E2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    note \<open>Env\<turnstile>(c ? e1 : e2)\<Colon>-(PrimT Boolean)\<close>
    moreover obtain C' where C': "Env\<turnstile> B' \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'"
    proof -
      have "PROP ?Hyp Env B \<langle>c\<rangle>" by (rule CondBool.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover 
    obtain E1' where "Env\<turnstile> B' \<union> assigns_if True c \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'"
    proof -
      from B'
      have "(B \<union> assigns_if True c) \<subseteq> (B' \<union> assigns_if True c)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if True c) \<langle>e1\<rangle>" by (rule CondBool.hyps)
      ultimately 
      show ?thesis using that by iprover
    qed
    moreover
    obtain E2' where "Env\<turnstile> B' \<union> assigns_if False c \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2'"
    proof -
      from B'
      have "(B \<union> assigns_if False c) \<subseteq> (B' \<union> assigns_if False c)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if False c) \<langle>e2\<rangle>" by(rule CondBool.hyps)
      ultimately 
      show ?thesis using that by iprover
    qed
    ultimately 
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.CondBool)
    thus ?case ..
  next
    case (Cond Env c e1 e2 B C E1 E2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    note \<open>\<not> Env\<turnstile>(c ? e1 : e2)\<Colon>-(PrimT Boolean)\<close>
    moreover obtain C' where C': "Env\<turnstile> B' \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'"
    proof -
      have "PROP ?Hyp Env B \<langle>c\<rangle>" by (rule Cond.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover 
    obtain E1' where "Env\<turnstile> B' \<union> assigns_if True c \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'"
    proof -
      from B'
      have "(B \<union> assigns_if True c) \<subseteq> (B' \<union> assigns_if True c)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if True c) \<langle>e1\<rangle>" by (rule Cond.hyps)
      ultimately 
      show ?thesis using that by iprover
    qed
    moreover
    obtain E2' where "Env\<turnstile> B' \<union> assigns_if False c \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2'"
    proof -
      from B'
      have "(B \<union> assigns_if False c) \<subseteq> (B' \<union> assigns_if False c)"
        by blast
      moreover
      have "PROP ?Hyp Env (B \<union> assigns_if False c) \<langle>e2\<rangle>" by (rule Cond.hyps)
      ultimately 
      show ?thesis using that by iprover
    qed
    ultimately 
    obtain A' where "Env\<turnstile> B' \<guillemotright>\<langle>c ? e1 : e2\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Cond)
    thus ?case ..
  next
    case (Call Env B e E args A accC statT mode mn pTs B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E' where E': "Env\<turnstile> B' \<guillemotright>\<langle>e\<rangle>\<guillemotright> E'"
    proof -
      have "PROP ?Hyp Env B \<langle>e\<rangle>" by (rule Call.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain A' where "Env\<turnstile> nrm E' \<guillemotright>\<langle>args\<rangle>\<guillemotright> A'"
    proof -
      have "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E" by (rule Call.hyps)
      from this B' E'
      have "nrm E \<subseteq> nrm E'"
        by (rule da_monotone [THEN conjE])
      moreover 
      have "PROP ?Hyp Env (nrm E) \<langle>args\<rangle>" by (rule Call.hyps)
      ultimately show ?thesis using that by iprover
    qed  
    ultimately
    have "Env\<turnstile> B' \<guillemotright>\<langle>{accC,statT,mode}e\<cdot>mn( {pTs}args)\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Call)
    thus ?case ..
  next
    case Methd thus ?case by (iprover intro: da.Methd)
  next
    case (Body Env B c C A D B')  
    note B' = \<open>B \<subseteq> B'\<close>
    obtain C' where C': "Env\<turnstile> B' \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'" and nrm_C': "nrm C \<subseteq> nrm C'"
    proof -
      have "Env\<turnstile> B \<guillemotright>\<langle>c\<rangle>\<guillemotright> C" by (rule Body.hyps)
      moreover note B'
      moreover
      from B' obtain C' where da_c: "Env\<turnstile> B' \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'"
        by (rule Body.hyps [elim_format]) blast
      ultimately
      have "nrm C \<subseteq> nrm C'"
        by (rule da_monotone [THEN conjE])
      with da_c that show ?thesis by iprover
    qed
    moreover 
    note \<open>Result \<in> nrm C\<close>
    with nrm_C' have "Result \<in> nrm C'"
      by blast
    moreover note \<open>jumpNestingOkS {Ret} c\<close>
    ultimately obtain A' where
      "Env\<turnstile> B' \<guillemotright>\<langle>Body D c\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Body)
    thus ?case ..
  next
    case LVar thus ?case by (iprover intro: da.LVar)
  next
    case FVar thus ?case by (iprover intro: da.FVar)
  next
    case (AVar Env B e1 E1 e2 A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E1' where E1': "Env\<turnstile> B' \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'"
    proof -
      have "PROP ?Hyp Env B \<langle>e1\<rangle>" by (rule AVar.hyps)
      with B'
      show ?thesis using that by iprover
    qed
    moreover
    obtain A' where "Env\<turnstile> nrm E1' \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A'"
    proof -
      have "Env\<turnstile> B \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1" by (rule AVar.hyps)
      from this B' E1'
      have "nrm E1 \<subseteq> nrm E1'"
        by (rule da_monotone [THEN conjE])
      moreover 
      have "PROP ?Hyp Env (nrm E1) \<langle>e2\<rangle>" by (rule AVar.hyps)
      ultimately show ?thesis using that by iprover
    qed  
    ultimately
    have "Env\<turnstile> B' \<guillemotright>\<langle>e1.[e2]\<rangle>\<guillemotright> A'"
      by (iprover intro: da.AVar)
    thus ?case ..
  next
    case Nil thus ?case by (iprover intro: da.Nil)
  next
    case (Cons Env B e E es A B')
    note B' = \<open>B \<subseteq> B'\<close>
    obtain E' where E': "Env\<turnstile> B' \<guillemotright>\<langle>e\<rangle>\<guillemotright> E'"
    proof -
      have "PROP ?Hyp Env B \<langle>e\<rangle>" by (rule Cons.hyps)
      with B'  
      show ?thesis using that by iprover
    qed
    moreover
    obtain A' where "Env\<turnstile> nrm E' \<guillemotright>\<langle>es\<rangle>\<guillemotright> A'"
    proof -
      have "Env\<turnstile> B \<guillemotright>\<langle>e\<rangle>\<guillemotright> E" by (rule Cons.hyps)
      from this B' E'
      have "nrm E \<subseteq> nrm E'"
        by (rule da_monotone [THEN conjE])
      moreover 
      have "PROP ?Hyp Env (nrm E) \<langle>es\<rangle>" by (rule Cons.hyps)
      ultimately show ?thesis using that by iprover
    qed  
    ultimately
    have "Env\<turnstile> B' \<guillemotright>\<langle>e # es\<rangle>\<guillemotright> A'"
      by (iprover intro: da.Cons)
    thus ?case ..
  qed
  from this [OF \<open>B \<subseteq> B'\<close>] show ?thesis .
qed

(* Remarks about the proof style:

   "by (rule <Case>.hyps)" vs "."
   --------------------------
  
   with <Case>.hyps you state more precise were the rule comes from

   . takes all assumptions into account, but looks more "light"
   and is more resistent for cut and paste proof in different 
   cases.

  "intro: da.intros" vs "da.<Case>"
  ---------------------------------
  The first ist more convinient for cut and paste between cases,
  the second is more informativ for the reader
*)

corollary da_weakenE [consumes 2]:
  assumes          da: "Env\<turnstile> B  \<guillemotright>t\<guillemotright> A"   and
                   B': "B \<subseteq> B'"          and
              ex_mono: "\<And> A'.  \<lbrakk>Env\<turnstile> B' \<guillemotright>t\<guillemotright> A'; nrm A \<subseteq> nrm A'; 
                               \<And> l. brk A l \<subseteq> brk A' l\<rbrakk> \<Longrightarrow> P" 
  shows "P"
proof -
  from da B'
  obtain A' where A': "Env\<turnstile> B' \<guillemotright>t\<guillemotright> A'"
    by (rule da_weaken [elim_format]) iprover
  with da B'
  have "nrm A \<subseteq> nrm A' \<and> (\<forall> l. brk A l \<subseteq> brk A' l)"
    by (rule da_monotone)
  with A' ex_mono
  show ?thesis
    by iprover
qed

end
