(*  Title:      HOL/Predicate.thy
    Author:     Lukas Bulwahn and Florian Haftmann, TU Muenchen
*)

section \<open>Predicates as enumerations\<close>

theory Predicate
imports String
begin

subsection \<open>The type of predicate enumerations (a monad)\<close>

datatype (plugins only: extraction) (dead 'a) pred = Pred (eval: "'a \<Rightarrow> bool")

lemma pred_eqI:
  "(\<And>w. eval P w \<longleftrightarrow> eval Q w) \<Longrightarrow> P = Q"
  by (cases P, cases Q) (auto simp add: fun_eq_iff)

lemma pred_eq_iff:
  "P = Q \<Longrightarrow> (\<And>w. eval P w \<longleftrightarrow> eval Q w)"
  by (simp add: pred_eqI)

instantiation pred :: (type) complete_lattice
begin

definition
  "P \<le> Q \<longleftrightarrow> eval P \<le> eval Q"

definition
  "P < Q \<longleftrightarrow> eval P < eval Q"

definition
  "\<bottom> = Pred \<bottom>"

lemma eval_bot [simp]:
  "eval \<bottom>  = \<bottom>"
  by (simp add: bot_pred_def)

definition
  "\<top> = Pred \<top>"

lemma eval_top [simp]:
  "eval \<top>  = \<top>"
  by (simp add: top_pred_def)

definition
  "P \<sqinter> Q = Pred (eval P \<sqinter> eval Q)"

lemma eval_inf [simp]:
  "eval (P \<sqinter> Q) = eval P \<sqinter> eval Q"
  by (simp add: inf_pred_def)

definition
  "P \<squnion> Q = Pred (eval P \<squnion> eval Q)"

lemma eval_sup [simp]:
  "eval (P \<squnion> Q) = eval P \<squnion> eval Q"
  by (simp add: sup_pred_def)

definition
  "\<Sqinter>A = Pred (\<Sqinter>(eval ` A))"

lemma eval_Inf [simp]:
  "eval (\<Sqinter>A) = \<Sqinter>(eval ` A)"
  by (simp add: Inf_pred_def)

definition
  "\<Squnion>A = Pred (\<Squnion>(eval ` A))"

lemma eval_Sup [simp]:
  "eval (\<Squnion>A) = \<Squnion>(eval ` A)"
  by (simp add: Sup_pred_def)

instance proof
qed (auto intro!: pred_eqI simp add: less_eq_pred_def less_pred_def le_fun_def less_fun_def)

end

lemma eval_INF [simp]:
  "eval (\<Sqinter>(f ` A)) = \<Sqinter>((eval \<circ> f) ` A)"
  by (simp add: image_comp)

lemma eval_SUP [simp]:
  "eval (\<Squnion>(f ` A)) = \<Squnion>((eval \<circ> f) ` A)"
  by (simp add: image_comp)

instantiation pred :: (type) complete_boolean_algebra
begin

definition
  "- P = Pred (- eval P)"

lemma eval_compl [simp]:
  "eval (- P) = - eval P"
  by (simp add: uminus_pred_def)

definition
  "P - Q = Pred (eval P - eval Q)"

lemma eval_minus [simp]:
  "eval (P - Q) = eval P - eval Q"
  by (simp add: minus_pred_def)

instance proof
  fix A::"'a pred set set"
  show "\<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"
  proof (simp add: less_eq_pred_def Sup_fun_def Inf_fun_def, safe)
    fix w
    assume A: "\<forall>x\<in>A. \<exists>f\<in>x. eval f w"
    define F where "F = (\<lambda> x . SOME f . f \<in> x \<and> eval f w)"
    have [simp]: "(\<forall>f\<in> (F ` A). eval f w)"
      by (metis (no_types, lifting) A F_def image_iff some_eq_ex)
    have "(\<exists>f. F ` A = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<forall>f\<in>(F ` A). eval f w)"
      using A by (simp, metis (no_types, lifting) F_def someI)+
    from this show "\<exists>x. (\<exists>f. x = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<forall>f\<in>x. eval f w)"
      by (rule exI [of _ "F ` A"])
  qed
qed (auto intro!: pred_eqI)

end

definition single :: "'a \<Rightarrow> 'a pred" where
  "single x = Pred ((=) x)"

lemma eval_single [simp]:
  "eval (single x) = (=) x"
  by (simp add: single_def)

definition bind :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b pred) \<Rightarrow> 'b pred" (infixl \<open>\<bind>\<close> 70) where
  "P \<bind> f = (\<Squnion>(f ` {x. eval P x}))"

lemma eval_bind [simp]:
  "eval (P \<bind> f) = eval (\<Squnion>(f ` {x. eval P x}))"
  by (simp add: bind_def)

lemma bind_bind:
  "(P \<bind> Q) \<bind> R = P \<bind> (\<lambda>x. Q x \<bind> R)"
  by (rule pred_eqI) auto

lemma bind_single:
  "P \<bind> single = P"
  by (rule pred_eqI) auto

lemma single_bind:
  "single x \<bind> P = P x"
  by (rule pred_eqI) auto

lemma bottom_bind:
  "\<bottom> \<bind> P = \<bottom>"
  by (rule pred_eqI) auto

lemma sup_bind:
  "(P \<squnion> Q) \<bind> R = P \<bind> R \<squnion> Q \<bind> R"
  by (rule pred_eqI) auto

lemma Sup_bind:
  "(\<Squnion>A \<bind> f) = \<Squnion>((\<lambda>x. x \<bind> f) ` A)"
  by (rule pred_eqI) auto

lemma pred_iffI:
  assumes "\<And>x. eval A x \<Longrightarrow> eval B x"
  and "\<And>x. eval B x \<Longrightarrow> eval A x"
  shows "A = B"
  using assms by (auto intro: pred_eqI)
  
lemma singleI: "eval (single x) x"
  by simp

lemma singleI_unit: "eval (single ()) x"
  by simp

lemma singleE: "eval (single x) y \<Longrightarrow> (y = x \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma singleE': "eval (single x) y \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma bindI: "eval P x \<Longrightarrow> eval (Q x) y \<Longrightarrow> eval (P \<bind> Q) y"
  by auto

lemma bindE: "eval (R \<bind> Q) y \<Longrightarrow> (\<And>x. eval R x \<Longrightarrow> eval (Q x) y \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma botE: "eval \<bottom> x \<Longrightarrow> P"
  by auto

lemma supI1: "eval A x \<Longrightarrow> eval (A \<squnion> B) x"
  by auto

lemma supI2: "eval B x \<Longrightarrow> eval (A \<squnion> B) x" 
  by auto

lemma supE: "eval (A \<squnion> B) x \<Longrightarrow> (eval A x \<Longrightarrow> P) \<Longrightarrow> (eval B x \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma single_not_bot [simp]:
  "single x \<noteq> \<bottom>"
  by (auto simp add: single_def bot_pred_def fun_eq_iff)

lemma not_bot:
  assumes "A \<noteq> \<bottom>"
  obtains x where "eval A x"
  using assms by (cases A) (auto simp add: bot_pred_def)


subsection \<open>Emptiness check and definite choice\<close>

definition is_empty :: "'a pred \<Rightarrow> bool" where
  "is_empty A \<longleftrightarrow> A = \<bottom>"

lemma is_empty_bot:
  "is_empty \<bottom>"
  by (simp add: is_empty_def)

lemma not_is_empty_single:
  "\<not> is_empty (single x)"
  by (auto simp add: is_empty_def single_def bot_pred_def fun_eq_iff)

lemma is_empty_sup:
  "is_empty (A \<squnion> B) \<longleftrightarrow> is_empty A \<and> is_empty B"
  by (auto simp add: is_empty_def)

definition singleton :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a pred \<Rightarrow> 'a" where
  "singleton default A = (if \<exists>!x. eval A x then THE x. eval A x else default ())" for default

lemma singleton_eqI:
  "\<exists>!x. eval A x \<Longrightarrow> eval A x \<Longrightarrow> singleton default A = x" for default
  by (auto simp add: singleton_def)

lemma eval_singletonI:
  "\<exists>!x. eval A x \<Longrightarrow> eval A (singleton default A)" for default
proof -
  assume assm: "\<exists>!x. eval A x"
  then obtain x where x: "eval A x" ..
  with assm have "singleton default A = x" by (rule singleton_eqI)
  with x show ?thesis by simp
qed

lemma single_singleton:
  "\<exists>!x. eval A x \<Longrightarrow> single (singleton default A) = A" for default
proof -
  assume assm: "\<exists>!x. eval A x"
  then have "eval A (singleton default A)"
    by (rule eval_singletonI)
  moreover from assm have "\<And>x. eval A x \<Longrightarrow> singleton default A = x"
    by (rule singleton_eqI)
  ultimately have "eval (single (singleton default A)) = eval A"
    by (simp (no_asm_use) add: single_def fun_eq_iff) blast
  then have "\<And>x. eval (single (singleton default A)) x = eval A x"
    by simp
  then show ?thesis by (rule pred_eqI)
qed

lemma singleton_undefinedI:
  "\<not> (\<exists>!x. eval A x) \<Longrightarrow> singleton default A = default ()" for default
  by (simp add: singleton_def)

lemma singleton_bot:
  "singleton default \<bottom> = default ()" for default
  by (auto simp add: bot_pred_def intro: singleton_undefinedI)

lemma singleton_single:
  "singleton default (single x) = x" for default
  by (auto simp add: intro: singleton_eqI singleI elim: singleE)

lemma singleton_sup_single_single:
  "singleton default (single x \<squnion> single y) = (if x = y then x else default ())" for default
proof (cases "x = y")
  case True then show ?thesis by (simp add: singleton_single)
next
  case False
  have "eval (single x \<squnion> single y) x"
    and "eval (single x \<squnion> single y) y"
  by (auto intro: supI1 supI2 singleI)
  with False have "\<not> (\<exists>!z. eval (single x \<squnion> single y) z)"
    by blast
  then have "singleton default (single x \<squnion> single y) = default ()"
    by (rule singleton_undefinedI)
  with False show ?thesis by simp
qed

lemma singleton_sup_aux:
  "singleton default (A \<squnion> B) = (if A = \<bottom> then singleton default B
    else if B = \<bottom> then singleton default A
    else singleton default
      (single (singleton default A) \<squnion> single (singleton default B)))" for default
proof (cases "(\<exists>!x. eval A x) \<and> (\<exists>!y. eval B y)")
  case True then show ?thesis by (simp add: single_singleton)
next
  case False
  from False have A_or_B:
    "singleton default A = default () \<or> singleton default B = default ()"
    by (auto intro!: singleton_undefinedI)
  then have rhs: "singleton default
    (single (singleton default A) \<squnion> single (singleton default B)) = default ()"
    by (auto simp add: singleton_sup_single_single singleton_single)
  from False have not_unique:
    "\<not> (\<exists>!x. eval A x) \<or> \<not> (\<exists>!y. eval B y)" by simp
  show ?thesis proof (cases "A \<noteq> \<bottom> \<and> B \<noteq> \<bottom>")
    case True
    then obtain a b where a: "eval A a" and b: "eval B b"
      by (blast elim: not_bot)
    with True not_unique have "\<not> (\<exists>!x. eval (A \<squnion> B) x)"
      by (auto simp add: sup_pred_def bot_pred_def)
    then have "singleton default (A \<squnion> B) = default ()" by (rule singleton_undefinedI)
    with True rhs show ?thesis by simp
  next
    case False then show ?thesis by auto
  qed
qed

lemma singleton_sup:
  "singleton default (A \<squnion> B) = (if A = \<bottom> then singleton default B
    else if B = \<bottom> then singleton default A
    else if singleton default A = singleton default B then singleton default A else default ())" for default
  using singleton_sup_aux [of default A B] by (simp only: singleton_sup_single_single)


subsection \<open>Derived operations\<close>

definition if_pred :: "bool \<Rightarrow> unit pred" where
  if_pred_eq: "if_pred b = (if b then single () else \<bottom>)"

definition holds :: "unit pred \<Rightarrow> bool" where
  holds_eq: "holds P = eval P ()"

definition not_pred :: "unit pred \<Rightarrow> unit pred" where
  not_pred_eq: "not_pred P = (if eval P () then \<bottom> else single ())"

lemma if_predI: "P \<Longrightarrow> eval (if_pred P) ()"
  unfolding if_pred_eq by (auto intro: singleI)

lemma if_predE: "eval (if_pred b) x \<Longrightarrow> (b \<Longrightarrow> x = () \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding if_pred_eq by (cases b) (auto elim: botE)

lemma not_predI: "\<not> P \<Longrightarrow> eval (not_pred (Pred (\<lambda>u. P))) ()"
  unfolding not_pred_eq by (auto intro: singleI)

lemma not_predI': "\<not> eval P () \<Longrightarrow> eval (not_pred P) ()"
  unfolding not_pred_eq by (auto intro: singleI)

lemma not_predE: "eval (not_pred (Pred (\<lambda>u. P))) x \<Longrightarrow> (\<not> P \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding not_pred_eq
  by (auto split: if_split_asm elim: botE)

lemma not_predE': "eval (not_pred P) x \<Longrightarrow> (\<not> eval P x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding not_pred_eq
  by (auto split: if_split_asm elim: botE)
lemma "f () = False \<or> f () = True"
by simp

lemma closure_of_bool_cases [no_atp]:
  fixes f :: "unit \<Rightarrow> bool"
  assumes "f = (\<lambda>u. False) \<Longrightarrow> P f"
  assumes "f = (\<lambda>u. True) \<Longrightarrow> P f"
  shows "P f"
proof -
  have "f = (\<lambda>u. False) \<or> f = (\<lambda>u. True)"
    apply (cases "f ()")
    apply (rule disjI2)
    apply (rule ext)
    apply (simp add: unit_eq)
    apply (rule disjI1)
    apply (rule ext)
    apply (simp add: unit_eq)
    done
  from this assms show ?thesis by blast
qed

lemma unit_pred_cases:
  assumes "P \<bottom>"
  assumes "P (single ())"
  shows "P Q"
using assms unfolding bot_pred_def bot_fun_def bot_bool_def empty_def single_def proof (cases Q)
  fix f
  assume "P (Pred (\<lambda>u. False))" "P (Pred (\<lambda>u. () = u))"
  then have "P (Pred f)" 
    by (cases _ f rule: closure_of_bool_cases) simp_all
  moreover assume "Q = Pred f"
  ultimately show "P Q" by simp
qed
  
lemma holds_if_pred:
  "holds (if_pred b) = b"
unfolding if_pred_eq holds_eq
by (cases b) (auto intro: singleI elim: botE)

lemma if_pred_holds:
  "if_pred (holds P) = P"
unfolding if_pred_eq holds_eq
by (rule unit_pred_cases) (auto intro: singleI elim: botE)

lemma is_empty_holds:
  "is_empty P \<longleftrightarrow> \<not> holds P"
unfolding is_empty_def holds_eq
by (rule unit_pred_cases) (auto elim: botE intro: singleI)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pred \<Rightarrow> 'b pred" where
  "map f P = P \<bind> (single \<circ> f)"

lemma eval_map [simp]:
  "eval (map f P) = (\<Squnion>x\<in>{x. eval P x}. (\<lambda>y. f x = y))"
  by (simp add: map_def comp_def image_comp)

functor map: map
  by (rule ext, rule pred_eqI, auto)+


subsection \<open>Implementation\<close>

datatype (plugins only: code extraction) (dead 'a) seq =
  Empty
| Insert "'a" "'a pred"
| Join "'a pred" "'a seq"

primrec pred_of_seq :: "'a seq \<Rightarrow> 'a pred" where
  "pred_of_seq Empty = \<bottom>"
| "pred_of_seq (Insert x P) = single x \<squnion> P"
| "pred_of_seq (Join P xq) = P \<squnion> pred_of_seq xq"

definition Seq :: "(unit \<Rightarrow> 'a seq) \<Rightarrow> 'a pred" where
  "Seq f = pred_of_seq (f ())"

code_datatype Seq

primrec member :: "'a seq \<Rightarrow> 'a \<Rightarrow> bool"  where
  "member Empty x \<longleftrightarrow> False"
| "member (Insert y P) x \<longleftrightarrow> x = y \<or> eval P x"
| "member (Join P xq) x \<longleftrightarrow> eval P x \<or> member xq x"

lemma eval_member:
  "member xq = eval (pred_of_seq xq)"
proof (induct xq)
  case Empty show ?case
  by (auto simp add: fun_eq_iff elim: botE)
next
  case Insert show ?case
  by (auto simp add: fun_eq_iff elim: supE singleE intro: supI1 supI2 singleI)
next
  case Join then show ?case
  by (auto simp add: fun_eq_iff elim: supE intro: supI1 supI2)
qed

lemma eval_code [(* FIXME declare simp *)code]: "eval (Seq f) = member (f ())"
  unfolding Seq_def by (rule sym, rule eval_member)

lemma single_code [code]:
  "single x = Seq (\<lambda>u. Insert x \<bottom>)"
  unfolding Seq_def by simp

primrec "apply" :: "('a \<Rightarrow> 'b pred) \<Rightarrow> 'a seq \<Rightarrow> 'b seq" where
  "apply f Empty = Empty"
| "apply f (Insert x P) = Join (f x) (Join (P \<bind> f) Empty)"
| "apply f (Join P xq) = Join (P \<bind> f) (apply f xq)"

lemma apply_bind:
  "pred_of_seq (apply f xq) = pred_of_seq xq \<bind> f"
proof (induct xq)
  case Empty show ?case
    by (simp add: bottom_bind)
next
  case Insert show ?case
    by (simp add: single_bind sup_bind)
next
  case Join then show ?case
    by (simp add: sup_bind)
qed
  
lemma bind_code [code]:
  "Seq g \<bind> f = Seq (\<lambda>u. apply f (g ()))"
  unfolding Seq_def by (rule sym, rule apply_bind)

lemma bot_set_code [code]:
  "\<bottom> = Seq (\<lambda>u. Empty)"
  unfolding Seq_def by simp

primrec adjunct :: "'a pred \<Rightarrow> 'a seq \<Rightarrow> 'a seq" where
  "adjunct P Empty = Join P Empty"
| "adjunct P (Insert x Q) = Insert x (Q \<squnion> P)"
| "adjunct P (Join Q xq) = Join Q (adjunct P xq)"

lemma adjunct_sup:
  "pred_of_seq (adjunct P xq) = P \<squnion> pred_of_seq xq"
  by (induct xq) (simp_all add: sup_assoc sup_commute sup_left_commute)

lemma sup_code [code]:
  "Seq f \<squnion> Seq g = Seq (\<lambda>u. case f ()
    of Empty \<Rightarrow> g ()
     | Insert x P \<Rightarrow> Insert x (P \<squnion> Seq g)
     | Join P xq \<Rightarrow> adjunct (Seq g) (Join P xq))"
proof (cases "f ()")
  case Empty
  thus ?thesis
    unfolding Seq_def by (simp add: sup_commute [of "\<bottom>"])
next
  case Insert
  thus ?thesis
    unfolding Seq_def by (simp add: sup_assoc)
next
  case Join
  thus ?thesis
    unfolding Seq_def
    by (simp add: adjunct_sup sup_assoc sup_commute sup_left_commute)
qed

primrec contained :: "'a seq \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "contained Empty Q \<longleftrightarrow> True"
| "contained (Insert x P) Q \<longleftrightarrow> eval Q x \<and> P \<le> Q"
| "contained (Join P xq) Q \<longleftrightarrow> P \<le> Q \<and> contained xq Q"

lemma single_less_eq_eval:
  "single x \<le> P \<longleftrightarrow> eval P x"
  by (auto simp add: less_eq_pred_def le_fun_def)

lemma contained_less_eq:
  "contained xq Q \<longleftrightarrow> pred_of_seq xq \<le> Q"
  by (induct xq) (simp_all add: single_less_eq_eval)

lemma less_eq_pred_code [code]:
  "Seq f \<le> Q = (case f ()
   of Empty \<Rightarrow> True
    | Insert x P \<Rightarrow> eval Q x \<and> P \<le> Q
    | Join P xq \<Rightarrow> P \<le> Q \<and> contained xq Q)"
  by (cases "f ()")
    (simp_all add: Seq_def single_less_eq_eval contained_less_eq)

instantiation pred :: (type) equal
begin

definition equal_pred
  where [simp]: "HOL.equal P Q \<longleftrightarrow> P = (Q :: 'a pred)"

instance by standard simp

end
    
lemma [code]:
  "HOL.equal P Q \<longleftrightarrow> P \<le> Q \<and> Q \<le> P" for P Q :: "'a pred"
  by auto

lemma [code nbe]:
  "HOL.equal P P \<longleftrightarrow> True" for P :: "'a pred"
  by (fact equal_refl)

lemma [code]:
  "case_pred f P = f (eval P)"
  by (fact pred.case_eq_if)

lemma [code]:
  "rec_pred f P = f (eval P)"
  by (cases P) simp

inductive eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "eq x x"

lemma eq_is_eq: "eq x y \<equiv> (x = y)"
  by (rule eq_reflection) (auto intro: eq.intros elim: eq.cases)

primrec null :: "'a seq \<Rightarrow> bool" where
  "null Empty \<longleftrightarrow> True"
| "null (Insert x P) \<longleftrightarrow> False"
| "null (Join P xq) \<longleftrightarrow> is_empty P \<and> null xq"

lemma null_is_empty:
  "null xq \<longleftrightarrow> is_empty (pred_of_seq xq)"
  by (induct xq) (simp_all add: is_empty_bot not_is_empty_single is_empty_sup)

lemma is_empty_code [code]:
  "is_empty (Seq f) \<longleftrightarrow> null (f ())"
  by (simp add: null_is_empty Seq_def)

primrec the_only :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a seq \<Rightarrow> 'a" where
  "the_only default Empty = default ()" for default
| "the_only default (Insert x P) =
    (if is_empty P then x else let y = singleton default P in if x = y then x else default ())" for default
| "the_only default (Join P xq) =
    (if is_empty P then the_only default xq else if null xq then singleton default P
       else let x = singleton default P; y = the_only default xq in
       if x = y then x else default ())" for default

lemma the_only_singleton:
  "the_only default xq = singleton default (pred_of_seq xq)" for default
  by (induct xq)
    (auto simp add: singleton_bot singleton_single is_empty_def
    null_is_empty Let_def singleton_sup)

lemma singleton_code [code]:
  "singleton default (Seq f) =
    (case f () of
      Empty \<Rightarrow> default ()
    | Insert x P \<Rightarrow> if is_empty P then x
        else let y = singleton default P in
          if x = y then x else default ()
    | Join P xq \<Rightarrow> if is_empty P then the_only default xq
        else if null xq then singleton default P
        else let x = singleton default P; y = the_only default xq in
          if x = y then x else default ())" for default
  by (cases "f ()")
   (auto simp add: Seq_def the_only_singleton is_empty_def
      null_is_empty singleton_bot singleton_single singleton_sup Let_def)

definition the :: "'a pred \<Rightarrow> 'a" where
  "the A = (THE x. eval A x)"

lemma the_eqI:
  "(THE x. eval P x) = x \<Longrightarrow> the P = x"
  by (simp add: the_def)

lemma the_eq [code]: "the A = singleton (\<lambda>x. Code.abort (STR ''not_unique'') (\<lambda>_. the A)) A"
  by (rule the_eqI) (simp add: singleton_def the_def)

code_reflect Predicate
  datatypes pred = Seq and seq = Empty | Insert | Join

ML \<open>
signature PREDICATE =
sig
  val anamorph: ('a -> ('b * 'a) option) -> int -> 'a -> 'b list * 'a
  datatype 'a pred = Seq of (unit -> 'a seq)
  and 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  val map: ('a -> 'b) -> 'a pred -> 'b pred
  val yield: 'a pred -> ('a * 'a pred) option
  val yieldn: int -> 'a pred -> 'a list * 'a pred
end;

structure Predicate : PREDICATE =
struct

fun anamorph f k x =
 (if k = 0 then ([], x)
  else case f x
   of NONE => ([], x)
    | SOME (v, y) => let
        val k' = k - 1;
        val (vs, z) = anamorph f k' y
      in (v :: vs, z) end);

datatype pred = datatype Predicate.pred
datatype seq = datatype Predicate.seq

fun map f = @{code Predicate.map} f;

fun yield (Seq f) = next (f ())
and next Empty = NONE
  | next (Insert (x, P)) = SOME (x, P)
  | next (Join (P, xq)) = (case yield P
     of NONE => next xq
      | SOME (x, Q) => SOME (x, Seq (fn _ => Join (Q, xq))));

fun yieldn k = anamorph yield k;

end;
\<close>

text \<open>Conversion from and to sets\<close>

definition pred_of_set :: "'a set \<Rightarrow> 'a pred" where
  "pred_of_set = Pred \<circ> (\<lambda>A x. x \<in> A)"

lemma eval_pred_of_set [simp]:
  "eval (pred_of_set A) x \<longleftrightarrow> x \<in>A"
  by (simp add: pred_of_set_def)

definition set_of_pred :: "'a pred \<Rightarrow> 'a set" where
  "set_of_pred = Collect \<circ> eval"

lemma member_set_of_pred [simp]:
  "x \<in> set_of_pred P \<longleftrightarrow> Predicate.eval P x"
  by (simp add: set_of_pred_def)

definition set_of_seq :: "'a seq \<Rightarrow> 'a set" where
  "set_of_seq = set_of_pred \<circ> pred_of_seq"

lemma member_set_of_seq [simp]:
  "x \<in> set_of_seq xq = Predicate.member xq x"
  by (simp add: set_of_seq_def eval_member)

lemma of_pred_code [code]:
  "set_of_pred (Predicate.Seq f) = (case f () of
     Predicate.Empty \<Rightarrow> {}
   | Predicate.Insert x P \<Rightarrow> insert x (set_of_pred P)
   | Predicate.Join P xq \<Rightarrow> set_of_pred P \<union> set_of_seq xq)"
  by (auto split: seq.split simp add: eval_code)

lemma of_seq_code [code]:
  "set_of_seq Predicate.Empty = {}"
  "set_of_seq (Predicate.Insert x P) = insert x (set_of_pred P)"
  "set_of_seq (Predicate.Join P xq) = set_of_pred P \<union> set_of_seq xq"
  by auto

text \<open>Lazy Evaluation of an indexed function\<close>

function iterate_upto :: "(natural \<Rightarrow> 'a) \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> 'a Predicate.pred"
where
  "iterate_upto f n m =
    Predicate.Seq (%u. if n > m then Predicate.Empty
     else Predicate.Insert (f n) (iterate_upto f (n + 1) m))"
by pat_completeness auto

termination by (relation "measure (%(f, n, m). nat_of_natural (m + 1 - n))")
  (auto simp add: less_natural_def)

text \<open>Misc\<close>

declare Inf_set_fold [where 'a = "'a Predicate.pred", code]
declare Sup_set_fold [where 'a = "'a Predicate.pred", code]

(* FIXME: better implement conversion by bisection *)

lemma pred_of_set_fold_sup:
  assumes "finite A"
  shows "pred_of_set A = Finite_Set.fold sup bot (Predicate.single ` A)" (is "?lhs = ?rhs")
proof (rule sym)
  interpret comp_fun_idem "sup :: 'a Predicate.pred \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'a Predicate.pred"
    by (fact comp_fun_idem_sup)
  from \<open>finite A\<close> show "?rhs = ?lhs" by (induct A) (auto intro!: pred_eqI)
qed

lemma pred_of_set_set_fold_sup:
  "pred_of_set (set xs) = fold sup (List.map Predicate.single xs) bot"
proof -
  interpret comp_fun_idem "sup :: 'a Predicate.pred \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'a Predicate.pred"
    by (fact comp_fun_idem_sup)
  show ?thesis by (simp add: pred_of_set_fold_sup fold_set_fold [symmetric])
qed

lemma pred_of_set_set_foldr_sup [code]:
  "pred_of_set (set xs) = foldr sup (List.map Predicate.single xs) bot"
  by (simp add: pred_of_set_set_fold_sup ac_simps foldr_fold fun_eq_iff)

no_notation
  bind (infixl \<open>\<bind>\<close> 70)

hide_type (open) pred seq
hide_const (open) Pred eval single bind is_empty singleton if_pred not_pred holds
  Empty Insert Join Seq member pred_of_seq "apply" adjunct null the_only eq map the
  iterate_upto
hide_fact (open) null_def member_def

end
