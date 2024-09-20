section "Constant Folding"

theory Sem_Equiv
imports Big_Step
begin

subsection "Semantic Equivalence up to a Condition"

type_synonym assn = "state \<Rightarrow> bool"

definition
  equiv_up_to :: "assn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> bool" (\<open>_ \<Turnstile> _ \<sim> _\<close> [50,0,10] 50)
where
  "(P \<Turnstile> c \<sim> c') = (\<forall>s s'. P s \<longrightarrow> (c,s) \<Rightarrow> s' \<longleftrightarrow> (c',s) \<Rightarrow> s')"

definition
  bequiv_up_to :: "assn \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bool" (\<open>_ \<Turnstile> _ <\<sim>> _\<close> [50,0,10] 50)
where
  "(P \<Turnstile> b <\<sim>> b') = (\<forall>s. P s \<longrightarrow> bval b s = bval b' s)"

lemma equiv_up_to_True:
  "((\<lambda>_. True) \<Turnstile> c \<sim> c') = (c \<sim> c')"
  by (simp add: equiv_def equiv_up_to_def)

lemma equiv_up_to_weaken:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (\<And>s. P' s \<Longrightarrow> P s) \<Longrightarrow> P' \<Turnstile> c \<sim> c'"
  by (simp add: equiv_up_to_def)

lemma equiv_up_toI:
  "(\<And>s s'. P s \<Longrightarrow> (c, s) \<Rightarrow> s' = (c', s) \<Rightarrow> s') \<Longrightarrow> P \<Turnstile> c \<sim> c'"
  by (unfold equiv_up_to_def) blast

lemma equiv_up_toD1:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> (c', s) \<Rightarrow> s'"
  by (unfold equiv_up_to_def) blast

lemma equiv_up_toD2:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (c', s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> (c, s) \<Rightarrow> s'"
  by (unfold equiv_up_to_def) blast


lemma equiv_up_to_refl [simp, intro!]:
  "P \<Turnstile> c \<sim> c"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_sym:
  "(P \<Turnstile> c \<sim> c') = (P \<Turnstile> c' \<sim> c)"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_trans:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> P \<Turnstile> c' \<sim> c'' \<Longrightarrow> P \<Turnstile> c \<sim> c''"
  by (auto simp: equiv_up_to_def)


lemma bequiv_up_to_refl [simp, intro!]:
  "P \<Turnstile> b <\<sim>> b"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_sym:
  "(P \<Turnstile> b <\<sim>> b') = (P \<Turnstile> b' <\<sim>> b)"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_trans:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> b' <\<sim>> b'' \<Longrightarrow> P \<Turnstile> b <\<sim>> b''"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_subst:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P s \<Longrightarrow> bval b s = bval b' s"
  by (simp add: bequiv_up_to_def)


lemma equiv_up_to_seq:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> Q \<Turnstile> d \<sim> d' \<Longrightarrow>
  (\<And>s s'. (c,s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> Q s') \<Longrightarrow>
  P \<Turnstile> (c;; d) \<sim> (c';; d')"
  by (clarsimp simp: equiv_up_to_def) blast

lemma equiv_up_to_while_lemma_weak:
  shows "(d,s) \<Rightarrow> s' \<Longrightarrow>
         P \<Turnstile> b <\<sim>> b' \<Longrightarrow>
         P \<Turnstile> c \<sim> c' \<Longrightarrow>
         (\<And>s s'. (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b s \<Longrightarrow> P s') \<Longrightarrow>
         P s \<Longrightarrow>
         d = WHILE b DO c \<Longrightarrow>
         (WHILE b' DO c', s) \<Rightarrow> s'"
proof (induction rule: big_step_induct)
  case (WhileTrue b s1 c s2 s3)
  hence IH: "P s2 \<Longrightarrow> (WHILE b' DO c', s2) \<Rightarrow> s3" by auto
  from WhileTrue.prems
  have "P \<Turnstile> b <\<sim>> b'" by simp
  with \<open>bval b s1\<close> \<open>P s1\<close>
  have "bval b' s1" by (simp add: bequiv_up_to_def)
  moreover
  from WhileTrue.prems
  have "P \<Turnstile> c \<sim> c'" by simp
  with \<open>bval b s1\<close> \<open>P s1\<close> \<open>(c, s1) \<Rightarrow> s2\<close>
  have "(c', s1) \<Rightarrow> s2" by (simp add: equiv_up_to_def)
  moreover
  from WhileTrue.prems
  have "\<And>s s'. (c,s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b s \<Longrightarrow> P s'" by simp
  with \<open>P s1\<close> \<open>bval b s1\<close> \<open>(c, s1) \<Rightarrow> s2\<close>
  have "P s2" by simp
  hence "(WHILE b' DO c', s2) \<Rightarrow> s3" by (rule IH)
  ultimately
  show ?case by blast
next
  case WhileFalse
  thus ?case by (auto simp: bequiv_up_to_def)
qed (fastforce simp: equiv_up_to_def bequiv_up_to_def)+

lemma equiv_up_to_while_weak:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "P \<Turnstile> c \<sim> c'"
  assumes I: "\<And>s s'. (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b s \<Longrightarrow> P s'"
  shows "P \<Turnstile> WHILE b DO c \<sim> WHILE b' DO c'"
proof -
  from b have b': "P \<Turnstile> b' <\<sim>> b" by (simp add: bequiv_up_to_sym)

  from c b have c': "P \<Turnstile> c' \<sim> c" by (simp add: equiv_up_to_sym)

  from I
  have I': "\<And>s s'. (c', s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b' s \<Longrightarrow> P s'"
    by (auto dest!: equiv_up_toD1 [OF c'] simp: bequiv_up_to_subst [OF b'])

  note equiv_up_to_while_lemma_weak [OF _ b c]
       equiv_up_to_while_lemma_weak [OF _ b' c']
  thus ?thesis using I I' by (auto intro!: equiv_up_toI)
qed

lemma equiv_up_to_if_weak:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> c \<sim> c' \<Longrightarrow> P \<Turnstile> d \<sim> d' \<Longrightarrow>
   P \<Turnstile> IF b THEN c ELSE d \<sim> IF b' THEN c' ELSE d'"
  by (auto simp: bequiv_up_to_def equiv_up_to_def)

lemma equiv_up_to_if_True [intro!]:
  "(\<And>s. P s \<Longrightarrow> bval b s) \<Longrightarrow> P \<Turnstile> IF b THEN c1 ELSE c2 \<sim> c1"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_if_False [intro!]:
  "(\<And>s. P s \<Longrightarrow> \<not> bval b s) \<Longrightarrow> P \<Turnstile> IF b THEN c1 ELSE c2 \<sim> c2"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_while_False [intro!]:
  "(\<And>s. P s \<Longrightarrow> \<not> bval b s) \<Longrightarrow> P \<Turnstile> WHILE b DO c \<sim> SKIP"
  by (auto simp: equiv_up_to_def)

lemma while_never: "(c, s) \<Rightarrow> u \<Longrightarrow> c \<noteq> WHILE (Bc True) DO c'"
 by (induct rule: big_step_induct) auto

lemma equiv_up_to_while_True [intro!,simp]:
  "P \<Turnstile> WHILE Bc True DO c \<sim> WHILE Bc True DO SKIP"
  unfolding equiv_up_to_def
  by (blast dest: while_never)


end
