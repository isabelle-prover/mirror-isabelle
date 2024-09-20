(*  Title:      HOL/Quotient_Examples/Quotient_Message.thy
    Author:     Christian Urban

Message datatype, based on an older version by Larry Paulson.
*)

theory Quotient_Message
imports Main "HOL-Library.Quotient_Syntax"
begin

subsection\<open>Defining the Free Algebra\<close>

datatype
  freemsg = NONCE  nat
        | MPAIR  freemsg freemsg
        | CRYPT  nat freemsg
        | DECRYPT  nat freemsg

inductive
  msgrel::"freemsg \<Rightarrow> freemsg \<Rightarrow> bool" (infixl \<open>\<sim>\<close> 50)
where
  CD:    "CRYPT K (DECRYPT K X) \<sim> X"
| DC:    "DECRYPT K (CRYPT K X) \<sim> X"
| NONCE: "NONCE N \<sim> NONCE N"
| MPAIR: "\<lbrakk>X \<sim> X'; Y \<sim> Y'\<rbrakk> \<Longrightarrow> MPAIR X Y \<sim> MPAIR X' Y'"
| CRYPT: "X \<sim> X' \<Longrightarrow> CRYPT K X \<sim> CRYPT K X'"
| DECRYPT: "X \<sim> X' \<Longrightarrow> DECRYPT K X \<sim> DECRYPT K X'"
| SYM:   "X \<sim> Y \<Longrightarrow> Y \<sim> X"
| TRANS: "\<lbrakk>X \<sim> Y; Y \<sim> Z\<rbrakk> \<Longrightarrow> X \<sim> Z"

lemmas msgrel.intros[intro]

text\<open>Proving that it is an equivalence relation\<close>

lemma msgrel_refl: "X \<sim> X"
by (induct X) (auto intro: msgrel.intros)

theorem equiv_msgrel: "equivp msgrel"
proof (rule equivpI)
  show "reflp msgrel" by (rule reflpI) (simp add: msgrel_refl)
  show "symp msgrel" by (rule sympI) (blast intro: msgrel.SYM)
  show "transp msgrel" by (rule transpI) (blast intro: msgrel.TRANS)
qed

subsection\<open>Some Functions on the Free Algebra\<close>

subsubsection\<open>The Set of Nonces\<close>

primrec
  freenonces :: "freemsg \<Rightarrow> nat set"
where
  "freenonces (NONCE N) = {N}"
| "freenonces (MPAIR X Y) = freenonces X \<union> freenonces Y"
| "freenonces (CRYPT K X) = freenonces X"
| "freenonces (DECRYPT K X) = freenonces X"

theorem msgrel_imp_eq_freenonces:
  assumes a: "U \<sim> V"
  shows "freenonces U = freenonces V"
  using a by (induct) (auto)

subsubsection\<open>The Left Projection\<close>

text\<open>A function to return the left part of the top pair in a message.  It will
be lifted to the initial algebra, to serve as an example of that process.\<close>
primrec
  freeleft :: "freemsg \<Rightarrow> freemsg"
where
  "freeleft (NONCE N) = NONCE N"
| "freeleft (MPAIR X Y) = X"
| "freeleft (CRYPT K X) = freeleft X"
| "freeleft (DECRYPT K X) = freeleft X"

text\<open>This theorem lets us prove that the left function respects the
equivalence relation.  It also helps us prove that MPair
  (the abstract constructor) is injective\<close>
lemma msgrel_imp_eqv_freeleft_aux:
  shows "freeleft U \<sim> freeleft U"
  by (fact msgrel_refl)

theorem msgrel_imp_eqv_freeleft:
  assumes a: "U \<sim> V"
  shows "freeleft U \<sim> freeleft V"
  using a
  by (induct) (auto intro: msgrel_imp_eqv_freeleft_aux)

subsubsection\<open>The Right Projection\<close>

text\<open>A function to return the right part of the top pair in a message.\<close>
primrec
  freeright :: "freemsg \<Rightarrow> freemsg"
where
  "freeright (NONCE N) = NONCE N"
| "freeright (MPAIR X Y) = Y"
| "freeright (CRYPT K X) = freeright X"
| "freeright (DECRYPT K X) = freeright X"

text\<open>This theorem lets us prove that the right function respects the
equivalence relation.  It also helps us prove that MPair
  (the abstract constructor) is injective\<close>
lemma msgrel_imp_eqv_freeright_aux:
  shows "freeright U \<sim> freeright U"
  by (fact msgrel_refl)

theorem msgrel_imp_eqv_freeright:
  assumes a: "U \<sim> V"
  shows "freeright U \<sim> freeright V"
  using a
  by (induct) (auto intro: msgrel_imp_eqv_freeright_aux)

subsubsection\<open>The Discriminator for Constructors\<close>

text\<open>A function to distinguish nonces, mpairs and encryptions\<close>
primrec
  freediscrim :: "freemsg \<Rightarrow> int"
where
   "freediscrim (NONCE N) = 0"
 | "freediscrim (MPAIR X Y) = 1"
 | "freediscrim (CRYPT K X) = freediscrim X + 2"
 | "freediscrim (DECRYPT K X) = freediscrim X - 2"

text\<open>This theorem helps us prove \<^term>\<open>Nonce N \<noteq> MPair X Y\<close>\<close>
theorem msgrel_imp_eq_freediscrim:
  assumes a: "U \<sim> V"
  shows "freediscrim U = freediscrim V"
  using a by (induct) (auto)

subsection\<open>The Initial Algebra: A Quotiented Message Type\<close>

quotient_type msg = freemsg / msgrel
  by (rule equiv_msgrel)

text\<open>The abstract message constructors\<close>

quotient_definition
  "Nonce :: nat \<Rightarrow> msg"
is
  "NONCE"
done

quotient_definition
  "MPair :: msg \<Rightarrow> msg \<Rightarrow> msg"
is
  "MPAIR"
by (rule MPAIR)

quotient_definition
  "Crypt :: nat \<Rightarrow> msg \<Rightarrow> msg"
is
  "CRYPT"
by (rule CRYPT)

quotient_definition
  "Decrypt :: nat \<Rightarrow> msg \<Rightarrow> msg"
is
  "DECRYPT"
by (rule DECRYPT)

text\<open>Establishing these two equations is the point of the whole exercise\<close>
theorem CD_eq [simp]:
  shows "Crypt K (Decrypt K X) = X"
  by (lifting CD)

theorem DC_eq [simp]:
  shows "Decrypt K (Crypt K X) = X"
  by (lifting DC)

subsection\<open>The Abstract Function to Return the Set of Nonces\<close>

quotient_definition
   "nonces:: msg \<Rightarrow> nat set"
is
  "freenonces"
by (rule msgrel_imp_eq_freenonces)

text\<open>Now prove the four equations for \<^term>\<open>nonces\<close>\<close>

lemma nonces_Nonce [simp]:
  shows "nonces (Nonce N) = {N}"
  by (lifting freenonces.simps(1))

lemma nonces_MPair [simp]:
  shows "nonces (MPair X Y) = nonces X \<union> nonces Y"
  by (lifting freenonces.simps(2))

lemma nonces_Crypt [simp]:
  shows "nonces (Crypt K X) = nonces X"
  by (lifting freenonces.simps(3))

lemma nonces_Decrypt [simp]:
  shows "nonces (Decrypt K X) = nonces X"
  by (lifting freenonces.simps(4))

subsection\<open>The Abstract Function to Return the Left Part\<close>

quotient_definition
  "left:: msg \<Rightarrow> msg"
is
  "freeleft"
by (rule msgrel_imp_eqv_freeleft)

lemma left_Nonce [simp]:
  shows "left (Nonce N) = Nonce N"
  by (lifting freeleft.simps(1))

lemma left_MPair [simp]:
  shows "left (MPair X Y) = X"
  by (lifting freeleft.simps(2))

lemma left_Crypt [simp]:
  shows "left (Crypt K X) = left X"
  by (lifting freeleft.simps(3))

lemma left_Decrypt [simp]:
  shows "left (Decrypt K X) = left X"
  by (lifting freeleft.simps(4))

subsection\<open>The Abstract Function to Return the Right Part\<close>

quotient_definition
  "right:: msg \<Rightarrow> msg"
is
  "freeright"
by (rule msgrel_imp_eqv_freeright)

text\<open>Now prove the four equations for \<^term>\<open>right\<close>\<close>

lemma right_Nonce [simp]:
  shows "right (Nonce N) = Nonce N"
  by (lifting freeright.simps(1))

lemma right_MPair [simp]:
  shows "right (MPair X Y) = Y"
  by (lifting freeright.simps(2))

lemma right_Crypt [simp]:
  shows "right (Crypt K X) = right X"
  by (lifting freeright.simps(3))

lemma right_Decrypt [simp]:
  shows "right (Decrypt K X) = right X"
  by (lifting freeright.simps(4))

subsection\<open>Injectivity Properties of Some Constructors\<close>

text\<open>Can also be proved using the function \<^term>\<open>nonces\<close>\<close>
lemma Nonce_Nonce_eq [iff]:
  shows "(Nonce m = Nonce n) = (m = n)"
proof
  assume "Nonce m = Nonce n"
  then show "m = n" 
    by (descending) (drule msgrel_imp_eq_freenonces, simp)
next
  assume "m = n"
  then show "Nonce m = Nonce n" by simp
qed

lemma MPair_imp_eq_left:
  assumes eq: "MPair X Y = MPair X' Y'"
  shows "X = X'"
  using eq 
  by (descending) (drule msgrel_imp_eqv_freeleft, simp)

lemma MPair_imp_eq_right:
  shows "MPair X Y = MPair X' Y' \<Longrightarrow> Y = Y'"
  by (descending) (drule msgrel_imp_eqv_freeright, simp)

theorem MPair_MPair_eq [iff]:
  shows "(MPair X Y = MPair X' Y') = (X=X' & Y=Y')"
  by (blast dest: MPair_imp_eq_left MPair_imp_eq_right)

theorem Nonce_neq_MPair [iff]:
  shows "Nonce N \<noteq> MPair X Y"
  by (descending) (auto dest: msgrel_imp_eq_freediscrim)

text\<open>Example suggested by a referee\<close>

theorem Crypt_Nonce_neq_Nonce:
  shows "Crypt K (Nonce M) \<noteq> Nonce N"
  by (descending) (auto dest: msgrel_imp_eq_freediscrim) 

text\<open>...and many similar results\<close>

theorem Crypt2_Nonce_neq_Nonce:
  shows "Crypt K (Crypt K' (Nonce M)) \<noteq> Nonce N"
  by (descending) (auto dest: msgrel_imp_eq_freediscrim)

theorem Crypt_Crypt_eq [iff]:
  shows "(Crypt K X = Crypt K X') = (X=X')"
proof
  assume "Crypt K X = Crypt K X'"
  hence "Decrypt K (Crypt K X) = Decrypt K (Crypt K X')" by simp
  thus "X = X'" by simp
next
  assume "X = X'"
  thus "Crypt K X = Crypt K X'" by simp
qed

theorem Decrypt_Decrypt_eq [iff]:
  shows "(Decrypt K X = Decrypt K X') = (X=X')"
proof
  assume "Decrypt K X = Decrypt K X'"
  hence "Crypt K (Decrypt K X) = Crypt K (Decrypt K X')" by simp
  thus "X = X'" by simp
next
  assume "X = X'"
  thus "Decrypt K X = Decrypt K X'" by simp
qed

lemma msg_induct [case_names Nonce MPair Crypt Decrypt, cases type: msg]:
  assumes N: "\<And>N. P (Nonce N)"
      and M: "\<And>X Y. \<lbrakk>P X; P Y\<rbrakk> \<Longrightarrow> P (MPair X Y)"
      and C: "\<And>K X. P X \<Longrightarrow> P (Crypt K X)"
      and D: "\<And>K X. P X \<Longrightarrow> P (Decrypt K X)"
  shows "P msg"
  using N M C D 
  by (descending) (auto intro: freemsg.induct)


subsection\<open>The Abstract Discriminator\<close>

text\<open>However, as \<open>Crypt_Nonce_neq_Nonce\<close> above illustrates, we don't
need this function in order to prove discrimination theorems.\<close>

quotient_definition
  "discrim:: msg \<Rightarrow> int"
is
  "freediscrim"
by (rule msgrel_imp_eq_freediscrim)

text\<open>Now prove the four equations for \<^term>\<open>discrim\<close>\<close>

lemma discrim_Nonce [simp]:
  shows "discrim (Nonce N) = 0"
  by (lifting freediscrim.simps(1))

lemma discrim_MPair [simp]:
  shows "discrim (MPair X Y) = 1"
  by (lifting freediscrim.simps(2))

lemma discrim_Crypt [simp]:
  shows "discrim (Crypt K X) = discrim X + 2"
  by (lifting freediscrim.simps(3))

lemma discrim_Decrypt [simp]:
  shows "discrim (Decrypt K X) = discrim X - 2"
  by (lifting freediscrim.simps(4))

end

