(*  Title:      HOL/Metis_Examples/Message.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring message authentication.
*)

section \<open>Metis Example Featuring Message Authentication\<close>

theory Message
imports Main
begin

declare [[metis_new_skolem]]

lemma strange_Un_eq [simp]: "A \<union> (B \<union> A) = B \<union> A"
by (metis Un_commute Un_left_absorb)

type_synonym key = nat

consts
  all_symmetric :: bool        \<comment> \<open>true if all keys are symmetric\<close>
  invKey        :: "key=>key"  \<comment> \<open>inverse of a symmetric key\<close>

specification (invKey)
  invKey [simp]: "invKey (invKey K) = K"
  invKey_symmetric: "all_symmetric --> invKey = id"
by (metis id_apply)


text\<open>The inverse of a symmetric key is itself; that of a public key
      is the private key and vice versa\<close>

definition symKeys :: "key set" where
  "symKeys == {K. invKey K = K}"

datatype  \<comment> \<open>We allow any number of friendly agents\<close>
  agent = Server | Friend nat | Spy

datatype
     msg = Agent  agent     \<comment> \<open>Agent names\<close>
         | Number nat       \<comment> \<open>Ordinary integers, timestamps, ...\<close>
         | Nonce  nat       \<comment> \<open>Unguessable nonces\<close>
         | Key    key       \<comment> \<open>Crypto keys\<close>
         | Hash   msg       \<comment> \<open>Hashing\<close>
         | MPair  msg msg   \<comment> \<open>Compound messages\<close>
         | Crypt  key msg   \<comment> \<open>Encryption, public- or shared-key\<close>


text\<open>Concrete syntax: messages appear as \<open>\<lbrace>A,B,NA\<rbrace>\<close>, etc...\<close>
nonterminal mtuple_args
syntax
  "" :: "'a \<Rightarrow> mtuple_args"  ("_")
  "_MTuple_args" :: "'a \<Rightarrow> mtuple_args \<Rightarrow> mtuple_args"  ("_,/ _")
  "_MTuple" :: "['a, mtuple_args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>)")
syntax_consts
  "_MTuple_args" "_MTuple" \<rightleftharpoons> MPair
translations
  "\<lbrace>x, y, z\<rbrace>" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<rbrace>"
  "\<lbrace>x, y\<rbrace>" \<rightleftharpoons> "CONST MPair x y"


definition HPair :: "[msg,msg] => msg" ("(4Hash[_] /_)" [0, 1000]) where
    \<comment> \<open>Message Y paired with a MAC computed with the help of X\<close>
    "Hash[X] Y == \<lbrace> Hash\<lbrace>X,Y\<rbrace>, Y\<rbrace>"

definition keysFor :: "msg set => key set" where
    \<comment> \<open>Keys useful to decrypt elements of a message set\<close>
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"


subsubsection\<open>Inductive Definition of All Parts" of a Message\<close>

inductive_set
  parts :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro]:               "X \<in> H ==> X \<in> parts H"
  | Fst:         "\<lbrace>X,Y\<rbrace>   \<in> parts H ==> X \<in> parts H"
  | Snd:         "\<lbrace>X,Y\<rbrace>   \<in> parts H ==> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H ==> X \<in> parts H"

lemma parts_mono: "G \<subseteq> H ==> parts(G) \<subseteq> parts(H)"
apply auto
apply (erule parts.induct)
   apply (metis parts.Inj rev_subsetD)
  apply (metis parts.Fst)
 apply (metis parts.Snd)
by (metis parts.Body)

text\<open>Equations hold because constructors are injective.\<close>
lemma Friend_image_eq [simp]: "(Friend x \<in> Friend`A) = (x\<in>A)"
by (metis agent.inject image_iff)

lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x \<in> A)"
by (metis image_iff msg.inject(4))

lemma Nonce_Key_image_eq [simp]: "Nonce x \<notin> Key`A"
by (metis image_iff msg.distinct(23))


subsubsection\<open>Inverse of keys\<close>

lemma invKey_eq [simp]: "(invKey K = invKey K') = (K = K')"
by (metis invKey)


subsection\<open>keysFor operator\<close>

lemma keysFor_empty [simp]: "keysFor {} = {}"
by (unfold keysFor_def, blast)

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
by (unfold keysFor_def, blast)

lemma keysFor_UN [simp]: "keysFor (\<Union>i\<in>A. H i) = (\<Union>i\<in>A. keysFor (H i))"
by (unfold keysFor_def, blast)

text\<open>Monotonicity\<close>
lemma keysFor_mono: "G \<subseteq> H ==> keysFor(G) \<subseteq> keysFor(H)"
by (unfold keysFor_def, blast)

lemma keysFor_insert_Agent [simp]: "keysFor (insert (Agent A) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Number [simp]: "keysFor (insert (Number N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Hash [simp]: "keysFor (insert (Hash X) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_MPair [simp]: "keysFor (insert \<lbrace>X,Y\<rbrace> H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Crypt [simp]:
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)"
by (unfold keysFor_def, auto)

lemma keysFor_image_Key [simp]: "keysFor (Key`E) = {}"
by (unfold keysFor_def, auto)

lemma Crypt_imp_invKey_keysFor: "Crypt K X \<in> H ==> invKey K \<in> keysFor H"
by (unfold keysFor_def, blast)


subsection\<open>Inductive relation "parts"\<close>

lemma MPair_parts:
     "[| \<lbrace>X,Y\<rbrace> \<in> parts H;
         [| X \<in> parts H; Y \<in> parts H |] ==> P |] ==> P"
by (blast dest: parts.Fst parts.Snd)

declare MPair_parts [elim!] parts.Body [dest!]
text\<open>NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE.
  \<open>MPair_parts\<close> is left as SAFE because it speeds up proofs.
  The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.\<close>

lemma parts_increasing: "H \<subseteq> parts(H)"
by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty [simp]: "parts{} = {}"
apply safe
apply (erule parts.induct)
apply blast+
done

lemma parts_emptyE [elim!]: "X\<in> parts{} ==> P"
by simp

text\<open>WARNING: loops if H = {Y}, therefore must not be repeated!\<close>
lemma parts_singleton: "X\<in> parts H ==> \<exists>Y\<in>H. X\<in> parts {Y}"
apply (erule parts.induct)
apply fast+
done


subsubsection\<open>Unions\<close>

lemma parts_Un_subset1: "parts(G) \<union> parts(H) \<subseteq> parts(G \<union> H)"
by (intro Un_least parts_mono Un_upper1 Un_upper2)

lemma parts_Un_subset2: "parts(G \<union> H) \<subseteq> parts(G) \<union> parts(H)"
apply (rule subsetI)
apply (erule parts.induct, blast+)
done

lemma parts_Un [simp]: "parts(G \<union> H) = parts(G) \<union> parts(H)"
by (intro equalityI parts_Un_subset1 parts_Un_subset2)

lemma parts_insert: "parts (insert X H) = parts {X} \<union> parts H"
apply (subst insert_is_Un [of _ H])
apply (simp only: parts_Un)
done

lemma parts_insert2:
     "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
by (metis Un_commute Un_empty_left Un_empty_right Un_insert_left Un_insert_right parts_Un)


lemma parts_UN_subset1: "(\<Union>x\<in>A. parts(H x)) \<subseteq> parts(\<Union>x\<in>A. H x)"
by (intro UN_least parts_mono UN_upper)

lemma parts_UN_subset2: "parts(\<Union>x\<in>A. H x) \<subseteq> (\<Union>x\<in>A. parts(H x))"
apply (rule subsetI)
apply (erule parts.induct, blast+)
done


text\<open>This allows \<open>blast\<close> to simplify occurrences of
  \<^term>\<open>parts(G\<union>H)\<close> in the assumption.\<close>
lemmas in_parts_UnE = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE]
declare in_parts_UnE [elim!]

lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])

subsubsection\<open>Idempotence and transitivity\<close>

lemma parts_partsD [dest!]: "X\<in> parts (parts H) ==> X\<in> parts H"
by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) = (G \<subseteq> parts H)"
apply (rule iffI)
apply (metis Un_absorb1 Un_subset_iff parts_Un parts_increasing)
apply (metis parts_idem parts_mono)
done

lemma parts_trans: "[| X\<in> parts G;  G \<subseteq> parts H |] ==> X\<in> parts H"
by (blast dest: parts_mono)

lemma parts_cut: "[|Y\<in> parts (insert X G);  X\<in> parts H|] ==> Y\<in> parts(G \<union> H)"
by (metis (no_types) Un_insert_left Un_insert_right insert_absorb le_supE
          parts_Un parts_idem parts_increasing parts_trans)

subsubsection\<open>Rewrite rules for pulling out atomic messages\<close>

lemmas parts_insert_eq_I = equalityI [OF subsetI parts_insert_subset]


lemma parts_insert_Agent [simp]:
     "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Nonce [simp]:
     "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Number [simp]:
     "parts (insert (Number N) H) = insert (Number N) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Key [simp]:
     "parts (insert (Key K) H) = insert (Key K) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Hash [simp]:
     "parts (insert (Hash X) H) = insert (Hash X) (parts H)"
apply (rule parts_insert_eq_I)
apply (erule parts.induct, auto)
done

lemma parts_insert_Crypt [simp]:
     "parts (insert (Crypt K X) H) =
          insert (Crypt K X) (parts (insert X H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
apply (blast intro: parts.Body)
done

lemma parts_insert_MPair [simp]:
     "parts (insert \<lbrace>X,Y\<rbrace> H) =
          insert \<lbrace>X,Y\<rbrace> (parts (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
apply (blast intro: parts.Fst parts.Snd)+
done

lemma parts_image_Key [simp]: "parts (Key`N) = Key`N"
apply auto
apply (erule parts.induct, auto)
done

lemma msg_Nonce_supply: "\<exists>N. \<forall>n. N\<le>n --> Nonce n \<notin> parts {msg}"
apply (induct_tac "msg")
apply (simp_all add: parts_insert2)
apply (metis Suc_n_not_le_n)
apply (metis le_trans linorder_linear)
done

subsection\<open>Inductive relation "analz"\<close>

text\<open>Inductive definition of "analz" -- what can be broken down from a set of
    messages, including keys.  A form of downward closure.  Pairs can
    be taken apart; messages decrypted with known keys.\<close>

inductive_set
  analz :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro,simp] :    "X \<in> H ==> X \<in> analz H"
  | Fst:     "\<lbrace>X,Y\<rbrace> \<in> analz H ==> X \<in> analz H"
  | Snd:     "\<lbrace>X,Y\<rbrace> \<in> analz H ==> Y \<in> analz H"
  | Decrypt [dest]:
             "[|Crypt K X \<in> analz H; Key(invKey K) \<in> analz H|] ==> X \<in> analz H"


text\<open>Monotonicity; Lemma 1 of Lowe's paper\<close>
lemma analz_mono: "G\<subseteq>H ==> analz(G) \<subseteq> analz(H)"
apply auto
apply (erule analz.induct)
apply (auto dest: analz.Fst analz.Snd)
done

text\<open>Making it safe speeds up proofs\<close>
lemma MPair_analz [elim!]:
     "[| \<lbrace>X,Y\<rbrace> \<in> analz H;
             [| X \<in> analz H; Y \<in> analz H |] ==> P
          |] ==> P"
by (blast dest: analz.Fst analz.Snd)

lemma analz_increasing: "H \<subseteq> analz(H)"
by blast

lemma analz_subset_parts: "analz H \<subseteq> parts H"
apply (rule subsetI)
apply (erule analz.induct, blast+)
done

lemmas analz_into_parts = analz_subset_parts [THEN subsetD]

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD]

lemma parts_analz [simp]: "parts (analz H) = parts H"
apply (rule equalityI)
apply (metis analz_subset_parts parts_subset_iff)
apply (metis analz_increasing parts_mono)
done


lemma analz_parts [simp]: "analz (parts H) = parts H"
apply auto
apply (erule analz.induct, auto)
done

lemmas analz_insertI = subset_insertI [THEN analz_mono, THEN [2] rev_subsetD]

subsubsection\<open>General equational properties\<close>

lemma analz_empty [simp]: "analz{} = {}"
apply safe
apply (erule analz.induct, blast+)
done

text\<open>Converse fails: we can analz more from the union than from the
  separate parts, as a key in one might decrypt a message in the other\<close>
lemma analz_Un: "analz(G) \<union> analz(H) \<subseteq> analz(G \<union> H)"
by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insert: "insert X (analz H) \<subseteq> analz(insert X H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

subsubsection\<open>Rewrite rules for pulling out atomic messages\<close>

lemmas analz_insert_eq_I = equalityI [OF subsetI analz_insert]

lemma analz_insert_Agent [simp]:
     "analz (insert (Agent agt) H) = insert (Agent agt) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Nonce [simp]:
     "analz (insert (Nonce N) H) = insert (Nonce N) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Number [simp]:
     "analz (insert (Number N) H) = insert (Number N) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_Hash [simp]:
     "analz (insert (Hash X) H) = insert (Hash X) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

text\<open>Can only pull out Keys if they are not needed to decrypt the rest\<close>
lemma analz_insert_Key [simp]:
    "K \<notin> keysFor (analz H) ==>
          analz (insert (Key K) H) = insert (Key K) (analz H)"
apply (unfold keysFor_def)
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)
done

lemma analz_insert_MPair [simp]:
     "analz (insert \<lbrace>X,Y\<rbrace> H) =
          insert \<lbrace>X,Y\<rbrace> (analz (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct, auto)
apply (erule analz.induct)
apply (blast intro: analz.Fst analz.Snd)+
done

text\<open>Can pull out enCrypted message if the Key is not known\<close>
lemma analz_insert_Crypt:
     "Key (invKey K) \<notin> analz H
      ==> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule analz_insert_eq_I)
apply (erule analz.induct, auto)

done

lemma lemma1: "Key (invKey K) \<in> analz H ==>
               analz (insert (Crypt K X) H) \<subseteq>
               insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule_tac x = x in analz.induct, auto)
done

lemma lemma2: "Key (invKey K) \<in> analz H ==>
               insert (Crypt K X) (analz (insert X H)) \<subseteq>
               analz (insert (Crypt K X) H)"
apply auto
apply (erule_tac x = x in analz.induct, auto)
apply (blast intro: analz_insertI analz.Decrypt)
done

lemma analz_insert_Decrypt:
     "Key (invKey K) \<in> analz H ==>
               analz (insert (Crypt K X) H) =
               insert (Crypt K X) (analz (insert X H))"
by (intro equalityI lemma1 lemma2)

text\<open>Case analysis: either the message is secure, or it is not! Effective,
but can cause subgoals to blow up! Use with \<open>if_split\<close>; apparently
\<open>split_tac\<close> does not cope with patterns such as \<^term>\<open>analz (insert
(Crypt K X) H)\<close>\<close>
lemma analz_Crypt_if [simp]:
     "analz (insert (Crypt K X) H) =
          (if (Key (invKey K) \<in> analz H)
           then insert (Crypt K X) (analz (insert X H))
           else insert (Crypt K X) (analz H))"
by (simp add: analz_insert_Crypt analz_insert_Decrypt)


text\<open>This rule supposes "for the sake of argument" that we have the key.\<close>
lemma analz_insert_Crypt_subset:
     "analz (insert (Crypt K X) H) \<subseteq>
           insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule analz.induct, auto)
done


lemma analz_image_Key [simp]: "analz (Key`N) = Key`N"
apply auto
apply (erule analz.induct, auto)
done


subsubsection\<open>Idempotence and transitivity\<close>

lemma analz_analzD [dest!]: "X\<in> analz (analz H) ==> X\<in> analz H"
by (erule analz.induct, blast+)

lemma analz_idem [simp]: "analz (analz H) = analz H"
by blast

lemma analz_subset_iff [simp]: "(analz G \<subseteq> analz H) = (G \<subseteq> analz H)"
apply (rule iffI)
apply (iprover intro: subset_trans analz_increasing)
apply (frule analz_mono, simp)
done

lemma analz_trans: "[| X\<in> analz G;  G \<subseteq> analz H |] ==> X\<in> analz H"
by (drule analz_mono, blast)


declare analz_trans[intro]

lemma analz_cut: "[| Y\<in> analz (insert X H);  X\<in> analz H |] ==> Y\<in> analz H"
by (metis analz_idem analz_increasing analz_mono insert_absorb insert_mono insert_subset)

text\<open>This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated.\<close>
lemma analz_insert_eq: "X\<in> analz H ==> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)


text\<open>A congruence rule for "analz"\<close>

lemma analz_subset_cong:
     "[| analz G \<subseteq> analz G'; analz H \<subseteq> analz H' |]
      ==> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply simp
apply (metis Un_absorb2 Un_commute Un_subset_iff Un_upper1 Un_upper2 analz_mono)
done


lemma analz_cong:
     "[| analz G = analz G'; analz H = analz H'
               |] ==> analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all)

lemma analz_insert_cong:
     "analz H = analz H' ==> analz(insert X H) = analz(insert X H')"
by (force simp only: insert_def intro!: analz_cong)

text\<open>If there are no pairs or encryptions then analz does nothing\<close>
lemma analz_trivial:
     "[| \<forall>X Y. \<lbrace>X,Y\<rbrace> \<notin> H;  \<forall>X K. Crypt K X \<notin> H |] ==> analz H = H"
apply safe
apply (erule analz.induct, blast+)
done


subsection\<open>Inductive relation "synth"\<close>

text\<open>Inductive definition of "synth" -- what can be built up from a set of
    messages.  A form of upward closure.  Pairs can be built, messages
    encrypted with known keys.  Agent names are public domain.
    Numbers can be guessed, but Nonces cannot be.\<close>

inductive_set
  synth :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj    [intro]:   "X \<in> H ==> X \<in> synth H"
  | Agent  [intro]:   "Agent agt \<in> synth H"
  | Number [intro]:   "Number n  \<in> synth H"
  | Hash   [intro]:   "X \<in> synth H ==> Hash X \<in> synth H"
  | MPair  [intro]:   "[|X \<in> synth H;  Y \<in> synth H|] ==> \<lbrace>X,Y\<rbrace> \<in> synth H"
  | Crypt  [intro]:   "[|X \<in> synth H;  Key(K) \<in> H|] ==> Crypt K X \<in> synth H"

text\<open>Monotonicity\<close>
lemma synth_mono: "G\<subseteq>H ==> synth(G) \<subseteq> synth(H)"
  by (auto, erule synth.induct, auto)

text\<open>NO \<open>Agent_synth\<close>, as any Agent name can be synthesized.
  The same holds for \<^term>\<open>Number\<close>\<close>
inductive_cases Nonce_synth [elim!]: "Nonce n \<in> synth H"
inductive_cases Key_synth   [elim!]: "Key K \<in> synth H"
inductive_cases Hash_synth  [elim!]: "Hash X \<in> synth H"
inductive_cases MPair_synth [elim!]: "\<lbrace>X,Y\<rbrace> \<in> synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X \<in> synth H"


lemma synth_increasing: "H \<subseteq> synth(H)"
by blast

subsubsection\<open>Unions\<close>

text\<open>Converse fails: we can synth more from the union than from the
  separate parts, building a compound message using elements of each.\<close>
lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
by (metis insert_iff insert_subset subset_insertI synth.Inj synth_mono)

subsubsection\<open>Idempotence and transitivity\<close>

lemma synth_synthD [dest!]: "X\<in> synth (synth H) ==> X\<in> synth H"
by (erule synth.induct, blast+)

lemma synth_idem: "synth (synth H) = synth H"
by blast

lemma synth_subset_iff [simp]: "(synth G \<subseteq> synth H) = (G \<subseteq> synth H)"
apply (rule iffI)
apply (iprover intro: subset_trans synth_increasing)
apply (frule synth_mono, simp add: synth_idem)
done

lemma synth_trans: "[| X\<in> synth G;  G \<subseteq> synth H |] ==> X\<in> synth H"
by (drule synth_mono, blast)

lemma synth_cut: "[| Y\<in> synth (insert X H);  X\<in> synth H |] ==> Y\<in> synth H"
by (metis insert_absorb insert_mono insert_subset synth_idem synth_increasing synth_mono)

lemma Agent_synth [simp]: "Agent A \<in> synth H"
by blast

lemma Number_synth [simp]: "Number n \<in> synth H"
by blast

lemma Nonce_synth_eq [simp]: "(Nonce N \<in> synth H) = (Nonce N \<in> H)"
by blast

lemma Key_synth_eq [simp]: "(Key K \<in> synth H) = (Key K \<in> H)"
by blast

lemma Crypt_synth_eq [simp]:
     "Key K \<notin> H ==> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
by blast


lemma keysFor_synth [simp]:
    "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
by (unfold keysFor_def, blast)


subsubsection\<open>Combinations of parts, analz and synth\<close>

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct)
apply (metis UnCI)
apply (metis MPair_synth UnCI UnE insert_absorb insert_subset parts.Fst parts_increasing)
apply (metis MPair_synth UnCI UnE insert_absorb insert_subset parts.Snd parts_increasing)
apply (metis Body Crypt_synth UnCI UnE insert_absorb insert_subset parts_increasing)
apply (metis Un_subset_iff parts_increasing parts_mono synth_increasing)
done

lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (rule equalityI)
apply (metis analz_idem analz_subset_cong order_eq_refl)
apply (metis analz_increasing analz_subset_cong order_eq_refl)
done

declare analz_mono [intro] analz.Fst [intro] analz.Snd [intro] Un_least [intro]

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct)
apply (metis UnCI UnE Un_commute analz.Inj)
apply (metis MPair_synth UnCI UnE Un_commute analz.Fst analz.Inj)
apply (metis MPair_synth UnCI UnE Un_commute analz.Inj analz.Snd)
apply (blast intro: analz.Decrypt)
apply blast
done

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
proof -
  have "\<forall>x\<^sub>2 x\<^sub>1. synth x\<^sub>1 \<union> analz (x\<^sub>1 \<union> x\<^sub>2) = analz (synth x\<^sub>1 \<union> x\<^sub>2)" by (metis Un_commute analz_synth_Un)
  hence "\<forall>x\<^sub>1. synth x\<^sub>1 \<union> analz x\<^sub>1 = analz (synth x\<^sub>1 \<union> {})" by (metis Un_empty_right)
  hence "\<forall>x\<^sub>1. synth x\<^sub>1 \<union> analz x\<^sub>1 = analz (synth x\<^sub>1)" by (metis Un_empty_right)
  hence "\<forall>x\<^sub>1. analz x\<^sub>1 \<union> synth x\<^sub>1 = analz (synth x\<^sub>1)" by (metis Un_commute)
  thus "analz (synth H) = analz H \<union> synth H" by metis
qed


subsubsection\<open>For reasoning about the Fake rule in traces\<close>

lemma parts_insert_subset_Un: "X \<in> G ==> parts(insert X H) \<subseteq> parts G \<union> parts H"
proof -
  assume "X \<in> G"
  hence "\<forall>x\<^sub>1. G \<subseteq> x\<^sub>1 \<longrightarrow> X \<in> x\<^sub>1 " by auto
  hence "\<forall>x\<^sub>1. X \<in> G \<union> x\<^sub>1" by (metis Un_upper1)
  hence "insert X H \<subseteq> G \<union> H" by (metis Un_upper2 insert_subset)
  hence "parts (insert X H) \<subseteq> parts (G \<union> H)" by (metis parts_mono)
  thus "parts (insert X H) \<subseteq> parts G \<union> parts H" by (metis parts_Un)
qed

lemma Fake_parts_insert:
     "X \<in> synth (analz H) ==>
      parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
proof -
  assume A1: "X \<in> synth (analz H)"
  have F1: "\<forall>x\<^sub>1. analz x\<^sub>1 \<union> synth (analz x\<^sub>1) = analz (synth (analz x\<^sub>1))"
    by (metis analz_idem analz_synth)
  have F2: "\<forall>x\<^sub>1. parts x\<^sub>1 \<union> synth (analz x\<^sub>1) = parts (synth (analz x\<^sub>1))"
    by (metis parts_analz parts_synth)
  have F3: "X \<in> synth (analz H)" using A1 by metis
  have "\<forall>x\<^sub>2 x\<^sub>1::msg set. x\<^sub>1 \<le> sup x\<^sub>1 x\<^sub>2" by (metis inf_sup_ord(3))
  hence F4: "\<forall>x\<^sub>1. analz x\<^sub>1 \<subseteq> analz (synth x\<^sub>1)" by (metis analz_synth)
  have F5: "X \<in> synth (analz H)" using F3 by metis
  have "\<forall>x\<^sub>1. analz x\<^sub>1 \<subseteq> synth (analz x\<^sub>1)
         \<longrightarrow> analz (synth (analz x\<^sub>1)) = synth (analz x\<^sub>1)"
    using F1 by (metis subset_Un_eq)
  hence F6: "\<forall>x\<^sub>1. analz (synth (analz x\<^sub>1)) = synth (analz x\<^sub>1)"
    by (metis synth_increasing)
  have "\<forall>x\<^sub>1. x\<^sub>1 \<subseteq> analz (synth x\<^sub>1)" using F4 by (metis analz_subset_iff)
  hence "\<forall>x\<^sub>1. x\<^sub>1 \<subseteq> analz (synth (analz x\<^sub>1))" by (metis analz_subset_iff)
  hence "\<forall>x\<^sub>1. x\<^sub>1 \<subseteq> synth (analz x\<^sub>1)" using F6 by metis
  hence "H \<subseteq> synth (analz H)" by metis
  hence "H \<subseteq> synth (analz H) \<and> X \<in> synth (analz H)" using F5 by metis
  hence "insert X H \<subseteq> synth (analz H)" by (metis insert_subset)
  hence "parts (insert X H) \<subseteq> parts (synth (analz H))" by (metis parts_mono)
  hence "parts (insert X H) \<subseteq> parts H \<union> synth (analz H)" using F2 by metis
  thus "parts (insert X H) \<subseteq> synth (analz H) \<union> parts H" by (metis Un_commute)
qed

lemma Fake_parts_insert_in_Un:
     "[|Z \<in> parts (insert X H);  X \<in> synth (analz H)|]
      ==> Z \<in>  synth (analz H) \<union> parts H"
by (blast dest: Fake_parts_insert [THEN subsetD, dest])

declare synth_mono [intro]

lemma Fake_analz_insert:
     "X \<in> synth (analz G) ==>
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
by (metis Un_commute Un_insert_left Un_insert_right Un_upper1 analz_analz_Un
          analz_mono analz_synth_Un insert_absorb)

lemma Fake_analz_insert_simpler:
     "X \<in> synth (analz G) ==>
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
apply (rule subsetI)
apply (subgoal_tac "x \<in> analz (synth (analz G) \<union> H) ")
apply (metis Un_commute analz_analz_Un analz_synth_Un)
by (metis Un_upper1 Un_upper2 analz_mono insert_absorb insert_subset)

end
