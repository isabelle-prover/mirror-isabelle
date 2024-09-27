(*  Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)(*<*)

section\<open>Theory of Agents and Messages for Security Protocols\<close>

theory Message imports "../Setup" begin

(*Needed occasionally with spy_analz_tac, e.g. in analz_insert_Key_newK*)
lemma [simp] : "A \<union> (B \<union> A) = B \<union> A"
by blast
(*>*)

section\<open>Agents and Messages\<close>

text \<open>
All protocol specifications refer to a syntactic theory of messages. 
Datatype
\<open>agent\<close> introduces the constant \<open>Server\<close> (a trusted central
machine, needed for some protocols), an infinite population of
friendly agents, and the~\<open>Spy\<close>:
\<close>

datatype agent = Server | Friend nat | Spy

text \<open>
Keys are just natural numbers.  Function \<open>invKey\<close> maps a public key to
the matching private key, and vice versa:
\<close>

type_synonym key = nat
consts invKey :: "key \<Rightarrow> key"
(*<*)
consts all_symmetric :: bool        \<comment> \<open>true if all keys are symmetric\<close>

specification (invKey)
  invKey [simp]: "invKey (invKey K) = K"
  invKey_symmetric: "all_symmetric \<longrightarrow> invKey = id"
    by (rule exI [of _ id], auto)


text\<open>The inverse of a symmetric key is itself; that of a public key
      is the private key and vice versa\<close>

definition symKeys :: "key set" where
  "symKeys == {K. invKey K = K}"
(*>*)

text \<open>
Datatype
\<open>msg\<close> introduces the message forms, which include agent names, nonces,
keys, compound messages, and encryptions.  
\<close>

datatype
     msg = Agent  agent
         | Nonce  nat
         | Key    key
         | MPair  msg msg
         | Crypt  key msg

text \<open>
\noindent
The notation $\comp{X\sb 1,\ldots X\sb{n-1},X\sb n}$
abbreviates
$\isa{MPair}\,X\sb 1\,\ldots\allowbreak(\isa{MPair}\,X\sb{n-1}\,X\sb n)$.

Since datatype constructors are injective, we have the theorem
@{thm [display,indent=0] msg.inject(5) [THEN iffD1, of K X K' X']}
A ciphertext can be decrypted using only one key and
can yield only one plaintext.  In the real world, decryption with the
wrong key succeeds but yields garbage.  Our model of encryption is
realistic if encryption adds some redundancy to the plaintext, such as a
checksum, so that garbage can be detected.
\<close>

(*<*)
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


definition keysFor :: "msg set \<Rightarrow> key set" where
    \<comment> \<open>Keys useful to decrypt elements of a message set\<close>
  "keysFor H == invKey ` {K. \<exists>X. Crypt K X \<in> H}"


subsubsection\<open>Inductive Definition of All Parts" of a Message\<close>

inductive_set
  parts :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj [intro]:               "X \<in> H \<Longrightarrow> X \<in> parts H"
  | Fst:         "\<lbrace>X,Y\<rbrace>   \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Snd:         "\<lbrace>X,Y\<rbrace>   \<in> parts H \<Longrightarrow> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H \<Longrightarrow> X \<in> parts H"


text\<open>Monotonicity\<close>
lemma parts_mono: "G \<subseteq> H \<Longrightarrow> parts(G) \<subseteq> parts(H)"
apply auto
apply (erule parts.induct) 
apply (blast dest: parts.Fst parts.Snd parts.Body)+
done


text\<open>Equations hold because constructors are injective.\<close>
lemma Friend_image_eq [simp]: "(Friend x \<in> Friend`A) = (x\<in>A)"
by auto

lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x\<in>A)"
by auto

lemma Nonce_Key_image_eq [simp]: "(Nonce x \<notin> Key`A)"
by auto


subsubsection\<open>Inverse of keys\<close>

lemma invKey_eq [simp]: "(invKey K = invKey K') = (K=K')"
apply safe
apply (drule_tac f = invKey in arg_cong, simp)
done


subsection\<open>keysFor operator\<close>

lemma keysFor_empty [simp]: "keysFor {} = {}"
by (unfold keysFor_def, blast)

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
by (unfold keysFor_def, blast)

lemma keysFor_UN [simp]: "keysFor (\<Union>i\<in>A. H i) = (\<Union>i\<in>A. keysFor (H i))"
by (unfold keysFor_def, blast)

text\<open>Monotonicity\<close>
lemma keysFor_mono: "G \<subseteq> H \<Longrightarrow> keysFor(G) \<subseteq> keysFor(H)"
by (unfold keysFor_def, blast)

lemma keysFor_insert_Agent [simp]: "keysFor (insert (Agent A) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_MPair [simp]: "keysFor (insert \<lbrace>X,Y\<rbrace> H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Crypt [simp]: 
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)"
by (unfold keysFor_def, auto)

lemma keysFor_image_Key [simp]: "keysFor (Key`E) = {}"
by (unfold keysFor_def, auto)

lemma Crypt_imp_invKey_keysFor: "Crypt K X \<in> H \<Longrightarrow> invKey K \<in> keysFor H"
by (unfold keysFor_def, blast)


subsection\<open>Inductive relation "parts"\<close>

lemma MPair_parts:
     "[| \<lbrace>X,Y\<rbrace> \<in> parts H;        
         [| X \<in> parts H; Y \<in> parts H |] ==> P |] ==> P"
by (blast dest: parts.Fst parts.Snd) 

declare MPair_parts [elim!]  parts.Body [dest!]
text\<open>NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE.  
  \<open>MPair_parts\<close> is left as SAFE because it speeds up proofs.
  The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.\<close>

lemma parts_increasing: "H \<subseteq> parts(H)"
by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty [simp]: "parts{} = {}"
apply safe
apply (erule parts.induct, blast+)
done

lemma parts_emptyE [elim!]: "X\<in> parts{} \<Longrightarrow> P"
by simp

text\<open>WARNING: loops if H = {Y}, therefore must not be repeated!\<close>
lemma parts_singleton: "X\<in> parts H \<Longrightarrow> \<exists>Y\<in>H. X\<in> parts {Y}"
by (erule parts.induct, fast+)


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

text\<open>TWO inserts to avoid looping.  This rewrite is better than nothing.
  Not suitable for Addsimps: its behaviour can be strange.\<close>
lemma parts_insert2:
     "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
apply (simp add: Un_assoc)
apply (simp add: parts_insert [symmetric])
done

lemma parts_UN_subset1: "(\<Union>x\<in>A. parts(H x)) \<subseteq> parts(\<Union>x\<in>A. H x)"
by (intro UN_least parts_mono UN_upper)

lemma parts_UN_subset2: "parts(\<Union>x\<in>A. H x) \<subseteq> (\<Union>x\<in>A. parts(H x))"
apply (rule subsetI)
apply (erule parts.induct, blast+)
done

lemma parts_UN [simp]: "parts(\<Union>x\<in>A. H x) = (\<Union>x\<in>A. parts(H x))"
by (intro equalityI parts_UN_subset1 parts_UN_subset2)

text\<open>Added to simplify arguments to parts, analz and synth.
  NOTE: the UN versions are no longer used!\<close>


text\<open>This allows \<open>blast\<close> to simplify occurrences of 
  \<^term>\<open>parts(G\<union>H)\<close> in the assumption.\<close>
lemmas in_parts_UnE = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE] 
declare in_parts_UnE [elim!]


lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])

subsubsection\<open>Idempotence and transitivity\<close>

lemma parts_partsD [dest!]: "X \<in> parts (parts H) \<Longrightarrow> X\<in> parts H"
by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) = (G \<subseteq> parts H)"
apply (rule iffI)
apply (iprover intro: subset_trans parts_increasing)  
apply (frule parts_mono, simp) 
done

lemma parts_trans: "[| X\<in> parts G;  G \<subseteq> parts H |] ==> X\<in> parts H"
by (drule parts_mono, blast)

text\<open>Cut\<close>
lemma parts_cut:
     "[| Y\<in> parts (insert X G);  X\<in> parts H |] ==> Y\<in> parts (G \<union> H)" 
by (blast intro: parts_trans) 


lemma parts_cut_eq [simp]: "X\<in> parts H ==> parts (insert X H) = parts H"
by (force dest!: parts_cut intro: parts_insertI)


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

lemma parts_insert_Key [simp]:
     "parts (insert (Key K) H) = insert (Key K) (parts H)"
apply (rule parts_insert_eq_I) 
apply (erule parts.induct, auto) 
done

lemma parts_insert_Crypt [simp]:
     "parts (insert (Crypt K X) H) = insert (Crypt K X) (parts (insert X H))"
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


text\<open>In any message, there is an upper bound N on its greatest nonce.\<close>
lemma msg_Nonce_supply: "\<exists>N. \<forall>n. N\<le>n \<longrightarrow> Nonce n \<notin> parts {msg}"
apply (induct_tac "msg")
apply (simp_all (no_asm_simp) add: exI parts_insert2)
 txt\<open>MPair case: blast works out the necessary sum itself!\<close>
 prefer 2 apply auto apply (blast elim!: add_leE)
txt\<open>Nonce case\<close>
apply (rename_tac nat)
apply (rule_tac x = "N + Suc nat" in exI, auto) 
done
(*>*)

section\<open>Modelling the Adversary\<close>

text \<open>
The spy is part of the system and must be built into the model.  He is
a malicious user who does not have to follow the protocol.  He
watches the network and uses any keys he knows to decrypt messages.
Thus he accumulates additional keys and nonces.  These he can use to
compose new messages, which he may send to anybody.  

Two functions enable us to formalize this behaviour: \<open>analz\<close> and
\<open>synth\<close>.  Each function maps a sets of messages to another set of
messages. The set \<open>analz H\<close> formalizes what the adversary can learn
from the set of messages~$H$.  The closure properties of this set are
defined inductively.
\<close>

inductive_set
  analz :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj [intro,simp] : "X \<in> H \<Longrightarrow> X \<in> analz H"
  | Fst:     "\<lbrace>X,Y\<rbrace> \<in> analz H \<Longrightarrow> X \<in> analz H"
  | Snd:     "\<lbrace>X,Y\<rbrace> \<in> analz H \<Longrightarrow> Y \<in> analz H"
  | Decrypt [dest]: 
             "\<lbrakk>Crypt K X \<in> analz H; Key(invKey K) \<in> analz H\<rbrakk>
              \<Longrightarrow> X \<in> analz H"
(*<*)
text\<open>Monotonicity; Lemma 1 of Lowe's paper\<close>
lemma analz_mono: "G\<subseteq>H \<Longrightarrow> analz(G) \<subseteq> analz(H)"
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
apply (rule analz_subset_parts [THEN parts_mono, THEN subset_trans], simp)
apply (blast intro: analz_increasing [THEN parts_mono, THEN subsetD])
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

text\<open>Can only pull out Keys if they are not needed to decrypt the rest\<close>
lemma analz_insert_Key [simp]: 
    "K \<notin> keysFor (analz H) \<Longrightarrow>   
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
      \<Longrightarrow> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule analz_insert_eq_I) 
apply (erule analz.induct, auto) 

done

lemma lemma1: "Key (invKey K) \<in> analz H \<Longrightarrow>   
               analz (insert (Crypt K X) H) \<subseteq>  
               insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule_tac x = x in analz.induct, auto)
done

lemma lemma2: "Key (invKey K) \<in> analz H \<Longrightarrow>   
               insert (Crypt K X) (analz (insert X H)) \<subseteq>  
               analz (insert (Crypt K X) H)"
apply auto
apply (erule_tac x = x in analz.induct, auto)
apply (blast intro: analz_insertI analz.Decrypt)
done

lemma analz_insert_Decrypt:
     "Key (invKey K) \<in> analz H \<Longrightarrow>   
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

lemma analz_analzD [dest!]: "X\<in> analz (analz H) \<Longrightarrow> X\<in> analz H"
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

text\<open>Cut; Lemma 2 of Lowe\<close>
lemma analz_cut: "[| Y\<in> analz (insert X H);  X\<in> analz H |] ==> Y\<in> analz H"
by (erule analz_trans, blast)

(*Cut can be proved easily by induction on
   "Y \<in> analz (insert X H) \<Longrightarrow> X \<in> analz H \<longrightarrow> Y \<in> analz H"
*)

text\<open>This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated.\<close>
lemma analz_insert_eq: "X\<in> analz H \<Longrightarrow> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)


text\<open>A congruence rule for "analz"\<close>

lemma analz_subset_cong:
     "[| analz G \<subseteq> analz G'; analz H \<subseteq> analz H' |] 
      ==> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply simp
apply (iprover intro: conjI subset_trans analz_mono Un_upper1 Un_upper2) 
done

lemma analz_cong:
     "[| analz G = analz G'; analz H = analz H' |] 
      ==> analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all) 

lemma analz_insert_cong:
     "analz H = analz H' \<Longrightarrow> analz(insert X H) = analz(insert X H')"
by (force simp only: insert_def intro!: analz_cong)

text\<open>If there are no pairs or encryptions then analz does nothing\<close>
lemma analz_trivial:
     "[| \<forall>X Y. \<lbrace>X,Y\<rbrace> \<notin> H;  \<forall>X K. Crypt K X \<notin> H |] ==> analz H = H"
apply safe
apply (erule analz.induct, blast+)
done

text\<open>These two are obsolete (with a single Spy) but cost little to prove...\<close>
lemma analz_UN_analz_lemma:
     "X\<in> analz (\<Union>i\<in>A. analz (H i)) \<Longrightarrow> X\<in> analz (\<Union>i\<in>A. H i)"
apply (erule analz.induct)
apply (blast intro: analz_mono [THEN [2] rev_subsetD])+
done

lemma analz_UN_analz [simp]: "analz (\<Union>i\<in>A. analz (H i)) = analz (\<Union>i\<in>A. H i)"
by (blast intro: analz_UN_analz_lemma analz_mono [THEN [2] rev_subsetD])
(*>*)
text \<open>
Note the \<open>Decrypt\<close> rule: the spy can decrypt a
message encrypted with key~$K$ if he has the matching key,~$K^{-1}$. 
Properties proved by rule induction include the following:
@{named_thms [display,indent=0] analz_mono [no_vars] (analz_mono) analz_idem [no_vars] (analz_idem)}

The set of fake messages that an intruder could invent
starting from~\<open>H\<close> is \<open>synth(analz H)\<close>, where \<open>synth H\<close>
formalizes what the adversary can build from the set of messages~$H$.  
\<close>

inductive_set
  synth :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Inj    [intro]: "X \<in> H \<Longrightarrow> X \<in> synth H"
  | Agent  [intro]: "Agent agt \<in> synth H"
  | MPair  [intro]:
              "\<lbrakk>X \<in> synth H;  Y \<in> synth H\<rbrakk> \<Longrightarrow> \<lbrace>X,Y\<rbrace> \<in> synth H"
  | Crypt  [intro]:
              "\<lbrakk>X \<in> synth H;  Key K \<in> H\<rbrakk> \<Longrightarrow> Crypt K X \<in> synth H"
(*<*)
lemma synth_mono: "G\<subseteq>H \<Longrightarrow> synth(G) \<subseteq> synth(H)"
  by (auto, erule synth.induct, auto)  

inductive_cases Key_synth   [elim!]: "Key K \<in> synth H"
inductive_cases MPair_synth [elim!]: "\<lbrace>X,Y\<rbrace> \<in> synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X \<in> synth H"

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct)
prefer 5 apply (blast intro: analz_mono [THEN [2] rev_subsetD])
apply (blast intro: analz.Fst analz.Snd analz.Decrypt)+
done

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
apply (cut_tac H = "{}" in analz_synth_Un)
apply (simp (no_asm_use))
done
(*>*)
text \<open>
The set includes all agent names.  Nonces and keys are assumed to be
unguessable, so none are included beyond those already in~$H$.   Two
elements of \<^term>\<open>synth H\<close> can be combined, and an element can be encrypted
using a key present in~$H$.

Like \<open>analz\<close>, this set operator is monotone and idempotent.  It also
satisfies an interesting equation involving \<open>analz\<close>:
@{named_thms [display,indent=0] analz_synth [no_vars] (analz_synth)}
Rule inversion plays a major role in reasoning about \<open>synth\<close>, through
declarations such as this one:
\<close>

inductive_cases Nonce_synth [elim!]: "Nonce n \<in> synth H"

text \<open>
\noindent
The resulting elimination rule replaces every assumption of the form
\<^term>\<open>Nonce n \<in> synth H\<close> by \<^term>\<open>Nonce n \<in> H\<close>,
expressing that a nonce cannot be guessed.  

A third operator, \<open>parts\<close>, is useful for stating correctness
properties.  The set
\<^term>\<open>parts H\<close> consists of the components of elements of~$H$.  This set
includes~\<open>H\<close> and is closed under the projections from a compound
message to its immediate parts. 
Its definition resembles that of \<open>analz\<close> except in the rule
corresponding to the constructor \<open>Crypt\<close>: 
@{thm [display,indent=5] parts.Body [no_vars]}
The body of an encrypted message is always regarded as part of it.  We can
use \<open>parts\<close> to express general well-formedness properties of a protocol,
for example, that an uncompromised agent's private key will never be
included as a component of any message.
\<close>
(*<*)
lemma synth_increasing: "H \<subseteq> synth(H)"
by blast

subsubsection\<open>Unions\<close>

text\<open>Converse fails: we can synth more from the union than from the 
  separate parts, building a compound message using elements of each.\<close>
lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
by (blast intro: synth_mono [THEN [2] rev_subsetD])

subsubsection\<open>Idempotence and transitivity\<close>

lemma synth_synthD [dest!]: "X\<in> synth (synth H) \<Longrightarrow> X\<in> synth H"
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

text\<open>Cut; Lemma 2 of Lowe\<close>
lemma synth_cut: "[| Y\<in> synth (insert X H);  X\<in> synth H |] ==> Y\<in> synth H"
by (erule synth_trans, blast)

lemma Agent_synth [simp]: "Agent A \<in> synth H"
by blast

lemma Nonce_synth_eq [simp]: "(Nonce N \<in> synth H) = (Nonce N \<in> H)"
by blast

lemma Key_synth_eq [simp]: "(Key K \<in> synth H) = (Key K \<in> H)"
by blast

lemma Crypt_synth_eq [simp]:
     "Key K \<notin> H \<Longrightarrow> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
by blast


lemma keysFor_synth [simp]: 
    "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
by (unfold keysFor_def, blast)


subsubsection\<open>Combinations of parts, analz and synth\<close>

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct)
apply (blast intro: synth_increasing [THEN parts_mono, THEN subsetD] 
                    parts.Fst parts.Snd parts.Body)+
done

lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (intro equalityI analz_subset_cong)+
apply simp_all
done


subsubsection\<open>For reasoning about the Fake rule in traces\<close>

lemma parts_insert_subset_Un: "X \<in> G \<Longrightarrow> parts(insert X H) \<subseteq> parts G \<union> parts H"
by (rule subset_trans [OF parts_mono parts_Un_subset2], blast)

text\<open>More specifically for Fake.  Very occasionally we could do with a version
  of the form  \<^term>\<open>parts{X} \<subseteq> synth (analz H) \<union> parts H\<close>\<close>
lemma Fake_parts_insert:
     "X \<in> synth (analz H) \<Longrightarrow>
      parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
apply (drule parts_insert_subset_Un)
apply (simp (no_asm_use))
apply blast
done

lemma Fake_parts_insert_in_Un:
     "[|Z \<in> parts (insert X H);  X \<in> synth (analz H)|] 
      ==> Z \<in>  synth (analz H) \<union> parts H"
by (blast dest: Fake_parts_insert  [THEN subsetD, dest])

text\<open>\<^term>\<open>H\<close> is sometimes \<^term>\<open>Key ` KK \<union> spies evs\<close>, so can't put 
  \<^term>\<open>G=H\<close>.\<close>
lemma Fake_analz_insert:
     "X \<in> synth (analz G) \<Longrightarrow>  
      analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
apply (rule subsetI)
apply (subgoal_tac "x \<in> analz (synth (analz G) \<union> H) ")
prefer 2 apply (blast intro: analz_mono [THEN [2] rev_subsetD] analz_mono [THEN synth_mono, THEN [2] rev_subsetD])
apply (simp (no_asm_use))
apply blast
done

lemma analz_conj_parts [simp]:
     "(X \<in> analz H & X \<in> parts H) = (X \<in> analz H)"
by (blast intro: analz_subset_parts [THEN subsetD])

lemma analz_disj_parts [simp]:
     "(X \<in> analz H | X \<in> parts H) = (X \<in> parts H)"
by (blast intro: analz_subset_parts [THEN subsetD])

text\<open>Without this equation, other rules for synth and analz would yield
  redundant cases\<close>
lemma MPair_synth_analz [iff]:
     "(\<lbrace>X,Y\<rbrace> \<in> synth (analz H)) =  
      (X \<in> synth (analz H) & Y \<in> synth (analz H))"
by blast

lemma Crypt_synth_analz:
     "[| Key K \<in> analz H;  Key (invKey K) \<in> analz H |]  
       ==> (Crypt K X \<in> synth (analz H)) = (X \<in> synth (analz H))"
by blast


text\<open>We do NOT want Crypt... messages broken up in protocols!!\<close>
declare parts.Body [rule del]


text\<open>Rewrites to push in Key and Crypt messages, so that other messages can
    be pulled out using the \<open>analz_insert\<close> rules\<close>

lemmas pushKeys =
  insert_commute [of "Key K" "Agent C"]
  insert_commute [of "Key K" "Nonce N"]
  insert_commute [of "Key K" "MPair X Y"]
  insert_commute [of "Key K" "Crypt X K'"]
  for K C N X Y K'

lemmas pushCrypts =
  insert_commute [of "Crypt X K" "Agent C"]
  insert_commute [of "Crypt X K" "Agent C"]
  insert_commute [of "Crypt X K" "Nonce N"]
  insert_commute [of "Crypt X K" "MPair X' Y"]
  for X K C N X' Y

text\<open>Cannot be added with \<open>[simp]\<close> -- messages should not always be
  re-ordered.\<close>
lemmas pushes = pushKeys pushCrypts


subsection\<open>Tactics useful for many protocol proofs\<close>
ML
\<open>
val invKey = @{thm invKey};
val keysFor_def = @{thm keysFor_def};
val symKeys_def = @{thm symKeys_def};
val parts_mono = @{thm parts_mono};
val analz_mono = @{thm analz_mono};
val synth_mono = @{thm synth_mono};
val analz_increasing = @{thm analz_increasing};

val analz_insertI = @{thm analz_insertI};
val analz_subset_parts = @{thm analz_subset_parts};
val Fake_parts_insert = @{thm Fake_parts_insert};
val Fake_analz_insert = @{thm Fake_analz_insert};
val pushes = @{thms pushes};


(*Analysis of Fake cases.  Also works for messages that forward unknown parts,
  but this application is no longer necessary if analz_insert_eq is used.
  Abstraction over i is ESSENTIAL: it delays the dereferencing of claset
  DEPENDS UPON "X" REFERRING TO THE FRADULENT MESSAGE *)

(*Apply rules to break down assumptions of the form
  Y \<in> parts(insert X H)  and  Y \<in> analz(insert X H)
*)
fun impOfSubs th = th RSN (2, @{thm rev_subsetD})

fun Fake_insert_tac ctxt =
    dresolve_tac ctxt [impOfSubs Fake_analz_insert,
                  impOfSubs Fake_parts_insert] THEN'
    eresolve_tac ctxt [asm_rl, @{thm synth.Inj}];

fun Fake_insert_simp_tac ctxt i = 
  REPEAT (Fake_insert_tac ctxt i) THEN asm_full_simp_tac ctxt i;

fun atomic_spy_analz_tac ctxt =
  SELECT_GOAL
   (Fake_insert_simp_tac ctxt 1 THEN
    IF_UNSOLVED (Blast.depth_tac (ctxt addIs [analz_insertI, impOfSubs analz_subset_parts]) 4 1));

fun spy_analz_tac ctxt i =
  DETERM
   (SELECT_GOAL
     (EVERY 
      [  (*push in occurrences of X...*)
       (REPEAT o CHANGED)
         (Rule_Insts.res_inst_tac ctxt [((("x", 1), Position.none), "X")] []
           (insert_commute RS ssubst) 1),
       (*...allowing further simplifications*)
       simp_tac ctxt 1,
       REPEAT (FIRSTGOAL (resolve_tac ctxt [allI,impI,notI,conjI,iffI])),
       DEPTH_SOLVE (atomic_spy_analz_tac ctxt 1)]) i);
\<close>

text\<open>By default only \<open>o_apply\<close> is built-in.  But in the presence of
eta-expansion this means that some terms displayed as \<^term>\<open>f o g\<close> will be
rewritten, and others will not!\<close>
declare o_def [simp]


lemma Crypt_notin_image_Key [simp]: "Crypt K X \<notin> Key ` A"
by auto

lemma synth_analz_mono: "G\<subseteq>H \<Longrightarrow> synth (analz(G)) \<subseteq> synth (analz(H))"
by (iprover intro: synth_mono analz_mono) 

lemma Fake_analz_eq [simp]:
     "X \<in> synth(analz H) \<Longrightarrow> synth (analz (insert X H)) = synth (analz H)"
apply (drule Fake_analz_insert[of _ _ "H"])
apply (simp add: synth_increasing[THEN Un_absorb2])
apply (drule synth_mono)
apply (simp add: synth_idem)
apply (rule equalityI)
apply (simp add: )
apply (rule synth_analz_mono, blast)   
done

text\<open>Two generalizations of \<open>analz_insert_eq\<close>\<close>
lemma gen_analz_insert_eq [rule_format]:
     "X \<in> analz H \<Longrightarrow> \<forall>G. H \<subseteq> G \<longrightarrow> analz (insert X G) = analz G"
by (blast intro: analz_cut analz_insertI analz_mono [THEN [2] rev_subsetD])

lemma synth_analz_insert_eq [rule_format]:
     "X \<in> synth (analz H) 
      \<Longrightarrow> \<forall>G. H \<subseteq> G \<longrightarrow> (Key K \<in> analz (insert X G)) = (Key K \<in> analz G)"
apply (erule synth.induct) 
apply (simp_all add: gen_analz_insert_eq subset_trans [OF _ subset_insertI]) 
done

lemma Fake_parts_sing:
     "X \<in> synth (analz H) \<Longrightarrow> parts{X} \<subseteq> synth (analz H) \<union> parts H"
apply (rule subset_trans) 
 apply (erule_tac [2] Fake_parts_insert)
apply (rule parts_mono, blast)
done

lemmas Fake_parts_sing_imp_Un = Fake_parts_sing [THEN [2] rev_subsetD]

method_setup spy_analz = \<open>
    Scan.succeed (SIMPLE_METHOD' o spy_analz_tac)\<close>
    "for proving the Fake case when analz is involved"

method_setup atomic_spy_analz = \<open>
    Scan.succeed (SIMPLE_METHOD' o atomic_spy_analz_tac)\<close>
    "for debugging spy_analz"

method_setup Fake_insert_simp = \<open>
    Scan.succeed (SIMPLE_METHOD' o Fake_insert_simp_tac)\<close>
    "for debugging spy_analz"


end
(*>*)
