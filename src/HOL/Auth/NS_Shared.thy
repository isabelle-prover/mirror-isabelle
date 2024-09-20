(*  Title:      HOL/Auth/NS_Shared.thy
    Author:     Lawrence C Paulson and Giampaolo Bella
    Copyright   1996  University of Cambridge
*)

section\<open>Needham-Schroeder Shared-Key Protocol\<close>

theory NS_Shared imports Public begin

text\<open>
From page 247 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426
\<close>

definition
 (* A is the true creator of X if she has sent X and X never appeared on
    the trace before this event. Recall that traces grow from head. *)
  Issues :: "[agent, agent, msg, event list] \<Rightarrow> bool"
             (\<open>_ Issues _ with _ on _\<close>) where
   "A Issues B with X on evs =
      (\<exists>Y. Says A B Y \<in> set evs \<and> X \<in> parts {Y} \<and>
        X \<notin> parts (spies (takeWhile (\<lambda>z. z  \<noteq> Says A B Y) (rev evs))))"


inductive_set ns_shared :: "event list set"
 where
        (*Initial trace is empty*)
  Nil:  "[] \<in> ns_shared"
        (*The spy MAY say anything he CAN say.  We do not expect him to
          invent new nonces here, but he can also use NS1.  Common to
          all similar protocols.*)
| Fake: "\<lbrakk>evsf \<in> ns_shared;  X \<in> synth (analz (spies evsf))\<rbrakk>
         \<Longrightarrow> Says Spy B X # evsf \<in> ns_shared"

        (*Alice initiates a protocol run, requesting to talk to any B*)
| NS1:  "\<lbrakk>evs1 \<in> ns_shared;  Nonce NA \<notin> used evs1\<rbrakk>
         \<Longrightarrow> Says A Server \<lbrace>Agent A, Agent B, Nonce NA\<rbrace> # evs1  \<in>  ns_shared"

        (*Server's response to Alice's message.
          !! It may respond more than once to A's request !!
          Server doesn't know who the true sender is, hence the A' in
              the sender field.*)
| NS2:  "\<lbrakk>evs2 \<in> ns_shared;  Key KAB \<notin> used evs2;  KAB \<in> symKeys;
          Says A' Server \<lbrace>Agent A, Agent B, Nonce NA\<rbrace> \<in> set evs2\<rbrakk>
         \<Longrightarrow> Says Server A
               (Crypt (shrK A)
                  \<lbrace>Nonce NA, Agent B, Key KAB,
                    (Crypt (shrK B) \<lbrace>Key KAB, Agent A\<rbrace>)\<rbrace>)
               # evs2 \<in> ns_shared"

         (*We can't assume S=Server.  Agent A "remembers" her nonce.
           Need A \<noteq> Server because we allow messages to self.*)
| NS3:  "\<lbrakk>evs3 \<in> ns_shared;  A \<noteq> Server;
          Says S A (Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace>) \<in> set evs3;
          Says A Server \<lbrace>Agent A, Agent B, Nonce NA\<rbrace> \<in> set evs3\<rbrakk>
         \<Longrightarrow> Says A B X # evs3 \<in> ns_shared"

        (*Bob's nonce exchange.  He does not know who the message came
          from, but responds to A because she is mentioned inside.*)
| NS4:  "\<lbrakk>evs4 \<in> ns_shared;  Nonce NB \<notin> used evs4;  K \<in> symKeys;
          Says A' B (Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>) \<in> set evs4\<rbrakk>
         \<Longrightarrow> Says B A (Crypt K (Nonce NB)) # evs4 \<in> ns_shared"

        (*Alice responds with Nonce NB if she has seen the key before.
          Maybe should somehow check Nonce NA again.
          We do NOT send NB-1 or similar as the Spy cannot spoof such things.
          Letting the Spy add or subtract 1 lets him send all nonces.
          Instead we distinguish the messages by sending the nonce twice.*)
| NS5:  "\<lbrakk>evs5 \<in> ns_shared;  K \<in> symKeys;
          Says B' A (Crypt K (Nonce NB)) \<in> set evs5;
          Says S  A (Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace>)
            \<in> set evs5\<rbrakk>
         \<Longrightarrow> Says A B (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) # evs5 \<in> ns_shared"

        (*This message models possible leaks of session keys.
          The two Nonces identify the protocol run: the rule insists upon
          the true senders in order to make them accurate.*)
| Oops: "\<lbrakk>evso \<in> ns_shared;  Says B A (Crypt K (Nonce NB)) \<in> set evso;
          Says Server A (Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace>)
              \<in> set evso\<rbrakk>
         \<Longrightarrow> Notes Spy \<lbrace>Nonce NA, Nonce NB, Key K\<rbrace> # evso \<in> ns_shared"


declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]


text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "\<lbrakk>A \<noteq> Server; Key K \<notin> used []; K \<in> symKeys\<rbrakk>
       \<Longrightarrow> \<exists>N. \<exists>evs \<in> ns_shared.
                    Says A B (Crypt K \<lbrace>Nonce N, Nonce N\<rbrace>) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] ns_shared.Nil
       [THEN ns_shared.NS1, THEN ns_shared.NS2, THEN ns_shared.NS3,
        THEN ns_shared.NS4, THEN ns_shared.NS5])
apply (possibility, simp add: used_Cons)
done

(*This version is similar, while instantiating ?K and ?N to epsilon-terms
lemma "A \<noteq> Server \<Longrightarrow> \<exists>evs \<in> ns_shared.
                Says A B (Crypt ?K \<lbrace>Nonce ?N, Nonce ?N\<rbrace>) \<in> set evs"
*)


subsection\<open>Inductive proofs about \<^term>\<open>ns_shared\<close>\<close>

subsubsection\<open>Forwarding lemmas, to aid simplification\<close>

text\<open>For reasoning about the encrypted portion of message NS3\<close>
lemma NS3_msg_in_parts_spies:
     "Says S A (Crypt KA \<lbrace>N, B, K, X\<rbrace>) \<in> set evs \<Longrightarrow> X \<in> parts (spies evs)"
by blast

text\<open>For reasoning about the Oops message\<close>
lemma Oops_parts_spies:
     "Says Server A (Crypt (shrK A) \<lbrace>NA, B, K, X\<rbrace>) \<in> set evs
            \<Longrightarrow> K \<in> parts (spies evs)"
by blast

text\<open>Theorems of the form \<^term>\<open>X \<notin> parts (spies evs)\<close> imply that NOBODY
    sends messages containing \<^term>\<open>X\<close>\<close>

text\<open>Spy never sees another agent's shared key! (unless it's bad at start)\<close>
lemma Spy_see_shrK [simp]:
     "evs \<in> ns_shared \<Longrightarrow> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies, simp_all, blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> ns_shared \<Longrightarrow> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto


text\<open>Nobody can have used non-existent keys!\<close>
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> ns_shared\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies, simp_all)
txt\<open>Fake, NS2, NS4, NS5\<close>
apply (force dest!: keysFor_parts_insert, blast+)
done


subsubsection\<open>Lemmas concerning the form of items passed in messages\<close>

text\<open>Describes the form of K, X and K' when the Server sends this message.\<close>
lemma Says_Server_message_form:
     "\<lbrakk>Says Server A (Crypt K' \<lbrace>N, Agent B, Key K, X\<rbrace>) \<in> set evs;
       evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> K \<notin> range shrK \<and>
          X = (Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>) \<and>
          K' = shrK A"
by (erule rev_mp, erule ns_shared.induct, auto)


text\<open>If the encrypted message appears then it originated with the Server\<close>
lemma A_trusts_NS2:
     "\<lbrakk>Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
       A \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> Says Server A (Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace>) \<in> set evs"
apply (erule rev_mp)
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies, auto)
done

lemma cert_A_form:
     "\<lbrakk>Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
       A \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> K \<notin> range shrK \<and>  X = (Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>)"
by (blast dest!: A_trusts_NS2 Says_Server_message_form)

text\<open>EITHER describes the form of X when the following message is sent,
  OR     reduces it to the Fake case.
  Use \<open>Says_Server_message_form\<close> if applicable.\<close>
lemma Says_S_message_form:
     "\<lbrakk>Says S A (Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace>) \<in> set evs;
       evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> (K \<notin> range shrK \<and> X = (Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>))
          \<or> X \<in> analz (spies evs)"
by (blast dest: Says_imp_knows_Spy analz_shrK_Decrypt cert_A_form analz.Inj)


(*Alternative version also provable
lemma Says_S_message_form2:
  "\<lbrakk>Says S A (Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace>) \<in> set evs;
    evs \<in> ns_shared\<rbrakk>
   \<Longrightarrow> Says Server A (Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace>) \<in> set evs
       \<or> X \<in> analz (spies evs)"
apply (case_tac "A \<in> bad")
apply (force dest!: Says_imp_knows_Spy [THEN analz.Inj])
by (blast dest!: A_trusts_NS2 Says_Server_message_form)
*)


(****
 SESSION KEY COMPROMISE THEOREM.  To prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (spies evs)) \<Longrightarrow>
  Key K \<in> analz (spies evs)

 A more general formula must be proved inductively.
****)

text\<open>NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.\<close>
lemma  "\<lbrakk>evs \<in> ns_shared;  Kab \<notin> range shrK\<rbrakk> \<Longrightarrow>
         (Crypt KAB X) \<in> parts (spies evs) \<and>
         Key K \<in> parts {X} \<longrightarrow> Key K \<in> parts (spies evs)"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies, simp_all)
txt\<open>Fake\<close>
apply (blast dest: parts_insert_subset_Un)
txt\<open>Base, NS4 and NS5\<close>
apply auto
done


subsubsection\<open>Session keys are not used to encrypt other session keys\<close>

text\<open>The equality makes the induction hypothesis easier to apply\<close>

lemma analz_image_freshK [rule_format]:
 "evs \<in> ns_shared \<Longrightarrow>
   \<forall>K KK. KK \<subseteq> - (range shrK) \<longrightarrow>
             (Key K \<in> analz (Key`KK \<union> (spies evs))) =
             (K \<in> KK \<or> Key K \<in> analz (spies evs))"
apply (erule ns_shared.induct)
apply (drule_tac [8] Says_Server_message_form)
apply (erule_tac [5] Says_S_message_form [THEN disjE], analz_freshK, spy_analz)
txt\<open>NS2, NS3\<close>
apply blast+
done


lemma analz_insert_freshK:
     "\<lbrakk>evs \<in> ns_shared;  KAB \<notin> range shrK\<rbrakk> \<Longrightarrow>
       (Key K \<in> analz (insert (Key KAB) (spies evs))) =
       (K = KAB \<or> Key K \<in> analz (spies evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


subsubsection\<open>The session key K uniquely identifies the message\<close>

text\<open>In messages of this form, the session key uniquely identifies the rest\<close>
lemma unique_session_keys:
     "\<lbrakk>Says Server A (Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace>) \<in> set evs;
       Says Server A' (Crypt (shrK A') \<lbrace>NA', Agent B', Key K, X'\<rbrace>) \<in> set evs;
       evs \<in> ns_shared\<rbrakk> \<Longrightarrow> A=A' \<and> NA=NA' \<and> B=B' \<and> X = X'"
by (erule rev_mp, erule rev_mp, erule ns_shared.induct, simp_all, blast+)


subsubsection\<open>Crucial secrecy property: Spy doesn't see the keys sent in NS2\<close>

text\<open>Beware of \<open>[rule_format]\<close> and the universal quantifier!\<close>
lemma secrecy_lemma:
     "\<lbrakk>Says Server A (Crypt (shrK A) \<lbrace>NA, Agent B, Key K,
                                      Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>\<rbrace>)
              \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> (\<forall>NB. Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs) \<longrightarrow>
         Key K \<notin> analz (spies evs)"
apply (erule rev_mp)
apply (erule ns_shared.induct, force)
apply (frule_tac [7] Says_Server_message_form)
apply (frule_tac [4] Says_S_message_form)
apply (erule_tac [5] disjE)
apply (simp_all add: analz_insert_eq analz_insert_freshK pushes split_ifs, spy_analz)
txt\<open>NS2\<close>
apply blast
txt\<open>NS3\<close>
apply (blast dest!: Crypt_Spy_analz_bad A_trusts_NS2
             dest:  Says_imp_knows_Spy analz.Inj unique_session_keys)
txt\<open>Oops\<close>
apply (blast dest: unique_session_keys)
done



text\<open>Final version: Server's message in the most abstract form\<close>
lemma Spy_not_see_encrypted_key:
     "\<lbrakk>Says Server A (Crypt K' \<lbrace>NA, Agent B, Key K, X\<rbrace>) \<in> set evs;
       \<forall>NB. Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (spies evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)


subsection\<open>Guarantees available at various stages of protocol\<close>

text\<open>If the encrypted message appears then it originated with the Server\<close>
lemma B_trusts_NS3:
     "\<lbrakk>Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace> \<in> parts (spies evs);
       B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> \<exists>NA. Says Server A
               (Crypt (shrK A) \<lbrace>NA, Agent B, Key K,
                                 Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>\<rbrace>)
              \<in> set evs"
apply (erule rev_mp)
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies, auto)
done


lemma A_trusts_NS4_lemma [rule_format]:
   "evs \<in> ns_shared \<Longrightarrow>
      Key K \<notin> analz (spies evs) \<longrightarrow>
      Says Server A (Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace>) \<in> set evs \<longrightarrow>
      Crypt K (Nonce NB) \<in> parts (spies evs) \<longrightarrow>
      Says B A (Crypt K (Nonce NB)) \<in> set evs"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply (analz_mono_contra, simp_all, blast)
txt\<open>NS2: contradiction from the assumptions \<^term>\<open>Key K \<notin> used evs2\<close> and
    \<^term>\<open>Crypt K (Nonce NB) \<in> parts (spies evs2)\<close>\<close> 
apply (force dest!: Crypt_imp_keysFor)
txt\<open>NS4\<close>
apply (metis B_trusts_NS3 Crypt_Spy_analz_bad Says_imp_analz_Spy Says_imp_parts_knows_Spy analz.Fst unique_session_keys)
done

text\<open>This version no longer assumes that K is secure\<close>
lemma A_trusts_NS4:
     "\<lbrakk>Crypt K (Nonce NB) \<in> parts (spies evs);
       Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
       \<forall>NB. Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Nonce NB)) \<in> set evs"
by (blast intro: A_trusts_NS4_lemma
          dest: A_trusts_NS2 Spy_not_see_encrypted_key)

text\<open>If the session key has been used in NS4 then somebody has forwarded
  component X in some instance of NS4.  Perhaps an interesting property,
  but not needed (after all) for the proofs below.\<close>
theorem NS4_implies_NS3 [rule_format]:
  "evs \<in> ns_shared \<Longrightarrow>
     Key K \<notin> analz (spies evs) \<longrightarrow>
     Says Server A (Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace>) \<in> set evs \<longrightarrow>
     Crypt K (Nonce NB) \<in> parts (spies evs) \<longrightarrow>
     (\<exists>A'. Says A' B X \<in> set evs)"
apply (erule ns_shared.induct, force)
apply (drule_tac [4] NS3_msg_in_parts_spies)
apply analz_mono_contra
apply (simp_all add: ex_disj_distrib, blast)
txt\<open>NS2\<close>
apply (blast dest!: new_keys_not_used Crypt_imp_keysFor)
txt\<open>NS4\<close>
apply (metis B_trusts_NS3 Crypt_Spy_analz_bad Says_imp_analz_Spy Says_imp_parts_knows_Spy analz.Fst unique_session_keys)
done


lemma B_trusts_NS5_lemma [rule_format]:
  "\<lbrakk>B \<notin> bad;  evs \<in> ns_shared\<rbrakk> \<Longrightarrow>
     Key K \<notin> analz (spies evs) \<longrightarrow>
     Says Server A
          (Crypt (shrK A) \<lbrace>NA, Agent B, Key K,
                            Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace>\<rbrace>) \<in> set evs \<longrightarrow>
     Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace> \<in> parts (spies evs) \<longrightarrow>
     Says A B (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) \<in> set evs"
apply (erule ns_shared.induct, force)
apply (drule_tac [4] NS3_msg_in_parts_spies)
apply (analz_mono_contra, simp_all, blast)
txt\<open>NS2\<close>
apply (blast dest!: new_keys_not_used Crypt_imp_keysFor)
txt\<open>NS5\<close>
apply (blast dest!: A_trusts_NS2
             dest: Says_imp_knows_Spy [THEN analz.Inj]
                   unique_session_keys Crypt_Spy_analz_bad)
done


text\<open>Very strong Oops condition reveals protocol's weakness\<close>
lemma B_trusts_NS5:
     "\<lbrakk>Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace> \<in> parts (spies evs);
       Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace> \<in> parts (spies evs);
       \<forall>NA NB. Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> Says A B (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) \<in> set evs"
by (blast intro: B_trusts_NS5_lemma
          dest: B_trusts_NS3 Spy_not_see_encrypted_key)

text\<open>Unaltered so far wrt original version\<close>

subsection\<open>Lemmas for reasoning about predicate "Issues"\<close>

lemma spies_Says_rev: "spies (evs @ [Says A B X]) = insert X (spies evs)"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
done

lemma spies_Gets_rev: "spies (evs @ [Gets A X]) = spies evs"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
done

lemma spies_Notes_rev: "spies (evs @ [Notes A X]) =
          (if A\<in>bad then insert X (spies evs) else spies evs)"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
done

lemma spies_evs_rev: "spies evs = spies (rev evs)"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a")
apply (simp_all (no_asm_simp) add: spies_Says_rev spies_Gets_rev spies_Notes_rev)
done

lemmas parts_spies_evs_revD2 = spies_evs_rev [THEN equalityD2, THEN parts_mono]

lemma spies_takeWhile: "spies (takeWhile P evs) \<subseteq> spies evs"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
txt\<open>Resembles \<open>used_subset_append\<close> in theory Event.\<close>
done

lemmas parts_spies_takeWhile_mono = spies_takeWhile [THEN parts_mono]


subsection\<open>Guarantees of non-injective agreement on the session key, and
of key distribution. They also express forms of freshness of certain messages,
namely that agents were alive after something happened.\<close>

lemma B_Issues_A:
     "\<lbrakk> Says B A (Crypt K (Nonce Nb)) \<in> set evs;
         Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; evs \<in> ns_shared \<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt K (Nonce Nb)) on evs"
unfolding Issues_def
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule ns_shared.induct, analz_mono_contra)
apply (simp_all)
txt\<open>fake\<close>
apply blast
apply (simp_all add: takeWhile_tail)
txt\<open>NS3 remains by pure coincidence!\<close>
apply (force dest!: A_trusts_NS2 Says_Server_message_form)
txt\<open>NS4 would be the non-trivial case can be solved by Nb being used\<close>
apply (blast dest: parts_spies_takeWhile_mono [THEN subsetD]
                   parts_spies_evs_revD2 [THEN subsetD])
done

text\<open>Tells A that B was alive after she sent him the session key.  The
session key must be assumed confidential for this deduction to be meaningful,
but that assumption can be relaxed by the appropriate argument.

Precisely, the theorem guarantees (to A) key distribution of the session key
to B. It also guarantees (to A) non-injective agreement of B with A on the
session key. Both goals are available to A in the sense of Goal Availability.
\<close>
lemma A_authenticates_and_keydist_to_B:
     "\<lbrakk>Crypt K (Nonce NB) \<in> parts (spies evs);
       Crypt (shrK A) \<lbrace>NA, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
       Key K \<notin> analz(knows Spy evs);
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt K (Nonce NB)) on evs"
by (blast intro: A_trusts_NS4_lemma B_Issues_A dest: A_trusts_NS2)

lemma A_trusts_NS5:
  "\<lbrakk> Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace> \<in> parts(spies evs);
     Crypt (shrK A) \<lbrace>Nonce NA, Agent B, Key K, X\<rbrace> \<in> parts(spies evs);
     Key K \<notin> analz (spies evs);
     A \<notin> bad; B \<notin> bad; evs \<in> ns_shared \<rbrakk>
 \<Longrightarrow> Says A B (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule ns_shared.induct, analz_mono_contra)
apply (simp_all)
txt\<open>Fake\<close>
apply blast
txt\<open>NS2\<close>
apply (force dest!: Crypt_imp_keysFor)
txt\<open>NS3\<close>
apply (metis NS3_msg_in_parts_spies parts_cut_eq)
txt\<open>NS5, the most important case, can be solved by unicity\<close>
apply (metis A_trusts_NS2 Crypt_Spy_analz_bad Says_imp_analz_Spy Says_imp_parts_knows_Spy analz.Fst analz.Snd unique_session_keys)
done

lemma A_Issues_B:
     "\<lbrakk> Says A B (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) \<in> set evs;
        Key K \<notin> analz (spies evs);
        A \<notin> bad;  B \<notin> bad; evs \<in> ns_shared \<rbrakk>
    \<Longrightarrow> A Issues B with (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) on evs"
unfolding Issues_def
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule ns_shared.induct, analz_mono_contra)
apply (simp_all)
txt\<open>fake\<close>
apply blast
apply (simp_all add: takeWhile_tail)
txt\<open>NS3 remains by pure coincidence!\<close>
apply (force dest!: A_trusts_NS2 Says_Server_message_form)
txt\<open>NS5 is the non-trivial case and cannot be solved as in \<^term>\<open>B_Issues_A\<close>! because NB is not fresh. We need \<^term>\<open>A_trusts_NS5\<close>, proved for this very purpose\<close>
apply (blast dest: A_trusts_NS5 parts_spies_takeWhile_mono [THEN subsetD]
        parts_spies_evs_revD2 [THEN subsetD])
done

text\<open>Tells B that A was alive after B issued NB.

Precisely, the theorem guarantees (to B) key distribution of the session key to A. It also guarantees (to B) non-injective agreement of A with B on the session key. Both goals are available to B in the sense of Goal Availability.
\<close>
lemma B_authenticates_and_keydist_to_A:
     "\<lbrakk>Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace> \<in> parts (spies evs);
       Crypt (shrK B) \<lbrace>Key K, Agent A\<rbrace> \<in> parts (spies evs);
       Key K \<notin> analz (spies evs);
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_shared\<rbrakk>
   \<Longrightarrow> A Issues B with (Crypt K \<lbrace>Nonce NB, Nonce NB\<rbrace>) on evs"
by (blast intro: A_Issues_B B_trusts_NS5_lemma dest: B_trusts_NS3)

end
