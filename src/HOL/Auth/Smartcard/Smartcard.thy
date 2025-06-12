(* Author:     Giampaolo Bella, Catania University
*)

section\<open>Theory of smartcards\<close>

theory Smartcard
imports EventSC "../All_Symmetric"
begin

text\<open>
As smartcards handle long-term (symmetric) keys, this theoy extends and 
supersedes theory Private.thy

An agent is bad if she reveals her PIN to the spy, not the shared key that
is embedded in her card. An agent's being bad implies nothing about her 
smartcard, which independently may be stolen or cloned.
\<close>

axiomatization
  shrK    :: "agent => key" and  (*long-term keys saved in smart cards*)
  crdK    :: "card  => key" and  (*smart cards' symmetric keys*)
  pin     :: "agent => key" and  (*pin to activate the smart cards*)

  (*Mostly for Shoup-Rubin*)
  Pairkey :: "agent * agent => nat" and
  pairK   :: "agent * agent => key"
where
  inj_shrK: "inj shrK" and  \<comment> \<open>No two smartcards store the same key\<close>
  inj_crdK: "inj crdK" and  \<comment> \<open>Nor do two cards\<close>
  inj_pin : "inj pin" and   \<comment> \<open>Nor do two agents have the same pin\<close>

  (*pairK is injective on each component, if we assume encryption to be a PRF
    or at least collision free *)
  inj_pairK    [iff]: "(pairK(A,B) = pairK(A',B')) = (A = A' & B = B')" and
  comm_Pairkey [iff]: "Pairkey(A,B) = Pairkey(B,A)" and

  (*long-term keys differ from each other*)
  pairK_disj_crdK [iff]: "pairK(A,B) \<noteq> crdK C" and
  pairK_disj_shrK [iff]: "pairK(A,B) \<noteq> shrK P" and
  pairK_disj_pin [iff]:  "pairK(A,B) \<noteq> pin P" and
  shrK_disj_crdK [iff]:  "shrK P \<noteq> crdK C" and
  shrK_disj_pin [iff]:  "shrK P \<noteq> pin Q" and
  crdK_disj_pin [iff]:   "crdK C \<noteq> pin P"

definition legalUse :: "card => bool" (\<open>legalUse (_)\<close>) where
  "legalUse C == C \<notin> stolen"

primrec illegalUse :: "card  => bool" where
  illegalUse_def: "illegalUse (Card A) = ( (Card A \<in> stolen \<and> A \<in> bad)  \<or>  Card A \<in> cloned )"


text\<open>initState must be defined with care\<close>

overloading
  initState \<equiv> initState
begin

primrec initState where
(*Server knows all long-term keys; adding cards' keys may be redundant but
  helps prove crdK_in_initState and crdK_in_used to distinguish cards' keys
  from fresh (session) keys*)
  initState_Server:  "initState Server = 
        (Key`(range shrK \<union> range crdK \<union> range pin \<union> range pairK)) \<union> 
        (Nonce`(range Pairkey))" |

(*Other agents know only their own*)
  initState_Friend:  "initState (Friend i) = {Key (pin (Friend i))}" |

(*Spy knows bad agents' pins, cloned cards' keys, pairKs, and Pairkeys *)
  initState_Spy: "initState Spy  = 
                 (Key`((pin`bad) \<union> (pin `{A. Card A \<in> cloned}) \<union> 
                                      (shrK`{A. Card A \<in> cloned}) \<union> 
                        (crdK`cloned) \<union> 
                        (pairK`{(X,A). Card A \<in> cloned})))
           \<union> (Nonce`(Pairkey`{(A,B). Card A \<in> cloned & Card B \<in> cloned}))"

end

text\<open>Still relying on axioms\<close>
axiomatization where
  Key_supply_ax:  "finite KK \<Longrightarrow> \<exists> K. K \<notin> KK & Key K \<notin> used evs" and

  (*Needed because of Spy's knowledge of Pairkeys*)
  Nonce_supply_ax: "finite NN \<Longrightarrow> \<exists> N. N \<notin> NN & Nonce N \<notin> used evs"







subsection\<open>Basic properties of shrK\<close>

(*Injectiveness: Agents' long-term keys are distinct.*)
declare inj_shrK [THEN inj_eq, iff]
declare inj_crdK [THEN inj_eq, iff]
declare inj_pin  [THEN inj_eq, iff]

lemma invKey_K [simp]: "invKey K = K"
apply (insert isSym_keys)
apply (simp add: symKeys_def) 
done


lemma analz_Decrypt' [dest]:
     "\<lbrakk> Crypt K X \<in> analz H;  Key K  \<in> analz H \<rbrakk> \<Longrightarrow> X \<in> analz H"
by auto

text\<open>Now cancel the \<open>dest\<close> attribute given to
 \<open>analz.Decrypt\<close> in its declaration.\<close>
declare analz.Decrypt [rule del]

text\<open>Rewrites should not refer to  \<^term>\<open>initState(Friend i)\<close> because
  that expression is not in normal form.\<close>

text\<open>Added to extend initstate with set of nonces\<close>
lemma parts_image_Nonce [simp]: "parts (Nonce`N) = Nonce`N"
  by auto

lemma keysFor_parts_initState [simp]: "keysFor (parts (initState C)) = {}"
unfolding keysFor_def
apply (induct_tac "C", auto)
done

(*Specialized to shared-key model: no @{term invKey}*)
lemma keysFor_parts_insert:
     "\<lbrakk> K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) \<rbrakk> 
     \<Longrightarrow> K \<in> keysFor (parts (G \<union> H)) | Key K \<in> parts H"
by (force dest: EventSC.keysFor_parts_insert)  

lemma Crypt_imp_keysFor: "Crypt K X \<in> H \<Longrightarrow> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)


subsection\<open>Function "knows"\<close>

(*Spy knows the pins of bad agents!*)
lemma Spy_knows_bad [intro!]: "A \<in> bad \<Longrightarrow> Key (pin A) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done

(*Spy knows the long-term keys of cloned cards!*)
lemma Spy_knows_cloned [intro!]: 
     "Card A \<in> cloned \<Longrightarrow>  Key (crdK (Card A)) \<in> knows Spy evs &   
                           Key (shrK A) \<in> knows Spy evs &  
                           Key (pin A)  \<in> knows Spy evs &  
                          (\<forall> B. Key (pairK(B,A)) \<in> knows Spy evs)"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done

lemma Spy_knows_cloned1 [intro!]: "C \<in> cloned \<Longrightarrow> Key (crdK C) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done

lemma Spy_knows_cloned2 [intro!]: "\<lbrakk> Card A \<in> cloned; Card B \<in> cloned \<rbrakk>  
   \<Longrightarrow> Nonce (Pairkey(A,B))\<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done

(*Spy only knows pins of bad agents!*)
lemma Spy_knows_Spy_bad [intro!]: "A\<in> bad \<Longrightarrow> Key (pin A) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done


(*For case analysis on whether or not an agent is compromised*)
lemma Crypt_Spy_analz_bad: 
  "\<lbrakk> Crypt (pin A) X \<in> analz (knows Spy evs);  A\<in>bad \<rbrakk>   
      \<Longrightarrow> X \<in> analz (knows Spy evs)"
apply (force dest!: analz.Decrypt)
done

(** Fresh keys never clash with other keys **)

lemma shrK_in_initState [iff]: "Key (shrK A) \<in> initState Server"
apply (induct_tac "A")
apply auto
done

lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
apply (rule initState_into_used)
apply blast
done

lemma crdK_in_initState [iff]: "Key (crdK A) \<in> initState Server"
apply (induct_tac "A")
apply auto
done

lemma crdK_in_used [iff]: "Key (crdK A) \<in> used evs"
apply (rule initState_into_used)
apply blast
done

lemma pin_in_initState [iff]: "Key (pin A) \<in> initState A"
apply (induct_tac "A")
apply auto
done

lemma pin_in_used [iff]: "Key (pin A) \<in> used evs"
apply (rule initState_into_used)
apply blast
done

lemma pairK_in_initState [iff]: "Key (pairK X) \<in> initState Server"
apply (induct_tac "X")
apply auto
done

lemma pairK_in_used [iff]: "Key (pairK X) \<in> used evs"
apply (rule initState_into_used)
apply blast
done



(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
lemma Key_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range shrK"
by blast

lemma shrK_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> shrK B \<noteq> K"
by blast

lemma crdK_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range crdK"
apply clarify
done

lemma crdK_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> crdK C \<noteq> K"
apply clarify
done

lemma pin_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range pin"
apply clarify
done

lemma pin_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> pin A \<noteq> K"
apply clarify
done

lemma pairK_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range pairK"
apply clarify
done

lemma pairK_neq [simp]: "Key K \<notin> used evs \<Longrightarrow> pairK(A,B) \<noteq> K"
apply clarify
done

declare shrK_neq [THEN not_sym, simp]
declare crdK_neq [THEN not_sym, simp]
declare pin_neq [THEN not_sym, simp]
declare pairK_neq [THEN not_sym, simp]


subsection\<open>Fresh nonces\<close>

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState (Friend i))"
by auto


(*This lemma no longer holds of smartcard protocols, where the cards can store
  nonces.

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
unfolding used_Nil
done

So, we must use old-style supply fresh nonce theorems relying on the appropriate axiom*)


subsection\<open>Supply fresh nonces for possibility theorems.\<close>


lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
apply (rule finite.emptyI [THEN Nonce_supply_ax, THEN exE], blast)
done

lemma Nonce_supply2: 
  "\<exists>N N'. Nonce N \<notin> used evs & Nonce N' \<notin> used evs' & N \<noteq> N'"
apply (cut_tac evs = evs in finite.emptyI [THEN Nonce_supply_ax])
apply (erule exE)
apply (cut_tac evs = evs' in finite.emptyI [THEN finite.insertI, THEN Nonce_supply_ax]) 
apply auto
done


lemma Nonce_supply3: "\<exists>N N' N''. Nonce N \<notin> used evs & Nonce N' \<notin> used evs' &  
                    Nonce N'' \<notin> used evs'' & N \<noteq> N' & N' \<noteq> N'' & N \<noteq> N''"
apply (cut_tac evs = evs in finite.emptyI [THEN Nonce_supply_ax])
apply (erule exE)
apply (cut_tac evs = evs' and a1 = N in finite.emptyI [THEN finite.insertI, THEN Nonce_supply_ax]) 
apply (erule exE)
apply (cut_tac evs = evs'' and a1 = Na and a2 = N in finite.emptyI [THEN finite.insertI, THEN finite.insertI, THEN Nonce_supply_ax]) 
apply blast
done

lemma Nonce_supply: "Nonce (SOME N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule finite.emptyI [THEN Nonce_supply_ax, THEN exE])
apply (rule someI, blast)
done



text\<open>Unlike the corresponding property of nonces, we cannot prove
    \<^term>\<open>finite KK \<Longrightarrow> \<exists>K. K \<notin> KK & Key K \<notin> used evs\<close>.
    We have infinitely many agents and there is nothing to stop their
    long-term keys from exhausting all the natural numbers.  Instead,
    possibility theorems must assume the existence of a few keys.\<close>


subsection\<open>Specialized Rewriting for Theorems About \<^term>\<open>analz\<close> and Image\<close>

lemma subset_Compl_range_shrK: "A \<subseteq> - (range shrK) \<Longrightarrow> shrK x \<notin> A"
by blast

lemma subset_Compl_range_crdK: "A \<subseteq> - (range crdK) \<Longrightarrow> crdK x \<notin> A"
apply blast
done

lemma subset_Compl_range_pin: "A \<subseteq> - (range pin) \<Longrightarrow> pin x \<notin> A"
apply blast
done

lemma subset_Compl_range_pairK: "A \<subseteq> - (range pairK) \<Longrightarrow> pairK x \<notin> A"
apply blast
done
lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H"
by blast

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key`(insert K KK) \<union> C"
by blast

(** Reverse the normal simplification of "image" to build up (not break down)
    the set of keys.  Use analz_insert_eq with (Un_upper2 RS analz_mono) to
    erase occurrences of forwarded message components (X). **)

lemmas analz_image_freshK_simps =
       simp_thms mem_simps \<comment> \<open>these two allow its use with \<open>only:\<close>\<close>
       disj_comms 
       image_insert [THEN sym] image_Un [THEN sym] empty_subsetI insert_subset
       analz_insert_eq Un_upper2 [THEN analz_mono, THEN [2] rev_subsetD]
       insert_Key_singleton subset_Compl_range_shrK subset_Compl_range_crdK
       subset_Compl_range_pin subset_Compl_range_pairK
       Key_not_used insert_Key_image Un_assoc [THEN sym]

(*Lemma for the trivial direction of the if-and-only-if*)
lemma analz_image_freshK_lemma:
     "(Key K \<in> analz (Key`nE \<union> H)) \<longrightarrow> (K \<in> nE | Key K \<in> analz H)  \<Longrightarrow>  
         (Key K \<in> analz (Key`nE \<union> H)) = (K \<in> nE | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])


subsection\<open>Tactics for possibility theorems\<close>

ML
\<open>
structure Smartcard =
struct

(*Omitting used_Says makes the tactic much faster: it leaves expressions
    such as  Nonce ?N \<notin> used evs that match Nonce_supply*)
fun possibility_tac ctxt =
   (REPEAT 
    (ALLGOALS (simp_tac (ctxt
      delsimps @{thms used_Cons_simps}
      |> Simplifier.set_unsafe_solver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac ctxt [refl, conjI, @{thm Nonce_supply}])))

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac ctxt =
    REPEAT 
    (ALLGOALS (asm_simp_tac (ctxt |> Simplifier.set_unsafe_solver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac ctxt [refl, conjI]))

val analz_image_freshK_ss = 
  simpset_of
   (\<^context> delsimps @{thms image_insert image_Un}
               delsimps @{thms imp_disjL}    (*reduces blow-up*)
               addsimps @{thms analz_image_freshK_simps})
end
\<close>


(*Lets blast_tac perform this step without needing the simplifier*)
lemma invKey_shrK_iff [iff]:
     "(Key (invKey K) \<in> X) = (Key K \<in> X)"
by auto

(*Specialized methods*)

method_setup analz_freshK = \<open>
    Scan.succeed (fn ctxt =>
     (SIMPLE_METHOD
      (EVERY [REPEAT_FIRST (resolve_tac ctxt @{thms allI ballI impI}),
          REPEAT_FIRST (resolve_tac ctxt @{thms analz_image_freshK_lemma}),
          ALLGOALS (asm_simp_tac (put_simpset Smartcard.analz_image_freshK_ss ctxt))])))\<close>
    "for proving the Session Key Compromise theorem"

method_setup possibility = \<open>
    Scan.succeed (fn ctxt =>
        SIMPLE_METHOD (Smartcard.possibility_tac ctxt))\<close>
    "for proving possibility theorems"

method_setup basic_possibility = \<open>
    Scan.succeed (fn ctxt =>
        SIMPLE_METHOD (Smartcard.basic_possibility_tac ctxt))\<close>
    "for proving possibility theorems"

lemma knows_subset_knows_Cons: "knows A evs \<subseteq> knows A (e # evs)"
by (induct e) (auto simp: knows_Cons)

(*Needed for actual protocols that will follow*)
declare shrK_disj_crdK[THEN not_sym, iff]
declare shrK_disj_pin[THEN not_sym, iff]
declare pairK_disj_shrK[THEN not_sym, iff]
declare pairK_disj_crdK[THEN not_sym, iff]
declare pairK_disj_pin[THEN not_sym, iff]
declare crdK_disj_pin[THEN not_sym, iff]

declare legalUse_def [iff] illegalUse_def [iff]

end
