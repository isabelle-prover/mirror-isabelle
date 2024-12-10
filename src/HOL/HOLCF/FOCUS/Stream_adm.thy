(*  Title:      HOL/HOLCF/FOCUS/Stream_adm.thy
    Author:     David von Oheimb, TU Muenchen
*)

section \<open>Admissibility for streams\<close>

theory Stream_adm
imports "HOLCF-Library.Stream" "HOL-Library.Order_Continuity"
begin

definition
  stream_monoP  :: "(('a stream) set \<Rightarrow> ('a stream) set) \<Rightarrow> bool" where
  "stream_monoP F = (\<exists>Q i. \<forall>P s. enat i \<le> #s \<longrightarrow>
                    (s \<in> F P) = (stream_take i\<cdot>s \<in> Q \<and> iterate i\<cdot>rt\<cdot>s \<in> P))"

definition
  stream_antiP  :: "(('a stream) set \<Rightarrow> ('a stream) set) \<Rightarrow> bool" where
  "stream_antiP F = (\<forall>P x. \<exists>Q i.
                (#x  < enat i \<longrightarrow> (\<forall>y. x \<sqsubseteq> y \<longrightarrow> y \<in> F P \<longrightarrow> x \<in> F P)) \<and>
                (enat i <= #x \<longrightarrow> (\<forall>y. x \<sqsubseteq> y \<longrightarrow>
                (y \<in> F P) = (stream_take i\<cdot>y \<in> Q \<and> iterate i\<cdot>rt\<cdot>y \<in> P))))"

definition
  antitonP :: "'a set => bool" where
  "antitonP P = (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> y\<in>P \<longrightarrow> x\<in>P)"


(* ----------------------------------------------------------------------- *)

section "admissibility"

lemma infinite_chain_adm_lemma:
  "\<lbrakk>chain Y; \<forall>i. P (Y i);  
    \<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i); \<not> finite_chain Y\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)\<rbrakk>
      \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (case_tac "finite_chain Y")
prefer 2 apply fast
apply (unfold finite_chain_def)
apply safe
apply (erule lub_finch1 [THEN lub_eqI, THEN ssubst])
apply assumption
apply (erule spec)
done

lemma increasing_chain_adm_lemma:
  "\<lbrakk>chain Y;  \<forall>i. P (Y i); \<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i);
    \<forall>i. \<exists>j>i. Y i \<noteq> Y j \<and> Y i \<sqsubseteq> Y j\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)\<rbrakk>
      \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (erule infinite_chain_adm_lemma)
apply assumption
apply (erule thin_rl)
apply (unfold finite_chain_def)
apply (unfold max_in_chain_def)
apply (fast dest: le_imp_less_or_eq elim: chain_mono_less)
done

lemma flatstream_adm_lemma:
  assumes 1: "chain Y"
  assumes 2: "\<forall>i. P (Y i)"
  assumes 3: "(\<And>Y. [| chain Y; \<forall>i. P (Y i); \<forall>k. \<exists>j. enat k < #((Y j)::'a::flat stream)|]
  ==> P(LUB i. Y i))"
  shows "P(LUB i. Y i)"
apply (rule increasing_chain_adm_lemma [OF 1 2])
apply (erule 3, assumption)
apply (erule thin_rl)
apply (rule allI)
apply (case_tac "\<forall>j. stream_finite (Y j)")
apply ( rule chain_incr)
apply ( rule allI)
apply ( drule spec)
apply ( safe)
apply ( rule exI)
apply ( rule slen_strict_mono)
apply (   erule spec)
apply (  assumption)
apply ( assumption)
apply (metis enat_ord_code(4) slen_infinite)
done

(* should be without reference to stream length? *)
lemma flatstream_admI: "[|(\<And>Y. [| chain Y; \<forall>i. P (Y i); 
 \<forall>k. \<exists>j. enat k < #((Y j)::'a::flat stream)|] ==> P(LUB i. Y i))|]==> adm P"
apply (unfold adm_def)
apply (intro strip)
apply (erule (1) flatstream_adm_lemma)
apply (fast)
done


(* context (theory "Extended_Nat");*)
lemma ile_lemma: "enat (i + j) <= x ==> enat i <= x"
  by (rule order_trans) auto

lemma stream_monoP2I:
"\<And>X. stream_monoP F \<Longrightarrow> \<forall>i. \<exists>l. \<forall>x y.
  enat l \<le> #x \<longrightarrow> (x::'a::flat stream) << y --> x \<in> (F ^^ i) top \<longrightarrow> y \<in> (F ^^ i) top"
apply (unfold stream_monoP_def)
apply (safe)
apply (rule_tac x="i*ia" in exI)
apply (induct_tac "ia")
apply ( simp)
apply (simp)
apply (intro strip)
apply (erule allE, erule all_dupE, drule mp, erule ile_lemma)
apply (drule_tac P="%x. x" in subst, assumption)
apply (erule allE, drule mp, rule ile_lemma) back
apply ( erule order_trans)
apply ( erule slen_mono)
apply (erule ssubst)
apply (safe)
apply ( erule (2) ile_lemma [THEN slen_take_lemma3, THEN subst])
apply (erule allE)
apply (drule mp)
apply ( erule slen_rt_mult)
apply (erule allE)
apply (drule mp)
apply (erule monofun_rt_mult)
apply (drule (1) mp)
apply (assumption)
done

lemma stream_monoP2_gfp_admI: "[| \<forall>i. \<exists>l. \<forall>x y.
 enat l \<le> #x \<longrightarrow> (x::'a::flat stream) << y \<longrightarrow> x \<in> (F ^^ i) top \<longrightarrow> y \<in> (F ^^ i) top;
    inf_continuous F |] ==> adm (\<lambda>x. x \<in> gfp F)"
apply (erule inf_continuous_gfp[of F, THEN ssubst])
apply (simp (no_asm))
apply (rule adm_lemmas)
apply (rule flatstream_admI)
apply (erule allE)
apply (erule exE)
apply (erule allE, erule exE)
apply (erule allE, erule allE, drule mp) (* stream_monoP *)
apply ( drule ileI1)
apply ( drule order_trans)
apply (  rule ile_eSuc)
apply ( drule eSuc_ile_mono [THEN iffD1])
apply ( assumption)
apply (drule mp)
apply ( erule is_ub_thelub)
apply (fast)
done

lemmas fstream_gfp_admI = stream_monoP2I [THEN stream_monoP2_gfp_admI]

lemma stream_antiP2I:
"\<And>X. [|stream_antiP (F::(('a::flat stream)set => ('a stream set)))|]
  ==> \<forall>i x y. x << y \<longrightarrow> y \<in> (F ^^ i) top \<longrightarrow> x \<in> (F ^^ i) top"
apply (unfold stream_antiP_def)
apply (rule allI)
apply (induct_tac "i")
apply ( simp)
apply (simp)
apply (intro strip)
apply (erule allE, erule all_dupE, erule exE, erule exE)
apply (erule conjE)
apply (case_tac "#x < enat i")
apply ( fast)
apply (unfold linorder_not_less)
apply (drule (1) mp)
apply (erule all_dupE, drule mp, rule below_refl)
apply (erule ssubst)
apply (erule allE, drule (1) mp)
apply (drule_tac P="%x. x" in subst, assumption)
apply (erule conjE, rule conjI)
apply ( erule slen_take_lemma3 [THEN ssubst], assumption)
apply ( assumption)
apply (erule allE, erule allE, drule mp, erule monofun_rt_mult)
apply (drule (1) mp)
apply (assumption)
done

lemma stream_antiP2_non_gfp_admI:
"\<And>X. [|\<forall>i x y. x << y \<longrightarrow> y \<in> (F ^^ i) top \<longrightarrow> x \<in> (F ^^ i) top; inf_continuous F |]
  ==> adm (\<lambda>u. \<not> u \<in> gfp F)"
apply (unfold adm_def)
apply (simp add: inf_continuous_gfp)
apply (fast dest!: is_ub_thelub)
done

lemmas fstream_non_gfp_admI = stream_antiP2I [THEN stream_antiP2_non_gfp_admI]



(**new approach for adm********************************************************)

section "antitonP"

lemma antitonPD: "[| antitonP P; y \<in> P; x<<y |] ==> x \<in> P"
apply (unfold antitonP_def)
apply auto
done

lemma antitonPI: "\<forall>x y. y \<in> P \<longrightarrow> x<<y --> x \<in> P \<Longrightarrow> antitonP P"
apply (unfold antitonP_def)
apply (fast)
done

lemma antitonP_adm_non_P: "antitonP P \<Longrightarrow> adm (\<lambda>u. u \<notin> P)"
apply (unfold adm_def)
apply (auto dest: antitonPD elim: is_ub_thelub)
done

lemma def_gfp_adm_nonP: "P \<equiv> gfp F \<Longrightarrow> {y. \<exists>x::'a::pcpo. y \<sqsubseteq> x \<and> x \<in> P} \<subseteq> F {y. \<exists>x. y \<sqsubseteq> x \<and> x \<in> P} \<Longrightarrow> 
  adm (\<lambda>u. u\<notin>P)"
apply (simp)
apply (rule antitonP_adm_non_P)
apply (rule antitonPI)
apply (drule gfp_upperbound)
apply (fast)
done

lemma adm_set:
"{\<Squnion>i. Y i |Y. chain Y \<and> (\<forall>i. Y i \<in> P)} \<subseteq> P \<Longrightarrow> adm (\<lambda>x. x\<in>P)"
apply (unfold adm_def)
apply (fast)
done

lemma def_gfp_admI: "P \<equiv> gfp F \<Longrightarrow> {\<Squnion>i. Y i |Y. chain Y \<and> (\<forall>i. Y i \<in> P)} \<subseteq> 
  F {\<Squnion>i. Y i |Y. chain Y \<and> (\<forall>i. Y i \<in> P)} \<Longrightarrow> adm (\<lambda>x. x\<in>P)"
apply (simp)
apply (rule adm_set)
apply (erule gfp_upperbound)
done

end
