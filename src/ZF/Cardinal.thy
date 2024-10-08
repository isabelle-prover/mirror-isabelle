(*  Title:      ZF/Cardinal.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Cardinal Numbers Without the Axiom of Choice\<close>

theory Cardinal imports OrderType Finite Nat Sum begin

definition
  (*least ordinal operator*)
   Least    :: "(i\<Rightarrow>o) \<Rightarrow> i"    (binder \<open>\<mu> \<close> 10)  where
     "Least(P) \<equiv> THE i. Ord(i) \<and> P(i) \<and> (\<forall>j. j<i \<longrightarrow> \<not>P(j))"

definition
  eqpoll   :: "[i,i] \<Rightarrow> o"     (infixl \<open>\<approx>\<close> 50)  where
    "A \<approx> B \<equiv> \<exists>f. f \<in> bij(A,B)"

definition
  lepoll   :: "[i,i] \<Rightarrow> o"     (infixl \<open>\<lesssim>\<close> 50)  where
    "A \<lesssim> B \<equiv> \<exists>f. f \<in> inj(A,B)"

definition
  lesspoll :: "[i,i] \<Rightarrow> o"     (infixl \<open>\<prec>\<close> 50)  where
    "A \<prec> B \<equiv> A \<lesssim> B \<and> \<not>(A \<approx> B)"

definition
  cardinal :: "i\<Rightarrow>i"  (\<open>(\<open>open_block notation=\<open>mixfix cardinal\<close>\<close>|_|)\<close>)
  where "|A| \<equiv> (\<mu> i. i \<approx> A)"

definition
  Finite   :: "i\<Rightarrow>o"  where
    "Finite(A) \<equiv> \<exists>n\<in>nat. A \<approx> n"

definition
  Card     :: "i\<Rightarrow>o"  where
    "Card(i) \<equiv> (i = |i|)"


subsection\<open>The Schroeder-Bernstein Theorem\<close>
text\<open>See Davey and Priestly, page 106\<close>

(** Lemma: Banach's Decomposition Theorem **)

lemma decomp_bnd_mono: "bnd_mono(X, \<lambda>W. X - g``(Y - f``W))"
by (rule bnd_monoI, blast+)

lemma Banach_last_equation:
    "g \<in> Y->X
     \<Longrightarrow> g``(Y - f`` lfp(X, \<lambda>W. X - g``(Y - f``W))) =
         X - lfp(X, \<lambda>W. X - g``(Y - f``W))"
apply (rule_tac P = "\<lambda>u. v = X-u" for v
       in decomp_bnd_mono [THEN lfp_unfold, THEN ssubst])
apply (simp add: double_complement  fun_is_rel [THEN image_subset])
done

lemma decomposition:
     "\<lbrakk>f \<in> X->Y;  g \<in> Y->X\<rbrakk> \<Longrightarrow>
      \<exists>XA XB YA YB. (XA \<inter> XB = 0) \<and> (XA \<union> XB = X) \<and>
                      (YA \<inter> YB = 0) \<and> (YA \<union> YB = Y) \<and>
                      f``XA=YA \<and> g``YB=XB"
apply (intro exI conjI)
apply (rule_tac [6] Banach_last_equation)
apply (rule_tac [5] refl)
apply (assumption |
       rule  Diff_disjoint Diff_partition fun_is_rel image_subset lfp_subset)+
done

lemma schroeder_bernstein:
    "\<lbrakk>f \<in> inj(X,Y);  g \<in> inj(Y,X)\<rbrakk> \<Longrightarrow> \<exists>h. h \<in> bij(X,Y)"
apply (insert decomposition [of f X Y g])
apply (simp add: inj_is_fun)
apply (blast intro!: restrict_bij bij_disjoint_Un intro: bij_converse_bij)
(* The instantiation of exI to @{term"restrict(f,XA) \<union> converse(restrict(g,YB))"}
   is forced by the context\<And>*)
done


(** Equipollence is an equivalence relation **)

lemma bij_imp_eqpoll: "f \<in> bij(A,B) \<Longrightarrow> A \<approx> B"
  unfolding eqpoll_def
apply (erule exI)
done

(*A \<approx> A*)
lemmas eqpoll_refl = id_bij [THEN bij_imp_eqpoll, simp]

lemma eqpoll_sym: "X \<approx> Y \<Longrightarrow> Y \<approx> X"
  unfolding eqpoll_def
apply (blast intro: bij_converse_bij)
done

lemma eqpoll_trans [trans]:
    "\<lbrakk>X \<approx> Y;  Y \<approx> Z\<rbrakk> \<Longrightarrow> X \<approx> Z"
  unfolding eqpoll_def
apply (blast intro: comp_bij)
done

(** Le-pollence is a partial ordering **)

lemma subset_imp_lepoll: "X<=Y \<Longrightarrow> X \<lesssim> Y"
  unfolding lepoll_def
apply (rule exI)
apply (erule id_subset_inj)
done

lemmas lepoll_refl = subset_refl [THEN subset_imp_lepoll, simp]

lemmas le_imp_lepoll = le_imp_subset [THEN subset_imp_lepoll]

lemma eqpoll_imp_lepoll: "X \<approx> Y \<Longrightarrow> X \<lesssim> Y"
by (unfold eqpoll_def bij_def lepoll_def, blast)

lemma lepoll_trans [trans]: "\<lbrakk>X \<lesssim> Y;  Y \<lesssim> Z\<rbrakk> \<Longrightarrow> X \<lesssim> Z"
  unfolding lepoll_def
apply (blast intro: comp_inj)
done

lemma eq_lepoll_trans [trans]: "\<lbrakk>X \<approx> Y;  Y \<lesssim> Z\<rbrakk> \<Longrightarrow> X \<lesssim> Z"
 by (blast intro: eqpoll_imp_lepoll lepoll_trans)

lemma lepoll_eq_trans [trans]: "\<lbrakk>X \<lesssim> Y;  Y \<approx> Z\<rbrakk> \<Longrightarrow> X \<lesssim> Z"
 by (blast intro: eqpoll_imp_lepoll lepoll_trans)

(*Asymmetry law*)
lemma eqpollI: "\<lbrakk>X \<lesssim> Y;  Y \<lesssim> X\<rbrakk> \<Longrightarrow> X \<approx> Y"
  unfolding lepoll_def eqpoll_def
apply (elim exE)
apply (rule schroeder_bernstein, assumption+)
done

lemma eqpollE:
    "\<lbrakk>X \<approx> Y; \<lbrakk>X \<lesssim> Y; Y \<lesssim> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (blast intro: eqpoll_imp_lepoll eqpoll_sym)

lemma eqpoll_iff: "X \<approx> Y \<longleftrightarrow> X \<lesssim> Y \<and> Y \<lesssim> X"
by (blast intro: eqpollI elim!: eqpollE)

lemma lepoll_0_is_0: "A \<lesssim> 0 \<Longrightarrow> A = 0"
  unfolding lepoll_def inj_def
apply (blast dest: apply_type)
done

(*@{term"0 \<lesssim> Y"}*)
lemmas empty_lepollI = empty_subsetI [THEN subset_imp_lepoll]

lemma lepoll_0_iff: "A \<lesssim> 0 \<longleftrightarrow> A=0"
by (blast intro: lepoll_0_is_0 lepoll_refl)

lemma Un_lepoll_Un:
    "\<lbrakk>A \<lesssim> B; C \<lesssim> D; B \<inter> D = 0\<rbrakk> \<Longrightarrow> A \<union> C \<lesssim> B \<union> D"
  unfolding lepoll_def
apply (blast intro: inj_disjoint_Un)
done

(*A \<approx> 0 \<Longrightarrow> A=0*)
lemmas eqpoll_0_is_0 = eqpoll_imp_lepoll [THEN lepoll_0_is_0]

lemma eqpoll_0_iff: "A \<approx> 0 \<longleftrightarrow> A=0"
by (blast intro: eqpoll_0_is_0 eqpoll_refl)

lemma eqpoll_disjoint_Un:
    "\<lbrakk>A \<approx> B;  C \<approx> D;  A \<inter> C = 0;  B \<inter> D = 0\<rbrakk>
     \<Longrightarrow> A \<union> C \<approx> B \<union> D"
  unfolding eqpoll_def
apply (blast intro: bij_disjoint_Un)
done


subsection\<open>lesspoll: contributions by Krzysztof Grabczewski\<close>

lemma lesspoll_not_refl: "\<not> (i \<prec> i)"
by (simp add: lesspoll_def)

lemma lesspoll_irrefl [elim!]: "i \<prec> i \<Longrightarrow> P"
by (simp add: lesspoll_def)

lemma lesspoll_imp_lepoll: "A \<prec> B \<Longrightarrow> A \<lesssim> B"
by (unfold lesspoll_def, blast)

lemma lepoll_well_ord: "\<lbrakk>A \<lesssim> B; well_ord(B,r)\<rbrakk> \<Longrightarrow> \<exists>s. well_ord(A,s)"
  unfolding lepoll_def
apply (blast intro: well_ord_rvimage)
done

lemma lepoll_iff_leqpoll: "A \<lesssim> B \<longleftrightarrow> A \<prec> B | A \<approx> B"
  unfolding lesspoll_def
apply (blast intro!: eqpollI elim!: eqpollE)
done

lemma inj_not_surj_succ:
  assumes fi: "f \<in> inj(A, succ(m))" and fns: "f \<notin> surj(A, succ(m))" 
  shows "\<exists>f. f \<in> inj(A,m)"
proof -
  from fi [THEN inj_is_fun] fns 
  obtain y where y: "y \<in> succ(m)" "\<And>x. x\<in>A \<Longrightarrow> f ` x \<noteq> y"
    by (auto simp add: surj_def)
  show ?thesis
    proof 
      show "(\<lambda>z\<in>A. if f`z = m then y else f`z) \<in> inj(A, m)" using y fi
        by (simp add: inj_def) 
           (auto intro!: if_type [THEN lam_type] intro: Pi_type dest: apply_funtype)
      qed
qed

(** Variations on transitivity **)

lemma lesspoll_trans [trans]:
      "\<lbrakk>X \<prec> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  unfolding lesspoll_def
apply (blast elim!: eqpollE intro: eqpollI lepoll_trans)
done

lemma lesspoll_trans1 [trans]:
      "\<lbrakk>X \<lesssim> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  unfolding lesspoll_def
apply (blast elim!: eqpollE intro: eqpollI lepoll_trans)
done

lemma lesspoll_trans2 [trans]:
      "\<lbrakk>X \<prec> Y; Y \<lesssim> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  unfolding lesspoll_def
apply (blast elim!: eqpollE intro: eqpollI lepoll_trans)
done

lemma eq_lesspoll_trans [trans]:
      "\<lbrakk>X \<approx> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (blast intro: eqpoll_imp_lepoll lesspoll_trans1)

lemma lesspoll_eq_trans [trans]:
      "\<lbrakk>X \<prec> Y; Y \<approx> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (blast intro: eqpoll_imp_lepoll lesspoll_trans2)


(** \<mu> -- the least number operator [from HOL/Univ.ML] **)

lemma Least_equality:
    "\<lbrakk>P(i);  Ord(i);  \<And>x. x<i \<Longrightarrow> \<not>P(x)\<rbrakk> \<Longrightarrow> (\<mu> x. P(x)) = i"
  unfolding Least_def
apply (rule the_equality, blast)
apply (elim conjE)
apply (erule Ord_linear_lt, assumption, blast+)
done

lemma LeastI: 
  assumes P: "P(i)" and i: "Ord(i)" shows "P(\<mu> x. P(x))"
proof -
  { from i have "P(i) \<Longrightarrow> P(\<mu> x. P(x))"
      proof (induct i rule: trans_induct)
        case (step i) 
        show ?case
          proof (cases "P(\<mu> a. P(a))")
            case True thus ?thesis .
          next
            case False
            hence "\<And>x. x \<in> i \<Longrightarrow> \<not>P(x)" using step
              by blast
            hence "(\<mu> a. P(a)) = i" using step
              by (blast intro: Least_equality ltD) 
            thus ?thesis using step.prems
              by simp 
          qed
      qed
  }
  thus ?thesis using P .
qed

text\<open>The proof is almost identical to the one above!\<close>
lemma Least_le: 
  assumes P: "P(i)" and i: "Ord(i)" shows "(\<mu> x. P(x)) \<le> i"
proof -
  { from i have "P(i) \<Longrightarrow> (\<mu> x. P(x)) \<le> i"
      proof (induct i rule: trans_induct)
        case (step i) 
        show ?case
          proof (cases "(\<mu> a. P(a)) \<le> i")
            case True thus ?thesis .
          next
            case False
            hence "\<And>x. x \<in> i \<Longrightarrow> \<not> (\<mu> a. P(a)) \<le> i" using step
              by blast
            hence "(\<mu> a. P(a)) = i" using step
              by (blast elim: ltE intro: ltI Least_equality lt_trans1)
            thus ?thesis using step
              by simp 
          qed
      qed
  }
  thus ?thesis using P .
qed

(*\<mu> really is the smallest*)
lemma less_LeastE: "\<lbrakk>P(i);  i < (\<mu> x. P(x))\<rbrakk> \<Longrightarrow> Q"
apply (rule Least_le [THEN [2] lt_trans2, THEN lt_irrefl], assumption+)
apply (simp add: lt_Ord)
done

(*Easier to apply than LeastI: conclusion has only one occurrence of P*)
lemma LeastI2:
    "\<lbrakk>P(i);  Ord(i);  \<And>j. P(j) \<Longrightarrow> Q(j)\<rbrakk> \<Longrightarrow> Q(\<mu> j. P(j))"
by (blast intro: LeastI )

(*If there is no such P then \<mu> is vacuously 0*)
lemma Least_0:
    "\<lbrakk>\<not> (\<exists>i. Ord(i) \<and> P(i))\<rbrakk> \<Longrightarrow> (\<mu> x. P(x)) = 0"
  unfolding Least_def
apply (rule the_0, blast)
done

lemma Ord_Least [intro,simp,TC]: "Ord(\<mu> x. P(x))"
proof (cases "\<exists>i. Ord(i) \<and> P(i)")
  case True 
  then obtain i where "P(i)" "Ord(i)"  by auto
  hence " (\<mu> x. P(x)) \<le> i"  by (rule Least_le) 
  thus ?thesis
    by (elim ltE)
next
  case False
  hence "(\<mu> x. P(x)) = 0"  by (rule Least_0)
  thus ?thesis
    by auto
qed


subsection\<open>Basic Properties of Cardinals\<close>

(*Not needed for simplification, but helpful below*)
lemma Least_cong: "(\<And>y. P(y) \<longleftrightarrow> Q(y)) \<Longrightarrow> (\<mu> x. P(x)) = (\<mu> x. Q(x))"
by simp

(*Need AC to get @{term"X \<lesssim> Y \<Longrightarrow> |X| \<le> |Y|"};  see well_ord_lepoll_imp_cardinal_le
  Converse also requires AC, but see well_ord_cardinal_eqE*)
lemma cardinal_cong: "X \<approx> Y \<Longrightarrow> |X| = |Y|"
  unfolding eqpoll_def cardinal_def
apply (rule Least_cong)
apply (blast intro: comp_bij bij_converse_bij)
done

(*Under AC, the premise becomes trivial; one consequence is ||A|| = |A|*)
lemma well_ord_cardinal_eqpoll:
  assumes r: "well_ord(A,r)" shows "|A| \<approx> A"
proof (unfold cardinal_def)
  show "(\<mu> i. i \<approx> A) \<approx> A"
    by (best intro: LeastI Ord_ordertype ordermap_bij bij_converse_bij bij_imp_eqpoll r) 
qed

(* @{term"Ord(A) \<Longrightarrow> |A| \<approx> A"} *)
lemmas Ord_cardinal_eqpoll = well_ord_Memrel [THEN well_ord_cardinal_eqpoll]

lemma Ord_cardinal_idem: "Ord(A) \<Longrightarrow> ||A|| = |A|"
 by (rule Ord_cardinal_eqpoll [THEN cardinal_cong])

lemma well_ord_cardinal_eqE:
  assumes woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" and eq: "|X| = |Y|"
shows "X \<approx> Y"
proof -
  have "X \<approx> |X|" by (blast intro: well_ord_cardinal_eqpoll [OF woX] eqpoll_sym)
  also have "... = |Y|" by (rule eq)
  also have "... \<approx> Y" by (rule well_ord_cardinal_eqpoll [OF woY])
  finally show ?thesis .
qed

lemma well_ord_cardinal_eqpoll_iff:
     "\<lbrakk>well_ord(X,r);  well_ord(Y,s)\<rbrakk> \<Longrightarrow> |X| = |Y| \<longleftrightarrow> X \<approx> Y"
by (blast intro: cardinal_cong well_ord_cardinal_eqE)


(** Observations from Kunen, page 28 **)

lemma Ord_cardinal_le: "Ord(i) \<Longrightarrow> |i| \<le> i"
  unfolding cardinal_def
apply (erule eqpoll_refl [THEN Least_le])
done

lemma Card_cardinal_eq: "Card(K) \<Longrightarrow> |K| = K"
  unfolding Card_def
apply (erule sym)
done

(* Could replace the  @{term"\<not>(j \<approx> i)"}  by  @{term"\<not>(i \<preceq> j)"}. *)
lemma CardI: "\<lbrakk>Ord(i);  \<And>j. j<i \<Longrightarrow> \<not>(j \<approx> i)\<rbrakk> \<Longrightarrow> Card(i)"
  unfolding Card_def cardinal_def
apply (subst Least_equality)
apply (blast intro: eqpoll_refl)+
done

lemma Card_is_Ord: "Card(i) \<Longrightarrow> Ord(i)"
  unfolding Card_def cardinal_def
apply (erule ssubst)
apply (rule Ord_Least)
done

lemma Card_cardinal_le: "Card(K) \<Longrightarrow> K \<le> |K|"
apply (simp (no_asm_simp) add: Card_is_Ord Card_cardinal_eq)
done

lemma Ord_cardinal [simp,intro!]: "Ord(|A|)"
  unfolding cardinal_def
apply (rule Ord_Least)
done

text\<open>The cardinals are the initial ordinals.\<close>
lemma Card_iff_initial: "Card(K) \<longleftrightarrow> Ord(K) \<and> (\<forall>j. j<K \<longrightarrow> \<not> j \<approx> K)"
proof -
  { fix j
    assume K: "Card(K)" "j \<approx> K"
    assume "j < K"
    also have "... = (\<mu> i. i \<approx> K)" using K
      by (simp add: Card_def cardinal_def)
    finally have "j < (\<mu> i. i \<approx> K)" .
    hence "False" using K
      by (best dest: less_LeastE) 
  }
  then show ?thesis
    by (blast intro: CardI Card_is_Ord) 
qed

lemma lt_Card_imp_lesspoll: "\<lbrakk>Card(a); i<a\<rbrakk> \<Longrightarrow> i \<prec> a"
  unfolding lesspoll_def
apply (drule Card_iff_initial [THEN iffD1])
apply (blast intro!: leI [THEN le_imp_lepoll])
done

lemma Card_0: "Card(0)"
apply (rule Ord_0 [THEN CardI])
apply (blast elim!: ltE)
done

lemma Card_Un: "\<lbrakk>Card(K);  Card(L)\<rbrakk> \<Longrightarrow> Card(K \<union> L)"
apply (rule Ord_linear_le [of K L])
apply (simp_all add: subset_Un_iff [THEN iffD1]  Card_is_Ord le_imp_subset
                     subset_Un_iff2 [THEN iffD1])
done

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

lemma Card_cardinal [iff]: "Card(|A|)"
proof (unfold cardinal_def)
  show "Card(\<mu> i. i \<approx> A)"
    proof (cases "\<exists>i. Ord (i) \<and> i \<approx> A")
      case False thus ?thesis           \<comment> \<open>degenerate case\<close>
        by (simp add: Least_0 Card_0)
    next
      case True                         \<comment> \<open>real case: \<^term>\<open>A\<close> is isomorphic to some ordinal\<close>
      then obtain i where i: "Ord(i)" "i \<approx> A" by blast
      show ?thesis
        proof (rule CardI [OF Ord_Least], rule notI)
          fix j
          assume j: "j < (\<mu> i. i \<approx> A)"
          assume "j \<approx> (\<mu> i. i \<approx> A)"
          also have "... \<approx> A" using i by (auto intro: LeastI)
          finally have "j \<approx> A" .
          thus False
            by (rule less_LeastE [OF _ j])
        qed
    qed
qed

(*Kunen's Lemma 10.5*)
lemma cardinal_eq_lemma:
  assumes i:"|i| \<le> j" and j: "j \<le> i" shows "|j| = |i|"
proof (rule eqpollI [THEN cardinal_cong])
  show "j \<lesssim> i" by (rule le_imp_lepoll [OF j])
next
  have Oi: "Ord(i)" using j by (rule le_Ord2)
  hence "i \<approx> |i|"
    by (blast intro: Ord_cardinal_eqpoll eqpoll_sym)
  also have "... \<lesssim> j"
    by (blast intro: le_imp_lepoll i)
  finally show "i \<lesssim> j" .
qed

lemma cardinal_mono:
  assumes ij: "i \<le> j" shows "|i| \<le> |j|"
using Ord_cardinal [of i] Ord_cardinal [of j]
proof (cases rule: Ord_linear_le)
  case le thus ?thesis .
next
  case ge
  have i: "Ord(i)" using ij
    by (simp add: lt_Ord)
  have ci: "|i| \<le> j"
    by (blast intro: Ord_cardinal_le ij le_trans i)
  have "|i| = ||i||"
    by (auto simp add: Ord_cardinal_idem i)
  also have "... = |j|"
    by (rule cardinal_eq_lemma [OF ge ci])
  finally have "|i| = |j|" .
  thus ?thesis by simp
qed

text\<open>Since we have \<^term>\<open>|succ(nat)| \<le> |nat|\<close>, the converse of \<open>cardinal_mono\<close> fails!\<close>
lemma cardinal_lt_imp_lt: "\<lbrakk>|i| < |j|;  Ord(i);  Ord(j)\<rbrakk> \<Longrightarrow> i < j"
apply (rule Ord_linear2 [of i j], assumption+)
apply (erule lt_trans2 [THEN lt_irrefl])
apply (erule cardinal_mono)
done

lemma Card_lt_imp_lt: "\<lbrakk>|i| < K;  Ord(i);  Card(K)\<rbrakk> \<Longrightarrow> i < K"
  by (simp (no_asm_simp) add: cardinal_lt_imp_lt Card_is_Ord Card_cardinal_eq)

lemma Card_lt_iff: "\<lbrakk>Ord(i);  Card(K)\<rbrakk> \<Longrightarrow> (|i| < K) \<longleftrightarrow> (i < K)"
by (blast intro: Card_lt_imp_lt Ord_cardinal_le [THEN lt_trans1])

lemma Card_le_iff: "\<lbrakk>Ord(i);  Card(K)\<rbrakk> \<Longrightarrow> (K \<le> |i|) \<longleftrightarrow> (K \<le> i)"
by (simp add: Card_lt_iff Card_is_Ord Ord_cardinal not_lt_iff_le [THEN iff_sym])

(*Can use AC or finiteness to discharge first premise*)
lemma well_ord_lepoll_imp_cardinal_le:
  assumes wB: "well_ord(B,r)" and AB: "A \<lesssim> B"
  shows "|A| \<le> |B|"
using Ord_cardinal [of A] Ord_cardinal [of B]
proof (cases rule: Ord_linear_le)
  case le thus ?thesis .
next
  case ge
  from lepoll_well_ord [OF AB wB]
  obtain s where s: "well_ord(A, s)" by blast
  have "B  \<approx> |B|" by (blast intro: wB eqpoll_sym well_ord_cardinal_eqpoll)
  also have "... \<lesssim> |A|" by (rule le_imp_lepoll [OF ge])
  also have "... \<approx> A" by (rule well_ord_cardinal_eqpoll [OF s])
  finally have "B \<lesssim> A" .
  hence "A \<approx> B" by (blast intro: eqpollI AB)
  hence "|A| = |B|" by (rule cardinal_cong)
  thus ?thesis by simp
qed

lemma lepoll_cardinal_le: "\<lbrakk>A \<lesssim> i; Ord(i)\<rbrakk> \<Longrightarrow> |A| \<le> i"
apply (rule le_trans)
apply (erule well_ord_Memrel [THEN well_ord_lepoll_imp_cardinal_le], assumption)
apply (erule Ord_cardinal_le)
done

lemma lepoll_Ord_imp_eqpoll: "\<lbrakk>A \<lesssim> i; Ord(i)\<rbrakk> \<Longrightarrow> |A| \<approx> A"
by (blast intro: lepoll_cardinal_le well_ord_Memrel well_ord_cardinal_eqpoll dest!: lepoll_well_ord)

lemma lesspoll_imp_eqpoll: "\<lbrakk>A \<prec> i; Ord(i)\<rbrakk> \<Longrightarrow> |A| \<approx> A"
  unfolding lesspoll_def
apply (blast intro: lepoll_Ord_imp_eqpoll)
done

lemma cardinal_subset_Ord: "\<lbrakk>A<=i; Ord(i)\<rbrakk> \<Longrightarrow> |A| \<subseteq> i"
apply (drule subset_imp_lepoll [THEN lepoll_cardinal_le])
apply (auto simp add: lt_def)
apply (blast intro: Ord_trans)
done

subsection\<open>The finite cardinals\<close>

lemma cons_lepoll_consD:
 "\<lbrakk>cons(u,A) \<lesssim> cons(v,B);  u\<notin>A;  v\<notin>B\<rbrakk> \<Longrightarrow> A \<lesssim> B"
apply (unfold lepoll_def inj_def, safe)
apply (rule_tac x = "\<lambda>x\<in>A. if f`x=v then f`u else f`x" in exI)
apply (rule CollectI)
(*Proving it's in the function space A->B*)
apply (rule if_type [THEN lam_type])
apply (blast dest: apply_funtype)
apply (blast elim!: mem_irrefl dest: apply_funtype)
(*Proving it's injective*)
apply (simp (no_asm_simp))
apply blast
done

lemma cons_eqpoll_consD: "\<lbrakk>cons(u,A) \<approx> cons(v,B);  u\<notin>A;  v\<notin>B\<rbrakk> \<Longrightarrow> A \<approx> B"
apply (simp add: eqpoll_iff)
apply (blast intro: cons_lepoll_consD)
done

(*Lemma suggested by Mike Fourman*)
lemma succ_lepoll_succD: "succ(m) \<lesssim> succ(n) \<Longrightarrow> m \<lesssim> n"
  unfolding succ_def
apply (erule cons_lepoll_consD)
apply (rule mem_not_refl)+
done


lemma nat_lepoll_imp_le:
     "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> m \<lesssim> n \<Longrightarrow> m \<le> n"
proof (induct m arbitrary: n rule: nat_induct)
  case 0 thus ?case by (blast intro!: nat_0_le)
next
  case (succ m)
  show ?case  using \<open>n \<in> nat\<close>
    proof (cases rule: natE)
      case 0 thus ?thesis using succ
        by (simp add: lepoll_def inj_def)
    next
      case (succ n') thus ?thesis using succ.hyps \<open> succ(m) \<lesssim> n\<close>
        by (blast intro!: succ_leI dest!: succ_lepoll_succD)
    qed
qed

lemma nat_eqpoll_iff: "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> m \<approx> n \<longleftrightarrow> m = n"
apply (rule iffI)
apply (blast intro: nat_lepoll_imp_le le_anti_sym elim!: eqpollE)
apply (simp add: eqpoll_refl)
done

(*The object of all this work: every natural number is a (finite) cardinal*)
lemma nat_into_Card:
  assumes n: "n \<in> nat" shows "Card(n)"
proof (unfold Card_def cardinal_def, rule sym)
  have "Ord(n)" using n  by auto
  moreover
  { fix i
    assume "i < n" "i \<approx> n"
    hence False using n
      by (auto simp add: lt_nat_in_nat [THEN nat_eqpoll_iff])
  }
  ultimately show "(\<mu> i. i \<approx> n) = n" by (auto intro!: Least_equality) 
qed

lemmas cardinal_0 = nat_0I [THEN nat_into_Card, THEN Card_cardinal_eq, iff]
lemmas cardinal_1 = nat_1I [THEN nat_into_Card, THEN Card_cardinal_eq, iff]


(*Part of Kunen's Lemma 10.6*)
lemma succ_lepoll_natE: "\<lbrakk>succ(n) \<lesssim> n;  n \<in> nat\<rbrakk> \<Longrightarrow> P"
by (rule nat_lepoll_imp_le [THEN lt_irrefl], auto)

lemma nat_lepoll_imp_ex_eqpoll_n:
     "\<lbrakk>n \<in> nat;  nat \<lesssim> X\<rbrakk> \<Longrightarrow> \<exists>Y. Y \<subseteq> X \<and> n \<approx> Y"
  unfolding lepoll_def eqpoll_def
apply (fast del: subsetI subsetCE
            intro!: subset_SIs
            dest!: Ord_nat [THEN [2] OrdmemD, THEN [2] restrict_inj]
            elim!: restrict_bij
                   inj_is_fun [THEN fun_is_rel, THEN image_subset])
done


(** \<lesssim>, \<prec> and natural numbers **)

lemma lepoll_succ: "i \<lesssim> succ(i)"
  by (blast intro: subset_imp_lepoll)

lemma lepoll_imp_lesspoll_succ:
  assumes A: "A \<lesssim> m" and m: "m \<in> nat"
  shows "A \<prec> succ(m)"
proof -
  { assume "A \<approx> succ(m)"
    hence "succ(m) \<approx> A" by (rule eqpoll_sym)
    also have "... \<lesssim> m" by (rule A)
    finally have "succ(m) \<lesssim> m" .
    hence False by (rule succ_lepoll_natE) (rule m) }
  moreover have "A \<lesssim> succ(m)" by (blast intro: lepoll_trans A lepoll_succ)
  ultimately show ?thesis by (auto simp add: lesspoll_def)
qed

lemma lesspoll_succ_imp_lepoll:
     "\<lbrakk>A \<prec> succ(m); m \<in> nat\<rbrakk> \<Longrightarrow> A \<lesssim> m"
  unfolding lesspoll_def lepoll_def eqpoll_def bij_def
apply (auto dest: inj_not_surj_succ)
done

lemma lesspoll_succ_iff: "m \<in> nat \<Longrightarrow> A \<prec> succ(m) \<longleftrightarrow> A \<lesssim> m"
by (blast intro!: lepoll_imp_lesspoll_succ lesspoll_succ_imp_lepoll)

lemma lepoll_succ_disj: "\<lbrakk>A \<lesssim> succ(m);  m \<in> nat\<rbrakk> \<Longrightarrow> A \<lesssim> m | A \<approx> succ(m)"
apply (rule disjCI)
apply (rule lesspoll_succ_imp_lepoll)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: lesspoll_def)
done

lemma lesspoll_cardinal_lt: "\<lbrakk>A \<prec> i; Ord(i)\<rbrakk> \<Longrightarrow> |A| < i"
apply (unfold lesspoll_def, clarify)
apply (frule lepoll_cardinal_le, assumption)
apply (blast intro: well_ord_Memrel well_ord_cardinal_eqpoll [THEN eqpoll_sym]
             dest: lepoll_well_ord  elim!: leE)
done


subsection\<open>The first infinite cardinal: Omega, or nat\<close>

(*This implies Kunen's Lemma 10.6*)
lemma lt_not_lepoll:
  assumes n: "n<i" "n \<in> nat" shows "\<not> i \<lesssim> n"
proof -
  { assume i: "i \<lesssim> n"
    have "succ(n) \<lesssim> i" using n
      by (elim ltE, blast intro: Ord_succ_subsetI [THEN subset_imp_lepoll])
    also have "... \<lesssim> n" by (rule i)
    finally have "succ(n) \<lesssim> n" .
    hence False  by (rule succ_lepoll_natE) (rule n) }
  thus ?thesis by auto
qed

text\<open>A slightly weaker version of \<open>nat_eqpoll_iff\<close>\<close>
lemma Ord_nat_eqpoll_iff:
  assumes i: "Ord(i)" and n: "n \<in> nat" shows "i \<approx> n \<longleftrightarrow> i=n"
using i nat_into_Ord [OF n]
proof (cases rule: Ord_linear_lt)
  case lt
  hence  "i \<in> nat" by (rule lt_nat_in_nat) (rule n)
  thus ?thesis by (simp add: nat_eqpoll_iff n)
next
  case eq
  thus ?thesis by (simp add: eqpoll_refl)
next
  case gt
  hence  "\<not> i \<lesssim> n" using n  by (rule lt_not_lepoll)
  hence  "\<not> i \<approx> n" using n  by (blast intro: eqpoll_imp_lepoll)
  moreover have "i \<noteq> n" using \<open>n<i\<close> by auto
  ultimately show ?thesis by blast
qed

lemma Card_nat: "Card(nat)"
proof -
  { fix i
    assume i: "i < nat" "i \<approx> nat"
    hence "\<not> nat \<lesssim> i"
      by (simp add: lt_def lt_not_lepoll)
    hence False using i
      by (simp add: eqpoll_iff)
  }
  hence "(\<mu> i. i \<approx> nat) = nat" by (blast intro: Least_equality eqpoll_refl)
  thus ?thesis
    by (auto simp add: Card_def cardinal_def)
qed

(*Allows showing that |i| is a limit cardinal*)
lemma nat_le_cardinal: "nat \<le> i \<Longrightarrow> nat \<le> |i|"
apply (rule Card_nat [THEN Card_cardinal_eq, THEN subst])
apply (erule cardinal_mono)
done

lemma n_lesspoll_nat: "n \<in> nat \<Longrightarrow> n \<prec> nat"
  by (blast intro: Ord_nat Card_nat ltI lt_Card_imp_lesspoll)


subsection\<open>Towards Cardinal Arithmetic\<close>
(** Congruence laws for successor, cardinal addition and multiplication **)

(*Congruence law for  cons  under equipollence*)
lemma cons_lepoll_cong:
    "\<lbrakk>A \<lesssim> B;  b \<notin> B\<rbrakk> \<Longrightarrow> cons(a,A) \<lesssim> cons(b,B)"
apply (unfold lepoll_def, safe)
apply (rule_tac x = "\<lambda>y\<in>cons (a,A) . if y=a then b else f`y" in exI)
apply (rule_tac d = "\<lambda>z. if z \<in> B then converse (f) `z else a" in lam_injective)
apply (safe elim!: consE')
   apply simp_all
apply (blast intro: inj_is_fun [THEN apply_type])+
done

lemma cons_eqpoll_cong:
     "\<lbrakk>A \<approx> B;  a \<notin> A;  b \<notin> B\<rbrakk> \<Longrightarrow> cons(a,A) \<approx> cons(b,B)"
by (simp add: eqpoll_iff cons_lepoll_cong)

lemma cons_lepoll_cons_iff:
     "\<lbrakk>a \<notin> A;  b \<notin> B\<rbrakk> \<Longrightarrow> cons(a,A) \<lesssim> cons(b,B)  \<longleftrightarrow>  A \<lesssim> B"
by (blast intro: cons_lepoll_cong cons_lepoll_consD)

lemma cons_eqpoll_cons_iff:
     "\<lbrakk>a \<notin> A;  b \<notin> B\<rbrakk> \<Longrightarrow> cons(a,A) \<approx> cons(b,B)  \<longleftrightarrow>  A \<approx> B"
by (blast intro: cons_eqpoll_cong cons_eqpoll_consD)

lemma singleton_eqpoll_1: "{a} \<approx> 1"
  unfolding succ_def
apply (blast intro!: eqpoll_refl [THEN cons_eqpoll_cong])
done

lemma cardinal_singleton: "|{a}| = 1"
apply (rule singleton_eqpoll_1 [THEN cardinal_cong, THEN trans])
apply (simp (no_asm) add: nat_into_Card [THEN Card_cardinal_eq])
done

lemma not_0_is_lepoll_1: "A \<noteq> 0 \<Longrightarrow> 1 \<lesssim> A"
apply (erule not_emptyE)
apply (rule_tac a = "cons (x, A-{x}) " in subst)
apply (rule_tac [2] a = "cons(0,0)" and P= "\<lambda>y. y \<lesssim> cons (x, A-{x})" in subst)
prefer 3 apply (blast intro: cons_lepoll_cong subset_imp_lepoll, auto)
done

(*Congruence law for  succ  under equipollence*)
lemma succ_eqpoll_cong: "A \<approx> B \<Longrightarrow> succ(A) \<approx> succ(B)"
  unfolding succ_def
apply (simp add: cons_eqpoll_cong mem_not_refl)
done

(*Congruence law for + under equipollence*)
lemma sum_eqpoll_cong: "\<lbrakk>A \<approx> C;  B \<approx> D\<rbrakk> \<Longrightarrow> A+B \<approx> C+D"
  unfolding eqpoll_def
apply (blast intro!: sum_bij)
done

(*Congruence law for * under equipollence*)
lemma prod_eqpoll_cong:
    "\<lbrakk>A \<approx> C;  B \<approx> D\<rbrakk> \<Longrightarrow> A*B \<approx> C*D"
  unfolding eqpoll_def
apply (blast intro!: prod_bij)
done

lemma inj_disjoint_eqpoll:
    "\<lbrakk>f \<in> inj(A,B);  A \<inter> B = 0\<rbrakk> \<Longrightarrow> A \<union> (B - range(f)) \<approx> B"
  unfolding eqpoll_def
apply (rule exI)
apply (rule_tac c = "\<lambda>x. if x \<in> A then f`x else x"
            and d = "\<lambda>y. if y \<in> range (f) then converse (f) `y else y"
       in lam_bijective)
apply (blast intro!: if_type inj_is_fun [THEN apply_type])
apply (simp (no_asm_simp) add: inj_converse_fun [THEN apply_funtype])
apply (safe elim!: UnE')
   apply (simp_all add: inj_is_fun [THEN apply_rangeI])
apply (blast intro: inj_converse_fun [THEN apply_type])+
done


subsection\<open>Lemmas by Krzysztof Grabczewski\<close>

(*New proofs using cons_lepoll_cons. Could generalise from succ to cons.*)

text\<open>If \<^term>\<open>A\<close> has at most \<^term>\<open>n+1\<close> elements and \<^term>\<open>a \<in> A\<close>
      then \<^term>\<open>A-{a}\<close> has at most \<^term>\<open>n\<close>.\<close>
lemma Diff_sing_lepoll:
      "\<lbrakk>a \<in> A;  A \<lesssim> succ(n)\<rbrakk> \<Longrightarrow> A - {a} \<lesssim> n"
  unfolding succ_def
apply (rule cons_lepoll_consD)
apply (rule_tac [3] mem_not_refl)
apply (erule cons_Diff [THEN ssubst], safe)
done

text\<open>If \<^term>\<open>A\<close> has at least \<^term>\<open>n+1\<close> elements then \<^term>\<open>A-{a}\<close> has at least \<^term>\<open>n\<close>.\<close>
lemma lepoll_Diff_sing:
  assumes A: "succ(n) \<lesssim> A" shows "n \<lesssim> A - {a}"
proof -
  have "cons(n,n) \<lesssim> A" using A
    by (unfold succ_def)
  also have "... \<lesssim> cons(a, A-{a})"
    by (blast intro: subset_imp_lepoll)
  finally have "cons(n,n) \<lesssim> cons(a, A-{a})" .
  thus ?thesis
    by (blast intro: cons_lepoll_consD mem_irrefl)
qed

lemma Diff_sing_eqpoll: "\<lbrakk>a \<in> A; A \<approx> succ(n)\<rbrakk> \<Longrightarrow> A - {a} \<approx> n"
by (blast intro!: eqpollI
          elim!: eqpollE
          intro: Diff_sing_lepoll lepoll_Diff_sing)

lemma lepoll_1_is_sing: "\<lbrakk>A \<lesssim> 1; a \<in> A\<rbrakk> \<Longrightarrow> A = {a}"
apply (frule Diff_sing_lepoll, assumption)
apply (drule lepoll_0_is_0)
apply (blast elim: equalityE)
done

lemma Un_lepoll_sum: "A \<union> B \<lesssim> A+B"
  unfolding lepoll_def
apply (rule_tac x = "\<lambda>x\<in>A \<union> B. if x\<in>A then Inl (x) else Inr (x)" in exI)
apply (rule_tac d = "\<lambda>z. snd (z)" in lam_injective)
apply force
apply (simp add: Inl_def Inr_def)
done

lemma well_ord_Un:
     "\<lbrakk>well_ord(X,R); well_ord(Y,S)\<rbrakk> \<Longrightarrow> \<exists>T. well_ord(X \<union> Y, T)"
by (erule well_ord_radd [THEN Un_lepoll_sum [THEN lepoll_well_ord]],
    assumption)

(*Krzysztof Grabczewski*)
lemma disj_Un_eqpoll_sum: "A \<inter> B = 0 \<Longrightarrow> A \<union> B \<approx> A + B"
  unfolding eqpoll_def
apply (rule_tac x = "\<lambda>a\<in>A \<union> B. if a \<in> A then Inl (a) else Inr (a)" in exI)
apply (rule_tac d = "\<lambda>z. case (\<lambda>x. x, \<lambda>x. x, z)" in lam_bijective)
apply auto
done


subsection \<open>Finite and infinite sets\<close>

lemma eqpoll_imp_Finite_iff: "A \<approx> B \<Longrightarrow> Finite(A) \<longleftrightarrow> Finite(B)"
  unfolding Finite_def
apply (blast intro: eqpoll_trans eqpoll_sym)
done

lemma Finite_0 [simp]: "Finite(0)"
  unfolding Finite_def
apply (blast intro!: eqpoll_refl nat_0I)
done

lemma Finite_cons: "Finite(x) \<Longrightarrow> Finite(cons(y,x))"
  unfolding Finite_def
apply (case_tac "y \<in> x")
apply (simp add: cons_absorb)
apply (erule bexE)
apply (rule bexI)
apply (erule_tac [2] nat_succI)
apply (simp (no_asm_simp) add: succ_def cons_eqpoll_cong mem_not_refl)
done

lemma Finite_succ: "Finite(x) \<Longrightarrow> Finite(succ(x))"
  unfolding succ_def
apply (erule Finite_cons)
done

lemma lepoll_nat_imp_Finite:
  assumes A: "A \<lesssim> n" and n: "n \<in> nat" shows "Finite(A)"
proof -
  have "A \<lesssim> n \<Longrightarrow> Finite(A)" using n
    proof (induct n)
      case 0
      hence "A = 0" by (rule lepoll_0_is_0) 
      thus ?case by simp
    next
      case (succ n)
      hence "A \<lesssim> n \<or> A \<approx> succ(n)" by (blast dest: lepoll_succ_disj)
      thus ?case using succ by (auto simp add: Finite_def) 
    qed
  thus ?thesis using A .
qed

lemma lesspoll_nat_is_Finite:
     "A \<prec> nat \<Longrightarrow> Finite(A)"
  unfolding Finite_def
apply (blast dest: ltD lesspoll_cardinal_lt
                   lesspoll_imp_eqpoll [THEN eqpoll_sym])
done

lemma lepoll_Finite:
  assumes Y: "Y \<lesssim> X" and X: "Finite(X)" shows "Finite(Y)"
proof -
  obtain n where n: "n \<in> nat" "X \<approx> n" using X
    by (auto simp add: Finite_def)
  have "Y \<lesssim> X"         by (rule Y)
  also have "... \<approx> n"  by (rule n)
  finally have "Y \<lesssim> n" .
  thus ?thesis using n by (simp add: lepoll_nat_imp_Finite)
qed

lemmas subset_Finite = subset_imp_lepoll [THEN lepoll_Finite]

lemma Finite_cons_iff [iff]: "Finite(cons(y,x)) \<longleftrightarrow> Finite(x)"
by (blast intro: Finite_cons subset_Finite)

lemma Finite_succ_iff [iff]: "Finite(succ(x)) \<longleftrightarrow> Finite(x)"
by (simp add: succ_def)

lemma Finite_Int: "Finite(A) | Finite(B) \<Longrightarrow> Finite(A \<inter> B)"
by (blast intro: subset_Finite)

lemmas Finite_Diff = Diff_subset [THEN subset_Finite]

lemma nat_le_infinite_Ord:
      "\<lbrakk>Ord(i);  \<not> Finite(i)\<rbrakk> \<Longrightarrow> nat \<le> i"
  unfolding Finite_def
apply (erule Ord_nat [THEN [2] Ord_linear2])
prefer 2 apply assumption
apply (blast intro!: eqpoll_refl elim!: ltE)
done

lemma Finite_imp_well_ord:
    "Finite(A) \<Longrightarrow> \<exists>r. well_ord(A,r)"
  unfolding Finite_def eqpoll_def
apply (blast intro: well_ord_rvimage bij_is_inj well_ord_Memrel nat_into_Ord)
done

lemma succ_lepoll_imp_not_empty: "succ(x) \<lesssim> y \<Longrightarrow> y \<noteq> 0"
by (fast dest!: lepoll_0_is_0)

lemma eqpoll_succ_imp_not_empty: "x \<approx> succ(n) \<Longrightarrow> x \<noteq> 0"
by (fast elim!: eqpoll_sym [THEN eqpoll_0_is_0, THEN succ_neq_0])

lemma Finite_Fin_lemma [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>A. (A\<approx>n \<and> A \<subseteq> X) \<longrightarrow> A \<in> Fin(X)"
apply (induct_tac n)
apply (rule allI)
apply (fast intro!: Fin.emptyI dest!: eqpoll_imp_lepoll [THEN lepoll_0_is_0])
apply (rule allI)
apply (rule impI)
apply (erule conjE)
apply (rule eqpoll_succ_imp_not_empty [THEN not_emptyE], assumption)
apply (frule Diff_sing_eqpoll, assumption)
apply (erule allE)
apply (erule impE, fast)
apply (drule subsetD, assumption)
apply (drule Fin.consI, assumption)
apply (simp add: cons_Diff)
done

lemma Finite_Fin: "\<lbrakk>Finite(A); A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<in> Fin(X)"
by (unfold Finite_def, blast intro: Finite_Fin_lemma)

lemma Fin_lemma [rule_format]: "n \<in> nat \<Longrightarrow> \<forall>A. A \<approx> n \<longrightarrow> A \<in> Fin(A)"
apply (induct_tac n)
apply (simp add: eqpoll_0_iff, clarify)
apply (subgoal_tac "\<exists>u. u \<in> A")
apply (erule exE)
apply (rule Diff_sing_eqpoll [elim_format])
prefer 2 apply assumption
apply assumption
apply (rule_tac b = A in cons_Diff [THEN subst], assumption)
apply (rule Fin.consI, blast)
apply (blast intro: subset_consI [THEN Fin_mono, THEN subsetD])
(*Now for the lemma assumed above*)
  unfolding eqpoll_def
apply (blast intro: bij_converse_bij [THEN bij_is_fun, THEN apply_type])
done

lemma Finite_into_Fin: "Finite(A) \<Longrightarrow> A \<in> Fin(A)"
  unfolding Finite_def
apply (blast intro: Fin_lemma)
done

lemma Fin_into_Finite: "A \<in> Fin(U) \<Longrightarrow> Finite(A)"
by (fast intro!: Finite_0 Finite_cons elim: Fin_induct)

lemma Finite_Fin_iff: "Finite(A) \<longleftrightarrow> A \<in> Fin(A)"
by (blast intro: Finite_into_Fin Fin_into_Finite)

lemma Finite_Un: "\<lbrakk>Finite(A); Finite(B)\<rbrakk> \<Longrightarrow> Finite(A \<union> B)"
by (blast intro!: Fin_into_Finite Fin_UnI
          dest!: Finite_into_Fin
          intro: Un_upper1 [THEN Fin_mono, THEN subsetD]
                 Un_upper2 [THEN Fin_mono, THEN subsetD])

lemma Finite_Un_iff [simp]: "Finite(A \<union> B) \<longleftrightarrow> (Finite(A) \<and> Finite(B))"
by (blast intro: subset_Finite Finite_Un)

text\<open>The converse must hold too.\<close>
lemma Finite_Union: "\<lbrakk>\<forall>y\<in>X. Finite(y);  Finite(X)\<rbrakk> \<Longrightarrow> Finite(\<Union>(X))"
apply (simp add: Finite_Fin_iff)
apply (rule Fin_UnionI)
apply (erule Fin_induct, simp)
apply (blast intro: Fin.consI Fin_mono [THEN [2] rev_subsetD])
done

(* Induction principle for Finite(A), by Sidi Ehmety *)
lemma Finite_induct [case_names 0 cons, induct set: Finite]:
"\<lbrakk>Finite(A); P(0);
    \<And>x B.   \<lbrakk>Finite(B); x \<notin> B; P(B)\<rbrakk> \<Longrightarrow> P(cons(x, B))\<rbrakk>
 \<Longrightarrow> P(A)"
apply (erule Finite_into_Fin [THEN Fin_induct])
apply (blast intro: Fin_into_Finite)+
done

(*Sidi Ehmety.  The contrapositive says \<not>Finite(A) \<Longrightarrow> \<not>Finite(A-{a}) *)
lemma Diff_sing_Finite: "Finite(A - {a}) \<Longrightarrow> Finite(A)"
  unfolding Finite_def
apply (case_tac "a \<in> A")
apply (subgoal_tac [2] "A-{a}=A", auto)
apply (rule_tac x = "succ (n) " in bexI)
apply (subgoal_tac "cons (a, A - {a}) = A \<and> cons (n, n) = succ (n) ")
apply (drule_tac a = a and b = n in cons_eqpoll_cong)
apply (auto dest: mem_irrefl)
done

(*Sidi Ehmety.  And the contrapositive of this says
   \<lbrakk>\<not>Finite(A); Finite(B)\<rbrakk> \<Longrightarrow> \<not>Finite(A-B) *)
lemma Diff_Finite [rule_format]: "Finite(B) \<Longrightarrow> Finite(A-B) \<longrightarrow> Finite(A)"
apply (erule Finite_induct, auto)
apply (case_tac "x \<in> A")
 apply (subgoal_tac [2] "A-cons (x, B) = A - B")
apply (subgoal_tac "A - cons (x, B) = (A - B) - {x}", simp)
apply (drule Diff_sing_Finite, auto)
done

lemma Finite_RepFun: "Finite(A) \<Longrightarrow> Finite(RepFun(A,f))"
by (erule Finite_induct, simp_all)

lemma Finite_RepFun_iff_lemma [rule_format]:
     "\<lbrakk>Finite(x); \<And>x y. f(x)=f(y) \<Longrightarrow> x=y\<rbrakk>
      \<Longrightarrow> \<forall>A. x = RepFun(A,f) \<longrightarrow> Finite(A)"
apply (erule Finite_induct)
 apply clarify
 apply (case_tac "A=0", simp)
 apply (blast del: allE, clarify)
apply (subgoal_tac "\<exists>z\<in>A. x = f(z)")
 prefer 2 apply (blast del: allE elim: equalityE, clarify)
apply (subgoal_tac "B = {f(u) . u \<in> A - {z}}")
 apply (blast intro: Diff_sing_Finite)
apply (thin_tac "\<forall>A. P(A) \<longrightarrow> Finite(A)" for P)
apply (rule equalityI)
 apply (blast intro: elim: equalityE)
apply (blast intro: elim: equalityCE)
done

text\<open>I don't know why, but if the premise is expressed using meta-connectives
then  the simplifier cannot prove it automatically in conditional rewriting.\<close>
lemma Finite_RepFun_iff:
     "(\<forall>x y. f(x)=f(y) \<longrightarrow> x=y) \<Longrightarrow> Finite(RepFun(A,f)) \<longleftrightarrow> Finite(A)"
by (blast intro: Finite_RepFun Finite_RepFun_iff_lemma [of _ f])

lemma Finite_Pow: "Finite(A) \<Longrightarrow> Finite(Pow(A))"
apply (erule Finite_induct)
apply (simp_all add: Pow_insert Finite_Un Finite_RepFun)
done

lemma Finite_Pow_imp_Finite: "Finite(Pow(A)) \<Longrightarrow> Finite(A)"
apply (subgoal_tac "Finite({{x} . x \<in> A})")
 apply (simp add: Finite_RepFun_iff )
apply (blast intro: subset_Finite)
done

lemma Finite_Pow_iff [iff]: "Finite(Pow(A)) \<longleftrightarrow> Finite(A)"
by (blast intro: Finite_Pow Finite_Pow_imp_Finite)

lemma Finite_cardinal_iff:
  assumes i: "Ord(i)" shows "Finite(|i|) \<longleftrightarrow> Finite(i)"
  by (auto simp add: Finite_def) (blast intro: eqpoll_trans eqpoll_sym Ord_cardinal_eqpoll [OF i])+


(*Krzysztof Grabczewski's proof that the converse of a finite, well-ordered
  set is well-ordered.  Proofs simplified by lcp. *)

lemma nat_wf_on_converse_Memrel: "n \<in> nat \<Longrightarrow> wf[n](converse(Memrel(n)))"
proof (induct n rule: nat_induct)
  case 0 thus ?case by (blast intro: wf_onI)
next
  case (succ x)
  hence wfx: "\<And>Z. Z = 0 \<or> (\<exists>z\<in>Z. \<forall>y. z \<in> y \<and> z \<in> x \<and> y \<in> x \<and> z \<in> x \<longrightarrow> y \<notin> Z)"
    by (simp add: wf_on_def wf_def)  \<comment> \<open>not easy to erase the duplicate \<^term>\<open>z \<in> x\<close>!\<close>
  show ?case
    proof (rule wf_onI)
      fix Z u
      assume Z: "u \<in> Z" "\<forall>z\<in>Z. \<exists>y\<in>Z. \<langle>y, z\<rangle> \<in> converse(Memrel(succ(x)))"
      show False 
        proof (cases "x \<in> Z")
          case True thus False using Z
            by (blast elim: mem_irrefl mem_asym)
          next
          case False thus False using wfx [of Z] Z
            by blast
        qed
    qed
qed

lemma nat_well_ord_converse_Memrel: "n \<in> nat \<Longrightarrow> well_ord(n,converse(Memrel(n)))"
apply (frule Ord_nat [THEN Ord_in_Ord, THEN well_ord_Memrel])
apply (simp add: well_ord_def tot_ord_converse nat_wf_on_converse_Memrel) 
done

lemma well_ord_converse:
     "\<lbrakk>well_ord(A,r);
        well_ord(ordertype(A,r), converse(Memrel(ordertype(A, r))))\<rbrakk>
      \<Longrightarrow> well_ord(A,converse(r))"
apply (rule well_ord_Int_iff [THEN iffD1])
apply (frule ordermap_bij [THEN bij_is_inj, THEN well_ord_rvimage], assumption)
apply (simp add: rvimage_converse converse_Int converse_prod
                 ordertype_ord_iso [THEN ord_iso_rvimage_eq])
done

lemma ordertype_eq_n:
  assumes r: "well_ord(A,r)" and A: "A \<approx> n" and n: "n \<in> nat"
  shows "ordertype(A,r) = n"
proof -
  have "ordertype(A,r) \<approx> A"
    by (blast intro: bij_imp_eqpoll bij_converse_bij ordermap_bij r)
  also have "... \<approx> n" by (rule A)
  finally have "ordertype(A,r) \<approx> n" .
  thus ?thesis
    by (simp add: Ord_nat_eqpoll_iff Ord_ordertype n r)
qed

lemma Finite_well_ord_converse:
    "\<lbrakk>Finite(A);  well_ord(A,r)\<rbrakk> \<Longrightarrow> well_ord(A,converse(r))"
  unfolding Finite_def
apply (rule well_ord_converse, assumption)
apply (blast dest: ordertype_eq_n intro!: nat_well_ord_converse_Memrel)
done

lemma nat_into_Finite: "n \<in> nat \<Longrightarrow> Finite(n)"
  by (auto simp add: Finite_def intro: eqpoll_refl) 

lemma nat_not_Finite: "\<not> Finite(nat)"
proof -
  { fix n
    assume n: "n \<in> nat" "nat \<approx> n"
    have "n \<in> nat"    by (rule n)
    also have "... = n" using n
      by (simp add: Ord_nat_eqpoll_iff Ord_nat)
    finally have "n \<in> n" .
    hence False
      by (blast elim: mem_irrefl)
  }
  thus ?thesis
    by (auto simp add: Finite_def)
qed

end
