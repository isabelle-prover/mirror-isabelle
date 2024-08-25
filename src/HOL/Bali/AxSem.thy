(*  Title:      HOL/Bali/AxSem.thy
    Author:     David von Oheimb
*)

subsection \<open>Axiomatic semantics of Java expressions and statements 
          (see also Eval.thy)
\<close>
theory AxSem imports Evaln TypeSafe begin

text \<open>
design issues:
\begin{itemize}
\item a strong version of validity for triples with premises, namely one that 
      takes the recursive depth needed to complete execution, enables 
      correctness proof
\item auxiliary variables are handled first-class (-> Thomas Kleymann)
\item expressions not flattened to elementary assignments (as usual for 
      axiomatic semantics) but treated first-class => explicit result value 
      handling
\item intermediate values not on triple, but on assertion level 
      (with result entry)
\item multiple results with semantical substitution mechnism not requiring a 
      stack 
\item because of dynamic method binding, terms need to be dependent on state.
  this is also useful for conditional expressions and statements
\item result values in triples exactly as in eval relation (also for xcpt 
      states)
\item validity: additional assumption of state conformance and well-typedness,
  which is required for soundness and thus rule hazard required of completeness
\end{itemize}

restrictions:
\begin{itemize}
\item all triples in a derivation are of the same type (due to weak 
      polymorphism)
\end{itemize}
\<close>

type_synonym  res = vals \<comment> \<open>result entry\<close>

abbreviation (input)
  Val where "Val x == In1 x"

abbreviation (input)
  Var where "Var x == In2 x"

abbreviation (input)
  Vals where "Vals x == In3 x"

syntax
  "_Val"    :: "[pttrn] => pttrn"     ("Val:_"  [951] 950)
  "_Var"    :: "[pttrn] => pttrn"     ("Var:_"  [951] 950)
  "_Vals"   :: "[pttrn] => pttrn"     ("Vals:_" [951] 950)

translations
  "\<lambda>Val:v . b"  == "(\<lambda>v. b) \<circ> CONST the_In1"
  "\<lambda>Var:v . b"  == "(\<lambda>v. b) \<circ> CONST the_In2"
  "\<lambda>Vals:v. b"  == "(\<lambda>v. b) \<circ> CONST the_In3"

  \<comment> \<open>relation on result values, state and auxiliary variables\<close>
type_synonym 'a assn = "res \<Rightarrow> state \<Rightarrow> 'a \<Rightarrow> bool"
translations
  (type) "'a assn" <= (type) "vals \<Rightarrow> state \<Rightarrow> 'a \<Rightarrow> bool"

definition
  assn_imp :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> bool" (infixr "\<Rightarrow>" 25)
  where "(P \<Rightarrow> Q) = (\<forall>Y s Z. P Y s Z \<longrightarrow> Q Y s Z)"
  
lemma assn_imp_def2 [iff]: "(P \<Rightarrow> Q) = (\<forall>Y s Z. P Y s Z \<longrightarrow> Q Y s Z)"
apply (unfold assn_imp_def)
apply (rule HOL.refl)
done


subsubsection "assertion transformers"

subsection "peek-and"

definition
  peek_and :: "'a assn \<Rightarrow> (state \<Rightarrow>  bool) \<Rightarrow> 'a assn" (infixl "\<and>." 13)
  where "(P \<and>. p) = (\<lambda>Y s Z. P Y s Z \<and> p s)"

lemma peek_and_def2 [simp]: "peek_and P p Y s = (\<lambda>Z. (P Y s Z \<and> p s))"
apply (unfold peek_and_def)
apply (simp (no_asm))
done

lemma peek_and_Not [simp]: "(P \<and>. (\<lambda>s. \<not> f s)) = (P \<and>. Not \<circ> f)"
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_and_and [simp]: "peek_and (peek_and P p) p = peek_and P p"
apply (unfold peek_and_def)
apply (simp (no_asm))
done

lemma peek_and_commut: "(P \<and>. p \<and>. q) = (P \<and>. q \<and>. p)"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply auto
done

abbreviation
  Normal :: "'a assn \<Rightarrow> 'a assn"
  where "Normal P == P \<and>. normal"

lemma peek_and_Normal [simp]: "peek_and (Normal P) p = Normal (peek_and P p)"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply auto
done

subsection "assn-supd"

definition
  assn_supd :: "'a assn \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> 'a assn" (infixl ";." 13)
  where "(P ;. f) = (\<lambda>Y s' Z. \<exists>s. P Y s Z \<and> s' = f s)"

lemma assn_supd_def2 [simp]: "assn_supd P f Y s' Z = (\<exists>s. P Y s Z \<and> s' = f s)"
apply (unfold assn_supd_def)
apply (simp (no_asm))
done

subsection "supd-assn"

definition
  supd_assn :: "(state \<Rightarrow> state) \<Rightarrow> 'a assn \<Rightarrow> 'a assn" (infixr ".;" 13)
  where "(f .; P) = (\<lambda>Y s. P Y (f s))"


lemma supd_assn_def2 [simp]: "(f .; P) Y s = P Y (f s)"
apply (unfold supd_assn_def)
apply (simp (no_asm))
done

lemma supd_assn_supdD [elim]: "((f .; Q) ;. f) Y s Z \<Longrightarrow> Q Y s Z"
apply auto
done

lemma supd_assn_supdI [elim]: "Q Y s Z \<Longrightarrow> (f .; (Q ;. f)) Y s Z"
apply (auto simp del: split_paired_Ex)
done

subsection "subst-res"

definition
  subst_res :: "'a assn \<Rightarrow> res \<Rightarrow> 'a assn" ("_\<leftarrow>_"  [60,61] 60)
  where "P\<leftarrow>w = (\<lambda>Y. P w)"

lemma subst_res_def2 [simp]: "(P\<leftarrow>w) Y = P w"
apply (unfold subst_res_def)
apply (simp (no_asm))
done

lemma subst_subst_res [simp]: "P\<leftarrow>w\<leftarrow>v = P\<leftarrow>w"
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_and_subst_res [simp]: "(P \<and>. p)\<leftarrow>w = (P\<leftarrow>w \<and>. p)"
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

(*###Do not work for some strange (unification?) reason
lemma subst_res_Val_beta [simp]: "(\<lambda>Y. P (the_In1 Y))\<leftarrow>Val v = (\<lambda>Y. P v)"
apply (rule ext)
by simp

lemma subst_res_Var_beta [simp]: "(\<lambda>Y. P (the_In2 Y))\<leftarrow>Var vf = (\<lambda>Y. P vf)";
apply (rule ext)
by simp

lemma subst_res_Vals_beta [simp]: "(\<lambda>Y. P (the_In3 Y))\<leftarrow>Vals vs = (\<lambda>Y. P vs)";
apply (rule ext)
by simp
*)

subsection "subst-Bool"

definition
  subst_Bool :: "'a assn \<Rightarrow> bool \<Rightarrow> 'a assn" ("_\<leftarrow>=_" [60,61] 60)
  where "P\<leftarrow>=b = (\<lambda>Y s Z. \<exists>v. P (Val v) s Z \<and> (normal s \<longrightarrow> the_Bool v=b))"

lemma subst_Bool_def2 [simp]: 
"(P\<leftarrow>=b) Y s Z = (\<exists>v. P (Val v) s Z \<and> (normal s \<longrightarrow> the_Bool v=b))"
apply (unfold subst_Bool_def)
apply (simp (no_asm))
done

lemma subst_Bool_the_BoolI: "P (Val b) s Z \<Longrightarrow> (P\<leftarrow>=the_Bool b) Y s Z"
apply auto
done

subsection "peek-res"

definition
  peek_res :: "(res \<Rightarrow> 'a assn) \<Rightarrow> 'a assn"
  where "peek_res Pf = (\<lambda>Y. Pf Y Y)"

syntax
  "_peek_res" :: "pttrn \<Rightarrow> 'a assn \<Rightarrow> 'a assn"            ("\<lambda>_:. _" [0,3] 3)
syntax_consts
  "_peek_res" == peek_res
translations
  "\<lambda>w:. P"   == "CONST peek_res (\<lambda>w. P)"

lemma peek_res_def2 [simp]: "peek_res P Y = P Y Y"
apply (unfold peek_res_def)
apply (simp (no_asm))
done

lemma peek_res_subst_res [simp]: "peek_res P\<leftarrow>w = P w\<leftarrow>w"
apply (rule ext)
apply (simp (no_asm))
done

(* unused *)
lemma peek_subst_res_allI: 
 "(\<And>a. T a (P (f a)\<leftarrow>f a)) \<Longrightarrow> \<forall>a. T a (peek_res P\<leftarrow>f a)"
apply (rule allI)
apply (simp (no_asm))
apply fast
done

subsection "ign-res"

definition
  ign_res :: "'a assn \<Rightarrow> 'a assn" ("_\<down>" [1000] 1000)
  where "P\<down> = (\<lambda>Y s Z. \<exists>Y. P Y s Z)"

lemma ign_res_def2 [simp]: "P\<down> Y s Z = (\<exists>Y. P Y s Z)"
apply (unfold ign_res_def)
apply (simp (no_asm))
done

lemma ign_ign_res [simp]: "P\<down>\<down> = P\<down>"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

lemma ign_subst_res [simp]: "P\<down>\<leftarrow>w = P\<down>"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_and_ign_res [simp]: "(P \<and>. p)\<down> = (P\<down> \<and>. p)"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

subsection "peek-st"

definition
  peek_st :: "(st \<Rightarrow> 'a assn) \<Rightarrow> 'a assn"
  where "peek_st P = (\<lambda>Y s. P (store s) Y s)"

syntax
  "_peek_st"   :: "pttrn \<Rightarrow> 'a assn \<Rightarrow> 'a assn"            ("\<lambda>_.. _" [0,3] 3)
syntax_consts
  "_peek_st" == peek_st
translations
  "\<lambda>s.. P"   == "CONST peek_st (\<lambda>s. P)"

lemma peek_st_def2 [simp]: "(\<lambda>s.. Pf s) Y s = Pf (store s) Y s"
apply (unfold peek_st_def)
apply (simp (no_asm))
done

lemma peek_st_triv [simp]: "(\<lambda>s.. P) = P"
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_st_st [simp]: "(\<lambda>s.. \<lambda>s'.. P s s') = (\<lambda>s.. P s s)"
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_st_split [simp]: "(\<lambda>s.. \<lambda>Y s'. P s Y s') = (\<lambda>Y s. P (store s) Y s)"
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_st_subst_res [simp]: "(\<lambda>s.. P s)\<leftarrow>w = (\<lambda>s.. P s\<leftarrow>w)"
apply (rule ext)
apply (simp (no_asm))
done

lemma peek_st_Normal [simp]: "(\<lambda>s..(Normal (P s))) = Normal (\<lambda>s.. P s)"
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

subsection "ign-res-eq"

definition
  ign_res_eq :: "'a assn \<Rightarrow> res \<Rightarrow> 'a assn" ("_\<down>=_"  [60,61] 60)
  where "P\<down>=w \<equiv> (\<lambda>Y:. P\<down> \<and>. (\<lambda>s. Y=w))"

lemma ign_res_eq_def2 [simp]: "(P\<down>=w) Y s Z = ((\<exists>Y. P Y s Z) \<and> Y=w)"
apply (unfold ign_res_eq_def)
apply auto
done

lemma ign_ign_res_eq [simp]: "(P\<down>=w)\<down> = P\<down>"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

(* unused *)
lemma ign_res_eq_subst_res: "P\<down>=w\<leftarrow>w = P\<down>"
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply (simp (no_asm))
done

(* unused *)
lemma subst_Bool_ign_res_eq: "((P\<leftarrow>=b)\<down>=x) Y s Z = ((P\<leftarrow>=b) Y s Z  \<and> Y=x)"
apply (simp (no_asm))
done

subsection "RefVar"

definition
  RefVar :: "(state \<Rightarrow> vvar \<times> state) \<Rightarrow> 'a assn \<Rightarrow> 'a assn" (infixr "..;" 13)
  where "(vf ..; P) = (\<lambda>Y s. let (v,s') = vf s in P (Var v) s')"
 
lemma RefVar_def2 [simp]: "(vf ..; P) Y s =  
  P (Var (fst (vf s))) (snd (vf s))"
apply (unfold RefVar_def Let_def)
apply (simp (no_asm) add: split_beta)
done

subsection "allocation"

definition
  Alloc :: "prog \<Rightarrow> obj_tag \<Rightarrow> 'a assn \<Rightarrow> 'a assn"
  where "Alloc G otag P = (\<lambda>Y s Z. \<forall>s' a. G\<turnstile>s \<midarrow>halloc otag\<succ>a\<rightarrow> s'\<longrightarrow> P (Val (Addr a)) s' Z)"

definition
  SXAlloc :: "prog \<Rightarrow> 'a assn \<Rightarrow> 'a assn"
  where "SXAlloc G P = (\<lambda>Y s Z. \<forall>s'. G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s' \<longrightarrow> P Y s' Z)"


lemma Alloc_def2 [simp]: "Alloc G otag P Y s Z =  
       (\<forall>s' a. G\<turnstile>s \<midarrow>halloc otag\<succ>a\<rightarrow> s'\<longrightarrow> P (Val (Addr a)) s' Z)"
apply (unfold Alloc_def)
apply (simp (no_asm))
done

lemma SXAlloc_def2 [simp]: 
  "SXAlloc G P Y s Z = (\<forall>s'. G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s' \<longrightarrow> P Y s' Z)"
apply (unfold SXAlloc_def)
apply (simp (no_asm))
done

subsubsection "validity"

definition
  type_ok :: "prog \<Rightarrow> term \<Rightarrow> state \<Rightarrow> bool" where
  "type_ok G t s =
    (\<exists>L T C A. (normal s \<longrightarrow> \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T \<and> 
                             \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>A )
               \<and> s\<Colon>\<preceq>(G,L))"

datatype    'a triple = triple "('a assn)" "term" "('a assn)" (** should be
something like triple = \<forall>'a. triple ('a assn) term ('a assn)   **)
                                        ("{(1_)}/ _\<succ>/ {(1_)}"     [3,65,3] 75)
type_synonym 'a triples = "'a triple set"

abbreviation
  var_triple   :: "['a assn, var         ,'a assn] \<Rightarrow> 'a triple"
                                         ("{(1_)}/ _=\<succ>/ {(1_)}"    [3,80,3] 75)
  where "{P} e=\<succ> {Q} == {P} In2 e\<succ> {Q}"

abbreviation
  expr_triple  :: "['a assn, expr        ,'a assn] \<Rightarrow> 'a triple"
                                         ("{(1_)}/ _-\<succ>/ {(1_)}"    [3,80,3] 75)
  where "{P} e-\<succ> {Q} == {P} In1l e\<succ> {Q}"

abbreviation
  exprs_triple :: "['a assn, expr list   ,'a assn] \<Rightarrow> 'a triple"
                                         ("{(1_)}/ _\<doteq>\<succ>/ {(1_)}"    [3,65,3] 75)
  where "{P} e\<doteq>\<succ> {Q} == {P} In3 e\<succ> {Q}"

abbreviation
  stmt_triple  :: "['a assn, stmt,        'a assn] \<Rightarrow> 'a triple"
                                         ("{(1_)}/ ._./ {(1_)}"     [3,65,3] 75)
  where "{P} .c. {Q} == {P} In1r c\<succ> {Q}"

notation (ASCII)
  triple  ("{(1_)}/ _>/ {(1_)}"      [3,65,3]75) and
  var_triple  ("{(1_)}/ _=>/ {(1_)}"    [3,80,3] 75) and
  expr_triple  ("{(1_)}/ _->/ {(1_)}"    [3,80,3] 75) and
  exprs_triple  ("{(1_)}/ _#>/ {(1_)}"    [3,65,3] 75)

lemma inj_triple: "inj (\<lambda>(P,t,Q). {P} t\<succ> {Q})"
apply (rule inj_onI)
apply auto
done

lemma triple_inj_eq: "({P} t\<succ> {Q} = {P'} t'\<succ> {Q'} ) = (P=P' \<and> t=t' \<and> Q=Q')"
apply auto
done

definition mtriples :: "('c \<Rightarrow> 'sig \<Rightarrow> 'a assn) \<Rightarrow> ('c \<Rightarrow> 'sig \<Rightarrow> expr) \<Rightarrow> 
                ('c \<Rightarrow> 'sig \<Rightarrow> 'a assn) \<Rightarrow> ('c \<times>  'sig) set \<Rightarrow> 'a triples" ("{{(1_)}/ _-\<succ>/ {(1_)} | _}"[3,65,3,65]75) where
 "{{P} tf-\<succ> {Q} | ms} = (\<lambda>(C,sig). {Normal(P C sig)} tf C sig-\<succ> {Q C sig})`ms"
  
definition
  triple_valid :: "prog \<Rightarrow> nat \<Rightarrow> 'a triple  \<Rightarrow> bool"  ("_\<Turnstile>_:_" [61,0, 58] 57)
  where
    "G\<Turnstile>n:t =
      (case t of {P} t\<succ> {Q} \<Rightarrow>
        \<forall>Y s Z. P Y s Z \<longrightarrow> type_ok G t s \<longrightarrow>
        (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s') \<longrightarrow> Q Y' s' Z))"

abbreviation
  triples_valid:: "prog \<Rightarrow> nat \<Rightarrow> 'a triples \<Rightarrow> bool"  ("_|\<Turnstile>_:_" [61,0, 58] 57)
  where "G|\<Turnstile>n:ts == Ball ts (triple_valid G n)"

notation (ASCII)
  triples_valid  (  "_||=_:_" [61,0, 58] 57)


definition
  ax_valids :: "prog \<Rightarrow> 'b triples \<Rightarrow> 'a triples \<Rightarrow> bool"  ("_,_|\<Turnstile>_" [61,58,58] 57)
  where "(G,A|\<Turnstile>ts) = (\<forall>n. G|\<Turnstile>n:A \<longrightarrow> G|\<Turnstile>n:ts)"

abbreviation
  ax_valid :: "prog \<Rightarrow> 'b triples \<Rightarrow> 'a triple \<Rightarrow> bool"  ("_,_\<Turnstile>_" [61,58,58] 57)
  where "G,A \<Turnstile>t == G,A|\<Turnstile>{t}"

notation (ASCII)
  ax_valid  ( "_,_|=_"   [61,58,58] 57)


lemma triple_valid_def2: "G\<Turnstile>n:{P} t\<succ> {Q} =  
 (\<forall>Y s Z. P Y s Z 
  \<longrightarrow> (\<exists>L. (normal s \<longrightarrow> (\<exists> C T A. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T \<and> 
                   \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>A)) \<and> 
           s\<Colon>\<preceq>(G,L))
  \<longrightarrow> (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s')\<longrightarrow> Q Y' s' Z))"
apply (unfold triple_valid_def type_ok_def)
apply (simp (no_asm))
done


declare split_paired_All [simp del] split_paired_Ex [simp del] 
declare if_split     [split del] if_split_asm     [split del] 
        option.split [split del] option.split_asm [split del]
setup \<open>map_theory_simpset (fn ctxt => ctxt delloop "split_all_tac")\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

inductive
  ax_derivs :: "prog \<Rightarrow> 'a triples \<Rightarrow> 'a triples \<Rightarrow> bool" ("_,_|\<turnstile>_" [61,58,58] 57)
  and ax_deriv :: "prog \<Rightarrow> 'a triples \<Rightarrow> 'a triple  \<Rightarrow> bool" ("_,_\<turnstile>_" [61,58,58] 57)
  for G :: prog
where

  "G,A \<turnstile>t \<equiv> G,A|\<turnstile>{t}"

| empty: " G,A|\<turnstile>{}"
| insert:"\<lbrakk>G,A\<turnstile>t; G,A|\<turnstile>ts\<rbrakk> \<Longrightarrow>
          G,A|\<turnstile>insert t ts"

| asm:   "ts\<subseteq>A \<Longrightarrow> G,A|\<turnstile>ts"

(* could be added for convenience and efficiency, but is not necessary
  cut:   "\<lbrakk>G,A'|\<turnstile>ts; G,A|\<turnstile>A'\<rbrakk> \<Longrightarrow>
           G,A |\<turnstile>ts"
*)
| weaken:"\<lbrakk>G,A|\<turnstile>ts'; ts \<subseteq> ts'\<rbrakk> \<Longrightarrow> G,A|\<turnstile>ts"

| conseq:"\<forall>Y s Z . P  Y s Z  \<longrightarrow> (\<exists>P' Q'. G,A\<turnstile>{P'} t\<succ> {Q'} \<and> (\<forall>Y' s'. 
         (\<forall>Y   Z'. P' Y s Z' \<longrightarrow> Q' Y' s' Z') \<longrightarrow>
                                 Q  Y' s' Z ))
                                         \<Longrightarrow> G,A\<turnstile>{P } t\<succ> {Q }"

| hazard:"G,A\<turnstile>{P \<and>. Not \<circ> type_ok G t} t\<succ> {Q}"

| Abrupt:  "G,A\<turnstile>{P\<leftarrow>(undefined3 t) \<and>. Not \<circ> normal} t\<succ> {P}"

  \<comment> \<open>variables\<close>
| LVar:  " G,A\<turnstile>{Normal (\<lambda>s.. P\<leftarrow>Var (lvar vn s))} LVar vn=\<succ> {P}"

| FVar: "\<lbrakk>G,A\<turnstile>{Normal P} .Init C. {Q};
          G,A\<turnstile>{Q} e-\<succ> {\<lambda>Val:a:. fvar C stat fn a ..; R}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} {accC,C,stat}e..fn=\<succ> {R}"

| AVar:  "\<lbrakk>G,A\<turnstile>{Normal P} e1-\<succ> {Q};
          \<forall>a. G,A\<turnstile>{Q\<leftarrow>Val a} e2-\<succ> {\<lambda>Val:i:. avar G i a ..; R}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} e1.[e2]=\<succ> {R}"
  \<comment> \<open>expressions\<close>

| NewC: "\<lbrakk>G,A\<turnstile>{Normal P} .Init C. {Alloc G (CInst C) Q}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} NewC C-\<succ> {Q}"

| NewA: "\<lbrakk>G,A\<turnstile>{Normal P} .init_comp_ty T. {Q};  G,A\<turnstile>{Q} e-\<succ>
          {\<lambda>Val:i:. abupd (check_neg i) .; Alloc G (Arr T (the_Intg i)) R}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} New T[e]-\<succ> {R}"

| Cast: "\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {\<lambda>Val:v:. \<lambda>s..
          abupd (raise_if (\<not>G,s\<turnstile>v fits T) ClassCast) .; Q\<leftarrow>Val v}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} Cast T e-\<succ> {Q}"

| Inst: "\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {\<lambda>Val:v:. \<lambda>s..
                  Q\<leftarrow>Val (Bool (v\<noteq>Null \<and> G,s\<turnstile>v fits RefT T))}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} e InstOf T-\<succ> {Q}"

| Lit:                          "G,A\<turnstile>{Normal (P\<leftarrow>Val v)} Lit v-\<succ> {P}"

| UnOp: "\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {\<lambda>Val:v:. Q\<leftarrow>Val (eval_unop unop v)}\<rbrakk>
          \<Longrightarrow>
          G,A\<turnstile>{Normal P} UnOp unop e-\<succ> {Q}"

| BinOp:
   "\<lbrakk>G,A\<turnstile>{Normal P} e1-\<succ> {Q};
     \<forall>v1. G,A\<turnstile>{Q\<leftarrow>Val v1} 
               (if need_second_arg binop v1 then (In1l e2) else (In1r Skip))\<succ>
               {\<lambda>Val:v2:. R\<leftarrow>Val (eval_binop binop v1 v2)}\<rbrakk>
    \<Longrightarrow>
    G,A\<turnstile>{Normal P} BinOp binop e1 e2-\<succ> {R}" 

| Super:" G,A\<turnstile>{Normal (\<lambda>s.. P\<leftarrow>Val (val_this s))} Super-\<succ> {P}"

| Acc:  "\<lbrakk>G,A\<turnstile>{Normal P} va=\<succ> {\<lambda>Var:(v,f):. Q\<leftarrow>Val v}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} Acc va-\<succ> {Q}"

| Ass:  "\<lbrakk>G,A\<turnstile>{Normal P} va=\<succ> {Q};
     \<forall>vf. G,A\<turnstile>{Q\<leftarrow>Var vf} e-\<succ> {\<lambda>Val:v:. assign (snd vf) v .; R}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} va:=e-\<succ> {R}"

| Cond: "\<lbrakk>G,A \<turnstile>{Normal P} e0-\<succ> {P'};
          \<forall>b. G,A\<turnstile>{P'\<leftarrow>=b} (if b then e1 else e2)-\<succ> {Q}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} e0 ? e1 : e2-\<succ> {Q}"

| Call: 
"\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {Q}; \<forall>a. G,A\<turnstile>{Q\<leftarrow>Val a} args\<doteq>\<succ> {R a};
  \<forall>a vs invC declC l. G,A\<turnstile>{(R a\<leftarrow>Vals vs \<and>.
 (\<lambda>s. declC=invocation_declclass G mode (store s) a statT \<lparr>name=mn,parTs=pTs\<rparr> \<and>
      invC = invocation_class mode (store s) a statT \<and>
         l = locals (store s)) ;.
      init_lvars G declC \<lparr>name=mn,parTs=pTs\<rparr> mode a vs) \<and>.
      (\<lambda>s. normal s \<longrightarrow> G\<turnstile>mode\<rightarrow>invC\<preceq>statT)}
 Methd declC \<lparr>name=mn,parTs=pTs\<rparr>-\<succ> {set_lvars l .; S}\<rbrakk> \<Longrightarrow>
         G,A\<turnstile>{Normal P} {accC,statT,mode}e\<cdot>mn({pTs}args)-\<succ> {S}"

| Methd:"\<lbrakk>G,A\<union> {{P} Methd-\<succ> {Q} | ms} |\<turnstile> {{P} body G-\<succ> {Q} | ms}\<rbrakk> \<Longrightarrow>
                                 G,A|\<turnstile>{{P} Methd-\<succ>  {Q} | ms}"

| Body: "\<lbrakk>G,A\<turnstile>{Normal P} .Init D. {Q}; 
  G,A\<turnstile>{Q} .c. {\<lambda>s.. abupd (absorb Ret) .; R\<leftarrow>(In1 (the (locals s Result)))}\<rbrakk> 
    \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} Body D c-\<succ> {R}"
  
  \<comment> \<open>expression lists\<close>

| Nil:                          "G,A\<turnstile>{Normal (P\<leftarrow>Vals [])} []\<doteq>\<succ> {P}"

| Cons: "\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {Q};
          \<forall>v. G,A\<turnstile>{Q\<leftarrow>Val v} es\<doteq>\<succ> {\<lambda>Vals:vs:. R\<leftarrow>Vals (v#vs)}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} e#es\<doteq>\<succ> {R}"

  \<comment> \<open>statements\<close>

| Skip:                         "G,A\<turnstile>{Normal (P\<leftarrow>\<diamondsuit>)} .Skip. {P}"

| Expr: "\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {Q\<leftarrow>\<diamondsuit>}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} .Expr e. {Q}"

| Lab: "\<lbrakk>G,A\<turnstile>{Normal P} .c. {abupd (absorb l) .; Q}\<rbrakk> \<Longrightarrow>
                           G,A\<turnstile>{Normal P} .l\<bullet> c. {Q}"

| Comp: "\<lbrakk>G,A\<turnstile>{Normal P} .c1. {Q};
          G,A\<turnstile>{Q} .c2. {R}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} .c1;;c2. {R}"

| If:   "\<lbrakk>G,A \<turnstile>{Normal P} e-\<succ> {P'};
          \<forall>b. G,A\<turnstile>{P'\<leftarrow>=b} .(if b then c1 else c2). {Q}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} .If(e) c1 Else c2. {Q}"
(* unfolding variant of Loop, not needed here
  LoopU:"\<lbrakk>G,A \<turnstile>{Normal P} e-\<succ> {P'};
          \<forall>b. G,A\<turnstile>{P'\<leftarrow>=b} .(if b then c;;While(e) c else Skip).{Q}\<rbrakk>
         \<Longrightarrow>              G,A\<turnstile>{Normal P} .While(e) c. {Q}"
*)
| Loop: "\<lbrakk>G,A\<turnstile>{P} e-\<succ> {P'}; 
          G,A\<turnstile>{Normal (P'\<leftarrow>=True)} .c. {abupd (absorb (Cont l)) .; P}\<rbrakk> \<Longrightarrow>
                            G,A\<turnstile>{P} .l\<bullet> While(e) c. {(P'\<leftarrow>=False)\<down>=\<diamondsuit>}"
  
| Jmp: "G,A\<turnstile>{Normal (abupd (\<lambda>a. (Some (Jump j))) .; P\<leftarrow>\<diamondsuit>)} .Jmp j. {P}"

| Throw:"\<lbrakk>G,A\<turnstile>{Normal P} e-\<succ> {\<lambda>Val:a:. abupd (throw a) .; Q\<leftarrow>\<diamondsuit>}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} .Throw e. {Q}"

| Try:  "\<lbrakk>G,A\<turnstile>{Normal P} .c1. {SXAlloc G Q};
          G,A\<turnstile>{Q \<and>. (\<lambda>s.  G,s\<turnstile>catch C) ;. new_xcpt_var vn} .c2. {R};
              (Q \<and>. (\<lambda>s. \<not>G,s\<turnstile>catch C)) \<Rightarrow> R\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} .Try c1 Catch(C vn) c2. {R}"

| Fin:  "\<lbrakk>G,A\<turnstile>{Normal P} .c1. {Q};
      \<forall>x. G,A\<turnstile>{Q \<and>. (\<lambda>s. x = fst s) ;. abupd (\<lambda>x. None)}
              .c2. {abupd (abrupt_if (x\<noteq>None) x) .; R}\<rbrakk> \<Longrightarrow>
                                 G,A\<turnstile>{Normal P} .c1 Finally c2. {R}"

| Done:                       "G,A\<turnstile>{Normal (P\<leftarrow>\<diamondsuit> \<and>. initd C)} .Init C. {P}"

| Init: "\<lbrakk>the (class G C) = c;
          G,A\<turnstile>{Normal ((P \<and>. Not \<circ> initd C) ;. supd (init_class_obj G C))}
              .(if C = Object then Skip else Init (super c)). {Q};
      \<forall>l. G,A\<turnstile>{Q \<and>. (\<lambda>s. l = locals (store s)) ;. set_lvars Map.empty}
              .init c. {set_lvars l .; R}\<rbrakk> \<Longrightarrow>
                               G,A\<turnstile>{Normal (P \<and>. Not \<circ> initd C)} .Init C. {R}"

\<comment> \<open>Some dummy rules for the intermediate terms \<open>Callee\<close>,
\<open>InsInitE\<close>, \<open>InsInitV\<close>, \<open>FinA\<close> only used by the smallstep 
semantics.\<close>
| InsInitV: " G,A\<turnstile>{Normal P} InsInitV c v=\<succ> {Q}"
| InsInitE: " G,A\<turnstile>{Normal P} InsInitE c e-\<succ> {Q}"
| Callee:    " G,A\<turnstile>{Normal P} Callee l e-\<succ> {Q}"
| FinA:      " G,A\<turnstile>{Normal P} .FinA a c. {Q}"
(*
axioms 
*)

definition
  adapt_pre :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> 'a assn \<Rightarrow> 'a assn"
  where "adapt_pre P Q Q' = (\<lambda>Y s Z. \<forall>Y' s'. \<exists>Z'. P Y s Z' \<and> (Q Y' s' Z' \<longrightarrow> Q' Y' s' Z))"


subsubsection "rules derived by induction"

lemma cut_valid: "\<lbrakk>G,A'|\<Turnstile>ts; G,A|\<Turnstile>A'\<rbrakk> \<Longrightarrow> G,A|\<Turnstile>ts"
apply (unfold ax_valids_def)
apply fast
done

(*if cut is available
Goal "\<lbrakk>G,A'|\<turnstile>ts; A' \<subseteq> A; \<forall>P Q t. {P} t\<succ> {Q} \<in> A' \<longrightarrow> (\<exists>T. (G,L)\<turnstile>t\<Colon>T) \<rbrakk> \<Longrightarrow>  
       G,A|\<turnstile>ts"
b y etac ax_derivs.cut 1;
b y eatac ax_derivs.asm 1 1;
qed "ax_thin";
*)
lemma ax_thin [rule_format (no_asm)]: 
  "G,(A'::'a triple set)|\<turnstile>(ts::'a triple set) \<Longrightarrow> \<forall>A. A' \<subseteq> A \<longrightarrow> G,A|\<turnstile>ts"
apply (erule ax_derivs.induct)
apply                (tactic "ALLGOALS (EVERY'[clarify_tac \<^context>, REPEAT o smp_tac \<^context> 1])")
apply                (rule ax_derivs.empty)
apply               (erule (1) ax_derivs.insert)
apply              (fast intro: ax_derivs.asm)
(*apply           (fast intro: ax_derivs.cut) *)
apply            (fast intro: ax_derivs.weaken)
apply           (rule ax_derivs.conseq, intro strip, tactic "smp_tac \<^context> 3 1",clarify,
  tactic "smp_tac \<^context> 1 1",rule exI, rule exI, erule (1) conjI) 
(* 37 subgoals *)
prefer 18 (* Methd *)
apply (rule ax_derivs.Methd, drule spec, erule mp, fast) 
apply (tactic \<open>TRYALL (resolve_tac \<^context> ((funpow 5 tl) @{thms ax_derivs.intros}))\<close>)
apply auto
done

lemma ax_thin_insert: "G,(A::'a triple set)\<turnstile>(t::'a triple) \<Longrightarrow> G,insert x A\<turnstile>t"
apply (erule ax_thin)
apply fast
done

lemma subset_mtriples_iff: 
  "ts \<subseteq> {{P} mb-\<succ> {Q} | ms} = (\<exists>ms'. ms'\<subseteq>ms \<and>  ts = {{P} mb-\<succ> {Q} | ms'})"
apply (unfold mtriples_def)
apply (rule subset_image_iff)
done

lemma weaken: 
 "G,(A::'a triple set)|\<turnstile>(ts'::'a triple set) \<Longrightarrow> \<forall>ts. ts \<subseteq> ts' \<longrightarrow> G,A|\<turnstile>ts"
apply (erule ax_derivs.induct)
(*42 subgoals*)
apply       (tactic "ALLGOALS (strip_tac \<^context>)")
apply       (tactic \<open>ALLGOALS(REPEAT o (EVERY'[dresolve_tac \<^context> @{thms subset_singletonD},
         eresolve_tac \<^context> [disjE],
         fast_tac (\<^context> addSIs @{thms ax_derivs.empty})]))\<close>)
apply       (tactic "TRYALL (hyp_subst_tac \<^context>)")
apply       (simp, rule ax_derivs.empty)
apply      (drule subset_insertD)
apply      (blast intro: ax_derivs.insert)
apply     (fast intro: ax_derivs.asm)
(*apply  (blast intro: ax_derivs.cut) *)
apply   (fast intro: ax_derivs.weaken)
apply  (rule ax_derivs.conseq, clarify, tactic "smp_tac \<^context> 3 1", blast(* unused *))
(*37 subgoals*)
apply (tactic \<open>TRYALL (resolve_tac \<^context> ((funpow 5 tl) @{thms ax_derivs.intros})
                   THEN_ALL_NEW fast_tac \<^context>)\<close>)
(*1 subgoal*)
apply (clarsimp simp add: subset_mtriples_iff)
apply (rule ax_derivs.Methd)
apply (drule spec)
apply (erule impE)
apply  (rule exI)
apply  (erule conjI)
apply  (rule HOL.refl)
oops (* dead end, Methd is to blame *)


subsubsection "rules derived from conseq"

text \<open>In the following rules we often have to give some type annotations like:
 \<^term>\<open>G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> {Q}\<close>.
Given only the term above without annotations, Isabelle would infer a more 
general type were we could have 
different types of auxiliary variables in the assumption set (\<^term>\<open>A\<close>) and 
in the triple itself (\<^term>\<open>P\<close> and \<^term>\<open>Q\<close>). But 
\<open>ax_derivs.Methd\<close> enforces the same type in the inductive definition of
the derivation. So we have to restrict the types to be able to apply the
rules. 
\<close>
lemma conseq12: "\<lbrakk>G,(A::'a triple set)\<turnstile>{P'::'a assn} t\<succ> {Q'};  
 \<forall>Y s Z. P Y s Z \<longrightarrow> (\<forall>Y' s'. (\<forall>Y Z'. P' Y s Z' \<longrightarrow> Q' Y' s' Z') \<longrightarrow>  
  Q Y' s' Z)\<rbrakk>  
  \<Longrightarrow>  G,A\<turnstile>{P ::'a assn} t\<succ> {Q }"
apply (rule ax_derivs.conseq)
apply clarsimp
apply blast
done

\<comment> \<open>Nice variant, since it is so symmetric we might be able to memorise it.\<close>
lemma conseq12': "\<lbrakk>G,(A::'a triple set)\<turnstile>{P'::'a assn} t\<succ> {Q'}; \<forall>s Y' s'.  
       (\<forall>Y Z. P' Y s Z \<longrightarrow> Q' Y' s' Z) \<longrightarrow>  
       (\<forall>Y Z. P  Y s Z \<longrightarrow> Q  Y' s' Z)\<rbrakk>  
  \<Longrightarrow>  G,A\<turnstile>{P::'a assn } t\<succ> {Q }"
apply (erule conseq12)
apply fast
done

lemma conseq12_from_conseq12': "\<lbrakk>G,(A::'a triple set)\<turnstile>{P'::'a assn} t\<succ> {Q'};  
 \<forall>Y s Z. P Y s Z \<longrightarrow> (\<forall>Y' s'. (\<forall>Y Z'. P' Y s Z' \<longrightarrow> Q' Y' s' Z') \<longrightarrow>  
  Q Y' s' Z)\<rbrakk>  
  \<Longrightarrow>  G,A\<turnstile>{P::'a assn} t\<succ> {Q }"
apply (erule conseq12')
apply blast
done

lemma conseq1: "\<lbrakk>G,(A::'a triple set)\<turnstile>{P'::'a assn} t\<succ> {Q}; P \<Rightarrow> P'\<rbrakk> 
 \<Longrightarrow> G,A\<turnstile>{P::'a assn} t\<succ> {Q}"
apply (erule conseq12)
apply blast
done

lemma conseq2: "\<lbrakk>G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> {Q'}; Q' \<Rightarrow> Q\<rbrakk> 
\<Longrightarrow> G,A\<turnstile>{P::'a assn} t\<succ> {Q}"
apply (erule conseq12)
apply blast
done

lemma ax_escape: 
 "\<lbrakk>\<forall>Y s Z. P Y s Z 
   \<longrightarrow> G,(A::'a triple set)\<turnstile>{\<lambda>Y' s' (Z'::'a). (Y',s') = (Y,s)} 
                             t\<succ> 
                            {\<lambda>Y s Z'. Q Y s Z}
\<rbrakk> \<Longrightarrow>  G,A\<turnstile>{P::'a assn} t\<succ> {Q::'a assn}"
apply (rule ax_derivs.conseq)
apply force
done

(* unused *)
lemma ax_constant: "\<lbrakk> C \<Longrightarrow> G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> {Q}\<rbrakk> 
\<Longrightarrow> G,A\<turnstile>{\<lambda>Y s Z. C \<and> P Y s Z} t\<succ> {Q}"
apply (rule ax_escape (* unused *))
apply clarify
apply (rule conseq12)
apply  fast
apply auto
done
(*alternative (more direct) proof:
apply (rule ax_derivs.conseq) *)(* unused *)(*
apply (fast)
*)


lemma ax_impossible [intro]: 
  "G,(A::'a triple set)\<turnstile>{\<lambda>Y s Z. False} t\<succ> {Q::'a assn}"
apply (rule ax_escape)
apply clarify
done

(* unused *)
lemma ax_nochange_lemma: "\<lbrakk>P Y s; All ((=) w)\<rbrakk> \<Longrightarrow> P w s"
apply auto
done

lemma ax_nochange:
 "G,(A::(res \<times> state) triple set)\<turnstile>{\<lambda>Y s Z. (Y,s)=Z} t\<succ> {\<lambda>Y s Z. (Y,s)=Z} 
  \<Longrightarrow> G,A\<turnstile>{P::(res \<times> state) assn} t\<succ> {P}"
apply (erule conseq12)
apply auto
apply (erule (1) ax_nochange_lemma)
done

(* unused *)
lemma ax_trivial: "G,(A::'a triple set)\<turnstile>{P::'a assn}  t\<succ> {\<lambda>Y s Z. True}"
apply (rule ax_derivs.conseq(* unused *))
apply auto
done

(* unused *)
lemma ax_disj: 
 "\<lbrakk>G,(A::'a triple set)\<turnstile>{P1::'a assn} t\<succ> {Q1}; G,A\<turnstile>{P2::'a assn} t\<succ> {Q2}\<rbrakk> 
  \<Longrightarrow>  G,A\<turnstile>{\<lambda>Y s Z. P1 Y s Z \<or> P2 Y s Z} t\<succ> {\<lambda>Y s Z. Q1 Y s Z \<or> Q2 Y s Z}"
apply (rule ax_escape (* unused *))
apply safe
apply  (erule conseq12, fast)+
done

(* unused *)
lemma ax_supd_shuffle: 
 "(\<exists>Q. G,(A::'a triple set)\<turnstile>{P::'a assn} .c1. {Q} \<and> G,A\<turnstile>{Q ;. f} .c2. {R}) =  
       (\<exists>Q'. G,A\<turnstile>{P} .c1. {f .; Q'} \<and> G,A\<turnstile>{Q'} .c2. {R})"
apply (best elim!: conseq1 conseq2)
done

lemma ax_cases: "
 \<lbrakk>G,(A::'a triple set)\<turnstile>{P \<and>.       C} t\<succ> {Q::'a assn};  
                   G,A\<turnstile>{P \<and>. Not \<circ> C} t\<succ> {Q}\<rbrakk> \<Longrightarrow> G,A\<turnstile>{P} t\<succ> {Q}"
apply (unfold peek_and_def)
apply (rule ax_escape)
apply clarify
apply (case_tac "C s")
apply  (erule conseq12, force)+
done
(*alternative (more direct) proof:
apply (rule rtac ax_derivs.conseq) *)(* unused *)(*
apply clarify
apply (case_tac "C s")
apply  force+
*)

lemma ax_adapt: "G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> {Q} 
  \<Longrightarrow> G,A\<turnstile>{adapt_pre P Q Q'} t\<succ> {Q'}"
apply (unfold adapt_pre_def)
apply (erule conseq12)
apply fast
done

lemma adapt_pre_adapts: "G,(A::'a triple set)\<Turnstile>{P::'a assn} t\<succ> {Q} 
\<longrightarrow> G,A\<Turnstile>{adapt_pre P Q Q'} t\<succ> {Q'}"
apply (unfold adapt_pre_def)
apply (simp add: ax_valids_def triple_valid_def2)
apply fast
done


lemma adapt_pre_weakest: 
"\<forall>G (A::'a triple set) t. G,A\<Turnstile>{P} t\<succ> {Q} \<longrightarrow> G,A\<Turnstile>{P'} t\<succ> {Q'} \<Longrightarrow>  
  P' \<Rightarrow> adapt_pre P Q (Q'::'a assn)"
apply (unfold adapt_pre_def)
apply (drule spec)
apply (drule_tac x = "{}" in spec)
apply (drule_tac x = "In1r Skip" in spec)
apply (simp add: ax_valids_def triple_valid_def2)
oops

lemma peek_and_forget1_Normal: 
 "G,(A::'a triple set)\<turnstile>{Normal P} t\<succ> {Q::'a assn} 
 \<Longrightarrow> G,A\<turnstile>{Normal (P \<and>. p)} t\<succ> {Q}"
apply (erule conseq1)
apply (simp (no_asm))
done

lemma peek_and_forget1: 
"G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> {Q} 
 \<Longrightarrow> G,A\<turnstile>{P \<and>. p} t\<succ> {Q}"
apply (erule conseq1)
apply (simp (no_asm))
done

lemmas ax_NormalD = peek_and_forget1 [of _ _ _ _ _ normal] 

lemma peek_and_forget2: 
"G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> {Q \<and>. p} 
\<Longrightarrow> G,A\<turnstile>{P} t\<succ> {Q}"
apply (erule conseq2)
apply (simp (no_asm))
done

lemma ax_subst_Val_allI: 
"\<forall>v. G,(A::'a triple set)\<turnstile>{(P'               v )\<leftarrow>Val v} t\<succ> {(Q v)::'a assn}
 \<Longrightarrow>  \<forall>v. G,A\<turnstile>{(\<lambda>w:. P' (the_In1 w))\<leftarrow>Val v} t\<succ> {Q v}"
apply (force elim!: conseq1)
done

lemma ax_subst_Var_allI: 
"\<forall>v. G,(A::'a triple set)\<turnstile>{(P'               v )\<leftarrow>Var v} t\<succ> {(Q v)::'a assn}
 \<Longrightarrow>  \<forall>v. G,A\<turnstile>{(\<lambda>w:. P' (the_In2 w))\<leftarrow>Var v} t\<succ> {Q v}"
apply (force elim!: conseq1)
done

lemma ax_subst_Vals_allI: 
"(\<forall>v. G,(A::'a triple set)\<turnstile>{(     P'          v )\<leftarrow>Vals v} t\<succ> {(Q v)::'a assn})
 \<Longrightarrow>  \<forall>v. G,A\<turnstile>{(\<lambda>w:. P' (the_In3 w))\<leftarrow>Vals v} t\<succ> {Q v}"
apply (force elim!: conseq1)
done


subsubsection "alternative axioms"

lemma ax_Lit2: 
  "G,(A::'a triple set)\<turnstile>{Normal P::'a assn} Lit v-\<succ> {Normal (P\<down>=Val v)}"
apply (rule ax_derivs.Lit [THEN conseq1])
apply force
done
lemma ax_Lit2_test_complete: 
  "G,(A::'a triple set)\<turnstile>{Normal (P\<leftarrow>Val v)::'a assn} Lit v-\<succ> {P}"
apply (rule ax_Lit2 [THEN conseq2])
apply force
done

lemma ax_LVar2: "G,(A::'a triple set)\<turnstile>{Normal P::'a assn} LVar vn=\<succ> {Normal (\<lambda>s.. P\<down>=Var (lvar vn s))}"
apply (rule ax_derivs.LVar [THEN conseq1])
apply force
done

lemma ax_Super2: "G,(A::'a triple set)\<turnstile>
  {Normal P::'a assn} Super-\<succ> {Normal (\<lambda>s.. P\<down>=Val (val_this s))}"
apply (rule ax_derivs.Super [THEN conseq1])
apply force
done

lemma ax_Nil2: 
  "G,(A::'a triple set)\<turnstile>{Normal P::'a assn} []\<doteq>\<succ> {Normal (P\<down>=Vals [])}"
apply (rule ax_derivs.Nil [THEN conseq1])
apply force
done


subsubsection "misc derived structural rules"

(* unused *)
lemma ax_finite_mtriples_lemma: "\<lbrakk>F \<subseteq> ms; finite ms; \<forall>(C,sig)\<in>ms. 
    G,(A::'a triple set)\<turnstile>{Normal (P C sig)::'a assn} mb C sig-\<succ> {Q C sig}\<rbrakk> \<Longrightarrow> 
       G,A|\<turnstile>{{P} mb-\<succ> {Q} | F}"
apply (frule (1) finite_subset)
apply (erule rev_mp)
apply (erule thin_rl)
apply (erule finite_induct)
apply  (unfold mtriples_def)
apply  (clarsimp intro!: ax_derivs.empty ax_derivs.insert)+
apply force
done
lemmas ax_finite_mtriples = ax_finite_mtriples_lemma [OF subset_refl]

lemma ax_derivs_insertD: 
 "G,(A::'a triple set)|\<turnstile>insert (t::'a triple) ts \<Longrightarrow> G,A\<turnstile>t \<and> G,A|\<turnstile>ts"
apply (fast intro: ax_derivs.weaken)
done

lemma ax_methods_spec: 
"\<lbrakk>G,(A::'a triple set)|\<turnstile>case_prod f ` ms; (C,sig) \<in> ms\<rbrakk>\<Longrightarrow> G,A\<turnstile>((f C sig)::'a triple)"
apply (erule ax_derivs.weaken)
apply (force del: image_eqI intro: rev_image_eqI)
done

(* this version is used to avoid using the cut rule *)
lemma ax_finite_pointwise_lemma [rule_format]: "\<lbrakk>F \<subseteq> ms; finite ms\<rbrakk> \<Longrightarrow>  
  ((\<forall>(C,sig)\<in>F. G,(A::'a triple set)\<turnstile>(f C sig::'a triple)) \<longrightarrow> (\<forall>(C,sig)\<in>ms. G,A\<turnstile>(g C sig::'a triple))) \<longrightarrow>  
      G,A|\<turnstile>case_prod f ` F \<longrightarrow> G,A|\<turnstile>case_prod g ` F"
apply (frule (1) finite_subset)
apply (erule rev_mp)
apply (erule thin_rl)
apply (erule finite_induct)
apply  clarsimp+
apply (drule ax_derivs_insertD)
apply (rule ax_derivs.insert)
apply  (simp (no_asm_simp) only: split_tupled_all)
apply  (auto elim: ax_methods_spec)
done
lemmas ax_finite_pointwise = ax_finite_pointwise_lemma [OF subset_refl]
 
lemma ax_no_hazard: 
  "G,(A::'a triple set)\<turnstile>{P \<and>. type_ok G t} t\<succ> {Q::'a assn} \<Longrightarrow> G,A\<turnstile>{P} t\<succ> {Q}"
apply (erule ax_cases)
apply (rule ax_derivs.hazard [THEN conseq1])
apply force
done

lemma ax_free_wt: 
 "(\<exists>T L C. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) 
  \<longrightarrow> G,(A::'a triple set)\<turnstile>{Normal P} t\<succ> {Q::'a assn} \<Longrightarrow> 
  G,A\<turnstile>{Normal P} t\<succ> {Q}"
apply (rule ax_no_hazard)
apply (rule ax_escape)
apply clarify
apply (erule mp [THEN conseq12])
apply  (auto simp add: type_ok_def)
done

ML \<open>ML_Thms.bind_thms ("ax_Abrupts", sum3_instantiate \<^context> @{thm ax_derivs.Abrupt})\<close>
declare ax_Abrupts [intro!]

lemmas ax_Normal_cases = ax_cases [of _ _ _ normal]

lemma ax_Skip [intro!]: "G,(A::'a triple set)\<turnstile>{P\<leftarrow>\<diamondsuit>} .Skip. {P::'a assn}"
apply (rule ax_Normal_cases)
apply  (rule ax_derivs.Skip)
apply fast
done
lemmas ax_SkipI = ax_Skip [THEN conseq1]


subsubsection "derived rules for methd call"

lemma ax_Call_known_DynT: 
"\<lbrakk>G\<turnstile>IntVir\<rightarrow>C\<preceq>statT; 
  \<forall>a vs l. G,A\<turnstile>{(R a\<leftarrow>Vals vs \<and>. (\<lambda>s. l = locals (store s)) ;.
  init_lvars G C \<lparr>name=mn,parTs=pTs\<rparr> IntVir a vs)} 
    Methd C \<lparr>name=mn,parTs=pTs\<rparr>-\<succ> {set_lvars l .; S}; 
  \<forall>a. G,A\<turnstile>{Q\<leftarrow>Val a} args\<doteq>\<succ>  
       {R a \<and>. (\<lambda>s. C = obj_class (the (heap (store s) (the_Addr a))) \<and>
                     C = invocation_declclass 
                            G IntVir (store s) a statT \<lparr>name=mn,parTs=pTs\<rparr> )};  
       G,(A::'a triple set)\<turnstile>{Normal P} e-\<succ> {Q::'a assn}\<rbrakk>  
   \<Longrightarrow> G,A\<turnstile>{Normal P} {accC,statT,IntVir}e\<cdot>mn({pTs}args)-\<succ> {S}"
apply (erule ax_derivs.Call)
apply  safe
apply  (erule spec)
apply (rule ax_escape, clarsimp)
apply (drule spec, drule spec, drule spec,erule conseq12)
apply force
done


lemma ax_Call_Static: 
 "\<lbrakk>\<forall>a vs l. G,A\<turnstile>{R a\<leftarrow>Vals vs \<and>. (\<lambda>s. l = locals (store s)) ;.  
               init_lvars G C \<lparr>name=mn,parTs=pTs\<rparr> Static any_Addr vs}  
              Methd C \<lparr>name=mn,parTs=pTs\<rparr>-\<succ> {set_lvars l .; S}; 
  G,A\<turnstile>{Normal P} e-\<succ> {Q};
  \<forall> a. G,(A::'a triple set)\<turnstile>{Q\<leftarrow>Val a} args\<doteq>\<succ> {(R::val \<Rightarrow> 'a assn)  a 
  \<and>. (\<lambda> s. C=invocation_declclass 
                G Static (store s) a statT \<lparr>name=mn,parTs=pTs\<rparr>)}
\<rbrakk>  \<Longrightarrow>  G,A\<turnstile>{Normal P} {accC,statT,Static}e\<cdot>mn({pTs}args)-\<succ> {S}"
apply (erule ax_derivs.Call)
apply  safe
apply  (erule spec)
apply (rule ax_escape, clarsimp)
apply (erule_tac V = "P \<longrightarrow> Q" for P Q in thin_rl)
apply (drule spec,drule spec,drule spec, erule conseq12)
apply (force simp add: init_lvars_def Let_def)
done

lemma ax_Methd1: 
 "\<lbrakk>G,A\<union>{{P} Methd-\<succ> {Q} | ms}|\<turnstile> {{P} body G-\<succ> {Q} | ms}; (C,sig)\<in> ms\<rbrakk> \<Longrightarrow> 
       G,A\<turnstile>{Normal (P C sig)} Methd C sig-\<succ> {Q C sig}"
apply (drule ax_derivs.Methd)
apply (unfold mtriples_def)
apply (erule (1) ax_methods_spec)
done

lemma ax_MethdN: 
"G,insert({Normal P} Methd  C sig-\<succ> {Q}) A\<turnstile> 
          {Normal P} body G C sig-\<succ> {Q} \<Longrightarrow>  
      G,A\<turnstile>{Normal P} Methd   C sig-\<succ> {Q}"
apply (rule ax_Methd1)
apply  (rule_tac [2] singletonI)
apply (unfold mtriples_def)
apply clarsimp
done

lemma ax_StatRef: 
  "G,(A::'a triple set)\<turnstile>{Normal (P\<leftarrow>Val Null)} StatRef rt-\<succ> {P::'a assn}"
apply (rule ax_derivs.Cast)
apply (rule ax_Lit2 [THEN conseq2])
apply clarsimp
done

subsubsection "rules derived from Init and Done"

  lemma ax_InitS: "\<lbrakk>the (class G C) = c; C \<noteq> Object;  
     \<forall>l. G,A\<turnstile>{Q \<and>. (\<lambda>s. l = locals (store s)) ;. set_lvars Map.empty}  
            .init c. {set_lvars l .; R};   
         G,A\<turnstile>{Normal ((P \<and>. Not \<circ> initd C) ;. supd (init_class_obj G C))}  
  .Init (super c). {Q}\<rbrakk> \<Longrightarrow>  
  G,(A::'a triple set)\<turnstile>{Normal (P \<and>. Not \<circ> initd C)} .Init C. {R::'a assn}"
apply (erule ax_derivs.Init)
apply  (simp (no_asm_simp))
apply assumption
done

lemma ax_Init_Skip_lemma: 
"\<forall>l. G,(A::'a triple set)\<turnstile>{P\<leftarrow>\<diamondsuit> \<and>. (\<lambda>s. l = locals (store s)) ;. set_lvars l'}
  .Skip. {(set_lvars l .; P)::'a assn}"
apply (rule allI)
apply (rule ax_SkipI)
apply clarsimp
done

lemma ax_triv_InitS: "\<lbrakk>the (class G C) = c;init c = Skip; C \<noteq> Object; 
       P\<leftarrow>\<diamondsuit> \<Rightarrow> (supd (init_class_obj G C) .; P);  
       G,A\<turnstile>{Normal (P \<and>. initd C)} .Init (super c). {(P \<and>. initd C)\<leftarrow>\<diamondsuit>}\<rbrakk> \<Longrightarrow>  
       G,(A::'a triple set)\<turnstile>{Normal P\<leftarrow>\<diamondsuit>} .Init C. {(P \<and>. initd C)::'a assn}"
apply (rule_tac C = "initd C" in ax_cases)
apply  (rule conseq1, rule ax_derivs.Done, clarsimp)
apply (simp (no_asm))
apply (erule (1) ax_InitS)
apply  simp
apply  (rule ax_Init_Skip_lemma)
apply (erule conseq1)
apply force
done

lemma ax_Init_Object: "wf_prog G \<Longrightarrow> G,(A::'a triple set)\<turnstile>
  {Normal ((supd (init_class_obj G Object) .; P\<leftarrow>\<diamondsuit>) \<and>. Not \<circ> initd Object)} 
       .Init Object. {(P \<and>. initd Object)::'a assn}"
apply (rule ax_derivs.Init)
apply   (drule class_Object, force)
apply (simp_all (no_asm))
apply (rule_tac [2] ax_Init_Skip_lemma)
apply (rule ax_SkipI, force)
done

lemma ax_triv_Init_Object: "\<lbrakk>wf_prog G;  
       (P::'a assn) \<Rightarrow> (supd (init_class_obj G Object) .; P)\<rbrakk> \<Longrightarrow>  
  G,(A::'a triple set)\<turnstile>{Normal P\<leftarrow>\<diamondsuit>} .Init Object. {P \<and>. initd Object}"
apply (rule_tac C = "initd Object" in ax_cases)
apply  (rule conseq1, rule ax_derivs.Done, clarsimp)
apply (erule ax_Init_Object [THEN conseq1])
apply force
done


subsubsection "introduction rules for Alloc and SXAlloc"

lemma ax_SXAlloc_Normal: 
 "G,(A::'a triple set)\<turnstile>{P::'a assn} .c. {Normal Q} 
 \<Longrightarrow> G,A\<turnstile>{P} .c. {SXAlloc G Q}"
apply (erule conseq2)
apply (clarsimp elim!: sxalloc_elim_cases simp add: split_tupled_all)
done

lemma ax_Alloc: 
  "G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> 
     {Normal (\<lambda>Y (x,s) Z. (\<forall>a. new_Addr (heap s) = Some a \<longrightarrow>  
      Q (Val (Addr a)) (Norm(init_obj G (CInst C) (Heap a) s)) Z)) \<and>. 
      heap_free (Suc (Suc 0))}
   \<Longrightarrow> G,A\<turnstile>{P} t\<succ> {Alloc G (CInst C) Q}"
apply (erule conseq2)
apply (auto elim!: halloc_elim_cases)
done

lemma ax_Alloc_Arr: 
 "G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> 
   {\<lambda>Val:i:. Normal (\<lambda>Y (x,s) Z. \<not>the_Intg i<0 \<and>  
    (\<forall>a. new_Addr (heap s) = Some a \<longrightarrow>  
    Q (Val (Addr a)) (Norm (init_obj G (Arr T (the_Intg i)) (Heap a) s)) Z)) \<and>.
    heap_free (Suc (Suc 0))} 
 \<Longrightarrow>  
 G,A\<turnstile>{P} t\<succ> {\<lambda>Val:i:. abupd (check_neg i) .; Alloc G (Arr T(the_Intg i)) Q}"
apply (erule conseq2)
apply (auto elim!: halloc_elim_cases)
done

lemma ax_SXAlloc_catch_SXcpt: 
 "\<lbrakk>G,(A::'a triple set)\<turnstile>{P::'a assn} t\<succ> 
     {(\<lambda>Y (x,s) Z. x=Some (Xcpt (Std xn)) \<and>  
      (\<forall>a. new_Addr (heap s) = Some a \<longrightarrow>  
      Q Y (Some (Xcpt (Loc a)),init_obj G (CInst (SXcpt xn)) (Heap a) s) Z))  
      \<and>. heap_free (Suc (Suc 0))}\<rbrakk> 
 \<Longrightarrow>  
 G,A\<turnstile>{P} t\<succ> {SXAlloc G (\<lambda>Y s Z. Q Y s Z \<and> G,s\<turnstile>catch SXcpt xn)}"
apply (erule conseq2)
apply (auto elim!: sxalloc_elim_cases halloc_elim_cases)
done

end
