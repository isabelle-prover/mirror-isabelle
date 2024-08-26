(*  Title:      ZF/ex/misc.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Composition of homomorphisms, Pastre's examples, ...
*)

section\<open>Miscellaneous ZF Examples\<close>

theory misc imports ZF begin

subsection\<open>Various Small Problems\<close>

text\<open>The singleton problems are much harder in HOL.\<close>
lemma singleton_example_1:
     "\<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  by blast

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  \<comment> \<open>Variant of the problem above.\<close>
  by blast

lemma "\<exists>!x. f (g(x)) = x \<Longrightarrow> \<exists>!y. g (f(y)) = y"
  \<comment> \<open>A unique fixpoint theorem --- \<open>fast\<close>/\<open>best\<close>/\<open>auto\<close> all fail.\<close> 
  apply (erule ex1E, rule ex1I, erule subst_context)
  apply (rule subst, assumption, erule allE, rule subst_context, erule mp)
  apply (erule subst_context)
  done


text\<open>A weird property of ordered pairs.\<close>
lemma "b\<noteq>c \<Longrightarrow> \<langle>a,b\<rangle> \<inter> \<langle>a,c\<rangle> = \<langle>a,a\<rangle>"
by (simp add: Pair_def Int_cons_left Int_cons_right doubleton_eq_iff, blast)

text\<open>These two are cited in Benzmueller and Kohlhase's system description of
 LEO, CADE-15, 1998 (page 139-143) as theorems LEO could not prove.\<close>
lemma "(X = Y \<union> Z) \<longleftrightarrow> (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
by (blast intro!: equalityI)

text\<open>the dual of the previous one\<close>
lemma "(X = Y \<inter> Z) \<longleftrightarrow> (X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
by (blast intro!: equalityI)

text\<open>trivial example of term synthesis: apparently hard for some provers!\<close>
schematic_goal "a \<noteq> b \<Longrightarrow> a:?X \<and> b \<notin> ?X"
by blast

text\<open>Nice blast benchmark.  Proved in 0.3s; old tactics can't manage it!\<close>
lemma "\<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by blast

text\<open>variant of the benchmark above\<close>
lemma "\<forall>x \<in> S. \<Union>(S) \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by blast

(*Example 12 (credited to Peter Andrews) from
 W. Bledsoe.  A Maximal Method for Set Variables in Automatic Theorem-proving.
 In: J. Hayes and D. Michie and L. Mikulich, eds.  Machine Intelligence 9.
 Ellis Horwood, 53-100 (1979). *)
lemma "(\<forall>F. {x} \<in> F \<longrightarrow> {y} \<in> F) \<longrightarrow> (\<forall>A. x \<in> A \<longrightarrow> y \<in> A)"
by best

text\<open>A characterization of functions suggested by Tobias Nipkow\<close>
lemma "r \<in> domain(r)->B  \<longleftrightarrow>  r \<subseteq> domain(r)*B \<and> (\<forall>X. r `` (r -`` X) \<subseteq> X)"
by (unfold Pi_def function_def, best)


subsection\<open>Composition of homomorphisms is a Homomorphism\<close>

text\<open>Given as a challenge problem in
  R. Boyer et al.,
  Set Theory in First-Order Logic: Clauses for Gödel's Axioms,
  JAR 2 (1986), 287-327\<close>

text\<open>collecting the relevant lemmas\<close>
declare comp_fun [simp] SigmaI [simp] apply_funtype [simp]

(*Force helps prove conditions of rewrites such as comp_fun_apply, since
  rewriting does not instantiate Vars.*)
lemma "(\<forall>A f B g. hom(A,f,B,g) =  
           {H \<in> A->B. f \<in> A*A->A \<and> g \<in> B*B->B \<and>  
                     (\<forall>x \<in> A. \<forall>y \<in> A. H`(f`\<langle>x,y\<rangle>) = g`<H`x,H`y>)}) \<longrightarrow>  
       J \<in> hom(A,f,B,g) \<and> K \<in> hom(B,g,C,h) \<longrightarrow>   
       (K O J) \<in> hom(A,f,C,h)"
by force

text\<open>Another version, with meta-level rewriting\<close>
lemma "(\<And>A f B g. hom(A,f,B,g) \<equiv>  
           {H \<in> A->B. f \<in> A*A->A \<and> g \<in> B*B->B \<and>  
                     (\<forall>x \<in> A. \<forall>y \<in> A. H`(f`\<langle>x,y\<rangle>) = g`<H`x,H`y>)}) 
       \<Longrightarrow> J \<in> hom(A,f,B,g) \<and> K \<in> hom(B,g,C,h) \<longrightarrow> (K O J) \<in> hom(A,f,C,h)"
by force


subsection\<open>Pastre's Examples\<close>

text\<open>D Pastre.  Automatic theorem proving in set theory. 
        Artificial Intelligence, 10:1--27, 1978.
Previously, these were done using ML code, but blast manages fine.\<close>

lemmas compIs [intro] = comp_surj comp_inj comp_fun [intro]
lemmas compDs [dest] =  comp_mem_injD1 comp_mem_surjD1 
                        comp_mem_injD2 comp_mem_surjD2

lemma pastre1: 
    "\<lbrakk>(h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> surj(C,C);          
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A\<rbrakk> \<Longrightarrow> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre3: 
    "\<lbrakk>(h O g O f) \<in> surj(A,A);          
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> inj(C,C);           
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A\<rbrakk> \<Longrightarrow> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre4: 
    "\<lbrakk>(h O g O f) \<in> surj(A,A);          
        (f O h O g) \<in> inj(B,B);           
        (g O f O h) \<in> inj(C,C);           
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A\<rbrakk> \<Longrightarrow> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre5: 
    "\<lbrakk>(h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> surj(B,B);          
        (g O f O h) \<in> inj(C,C);           
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A\<rbrakk> \<Longrightarrow> h \<in> bij(C,A)"
by (unfold bij_def, blast)

lemma pastre6: 
    "\<lbrakk>(h O g O f) \<in> inj(A,A);           
        (f O h O g) \<in> inj(B,B);           
        (g O f O h) \<in> surj(C,C);          
        f \<in> A->B;  g \<in> B->C;  h \<in> C->A\<rbrakk> \<Longrightarrow> h \<in> bij(C,A)"
by (unfold bij_def, blast)


end

