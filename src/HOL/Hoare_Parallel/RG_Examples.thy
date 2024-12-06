section \<open>Examples\<close>

theory RG_Examples
imports RG_Syntax
begin

lemmas definitions [simp]= stable_def Pre_def Rely_def Guar_def Post_def Com_def

subsection \<open>Set Elements of an Array to Zero\<close>

lemma le_less_trans2: "\<lbrakk>(j::nat)<k; i\<le> j\<rbrakk> \<Longrightarrow> i<k"
by simp

lemma add_le_less_mono: "\<lbrakk> (a::nat) < c; b\<le>d \<rbrakk> \<Longrightarrow> a + b < c + d"
by simp

record Example1 =
  A :: "nat list"

lemma Example1:
 "\<turnstile> COBEGIN
      SCHEME [0 \<le> i < n]
     (\<acute>A := \<acute>A [i := 0],
     \<lbrace> n < length \<acute>A \<rbrace>,
     \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> \<ordmasculine>A ! i = \<ordfeminine>A ! i \<rbrace>,
     \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> (\<forall>j<n. i \<noteq> j \<longrightarrow> \<ordmasculine>A ! j = \<ordfeminine>A ! j) \<rbrace>,
     \<lbrace> \<acute>A ! i = 0 \<rbrace>)
    COEND
 SAT [\<lbrace> n < length \<acute>A \<rbrace>, \<lbrace> \<ordmasculine>A = \<ordfeminine>A \<rbrace>, \<lbrace> True \<rbrace>, \<lbrace> \<forall>i < n. \<acute>A ! i = 0 \<rbrace>]"
apply(rule Parallel)
apply (auto intro!: Basic)
done

lemma Example1_parameterized:
"k < t \<Longrightarrow>
  \<turnstile> COBEGIN
    SCHEME [k*n\<le>i<(Suc k)*n] (\<acute>A:=\<acute>A[i:=0],
   \<lbrace>t*n < length \<acute>A\<rbrace>,
   \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and> \<ordmasculine>A!i = \<ordfeminine>A!i\<rbrace>,
   \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and> (\<forall>j<length \<ordmasculine>A . i\<noteq>j \<longrightarrow> \<ordmasculine>A!j = \<ordfeminine>A!j)\<rbrace>,
   \<lbrace>\<acute>A!i=0\<rbrace>)
   COEND
 SAT [\<lbrace>t*n < length \<acute>A\<rbrace>,
      \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and> (\<forall>i<n. \<ordmasculine>A!(k*n+i)=\<ordfeminine>A!(k*n+i))\<rbrace>,
      \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and>
      (\<forall>i<length \<ordmasculine>A . (i<k*n \<longrightarrow> \<ordmasculine>A!i = \<ordfeminine>A!i) \<and> ((Suc k)*n \<le> i\<longrightarrow> \<ordmasculine>A!i = \<ordfeminine>A!i))\<rbrace>,
      \<lbrace>\<forall>i<n. \<acute>A!(k*n+i) = 0\<rbrace>]"
apply(rule Parallel)
    apply auto
  apply(erule_tac x="k*n +i" in allE)
  apply(subgoal_tac "k*n+i <length (A b)")
   apply force
  apply(erule le_less_trans2)
  apply(case_tac t,simp+)
  apply (simp add:add.commute)
  apply(simp add: add_le_mono)
apply(rule Basic)
   apply simp
   apply clarify
   apply (subgoal_tac "k*n+i< length (A x)")
    apply simp
   apply(erule le_less_trans2)
   apply(case_tac t,simp+)
   apply (simp add:add.commute)
   apply(rule add_le_mono, auto)
done


subsection \<open>Increment a Variable in Parallel\<close>

subsubsection \<open>Two components\<close>

record Example2 =
  x  :: nat
  c_0 :: nat
  c_1 :: nat

lemma Example2:
 "\<turnstile>  COBEGIN
    (\<langle> \<acute>x:=\<acute>x+1;; \<acute>c_0:=\<acute>c_0 + 1 \<rangle>,
     \<lbrace>\<acute>x=\<acute>c_0 + \<acute>c_1  \<and> \<acute>c_0=0\<rbrace>,
     \<lbrace>\<ordmasculine>c_0 = \<ordfeminine>c_0 \<and>
        (\<ordmasculine>x=\<ordmasculine>c_0 + \<ordmasculine>c_1
        \<longrightarrow> \<ordfeminine>x = \<ordfeminine>c_0 + \<ordfeminine>c_1)\<rbrace>,
     \<lbrace>\<ordmasculine>c_1 = \<ordfeminine>c_1 \<and>
         (\<ordmasculine>x=\<ordmasculine>c_0 + \<ordmasculine>c_1
         \<longrightarrow> \<ordfeminine>x =\<ordfeminine>c_0 + \<ordfeminine>c_1)\<rbrace>,
     \<lbrace>\<acute>x=\<acute>c_0 + \<acute>c_1 \<and> \<acute>c_0=1 \<rbrace>)
  \<parallel>
      (\<langle> \<acute>x:=\<acute>x+1;; \<acute>c_1:=\<acute>c_1+1 \<rangle>,
     \<lbrace>\<acute>x=\<acute>c_0 + \<acute>c_1 \<and> \<acute>c_1=0 \<rbrace>,
     \<lbrace>\<ordmasculine>c_1 = \<ordfeminine>c_1 \<and>
        (\<ordmasculine>x=\<ordmasculine>c_0 + \<ordmasculine>c_1
        \<longrightarrow> \<ordfeminine>x = \<ordfeminine>c_0 + \<ordfeminine>c_1)\<rbrace>,
     \<lbrace>\<ordmasculine>c_0 = \<ordfeminine>c_0 \<and>
         (\<ordmasculine>x=\<ordmasculine>c_0 + \<ordmasculine>c_1
        \<longrightarrow> \<ordfeminine>x =\<ordfeminine>c_0 + \<ordfeminine>c_1)\<rbrace>,
     \<lbrace>\<acute>x=\<acute>c_0 + \<acute>c_1 \<and> \<acute>c_1=1\<rbrace>)
 COEND
 SAT [\<lbrace>\<acute>x=0 \<and> \<acute>c_0=0 \<and> \<acute>c_1=0\<rbrace>,
      \<lbrace>\<ordmasculine>x=\<ordfeminine>x \<and>  \<ordmasculine>c_0= \<ordfeminine>c_0 \<and> \<ordmasculine>c_1=\<ordfeminine>c_1\<rbrace>,
      \<lbrace>True\<rbrace>,
      \<lbrace>\<acute>x=2\<rbrace>]"
apply(rule Parallel)
   apply simp_all
   apply clarify
   apply(case_tac i)
    apply simp
    apply(rule conjI)
     apply clarify
     apply simp
    apply clarify
    apply simp
   apply simp
   apply(rule conjI)
    apply clarify
    apply simp
   apply clarify
   apply simp
   apply(subgoal_tac "x=0")
    apply simp
   apply arith
  apply clarify
  apply(case_tac xa, simp, simp)
 apply clarify
 apply simp
 apply(erule_tac x=0 in all_dupE)
 apply(erule_tac x=1 in allE,simp)
apply clarify
apply(case_tac i,simp)
 apply(rule Await)
  apply simp_all
 apply(clarify)
 apply(rule Seq)
  prefer 2
  apply(rule Basic)
   apply simp_all
  apply(rule subset_refl)
 apply(rule Basic)
 apply simp_all
 apply clarify
 apply simp
apply(rule Await)
 apply simp_all
apply(clarify)
apply(rule Seq)
 prefer 2
 apply(rule Basic)
  apply simp_all
 apply(rule subset_refl)
apply(auto intro!: Basic)
done

subsubsection \<open>Parameterized\<close>

lemma Example2_lemma2_aux: "j<n \<Longrightarrow>
 (\<Sum>i=0..<n. (b i::nat)) =
 (\<Sum>i=0..<j. b i) + b j + (\<Sum>i=0..<n-(Suc j) . b (Suc j + i))"
apply(induct n)
 apply simp_all
apply(simp add:less_Suc_eq)
 apply(auto)
apply(subgoal_tac "n - j = Suc(n- Suc j)")
  apply simp
apply arith
done

lemma Example2_lemma2_aux2:
  "j\<le> s \<Longrightarrow> (\<Sum>i::nat=0..<j. (b (s:=t)) i) = (\<Sum>i=0..<j. b i)"
  by (induct j) simp_all

lemma Example2_lemma2:
 "\<lbrakk>j<n; b j=0\<rbrakk> \<Longrightarrow> Suc (\<Sum>i::nat=0..<n. b i)=(\<Sum>i=0..<n. (b (j := Suc 0)) i)"
apply(frule_tac b="(b (j:=(Suc 0)))" in Example2_lemma2_aux)
apply(erule_tac  t="sum (b(j := (Suc 0))) {0..<n}" in ssubst)
apply(frule_tac b=b in Example2_lemma2_aux)
apply(erule_tac  t="sum b {0..<n}" in ssubst)
apply(subgoal_tac "Suc (sum b {0..<j} + b j + (\<Sum>i=0..<n - Suc j. b (Suc j + i)))=(sum b {0..<j} + Suc (b j) + (\<Sum>i=0..<n - Suc j. b (Suc j + i)))")
apply(rotate_tac -1)
apply(erule ssubst)
apply(subgoal_tac "j\<le>j")
 apply(drule_tac b="b" and t="(Suc 0)" in Example2_lemma2_aux2)
apply(rotate_tac -1)
apply(erule ssubst)
apply simp_all
done

lemma Example2_lemma2_Suc0: "\<lbrakk>j<n; b j=0\<rbrakk> \<Longrightarrow>
 Suc (\<Sum>i::nat=0..< n. b i)=(\<Sum>i=0..< n. (b (j:=Suc 0)) i)"
by(simp add:Example2_lemma2)

record Example2_parameterized =
  C :: "nat \<Rightarrow> nat"
  y  :: nat

lemma Example2_parameterized: "0<n \<Longrightarrow>
  \<turnstile> COBEGIN SCHEME  [0\<le>i<n]
     (\<langle> \<acute>y:=\<acute>y+1;; \<acute>C:=\<acute>C (i:=1) \<rangle>,
     \<lbrace>\<acute>y=(\<Sum>i=0..<n. \<acute>C i) \<and> \<acute>C i=0\<rbrace>,
     \<lbrace>\<ordmasculine>C i = \<ordfeminine>C i \<and>
      (\<ordmasculine>y=(\<Sum>i=0..<n. \<ordmasculine>C i) \<longrightarrow> \<ordfeminine>y =(\<Sum>i=0..<n. \<ordfeminine>C i))\<rbrace>,
     \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordmasculine>C j = \<ordfeminine>C j) \<and>
       (\<ordmasculine>y=(\<Sum>i=0..<n. \<ordmasculine>C i) \<longrightarrow> \<ordfeminine>y =(\<Sum>i=0..<n. \<ordfeminine>C i))\<rbrace>,
     \<lbrace>\<acute>y=(\<Sum>i=0..<n. \<acute>C i) \<and> \<acute>C i=1\<rbrace>)
    COEND
 SAT [\<lbrace>\<acute>y=0 \<and> (\<Sum>i=0..<n. \<acute>C i)=0 \<rbrace>, \<lbrace>\<ordmasculine>C=\<ordfeminine>C \<and> \<ordmasculine>y=\<ordfeminine>y\<rbrace>, \<lbrace>True\<rbrace>, \<lbrace>\<acute>y=n\<rbrace>]"
apply(rule Parallel)
apply force
apply force
apply(force)
apply clarify
apply simp
apply simp
apply clarify
apply simp
apply(rule Await)
apply simp_all
apply clarify
apply(rule Seq)
prefer 2
apply(rule Basic)
apply(rule subset_refl)
apply simp+
apply(rule Basic)
apply simp
apply clarify
apply simp
apply(simp add:Example2_lemma2_Suc0 cong:if_cong)
apply simp_all
done

subsection \<open>Find Least Element\<close>

text \<open>A previous lemma:\<close>

lemma mod_aux :"\<lbrakk>i < (n::nat); a mod n = i;  j < a + n; j mod n = i; a < j\<rbrakk> \<Longrightarrow> False"
apply(subgoal_tac "a=a div n*n + a mod n" )
 prefer 2 apply (simp (no_asm_use))
apply(subgoal_tac "j=j div n*n + j mod n")
 prefer 2 apply (simp (no_asm_use))
apply simp
apply(subgoal_tac "a div n*n < j div n*n")
prefer 2 apply arith
apply(subgoal_tac "j div n*n < (a div n + 1)*n")
prefer 2 apply simp
apply (simp only:mult_less_cancel2)
apply arith
done

record Example3 =
  X :: "nat \<Rightarrow> nat"
  Y :: "nat \<Rightarrow> nat"

lemma Example3: "m mod n=0 \<Longrightarrow>
 \<turnstile> COBEGIN
 SCHEME [0\<le>i<n]
 (WHILE (\<forall>j<n. \<acute>X i < \<acute>Y j)  DO
   IF P(B!(\<acute>X i)) THEN \<acute>Y:=\<acute>Y (i:=\<acute>X i)
   ELSE \<acute>X:= \<acute>X (i:=(\<acute>X i)+ n) FI
  OD,
 \<lbrace>(\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i)\<rbrace>,
 \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordfeminine>Y j \<le> \<ordmasculine>Y j) \<and> \<ordmasculine>X i = \<ordfeminine>X i \<and>
   \<ordmasculine>Y i = \<ordfeminine>Y i\<rbrace>,
 \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordmasculine>X j = \<ordfeminine>X j \<and> \<ordmasculine>Y j = \<ordfeminine>Y j) \<and>
   \<ordfeminine>Y i \<le> \<ordmasculine>Y i\<rbrace>,
 \<lbrace>(\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i) \<and> (\<exists>j<n. \<acute>Y j \<le> \<acute>X i) \<rbrace>)
 COEND
 SAT [\<lbrace> \<forall>i<n. \<acute>X i=i \<and> \<acute>Y i=m+i \<rbrace>,\<lbrace>\<ordmasculine>X=\<ordfeminine>X \<and> \<ordmasculine>Y=\<ordfeminine>Y\<rbrace>,\<lbrace>True\<rbrace>,
  \<lbrace>\<forall>i<n. (\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and>
    (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i) \<and> (\<exists>j<n. \<acute>Y j \<le> \<acute>X i)\<rbrace>]"
apply(rule Parallel)
\<comment> \<open>5 subgoals left\<close>
apply force+
apply clarify
apply simp
apply(rule While)
    apply force
   apply force
    apply force
  apply (erule dvdE)
 apply(rule_tac pre'="\<lbrace> \<acute>X i mod n = i \<and> (\<forall>j. j<\<acute>X i \<longrightarrow> j mod n = i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i < n * k \<longrightarrow> P (B!(\<acute>Y i))) \<and> \<acute>X i<\<acute>Y i\<rbrace>" in Conseq)
     apply force
    apply(rule subset_refl)+
 apply(rule Cond)
    apply force
   apply(rule Basic)
      apply force
     apply fastforce
    apply force
   apply force
  apply(rule Basic)
     apply simp
     apply clarify
     apply simp
     apply (case_tac "X x (j mod n) \<le> j")
     apply (drule le_imp_less_or_eq)
     apply (erule disjE)
     apply (drule_tac j=j and n=n and i="j mod n" and a="X x (j mod n)" in mod_aux)
     apply auto
done

text \<open>Same but with a list as auxiliary variable:\<close>

record Example3_list =
  X :: "nat list"
  Y :: "nat list"

lemma Example3_list: "m mod n=0 \<Longrightarrow> \<turnstile> (COBEGIN SCHEME [0\<le>i<n]
 (WHILE (\<forall>j<n. \<acute>X!i < \<acute>Y!j)  DO
     IF P(B!(\<acute>X!i)) THEN \<acute>Y:=\<acute>Y[i:=\<acute>X!i] ELSE \<acute>X:= \<acute>X[i:=(\<acute>X!i)+ n] FI
  OD,
 \<lbrace>n<length \<acute>X \<and> n<length \<acute>Y \<and> (\<acute>X!i) mod n=i \<and> (\<forall>j<\<acute>X!i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y!i<m \<longrightarrow> P(B!(\<acute>Y!i)) \<and> \<acute>Y!i\<le> m+i)\<rbrace>,
 \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordfeminine>Y!j \<le> \<ordmasculine>Y!j) \<and> \<ordmasculine>X!i = \<ordfeminine>X!i \<and>
   \<ordmasculine>Y!i = \<ordfeminine>Y!i \<and> length \<ordmasculine>X = length \<ordfeminine>X \<and> length \<ordmasculine>Y = length \<ordfeminine>Y\<rbrace>,
 \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordmasculine>X!j = \<ordfeminine>X!j \<and> \<ordmasculine>Y!j = \<ordfeminine>Y!j) \<and>
   \<ordfeminine>Y!i \<le> \<ordmasculine>Y!i \<and> length \<ordmasculine>X = length \<ordfeminine>X \<and> length \<ordmasculine>Y = length \<ordfeminine>Y\<rbrace>,
 \<lbrace>(\<acute>X!i) mod n=i \<and> (\<forall>j<\<acute>X!i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y!i<m \<longrightarrow> P(B!(\<acute>Y!i)) \<and> \<acute>Y!i\<le> m+i) \<and> (\<exists>j<n. \<acute>Y!j \<le> \<acute>X!i) \<rbrace>) COEND)
 SAT [\<lbrace>n<length \<acute>X \<and> n<length \<acute>Y \<and> (\<forall>i<n. \<acute>X!i=i \<and> \<acute>Y!i=m+i) \<rbrace>,
      \<lbrace>\<ordmasculine>X=\<ordfeminine>X \<and> \<ordmasculine>Y=\<ordfeminine>Y\<rbrace>,
      \<lbrace>True\<rbrace>,
      \<lbrace>\<forall>i<n. (\<acute>X!i) mod n=i \<and> (\<forall>j<\<acute>X!i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and>
        (\<acute>Y!i<m \<longrightarrow> P(B!(\<acute>Y!i)) \<and> \<acute>Y!i\<le> m+i) \<and> (\<exists>j<n. \<acute>Y!j \<le> \<acute>X!i)\<rbrace>]"
  apply (rule Parallel)
apply (auto cong del: image_cong_simp)
apply force
apply (rule While)
    apply force
   apply force
  apply force
  apply (erule dvdE)
 apply(rule_tac pre'="\<lbrace>n<length \<acute>X \<and> n<length \<acute>Y \<and> \<acute>X ! i mod n = i \<and> (\<forall>j. j < \<acute>X ! i \<longrightarrow> j mod n = i \<longrightarrow> \<not> P (B ! j)) \<and> (\<acute>Y ! i < n * k \<longrightarrow> P (B ! (\<acute>Y ! i))) \<and> \<acute>X!i<\<acute>Y!i\<rbrace>" in Conseq)
     apply force
    apply(rule subset_refl)+
 apply(rule Cond)
    apply force
   apply(rule Basic)
      apply force
     apply force
    apply force
   apply force
  apply(rule Basic)
     apply simp
     apply clarify
     apply simp
     apply(rule allI)
     apply(rule impI)+
     apply(case_tac "X x ! i\<le> j")
      apply(drule le_imp_less_or_eq)
      apply(erule disjE)
       apply(drule_tac j=j and n=n and i=i and a="X x ! i" in mod_aux)
     apply auto
done

end
