(*  Title:      HOL/Hoare/SchorrWaite.thy
    Author:     Farhad Mehta
    Copyright   2003 TUM
*)

section \<open>Proof of the Schorr-Waite graph marking algorithm\<close>

theory SchorrWaite
  imports HeapSyntax
begin

subsection \<open>Machinery for the Schorr-Waite proof\<close>

definition
  \<comment> \<open>Relations induced by a mapping\<close>
  rel :: "('a \<Rightarrow> 'a ref) \<Rightarrow> ('a \<times> 'a) set"
  where "rel m = {(x,y). m x = Ref y}"

definition
  relS :: "('a \<Rightarrow> 'a ref) set \<Rightarrow> ('a \<times> 'a) set"
  where "relS M = (\<Union>m \<in> M. rel m)"

definition
  addrs :: "'a ref set \<Rightarrow> 'a set"
  where "addrs P = {a. Ref a \<in> P}"

definition
  reachable :: "('a \<times> 'a) set \<Rightarrow> 'a ref set \<Rightarrow> 'a set"
  where "reachable r P = (r\<^sup>* `` addrs P)"

lemmas rel_defs = relS_def rel_def

text \<open>Rewrite rules for relations induced by a mapping\<close>

lemma self_reachable: "b \<in> B \<Longrightarrow> b \<in> R\<^sup>* `` B"
apply blast
done

lemma oneStep_reachable: "b \<in> R``B \<Longrightarrow> b \<in> R\<^sup>* `` B"
apply blast
done

lemma still_reachable: "\<lbrakk>B\<subseteq>Ra\<^sup>*``A; \<forall> (x,y) \<in> Rb-Ra. y\<in> (Ra\<^sup>*``A)\<rbrakk> \<Longrightarrow> Rb\<^sup>* `` B \<subseteq> Ra\<^sup>* `` A "
apply (clarsimp simp only:Image_iff)
apply (erule rtrancl_induct)
 apply blast
apply (subgoal_tac "(y, z) \<in> Ra\<union>(Rb-Ra)")
 apply (erule UnE)
 apply (auto intro:rtrancl_into_rtrancl)
apply blast
done

lemma still_reachable_eq: "\<lbrakk> A\<subseteq>Rb\<^sup>*``B; B\<subseteq>Ra\<^sup>*``A; \<forall> (x,y) \<in> Ra-Rb. y \<in>(Rb\<^sup>*``B); \<forall> (x,y) \<in> Rb-Ra. y\<in> (Ra\<^sup>*``A)\<rbrakk> \<Longrightarrow> Ra\<^sup>*``A =  Rb\<^sup>*``B "
apply (rule equalityI)
 apply (erule still_reachable ,assumption)+
done

lemma reachable_null: "reachable mS {Null} = {}"
apply (simp add: reachable_def addrs_def)
done

lemma reachable_empty: "reachable mS {} = {}"
apply (simp add: reachable_def addrs_def)
done

lemma reachable_union: "(reachable mS aS \<union> reachable mS bS) = reachable mS (aS \<union> bS)"
apply (simp add: reachable_def rel_defs addrs_def)
apply blast
done

lemma reachable_union_sym: "reachable r (insert a aS) = (r\<^sup>* `` addrs {a}) \<union> reachable r aS"
apply (simp add: reachable_def rel_defs addrs_def)
apply blast
done

lemma rel_upd1: "(a,b) \<notin> rel (r(q:=t)) \<Longrightarrow> (a,b) \<in> rel r \<Longrightarrow> a=q"
apply (rule classical)
apply (simp add:rel_defs fun_upd_apply)
done

lemma rel_upd2: "(a,b)  \<notin> rel r \<Longrightarrow> (a,b) \<in> rel (r(q:=t)) \<Longrightarrow> a=q"
apply (rule classical)
apply (simp add:rel_defs fun_upd_apply)
done

definition
  \<comment> \<open>Restriction of a relation\<close>
  restr ::"('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set"
    (\<open>(\<open>notation=\<open>mixfix relation restriction\<close>\<close>_/ | _)\<close> [50, 51] 50)
  where "restr r m = {(x,y). (x,y) \<in> r \<and> \<not> m x}"

text \<open>Rewrite rules for the restriction of a relation\<close>

lemma restr_identity[simp]:
 " (\<forall>x. \<not> m x) \<Longrightarrow> (R |m) = R"
by (auto simp add:restr_def)

lemma restr_rtrancl[simp]: " \<lbrakk>m l\<rbrakk> \<Longrightarrow> (R | m)\<^sup>* `` {l} = {l}"
by (auto simp add:restr_def elim:converse_rtranclE)

lemma [simp]: " \<lbrakk>m l\<rbrakk> \<Longrightarrow> (l,x) \<in> (R | m)\<^sup>* = (l=x)"
by (auto simp add:restr_def elim:converse_rtranclE)

lemma restr_upd: "((rel (r (q := t)))|(m(q := True))) = ((rel (r))|(m(q := True))) "
apply (auto simp:restr_def rel_def fun_upd_apply)
apply (rename_tac a b)
apply (case_tac "a=q")
 apply auto
done

lemma restr_un: "((r \<union> s)|m) = (r|m) \<union> (s|m)"
  by (auto simp add:restr_def)

lemma rel_upd3: "(a, b) \<notin> (r|(m(q := t))) \<Longrightarrow> (a,b) \<in> (r|m) \<Longrightarrow> a = q "
apply (rule classical)
apply (simp add:restr_def fun_upd_apply)
done

definition
  \<comment> \<open>A short form for the stack mapping function for List\<close>
  S :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a ref) \<Rightarrow> ('a \<Rightarrow> 'a ref) \<Rightarrow> ('a \<Rightarrow> 'a ref)"
  where "S c l r = (\<lambda>x. if c x then r x else l x)"

text \<open>Rewrite rules for Lists using S as their mapping\<close>

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S c l r) p stack = List (S (c(a:=x)) (l(a:=y)) (r(a:=z))) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S c l (r(a:=z))) p stack = List (S c l r) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S c (l(a:=z)) r) p stack = List (S c l r) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S (c(a:=z)) l r) p stack = List (S c l r) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

primrec
  \<comment> \<open>Recursive definition of what is means for a the graph/stack structure to be reconstructible\<close>
  stkOk :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a ref) \<Rightarrow> ('a \<Rightarrow> 'a ref) \<Rightarrow> ('a \<Rightarrow> 'a ref) \<Rightarrow> ('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow>'a list \<Rightarrow>  bool"
where
  stkOk_nil:  "stkOk c l r iL iR t [] = True"
| stkOk_cons:
    "stkOk c l r iL iR t (p#stk) = (stkOk c l r iL iR (Ref p) (stk) \<and> 
      iL p = (if c p then l p else t) \<and>
      iR p = (if c p then t else r p))"

text \<open>Rewrite rules for stkOk\<close>

lemma [simp]: "\<And>t. \<lbrakk> x \<notin> set xs; Ref x\<noteq>t \<rbrakk> \<Longrightarrow>
  stkOk (c(x := f)) l r iL iR t xs = stkOk c l r iL iR t xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>t. \<lbrakk> x \<notin> set xs; Ref x\<noteq>t \<rbrakk> \<Longrightarrow>
 stkOk c (l(x := g)) r iL iR t xs = stkOk c l r iL iR t xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>t. \<lbrakk> x \<notin> set xs; Ref x\<noteq>t \<rbrakk> \<Longrightarrow>
 stkOk c l (r(x := g)) iL iR t xs = stkOk c l r iL iR t xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma stkOk_r_rewrite [simp]: "\<And>x. x \<notin> set xs \<Longrightarrow>
  stkOk c l (r(x := g)) iL iR (Ref x) xs = stkOk c l r iL iR (Ref x) xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>x. x \<notin> set xs \<Longrightarrow>
 stkOk c (l(x := g)) r iL iR (Ref x) xs = stkOk c l r iL iR (Ref x) xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>x. x \<notin> set xs \<Longrightarrow>
 stkOk (c(x := g)) l r iL iR (Ref x) xs = stkOk c l r iL iR (Ref x) xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done


subsection \<open>The Schorr-Waite algorithm\<close>

theorem SchorrWaiteAlgorithm: 
"VARS c m l r t p q root
 {R = reachable (relS {l, r}) {root} \<and> (\<forall>x. \<not> m x) \<and> iR = r \<and> iL = l} 
 t := root; p := Null;
 WHILE p \<noteq> Null \<or> t \<noteq> Null \<and> \<not> t^.m
 INV {\<exists>stack.
          List (S c l r) p stack \<and>                                      \<comment> \<open>\<open>i1\<close>\<close>
          (\<forall>x \<in> set stack. m x) \<and>                                       \<comment> \<open>\<open>i2\<close>\<close>
          R = reachable (relS{l, r}) {t,p} \<and>                            \<comment> \<open>\<open>i3\<close>\<close>
          (\<forall>x. x \<in> R \<and> \<not>m x \<longrightarrow>                                         \<comment> \<open>\<open>i4\<close>\<close>
                 x \<in> reachable (relS{l,r}|m) ({t}\<union>set(map r stack))) \<and>
          (\<forall>x. m x \<longrightarrow> x \<in> R) \<and>                                         \<comment> \<open>\<open>i5\<close>\<close>
          (\<forall>x. x \<notin> set stack \<longrightarrow> r x = iR x \<and> l x = iL x) \<and>             \<comment> \<open>\<open>i6\<close>\<close>
          (stkOk c l r iL iR t stack)                                   \<comment> \<open>\<open>i7\<close>\<close>}
 DO IF t = Null \<or> t^.m
      THEN IF p^.c
               THEN q := t; t := p; p := p^.r; t^.r := q                \<comment> \<open>\<open>pop\<close>\<close>
               ELSE q := t; t := p^.r; p^.r := p^.l;                    \<comment> \<open>\<open>swing\<close>\<close>
                        p^.l := q; p^.c := True          FI    
      ELSE q := p; p := t; t := t^.l; p^.l := q;                        \<comment> \<open>\<open>push\<close>\<close>
               p^.m := True; p^.c := False            FI       OD
 {(\<forall>x. (x \<in> R) = m x) \<and> (r = iR \<and> l = iL) }"
  (is "Valid
         {(c, m, l, r, t, p, q, root). ?Pre c m l r root}
         (Seq _ (Seq _ (While {(c, m, l, r, t, p, q, root). ?whileB m t p} _)))
         (Aseq _ (Aseq _ (Awhile {(c, m, l, r, t, p, q, root). ?inv c m l r t p} _ _))) _")
proof (vcg)
  {

    fix c m l r t p q root
    assume "?Pre c m l r root"
    thus "?inv c m l r root Null"  by (auto simp add: reachable_def addrs_def)
  next

    fix c m l r t p q
    let "\<exists>stack. ?Inv stack"  =  "?inv c m l r t p"
    assume a: "?inv c m l r t p \<and> \<not>(p \<noteq> Null \<or> t \<noteq> Null \<and> \<not> t^.m)"  
    then obtain stack where inv: "?Inv stack" by blast
    from a have pNull: "p = Null" and tDisj: "t=Null \<or> (t\<noteq>Null \<and> t^.m )" by auto
    let "?I1 \<and> _ \<and> _ \<and> ?I4 \<and> ?I5 \<and> ?I6 \<and> _"  =  "?Inv stack"
    from inv have i1: "?I1" and i4: "?I4" and i5: "?I5" and i6: "?I6" by simp+
    from pNull i1 have stackEmpty: "stack = []" by simp
    from tDisj i4 have RisMarked[rule_format]: "\<forall>x.  x \<in> R \<longrightarrow> m x"  by(auto simp: reachable_def addrs_def stackEmpty)
    from i5 i6 show "(\<forall>x.(x \<in> R) = m x) \<and> r = iR \<and> l = iL"  by(auto simp: stackEmpty fun_eq_iff intro:RisMarked)

  next   
      fix c m l r t p q root
      let "\<exists>stack. ?Inv stack"  =  "?inv c m l r t p"
      let "\<exists>stack. ?popInv stack"  =  "?inv c m l (r(p \<rightarrow> t)) p (p^.r)"
      let "\<exists>stack. ?swInv stack"  =
        "?inv (c(p \<rightarrow> True)) m (l(p \<rightarrow> t)) (r(p \<rightarrow> p^.l)) (p^.r) p"
      let "\<exists>stack. ?puInv stack"  =
        "?inv (c(t \<rightarrow> False)) (m(t \<rightarrow> True)) (l(t \<rightarrow> p)) r (t^.l) t"
      let "?ifB1"  =  "(t = Null \<or> t^.m)"
      let "?ifB2"  =  "p^.c" 

      assume "(\<exists>stack.?Inv stack) \<and> ?whileB m t p"
      then obtain stack where inv: "?Inv stack" and whileB: "?whileB m t p" by blast
      let "?I1 \<and> ?I2 \<and> ?I3 \<and> ?I4 \<and> ?I5 \<and> ?I6 \<and> ?I7" = "?Inv stack"
      from inv have i1: "?I1" and i2: "?I2" and i3: "?I3" and i4: "?I4"
                  and i5: "?I5" and i6: "?I6" and i7: "?I7" by simp+        
      have stackDist: "distinct (stack)" using i1 by (rule List_distinct)

      show "(?ifB1 \<longrightarrow> (?ifB2 \<longrightarrow> (\<exists>stack.?popInv stack)) \<and> 
                            (\<not>?ifB2 \<longrightarrow> (\<exists>stack.?swInv stack)) ) \<and>
              (\<not>?ifB1 \<longrightarrow> (\<exists>stack.?puInv stack))"
      proof - 
        {
          assume ifB1: "t = Null \<or> t^.m" and ifB2: "p^.c"
          from ifB1 whileB have pNotNull: "p \<noteq> Null" by auto
          then obtain addr_p where addr_p_eq: "p = Ref addr_p" by auto
          with i1 obtain stack_tl where stack_eq: "stack = (addr p) # stack_tl"
            by auto
          with i2 have m_addr_p: "p^.m" by auto
          have stackDist: "distinct (stack)" using i1 by (rule List_distinct)
          from stack_eq stackDist have p_notin_stack_tl: "addr p \<notin> set stack_tl" by simp
          let "?poI1\<and> ?poI2\<and> ?poI3\<and> ?poI4\<and> ?poI5\<and> ?poI6\<and> ?poI7" = "?popInv stack_tl"
          have "?popInv stack_tl"
          proof -

            \<comment> \<open>List property is maintained:\<close>
            from i1 p_notin_stack_tl ifB2
            have poI1: "List (S c l (r(p \<rightarrow> t))) (p^.r) stack_tl" 
              by(simp add: addr_p_eq stack_eq, simp add: S_def)

            moreover
            \<comment> \<open>Everything on the stack is marked:\<close>
            from i2 have poI2: "\<forall> x \<in> set stack_tl. m x" by (simp add:stack_eq)
            moreover

            \<comment> \<open>Everything is still reachable:\<close>
            let "(R = reachable ?Ra ?A)" = "?I3"
            let "?Rb" = "(relS {l, r(p \<rightarrow> t)})"
            let "?B" = "{p, p^.r}"
            \<comment> \<open>Our goal is \<open>R = reachable ?Rb ?B\<close>.\<close>
            have "?Ra\<^sup>* `` addrs ?A = ?Rb\<^sup>* `` addrs ?B" (is "?L = ?R")
            proof
              show "?L \<subseteq> ?R"
              proof (rule still_reachable)
                show "addrs ?A \<subseteq> ?Rb\<^sup>* `` addrs ?B" by(fastforce simp:addrs_def relS_def rel_def addr_p_eq 
                     intro:oneStep_reachable Image_iff[THEN iffD2])
                show "\<forall>(x,y) \<in> ?Ra-?Rb. y \<in> (?Rb\<^sup>* `` addrs ?B)" by (clarsimp simp:relS_def) 
                     (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd1)
              qed
              show "?R \<subseteq> ?L"
              proof (rule still_reachable)
                show "addrs ?B \<subseteq> ?Ra\<^sup>* `` addrs ?A"
                  by(fastforce simp:addrs_def rel_defs addr_p_eq 
                      intro:oneStep_reachable Image_iff[THEN iffD2])
              next
                show "\<forall>(x, y)\<in>?Rb-?Ra. y\<in>(?Ra\<^sup>*``addrs ?A)"
                  by (clarsimp simp:relS_def) 
                     (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd2)
              qed
            qed
            with i3 have poI3: "R = reachable ?Rb ?B"  by (simp add:reachable_def) 
            moreover

            \<comment> \<open>If it is reachable and not marked, it is still reachable using...\<close>
            let "\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Ra ?A"  =  ?I4        
            let "?Rb" = "relS {l, r(p \<rightarrow> t)} | m"
            let "?B" = "{p} \<union> set (map (r(p \<rightarrow> t)) stack_tl)"
            \<comment> \<open>Our goal is \<open>\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Rb ?B\<close>.\<close>
            let ?T = "{t, p^.r}"

            have "?Ra\<^sup>* `` addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
            proof (rule still_reachable)
              have rewrite: "\<forall>s\<in>set stack_tl. (r(p \<rightarrow> t)) s = r s"
                by (auto simp add:p_notin_stack_tl intro:fun_upd_other) 
              show "addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
                by (fastforce cong:map_cong simp:stack_eq addrs_def rewrite intro:self_reachable)
              show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``(addrs ?B \<union> addrs ?T))"
                by (clarsimp simp:restr_def relS_def) 
                  (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd1)
            qed
            \<comment> \<open>We now bring a term from the right to the left of the subset relation.\<close>
            hence subset: "?Ra\<^sup>* `` addrs ?A - ?Rb\<^sup>* `` addrs ?T \<subseteq> ?Rb\<^sup>* `` addrs ?B"
              by blast
            have poI4: "\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Rb ?B"
            proof (rule allI, rule impI)
              fix x
              assume a: "x \<in> R \<and> \<not> m x"
              \<comment> \<open>First, a disjunction on \<^term>\<open>p^.r\<close> used later in the proof\<close>
              have pDisj:"p^.r = Null \<or> (p^.r \<noteq> Null \<and> p^.r^.m)" using poI1 poI2 
                by auto
              \<comment> \<open>\<^term>\<open>x\<close> belongs to the left hand side of @{thm[source] subset}:\<close>
              have incl: "x \<in> ?Ra\<^sup>*``addrs ?A" using  a i4 by (simp only:reachable_def, clarsimp)
              have excl: "x \<notin> ?Rb\<^sup>*`` addrs ?T" using pDisj ifB1 a by (auto simp add:addrs_def)
              \<comment> \<open>And therefore also belongs to the right hand side of @{thm[source]subset},\<close>
              \<comment> \<open>which corresponds to our goal.\<close>
              from incl excl subset  show "x \<in> reachable ?Rb ?B" by (auto simp add:reachable_def)
            qed
            moreover

            \<comment> \<open>If it is marked, then it is reachable\<close>
            from i5 have poI5: "\<forall>x. m x \<longrightarrow> x \<in> R" .
            moreover

            \<comment> \<open>If it is not on the stack, then its \<^term>\<open>l\<close> and \<^term>\<open>r\<close> fields are unchanged\<close>
            from i7 i6 ifB2 
            have poI6: "\<forall>x. x \<notin> set stack_tl \<longrightarrow> (r(p \<rightarrow> t)) x = iR x \<and> l x = iL x" 
              by(auto simp: addr_p_eq stack_eq fun_upd_apply)

            moreover

            \<comment> \<open>If it is on the stack, then its \<^term>\<open>l\<close> and \<^term>\<open>r\<close> fields can be reconstructed\<close>
            from p_notin_stack_tl i7 have poI7: "stkOk c l (r(p \<rightarrow> t)) iL iR p stack_tl"
              by (clarsimp simp:stack_eq addr_p_eq)

            ultimately show "?popInv stack_tl" by simp
          qed
          hence "\<exists>stack. ?popInv stack" ..
        }
        moreover

        \<comment> \<open>Proofs of the Swing and Push arm follow.\<close>
        \<comment> \<open>Since they are in principle simmilar to the Pop arm proof,\<close>
        \<comment> \<open>we show fewer comments and use frequent pattern matching.\<close>
        {
          \<comment> \<open>Swing arm\<close>
          assume ifB1: "?ifB1" and nifB2: "\<not>?ifB2"
          from ifB1 whileB have pNotNull: "p \<noteq> Null" by clarsimp
          then obtain addr_p where addr_p_eq: "p = Ref addr_p" by clarsimp
          with i1 obtain stack_tl where stack_eq: "stack = (addr p) # stack_tl" by clarsimp
          with i2 have m_addr_p: "p^.m" by clarsimp
          from stack_eq stackDist have p_notin_stack_tl: "(addr p) \<notin> set stack_tl"
            by simp
          let "?swI1\<and>?swI2\<and>?swI3\<and>?swI4\<and>?swI5\<and>?swI6\<and>?swI7" = "?swInv stack"
          have "?swInv stack"
          proof -
            
            \<comment> \<open>List property is maintained:\<close>
            from i1 p_notin_stack_tl nifB2
            have swI1: "?swI1"
              by (simp add:addr_p_eq stack_eq, simp add:S_def)
            moreover
            
            \<comment> \<open>Everything on the stack is marked:\<close>
            from i2
            have swI2: "?swI2" .
            moreover
            
            \<comment> \<open>Everything is still reachable:\<close>
            let "R = reachable ?Ra ?A" = "?I3"
            let "R = reachable ?Rb ?B" = "?swI3"
            have "?Ra\<^sup>* `` addrs ?A = ?Rb\<^sup>* `` addrs ?B"
            proof (rule still_reachable_eq)
              show "addrs ?A \<subseteq> ?Rb\<^sup>* `` addrs ?B"
                by(fastforce simp:addrs_def rel_defs addr_p_eq intro:oneStep_reachable Image_iff[THEN iffD2])
            next
              show "addrs ?B \<subseteq> ?Ra\<^sup>* `` addrs ?A"
                by(fastforce simp:addrs_def rel_defs addr_p_eq intro:oneStep_reachable Image_iff[THEN iffD2])
            next
              show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``addrs ?B)"
                by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd1)
            next
              show "\<forall>(x, y)\<in>?Rb-?Ra. y\<in>(?Ra\<^sup>*``addrs ?A)"
                by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd2)
            qed
            with i3
            have swI3: "?swI3" by (simp add:reachable_def) 
            moreover

            \<comment> \<open>If it is reachable and not marked, it is still reachable using...\<close>
            let "\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Ra ?A" = ?I4
            let "\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Rb ?B" = ?swI4
            let ?T = "{t}"
            have "?Ra\<^sup>*``addrs ?A \<subseteq> ?Rb\<^sup>*``(addrs ?B \<union> addrs ?T)"
            proof (rule still_reachable)
              have rewrite: "(\<forall>s\<in>set stack_tl. (r(addr p := l(addr p))) s = r s)"
                by (auto simp add:p_notin_stack_tl intro:fun_upd_other)
              show "addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
                by (fastforce cong:map_cong simp:stack_eq addrs_def rewrite intro:self_reachable)
            next
              show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``(addrs ?B \<union> addrs ?T))"
                by (clarsimp simp:relS_def restr_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd1)
            qed
            then have subset: "?Ra\<^sup>*``addrs ?A - ?Rb\<^sup>*``addrs ?T \<subseteq> ?Rb\<^sup>*``addrs ?B"
              by blast
            have ?swI4
            proof (rule allI, rule impI)
              fix x
              assume a: "x \<in> R \<and>\<not> m x"
              with i4 addr_p_eq stack_eq  have inc: "x \<in> ?Ra\<^sup>*``addrs ?A" 
                by (simp only:reachable_def, clarsimp)
              with ifB1 a 
              have exc: "x \<notin> ?Rb\<^sup>*`` addrs ?T" 
                by (auto simp add:addrs_def)
              from inc exc subset  show "x \<in> reachable ?Rb ?B" 
                by (auto simp add:reachable_def)
            qed
            moreover
            
            \<comment> \<open>If it is marked, then it is reachable\<close>
            from i5
            have "?swI5" .
            moreover

            \<comment> \<open>If it is not on the stack, then its \<^term>\<open>l\<close> and \<^term>\<open>r\<close> fields are unchanged\<close>
            from i6 stack_eq
            have "?swI6"
              by clarsimp           
            moreover

            \<comment> \<open>If it is on the stack, then its \<^term>\<open>l\<close> and \<^term>\<open>r\<close> fields can be reconstructed\<close>
            from stackDist i7 nifB2 
            have "?swI7"
              by (clarsimp simp:addr_p_eq stack_eq)

            ultimately show ?thesis by auto
          qed
          then have "\<exists>stack. ?swInv stack" by blast
        }
        moreover

        {
          \<comment> \<open>Push arm\<close>
          assume nifB1: "\<not>?ifB1"
          from nifB1 whileB have tNotNull: "t \<noteq> Null" by clarsimp
          then obtain addr_t where addr_t_eq: "t = Ref addr_t" by clarsimp
          with i1 obtain new_stack where new_stack_eq: "new_stack = (addr t) # stack" by clarsimp
          from tNotNull nifB1 have n_m_addr_t: "\<not> (t^.m)" by clarsimp
          with i2 have t_notin_stack: "(addr t) \<notin> set stack" by blast
          let "?puI1\<and>?puI2\<and>?puI3\<and>?puI4\<and>?puI5\<and>?puI6\<and>?puI7" = "?puInv new_stack"
          have "?puInv new_stack"
          proof -
            
            \<comment> \<open>List property is maintained:\<close>
            from i1 t_notin_stack
            have puI1: "?puI1"
              by (simp add:addr_t_eq new_stack_eq, simp add:S_def)
            moreover
            
            \<comment> \<open>Everything on the stack is marked:\<close>
            from i2
            have puI2: "?puI2" 
              by (simp add:new_stack_eq fun_upd_apply)
            moreover
            
            \<comment> \<open>Everything is still reachable:\<close>
            let "R = reachable ?Ra ?A" = "?I3"
            let "R = reachable ?Rb ?B" = "?puI3"
            have "?Ra\<^sup>* `` addrs ?A = ?Rb\<^sup>* `` addrs ?B"
            proof (rule still_reachable_eq)
              show "addrs ?A \<subseteq> ?Rb\<^sup>* `` addrs ?B"
                by(fastforce simp:addrs_def rel_defs addr_t_eq intro:oneStep_reachable Image_iff[THEN iffD2])
            next
              show "addrs ?B \<subseteq> ?Ra\<^sup>* `` addrs ?A"
                by(fastforce simp:addrs_def rel_defs addr_t_eq intro:oneStep_reachable Image_iff[THEN iffD2])
            next
              show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``addrs ?B)"
                by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd1)
            next
              show "\<forall>(x, y)\<in>?Rb-?Ra. y\<in>(?Ra\<^sup>*``addrs ?A)"
                by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd2)
            qed
            with i3
            have puI3: "?puI3" by (simp add:reachable_def) 
            moreover
            
            \<comment> \<open>If it is reachable and not marked, it is still reachable using...\<close>
            let "\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Ra ?A" = ?I4
            let "\<forall>x. x \<in> R \<and> \<not> ?new_m x \<longrightarrow> x \<in> reachable ?Rb ?B" = ?puI4
            let ?T = "{t}"
            have "?Ra\<^sup>*``addrs ?A \<subseteq> ?Rb\<^sup>*``(addrs ?B \<union> addrs ?T)"
            proof (rule still_reachable)
              show "addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
                by (fastforce simp:new_stack_eq addrs_def intro:self_reachable)
            next
              show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``(addrs ?B \<union> addrs ?T))"
                by (clarsimp simp:relS_def new_stack_eq restr_un restr_upd) 
                   (fastforce simp add:rel_def Image_iff restr_def addrs_def fun_upd_apply addr_t_eq dest:rel_upd3)
            qed
            then have subset: "?Ra\<^sup>*``addrs ?A - ?Rb\<^sup>*``addrs ?T \<subseteq> ?Rb\<^sup>*``addrs ?B"
              by blast
            have ?puI4
            proof (rule allI, rule impI)
              fix x
              assume a: "x \<in> R \<and> \<not> ?new_m x"
              have xDisj: "x=(addr t) \<or> x\<noteq>(addr t)" by simp
              with i4 a have inc: "x \<in> ?Ra\<^sup>*``addrs ?A"
                by (fastforce simp:addr_t_eq addrs_def reachable_def intro:self_reachable)
              have exc: "x \<notin> ?Rb\<^sup>*`` addrs ?T"
                using xDisj a n_m_addr_t
                by (clarsimp simp add:addrs_def addr_t_eq) 
              from inc exc subset  show "x \<in> reachable ?Rb ?B" 
                by (auto simp add:reachable_def)
            qed  
            moreover
            
            \<comment> \<open>If it is marked, then it is reachable\<close>
            from i5
            have "?puI5"
              by (auto simp:addrs_def i3 reachable_def addr_t_eq fun_upd_apply intro:self_reachable)
            moreover
            
            \<comment> \<open>If it is not on the stack, then its \<^term>\<open>l\<close> and \<^term>\<open>r\<close> fields are unchanged\<close>
            from i6 
            have "?puI6"
              by (simp add:new_stack_eq)
            moreover

            \<comment> \<open>If it is on the stack, then its \<^term>\<open>l\<close> and \<^term>\<open>r\<close> fields can be reconstructed\<close>
            from stackDist i6 t_notin_stack i7
            have "?puI7" by (clarsimp simp:addr_t_eq new_stack_eq)

            ultimately show ?thesis by auto
          qed
          then have "\<exists>stack. ?puInv stack" by blast

        }
        ultimately show ?thesis by blast
      qed
    }
  qed

end
