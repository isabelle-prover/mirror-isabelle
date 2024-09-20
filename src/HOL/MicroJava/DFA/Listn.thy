(*  Title:      HOL/MicroJava/DFA/Listn.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

section \<open>Fixed Length Lists\<close>

theory Listn
imports Err
begin

definition list :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
"list n A == {xs. length xs = n & set xs <= A}"

definition le :: "'a ord \<Rightarrow> ('a list)ord" where
"le r == list_all2 (%x y. x <=_r y)"

abbreviation
  lesublist_syntax :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"
       (\<open>(_ /<=[_] _)\<close> [50, 0, 51] 50)
  where "x <=[r] y == x <=_(le r) y"

abbreviation
  lesssublist_syntax :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"
       (\<open>(_ /<[_] _)\<close> [50, 0, 51] 50)
  where "x <[r] y == x <_(le r) y"

definition map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
"map2 f == (%xs ys. map (case_prod f) (zip xs ys))"

abbreviation
  plussublist_syntax :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
       (\<open>(_ /+[_] _)\<close> [65, 0, 66] 65)
  where "x +[f] y == x +_(map2 f) y"

primrec coalesce :: "'a err list \<Rightarrow> 'a list err" where
  "coalesce [] = OK[]"
| "coalesce (ex#exs) = Err.sup (#) ex (coalesce exs)"

definition sl :: "nat \<Rightarrow> 'a sl \<Rightarrow> 'a list sl" where
"sl n == %(A,r,f). (list n A, le r, map2 f)"

definition sup :: "('a \<Rightarrow> 'b \<Rightarrow> 'c err) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list err" where
"sup f == %xs ys. if size xs = size ys then coalesce(xs +[f] ys) else Err"

definition upto_esl :: "nat \<Rightarrow> 'a esl \<Rightarrow> 'a list esl" where
"upto_esl m == %(A,r,f). (\<Union>{list n A |n. n <= m}, le r, sup f)"

lemmas [simp] = set_update_subsetI

lemma unfold_lesub_list:
  "xs <=[r] ys == Listn.le r xs ys"
  by (simp add: lesub_def)

lemma Nil_le_conv [iff]:
  "([] <=[r] ys) = (ys = [])"
apply (unfold lesub_def Listn.le_def)
apply simp
done

lemma Cons_notle_Nil [iff]: 
  "~ x#xs <=[r] []"
apply (unfold lesub_def Listn.le_def)
apply simp
done


lemma Cons_le_Cons [iff]:
  "x#xs <=[r] y#ys = (x <=_r y & xs <=[r] ys)"
apply (unfold lesub_def Listn.le_def)
apply simp
done

lemma Cons_less_Conss [simp]:
  "order r \<Longrightarrow> 
  x#xs <_(Listn.le r) y#ys = 
  (x <_r y & xs <=[r] ys  |  x = y & xs <_(Listn.le r) ys)"
apply (unfold lesssub_def)
apply blast
done  

lemma list_update_le_cong:
  "\<lbrakk> i<size xs; xs <=[r] ys; x <=_r y \<rbrakk> \<Longrightarrow> xs[i:=x] <=[r] ys[i:=y]"
apply (unfold unfold_lesub_list)
apply (unfold Listn.le_def)
apply (simp add: list_all2_conv_all_nth nth_list_update)
done


lemma le_listD:
  "\<lbrakk> xs <=[r] ys; p < size xs \<rbrakk> \<Longrightarrow> xs!p <=_r ys!p"
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_conv_all_nth)
done

lemma le_list_refl:
  "\<forall>x. x <=_r x \<Longrightarrow> xs <=[r] xs"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done

lemma le_list_trans:
  "\<lbrakk> order r; xs <=[r] ys; ys <=[r] zs \<rbrakk> \<Longrightarrow> xs <=[r] zs"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply clarify
apply simp
apply (blast intro: order_trans)
done

lemma le_list_antisym:
  "\<lbrakk> order r; xs <=[r] ys; ys <=[r] xs \<rbrakk> \<Longrightarrow> xs = ys"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply (rule nth_equalityI)
 apply blast
apply clarify
apply simp
apply (blast intro: order_antisym)
done

lemma order_listI [simp, intro!]:
  "order r \<Longrightarrow> order(Listn.le r)"
apply (subst Semilat.order_def)
apply (blast intro: le_list_refl le_list_trans le_list_antisym
             dest: order_refl)
done


lemma lesub_list_impl_same_size [simp]:
  "xs <=[r] ys \<Longrightarrow> size ys = size xs"  
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_conv_all_nth)
done 

lemma lesssub_list_impl_same_size:
  "xs <_(Listn.le r) ys \<Longrightarrow> size ys = size xs"
apply (unfold lesssub_def)
apply auto
done  

lemma le_list_appendI:
  "\<And>b c d. a <=[r] b \<Longrightarrow> c <=[r] d \<Longrightarrow> a@c <=[r] b@d"
apply (induct a)
 apply simp
apply (case_tac b)
apply auto
done

lemma le_listI:
  "length a = length b \<Longrightarrow> (\<And>n. n < length a \<Longrightarrow> a!n <=_r b!n) \<Longrightarrow> a <=[r] b"
  apply (unfold lesub_def Listn.le_def)
  apply (simp add: list_all2_conv_all_nth)
  done

lemma listI:
  "\<lbrakk> length xs = n; set xs <= A \<rbrakk> \<Longrightarrow> xs \<in> list n A"
apply (unfold list_def)
apply blast
done

lemma listE_length [simp]:
   "xs \<in> list n A \<Longrightarrow> length xs = n"
apply (unfold list_def)
apply blast
done 

lemma less_lengthI:
  "\<lbrakk> xs \<in> list n A; p < n \<rbrakk> \<Longrightarrow> p < length xs"
  by simp

lemma listE_set [simp]:
  "xs \<in> list n A \<Longrightarrow> set xs <= A"
apply (unfold list_def)
apply blast
done 

lemma list_0 [simp]:
  "list 0 A = {[]}"
apply (unfold list_def)
apply auto
done 

lemma in_list_Suc_iff: 
  "(xs \<in> list (Suc n) A) = (\<exists>y\<in> A. \<exists>ys\<in> list n A. xs = y#ys)"
apply (unfold list_def)
apply (case_tac "xs")
apply auto
done 

lemma Cons_in_list_Suc [iff]:
  "(x#xs \<in> list (Suc n) A) = (x\<in> A & xs \<in> list n A)"
apply (simp add: in_list_Suc_iff)
done 

lemma list_not_empty:
  "\<exists>a. a\<in> A \<Longrightarrow> \<exists>xs. xs \<in> list n A"
apply (induct "n")
 apply simp
apply (simp add: in_list_Suc_iff)
apply blast
done


lemma nth_in [rule_format, simp]:
  "\<forall>i n. length xs = n \<longrightarrow> set xs <= A \<longrightarrow> i < n \<longrightarrow> (xs!i) \<in> A"
apply (induct "xs")
 apply simp
apply (simp add: nth_Cons split: nat.split)
done

lemma listE_nth_in:
  "\<lbrakk> xs \<in> list n A; i < n \<rbrakk> \<Longrightarrow> (xs!i) \<in> A"
  by auto


lemma listn_Cons_Suc [elim!]:
  "l#xs \<in> list n A \<Longrightarrow> (\<And>n'. n = Suc n' \<Longrightarrow> l \<in> A \<Longrightarrow> xs \<in> list n' A \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases n) auto

lemma listn_appendE [elim!]:
  "a@b \<in> list n A \<Longrightarrow> (\<And>n1 n2. n=n1+n2 \<Longrightarrow> a \<in> list n1 A \<Longrightarrow> b \<in> list n2 A \<Longrightarrow> P) \<Longrightarrow> P" 
proof -
  have "\<And>n. a@b \<in> list n A \<Longrightarrow> \<exists>n1 n2. n=n1+n2 \<and> a \<in> list n1 A \<and> b \<in> list n2 A"
    (is "\<And>n. ?list a n \<Longrightarrow> \<exists>n1 n2. ?P a n n1 n2")
  proof (induct a)
    fix n assume "?list [] n"
    hence "?P [] n 0 n" by simp
    thus "\<exists>n1 n2. ?P [] n n1 n2" by fast
  next
    fix n l ls
    assume "?list (l#ls) n"
    then obtain n' where n: "n = Suc n'" "l \<in> A" and list_n': "ls@b \<in> list n' A" by fastforce
    assume "\<And>n. ls @ b \<in> list n A \<Longrightarrow> \<exists>n1 n2. n = n1 + n2 \<and> ls \<in> list n1 A \<and> b \<in> list n2 A"
    hence "\<exists>n1 n2. n' = n1 + n2 \<and> ls \<in> list n1 A \<and> b \<in> list n2 A" by this (rule list_n')
    then obtain n1 n2 where "n' = n1 + n2" "ls \<in> list n1 A" "b \<in> list n2 A" by fast
    with n have "?P (l#ls) n (n1+1) n2" by simp
    thus "\<exists>n1 n2. ?P (l#ls) n n1 n2" by fastforce
  qed
  moreover
  assume "a@b \<in> list n A" "\<And>n1 n2. n=n1+n2 \<Longrightarrow> a \<in> list n1 A \<Longrightarrow> b \<in> list n2 A \<Longrightarrow> P"
  ultimately
  show ?thesis by blast
qed


lemma listt_update_in_list [simp, intro!]:
  "\<lbrakk> xs \<in> list n A; x\<in> A \<rbrakk> \<Longrightarrow> xs[i := x] \<in> list n A"
apply (unfold list_def)
apply simp
done 

lemma plus_list_Nil [simp]:
  "[] +[f] xs = []"
apply (unfold plussub_def map2_def)
apply simp
done 

lemma plus_list_Cons [simp]:
  "(x#xs) +[f] ys = (case ys of [] \<Rightarrow> [] | y#ys \<Rightarrow> (x +_f y)#(xs +[f] ys))"
  by (simp add: plussub_def map2_def split: list.split)

lemma length_plus_list [rule_format, simp]:
  "\<forall>ys. length(xs +[f] ys) = min(length xs) (length ys)"
apply (induct xs)
 apply simp
apply clarify
apply (simp (no_asm_simp) split: list.split)
done

lemma nth_plus_list [rule_format, simp]:
  "\<forall>xs ys i. length xs = n \<longrightarrow> length ys = n \<longrightarrow> i<n \<longrightarrow> 
  (xs +[f] ys)!i = (xs!i) +_f (ys!i)"
apply (induct n)
 apply simp
apply clarify
apply (case_tac xs)
 apply simp
apply (force simp add: nth_Cons split: list.split nat.split)
done


lemma (in Semilat) plus_list_ub1 [rule_format]:
 "\<lbrakk> set xs <= A; set ys <= A; size xs = size ys \<rbrakk> 
  \<Longrightarrow> xs <=[r] xs +[f] ys"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done

lemma (in Semilat) plus_list_ub2:
 "\<lbrakk>set xs <= A; set ys <= A; size xs = size ys \<rbrakk>
  \<Longrightarrow> ys <=[r] xs +[f] ys"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done

lemma (in Semilat) plus_list_lub [rule_format]:
shows "\<forall>xs ys zs. set xs <= A \<longrightarrow> set ys <= A \<longrightarrow> set zs <= A 
  \<longrightarrow> size xs = n & size ys = n \<longrightarrow> 
  xs <=[r] zs & ys <=[r] zs \<longrightarrow> xs +[f] ys <=[r] zs"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done

lemma (in Semilat) list_update_incr [rule_format]:
 "x\<in> A \<Longrightarrow> set xs <= A \<longrightarrow> 
  (\<forall>i. i<size xs \<longrightarrow> xs <=[r] xs[i := x +_f xs!i])"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply (induct xs)
 apply simp
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp add: nth_Cons split: nat.split)
done

lemma acc_le_listI [intro!]:
  "\<lbrakk> order r; acc r \<rbrakk> \<Longrightarrow> acc(Listn.le r)"
apply (unfold acc_def)
apply (subgoal_tac
 "wf(UN n. {(ys,xs). size xs = n \<and> size ys = n \<and> xs <_(Listn.le r) ys})")
 apply (erule wf_subset)
 apply (blast intro: lesssub_list_impl_same_size)
apply (rule wf_UN)
 prefer 2
 apply (rename_tac m n)
 apply (case_tac "m=n")
  apply simp
 apply (fast intro!: equals0I dest: not_sym)
apply (rename_tac n)
apply (induct_tac n)
 apply (simp add: lesssub_def cong: conj_cong)
apply (rename_tac k)
apply (simp add: wf_eq_minimal)
apply (simp (no_asm) add: length_Suc_conv cong: conj_cong)
apply clarify
apply (rename_tac M m)
apply (case_tac "\<exists>x xs. size xs = k \<and> x#xs \<in> M")
 prefer 2
 apply (erule thin_rl)
 apply (erule thin_rl)
 apply blast
apply (erule_tac x = "{a. \<exists>xs. size xs = k \<and> a#xs \<in> M}" in allE)
apply (erule impE)
 apply blast
apply (thin_tac "\<exists>x xs. P x xs" for P)
apply clarify
apply (rename_tac maxA xs)
apply (erule_tac x = "{ys. size ys = size xs \<and> maxA#ys \<in> M}" in allE)
apply (erule impE)
 apply blast
apply clarify
apply (thin_tac "m \<in> M")
  apply (thin_tac "maxA#xs \<in> M")
apply (rule bexI)
 prefer 2
 apply assumption
apply clarify
apply simp
apply blast
done

lemma closed_listI:
  "closed S f \<Longrightarrow> closed (list n S) (map2 f)"
apply (unfold closed_def)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply simp
done


lemma Listn_sl_aux:
assumes "semilat (A, r, f)" shows "semilat (Listn.sl n (A,r,f))"
proof -
  interpret Semilat A r f using assms by (rule Semilat.intro)
show ?thesis
apply (unfold Listn.sl_def)
apply (simp (no_asm) only: semilat_Def split_conv)
apply (rule conjI)
 apply simp
apply (rule conjI)
 apply (simp only: closedI closed_listI)
apply (simp (no_asm) only: list_def)
apply (simp (no_asm_simp) add: plus_list_ub1 plus_list_ub2 plus_list_lub)
done
qed

lemma Listn_sl: "\<And>L. semilat L \<Longrightarrow> semilat (Listn.sl n L)"
 by(simp add: Listn_sl_aux split_tupled_all)

lemma coalesce_in_err_list [rule_format]:
  "\<forall>xes. xes \<in> list n (err A) \<longrightarrow> coalesce xes \<in> err(list n A)"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp (no_asm) add: plussub_def Err.sup_def lift2_def split: err.split)
apply force
done 

lemma lem: "\<And>x xs. x +_(#) xs = x#xs"
  by (simp add: plussub_def)

lemma coalesce_eq_OK1_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow> 
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow> 
  (\<forall>zs. coalesce (xs +[f] ys) = OK zs \<longrightarrow> xs <=[r] zs))"
apply (induct n)
  apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK1)
done

lemma coalesce_eq_OK2_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow> 
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow> 
  (\<forall>zs. coalesce (xs +[f] ys) = OK zs \<longrightarrow> ys <=[r] zs))"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK2)
done 

lemma lift2_le_ub:
  "\<lbrakk> semilat(err A, Err.le r, lift2 f); x\<in> A; y\<in> A; x +_f y = OK z; 
      u\<in> A; x <=_r u; y <=_r u \<rbrakk> \<Longrightarrow> z <=_r u"
apply (unfold semilat_Def plussub_def err_def)
apply (simp add: lift2_def)
apply clarify
apply (rotate_tac -3)
apply (erule thin_rl)
apply (erule thin_rl)
apply force
done

lemma coalesce_eq_OK_ub_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow> 
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow> 
  (\<forall>zs us. coalesce (xs +[f] ys) = OK zs \<and> xs <=[r] us \<and> ys <=[r] us 
           \<and> us \<in> list n A \<longrightarrow> zs <=[r] us))"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp (no_asm_use) split: err.split_asm add: lem Err.sup_def lift2_def)
apply clarify
apply (rule conjI)
 apply (blast intro: lift2_le_ub)
apply blast
done 

lemma lift2_eq_ErrD:
  "\<lbrakk> x +_f y = Err; semilat(err A, Err.le r, lift2 f); x\<in> A; y\<in> A \<rbrakk> 
  \<Longrightarrow> ~(\<exists>u\<in> A. x <=_r u & y <=_r u)"
  by (simp add: OK_plus_OK_eq_Err_conv [THEN iffD1])


lemma coalesce_eq_Err_D [rule_format]:
  "\<lbrakk> semilat(err A, Err.le r, lift2 f) \<rbrakk> 
  \<Longrightarrow> \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow> 
      coalesce (xs +[f] ys) = Err \<longrightarrow> 
      \<not>(\<exists>zs\<in> list n A. xs <=[r] zs \<and> ys <=[r] zs))"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
 apply (blast dest: lift2_eq_ErrD)
done 

lemma closed_err_lift2_conv:
  "closed (err A) (lift2 f) = (\<forall>x\<in> A. \<forall>y\<in> A. x +_f y \<in> err A)"
apply (unfold closed_def)
apply (simp add: err_def)
done 

lemma closed_map2_list [rule_format]:
  "closed (err A) (lift2 f) \<Longrightarrow> 
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow> 
  map2 f xs ys \<in> list n (err A))"
apply (unfold map2_def)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp add: plussub_def closed_err_lift2_conv)
done

lemma closed_lift2_sup:
  "closed (err A) (lift2 f) \<Longrightarrow> 
  closed (err (list n A)) (lift2 (sup f))"
  by (fastforce  simp add: closed_def plussub_def sup_def lift2_def
                          coalesce_in_err_list closed_map2_list
                split: err.split)

lemma err_semilat_sup:
  "err_semilat (A,r,f) \<Longrightarrow> 
  err_semilat (list n A, Listn.le r, sup f)"
apply (unfold Err.sl_def)
apply (simp only: split_conv)
apply (simp (no_asm) only: semilat_Def plussub_def)
apply (simp (no_asm_simp) only: Semilat.closedI [OF Semilat.intro] closed_lift2_sup)
apply (rule conjI)
 apply (drule Semilat.orderI [OF Semilat.intro])
 apply simp
apply (simp (no_asm) only: unfold_lesub_err Err.le_def err_def sup_def lift2_def)
apply (simp (no_asm_simp) add: coalesce_eq_OK1_D coalesce_eq_OK2_D split: err.split)
apply (blast intro: coalesce_eq_OK_ub_D dest: coalesce_eq_Err_D)
done 

lemma err_semilat_upto_esl:
  "\<And>L. err_semilat L \<Longrightarrow> err_semilat(upto_esl m L)"
apply (unfold Listn.upto_esl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (fastforce intro!: err_semilat_UnionI err_semilat_sup
                dest: lesub_list_impl_same_size 
                simp add: plussub_def Listn.sup_def)
done

end
