(*  Title:      HOL/Bali/Table.thy
    Author:     David von Oheimb
*)
subsection \<open>Abstract tables and their implementation as lists\<close>

theory Table imports Basis begin

text \<open>
design issues:
\begin{itemize}
\item definition of table: infinite map vs. list vs. finite set
      list chosen, because:
  \begin{itemize} 
  \item[+]  a priori finite
  \item[+]  lookup is more operational than for finite set
  \item[-]  not very abstract, but function table converts it to abstract 
            mapping
  \end{itemize}
\item coding of lookup result: Some/None vs. value/arbitrary
   Some/None chosen, because:
  \begin{itemize}
  \item[++] makes definedness check possible (applies also to finite set),
     which is important for the type standard, hiding/overriding, etc.
     (though it may perhaps be possible at least for the operational semantics
      to treat programs as infinite, i.e. where classes, fields, methods etc.
      of any name are considered to be defined)
  \item[-]  sometimes awkward case distinctions, alleviated by operator 'the'
  \end{itemize}
\end{itemize}
\<close>

type_synonym ('a, 'b) table    \<comment> \<open>table with key type 'a and contents type 'b\<close>
      = "'a \<rightharpoonup> 'b"
type_synonym ('a, 'b) tables   \<comment> \<open>non-unique table with key 'a and contents 'b\<close>
      = "'a \<Rightarrow> 'b set"


subsubsection "map of / table of"

abbreviation
  table_of :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) table"   \<comment> \<open>concrete table\<close>
  where "table_of \<equiv> map_of"

translations
  (type) "('a, 'b) table" <= (type) "'a \<rightharpoonup> 'b"

(* ### To map *)
lemma map_add_find_left[simp]: "n k = None \<Longrightarrow> (m ++ n) k = m k"
  by (simp add: map_add_def)


subsubsection \<open>Conditional Override\<close>

definition cond_override :: "('b \<Rightarrow>'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b)table \<Rightarrow> ('a, 'b)table \<Rightarrow> ('a, 'b) table" where

\<comment> \<open>when merging tables old and new, only override an entry of table old when  
   the condition cond holds\<close>
"cond_override cond old new =
 (\<lambda>k.
  (case new k of
     None         \<Rightarrow> old k                       
   | Some new_val \<Rightarrow> (case old k of
                        None         \<Rightarrow> Some new_val          
                      | Some old_val \<Rightarrow> (if cond new_val old_val
                                         then Some new_val     
                                         else Some old_val))))"

lemma cond_override_empty1[simp]: "cond_override c Map.empty t = t"
  by (simp add: cond_override_def fun_eq_iff)

lemma cond_override_empty2[simp]: "cond_override c t Map.empty = t"
  by (simp add: cond_override_def fun_eq_iff)

lemma cond_override_None[simp]:
  "old k = None \<Longrightarrow> (cond_override c old new) k = new k"
  by (simp add: cond_override_def)

lemma cond_override_override:
  "\<lbrakk>old k = Some ov;new k = Some nv; C nv ov\<rbrakk> 
    \<Longrightarrow> (cond_override C old new) k = Some nv"
  by (auto simp add: cond_override_def)

lemma cond_override_noOverride:
  "\<lbrakk>old k = Some ov;new k = Some nv; \<not> (C nv ov)\<rbrakk> 
    \<Longrightarrow> (cond_override C old new) k = Some ov"
  by (auto simp add: cond_override_def)

lemma dom_cond_override: "dom (cond_override C s t) \<subseteq> dom s \<union> dom t"
  by (auto simp add: cond_override_def dom_def)

lemma finite_dom_cond_override:
 "\<lbrakk> finite (dom s); finite (dom t) \<rbrakk> \<Longrightarrow> finite (dom (cond_override C s t))"
apply (rule_tac B="dom s \<union> dom t" in finite_subset)
apply (rule dom_cond_override)
by (rule finite_UnI)


subsubsection \<open>Filter on Tables\<close>

definition filter_tab :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) table \<Rightarrow> ('a, 'b) table"
  where
    "filter_tab c t = (\<lambda>k. (case t k of 
                             None   \<Rightarrow> None
                           | Some x \<Rightarrow> if c k x then Some x else None))"

lemma filter_tab_empty[simp]: "filter_tab c Map.empty = Map.empty"
by (simp add: filter_tab_def empty_def)

lemma filter_tab_True[simp]: "filter_tab (\<lambda>x y. True) t = t"
by (simp add: fun_eq_iff filter_tab_def)

lemma filter_tab_False[simp]: "filter_tab (\<lambda>x y. False) t = Map.empty"
by (simp add: fun_eq_iff filter_tab_def empty_def)

lemma filter_tab_ran_subset: "ran (filter_tab c t) \<subseteq> ran t"
by (auto simp add: filter_tab_def ran_def)

lemma filter_tab_range_subset: "range (filter_tab c t) \<subseteq> range t \<union> {None}"
apply (auto simp add: filter_tab_def)
apply (drule sym, blast)
done

lemma finite_range_filter_tab:
  "finite (range t) \<Longrightarrow> finite (range (filter_tab c t))"
apply (rule_tac B="range t \<union> {None} " in finite_subset)
apply (rule filter_tab_range_subset)
apply (auto intro: finite_UnI)
done

lemma filter_tab_SomeD[dest!]: 
"filter_tab c t k = Some x \<Longrightarrow> (t k = Some x) \<and> c k x"
by (auto simp add: filter_tab_def)

lemma filter_tab_SomeI: "\<lbrakk>t k = Some x;C k x\<rbrakk> \<Longrightarrow>filter_tab C t k = Some x"
by (simp add: filter_tab_def)

lemma filter_tab_all_True: 
 "\<forall> k y. t k = Some y \<longrightarrow> p k y \<Longrightarrow>filter_tab p t = t"
apply (auto simp add: filter_tab_def fun_eq_iff)
done

lemma filter_tab_all_True_Some:
 "\<lbrakk>\<forall> k y. t k = Some y \<longrightarrow> p k y; t k = Some v\<rbrakk> \<Longrightarrow> filter_tab p t k = Some v"
by (auto simp add: filter_tab_def fun_eq_iff)

lemma filter_tab_all_False: 
 "\<forall> k y. t k = Some y \<longrightarrow> \<not> p k y \<Longrightarrow>filter_tab p t = Map.empty"
by (auto simp add: filter_tab_def fun_eq_iff)

lemma filter_tab_None: "t k = None \<Longrightarrow> filter_tab p t k = None"
apply (simp add: filter_tab_def fun_eq_iff)
done

lemma filter_tab_dom_subset: "dom (filter_tab C t) \<subseteq> dom t"
by (auto simp add: filter_tab_def dom_def)

lemma filter_tab_eq: "\<lbrakk>a=b\<rbrakk> \<Longrightarrow> filter_tab C a = filter_tab C b"
by (auto simp add: fun_eq_iff filter_tab_def)

lemma finite_dom_filter_tab:
"finite (dom t) \<Longrightarrow> finite (dom (filter_tab C t))"
apply (rule_tac B="dom t" in finite_subset)
by (rule filter_tab_dom_subset)


lemma filter_tab_weaken:
"\<lbrakk>\<forall> a \<in> t k: \<exists> b \<in> s k: P a b; 
  \<And> k x y. \<lbrakk>t k = Some x;s k = Some y\<rbrakk> \<Longrightarrow> cond k x \<longrightarrow> cond k y
 \<rbrakk> \<Longrightarrow> \<forall> a \<in> filter_tab cond t k: \<exists> b \<in> filter_tab cond s k: P a b"
by (force simp add: filter_tab_def)

lemma cond_override_filter: 
  "\<lbrakk>\<And> k old new. \<lbrakk>s k = Some new; t k = Some old\<rbrakk> 
    \<Longrightarrow> (\<not> overC new old \<longrightarrow>  \<not> filterC k new) \<and> 
        (overC new old \<longrightarrow> filterC k old \<longrightarrow> filterC k new)
   \<rbrakk> \<Longrightarrow>
    cond_override overC (filter_tab filterC t) (filter_tab filterC s) 
    = filter_tab filterC (cond_override overC t s)"
by (auto simp add: fun_eq_iff cond_override_def filter_tab_def )


subsubsection \<open>Misc\<close>

lemma Ball_set_table: "(\<forall> (x,y)\<in> set l. P x y) \<Longrightarrow> \<forall> x. \<forall> y\<in> map_of l x: P x y"
apply (erule rev_mp)
apply (induct l)
apply simp
apply (simp (no_asm))
apply auto
done

lemma Ball_set_tableD: 
  "\<lbrakk>(\<forall> (x,y)\<in> set l. P x y); x \<in> set_option (table_of l xa)\<rbrakk> \<Longrightarrow> P xa x"
apply (frule Ball_set_table)
by auto

declare map_of_SomeD [elim]

lemma table_of_Some_in_set:
"table_of l k = Some x \<Longrightarrow> (k,x) \<in> set l"
by auto

lemma set_get_eq: 
  "unique l \<Longrightarrow> (k, the (table_of l k)) \<in> set l = (table_of l k \<noteq> None)"
by (auto dest!: weak_map_of_SomeI)

lemma inj_Pair_const2: "inj (\<lambda>k. (k, C))"
apply (rule inj_onI)
apply auto
done

lemma table_of_mapconst_SomeI:
  "\<lbrakk>table_of t k = Some y'; snd y=y'; fst y=c\<rbrakk> \<Longrightarrow>
    table_of (map (\<lambda>(k,x). (k,c,x)) t) k = Some y"
  by (induct t) auto

lemma table_of_mapconst_NoneI:
  "\<lbrakk>table_of t k = None\<rbrakk> \<Longrightarrow>
    table_of (map (\<lambda>(k,x). (k,c,x)) t) k = None"
  by (induct t) auto

lemmas table_of_map2_SomeI = inj_Pair_const2 [THEN map_of_mapk_SomeI]

lemma table_of_map_SomeI: "table_of t k = Some x \<Longrightarrow>
   table_of (map (\<lambda>(k,x). (k, f x)) t) k = Some (f x)"
  by (induct t) auto

lemma table_of_remap_SomeD:
  "table_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) \<Longrightarrow>
    table_of t (k, k') = Some x"
  by (induct t) auto

lemma table_of_mapf_Some:
  "\<forall>x y. f x = f y \<longrightarrow> x = y \<Longrightarrow>
    table_of (map (\<lambda>(k,x). (k,f x)) t) k = Some (f x) \<Longrightarrow> table_of t k = Some x"
  by (induct t) auto

lemma table_of_mapf_SomeD [dest!]:
  "table_of (map (\<lambda>(k,x). (k, f x)) t) k = Some z \<Longrightarrow> (\<exists>y\<in>table_of t k: z=f y)"
  by (induct t) auto

lemma table_of_mapf_NoneD [dest!]:
  "table_of (map (\<lambda>(k,x). (k, f x)) t) k = None \<Longrightarrow> (table_of t k = None)"
  by (induct t) auto

lemma table_of_mapkey_SomeD [dest!]:
  "table_of (map (\<lambda>(k,x). ((k,C),x)) t) (k,D) = Some x \<Longrightarrow> C = D \<and> table_of t k = Some x"
  by (induct t) auto

lemma table_of_mapkey_SomeD2 [dest!]:
  "table_of (map (\<lambda>(k,x). ((k,C),x)) t) ek = Some x \<Longrightarrow>
    C = snd ek \<and> table_of t (fst ek) = Some x"
  by (induct t) auto

lemma table_append_Some_iff: "table_of (xs@ys) k = Some z = 
 (table_of xs k = Some z \<or> (table_of xs k = None \<and> table_of ys k = Some z))"
apply (simp)
apply (rule map_add_Some_iff)
done

lemma table_of_filter_unique_SomeD [rule_format (no_asm)]:
  "table_of (filter P xs) k = Some z \<Longrightarrow> unique xs \<longrightarrow> table_of xs k = Some z"
  by (induct xs) (auto del: map_of_SomeD intro!: map_of_SomeD)


definition Un_tables :: "('a, 'b) tables set \<Rightarrow> ('a, 'b) tables"
  where "Un_tables ts = (\<lambda>k. \<Union>t\<in>ts. t k)"

definition overrides_t :: "('a, 'b) tables \<Rightarrow> ('a, 'b) tables \<Rightarrow> ('a, 'b) tables"
    (infixl \<open>\<oplus>\<oplus>\<close> 100)
  where "s \<oplus>\<oplus> t = (\<lambda>k. if t k = {} then s k else t k)"

definition
  hidings_entails :: "('a, 'b) tables \<Rightarrow> ('a, 'c) tables \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
    (\<open>_ hidings _ entails _\<close> 20)
  where "(t hidings s entails R) = (\<forall>k. \<forall>x\<in>t k. \<forall>y\<in>s k. R x y)"

definition
  \<comment> \<open>variant for unique table:\<close>
  hiding_entails :: "('a, 'b) table  \<Rightarrow> ('a, 'c) table  \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
    (\<open>_ hiding _ entails _\<close>  20)
  where "(t hiding  s entails R) = (\<forall>k. \<forall>x\<in>t k: \<forall>y\<in>s k: R x y)"

definition
  \<comment> \<open>variant for a unique table and conditional overriding:\<close>
  cond_hiding_entails :: "('a, 'b) table  \<Rightarrow> ('a, 'c) table  
                          \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"  
                          (\<open>_ hiding _ under _ entails _\<close>  20)
  where "(t hiding  s under C entails R) = (\<forall>k. \<forall>x\<in>t k: \<forall>y\<in>s k: C x y \<longrightarrow> R x y)"


subsubsection "Untables"

lemma Un_tablesI [intro]:  "t \<in> ts \<Longrightarrow> x \<in> t k \<Longrightarrow> x \<in> Un_tables ts k"
  by (auto simp add: Un_tables_def)

lemma Un_tablesD [dest!]: "x \<in> Un_tables ts k \<Longrightarrow> \<exists>t. t \<in> ts \<and> x \<in> t k"
  by (auto simp add: Un_tables_def)

lemma Un_tables_empty [simp]: "Un_tables {} = (\<lambda>k. {})"
  by (simp add: Un_tables_def)


subsubsection "overrides"

lemma empty_overrides_t [simp]: "(\<lambda>k. {}) \<oplus>\<oplus> m = m"
  by (simp add: overrides_t_def)

lemma overrides_empty_t [simp]: "m \<oplus>\<oplus> (\<lambda>k. {}) = m"
  by (simp add: overrides_t_def)

lemma overrides_t_Some_iff: 
  "(x \<in> (s \<oplus>\<oplus> t) k) = (x \<in> t k \<or> t k = {} \<and> x \<in> s k)"
  by (simp add: overrides_t_def)

lemmas overrides_t_SomeD = overrides_t_Some_iff [THEN iffD1, dest!]

lemma overrides_t_right_empty [simp]: "n k = {} \<Longrightarrow> (m \<oplus>\<oplus> n) k = m k"  
  by (simp add: overrides_t_def)

lemma overrides_t_find_right [simp]: "n k \<noteq> {} \<Longrightarrow> (m \<oplus>\<oplus> n) k = n k"  
  by (simp add: overrides_t_def)


subsubsection "hiding entails"

lemma hiding_entailsD: 
  "t hiding s entails R \<Longrightarrow> t k = Some x \<Longrightarrow> s k = Some y \<Longrightarrow> R x y"
  by (simp add: hiding_entails_def)

lemma empty_hiding_entails [simp]: "Map.empty hiding s entails R"
  by (simp add: hiding_entails_def)

lemma hiding_empty_entails [simp]: "t hiding Map.empty entails R"
  by (simp add: hiding_entails_def)


subsubsection "cond hiding entails"

lemma cond_hiding_entailsD: 
"\<lbrakk>t hiding s under C entails R; t k = Some x; s k = Some y; C x y\<rbrakk> \<Longrightarrow> R x y"
by (simp add: cond_hiding_entails_def)

lemma empty_cond_hiding_entails[simp]: "Map.empty hiding s under C entails R"
by (simp add: cond_hiding_entails_def)

lemma cond_hiding_empty_entails[simp]: "t hiding Map.empty under C entails R"
by (simp add: cond_hiding_entails_def)

lemma hidings_entailsD: "\<lbrakk>t hidings s entails R; x \<in> t k; y \<in> s k\<rbrakk> \<Longrightarrow> R x y"
by (simp add: hidings_entails_def)

lemma hidings_empty_entails [intro!]: "t hidings (\<lambda>k. {}) entails R"
apply (unfold hidings_entails_def)
apply (simp (no_asm))
done

lemma empty_hidings_entails [intro!]:
  "(\<lambda>k. {}) hidings s entails R"apply (unfold hidings_entails_def)
by (simp (no_asm))


(*###TO Map?*)
primrec atleast_free :: "('a \<rightharpoonup> 'b) => nat => bool"
where
  "atleast_free m 0 = True"
| atleast_free_Suc: "atleast_free m (Suc n) = (\<exists>a. m a = None \<and> (\<forall>b. atleast_free (m(a\<mapsto>b)) n))"

lemma atleast_free_weaken [rule_format (no_asm)]: 
  "\<forall>m. atleast_free m (Suc n) \<longrightarrow> atleast_free m n"
apply (induct_tac "n")
apply (simp (no_asm))
apply clarify
apply (simp (no_asm))
apply (drule atleast_free_Suc [THEN iffD1])
apply fast
done

lemma atleast_free_SucI: 
"[| h a = None; \<forall>obj. atleast_free (h(a|->obj)) n |] ==> atleast_free h (Suc n)"
by force

declare fun_upd_apply [simp del]
lemma atleast_free_SucD_lemma [rule_format (no_asm)]: 
"\<forall>m a. m a = None \<longrightarrow> (\<forall>c. atleast_free (m(a\<mapsto>c)) n) \<longrightarrow>
  (\<forall>b d. a \<noteq> b \<longrightarrow> atleast_free (m(b\<mapsto>d)) n)"
apply (induct_tac "n")
apply  auto
apply (rule_tac x = "a" in exI)
apply  (rule conjI)
apply  (force simp add: fun_upd_apply)
apply (erule_tac V = "m a = None" in thin_rl)
apply clarify
apply (subst fun_upd_twist)
apply  (erule not_sym)
apply (rename_tac "ba")
apply (drule_tac x = "ba" in spec)
apply clarify
apply (tactic "smp_tac \<^context> 2 1")
apply (erule (1) notE impE)
apply (case_tac "aa = b")
apply fast+
done
declare fun_upd_apply [simp]

lemma atleast_free_SucD: "atleast_free h (Suc n) ==> atleast_free (h(a|->b)) n"
apply auto
apply (case_tac "aa = a")
apply auto
apply (erule atleast_free_SucD_lemma)
apply auto
done

declare atleast_free_Suc [simp del]

end
