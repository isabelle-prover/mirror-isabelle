(*  Title:      HOL/MicroJava/Comp/AuxLemmas.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2002
*)


(* Auxiliary Lemmas *)

theory AuxLemmas = JBasis:

(**********************************************************************)
(* List.thy *)
(**********************************************************************)



lemma foldr_foldl: "foldr f xs a = foldl (\<lambda> x y. (f y x)) a (rev xs)"
by (induct xs, simp, simp)

lemma foldl_foldr: "foldl f a xs = foldr (\<lambda> x y. (f y x)) (rev xs) a"
by (simp add: foldr_foldl [of "(\<lambda> x y. (f y x))" "(rev xs)"])

lemma foldr_append: "foldr f (xs @ ys) a = foldr f xs (foldr f ys a)"
by (induct xs, auto)

lemma app_nth_len [simp]: "(pre @ a # post) ! length pre = a"
by (induct "pre") auto

lemma app_nth_len_plus [simp]: "(pre @ post) ! ((length pre) + n) = post ! n"
by (induct "pre") auto

lemma app_nth_greater_len [rule_format (no_asm), simp]:
 "\<forall> ind. length pre \<le> ind \<longrightarrow> (pre @ a # post) ! (Suc ind) = (pre @ post) ! ind"
apply (induct "pre")
apply auto
apply (case_tac ind)
apply auto
done

lemma list_update_length [simp]: "(xs @ a# ys)[length xs := b] = (xs @ b# ys)"
by (induct xs, auto)


lemma length_takeWhile: "v \<in> set xs \<Longrightarrow> length (takeWhile (%z. z~=v) xs) < length xs"
by (induct xs, auto)

lemma nth_length_takeWhile [simp]: 
  "v \<in> set xs \<Longrightarrow> xs ! (length (takeWhile (%z. z~=v) xs)) = v"
by (induct xs, auto)


lemma map_fun_upd [simp]: "y \<notin> set xs \<Longrightarrow> map (f(y:=v)) xs = map f xs"
by (induct xs, auto)

lemma map_list_update [simp]:
  "\<lbrakk> x \<in> set xs; distinct xs\<rbrakk> \<Longrightarrow> 
  (map f xs) [length (takeWhile (\<lambda>z. z \<noteq> x) xs) := v] = 
  map (f(x:=v)) xs"
apply (induct xs)
apply simp
apply (case_tac "x=a")
apply auto
done


(**********************************************************************)
(* Product_Type.thy *)
(**********************************************************************)


lemma split_compose: "(split f) \<circ> (\<lambda> (a,b). ((fa a), (fb b))) =
  (\<lambda> (a,b). (f (fa a) (fb b)))"
by (simp add: split_def o_def)

lemma split_iter: "(\<lambda> (a,b,c). ((g1 a), (g2 b), (g3 c))) = 
        (\<lambda> (a,p). ((g1 a), (\<lambda> (b, c). ((g2 b), (g3 c))) p))"
by (simp add: split_def o_def)


(**********************************************************************)
(* Set.thy *)
(**********************************************************************)

lemma singleton_in_set: "A = {a} \<Longrightarrow> a \<in> A" by simp

(**********************************************************************)
(* Map.thy *)
(**********************************************************************)

lemma the_map_upd: "(the \<circ> f(x\<mapsto>v)) = (the \<circ> f)(x:=v)"
by (simp add: expand_fun_eq)

lemma map_of_in_set: 
  "(map_of xs x = None) = (x \<notin> set (map fst xs))"
by (induct xs, auto)

lemma map_map_upd [simp]: 
  "y \<notin> set xs \<Longrightarrow> map (the \<circ> f(y\<mapsto>v)) xs = map (the \<circ> f) xs"
by (simp add: the_map_upd)

lemma map_map_upds [rule_format (no_asm), simp]: 
"\<forall> f vs. (\<forall>y\<in>set ys. y \<notin> set xs) \<longrightarrow> map (the \<circ> f(ys[\<mapsto>]vs)) xs = map (the \<circ> f) xs"
apply (induct ys)
apply simp
apply (intro strip)
apply (simp only: map_upds.simps)
apply (subgoal_tac "\<forall>y\<in>set list. y \<notin> set xs")
apply (subgoal_tac "a\<notin> set xs")
apply (subgoal_tac "map (the \<circ> f(a\<mapsto>hd vs)(list[\<mapsto>]tl vs)) xs = map (the \<circ> f(a\<mapsto>hd vs)) xs")
apply (simp only:)
apply (erule map_map_upd)
apply blast
apply simp+
done

lemma map_upds_distinct [rule_format (no_asm), simp]: 
  "\<forall> f vs. length ys = length vs \<longrightarrow> distinct ys \<longrightarrow> map (the \<circ> f(ys[\<mapsto>]vs)) ys = vs"
apply (induct ys)
apply simp
apply (intro strip)
apply (case_tac vs)
apply simp
apply (simp only: map_upds.simps distinct.simps hd.simps tl.simps)
apply clarify
apply (simp only: map.simps map_map_upd)
apply simp
apply (simp add: o_def)
done


lemma map_of_map_as_map_upd [rule_format (no_asm)]: "distinct (map f zs) \<longrightarrow> 
map_of (map (\<lambda> p. (f p, g p)) zs) = empty (map f zs [\<mapsto>] map g zs)"
by (induct zs, auto)

(* In analogy to Map.map_of_SomeD *)
lemma map_upds_SomeD [rule_format (no_asm)]: 
  "\<forall> m ys. (m(xs[\<mapsto>]ys)) k = Some y \<longrightarrow> k \<in> (set xs) \<or> (m k = Some y)"
apply (induct xs)
apply simp
apply (case_tac "k = a")
apply auto
done

lemma map_of_upds_SomeD: "(map_of m (xs[\<mapsto>]ys)) k = Some y 
  \<Longrightarrow> k \<in> (set (xs @ map fst m))"
by (auto dest: map_upds_SomeD map_of_SomeD fst_in_set_lemma)


lemma map_of_map_prop [rule_format (no_asm)]: 
  "(map_of (map f xs) k = Some v) \<longrightarrow> 
  (\<forall> x \<in> set xs. (P1 x)) \<longrightarrow> 
  (\<forall> x. (P1 x) \<longrightarrow> (P2 (f x))) \<longrightarrow>
  (P2(k, v))"
by (induct xs,auto)

lemma map_of_map2: "\<forall> x \<in> set xs. (fst (f x)) = (fst x) \<Longrightarrow>
  map_of (map f xs) a = option_map (\<lambda> b. (snd (f (a, b)))) (map_of xs a)"
by (induct xs, auto)

lemma option_map_of [simp]: "(option_map f (map_of xs k) = None) = ((map_of xs k) = None)"
by (simp add: option_map_def split: option.split)



end
