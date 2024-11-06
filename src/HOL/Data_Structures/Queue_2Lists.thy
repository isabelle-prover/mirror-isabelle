(* Author: Tobias Nipkow *)

section \<open>Queue Implementation via 2 Lists\<close>

theory Queue_2Lists
imports
  Queue_Spec
  Time_Funs
begin

text \<open>Definitions:\<close>

type_synonym 'a queue = "'a list \<times> 'a list"

fun norm :: "'a queue \<Rightarrow> 'a queue" where
"norm (fs,rs) = (if fs = [] then (itrev rs [], []) else (fs,rs))"

fun enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"enq a (fs,rs) = norm(fs, a # rs)"

fun deq :: "'a queue \<Rightarrow> 'a queue" where
"deq (fs,rs) = (if fs = [] then (fs,rs) else norm(tl fs,rs))"

fun first :: "'a queue \<Rightarrow> 'a" where
"first (a # fs,rs) = a"

fun is_empty :: "'a queue \<Rightarrow> bool" where
"is_empty (fs,rs) = (fs = [])"

fun list :: "'a queue \<Rightarrow> 'a list" where
"list (fs,rs) = fs @ rev rs"

fun invar :: "'a queue \<Rightarrow> bool" where
"invar (fs,rs) = (fs = [] \<longrightarrow> rs = [])"


text \<open>Implementation correctness:\<close>

interpretation Queue
where empty = "([],[])" and enq = enq and deq = deq and first = first
and is_empty = is_empty and list = list and invar = invar
proof (standard, goal_cases)
  case 1 show ?case by (simp)
next
  case (2 q) thus ?case by(cases q) (simp)
next
  case (3 q) thus ?case by(cases q) (simp add: itrev_Nil)
next
  case (4 q) thus ?case by(cases q) (auto simp: neq_Nil_conv)
next
  case (5 q) thus ?case by(cases q) (auto)
next
  case 6 show ?case by(simp)
next
  case (7 q) thus ?case by(cases q) (simp)
next
  case (8 q) thus ?case by(cases q) (simp)
qed

text \<open>Running times:\<close>

time_fun norm
time_fun enq
time_fun deq

text \<open>Amortized running times:\<close>

fun \<Phi> :: "'a queue \<Rightarrow> nat" where
"\<Phi>(fs,rs) = length rs"

lemma a_enq: "T_enq a (fs,rs) + \<Phi>(enq a (fs,rs)) - \<Phi>(fs,rs) \<le> 2"
by(auto simp: T_itrev)

lemma a_deq: "T_deq (fs,rs) + \<Phi>(deq (fs,rs)) - \<Phi>(fs,rs) \<le> 1"
by(auto simp: T_itrev T_tl)

end
