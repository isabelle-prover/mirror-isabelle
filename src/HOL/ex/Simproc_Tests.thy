(*  Title:      HOL/ex/Simproc_Tests.thy
    Author:     Brian Huffman
*)

section \<open>Testing of arithmetic simprocs\<close>

theory Simproc_Tests
imports Main
begin

text \<open>
  This theory tests the various simprocs defined in \<^file>\<open>~~/src/HOL/Nat.thy\<close> and
  \<^file>\<open>~~/src/HOL/Numeral_Simprocs.thy\<close>. Many of the tests are derived from commented-out code
  originally found in \<^file>\<open>~~/src/HOL/Tools/numeral_simprocs.ML\<close>.
\<close>

subsection \<open>ML bindings\<close>

ML \<open>
  fun test ctxt procs =
    CHANGED (asm_simp_tac (put_simpset HOL_basic_ss ctxt |> fold Simplifier.add_proc procs) 1)
\<close>

subsection \<open>Cancellation simprocs from \<open>Nat.thy\<close>\<close>

notepad begin
  fix a b c d :: nat
  {
    assume "b = Suc c" have "a + b = Suc (c + a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_sums\<close>]\<close>) fact
  next
    assume "b < Suc c" have "a + b < Suc (c + a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natless_cancel_sums\<close>]\<close>) fact
  next
    assume "b \<le> Suc c" have "a + b \<le> Suc (c + a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_sums\<close>]\<close>) fact
  next
    assume "b - Suc c = d" have "a + b - Suc (c + a) = d"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_sums\<close>]\<close>) fact
  }
end

schematic_goal "\<And>(y::?'b::size). size (?x::?'a::size) \<le> size y + size ?x"
  by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_sums\<close>]\<close>) (rule le0)
(* TODO: test more simprocs with schematic variables *)

subsection \<open>Abelian group cancellation simprocs\<close>

notepad begin
  fix a b c u :: "'a::ab_group_add"
  {
    assume "(a + 0) - (b + 0) = u" have "(a + c) - (b + c) = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>group_cancel_diff\<close>]\<close>) fact
  next
    assume "a + 0 = b + 0" have "a + c = b + c"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>group_cancel_eq\<close>]\<close>) fact
  }
end
(* TODO: more tests for Groups.group_cancel_{add,diff,eq,less,le} *)

subsection \<open>\<open>int_combine_numerals\<close>\<close>

(* FIXME: int_combine_numerals often unnecessarily regroups addition
and rewrites subtraction to negation. Ideally it should behave more
like Groups.abel_cancel_sum, preserving the shape of terms as much as
possible. *)

notepad begin
  fix a b c d oo uu i j k l u v w x y z :: "'a::comm_ring_1"
  {
    assume "a + - b = u" have "(a + c) - (b + c) = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "10 + (2 * l + oo) = uu"
    have "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "-3 + (i + (j + k)) = y"
    have "(i + j + 12 + k) - 15 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "7 + (i + (j + k)) = y"
    have "(i + j + 12 + k) - 5 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "-4 * (u * v) + (2 * x + y) = w"
    have "(2*x - (u*v) + y) - v*3*u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "2 * x * u * v + y = w"
    have "(2*x*u*v + (u*v)*4 + y) - v*u*4 = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "3 * (u * v) + (2 * x * u * v + y) = w"
    have "(2*x*u*v + (u*v)*4 + y) - v*u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "-3 * (u * v) + (- (x * u * v) + - y) = w"
    have "u*v - (x*u*v + (u*v)*4 + y) = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "a + - c = d"
    have "a + -(b+c) + b = d"
      apply (simp only: minus_add_distrib)
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "-2 * b + (a + - c) = d"
    have "a + -(b+c) - b = d"
      apply (simp only: minus_add_distrib)
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "-7 + (i + (j + (k + (- u + - y)))) = z"
    have "(i + j + -2 + k) - (u + 5 + y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "-27 + (i + (j + k)) = y"
    have "(i + j + -12 + k) - 15 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "27 + (i + (j + k)) = y"
    have "(i + j + 12 + k) - -15 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  next
    assume "3 + (i + (j + k)) = y"
    have "(i + j + -12 + k) - -15 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>inteq_cancel_numerals\<close>\<close>

notepad begin
  fix i j k u vv w y z w' y' z' :: "'a::comm_ring_1"
  {
    assume "u = 0" have "2*u = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>inteq_cancel_numerals\<close>]\<close>) fact
(* conclusion matches Rings.ring_1_no_zero_divisors_class.mult_cancel_right2 *)
  next
    assume "i + (j + k) = 3 + (u + y)"
    have "(i + j + 12 + k) = u + 15 + y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>inteq_cancel_numerals\<close>]\<close>) fact
  next
    assume "7 + (j + (i + k)) = y"
    have "(i + j*2 + 12 + k) = j + 5 + y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>inteq_cancel_numerals\<close>]\<close>) fact
  next
    assume "u + (6*z + (4*y + 6*w)) = 6*z' + (4*y' + (6*w' + vv))"
    have "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + vv"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_combine_numerals\<close>, \<^simproc>\<open>inteq_cancel_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>intless_cancel_numerals\<close>\<close>

notepad begin
  fix b c i j k u y :: "'a::linordered_idom"
  {
    assume "y < 2 * b" have "y - b < b"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>intless_cancel_numerals\<close>]\<close>) fact
  next
    assume "c + y < 4 * b" have "y - (3*b + c) < b - 2*c"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>intless_cancel_numerals\<close>]\<close>) fact
  next
    assume "i + (j + k) < 8 + (u + y)"
    have "(i + j + -3 + k) < u + 5 + y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>intless_cancel_numerals\<close>]\<close>) fact
  next
    assume "9 + (i + (j + k)) < u + y"
    have "(i + j + 3 + k) < u + -6 + y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>intless_cancel_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>ring_eq_cancel_numeral_factor\<close>\<close>

notepad begin
  fix x y :: "'a::{idom,ring_char_0}"
  {
    assume "3*x = 4*y" have "9*x = 12 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "-3*x = 4*y" have "-99*x = 132 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "111*x = -44*y" have "999*x = -396 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "11*x = 9*y" have "-99*x = -81 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "2*x = y" have "-2 * x = -1 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "2*x = y" have "-2 * x = -y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_numeral_factor\<close>]\<close>) fact
  }
end

subsection \<open>\<open>int_div_cancel_numeral_factors\<close>\<close>

notepad begin
  fix x y z :: "'a::{unique_euclidean_semiring,comm_ring_1,ring_char_0}"
  {
    assume "(3*x) div (4*y) = z" have "(9*x) div (12*y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_numeral_factors\<close>]\<close>) fact
  next
    assume "(-3*x) div (4*y) = z" have "(-99*x) div (132*y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_numeral_factors\<close>]\<close>) fact
  next
    assume "(111*x) div (-44*y) = z" have "(999*x) div (-396*y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_numeral_factors\<close>]\<close>) fact
  next
    assume "(11*x) div (9*y) = z" have "(-99*x) div (-81*y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_numeral_factors\<close>]\<close>) fact
  next
    assume "(2*x) div y = z"
    have "(-2 * x) div (-1 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_numeral_factors\<close>]\<close>) fact
  }
end

subsection \<open>\<open>ring_less_cancel_numeral_factor\<close>\<close>

notepad begin
  fix x y :: "'a::linordered_idom"
  {
    assume "3*x < 4*y" have "9*x < 12 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_less_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "-3*x < 4*y" have "-99*x < 132 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_less_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "111*x < -44*y" have "999*x < -396 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_less_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "9*y < 11*x" have "-99*x < -81 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_less_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "y < 2*x" have "-2 * x < -y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_less_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "23*y < x" have "-x < -23 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_less_cancel_numeral_factor\<close>]\<close>) fact
  }
end

subsection \<open>\<open>ring_le_cancel_numeral_factor\<close>\<close>

notepad begin
  fix x y :: "'a::linordered_idom"
  {
    assume "3*x \<le> 4*y" have "9*x \<le> 12 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "-3*x \<le> 4*y" have "-99*x \<le> 132 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "111*x \<le> -44*y" have "999*x \<le> -396 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "9*y \<le> 11*x" have "-99*x \<le> -81 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "y \<le> 2*x" have "-2 * x \<le> -1 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "23*y \<le> x" have "-x \<le> -23 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "y \<le> 0" have "0 \<le> y * -2"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "- x \<le> y" have "- (2 * x) \<le> 2*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_le_cancel_numeral_factor\<close>]\<close>) fact
  }
end

subsection \<open>\<open>divide_cancel_numeral_factor\<close>\<close>

notepad begin
  fix x y z :: "'a::{field,ring_char_0}"
  {
    assume "(3*x) / (4*y) = z" have "(9*x) / (12 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "(-3*x) / (4*y) = z" have "(-99*x) / (132 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "(111*x) / (-44*y) = z" have "(999*x) / (-396 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "(11*x) / (9*y) = z" have "(-99*x) / (-81 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "(2*x) / y = z" have "(-2 * x) / (-1 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_numeral_factor\<close>]\<close>) fact
  }
end

subsection \<open>\<open>ring_eq_cancel_factor\<close>\<close>

notepad begin
  fix a b c d k x y :: "'a::idom"
  {
    assume "k = 0 \<or> x = y" have "x*k = k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "k = 0 \<or> 1 = y" have "k = k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "b = 0 \<or> a*c = 1" have "a*(b*c) = b"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "a = 0 \<or> b = 0 \<or> c = d*x" have "a*(b*c) = d*b*(x*a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "k = 0 \<or> x = y" have "x*k = k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "k = 0 \<or> 1 = y" have "k = k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>ring_eq_cancel_factor\<close>]\<close>) fact
  }
end

subsection \<open>\<open>int_div_cancel_factor\<close>\<close>

notepad begin
  fix a b c d k uu x y :: "'a::unique_euclidean_semiring"
  {
    assume "(if k = 0 then 0 else x div y) = uu"
    have "(x*k) div (k*y) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_factor\<close>]\<close>) fact
  next
    assume "(if k = 0 then 0 else 1 div y) = uu"
    have "(k) div (k*y) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_factor\<close>]\<close>) fact
  next
    assume "(if b = 0 then 0 else a * c) = uu"
    have "(a*(b*c)) div b = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_factor\<close>]\<close>) fact
  next
    assume "(if a = 0 then 0 else if b = 0 then 0 else c div (d * x)) = uu"
    have "(a*(b*c)) div (d*b*(x*a)) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>int_div_cancel_factor\<close>]\<close>) fact
  }
end

lemma shows "a*(b*c)/(y*z) = d*(b::'a::linordered_field)*(x*a)/z"
oops \<comment> \<open>FIXME: need simproc to cover this case\<close>

subsection \<open>\<open>divide_cancel_factor\<close>\<close>

notepad begin
  fix a b c d k uu x y :: "'a::field"
  {
    assume "(if k = 0 then 0 else x / y) = uu"
    have "(x*k) / (k*y) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_factor\<close>]\<close>) fact
  next
    assume "(if k = 0 then 0 else 1 / y) = uu"
    have "(k) / (k*y) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_factor\<close>]\<close>) fact
  next
    assume "(if b = 0 then 0 else a * c) = uu"
    have "(a*(b*c)) / b = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_factor\<close>]\<close>) fact
  next
    assume "(if a = 0 then 0 else if b = 0 then 0 else c / (d * x)) = uu"
    have "(a*(b*c)) / (d*b*(x*a)) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>divide_cancel_factor\<close>]\<close>) fact
  }
end

lemma
  fixes a b c d x y z :: "'a::linordered_field"
  shows "a*(b*c)/(y*z) = d*(b)*(x*a)/z"
oops \<comment> \<open>FIXME: need simproc to cover this case\<close>

subsection \<open>\<open>linordered_ring_less_cancel_factor\<close>\<close>

notepad begin
  fix x y z :: "'a::linordered_idom"
  {
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> x*z < y*z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>linordered_ring_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> x*z < z*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>linordered_ring_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> z*x < y*z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>linordered_ring_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> z*x < z*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>linordered_ring_less_cancel_factor\<close>]\<close>) fact
  next
    txt "This simproc now uses the simplifier to prove that terms to
      be canceled are positive/negative."
    assume z_pos: "0 < z"
    assume "x < y" have "z*x < z*y"
      by (tactic \<open>CHANGED (asm_simp_tac (put_simpset HOL_basic_ss \<^context>
        |> Simplifier.add_proc \<^simproc>\<open>linordered_ring_less_cancel_factor\<close>
        |> Simplifier.add_simp @{thm z_pos}) 1)\<close>) fact
  }
end

subsection \<open>\<open>linordered_ring_le_cancel_factor\<close>\<close>

notepad begin
  fix x y z :: "'a::linordered_idom"
  {
    assume "0 < z \<Longrightarrow> x \<le> y" have "0 < z \<Longrightarrow> x*z \<le> y*z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>linordered_ring_le_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < z \<Longrightarrow> x \<le> y" have "0 < z \<Longrightarrow> z*x \<le> z*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>linordered_ring_le_cancel_factor\<close>]\<close>) fact
  }
end

subsection \<open>\<open>field_combine_numerals\<close>\<close>

notepad begin
  fix x y z uu :: "'a::{field,ring_char_0}"
  {
    assume "5 / 6 * x = uu" have "x / 2 + x / 3 = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>field_combine_numerals\<close>]\<close>) fact
  next
    assume "6 / 9 * x + y = uu" have "x / 3 + y + x / 3 = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>field_combine_numerals\<close>]\<close>) fact
  next
    assume "9 / 9 * x = uu" have "2 * x / 3 + x / 3 = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>field_combine_numerals\<close>]\<close>) fact
  next
    assume "y + z = uu"
    have "x / 2 + y - 3 * x / 6 + z = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>field_combine_numerals\<close>]\<close>) fact
  next
    assume "1 / 15 * x + y = uu"
    have "7 * x / 5 + y - 4 * x / 3 = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>field_combine_numerals\<close>]\<close>) fact
  }
end

lemma
  fixes x :: "'a::{linordered_field}"
  shows "2/3 * x + x / 3 = uu"
apply (tactic \<open>test \<^context> [\<^simproc>\<open>field_combine_numerals\<close>]\<close>)?
oops \<comment> \<open>FIXME: test fails\<close>

subsection \<open>\<open>nat_combine_numerals\<close>\<close>

notepad begin
  fix i j k m n u :: nat
  {
    assume "4*k = u" have "k + 3*k = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_combine_numerals\<close>]\<close>) fact
  next
    (* FIXME "Suc (i + 3) \<equiv> i + 4" *)
    assume "4 * Suc 0 + i = u" have "Suc (i + 3) = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_combine_numerals\<close>]\<close>) fact
  next
    (* FIXME "Suc (i + j + 3 + k) \<equiv> i + j + 4 + k" *)
    assume "4 * Suc 0 + (i + (j + k)) = u" have "Suc (i + j + 3 + k) = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_combine_numerals\<close>]\<close>) fact
  next
    assume "2 * j + 4 * k = u" have "k + j + 3*k + j = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_combine_numerals\<close>]\<close>) fact
  next
    assume "6 * Suc 0 + (5 * (i * j) + (4 * k + i)) = u"
    have "Suc (j*i + i + k + 5 + 3*k + i*j*4) = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_combine_numerals\<close>]\<close>) fact
  next
    assume "5 * (m * n) = u" have "(2*n*m) + (3*(m*n)) = u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_combine_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>nateq_cancel_numerals\<close>\<close>

notepad begin
  fix i j k l oo u uu vv w y z w' y' z' :: "nat"
  {
    assume "Suc 0 * u = 0" have "2*u = (u::nat)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc 0 * u = Suc 0" have "2*u = Suc (u)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "i + (j + k) = 3 * Suc 0 + (u + y)"
    have "(i + j + 12 + k) = u + 15 + y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "7 * Suc 0 + (i + (j + k)) = u + y"
    have "(i + j + 12 + k) = u + 5 + y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "11 * Suc 0 + (i + (j + k)) = u + y"
    have "(i + j + 12 + k) = Suc (u + y)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "i + (j + k) = 2 * Suc 0 + (u + y)"
    have "(i + j + 5 + k) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (u + y)))))))"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc 0 * u + (2 * y + 3 * z) = Suc 0"
    have "2*y + 3*z + 2*u = Suc (u)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc 0 * u + (2 * y + (3 * z + (6 * w + (2 * y + 3 * z)))) = Suc 0"
    have "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = Suc (u)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc 0 * u + (2 * y + (3 * z + (6 * w + (2 * y + 3 * z)))) =
      2 * y' + (3 * z' + (6 * w' + (2 * y' + (3 * z' + vv))))"
    have "2*y + 3*z + 6*w + 2*y + 3*z + 2*u =
      2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + vv"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  next
    assume "2 * u + (2 * z + (5 * Suc 0 + 2 * y)) = vv"
    have "6 + 2*y + 3*z + 4*u = Suc (vv + 2*u + z)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nateq_cancel_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>natless_cancel_numerals\<close>\<close>

notepad begin
  fix length :: "'a \<Rightarrow> nat" and l1 l2 xs :: "'a" and f :: "nat \<Rightarrow> 'a"
  fix c i j k l m oo u uu vv w y z w' y' z' :: "nat"
  {
    assume "0 < j" have "(2*length xs < 2*length xs + j)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natless_cancel_numerals\<close>]\<close>) fact
  next
    assume "0 < j" have "(2*length xs < length xs * 2 + j)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natless_cancel_numerals\<close>]\<close>) fact
  next
    assume "i + (j + k) < u + y"
    have "(i + j + 5 + k) < Suc (Suc (Suc (Suc (Suc (u + y)))))"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natless_cancel_numerals\<close>]\<close>) fact
  next
    assume "0 < Suc 0 * (m * n) + u" have "(2*n*m) < (3*(m*n)) + u"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natless_cancel_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>natle_cancel_numerals\<close>\<close>

notepad begin
  fix length :: "'a \<Rightarrow> nat" and l2 l3 :: "'a" and f :: "nat \<Rightarrow> 'a"
  fix c e i j k l oo u uu vv w y z w' y' z' :: "nat"
  {
    assume "u + y \<le> 36 * Suc 0 + (i + (j + k))"
    have "Suc (Suc (Suc (Suc (Suc (u + y))))) \<le> ((i + j) + 41 + k)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_numerals\<close>]\<close>) fact
  next
    assume "5 * Suc 0 + (case length (f c) of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> k) = 0"
    have "(Suc (Suc (Suc (Suc (Suc (Suc (case length (f c) of 0 => 0 | Suc k => k)))))) \<le> Suc 0)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_numerals\<close>]\<close>) fact
  next
    assume "6 + length l2 = 0" have "Suc (Suc (Suc (Suc (Suc (Suc (length l1 + length l2)))))) \<le> length l1"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_numerals\<close>]\<close>) fact
  next
    assume "5 + length l3 = 0"
    have "( (Suc (Suc (Suc (Suc (Suc (length (compT P E A ST mxr e) + length l3)))))) \<le> length (compT P E A ST mxr e))"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_numerals\<close>]\<close>) fact
  next
    assume "5 + length (compT P E (A \<union> A' e) ST mxr c) = 0"
    have "( (Suc (Suc (Suc (Suc (Suc (length (compT P E A ST mxr e) + length (compT P E (A Un A' e) ST mxr c))))))) \<le> length (compT P E A ST mxr e))"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natle_cancel_numerals\<close>]\<close>) fact
  }
end

subsection \<open>\<open>natdiff_cancel_numerals\<close>\<close>

notepad begin
  fix length :: "'a \<Rightarrow> nat" and l2 l3 :: "'a" and f :: "nat \<Rightarrow> 'a"
  fix c e i j k l oo u uu vv v w x y z zz w' y' z' :: "nat"
  {
    assume "i + (j + k) - 3 * Suc 0 = y" have "(i + j + 12 + k) - 15 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "7 * Suc 0 + (i + (j + k)) - 0 = y" have "(i + j + 12 + k) - 5 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "u - Suc 0 * Suc 0 = y" have "Suc u - 2 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc 0 * Suc 0 + u - 0 = y" have "Suc (Suc (Suc u)) - 2 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc 0 * Suc 0 + (i + (j + k)) - 0 = y"
    have "(i + j + 2 + k) - 1 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "i + (j + k) - Suc 0 * Suc 0 = y"
    have "(i + j + 1 + k) - 2 = y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "2 * x + y - 2 * (u * v) = w"
    have "(2*x + (u*v) + y) - v*3*u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "2 * x * u * v + (5 + y) - 0 = w"
    have "(2*x*u*v + 5 + (u*v)*4 + y) - v*u*4 = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "3 * (u * v) + (2 * x * u * v + y) - 0 = w"
    have "(2*x*u*v + (u*v)*4 + y) - v*u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "3 * u + (2 + (2 * x * u * v + y)) - 0 = w"
    have "Suc (Suc (2*x*u*v + u*4 + y)) - u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "Suc (Suc 0 * (u * v)) - 0 = w"
    have "Suc ((u*v)*4) - v*3*u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "2 - 0 = w" have "Suc (Suc ((u*v)*3)) - v*3*u = w"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "17 * Suc 0 + (i + (j + k)) - (u + y) = zz"
    have "(i + j + 32 + k) - (u + 15 + y) = zz"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  next
    assume "u + y - 0 = v" have "Suc (Suc (Suc (Suc (Suc (u + y))))) - 5 = v"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>natdiff_cancel_numerals\<close>]\<close>) fact
  }
end

subsection \<open>Factor-cancellation simprocs for type \<^typ>\<open>nat\<close>\<close>

text \<open>\<open>nat_eq_cancel_factor\<close>, \<open>nat_less_cancel_factor\<close>,
\<open>nat_le_cancel_factor\<close>, \<open>nat_divide_cancel_factor\<close>, and
\<open>nat_dvd_cancel_factor\<close>.\<close>

notepad begin
  fix a b c d k x y uu :: nat
  {
    assume "k = 0 \<or> x = y" have "x*k = k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "k = 0 \<or> Suc 0 = y" have "k = k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "b = 0 \<or> a * c = Suc 0" have "a*(b*c) = b"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "a = 0 \<or> b = 0 \<or> c = d * x" have "a*(b*c) = d*b*(x*a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_eq_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < k \<and> x < y" have "x*k < k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < k \<and> Suc 0 < y" have "k < k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < b \<and> a * c < Suc 0" have "a*(b*c) < b"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < a \<and> 0 < b \<and> c < d * x" have "a*(b*c) < d*b*(x*a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_less_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < k \<longrightarrow> x \<le> y" have "x*k \<le> k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_le_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < k \<longrightarrow> Suc 0 \<le> y" have "k \<le> k*y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_le_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < b \<longrightarrow> a * c \<le> Suc 0" have "a*(b*c) \<le> b"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_le_cancel_factor\<close>]\<close>) fact
  next
    assume "0 < a \<longrightarrow> 0 < b \<longrightarrow> c \<le> d * x" have "a*(b*c) \<le> d*b*(x*a)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_le_cancel_factor\<close>]\<close>) fact
  next
    assume "(if k = 0 then 0 else x div y) = uu" have "(x*k) div (k*y) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_div_cancel_factor\<close>]\<close>) fact
  next
    assume "(if k = 0 then 0 else Suc 0 div y) = uu" have "k div (k*y) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_div_cancel_factor\<close>]\<close>) fact
  next
    assume "(if b = 0 then 0 else a * c) = uu" have "(a*(b*c)) div (b) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_div_cancel_factor\<close>]\<close>) fact
  next
    assume "(if a = 0 then 0 else if b = 0 then 0 else c div (d * x)) = uu"
    have "(a*(b*c)) div (d*b*(x*a)) = uu"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_div_cancel_factor\<close>]\<close>) fact
  next
    assume "k = 0 \<or> x dvd y" have "(x*k) dvd (k*y)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_dvd_cancel_factor\<close>]\<close>) fact
  next
    assume "k = 0 \<or> Suc 0 dvd y" have "k dvd (k*y)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_dvd_cancel_factor\<close>]\<close>) fact
  next
    assume "b = 0 \<or> a * c dvd Suc 0" have "(a*(b*c)) dvd (b)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_dvd_cancel_factor\<close>]\<close>) fact
  next
    assume "b = 0 \<or> Suc 0 dvd a * c" have "b dvd (a*(b*c))"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_dvd_cancel_factor\<close>]\<close>) fact
  next
    assume "a = 0 \<or> b = 0 \<or> c dvd d * x" have "(a*(b*c)) dvd (d*b*(x*a))"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_dvd_cancel_factor\<close>]\<close>) fact
  }
end

subsection \<open>Numeral-cancellation simprocs for type \<^typ>\<open>nat\<close>\<close>

notepad begin
  fix x y z :: nat
  {
    assume "3 * x = 4 * y" have "9*x = 12 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_eq_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "3 * x < 4 * y" have "9*x < 12 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_less_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "3 * x \<le> 4 * y" have "9*x \<le> 12 * y"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_le_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "(3 * x) div (4 * y) = z" have "(9*x) div (12 * y) = z"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_div_cancel_numeral_factor\<close>]\<close>) fact
  next
    assume "(3 * x) dvd (4 * y)" have "(9*x) dvd (12 * y)"
      by (tactic \<open>test \<^context> [\<^simproc>\<open>nat_dvd_cancel_numeral_factor\<close>]\<close>) fact
  }
end

subsection \<open>Integer numeral div/mod simprocs\<close>

notepad begin
  have "(10::int) div 3 = 3"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(10::int) mod 3 = 1"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(10::int) div -3 = -4"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(10::int) mod -3 = -2"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(-10::int) div 3 = -4"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(-10::int) mod 3 = 2"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(-10::int) div -3 = 3"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(-10::int) mod -3 = -1"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(8452::int) mod 3 = 1"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(59485::int) div 434 = 137"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "(1000006::int) mod 10 = 6"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "10000000 div 2 = (5000000::int)"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "10000001 mod 2 = (1::int)"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "10000055 div 32 = (312501::int)"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "10000055 mod 32 = (23::int)"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "100094 div 144 = (695::int)"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
  have "100094 mod 144 = (14::int)"
    by (tactic \<open>test \<^context> [\<^simproc>\<open>numeral_divmod\<close>]\<close>)
end

end
