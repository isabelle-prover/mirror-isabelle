(*  Title:      HOL/Library/Word.thy
    Author:     Jeremy Dawson and Gerwin Klein, NICTA, et. al.
*)

section \<open>A type of finite bit strings\<close>

theory Word
imports
  "HOL-Library.Type_Length"
begin

subsection \<open>Preliminaries\<close>

lemma signed_take_bit_decr_length_iff:
  \<open>signed_take_bit (LENGTH('a::len) - Suc 0) k = signed_take_bit (LENGTH('a) - Suc 0) l
    \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by (cases \<open>LENGTH('a)\<close>)
    (simp_all add: signed_take_bit_eq_iff_take_bit_eq)


subsection \<open>Fundamentals\<close>

subsubsection \<open>Type definition\<close>

quotient_type (overloaded) 'a word = int / \<open>\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a::len) l\<close>
  morphisms rep Word by (auto intro!: equivpI reflpI sympI transpI)

hide_const (open) rep \<comment> \<open>only for foundational purpose\<close>
hide_const (open) Word \<comment> \<open>only for code generation\<close>


subsubsection \<open>Basic arithmetic\<close>

instantiation word :: (len) comm_ring_1
begin

lift_definition zero_word :: \<open>'a word\<close>
  is 0 .

lift_definition one_word :: \<open>'a word\<close>
  is 1 .

lift_definition plus_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>(+)\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_add_cong)

lift_definition minus_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>(-)\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_diff_cong)

lift_definition uminus_word :: \<open>'a word \<Rightarrow> 'a word\<close>
  is uminus
  by (auto simp add: take_bit_eq_mod intro: mod_minus_cong)

lift_definition times_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>(*)\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_mult_cong)

instance
  by (standard; transfer) (simp_all add: algebra_simps)

end

context
  includes lifting_syntax
  notes
    power_transfer [transfer_rule]
    transfer_rule_of_bool [transfer_rule]
    transfer_rule_numeral [transfer_rule]
    transfer_rule_of_nat [transfer_rule]
    transfer_rule_of_int [transfer_rule]
begin

lemma power_transfer_word [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (^) (^)\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) of_bool of_bool\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) numeral numeral\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) int of_nat\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) (\<lambda>k. k) of_int\<close>
proof -
  have \<open>((=) ===> pcr_word) of_int of_int\<close>
    by transfer_prover
  then show ?thesis by (simp add: id_def)
qed

lemma [transfer_rule]:
  \<open>(pcr_word ===> (\<longleftrightarrow>)) even ((dvd) 2 :: 'a::len word \<Rightarrow> bool)\<close>
proof -
  have even_word_unfold: "even k \<longleftrightarrow> (\<exists>l. take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l))" (is "?P \<longleftrightarrow> ?Q")
    for k :: int
  proof
    assume ?P
    then show ?Q
      by auto
  next
    assume ?Q
    then obtain l where "take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l)" ..
    then have "even (take_bit LENGTH('a) k)"
      by simp
    then show ?P
      by simp
  qed
  show ?thesis by (simp only: even_word_unfold [abs_def] dvd_def [where ?'a = "'a word", abs_def])
    transfer_prover
qed

end

lemma exp_eq_zero_iff [simp]:
  \<open>2 ^ n = (0 :: 'a::len word) \<longleftrightarrow> n \<ge> LENGTH('a)\<close>
  by transfer auto

lemma word_exp_length_eq_0 [simp]:
  \<open>(2 :: 'a::len word) ^ LENGTH('a) = 0\<close>
  by simp


subsubsection \<open>Basic tool setup\<close>

ML_file \<open>Tools/word_lib.ML\<close>


subsubsection \<open>Basic code generation setup\<close>

context
begin

qualified lift_definition the_int :: \<open>'a::len word \<Rightarrow> int\<close>
  is \<open>take_bit LENGTH('a)\<close> .

end

lemma [code abstype]:
  \<open>Word.Word (Word.the_int w) = w\<close>
  by transfer simp

lemma Word_eq_word_of_int [code_post, simp]:
  \<open>Word.Word = of_int\<close>
  by (rule; transfer) simp

quickcheck_generator word
  constructors:
    \<open>0 :: 'a::len word\<close>,
    \<open>numeral :: num \<Rightarrow> 'a::len word\<close>

instantiation word :: (len) equal
begin

lift_definition equal_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> bool\<close>
  is \<open>\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by simp

instance
  by (standard; transfer) rule

end

lemma [code]:
  \<open>HOL.equal v w \<longleftrightarrow> HOL.equal (Word.the_int v) (Word.the_int w)\<close>
  by transfer (simp add: equal)

lemma [code]:
  \<open>Word.the_int 0 = 0\<close>
  by transfer simp

lemma [code]:
  \<open>Word.the_int 1 = 1\<close>
  by transfer simp

lemma [code]:
  \<open>Word.the_int (v + w) = take_bit LENGTH('a) (Word.the_int v + Word.the_int w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_add)

lemma [code]:
  \<open>Word.the_int (- w) = (let k = Word.the_int w in if w = 0 then 0 else 2 ^ LENGTH('a) - k)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (auto simp add: take_bit_eq_mod zmod_zminus1_eq_if)

lemma [code]:
  \<open>Word.the_int (v - w) = take_bit LENGTH('a) (Word.the_int v - Word.the_int w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_diff)

lemma [code]:
  \<open>Word.the_int (v * w) = take_bit LENGTH('a) (Word.the_int v * Word.the_int w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_mult)


subsubsection \<open>Basic conversions\<close>

abbreviation word_of_nat :: \<open>nat \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_nat \<equiv> of_nat\<close>

abbreviation word_of_int :: \<open>int \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_int \<equiv> of_int\<close>

lemma word_of_nat_eq_iff:
  \<open>word_of_nat m = (word_of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m = take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma word_of_int_eq_iff:
  \<open>word_of_int k = (word_of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by transfer rule

lemma word_of_nat_eq_0_iff:
  \<open>word_of_nat n = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd n\<close>
  using word_of_nat_eq_iff [where ?'a = 'a, of n 0] by (simp add: take_bit_eq_0_iff)

lemma word_of_int_eq_0_iff:
  \<open>word_of_int k = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd k\<close>
  using word_of_int_eq_iff [where ?'a = 'a, of k 0] by (simp add: take_bit_eq_0_iff)

context semiring_1
begin

lift_definition unsigned :: \<open>'b::len word \<Rightarrow> 'a\<close>
  is \<open>of_nat \<circ> nat \<circ> take_bit LENGTH('b)\<close>
  by simp

lemma unsigned_0 [simp]:
  \<open>unsigned 0 = 0\<close>
  by transfer simp

lemma unsigned_1 [simp]:
  \<open>unsigned 1 = 1\<close>
  by transfer simp

lemma unsigned_numeral [simp]:
  \<open>unsigned (numeral n :: 'b::len word) = of_nat (take_bit LENGTH('b) (numeral n))\<close>
  by transfer (simp add: nat_take_bit_eq)

lemma unsigned_neg_numeral [simp]:
  \<open>unsigned (- numeral n :: 'b::len word) = of_nat (nat (take_bit LENGTH('b) (- numeral n)))\<close>
  by transfer simp

end

context semiring_1
begin

lemma unsigned_of_nat:
  \<open>unsigned (word_of_nat n :: 'b::len word) = of_nat (take_bit LENGTH('b) n)\<close>
  by transfer (simp add: nat_eq_iff take_bit_of_nat)

lemma unsigned_of_int:
  \<open>unsigned (word_of_int k :: 'b::len word) = of_nat (nat (take_bit LENGTH('b) k))\<close>
  by transfer simp

end

context semiring_char_0
begin

lemma unsigned_word_eqI:
  \<open>v = w\<close> if \<open>unsigned v = unsigned w\<close>
  using that by transfer (simp add: eq_nat_nat_iff)

lemma word_eq_iff_unsigned:
  \<open>v = w \<longleftrightarrow> unsigned v = unsigned w\<close>
  by (auto intro: unsigned_word_eqI)

lemma inj_unsigned [simp]:
  \<open>inj unsigned\<close>
  by (rule injI) (simp add: unsigned_word_eqI)

lemma unsigned_eq_0_iff:
  \<open>unsigned w = 0 \<longleftrightarrow> w = 0\<close>
  using word_eq_iff_unsigned [of w 0] by simp

end

context ring_1
begin

lift_definition signed :: \<open>'b::len word \<Rightarrow> 'a\<close>
  is \<open>of_int \<circ> signed_take_bit (LENGTH('b) - Suc 0)\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma signed_0 [simp]:
  \<open>signed 0 = 0\<close>
  by transfer simp

lemma signed_1 [simp]:
  \<open>signed (1 :: 'b::len word) = (if LENGTH('b) = 1 then - 1 else 1)\<close>
  by (transfer fixing: uminus; cases \<open>LENGTH('b)\<close>) (auto dest: gr0_implies_Suc)

lemma signed_minus_1 [simp]:
  \<open>signed (- 1 :: 'b::len word) = - 1\<close>
  by (transfer fixing: uminus) simp

lemma signed_numeral [simp]:
  \<open>signed (numeral n :: 'b::len word) = of_int (signed_take_bit (LENGTH('b) - 1) (numeral n))\<close>
  by transfer simp

lemma signed_neg_numeral [simp]:
  \<open>signed (- numeral n :: 'b::len word) = of_int (signed_take_bit (LENGTH('b) - 1) (- numeral n))\<close>
  by transfer simp

lemma signed_of_nat:
  \<open>signed (word_of_nat n :: 'b::len word) = of_int (signed_take_bit (LENGTH('b) - Suc 0) (int n))\<close>
  by transfer simp

lemma signed_of_int:
  \<open>signed (word_of_int n :: 'b::len word) = of_int (signed_take_bit (LENGTH('b) - Suc 0) n)\<close>
  by transfer simp

end

context ring_char_0
begin

lemma signed_word_eqI:
  \<open>v = w\<close> if \<open>signed v = signed w\<close>
  using that by transfer (simp flip: signed_take_bit_decr_length_iff)

lemma word_eq_iff_signed:
  \<open>v = w \<longleftrightarrow> signed v = signed w\<close>
  by (auto intro: signed_word_eqI)

lemma inj_signed [simp]:
  \<open>inj signed\<close>
  by (rule injI) (simp add: signed_word_eqI)

lemma signed_eq_0_iff:
  \<open>signed w = 0 \<longleftrightarrow> w = 0\<close>
  using word_eq_iff_signed [of w 0] by simp

end

abbreviation unat :: \<open>'a::len word \<Rightarrow> nat\<close>
  where \<open>unat \<equiv> unsigned\<close>

abbreviation uint :: \<open>'a::len word \<Rightarrow> int\<close>
  where \<open>uint \<equiv> unsigned\<close>

abbreviation sint :: \<open>'a::len word \<Rightarrow> int\<close>
  where \<open>sint \<equiv> signed\<close>

abbreviation ucast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>ucast \<equiv> unsigned\<close>

abbreviation scast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>scast \<equiv> signed\<close>

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>(pcr_word ===> (=)) (nat \<circ> take_bit LENGTH('a)) (unat :: 'a::len word \<Rightarrow> nat)\<close>
  using unsigned.transfer [where ?'a = nat] by simp

lemma [transfer_rule]:
  \<open>(pcr_word ===> (=)) (take_bit LENGTH('a)) (uint :: 'a::len word \<Rightarrow> int)\<close>
  using unsigned.transfer [where ?'a = int] by (simp add: comp_def)

lemma [transfer_rule]:
  \<open>(pcr_word ===> (=)) (signed_take_bit (LENGTH('a) - Suc 0)) (sint :: 'a::len word \<Rightarrow> int)\<close>
  using signed.transfer [where ?'a = int] by simp

lemma [transfer_rule]:
  \<open>(pcr_word ===> pcr_word) (take_bit LENGTH('a)) (ucast :: 'a::len word \<Rightarrow> 'b::len word)\<close>
proof (rule rel_funI)
  fix k :: int and w :: \<open>'a word\<close>
  assume \<open>pcr_word k w\<close>
  then have \<open>w = word_of_int k\<close>
    by (simp add: pcr_word_def cr_word_def relcompp_apply)
  moreover have \<open>pcr_word (take_bit LENGTH('a) k) (ucast (word_of_int k :: 'a word))\<close>
    by transfer (simp add: pcr_word_def cr_word_def relcompp_apply)
  ultimately show \<open>pcr_word (take_bit LENGTH('a) k) (ucast w)\<close>
    by simp
qed

lemma [transfer_rule]:
  \<open>(pcr_word ===> pcr_word) (signed_take_bit (LENGTH('a) - Suc 0)) (scast :: 'a::len word \<Rightarrow> 'b::len word)\<close>
proof (rule rel_funI)
  fix k :: int and w :: \<open>'a word\<close>
  assume \<open>pcr_word k w\<close>
  then have \<open>w = word_of_int k\<close>
    by (simp add: pcr_word_def cr_word_def relcompp_apply)
  moreover have \<open>pcr_word (signed_take_bit (LENGTH('a) - Suc 0) k) (scast (word_of_int k :: 'a word))\<close>
    by transfer (simp add: pcr_word_def cr_word_def relcompp_apply)
  ultimately show \<open>pcr_word (signed_take_bit (LENGTH('a) - Suc 0) k) (scast w)\<close>
    by simp
qed

end

lemma of_nat_unat [simp]:
  \<open>of_nat (unat w) = unsigned w\<close>
  by transfer simp

lemma of_int_uint [simp]:
  \<open>of_int (uint w) = unsigned w\<close>
  by transfer simp

lemma of_int_sint [simp]:
  \<open>of_int (sint a) = signed a\<close>
  by transfer (simp_all add: take_bit_signed_take_bit)

lemma nat_uint_eq [simp]:
  \<open>nat (uint w) = unat w\<close>
  by transfer simp

lemma sgn_uint_eq [simp]:
  \<open>sgn (uint w) = of_bool (w \<noteq> 0)\<close>
  by transfer (simp add: less_le)

text \<open>Aliasses only for code generation\<close>

context
begin

qualified lift_definition of_int :: \<open>int \<Rightarrow> 'a::len word\<close>
  is \<open>take_bit LENGTH('a)\<close> .

qualified lift_definition of_nat :: \<open>nat \<Rightarrow> 'a::len word\<close>
  is \<open>int \<circ> take_bit LENGTH('a)\<close> .

qualified lift_definition the_nat :: \<open>'a::len word \<Rightarrow> nat\<close>
  is \<open>nat \<circ> take_bit LENGTH('a)\<close> by simp

qualified lift_definition the_signed_int :: \<open>'a::len word \<Rightarrow> int\<close>
  is \<open>signed_take_bit (LENGTH('a) - Suc 0)\<close> by (simp add: signed_take_bit_decr_length_iff)

qualified lift_definition cast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  is \<open>take_bit LENGTH('a)\<close> by simp

qualified lift_definition signed_cast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  is \<open>signed_take_bit (LENGTH('a) - Suc 0)\<close> by (metis signed_take_bit_decr_length_iff)

end

lemma [code_abbrev, simp]:
  \<open>Word.the_int = uint\<close>
  by transfer rule

lemma [code]:
  \<open>Word.the_int (Word.of_int k :: 'a::len word) = take_bit LENGTH('a) k\<close>
  by transfer simp

lemma [code_abbrev, simp]:
  \<open>Word.of_int = word_of_int\<close>
  by (rule; transfer) simp

lemma [code]:
  \<open>Word.the_int (Word.of_nat n :: 'a::len word) = take_bit LENGTH('a) (int n)\<close>
  by transfer (simp add: take_bit_of_nat)

lemma [code_abbrev, simp]:
  \<open>Word.of_nat = word_of_nat\<close>
  by (rule; transfer) (simp add: take_bit_of_nat)

lemma [code]:
  \<open>Word.the_nat w = nat (Word.the_int w)\<close>
  by transfer simp

lemma [code_abbrev, simp]:
  \<open>Word.the_nat = unat\<close>
  by (rule; transfer) simp

lemma [code]:
  \<open>Word.the_signed_int w = signed_take_bit (LENGTH('a) - Suc 0) (Word.the_int w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: signed_take_bit_take_bit)

lemma [code_abbrev, simp]:
  \<open>Word.the_signed_int = sint\<close>
  by (rule; transfer) simp

lemma [code]:
  \<open>Word.the_int (Word.cast w :: 'b::len word) = take_bit LENGTH('b) (Word.the_int w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer simp

lemma [code_abbrev, simp]:
  \<open>Word.cast = ucast\<close>
  by (rule; transfer) simp

lemma [code]:
  \<open>Word.the_int (Word.signed_cast w :: 'b::len word) = take_bit LENGTH('b) (Word.the_signed_int w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer simp

lemma [code_abbrev, simp]:
  \<open>Word.signed_cast = scast\<close>
  by (rule; transfer) simp

lemma [code]:
  \<open>unsigned w = of_nat (nat (Word.the_int w))\<close>
  by transfer simp

lemma [code]:
  \<open>signed w = of_int (Word.the_signed_int w)\<close>
  by transfer simp


subsubsection \<open>Basic ordering\<close>

instantiation word :: (len) linorder
begin

lift_definition less_eq_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a \<le> take_bit LENGTH('a) b"
  by simp

lift_definition less_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a < take_bit LENGTH('a) b"
  by simp

instance
  by (standard; transfer) auto

end

interpretation word_order: ordering_top \<open>(\<le>)\<close> \<open>(<)\<close> \<open>- 1 :: 'a::len word\<close>
  by (standard; transfer) (simp add: take_bit_eq_mod zmod_minus1)

interpretation word_coorder: ordering_top \<open>(\<ge>)\<close> \<open>(>)\<close> \<open>0 :: 'a::len word\<close>
  by (standard; transfer) simp

lemma word_of_nat_less_eq_iff:
  \<open>word_of_nat m \<le> (word_of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m \<le> take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma word_of_int_less_eq_iff:
  \<open>word_of_int k \<le> (word_of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k \<le> take_bit LENGTH('a) l\<close>
  by transfer rule

lemma word_of_nat_less_iff:
  \<open>word_of_nat m < (word_of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m < take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma word_of_int_less_iff:
  \<open>word_of_int k < (word_of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k < take_bit LENGTH('a) l\<close>
  by transfer rule

lemma word_le_def [code]:
  "a \<le> b \<longleftrightarrow> uint a \<le> uint b"
  by transfer rule

lemma word_less_def [code]:
  "a < b \<longleftrightarrow> uint a < uint b"
  by transfer rule

lemma word_greater_zero_iff:
  \<open>a > 0 \<longleftrightarrow> a \<noteq> 0\<close> for a :: \<open>'a::len word\<close>
  by transfer (simp add: less_le)

lemma of_nat_word_less_eq_iff:
  \<open>of_nat m \<le> (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m \<le> take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_less_iff:
  \<open>of_nat m < (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m < take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_int_word_less_eq_iff:
  \<open>of_int k \<le> (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k \<le> take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_less_iff:
  \<open>of_int k < (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k < take_bit LENGTH('a) l\<close>
  by transfer rule



subsection \<open>Enumeration\<close>

lemma inj_on_word_of_nat:
  \<open>inj_on (word_of_nat :: nat \<Rightarrow> 'a::len word) {0..<2 ^ LENGTH('a)}\<close>
  by (rule inj_onI; transfer) (simp_all add: take_bit_int_eq_self)

lemma UNIV_word_eq_word_of_nat:
  \<open>(UNIV :: 'a::len word set) = word_of_nat ` {0..<2 ^ LENGTH('a)}\<close> (is \<open>_ = ?A\<close>)
proof
  show \<open>word_of_nat ` {0..<2 ^ LENGTH('a)} \<subseteq> UNIV\<close>
    by simp
  show \<open>UNIV \<subseteq> ?A\<close>
  proof
    fix w :: \<open>'a word\<close>
    show \<open>w \<in> (word_of_nat ` {0..<2 ^ LENGTH('a)} :: 'a word set)\<close>
      by (rule image_eqI [of _ _ \<open>unat w\<close>]; transfer) simp_all
  qed
qed

instantiation word :: (len) enum
begin

definition enum_word :: \<open>'a word list\<close>
  where \<open>enum_word = map word_of_nat [0..<2 ^ LENGTH('a)]\<close>

definition enum_all_word :: \<open>('a word \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>enum_all_word = All\<close>

definition enum_ex_word :: \<open>('a word \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>enum_ex_word = Ex\<close>

instance
  by standard
    (simp_all add: enum_all_word_def enum_ex_word_def enum_word_def distinct_map inj_on_word_of_nat flip: UNIV_word_eq_word_of_nat)

end

lemma [code]:
  \<open>Enum.enum_all P \<longleftrightarrow> list_all P Enum.enum\<close>
  \<open>Enum.enum_ex P \<longleftrightarrow> list_ex P Enum.enum\<close> for P :: \<open>'a::len word \<Rightarrow> bool\<close>
  by (simp_all add: enum_all_word_def enum_ex_word_def enum_UNIV list_all_iff list_ex_iff)


subsection \<open>Bit-wise operations\<close>

text \<open>
  The following specification of word division just lifts the pre-existing
  division on integers named ``F-Division'' in \<^cite>\<open>"leijen01"\<close>.
\<close>

instantiation word :: (len) semiring_modulo
begin

lift_definition divide_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>a b. take_bit LENGTH('a) a div take_bit LENGTH('a) b\<close>
  by simp

lift_definition modulo_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>a b. take_bit LENGTH('a) a mod take_bit LENGTH('a) b\<close>
  by simp

instance proof
  show "a div b * b + a mod b = a" for a b :: "'a word"
  proof transfer
    fix k l :: int
    define r :: int where "r = 2 ^ LENGTH('a)"
    then have r: "take_bit LENGTH('a) k = k mod r" for k
      by (simp add: take_bit_eq_mod)
    have "k mod r = ((k mod r) div (l mod r) * (l mod r)
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: div_mult_mod_eq)
    also have "... = (((k mod r) div (l mod r) * (l mod r)) mod r
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_add_left_eq)
    also have "... = (((k mod r) div (l mod r) * l) mod r
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_mult_right_eq)
    finally have "k mod r = ((k mod r) div (l mod r) * l
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_simps)
    with r show "take_bit LENGTH('a) (take_bit LENGTH('a) k div take_bit LENGTH('a) l * l
      + take_bit LENGTH('a) k mod take_bit LENGTH('a) l) = take_bit LENGTH('a) k"
      by simp
  qed
qed

end

lemma unat_div_distrib:
  \<open>unat (v div w) = unat v div unat w\<close>
proof transfer
  fix k l
  have \<open>nat (take_bit LENGTH('a) k) div nat (take_bit LENGTH('a) l) \<le> nat (take_bit LENGTH('a) k)\<close>
    by (rule div_le_dividend)
  also have \<open>nat (take_bit LENGTH('a) k) < 2 ^ LENGTH('a)\<close>
    by (simp add: nat_less_iff)
  finally show \<open>(nat \<circ> take_bit LENGTH('a)) (take_bit LENGTH('a) k div take_bit LENGTH('a) l) =
    (nat \<circ> take_bit LENGTH('a)) k div (nat \<circ> take_bit LENGTH('a)) l\<close>
    by (simp add: nat_take_bit_eq div_int_pos_iff nat_div_distrib take_bit_nat_eq_self_iff)
qed

lemma unat_mod_distrib:
  \<open>unat (v mod w) = unat v mod unat w\<close>
proof transfer
  fix k l
  have \<open>nat (take_bit LENGTH('a) k) mod nat (take_bit LENGTH('a) l) \<le> nat (take_bit LENGTH('a) k)\<close>
    by (rule mod_less_eq_dividend)
  also have \<open>nat (take_bit LENGTH('a) k) < 2 ^ LENGTH('a)\<close>
    by (simp add: nat_less_iff)
  finally show \<open>(nat \<circ> take_bit LENGTH('a)) (take_bit LENGTH('a) k mod take_bit LENGTH('a) l) =
    (nat \<circ> take_bit LENGTH('a)) k mod (nat \<circ> take_bit LENGTH('a)) l\<close>
    by (simp add: nat_take_bit_eq mod_int_pos_iff less_le nat_mod_distrib take_bit_nat_eq_self_iff)
qed

instance word :: (len) semiring_parity
  by (standard; transfer)
    (auto simp add: mod_2_eq_odd take_bit_Suc elim: evenE dest: le_Suc_ex)

lemma word_bit_induct [case_names zero even odd]:
  \<open>P a\<close> if word_zero: \<open>P 0\<close>
    and word_even: \<open>\<And>a. P a \<Longrightarrow> 0 < a \<Longrightarrow> a < 2 ^ (LENGTH('a) - Suc 0) \<Longrightarrow> P (2 * a)\<close>
    and word_odd: \<open>\<And>a. P a \<Longrightarrow> a < 2 ^ (LENGTH('a) - Suc 0) \<Longrightarrow> P (1 + 2 * a)\<close>
  for P and a :: \<open>'a::len word\<close>
proof -
  define m :: nat where \<open>m = LENGTH('a) - Suc 0\<close>
  then have l: \<open>LENGTH('a) = Suc m\<close>
    by simp
  define n :: nat where \<open>n = unat a\<close>
  then have \<open>n < 2 ^ LENGTH('a)\<close>
    by transfer (simp add: take_bit_eq_mod)
  then have \<open>n < 2 * 2 ^ m\<close>
    by (simp add: l)
  then have \<open>P (of_nat n)\<close>
  proof (induction n rule: nat_bit_induct)
    case zero
    show ?case
      by simp (rule word_zero)
  next
    case (even n)
    then have \<open>n < 2 ^ m\<close>
      by simp
    with even.IH have \<open>P (of_nat n)\<close>
      by simp
    moreover from \<open>n < 2 ^ m\<close> even.hyps have \<open>0 < (of_nat n :: 'a word)\<close>
      by (auto simp add: word_greater_zero_iff l word_of_nat_eq_0_iff)
    moreover from \<open>n < 2 ^ m\<close> have \<open>(of_nat n :: 'a word) < 2 ^ (LENGTH('a) - Suc 0)\<close>
      using of_nat_word_less_iff [where ?'a = 'a, of n \<open>2 ^ m\<close>]
      by (simp add: l take_bit_eq_mod)
    ultimately have \<open>P (2 * of_nat n)\<close>
      by (rule word_even)
    then show ?case
      by simp
  next
    case (odd n)
    then have \<open>Suc n \<le> 2 ^ m\<close>
      by simp
    with odd.IH have \<open>P (of_nat n)\<close>
      by simp
    moreover from \<open>Suc n \<le> 2 ^ m\<close> have \<open>(of_nat n :: 'a word) < 2 ^ (LENGTH('a) - Suc 0)\<close>
      using of_nat_word_less_iff [where ?'a = 'a, of n \<open>2 ^ m\<close>]
      by (simp add: l take_bit_eq_mod)
    ultimately have \<open>P (1 + 2 * of_nat n)\<close>
      by (rule word_odd)
    then show ?case
      by simp
  qed
  moreover have \<open>of_nat (nat (uint a)) = a\<close>
    by transfer simp
  ultimately show ?thesis
    by (simp add: n_def)
qed

lemma bit_word_half_eq:
  \<open>(of_bool b + a * 2) div 2 = a\<close>
    if \<open>a < 2 ^ (LENGTH('a) - Suc 0)\<close>
    for a :: \<open>'a::len word\<close>
proof (cases \<open>2 \<le> LENGTH('a::len)\<close>)
  case False
  have \<open>of_bool (odd k) < (1 :: int) \<longleftrightarrow> even k\<close> for k :: int
    by auto
  with False that show ?thesis
    by transfer (simp add: eq_iff)
next
  case True
  obtain n where length: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  show ?thesis proof (cases b)
    case False
    moreover have \<open>a * 2 div 2 = a\<close>
    using that proof transfer
      fix k :: int
      from length have \<open>k * 2 mod 2 ^ LENGTH('a) = (k mod 2 ^ n) * 2\<close>
        by simp
      moreover assume \<open>take_bit LENGTH('a) k < take_bit LENGTH('a) (2 ^ (LENGTH('a) - Suc 0))\<close>
      with \<open>LENGTH('a) = Suc n\<close> have \<open>take_bit LENGTH('a) k = take_bit n k\<close>
        by (auto simp add: take_bit_Suc_from_most)
      ultimately have \<open>take_bit LENGTH('a) (k * 2) = take_bit LENGTH('a) k * 2\<close>
        by (simp add: take_bit_eq_mod)
      with True show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (k * 2) div take_bit LENGTH('a) 2)
        = take_bit LENGTH('a) k\<close>
        by simp
    qed
    ultimately show ?thesis
      by simp
  next
    case True
    moreover have \<open>(1 + a * 2) div 2 = a\<close>
    using that proof transfer
      fix k :: int
      from length have \<open>(1 + k * 2) mod 2 ^ LENGTH('a) = 1 + (k mod 2 ^ n) * 2\<close>
        using pos_zmod_mult_2 [of \<open>2 ^ n\<close> k] by (simp add: ac_simps)
      moreover assume \<open>take_bit LENGTH('a) k < take_bit LENGTH('a) (2 ^ (LENGTH('a) - Suc 0))\<close>
      with \<open>LENGTH('a) = Suc n\<close> have \<open>take_bit LENGTH('a) k = take_bit n k\<close>
        by (auto simp add: take_bit_Suc_from_most)
      ultimately have \<open>take_bit LENGTH('a) (1 + k * 2) = 1 + take_bit LENGTH('a) k * 2\<close>
        by (simp add: take_bit_eq_mod)
      with True show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (1 + k * 2) div take_bit LENGTH('a) 2)
        = take_bit LENGTH('a) k\<close>
        by (auto simp add: take_bit_Suc)
    qed
    ultimately show ?thesis
      by simp
  qed
qed

lemma even_mult_exp_div_word_iff:
  \<open>even (a * 2 ^ m div 2 ^ n) \<longleftrightarrow> \<not> (
    m \<le> n \<and>
    n < LENGTH('a) \<and> odd (a div 2 ^ (n - m)))\<close> for a :: \<open>'a::len word\<close>
  by transfer
    (auto simp flip: drop_bit_eq_div simp add: even_drop_bit_iff_not_bit bit_take_bit_iff,
      simp_all flip: push_bit_eq_mult add: bit_push_bit_iff_int)

instantiation word :: (len) semiring_bits
begin

lift_definition bit_word :: \<open>'a word \<Rightarrow> nat \<Rightarrow> bool\<close>
  is \<open>\<lambda>k n. n < LENGTH('a) \<and> bit k n\<close>
proof
  fix k l :: int and n :: nat
  assume *: \<open>take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  show \<open>n < LENGTH('a) \<and> bit k n \<longleftrightarrow> n < LENGTH('a) \<and> bit l n\<close>
  proof (cases \<open>n < LENGTH('a)\<close>)
    case True
    from * have \<open>bit (take_bit LENGTH('a) k) n \<longleftrightarrow> bit (take_bit LENGTH('a) l) n\<close>
      by simp
    then show ?thesis
      by (simp add: bit_take_bit_iff)
  next
    case False
    then show ?thesis
      by simp
  qed
qed

instance proof
  show \<open>P a\<close> if stable: \<open>\<And>a. a div 2 = a \<Longrightarrow> P a\<close>
    and rec: \<open>\<And>a b. P a \<Longrightarrow> (of_bool b + 2 * a) div 2 = a \<Longrightarrow> P (of_bool b + 2 * a)\<close>
  for P and a :: \<open>'a word\<close>
  proof (induction a rule: word_bit_induct)
    case zero
    have \<open>0 div 2 = (0::'a word)\<close>
      by transfer simp
    with stable [of 0] show ?case
      by simp
  next
    case (even a)
    with rec [of a False] show ?case
      using bit_word_half_eq [of a False] by (simp add: ac_simps)
  next
    case (odd a)
    with rec [of a True] show ?case
      using bit_word_half_eq [of a True] by (simp add: ac_simps)
  qed
  show \<open>bit a n \<longleftrightarrow> odd (a div 2 ^ n)\<close> for a :: \<open>'a word\<close> and n
    by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit bit_iff_odd_drop_bit)
  show \<open>a div 0 = 0\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>a div 1 = a\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>0 div a = 0\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>a mod b div b = 0\<close>
    for a b :: \<open>'a word\<close>
    by (simp add: word_eq_iff_unsigned [where ?'a = nat] unat_div_distrib unat_mod_distrib)
  show \<open>a div 2 div 2 ^ n = a div 2 ^ Suc n\<close>
    for a :: \<open>'a word\<close> and m n :: nat
    apply transfer
    using drop_bit_eq_div [symmetric, where ?'a = int,of _ 1]
    apply (auto simp add: not_less take_bit_drop_bit ac_simps simp flip: drop_bit_eq_div simp del: power.simps)
    apply (simp add: drop_bit_take_bit)
    done
  show \<open>even (2 * a div 2 ^ Suc n) \<longleftrightarrow> even (a div 2 ^ n)\<close> if \<open>2 ^ Suc n \<noteq> (0::'a word)\<close>
    for a :: \<open>'a word\<close> and n :: nat
    using that by transfer
      (simp add: even_drop_bit_iff_not_bit bit_simps flip: drop_bit_eq_div del: power.simps)
qed

end

lemma bit_word_eqI:
  \<open>a = b\<close> if \<open>\<And>n. n < LENGTH('a) \<Longrightarrow> bit a n \<longleftrightarrow> bit b n\<close>
  for a b :: \<open>'a::len word\<close>
  using that by transfer (auto simp add: nat_less_le bit_eq_iff bit_take_bit_iff)

lemma bit_imp_le_length:
  \<open>n < LENGTH('a)\<close> if \<open>bit w n\<close>
    for w :: \<open>'a::len word\<close>
  using that by transfer simp

lemma not_bit_length [simp]:
  \<open>\<not> bit w LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  by transfer simp

lemma finite_bit_word [simp]:
  \<open>finite {n. bit w n}\<close>
  for w :: \<open>'a::len word\<close>
proof -
  have \<open>{n. bit w n} \<subseteq> {0..LENGTH('a)}\<close>
    by (auto dest: bit_imp_le_length)
  moreover have \<open>finite {0..LENGTH('a)}\<close>
    by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma bit_numeral_word_iff [simp]:
  \<open>bit (numeral w :: 'a::len word) n
    \<longleftrightarrow> n < LENGTH('a) \<and> bit (numeral w :: int) n\<close>
  by transfer simp

lemma bit_neg_numeral_word_iff [simp]:
  \<open>bit (- numeral w :: 'a::len word) n
    \<longleftrightarrow> n < LENGTH('a) \<and> bit (- numeral w :: int) n\<close>
  by transfer simp

instantiation word :: (len) ring_bit_operations
begin

lift_definition not_word :: \<open>'a word \<Rightarrow> 'a word\<close>
  is not
  by (simp add: take_bit_not_iff)

lift_definition and_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>and\<close>
  by simp

lift_definition or_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is or
  by simp

lift_definition xor_word ::  \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is xor
  by simp

lift_definition mask_word :: \<open>nat \<Rightarrow> 'a word\<close>
  is mask
  .

lift_definition set_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is set_bit
  by (simp add: set_bit_def)

lift_definition unset_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is unset_bit
  by (simp add: unset_bit_def)

lift_definition flip_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is flip_bit
  by (simp add: flip_bit_def)

lift_definition push_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is push_bit
proof -
  show \<open>take_bit LENGTH('a) (push_bit n k) = take_bit LENGTH('a) (push_bit n l)\<close>
    if \<open>take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close> for k l :: int and n :: nat
  proof -
    from that
    have \<open>take_bit (LENGTH('a) - n) (take_bit LENGTH('a) k)
      = take_bit (LENGTH('a) - n) (take_bit LENGTH('a) l)\<close>
      by simp
    moreover have \<open>min (LENGTH('a) - n) LENGTH('a) = LENGTH('a) - n\<close>
      by simp
    ultimately show ?thesis
      by (simp add: take_bit_push_bit)
  qed
qed

lift_definition drop_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>n. drop_bit n \<circ> take_bit LENGTH('a)\<close>
  by (simp add: take_bit_eq_mod)

lift_definition take_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>n. take_bit (min LENGTH('a) n)\<close>
  by (simp add: ac_simps) (simp only: flip: take_bit_take_bit)

context
  includes bit_operations_syntax
begin

instance proof
  fix v w :: \<open>'a word\<close> and n m :: nat
  show \<open>NOT v = - v - 1\<close>
    by transfer (simp add: not_eq_complement)
  show \<open>v AND w = of_bool (odd v \<and> odd w) + 2 * (v div 2 AND w div 2)\<close>
    apply transfer
    apply (rule bit_eqI)
    apply (auto simp add: even_bit_succ_iff bit_simps bit_0 simp flip: bit_Suc)
    done
  show \<open>v OR w = of_bool (odd v \<or> odd w) + 2 * (v div 2 OR w div 2)\<close>
    apply transfer
    apply (rule bit_eqI)
    apply (auto simp add: even_bit_succ_iff bit_simps bit_0 simp flip: bit_Suc)
    done
  show \<open>v XOR w = of_bool (odd v \<noteq> odd w) + 2 * (v div 2 XOR w div 2)\<close>
    apply transfer
    apply (rule bit_eqI)
    subgoal for k l n
      apply (cases n)
       apply (auto simp add: even_bit_succ_iff bit_simps bit_0 even_xor_iff simp flip: bit_Suc)
      done
    done
  show \<open>mask n = 2 ^ n - (1 :: 'a word)\<close>
    by transfer (simp flip: mask_eq_exp_minus_1)
  show \<open>set_bit n v = v OR push_bit n 1\<close>
    by transfer (simp add: set_bit_eq_or)
  show \<open>unset_bit n v = (v OR push_bit n 1) XOR push_bit n 1\<close>
    by transfer (simp add: unset_bit_eq_or_xor)
  show \<open>flip_bit n v = v XOR push_bit n 1\<close>
    by transfer (simp add: flip_bit_eq_xor)
  show \<open>push_bit n v = v * 2 ^ n\<close>
    by transfer (simp add: push_bit_eq_mult)
  show \<open>drop_bit n v = v div 2 ^ n\<close>
    by transfer (simp add: drop_bit_take_bit flip: drop_bit_eq_div)
  show \<open>take_bit n v = v mod 2 ^ n\<close>
    by transfer (simp flip: take_bit_eq_mod)
qed

end

end

lemma [code]:
  \<open>push_bit n w = w * 2 ^ n\<close> for w :: \<open>'a::len word\<close>
  by (fact push_bit_eq_mult)

lemma [code]:
  \<open>Word.the_int (drop_bit n w) = drop_bit n (Word.the_int w)\<close>
  by transfer (simp add: drop_bit_take_bit min_def le_less less_diff_conv)

lemma [code]:
  \<open>Word.the_int (take_bit n w) = (if n < LENGTH('a::len) then take_bit n (Word.the_int w) else Word.the_int w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: not_le not_less ac_simps min_absorb2)

lemma [code_abbrev]:
  \<open>push_bit n 1 = (2 :: 'a::len word) ^ n\<close>
  by (fact push_bit_of_1)

context
  includes bit_operations_syntax
begin

lemma [code]:
  \<open>NOT w = Word.of_int (NOT (Word.the_int w))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_not_take_bit) 

lemma [code]:
  \<open>Word.the_int (v AND w) = Word.the_int v AND Word.the_int w\<close>
  by transfer simp

lemma [code]:
  \<open>Word.the_int (v OR w) = Word.the_int v OR Word.the_int w\<close>
  by transfer simp

lemma [code]:
  \<open>Word.the_int (v XOR w) = Word.the_int v XOR Word.the_int w\<close>
  by transfer simp

lemma [code]:
  \<open>Word.the_int (mask n :: 'a::len word) = mask (min LENGTH('a) n)\<close>
  by transfer simp

lemma [code]:
  \<open>set_bit n w = w OR push_bit n 1\<close> for w :: \<open>'a::len word\<close>
  by (fact set_bit_eq_or)

lemma [code]:
  \<open>unset_bit n w = w AND NOT (push_bit n 1)\<close> for w :: \<open>'a::len word\<close>
  by (fact unset_bit_eq_and_not)

lemma [code]:
  \<open>flip_bit n w = w XOR push_bit n 1\<close> for w :: \<open>'a::len word\<close>
  by (fact flip_bit_eq_xor)

context
  includes lifting_syntax
begin

lemma set_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word) set_bit set_bit\<close>
  by (unfold set_bit_def) transfer_prover

lemma unset_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word) unset_bit unset_bit\<close>
  by (unfold unset_bit_def) transfer_prover

lemma flip_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word) flip_bit flip_bit\<close>
  by (unfold flip_bit_def) transfer_prover

lemma signed_take_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word)
    (\<lambda>n k. signed_take_bit n (take_bit LENGTH('a::len) k))
    (signed_take_bit :: nat \<Rightarrow> 'a word \<Rightarrow> 'a word)\<close>
proof -
  let ?K = \<open>\<lambda>n (k :: int). take_bit (min LENGTH('a) n) k OR of_bool (n < LENGTH('a) \<and> bit k n) * NOT (mask n)\<close>
  let ?W = \<open>\<lambda>n (w :: 'a word). take_bit n w OR of_bool (bit w n) * NOT (mask n)\<close>
  have \<open>((=) ===> pcr_word ===> pcr_word) ?K ?W\<close>
    by transfer_prover
  also have \<open>?K = (\<lambda>n k. signed_take_bit n (take_bit LENGTH('a::len) k))\<close>
    by (simp add: fun_eq_iff signed_take_bit_def bit_take_bit_iff ac_simps)
  also have \<open>?W = signed_take_bit\<close>
    by (simp add: fun_eq_iff signed_take_bit_def)
  finally show ?thesis .
qed

end

end


subsection \<open>Conversions including casts\<close>

subsubsection \<open>Generic unsigned conversion\<close>

context semiring_bits
begin

lemma bit_unsigned_iff [bit_simps]:
  \<open>bit (unsigned w) n \<longleftrightarrow> possible_bit TYPE('a) n \<and> bit w n\<close>
  for w :: \<open>'b::len word\<close>
  by (transfer fixing: bit) (simp add: bit_of_nat_iff bit_nat_iff bit_take_bit_iff)

end

lemma possible_bit_word[simp]:
  \<open>possible_bit TYPE(('a :: len) word) m \<longleftrightarrow> m < LENGTH('a)\<close>
  by (simp add: possible_bit_def linorder_not_le)

context semiring_bit_operations
begin

lemma unsigned_minus_1_eq_mask:
  \<open>unsigned (- 1 :: 'b::len word) = mask LENGTH('b)\<close>
  by (transfer fixing: mask) (simp add: nat_mask_eq of_nat_mask_eq)

lemma unsigned_push_bit_eq:
  \<open>unsigned (push_bit n w) = take_bit LENGTH('b) (push_bit n (unsigned w))\<close>
  for w :: \<open>'b::len word\<close>
proof (rule bit_eqI)
  fix m
  assume \<open>possible_bit TYPE('a) m\<close>
  show \<open>bit (unsigned (push_bit n w)) m = bit (take_bit LENGTH('b) (push_bit n (unsigned w))) m\<close>
  proof (cases \<open>n \<le> m\<close>)
    case True
    with \<open>possible_bit TYPE('a) m\<close> have \<open>possible_bit TYPE('a) (m - n)\<close>
      by (simp add: possible_bit_less_imp)
    with True show ?thesis
      by (simp add: bit_unsigned_iff bit_push_bit_iff Bit_Operations.bit_push_bit_iff bit_take_bit_iff not_le ac_simps)
  next
    case False
    then show ?thesis
      by (simp add: not_le bit_unsigned_iff bit_push_bit_iff Bit_Operations.bit_push_bit_iff bit_take_bit_iff)
  qed
qed

lemma unsigned_take_bit_eq:
  \<open>unsigned (take_bit n w) = take_bit n (unsigned w)\<close>
  for w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff bit_take_bit_iff Bit_Operations.bit_take_bit_iff)

end

context linordered_euclidean_semiring_bit_operations
begin

lemma unsigned_drop_bit_eq:
  \<open>unsigned (drop_bit n w) = drop_bit n (take_bit LENGTH('b) (unsigned w))\<close>
  for w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (auto simp add: bit_unsigned_iff bit_take_bit_iff bit_drop_bit_eq Bit_Operations.bit_drop_bit_eq possible_bit_def dest: bit_imp_le_length)

end

lemma ucast_drop_bit_eq:
  \<open>ucast (drop_bit n w) = drop_bit n (ucast w :: 'b::len word)\<close>
  if \<open>LENGTH('a) \<le> LENGTH('b)\<close> for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (use that in \<open>auto simp add: bit_unsigned_iff bit_drop_bit_eq dest: bit_imp_le_length\<close>)

context semiring_bit_operations
begin

context
  includes bit_operations_syntax
begin

lemma unsigned_and_eq:
  \<open>unsigned (v AND w) = unsigned v AND unsigned w\<close>
  for v w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps)

lemma unsigned_or_eq:
  \<open>unsigned (v OR w) = unsigned v OR unsigned w\<close>
  for v w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps)

lemma unsigned_xor_eq:
  \<open>unsigned (v XOR w) = unsigned v XOR unsigned w\<close>
  for v w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps)

end

end

context ring_bit_operations
begin

context
  includes bit_operations_syntax
begin

lemma unsigned_not_eq:
  \<open>unsigned (NOT w) = take_bit LENGTH('b) (NOT (unsigned w))\<close>
  for w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps)

end

end

context linordered_euclidean_semiring
begin

lemma unsigned_greater_eq [simp]:
  \<open>0 \<le> unsigned w\<close> for w :: \<open>'b::len word\<close>
  by (transfer fixing: less_eq) simp

lemma unsigned_less [simp]:
  \<open>unsigned w < 2 ^ LENGTH('b)\<close> for w :: \<open>'b::len word\<close>
  by (transfer fixing: less) simp

end

context linordered_semidom
begin

lemma word_less_eq_iff_unsigned:
  "a \<le> b \<longleftrightarrow> unsigned a \<le> unsigned b"
  by (transfer fixing: less_eq) (simp add: nat_le_eq_zle)

lemma word_less_iff_unsigned:
  "a < b \<longleftrightarrow> unsigned a < unsigned b"
  by (transfer fixing: less) (auto dest: preorder_class.le_less_trans [OF take_bit_nonnegative])

end


subsubsection \<open>Generic signed conversion\<close>

context ring_bit_operations
begin

lemma bit_signed_iff [bit_simps]:
  \<open>bit (signed w) n \<longleftrightarrow> possible_bit TYPE('a) n \<and> bit w (min (LENGTH('b) - Suc 0) n)\<close>
  for w :: \<open>'b::len word\<close>
  by (transfer fixing: bit)
    (auto simp add: bit_of_int_iff Bit_Operations.bit_signed_take_bit_iff min_def)

lemma signed_push_bit_eq:
  \<open>signed (push_bit n w) = signed_take_bit (LENGTH('b) - Suc 0) (push_bit n (signed w :: 'a))\<close>
  for w :: \<open>'b::len word\<close>
  apply (simp add: bit_eq_iff bit_simps possible_bit_less_imp min_less_iff_disj)
  apply (cases n, simp_all add: min_def)
  done

lemma signed_take_bit_eq:
  \<open>signed (take_bit n w) = (if n < LENGTH('b) then take_bit n (signed w) else signed w)\<close>
  for w :: \<open>'b::len word\<close>
  by (transfer fixing: take_bit; cases \<open>LENGTH('b)\<close>)
    (auto simp add: Bit_Operations.signed_take_bit_take_bit Bit_Operations.take_bit_signed_take_bit take_bit_of_int min_def less_Suc_eq)

context
  includes bit_operations_syntax
begin

lemma signed_not_eq:
  \<open>signed (NOT w) = signed_take_bit LENGTH('b) (NOT (signed w))\<close>
  for w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps possible_bit_less_imp min_less_iff_disj)
    (auto simp: min_def)

lemma signed_and_eq:
  \<open>signed (v AND w) = signed v AND signed w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_signed_iff bit_and_iff Bit_Operations.bit_and_iff)

lemma signed_or_eq:
  \<open>signed (v OR w) = signed v OR signed w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_signed_iff bit_or_iff Bit_Operations.bit_or_iff)

lemma signed_xor_eq:
  \<open>signed (v XOR w) = signed v XOR signed w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_signed_iff bit_xor_iff Bit_Operations.bit_xor_iff)

end

end


subsubsection \<open>More\<close>

lemma sint_greater_eq:
  \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> sint w\<close> for w :: \<open>'a::len word\<close>
proof (cases \<open>bit w (LENGTH('a) - Suc 0)\<close>)
  case True
  then show ?thesis
    by transfer (simp add: signed_take_bit_eq_if_negative minus_exp_eq_not_mask or_greater_eq ac_simps)
next
  have *: \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> (0::int)\<close>
    by simp
  case False
  then show ?thesis
    by transfer (auto simp add: signed_take_bit_eq intro: order_trans *)
qed

lemma sint_less:
  \<open>sint w < 2 ^ (LENGTH('a) - Suc 0)\<close> for w :: \<open>'a::len word\<close>
  by (cases \<open>bit w (LENGTH('a) - Suc 0)\<close>; transfer)
    (simp_all add: signed_take_bit_eq signed_take_bit_def not_eq_complement mask_eq_exp_minus_1 OR_upper)

lemma uint_div_distrib:
  \<open>uint (v div w) = uint v div uint w\<close>
proof -
  have \<open>int (unat (v div w)) = int (unat v div unat w)\<close>
    by (simp add: unat_div_distrib)
  then show ?thesis
    by (simp add: of_nat_div)
qed

lemma unat_drop_bit_eq:
  \<open>unat (drop_bit n w) = drop_bit n (unat w)\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff bit_drop_bit_eq)

lemma uint_mod_distrib:
  \<open>uint (v mod w) = uint v mod uint w\<close>
proof -
  have \<open>int (unat (v mod w)) = int (unat v mod unat w)\<close>
    by (simp add: unat_mod_distrib)
  then show ?thesis
    by (simp add: of_nat_mod)
qed

context semiring_bit_operations
begin

lemma unsigned_ucast_eq:
  \<open>unsigned (ucast w :: 'c::len word) = take_bit LENGTH('c) (unsigned w)\<close>
  for w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff Word.bit_unsigned_iff bit_take_bit_iff not_le)

end

context ring_bit_operations
begin

lemma signed_ucast_eq:
  \<open>signed (ucast w :: 'c::len word) = signed_take_bit (LENGTH('c) - Suc 0) (unsigned w)\<close>
  for w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps min_less_iff_disj)

lemma signed_scast_eq:
  \<open>signed (scast w :: 'c::len word) = signed_take_bit (LENGTH('c) - Suc 0) (signed w)\<close>
  for w :: \<open>'b::len word\<close>
  by (simp add: bit_eq_iff bit_simps min_less_iff_disj)

end

lemma uint_nonnegative: "0 \<le> uint w"
  by (fact unsigned_greater_eq)

lemma uint_bounded: "uint w < 2 ^ LENGTH('a)"
  for w :: "'a::len word"
  by (fact unsigned_less)

lemma uint_idem: "uint w mod 2 ^ LENGTH('a) = uint w"
  for w :: "'a::len word"
  by transfer (simp add: take_bit_eq_mod)

lemma word_uint_eqI: "uint a = uint b \<Longrightarrow> a = b"
  by (fact unsigned_word_eqI)

lemma word_uint_eq_iff: "a = b \<longleftrightarrow> uint a = uint b"
  by (fact word_eq_iff_unsigned)

lemma uint_word_of_int_eq:
  \<open>uint (word_of_int k :: 'a::len word) = take_bit LENGTH('a) k\<close>
  by transfer rule

lemma uint_word_of_int: "uint (word_of_int k :: 'a::len word) = k mod 2 ^ LENGTH('a)"
  by (simp add: uint_word_of_int_eq take_bit_eq_mod)
  
lemma word_of_int_uint: "word_of_int (uint w) = w"
  by transfer simp

lemma word_div_def [code]:
  "a div b = word_of_int (uint a div uint b)"
  by transfer rule

lemma word_mod_def [code]:
  "a mod b = word_of_int (uint a mod uint b)"
  by transfer rule

lemma split_word_all: "(\<And>x::'a::len word. PROP P x) \<equiv> (\<And>x. PROP P (word_of_int x))"
proof
  fix x :: "'a word"
  assume "\<And>x. PROP P (word_of_int x)"
  then have "PROP P (word_of_int (uint x))" .
  then show "PROP P x"
    by (simp only: word_of_int_uint)
qed

lemma sint_uint:
  \<open>sint w = signed_take_bit (LENGTH('a) - Suc 0) (uint w)\<close>
  for w :: \<open>'a::len word\<close>
  by (cases \<open>LENGTH('a)\<close>; transfer) (simp_all add: signed_take_bit_take_bit)

lemma unat_eq_nat_uint:
  \<open>unat w = nat (uint w)\<close>
  by simp

lemma ucast_eq:
  \<open>ucast w = word_of_int (uint w)\<close>
  by transfer simp

lemma scast_eq:
  \<open>scast w = word_of_int (sint w)\<close>
  by transfer simp

lemma uint_0_eq:
  \<open>uint 0 = 0\<close>
  by (fact unsigned_0)

lemma uint_1_eq:
  \<open>uint 1 = 1\<close>
  by (fact unsigned_1)

lemma word_m1_wi: "- 1 = word_of_int (- 1)"
  by simp

lemma uint_0_iff: "uint x = 0 \<longleftrightarrow> x = 0"
  by (auto simp add: unsigned_word_eqI)

lemma unat_0_iff: "unat x = 0 \<longleftrightarrow> x = 0"
  by (auto simp add: unsigned_word_eqI)

lemma unat_0: "unat 0 = 0"
  by (fact unsigned_0)

lemma unat_gt_0: "0 < unat x \<longleftrightarrow> x \<noteq> 0"
  by (auto simp: unat_0_iff [symmetric])

lemma ucast_0: "ucast 0 = 0"
  by (fact unsigned_0)

lemma sint_0: "sint 0 = 0"
  by (fact signed_0)

lemma scast_0: "scast 0 = 0"
  by (fact signed_0)

lemma sint_n1: "sint (- 1) = - 1"
  by (fact signed_minus_1)

lemma scast_n1: "scast (- 1) = - 1"
  by (fact signed_minus_1)

lemma uint_1: "uint (1::'a::len word) = 1"
  by (fact uint_1_eq)

lemma unat_1: "unat (1::'a::len word) = 1"
  by (fact unsigned_1)

lemma ucast_1: "ucast (1::'a::len word) = 1"
  by (fact unsigned_1)

instantiation word :: (len) size
begin

lift_definition size_word :: \<open>'a word \<Rightarrow> nat\<close>
  is \<open>\<lambda>_. LENGTH('a)\<close> ..

instance ..

end

lemma word_size [code]:
  \<open>size w = LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  by (fact size_word.rep_eq)

lemma word_size_gt_0 [iff]: "0 < size w"
  for w :: "'a::len word"
  by (simp add: word_size)

lemmas lens_gt_0 = word_size_gt_0 len_gt_0

lemma lens_not_0 [iff]:
  \<open>size w \<noteq> 0\<close> for  w :: \<open>'a::len word\<close>
  by auto

lift_definition source_size :: \<open>('a::len word \<Rightarrow> 'b) \<Rightarrow> nat\<close>
  is \<open>\<lambda>_. LENGTH('a)\<close> .

lift_definition target_size :: \<open>('a \<Rightarrow> 'b::len word) \<Rightarrow> nat\<close>
  is \<open>\<lambda>_. LENGTH('b)\<close> ..

lift_definition is_up :: \<open>('a::len word \<Rightarrow> 'b::len word) \<Rightarrow> bool\<close>
  is \<open>\<lambda>_. LENGTH('a) \<le> LENGTH('b)\<close> ..

lift_definition is_down :: \<open>('a::len word \<Rightarrow> 'b::len word) \<Rightarrow> bool\<close>
  is \<open>\<lambda>_. LENGTH('a) \<ge> LENGTH('b)\<close> ..

lemma is_up_eq:
  \<open>is_up f \<longleftrightarrow> source_size f \<le> target_size f\<close>
  for f :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  by (simp add: source_size.rep_eq target_size.rep_eq is_up.rep_eq)

lemma is_down_eq:
  \<open>is_down f \<longleftrightarrow> target_size f \<le> source_size f\<close>
  for f :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  by (simp add: source_size.rep_eq target_size.rep_eq is_down.rep_eq)

lift_definition word_int_case :: \<open>(int \<Rightarrow> 'b) \<Rightarrow> 'a::len word \<Rightarrow> 'b\<close>
  is \<open>\<lambda>f. f \<circ> take_bit LENGTH('a)\<close> by simp

lemma word_int_case_eq_uint [code]:
  \<open>word_int_case f w = f (uint w)\<close>
  by transfer simp

translations
  "case x of XCONST of_int y \<Rightarrow> b" \<rightleftharpoons> "CONST word_int_case (\<lambda>y. b) x"
  "case x of (XCONST of_int :: 'a) y \<Rightarrow> b" \<rightharpoonup> "CONST word_int_case (\<lambda>y. b) x"


subsection \<open>Arithmetic operations\<close>

lemma div_word_self:
  \<open>w div w = 1\<close> if \<open>w \<noteq> 0\<close> for w :: \<open>'a::len word\<close>
  using that by transfer simp

lemma mod_word_self [simp]:
  \<open>w mod w = 0\<close> for w :: \<open>'a::len word\<close>
  apply (cases \<open>w = 0\<close>)
  apply auto
  using div_mult_mod_eq [of w w] by (simp add: div_word_self)

lemma div_word_less:
  \<open>w div v = 0\<close> if \<open>w < v\<close> for w v :: \<open>'a::len word\<close>
  using that by transfer simp

lemma mod_word_less:
  \<open>w mod v = w\<close> if \<open>w < v\<close> for w v :: \<open>'a::len word\<close>
  using div_mult_mod_eq [of w v] using that by (simp add: div_word_less)

lemma div_word_one [simp]:
  \<open>1 div w = of_bool (w = 1)\<close> for w :: \<open>'a::len word\<close>
proof transfer
  fix k :: int
  show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) 1 div take_bit LENGTH('a) k) =
         take_bit LENGTH('a) (of_bool (take_bit LENGTH('a) k = take_bit LENGTH('a) 1))\<close>
  proof (cases \<open>take_bit LENGTH('a) k > 1\<close>)
    case False
    with take_bit_nonnegative [of \<open>LENGTH('a)\<close> k]
    have \<open>take_bit LENGTH('a) k = 0 \<or> take_bit LENGTH('a) k = 1\<close>
      by linarith
    then show ?thesis
      by auto
  next
    case True
    then show ?thesis
      by simp
  qed
qed

lemma mod_word_one [simp]:
  \<open>1 mod w = 1 - w * of_bool (w = 1)\<close> for w :: \<open>'a::len word\<close>
  using div_mult_mod_eq [of 1 w] by auto

lemma div_word_by_minus_1_eq [simp]:
  \<open>w div - 1 = of_bool (w = - 1)\<close> for w :: \<open>'a::len word\<close>
  by (auto intro: div_word_less simp add: div_word_self word_order.not_eq_extremum)

lemma mod_word_by_minus_1_eq [simp]:
  \<open>w mod - 1 = w * of_bool (w < - 1)\<close> for w :: \<open>'a::len word\<close>
proof (cases \<open>w = - 1\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  moreover have \<open>w < - 1\<close>
    using False by (simp add: word_order.not_eq_extremum)
  ultimately show ?thesis
    by (simp add: mod_word_less)
qed

text \<open>Legacy theorems:\<close>

lemma word_add_def [code]:
  "a + b = word_of_int (uint a + uint b)"
  by transfer (simp add: take_bit_add)

lemma word_sub_wi [code]:
  "a - b = word_of_int (uint a - uint b)"
  by transfer (simp add: take_bit_diff)

lemma word_mult_def [code]:
  "a * b = word_of_int (uint a * uint b)"
  by transfer (simp add: take_bit_eq_mod mod_simps)

lemma word_minus_def [code]:
  "- a = word_of_int (- uint a)"
  by transfer (simp add: take_bit_minus)

lemma word_0_wi:
  "0 = word_of_int 0"
  by transfer simp

lemma word_1_wi:
  "1 = word_of_int 1"
  by transfer simp

lift_definition word_succ :: "'a::len word \<Rightarrow> 'a word" is "\<lambda>x. x + 1"
  by (auto simp add: take_bit_eq_mod intro: mod_add_cong)

lift_definition word_pred :: "'a::len word \<Rightarrow> 'a word" is "\<lambda>x. x - 1"
  by (auto simp add: take_bit_eq_mod intro: mod_diff_cong)

lemma word_succ_alt [code]:
  "word_succ a = word_of_int (uint a + 1)"
  by transfer (simp add: take_bit_eq_mod mod_simps)

lemma word_pred_alt [code]:
  "word_pred a = word_of_int (uint a - 1)"
  by transfer (simp add: take_bit_eq_mod mod_simps)

lemmas word_arith_wis = 
  word_add_def word_sub_wi word_mult_def
  word_minus_def word_succ_alt word_pred_alt
  word_0_wi word_1_wi

lemma wi_homs:
  shows wi_hom_add: "word_of_int a + word_of_int b = word_of_int (a + b)"
    and wi_hom_sub: "word_of_int a - word_of_int b = word_of_int (a - b)"
    and wi_hom_mult: "word_of_int a * word_of_int b = word_of_int (a * b)"
    and wi_hom_neg: "- word_of_int a = word_of_int (- a)"
    and wi_hom_succ: "word_succ (word_of_int a) = word_of_int (a + 1)"
    and wi_hom_pred: "word_pred (word_of_int a) = word_of_int (a - 1)"
  by (transfer, simp)+

lemmas wi_hom_syms = wi_homs [symmetric]

lemmas word_of_int_homs = wi_homs word_0_wi word_1_wi

lemmas word_of_int_hom_syms = word_of_int_homs [symmetric]

lemma double_eq_zero_iff:
  \<open>2 * a = 0 \<longleftrightarrow> a = 0 \<or> a = 2 ^ (LENGTH('a) - Suc 0)\<close>
  for a :: \<open>'a::len word\<close>
proof -
  define n where \<open>n = LENGTH('a) - Suc 0\<close>
  then have *: \<open>LENGTH('a) = Suc n\<close>
    by simp
  have \<open>a = 0\<close> if \<open>2 * a = 0\<close> and \<open>a \<noteq> 2 ^ (LENGTH('a) - Suc 0)\<close>
    using that by transfer
      (auto simp add: take_bit_eq_0_iff take_bit_eq_mod *)
  moreover have \<open>2 ^ LENGTH('a) = (0 :: 'a word)\<close>
    by transfer simp
  then have \<open>2 * 2 ^ (LENGTH('a) - Suc 0) = (0 :: 'a word)\<close>
    by (simp add: *)
  ultimately show ?thesis
    by auto
qed


subsection \<open>Ordering\<close>

lift_definition word_sle :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> bool\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k \<le> signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition word_sless :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> bool\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k < signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

notation
  word_sle    ("'(\<le>s')") and
  word_sle    ("(_/ \<le>s _)"  [51, 51] 50) and
  word_sless  ("'(<s')") and
  word_sless  ("(_/ <s _)"  [51, 51] 50)

notation (input)
  word_sle    ("(_/ <=s _)"  [51, 51] 50)

lemma word_sle_eq [code]:
  \<open>a <=s b \<longleftrightarrow> sint a \<le> sint b\<close>
  by transfer simp

lemma [code]:
  \<open>a <s b \<longleftrightarrow> sint a < sint b\<close>
  by transfer simp

lemma signed_ordering: \<open>ordering word_sle word_sless\<close>
  apply (standard; transfer)
  using signed_take_bit_decr_length_iff by force+

lemma signed_linorder: \<open>class.linorder word_sle word_sless\<close>
  by (standard; transfer) (auto simp add: signed_take_bit_decr_length_iff)

interpretation signed: linorder word_sle word_sless
  by (fact signed_linorder)

lemma word_sless_eq:
  \<open>x <s y \<longleftrightarrow> x <=s y \<and> x \<noteq> y\<close>
  by (fact signed.less_le)

lemma word_less_alt: "a < b \<longleftrightarrow> uint a < uint b"
  by (fact word_less_def)

lemma word_zero_le [simp]: "0 \<le> y"
  for y :: "'a::len word"
  by (fact word_coorder.extremum)

lemma word_m1_ge [simp] : "word_pred 0 \<ge> y" (* FIXME: delete *)
  by transfer (simp add: mask_eq_exp_minus_1)

lemma word_n1_ge [simp]: "y \<le> -1"
  for y :: "'a::len word"
  by (fact word_order.extremum)

lemmas word_not_simps [simp] =
  word_zero_le [THEN leD] word_m1_ge [THEN leD] word_n1_ge [THEN leD]

lemma word_gt_0: "0 < y \<longleftrightarrow> 0 \<noteq> y"
  for y :: "'a::len word"
  by (simp add: less_le)

lemmas word_gt_0_no [simp] = word_gt_0 [of "numeral y"] for y

lemma word_sless_alt: "a <s b \<longleftrightarrow> sint a < sint b"
  by transfer simp

lemma word_le_nat_alt: "a \<le> b \<longleftrightarrow> unat a \<le> unat b"
  by transfer (simp add: nat_le_eq_zle)

lemma word_less_nat_alt: "a < b \<longleftrightarrow> unat a < unat b"
  by transfer (auto simp add: less_le [of 0])

lemmas unat_mono = word_less_nat_alt [THEN iffD1]

instance word :: (len) wellorder
proof
  fix P :: "'a word \<Rightarrow> bool" and a
  assume *: "(\<And>b. (\<And>a. a < b \<Longrightarrow> P a) \<Longrightarrow> P b)"
  have "wf (measure unat)" ..
  moreover have "{(a, b :: ('a::len) word). a < b} \<subseteq> measure unat"
    by (auto simp add: word_less_nat_alt)
  ultimately have "wf {(a, b :: ('a::len) word). a < b}"
    by (rule wf_subset)
  then show "P a" using *
    by induction blast
qed

lemma wi_less:
  "(word_of_int n < (word_of_int m :: 'a::len word)) =
    (n mod 2 ^ LENGTH('a) < m mod 2 ^ LENGTH('a))"
  by transfer (simp add: take_bit_eq_mod)

lemma wi_le:
  "(word_of_int n \<le> (word_of_int m :: 'a::len word)) =
    (n mod 2 ^ LENGTH('a) \<le> m mod 2 ^ LENGTH('a))"
  by transfer (simp add: take_bit_eq_mod)


subsection \<open>Bit-wise operations\<close>

context
  includes bit_operations_syntax
begin

lemma uint_take_bit_eq:
  \<open>uint (take_bit n w) = take_bit n (uint w)\<close>
  by transfer (simp add: ac_simps)

lemma take_bit_word_eq_self:
  \<open>take_bit n w = w\<close> if \<open>LENGTH('a) \<le> n\<close> for w :: \<open>'a::len word\<close>
  using that by transfer simp

lemma take_bit_length_eq [simp]:
  \<open>take_bit LENGTH('a) w = w\<close> for w :: \<open>'a::len word\<close>
  by (rule take_bit_word_eq_self) simp

lemma bit_word_of_int_iff:
  \<open>bit (word_of_int k :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> bit k n\<close>
  by transfer rule

lemma bit_uint_iff:
  \<open>bit (uint w) n \<longleftrightarrow> n < LENGTH('a) \<and> bit w n\<close>
    for w :: \<open>'a::len word\<close>
  by transfer (simp add: bit_take_bit_iff)

lemma bit_sint_iff:
  \<open>bit (sint w) n \<longleftrightarrow> n \<ge> LENGTH('a) \<and> bit w (LENGTH('a) - 1) \<or> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (auto simp add: bit_signed_take_bit_iff min_def le_less not_less)

lemma bit_word_ucast_iff:
  \<open>bit (ucast w :: 'b::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> n < LENGTH('b) \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: bit_take_bit_iff ac_simps)

lemma bit_word_scast_iff:
  \<open>bit (scast w :: 'b::len word) n \<longleftrightarrow>
    n < LENGTH('b) \<and> (bit w n \<or> LENGTH('a) \<le> n \<and> bit w (LENGTH('a) - Suc 0))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (auto simp add: bit_signed_take_bit_iff le_less min_def)

lemma bit_word_iff_drop_bit_and [code]:
  \<open>bit a n \<longleftrightarrow> drop_bit n a AND 1 = 1\<close> for a :: \<open>'a::len word\<close>
  by (simp add: bit_iff_odd_drop_bit odd_iff_mod_2_eq_one and_one_eq)

lemma
  word_not_def: "NOT (a::'a::len word) = word_of_int (NOT (uint a))"
    and word_and_def: "(a::'a word) AND b = word_of_int (uint a AND uint b)"
    and word_or_def: "(a::'a word) OR b = word_of_int (uint a OR uint b)"
    and word_xor_def: "(a::'a word) XOR b = word_of_int (uint a XOR uint b)"
  by (transfer, simp add: take_bit_not_take_bit)+

definition even_word :: \<open>'a::len word \<Rightarrow> bool\<close>
  where [code_abbrev]: \<open>even_word = even\<close>

lemma even_word_iff [code]:
  \<open>even_word a \<longleftrightarrow> a AND 1 = 0\<close>
  by (simp add: and_one_eq even_iff_mod_2_eq_zero even_word_def)

lemma map_bit_range_eq_if_take_bit_eq:
  \<open>map (bit k) [0..<n] = map (bit l) [0..<n]\<close>
  if \<open>take_bit n k = take_bit n l\<close> for k l :: int
using that proof (induction n arbitrary: k l)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems have \<open>take_bit n (k div 2) = take_bit n (l div 2)\<close>
    by (simp add: take_bit_Suc)
  then have \<open>map (bit (k div 2)) [0..<n] = map (bit (l div 2)) [0..<n]\<close>
    by (rule Suc.IH)
  moreover have \<open>bit (r div 2) = bit r \<circ> Suc\<close> for r :: int
    by (simp add: fun_eq_iff bit_Suc)
  moreover from Suc.prems have \<open>even k \<longleftrightarrow> even l\<close>
    by (auto simp add: take_bit_Suc elim!: evenE oddE) arith+
  ultimately show ?case
    by (simp only: map_Suc_upt upt_conv_Cons flip: list.map_comp) (simp add: bit_0)
qed

lemma
  take_bit_word_Bit0_eq [simp]: \<open>take_bit (numeral n) (numeral (num.Bit0 m) :: 'a::len word)
    = 2 * take_bit (pred_numeral n) (numeral m)\<close> (is ?P)
  and take_bit_word_Bit1_eq [simp]: \<open>take_bit (numeral n) (numeral (num.Bit1 m) :: 'a::len word)
    = 1 + 2 * take_bit (pred_numeral n) (numeral m)\<close> (is ?Q)
  and take_bit_word_minus_Bit0_eq [simp]: \<open>take_bit (numeral n) (- numeral (num.Bit0 m) :: 'a::len word)
    = 2 * take_bit (pred_numeral n) (- numeral m)\<close> (is ?R)
  and take_bit_word_minus_Bit1_eq [simp]: \<open>take_bit (numeral n) (- numeral (num.Bit1 m) :: 'a::len word)
    = 1 + 2 * take_bit (pred_numeral n) (- numeral (Num.inc m))\<close> (is ?S)
proof -
  define w :: \<open>'a::len word\<close>
    where \<open>w = numeral m\<close>
  moreover define q :: nat
    where \<open>q = pred_numeral n\<close>
  ultimately have num:
    \<open>numeral m = w\<close>
    \<open>numeral (num.Bit0 m) = 2 * w\<close>
    \<open>numeral (num.Bit1 m) = 1 + 2 * w\<close>
    \<open>numeral (Num.inc m) = 1 + w\<close>
    \<open>pred_numeral n = q\<close>
    \<open>numeral n = Suc q\<close>
    by (simp_all only: w_def q_def numeral_Bit0 [of m] numeral_Bit1 [of m] ac_simps
      numeral_inc numeral_eq_Suc flip: mult_2)
  have even: \<open>take_bit (Suc q) (2 * w) = 2 * take_bit q w\<close> for w :: \<open>'a::len word\<close>
    by (rule bit_word_eqI)
      (auto simp add: bit_take_bit_iff bit_double_iff)
  have odd: \<open>take_bit (Suc q) (1 + 2 * w) = 1 + 2 * take_bit q w\<close> for w :: \<open>'a::len word\<close>
    by (rule bit_eqI)
      (auto simp add: bit_take_bit_iff bit_double_iff even_bit_succ_iff)
  show ?P
    using even [of w] by (simp add: num)
  show ?Q
    using odd [of w] by (simp add: num)
  show ?R
    using even [of \<open>- w\<close>] by (simp add: num)
  show ?S
    using odd [of \<open>- (1 + w)\<close>] by (simp add: num)
qed


subsection \<open>More shift operations\<close>

lift_definition signed_drop_bit :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>n. drop_bit n \<circ> signed_take_bit (LENGTH('a) - Suc 0)\<close>
  using signed_take_bit_decr_length_iff
  by (simp add: take_bit_drop_bit) force

lemma bit_signed_drop_bit_iff [bit_simps]:
  \<open>bit (signed_drop_bit m w) n \<longleftrightarrow> bit w (if LENGTH('a) - m \<le> n \<and> n < LENGTH('a) then LENGTH('a) - 1 else m + n)\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (auto simp add: bit_drop_bit_eq bit_signed_take_bit_iff not_le min_def)
   apply (metis add.commute le_antisym less_diff_conv less_eq_decr_length_iff)
  apply (metis le_antisym less_eq_decr_length_iff)
  done

lemma [code]:
  \<open>Word.the_int (signed_drop_bit n w) = take_bit LENGTH('a) (drop_bit n (Word.the_signed_int w))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer simp

lemma signed_drop_bit_of_0 [simp]:
  \<open>signed_drop_bit n 0 = 0\<close>
  by transfer simp

lemma signed_drop_bit_of_minus_1 [simp]:
  \<open>signed_drop_bit n (- 1) = - 1\<close>
  by transfer simp

lemma signed_drop_bit_signed_drop_bit [simp]:
  \<open>signed_drop_bit m (signed_drop_bit n w) = signed_drop_bit (m + n) w\<close>
  for w :: \<open>'a::len word\<close>
proof (cases \<open>LENGTH('a)\<close>)
  case 0
  then show ?thesis
    using len_not_eq_0 by blast
next
  case (Suc n)
  then show ?thesis
    by (force simp add: bit_signed_drop_bit_iff not_le less_diff_conv ac_simps intro!: bit_word_eqI)
qed

lemma signed_drop_bit_0 [simp]:
  \<open>signed_drop_bit 0 w = w\<close>
  by transfer (simp add: take_bit_signed_take_bit)

lemma sint_signed_drop_bit_eq:
  \<open>sint (signed_drop_bit n w) = drop_bit n (sint w)\<close>
proof (cases \<open>LENGTH('a) = 0 \<or> n=0\<close>)
  case False
  then show ?thesis
    apply simp
    apply (rule bit_eqI)
    by (auto simp add: bit_sint_iff bit_drop_bit_eq bit_signed_drop_bit_iff dest: bit_imp_le_length)
qed auto


subsection \<open>Single-bit operations\<close>

lemma set_bit_eq_idem_iff:
  \<open>Bit_Operations.set_bit n w = w \<longleftrightarrow> bit w n \<or> n \<ge> LENGTH('a)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: bit_eq_iff) (auto simp add: bit_simps not_le)

lemma unset_bit_eq_idem_iff:
  \<open>unset_bit n w = w \<longleftrightarrow> bit w n \<longrightarrow> n \<ge> LENGTH('a)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: bit_eq_iff) (auto simp add: bit_simps dest: bit_imp_le_length)

lemma flip_bit_eq_idem_iff:
  \<open>flip_bit n w = w \<longleftrightarrow> n \<ge> LENGTH('a)\<close>
  for w :: \<open>'a::len word\<close>
  using linorder_le_less_linear
  by (simp add: bit_eq_iff) (auto simp add: bit_simps)


subsection \<open>Rotation\<close>

lift_definition word_rotr :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>n k. concat_bit (LENGTH('a) - n mod LENGTH('a))
    (drop_bit (n mod LENGTH('a)) (take_bit LENGTH('a) k))
    (take_bit (n mod LENGTH('a)) k)\<close>
  subgoal for n k l
    by (simp add: concat_bit_def nat_le_iff less_imp_le
      take_bit_tightened [of \<open>LENGTH('a)\<close> k l \<open>n mod LENGTH('a::len)\<close>])
  done

lift_definition word_rotl :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>n k. concat_bit (n mod LENGTH('a))
    (drop_bit (LENGTH('a) - n mod LENGTH('a)) (take_bit LENGTH('a) k))
    (take_bit (LENGTH('a) - n mod LENGTH('a)) k)\<close>
  subgoal for n k l
    by (simp add: concat_bit_def nat_le_iff less_imp_le
      take_bit_tightened [of \<open>LENGTH('a)\<close> k l \<open>LENGTH('a) - n mod LENGTH('a::len)\<close>])
  done

lift_definition word_roti :: \<open>int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>r k. concat_bit (LENGTH('a) - nat (r mod int LENGTH('a)))
    (drop_bit (nat (r mod int LENGTH('a))) (take_bit LENGTH('a) k))
    (take_bit (nat (r mod int LENGTH('a))) k)\<close>
  subgoal for r k l
    by (simp add: concat_bit_def nat_le_iff less_imp_le
      take_bit_tightened [of \<open>LENGTH('a)\<close> k l \<open>nat (r mod int LENGTH('a::len))\<close>])
  done

lemma word_rotl_eq_word_rotr [code]:
  \<open>word_rotl n = (word_rotr (LENGTH('a) - n mod LENGTH('a)) :: 'a::len word \<Rightarrow> 'a word)\<close>
  by (rule ext, cases \<open>n mod LENGTH('a) = 0\<close>; transfer) simp_all

lemma word_roti_eq_word_rotr_word_rotl [code]:
  \<open>word_roti i w =
    (if i \<ge> 0 then word_rotr (nat i) w else word_rotl (nat (- i)) w)\<close>
proof (cases \<open>i \<ge> 0\<close>)
  case True
  moreover define n where \<open>n = nat i\<close>
  ultimately have \<open>i = int n\<close>
    by simp
  moreover have \<open>word_roti (int n) = (word_rotr n :: _ \<Rightarrow> 'a word)\<close>
    by (rule ext, transfer) (simp add: nat_mod_distrib)
  ultimately show ?thesis
    by simp
next
  case False
  moreover define n where \<open>n = nat (- i)\<close>
  ultimately have \<open>i = - int n\<close> \<open>n > 0\<close>
    by simp_all
  moreover have \<open>word_roti (- int n) = (word_rotl n :: _ \<Rightarrow> 'a word)\<close>
    by (rule ext, transfer)
      (simp add: zmod_zminus1_eq_if flip: of_nat_mod of_nat_diff)
  ultimately show ?thesis
    by simp
qed

lemma bit_word_rotr_iff [bit_simps]:
  \<open>bit (word_rotr m w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w ((n + m) mod LENGTH('a))\<close>
  for w :: \<open>'a::len word\<close>
proof transfer
  fix k :: int and m n :: nat
  define q where \<open>q = m mod LENGTH('a)\<close>
  have \<open>q < LENGTH('a)\<close> 
    by (simp add: q_def)
  then have \<open>q \<le> LENGTH('a)\<close>
    by simp
  have \<open>m mod LENGTH('a) = q\<close>
    by (simp add: q_def)
  moreover have \<open>(n + m) mod LENGTH('a) = (n + q) mod LENGTH('a)\<close>
    by (subst mod_add_right_eq [symmetric]) (simp add: \<open>m mod LENGTH('a) = q\<close>)
  moreover have \<open>n < LENGTH('a) \<and>
    bit (concat_bit (LENGTH('a) - q) (drop_bit q (take_bit LENGTH('a) k)) (take_bit q k)) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit k ((n + q) mod LENGTH('a))\<close>
    using \<open>q < LENGTH('a)\<close>
    by (cases \<open>q + n \<ge> LENGTH('a)\<close>)
     (auto simp add: bit_concat_bit_iff bit_drop_bit_eq
        bit_take_bit_iff le_mod_geq ac_simps)
  ultimately show \<open>n < LENGTH('a) \<and>
    bit (concat_bit (LENGTH('a) - m mod LENGTH('a))
      (drop_bit (m mod LENGTH('a)) (take_bit LENGTH('a) k))
      (take_bit (m mod LENGTH('a)) k)) n
    \<longleftrightarrow> n < LENGTH('a) \<and>
      (n + m) mod LENGTH('a) < LENGTH('a) \<and>
      bit k ((n + m) mod LENGTH('a))\<close>
    by simp
qed

lemma bit_word_rotl_iff [bit_simps]:
  \<open>bit (word_rotl m w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w ((n + (LENGTH('a) - m mod LENGTH('a))) mod LENGTH('a))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: word_rotl_eq_word_rotr bit_word_rotr_iff)

lemma bit_word_roti_iff [bit_simps]:
  \<open>bit (word_roti k w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w (nat ((int n + k) mod int LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
proof transfer
  fix k l :: int and n :: nat
  define m where \<open>m = nat (k mod int LENGTH('a))\<close>
  have \<open>m < LENGTH('a)\<close> 
    by (simp add: nat_less_iff m_def)
  then have \<open>m \<le> LENGTH('a)\<close>
    by simp
  have \<open>k mod int LENGTH('a) = int m\<close>
    by (simp add: nat_less_iff m_def)
  moreover have \<open>(int n + k) mod int LENGTH('a) = int ((n + m) mod LENGTH('a))\<close>
    by (subst mod_add_right_eq [symmetric]) (simp add: of_nat_mod \<open>k mod int LENGTH('a) = int m\<close>)
  moreover have \<open>n < LENGTH('a) \<and>
    bit (concat_bit (LENGTH('a) - m) (drop_bit m (take_bit LENGTH('a) l)) (take_bit m l)) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit l ((n + m) mod LENGTH('a))\<close>
    using \<open>m < LENGTH('a)\<close>
    by (cases \<open>m + n \<ge> LENGTH('a)\<close>)
     (auto simp add: bit_concat_bit_iff bit_drop_bit_eq
        bit_take_bit_iff nat_less_iff not_le not_less ac_simps
        le_diff_conv le_mod_geq)
  ultimately show \<open>n < LENGTH('a)
    \<and> bit (concat_bit (LENGTH('a) - nat (k mod int LENGTH('a)))
             (drop_bit (nat (k mod int LENGTH('a))) (take_bit LENGTH('a) l))
             (take_bit (nat (k mod int LENGTH('a))) l)) n \<longleftrightarrow>
       n < LENGTH('a) 
    \<and> nat ((int n + k) mod int LENGTH('a)) < LENGTH('a)
    \<and> bit l (nat ((int n + k) mod int LENGTH('a)))\<close>
    by simp
qed

lemma uint_word_rotr_eq:
  \<open>uint (word_rotr n w) = concat_bit (LENGTH('a) - n mod LENGTH('a))
    (drop_bit (n mod LENGTH('a)) (uint w))
    (uint (take_bit (n mod LENGTH('a)) w))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_concat_bit_eq)

lemma [code]:
  \<open>Word.the_int (word_rotr n w) = concat_bit (LENGTH('a) - n mod LENGTH('a))
    (drop_bit (n mod LENGTH('a)) (Word.the_int w))
    (Word.the_int (take_bit (n mod LENGTH('a)) w))\<close>
  for w :: \<open>'a::len word\<close>
  using uint_word_rotr_eq [of n w] by simp

    
subsection \<open>Split and cat operations\<close>

lift_definition word_cat :: \<open>'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word\<close>
  is \<open>\<lambda>k l. concat_bit LENGTH('b) l (take_bit LENGTH('a) k)\<close>
  by (simp add: bit_eq_iff bit_concat_bit_iff bit_take_bit_iff)

lemma word_cat_eq:
  \<open>(word_cat v w :: 'c::len word) = push_bit LENGTH('b) (ucast v) + ucast w\<close>
  for v :: \<open>'a::len word\<close> and w :: \<open>'b::len word\<close>
  by transfer (simp add: concat_bit_eq ac_simps)

lemma word_cat_eq' [code]:
  \<open>word_cat a b = word_of_int (concat_bit LENGTH('b) (uint b) (uint a))\<close>
  for a :: \<open>'a::len word\<close> and b :: \<open>'b::len word\<close>
  by transfer (simp add: concat_bit_take_bit_eq)

lemma bit_word_cat_iff [bit_simps]:
  \<open>bit (word_cat v w :: 'c::len word) n \<longleftrightarrow> n < LENGTH('c) \<and> (if n < LENGTH('b) then bit w n else bit v (n - LENGTH('b)))\<close> 
  for v :: \<open>'a::len word\<close> and w :: \<open>'b::len word\<close>
  by transfer (simp add: bit_concat_bit_iff bit_take_bit_iff)

definition word_split :: \<open>'a::len word \<Rightarrow> 'b::len word \<times> 'c::len word\<close>
  where \<open>word_split w =
    (ucast (drop_bit LENGTH('c) w) :: 'b::len word, ucast w :: 'c::len word)\<close>

definition word_rcat :: \<open>'a::len word list \<Rightarrow> 'b::len word\<close>
  where \<open>word_rcat = word_of_int \<circ> horner_sum uint (2 ^ LENGTH('a)) \<circ> rev\<close>


subsection \<open>More on conversions\<close>

lemma int_word_sint:
  \<open>sint (word_of_int x :: 'a::len word) = (x + 2 ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('a) - 2 ^ (LENGTH('a) - 1)\<close>
  by transfer (simp flip: take_bit_eq_mod add: signed_take_bit_eq_take_bit_shift)

lemma sint_sbintrunc': "sint (word_of_int bin :: 'a word) = signed_take_bit (LENGTH('a::len) - 1) bin"
  by (simp add: signed_of_int)

lemma uint_sint: "uint w = take_bit LENGTH('a) (sint w)"
  for w :: "'a::len word"
  by transfer (simp add: take_bit_signed_take_bit)

lemma bintr_uint: "LENGTH('a) \<le> n \<Longrightarrow> take_bit n (uint w) = uint w"
  for w :: "'a::len word"
  by transfer (simp add: min_def)

lemma wi_bintr:
  "LENGTH('a::len) \<le> n \<Longrightarrow>
    word_of_int (take_bit n w) = (word_of_int w :: 'a word)"
  by transfer simp

lemma word_numeral_alt: "numeral b = word_of_int (numeral b)"
  by (induct b, simp_all only: numeral.simps word_of_int_homs)

declare word_numeral_alt [symmetric, code_abbrev]

lemma word_neg_numeral_alt: "- numeral b = word_of_int (- numeral b)"
  by (simp only: word_numeral_alt wi_hom_neg)

declare word_neg_numeral_alt [symmetric, code_abbrev]

lemma uint_bintrunc [simp]:
  "uint (numeral bin :: 'a word) =
    take_bit (LENGTH('a::len)) (numeral bin)"
  by transfer rule

lemma uint_bintrunc_neg [simp]:
  "uint (- numeral bin :: 'a word) = take_bit (LENGTH('a::len)) (- numeral bin)"
  by transfer rule

lemma sint_sbintrunc [simp]:
  "sint (numeral bin :: 'a word) = signed_take_bit (LENGTH('a::len) - 1) (numeral bin)"
  by transfer simp

lemma sint_sbintrunc_neg [simp]:
  "sint (- numeral bin :: 'a word) = signed_take_bit (LENGTH('a::len) - 1) (- numeral bin)"
  by transfer simp

lemma unat_bintrunc [simp]:
  "unat (numeral bin :: 'a::len word) = nat (take_bit (LENGTH('a)) (numeral bin))"
  by transfer simp

lemma unat_bintrunc_neg [simp]:
  "unat (- numeral bin :: 'a::len word) = nat (take_bit (LENGTH('a)) (- numeral bin))"
  by transfer simp

lemma size_0_eq: "size w = 0 \<Longrightarrow> v = w"
  for v w :: "'a::len word"
  by transfer simp

lemma uint_ge_0 [iff]: "0 \<le> uint x"
  by (fact unsigned_greater_eq)

lemma uint_lt2p [iff]: "uint x < 2 ^ LENGTH('a)"
  for x :: "'a::len word"
  by (fact unsigned_less)

lemma sint_ge: "- (2 ^ (LENGTH('a) - 1)) \<le> sint x"
  for x :: "'a::len word"
  using sint_greater_eq [of x] by simp

lemma sint_lt: "sint x < 2 ^ (LENGTH('a) - 1)"
  for x :: "'a::len word"
  using sint_less [of x] by simp

lemma uint_m2p_neg: "uint x - 2 ^ LENGTH('a) < 0"
  for x :: "'a::len word"
  by (simp only: diff_less_0_iff_less uint_lt2p)

lemma uint_m2p_not_non_neg: "\<not> 0 \<le> uint x - 2 ^ LENGTH('a)"
  for x :: "'a::len word"
  by (simp only: not_le uint_m2p_neg)

lemma lt2p_lem: "LENGTH('a) \<le> n \<Longrightarrow> uint w < 2 ^ n"
  for w :: "'a::len word"
  using uint_bounded [of w] by (rule less_le_trans) simp

lemma uint_le_0_iff [simp]: "uint x \<le> 0 \<longleftrightarrow> uint x = 0"
  by (fact uint_ge_0 [THEN leD, THEN antisym_conv1])

lemma uint_nat: "uint w = int (unat w)"
  by transfer simp

lemma uint_numeral: "uint (numeral b :: 'a::len word) = numeral b mod 2 ^ LENGTH('a)"
  by (simp flip: take_bit_eq_mod add: of_nat_take_bit)

lemma uint_neg_numeral: "uint (- numeral b :: 'a::len word) = - numeral b mod 2 ^ LENGTH('a)"
  by (simp flip: take_bit_eq_mod add: of_nat_take_bit)

lemma unat_numeral: "unat (numeral b :: 'a::len word) = numeral b mod 2 ^ LENGTH('a)"
  by transfer (simp add: take_bit_eq_mod nat_mod_distrib nat_power_eq)

lemma sint_numeral:
  "sint (numeral b :: 'a::len word) =
    (numeral b + 2 ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('a) - 2 ^ (LENGTH('a) - 1)"
  by (metis int_word_sint word_numeral_alt)

lemma word_of_int_0 [simp, code_post]: "word_of_int 0 = 0"
  by (fact of_int_0)

lemma word_of_int_1 [simp, code_post]: "word_of_int 1 = 1"
  by (fact of_int_1)

lemma word_of_int_neg_1 [simp]: "word_of_int (- 1) = - 1"
  by (simp add: wi_hom_syms)

lemma word_of_int_numeral [simp] : "(word_of_int (numeral bin) :: 'a::len word) = numeral bin"
  by (fact of_int_numeral)

lemma word_of_int_neg_numeral [simp]:
  "(word_of_int (- numeral bin) :: 'a::len word) = - numeral bin"
  by (fact of_int_neg_numeral)

lemma word_int_case_wi:
  "word_int_case f (word_of_int i :: 'b word) = f (i mod 2 ^ LENGTH('b::len))"
  by transfer (simp add: take_bit_eq_mod)

lemma word_int_split:
  "P (word_int_case f x) =
    (\<forall>i. x = (word_of_int i :: 'b::len word) \<and> 0 \<le> i \<and> i < 2 ^ LENGTH('b) \<longrightarrow> P (f i))"
  by transfer (auto simp add: take_bit_eq_mod)

lemma word_int_split_asm:
  "P (word_int_case f x) =
    (\<nexists>n. x = (word_of_int n :: 'b::len word) \<and> 0 \<le> n \<and> n < 2 ^ LENGTH('b::len) \<and> \<not> P (f n))"
  by transfer (auto simp add: take_bit_eq_mod)

lemma uint_range_size: "0 \<le> uint w \<and> uint w < 2 ^ size w"
  by transfer simp

lemma sint_range_size: "- (2 ^ (size w - Suc 0)) \<le> sint w \<and> sint w < 2 ^ (size w - Suc 0)"
  by (simp add: word_size sint_greater_eq sint_less)

lemma sint_above_size: "2 ^ (size w - 1) \<le> x \<Longrightarrow> sint w < x"
  for w :: "'a::len word"
  unfolding word_size by (rule less_le_trans [OF sint_lt])

lemma sint_below_size: "x \<le> - (2 ^ (size w - 1)) \<Longrightarrow> x \<le> sint w"
  for w :: "'a::len word"
  unfolding word_size by (rule order_trans [OF _ sint_ge])

lemma word_unat_eq_iff:
  \<open>v = w \<longleftrightarrow> unat v = unat w\<close>
  for v w :: \<open>'a::len word\<close>
  by (fact word_eq_iff_unsigned)


subsection \<open>Testing bits\<close>

lemma bin_nth_uint_imp: "bit (uint w) n \<Longrightarrow> n < LENGTH('a)"
  for w :: "'a::len word"
  by transfer (simp add: bit_take_bit_iff)

lemma bin_nth_sint:
  "LENGTH('a) \<le> n \<Longrightarrow>
    bit (sint w) n = bit (sint w) (LENGTH('a) - 1)"
  for w :: "'a::len word"
  by (transfer fixing: n) (simp add: bit_signed_take_bit_iff le_diff_conv min_def)

lemma num_of_bintr':
  "take_bit (LENGTH('a::len)) (numeral a :: int) = (numeral b) \<Longrightarrow>
    numeral a = (numeral b :: 'a word)"
proof (transfer fixing: a b)
  assume \<open>take_bit LENGTH('a) (numeral a :: int) = numeral b\<close>
  then have \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (numeral a :: int)) = take_bit LENGTH('a) (numeral b)\<close>
    by simp
  then show \<open>take_bit LENGTH('a) (numeral a :: int) = take_bit LENGTH('a) (numeral b)\<close>
    by simp
qed

lemma num_of_sbintr':
  "signed_take_bit (LENGTH('a::len) - 1) (numeral a :: int) = (numeral b) \<Longrightarrow>
    numeral a = (numeral b :: 'a word)"
proof (transfer fixing: a b)
  assume \<open>signed_take_bit (LENGTH('a) - 1) (numeral a :: int) = numeral b\<close>
  then have \<open>take_bit LENGTH('a) (signed_take_bit (LENGTH('a) - 1) (numeral a :: int)) = take_bit LENGTH('a) (numeral b)\<close>
    by simp
  then show \<open>take_bit LENGTH('a) (numeral a :: int) = take_bit LENGTH('a) (numeral b)\<close>
    by (simp add: take_bit_signed_take_bit)
qed
 
lemma num_abs_bintr:
  "(numeral x :: 'a word) =
    word_of_int (take_bit (LENGTH('a::len)) (numeral x))"
  by transfer simp

lemma num_abs_sbintr:
  "(numeral x :: 'a word) =
    word_of_int (signed_take_bit (LENGTH('a::len) - 1) (numeral x))"
  by transfer (simp add: take_bit_signed_take_bit)

text \<open>
  \<open>cast\<close> -- note, no arg for new length, as it's determined by type of result,
  thus in \<open>cast w = w\<close>, the type means cast to length of \<open>w\<close>!
\<close>

lemma bit_ucast_iff:
  \<open>bit (ucast a :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a::len) \<and> bit a n\<close>
  by transfer (simp add: bit_take_bit_iff)

lemma ucast_id [simp]: "ucast w = w"
  by transfer simp

lemma scast_id [simp]: "scast w = w"
  by transfer (simp add: take_bit_signed_take_bit)

lemma ucast_mask_eq:
  \<open>ucast (mask n :: 'b word) = mask (min LENGTH('b::len) n)\<close>
  by (simp add: bit_eq_iff) (auto simp add: bit_mask_iff bit_ucast_iff)

\<comment> \<open>literal u(s)cast\<close>
lemma ucast_bintr [simp]:
  "ucast (numeral w :: 'a::len word) =
    word_of_int (take_bit (LENGTH('a)) (numeral w))"
  by transfer simp

(* TODO: neg_numeral *)

lemma scast_sbintr [simp]:
  "scast (numeral w ::'a::len word) =
    word_of_int (signed_take_bit (LENGTH('a) - Suc 0) (numeral w))"
  by transfer simp

lemma source_size: "source_size (c::'a::len word \<Rightarrow> _) = LENGTH('a)"
  by transfer simp

lemma target_size: "target_size (c::_ \<Rightarrow> 'b::len word) = LENGTH('b)"
  by transfer simp

lemma is_down: "is_down c \<longleftrightarrow> LENGTH('b) \<le> LENGTH('a)"
  for c :: "'a::len word \<Rightarrow> 'b::len word"
  by transfer simp

lemma is_up: "is_up c \<longleftrightarrow> LENGTH('a) \<le> LENGTH('b)"
  for c :: "'a::len word \<Rightarrow> 'b::len word"
  by transfer simp

lemma is_up_down:
  \<open>is_up c \<longleftrightarrow> is_down d\<close>
  for c :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  and d :: \<open>'b::len word \<Rightarrow> 'a::len word\<close>
  by transfer simp

context
  fixes dummy_types :: \<open>'a::len \<times> 'b::len\<close>
begin

private abbreviation (input) UCAST :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>UCAST == ucast\<close>

private abbreviation (input) SCAST :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>SCAST == scast\<close>

lemma down_cast_same:
  \<open>UCAST = scast\<close> if \<open>is_down UCAST\<close>
  by (rule ext, use that in transfer) (simp add: take_bit_signed_take_bit)

lemma sint_up_scast:
  \<open>sint (SCAST w) = sint w\<close> if \<open>is_up SCAST\<close>
  using that by transfer (simp add: min_def Suc_leI le_diff_iff)

lemma uint_up_ucast:
  \<open>uint (UCAST w) = uint w\<close> if \<open>is_up UCAST\<close>
  using that by transfer (simp add: min_def)

lemma ucast_up_ucast:
  \<open>ucast (UCAST w) = ucast w\<close> if \<open>is_up UCAST\<close>
  using that by transfer (simp add: ac_simps)

lemma ucast_up_ucast_id:
  \<open>ucast (UCAST w) = w\<close> if \<open>is_up UCAST\<close>
  using that by (simp add: ucast_up_ucast)

lemma scast_up_scast:
  \<open>scast (SCAST w) = scast w\<close> if \<open>is_up SCAST\<close>
  using that by transfer (simp add: ac_simps)

lemma scast_up_scast_id:
  \<open>scast (SCAST w) = w\<close> if \<open>is_up SCAST\<close>
  using that by (simp add: scast_up_scast)

lemma isduu:
  \<open>is_up UCAST\<close> if \<open>is_down d\<close>
    for d :: \<open>'b word \<Rightarrow> 'a word\<close>
  using that is_up_down [of UCAST d] by simp

lemma isdus:
  \<open>is_up SCAST\<close> if \<open>is_down d\<close>
    for d :: \<open>'b word \<Rightarrow> 'a word\<close>
  using that is_up_down [of SCAST d] by simp

lemmas ucast_down_ucast_id = isduu [THEN ucast_up_ucast_id]
lemmas scast_down_scast_id = isdus [THEN scast_up_scast_id]

lemma up_ucast_surj:
  \<open>surj (ucast :: 'b word \<Rightarrow> 'a word)\<close> if \<open>is_up UCAST\<close>
  by (rule surjI) (use that in \<open>rule ucast_up_ucast_id\<close>)

lemma up_scast_surj:
  \<open>surj (scast :: 'b word \<Rightarrow> 'a word)\<close> if \<open>is_up SCAST\<close>
  by (rule surjI) (use that in \<open>rule scast_up_scast_id\<close>)

lemma down_ucast_inj:
  \<open>inj_on UCAST A\<close> if \<open>is_down (ucast :: 'b word \<Rightarrow> 'a word)\<close>
  by (rule inj_on_inverseI) (use that in \<open>rule ucast_down_ucast_id\<close>)

lemma down_scast_inj:
  \<open>inj_on SCAST A\<close> if \<open>is_down (scast :: 'b word \<Rightarrow> 'a word)\<close>
  by (rule inj_on_inverseI) (use that in \<open>rule scast_down_scast_id\<close>)
  
lemma ucast_down_wi:
  \<open>UCAST (word_of_int x) = word_of_int x\<close> if \<open>is_down UCAST\<close>
  using that by transfer simp

lemma ucast_down_no:
  \<open>UCAST (numeral bin) = numeral bin\<close> if \<open>is_down UCAST\<close>
  using that by transfer simp

end

lemmas word_log_defs = word_and_def word_or_def word_xor_def word_not_def

lemma bit_last_iff:
  \<open>bit w (LENGTH('a) - Suc 0) \<longleftrightarrow> sint w < 0\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  for w :: \<open>'a::len word\<close>
proof -
  have \<open>?P \<longleftrightarrow> bit (uint w) (LENGTH('a) - Suc 0)\<close>
    by (simp add: bit_uint_iff)
  also have \<open>\<dots> \<longleftrightarrow> ?Q\<close>
    by (simp add: sint_uint)
  finally show ?thesis .
qed

lemma drop_bit_eq_zero_iff_not_bit_last:
  \<open>drop_bit (LENGTH('a) - Suc 0) w = 0 \<longleftrightarrow> \<not> bit w (LENGTH('a) - Suc 0)\<close>
  for w :: "'a::len word"
proof (cases \<open>LENGTH('a)\<close>)
  case (Suc n)
  then show ?thesis
    apply transfer
    apply (simp add: take_bit_drop_bit)
    by (simp add: bit_iff_odd_drop_bit drop_bit_take_bit odd_iff_mod_2_eq_one)
qed auto

lemma unat_div:
  \<open>unat (x div y) = unat x div unat y\<close>
  by (fact unat_div_distrib)

lemma unat_mod:
  \<open>unat (x mod y) = unat x mod unat y\<close>
  by (fact unat_mod_distrib)


subsection \<open>Word Arithmetic\<close>

lemmas less_eq_word_numeral_numeral [simp] =
  word_le_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_word_numeral_numeral [simp] =
  word_less_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_eq_word_minus_numeral_numeral [simp] =
  word_le_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_word_minus_numeral_numeral [simp] =
  word_less_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_eq_word_numeral_minus_numeral [simp] =
  word_le_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_word_numeral_minus_numeral [simp] =
  word_less_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_eq_word_minus_numeral_minus_numeral [simp] =
  word_le_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_word_minus_numeral_minus_numeral [simp] =
  word_less_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_word_numeral_minus_1 [simp] =
  word_less_def [of \<open>numeral a\<close> \<open>- 1\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas less_word_minus_numeral_minus_1 [simp] =
  word_less_def [of \<open>- numeral a\<close> \<open>- 1\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b

lemmas sless_eq_word_numeral_numeral [simp] =
  word_sle_eq [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_word_numeral_numeral [simp] =
  word_sless_alt [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_eq_word_minus_numeral_numeral [simp] =
  word_sle_eq [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_word_minus_numeral_numeral [simp] =
  word_sless_alt [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_eq_word_numeral_minus_numeral [simp] =
  word_sle_eq [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_word_numeral_minus_numeral [simp] =
  word_sless_alt [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_eq_word_minus_numeral_minus_numeral [simp] =
  word_sle_eq [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sless_word_minus_numeral_minus_numeral [simp] =
  word_sless_alt [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b

lemmas div_word_numeral_numeral [simp] =
  word_div_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas div_word_minus_numeral_numeral [simp] =
  word_div_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas div_word_numeral_minus_numeral [simp] =
  word_div_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas div_word_minus_numeral_minus_numeral [simp] =
  word_div_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas div_word_minus_1_numeral [simp] =
  word_div_def [of \<open>- 1\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas div_word_minus_1_minus_numeral [simp] =
  word_div_def [of \<open>- 1\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b

lemmas mod_word_numeral_numeral [simp] =
  word_mod_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas mod_word_minus_numeral_numeral [simp] =
  word_mod_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas mod_word_numeral_minus_numeral [simp] =
  word_mod_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas mod_word_minus_numeral_minus_numeral [simp] =
  word_mod_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas mod_word_minus_1_numeral [simp] =
  word_mod_def [of \<open>- 1\<close> \<open>numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b
lemmas mod_word_minus_1_minus_numeral [simp] =
  word_mod_def [of \<open>- 1\<close> \<open>- numeral b\<close>, simplified uint_bintrunc uint_bintrunc_neg unsigned_minus_1_eq_mask mask_eq_exp_minus_1]
  for a b

lemma signed_drop_bit_of_1 [simp]:
  \<open>signed_drop_bit n (1 :: 'a::len word) = of_bool (LENGTH('a) = 1 \<or> n = 0)\<close>
  apply (transfer fixing: n)
  apply (cases \<open>LENGTH('a)\<close>)
   apply (auto simp add: take_bit_signed_take_bit)
  apply (auto simp add: take_bit_drop_bit gr0_conv_Suc simp flip: take_bit_eq_self_iff_drop_bit_eq_0)
  done

lemma take_bit_word_beyond_length_eq:
  \<open>take_bit n w = w\<close> if \<open>LENGTH('a) \<le> n\<close> for w :: \<open>'a::len word\<close>
  using that by transfer simp

lemmas word_div_no [simp] = word_div_def [of "numeral a" "numeral b"] for a b
lemmas word_mod_no [simp] = word_mod_def [of "numeral a" "numeral b"] for a b
lemmas word_less_no [simp] = word_less_def [of "numeral a" "numeral b"] for a b
lemmas word_le_no [simp] = word_le_def [of "numeral a" "numeral b"] for a b
lemmas word_sless_no [simp] = word_sless_eq [of "numeral a" "numeral b"] for a b
lemmas word_sle_no [simp] = word_sle_eq [of "numeral a" "numeral b"] for a b

lemma size_0_same': "size w = 0 \<Longrightarrow> w = v"
  for v w :: "'a::len word"
  by (unfold word_size) simp

lemmas size_0_same = size_0_same' [unfolded word_size]

lemmas unat_eq_0 = unat_0_iff
lemmas unat_eq_zero = unat_0_iff

lemma mask_1: "mask 1 = 1"
  by simp

lemma mask_Suc_0: "mask (Suc 0) = 1"
  by simp

lemma bin_last_bintrunc: "odd (take_bit l n) \<longleftrightarrow> l > 0 \<and> odd n"
  by simp

lemma push_bit_word_beyond [simp]:
  \<open>push_bit n w = 0\<close> if \<open>LENGTH('a) \<le> n\<close> for w :: \<open>'a::len word\<close>
  using that by (transfer fixing: n) (simp add: take_bit_push_bit)

lemma drop_bit_word_beyond [simp]:
  \<open>drop_bit n w = 0\<close> if \<open>LENGTH('a) \<le> n\<close> for w :: \<open>'a::len word\<close>
  using that by (transfer fixing: n) (simp add: drop_bit_take_bit)

lemma signed_drop_bit_beyond:
  \<open>signed_drop_bit n w = (if bit w (LENGTH('a) - Suc 0) then - 1 else 0)\<close>
  if \<open>LENGTH('a) \<le> n\<close> for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (simp add: bit_signed_drop_bit_iff that)

lemma take_bit_numeral_minus_numeral_word [simp]:
  \<open>take_bit (numeral m) (- numeral n :: 'a::len word) =
    (case take_bit_num (numeral m) n of None \<Rightarrow> 0 | Some q \<Rightarrow> take_bit (numeral m) (2 ^ numeral m - numeral q))\<close> (is \<open>?lhs = ?rhs\<close>)
proof (cases \<open>LENGTH('a) \<le> numeral m\<close>)
  case True
  then have *: \<open>(take_bit (numeral m) :: 'a word \<Rightarrow> 'a word) = id\<close>
    by (simp add: fun_eq_iff take_bit_word_eq_self)
  have **: \<open>2 ^ numeral m = (0 :: 'a word)\<close>
    using True by (simp flip: exp_eq_zero_iff)
  show ?thesis
    by (auto simp only: * ** split: option.split
      dest!: take_bit_num_eq_None_imp [where ?'a = \<open>'a word\<close>] take_bit_num_eq_Some_imp [where ?'a = \<open>'a word\<close>])
      simp_all
next
  case False
  then show ?thesis
    by (transfer fixing: m n) simp
qed

lemma of_nat_inverse:
  \<open>word_of_nat r = a \<Longrightarrow> r < 2 ^ LENGTH('a) \<Longrightarrow> unat a = r\<close>
  for a :: \<open>'a::len word\<close>
  by (metis id_apply of_nat_eq_id take_bit_nat_eq_self_iff unsigned_of_nat)


subsection \<open>Transferring goals from words to ints\<close>

lemma word_ths:
  shows word_succ_p1: "word_succ a = a + 1"
    and word_pred_m1: "word_pred a = a - 1"
    and word_pred_succ: "word_pred (word_succ a) = a"
    and word_succ_pred: "word_succ (word_pred a) = a"
    and word_mult_succ: "word_succ a * b = b + a * b"
  by (transfer, simp add: algebra_simps)+

lemma uint_cong: "x = y \<Longrightarrow> uint x = uint y"
  by simp

lemma uint_word_ariths:
  fixes a b :: "'a::len word"
  shows "uint (a + b) = (uint a + uint b) mod 2 ^ LENGTH('a::len)"
    and "uint (a - b) = (uint a - uint b) mod 2 ^ LENGTH('a)"
    and "uint (a * b) = uint a * uint b mod 2 ^ LENGTH('a)"
    and "uint (- a) = - uint a mod 2 ^ LENGTH('a)"
    and "uint (word_succ a) = (uint a + 1) mod 2 ^ LENGTH('a)"
    and "uint (word_pred a) = (uint a - 1) mod 2 ^ LENGTH('a)"
    and "uint (0 :: 'a word) = 0 mod 2 ^ LENGTH('a)"
    and "uint (1 :: 'a word) = 1 mod 2 ^ LENGTH('a)"
  by (simp_all only: word_arith_wis uint_word_of_int_eq flip: take_bit_eq_mod)

lemma uint_word_arith_bintrs:
  fixes a b :: "'a::len word"
  shows "uint (a + b) = take_bit (LENGTH('a)) (uint a + uint b)"
    and "uint (a - b) = take_bit (LENGTH('a)) (uint a - uint b)"
    and "uint (a * b) = take_bit (LENGTH('a)) (uint a * uint b)"
    and "uint (- a) = take_bit (LENGTH('a)) (- uint a)"
    and "uint (word_succ a) = take_bit (LENGTH('a)) (uint a + 1)"
    and "uint (word_pred a) = take_bit (LENGTH('a)) (uint a - 1)"
    and "uint (0 :: 'a word) = take_bit (LENGTH('a)) 0"
    and "uint (1 :: 'a word) = take_bit (LENGTH('a)) 1"
  by (simp_all add: uint_word_ariths take_bit_eq_mod)

lemma sint_word_ariths:
  fixes a b :: "'a::len word"
  shows "sint (a + b) = signed_take_bit (LENGTH('a) - 1) (sint a + sint b)"
    and "sint (a - b) = signed_take_bit (LENGTH('a) - 1) (sint a - sint b)"
    and "sint (a * b) = signed_take_bit (LENGTH('a) - 1) (sint a * sint b)"
    and "sint (- a) = signed_take_bit (LENGTH('a) - 1) (- sint a)"
    and "sint (word_succ a) = signed_take_bit (LENGTH('a) - 1) (sint a + 1)"
    and "sint (word_pred a) = signed_take_bit (LENGTH('a) - 1) (sint a - 1)"
    and "sint (0 :: 'a word) = signed_take_bit (LENGTH('a) - 1) 0"
    and "sint (1 :: 'a word) = signed_take_bit (LENGTH('a) - 1) 1"
  subgoal
    by transfer (simp add: signed_take_bit_add)
  subgoal
    by transfer (simp add: signed_take_bit_diff)
  subgoal
    by transfer (simp add: signed_take_bit_mult)
  subgoal
    by transfer (simp add: signed_take_bit_minus)
     apply (metis of_int_sint scast_id sint_sbintrunc' wi_hom_succ)
    apply (metis of_int_sint scast_id sint_sbintrunc' wi_hom_pred)
   apply (simp_all add: sint_uint)
  done

lemma word_pred_0_n1: "word_pred 0 = word_of_int (- 1)"
  unfolding word_pred_m1 by simp

lemma succ_pred_no [simp]:
    "word_succ (numeral w) = numeral w + 1"
    "word_pred (numeral w) = numeral w - 1"
    "word_succ (- numeral w) = - numeral w + 1"
    "word_pred (- numeral w) = - numeral w - 1"
  by (simp_all add: word_succ_p1 word_pred_m1)

lemma word_sp_01 [simp]:
  "word_succ (- 1) = 0 \<and> word_succ 0 = 1 \<and> word_pred 0 = - 1 \<and> word_pred 1 = 0"
  by (simp_all add: word_succ_p1 word_pred_m1)

\<comment> \<open>alternative approach to lifting arithmetic equalities\<close>
lemma word_of_int_Ex: "\<exists>y. x = word_of_int y"
  by (rule_tac x="uint x" in exI) simp


subsection \<open>Order on fixed-length words\<close>

lift_definition udvd :: \<open>'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool\<close> (infixl \<open>udvd\<close> 50)
  is \<open>\<lambda>k l. take_bit LENGTH('a) k dvd take_bit LENGTH('a) l\<close> by simp

lemma udvd_iff_dvd:
  \<open>x udvd y \<longleftrightarrow> unat x dvd unat y\<close>
  by transfer (simp add: nat_dvd_iff)

lemma udvd_iff_dvd_int:
  \<open>v udvd w \<longleftrightarrow> uint v dvd uint w\<close>
  by transfer rule

lemma udvdI [intro]:
  \<open>v udvd w\<close> if \<open>unat w = unat v * unat u\<close>
proof -
  from that have \<open>unat v dvd unat w\<close> ..
  then show ?thesis
    by (simp add: udvd_iff_dvd)
qed

lemma udvdE [elim]:
  fixes v w :: \<open>'a::len word\<close>
  assumes \<open>v udvd w\<close>
  obtains u :: \<open>'a word\<close> where \<open>unat w = unat v * unat u\<close>
proof (cases \<open>v = 0\<close>)
  case True
  moreover from True \<open>v udvd w\<close> have \<open>w = 0\<close>
    by transfer simp
  ultimately show thesis
    using that by simp
next
  case False
  then have \<open>unat v > 0\<close>
    by (simp add: unat_gt_0)
  from \<open>v udvd w\<close> have \<open>unat v dvd unat w\<close>
    by (simp add: udvd_iff_dvd)
  then obtain n where \<open>unat w = unat v * n\<close> ..
  moreover have \<open>n < 2 ^ LENGTH('a)\<close>
  proof (rule ccontr)
    assume \<open>\<not> n < 2 ^ LENGTH('a)\<close>
    then have \<open>n \<ge> 2 ^ LENGTH('a)\<close>
      by (simp add: not_le)
    then have \<open>unat v * n \<ge> 2 ^ LENGTH('a)\<close>
      using \<open>unat v > 0\<close> mult_le_mono [of 1 \<open>unat v\<close> \<open>2 ^ LENGTH('a)\<close> n]
      by simp
    with \<open>unat w = unat v * n\<close>
    have \<open>unat w \<ge> 2 ^ LENGTH('a)\<close>
      by simp
    with unsigned_less [of w, where ?'a = nat] show False
      by linarith
  qed
  ultimately have \<open>unat w = unat v * unat (word_of_nat n :: 'a word)\<close>
    by (auto simp add: take_bit_nat_eq_self_iff unsigned_of_nat intro: sym)
  with that show thesis .
qed

lemma udvd_imp_mod_eq_0:
  \<open>w mod v = 0\<close> if \<open>v udvd w\<close>
  using that by transfer simp

lemma mod_eq_0_imp_udvd [intro?]:
  \<open>v udvd w\<close> if \<open>w mod v = 0\<close>
proof -
  from that have \<open>unat (w mod v) = unat 0\<close>
    by simp
  then have \<open>unat w mod unat v = 0\<close>
    by (simp add: unat_mod_distrib)
  then have \<open>unat v dvd unat w\<close> ..
  then show ?thesis
    by (simp add: udvd_iff_dvd)
qed

lemma udvd_imp_dvd:
  \<open>v dvd w\<close> if \<open>v udvd w\<close> for v w :: \<open>'a::len word\<close>
proof -
  from that obtain u :: \<open>'a word\<close> where \<open>unat w = unat v * unat u\<close> ..
  then have \<open>(word_of_nat (unat w) :: 'a word) = word_of_nat (unat v * unat u)\<close>
    by simp
  then have \<open>w = v * u\<close>
    by simp
  then show \<open>v dvd w\<close> ..
qed

lemma exp_dvd_iff_exp_udvd:
  \<open>2 ^ n dvd w \<longleftrightarrow> 2 ^ n udvd w\<close> for v w :: \<open>'a::len word\<close>
proof
  assume \<open>2 ^ n udvd w\<close> then show \<open>2 ^ n dvd w\<close>
    by (rule udvd_imp_dvd) 
next
  assume \<open>2 ^ n dvd w\<close>
  then obtain u :: \<open>'a word\<close> where \<open>w = 2 ^ n * u\<close> ..
  then have \<open>w = push_bit n u\<close>
    by (simp add: push_bit_eq_mult)
  then show \<open>2 ^ n udvd w\<close>
    by transfer (simp add: take_bit_push_bit dvd_eq_mod_eq_0 flip: take_bit_eq_mod)
qed

lemma udvd_nat_alt:
  \<open>a udvd b \<longleftrightarrow> (\<exists>n. unat b = n * unat a)\<close>
  by (auto simp add: udvd_iff_dvd)

lemma udvd_unfold_int:
  \<open>a udvd b \<longleftrightarrow> (\<exists>n\<ge>0. uint b = n * uint a)\<close>
  unfolding udvd_iff_dvd_int
  by (metis dvd_div_mult_self dvd_triv_right uint_div_distrib uint_ge_0)

lemma unat_minus_one:
  \<open>unat (w - 1) = unat w - 1\<close> if \<open>w \<noteq> 0\<close>
proof -
  have "0 \<le> uint w" by (fact uint_nonnegative)
  moreover from that have "0 \<noteq> uint w"
    by (simp add: uint_0_iff)
  ultimately have "1 \<le> uint w"
    by arith
  from uint_lt2p [of w] have "uint w - 1 < 2 ^ LENGTH('a)"
    by arith
  with \<open>1 \<le> uint w\<close> have "(uint w - 1) mod 2 ^ LENGTH('a) = uint w - 1"
    by (auto intro: mod_pos_pos_trivial)
  with \<open>1 \<le> uint w\<close> have "nat ((uint w - 1) mod 2 ^ LENGTH('a)) = nat (uint w) - 1"
    by (auto simp del: nat_uint_eq)
  then show ?thesis
    by (simp only: unat_eq_nat_uint word_arith_wis mod_diff_right_eq)
      (metis of_int_1 uint_word_of_int unsigned_1)
qed

lemma measure_unat: "p \<noteq> 0 \<Longrightarrow> unat (p - 1) < unat p"
  by (simp add: unat_minus_one) (simp add: unat_0_iff [symmetric])

lemmas uint_add_ge0 [simp] = add_nonneg_nonneg [OF uint_ge_0 uint_ge_0]
lemmas uint_mult_ge0 [simp] = mult_nonneg_nonneg [OF uint_ge_0 uint_ge_0]

lemma uint_sub_lt2p [simp]: "uint x - uint y < 2 ^ LENGTH('a)"
  for x :: "'a::len word" and y :: "'b::len word"
  using uint_ge_0 [of y] uint_lt2p [of x] by arith


subsection \<open>Conditions for the addition (etc) of two words to overflow\<close>

lemma uint_add_lem:
  "(uint x + uint y < 2 ^ LENGTH('a)) =
    (uint (x + y) = uint x + uint y)"
  for x y :: "'a::len word"
  by (metis add.right_neutral add_mono_thms_linordered_semiring(1) mod_pos_pos_trivial of_nat_0_le_iff uint_lt2p uint_nat uint_word_ariths(1))

lemma uint_mult_lem:
  "(uint x * uint y < 2 ^ LENGTH('a)) =
    (uint (x * y) = uint x * uint y)"
  for x y :: "'a::len word"
  by (metis mod_pos_pos_trivial uint_lt2p uint_mult_ge0 uint_word_ariths(3))

lemma uint_sub_lem: "uint x \<ge> uint y \<longleftrightarrow> uint (x - y) = uint x - uint y"
  by (simp add: uint_word_arith_bintrs take_bit_int_eq_self_iff)

lemma uint_add_le: "uint (x + y) \<le> uint x + uint y"
  unfolding uint_word_ariths by (simp add: zmod_le_nonneg_dividend) 

lemma uint_sub_ge: "uint (x - y) \<ge> uint x - uint y"
  unfolding uint_word_ariths
  by (simp flip: take_bit_eq_mod add: take_bit_int_greater_eq_self_iff)

lemma int_mod_ge: \<open>a \<le> a mod n\<close> if \<open>a < n\<close> \<open>0 < n\<close>
  for a n :: int
  using that order.trans [of a 0 \<open>a mod n\<close>] by (cases \<open>a < 0\<close>) auto

lemma mod_add_if_z:
  "\<lbrakk>x < z; y < z; 0 \<le> y; 0 \<le> x; 0 \<le> z\<rbrakk> \<Longrightarrow>
    (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  for x y z :: int
  apply (simp add: not_less)
  by (metis (no_types) add_strict_mono diff_ge_0_iff_ge diff_less_eq minus_mod_self2 mod_pos_pos_trivial)

lemma uint_plus_if':
  "uint (a + b) =
    (if uint a + uint b < 2 ^ LENGTH('a) then uint a + uint b
     else uint a + uint b - 2 ^ LENGTH('a))"
  for a b :: "'a::len word"
  using mod_add_if_z [of "uint a" _ "uint b"] by (simp add: uint_word_ariths)

lemma mod_sub_if_z:
  "\<lbrakk>x < z; y < z; 0 \<le> y; 0 \<le> x; 0 \<le> z\<rbrakk> \<Longrightarrow>
    (x - y) mod z = (if y \<le> x then x - y else x - y + z)"
  for x y z :: int
  using mod_pos_pos_trivial [of "x - y + z" z] by (auto simp add: not_le)

lemma uint_sub_if':
  "uint (a - b) =
    (if uint b \<le> uint a then uint a - uint b
     else uint a - uint b + 2 ^ LENGTH('a))"
  for a b :: "'a::len word"
  using mod_sub_if_z [of "uint a" _ "uint b"] by (simp add: uint_word_ariths)

lemma word_of_int_inverse:
  "word_of_int r = a \<Longrightarrow> 0 \<le> r \<Longrightarrow> r < 2 ^ LENGTH('a) \<Longrightarrow> uint a = r"
  for a :: "'a::len word"
  by transfer (simp add: take_bit_int_eq_self)

lemma unat_split: "P (unat x) \<longleftrightarrow> (\<forall>n. of_nat n = x \<and> n < 2^LENGTH('a) \<longrightarrow> P n)"
  for x :: "'a::len word"
  by (auto simp add: unsigned_of_nat take_bit_nat_eq_self)

lemma unat_split_asm: "P (unat x) \<longleftrightarrow> (\<nexists>n. of_nat n = x \<and> n < 2^LENGTH('a) \<and> \<not> P n)"
  for x :: "'a::len word"
  by (auto simp add: unsigned_of_nat take_bit_nat_eq_self)

lemma un_ui_le:
  \<open>unat a \<le> unat b \<longleftrightarrow> uint a \<le> uint b\<close>
  by transfer (simp add: nat_le_iff) 

lemma unat_plus_if':
  \<open>unat (a + b) =
    (if unat a + unat b < 2 ^ LENGTH('a)
    then unat a + unat b
    else unat a + unat b - 2 ^ LENGTH('a))\<close> for a b :: \<open>'a::len word\<close>
  apply (auto simp add: not_less le_iff_add)
   apply (metis (mono_tags, lifting) of_nat_add of_nat_unat take_bit_nat_eq_self_iff unsigned_less unsigned_of_nat unsigned_word_eqI)
  apply (smt (verit, ccfv_SIG) dbl_simps(3) dbl_simps(5) numerals(1) of_nat_0_le_iff of_nat_add of_nat_eq_iff of_nat_numeral of_nat_power of_nat_unat uint_plus_if' unsigned_1)
  done

lemma unat_sub_if_size:
  "unat (x - y) =
    (if unat y \<le> unat x
     then unat x - unat y
     else unat x + 2 ^ size x - unat y)"
proof -
  { assume xy: "\<not> uint y \<le> uint x"
    have "nat (uint x - uint y + 2 ^ LENGTH('a)) = nat (uint x + 2 ^ LENGTH('a) - uint y)"
      by simp
    also have "... = nat (uint x + 2 ^ LENGTH('a)) - nat (uint y)"
      by (simp add: nat_diff_distrib')
    also have "... = nat (uint x) + 2 ^ LENGTH('a) - nat (uint y)"
      by (metis nat_add_distrib nat_eq_numeral_power_cancel_iff order_less_imp_le unsigned_0 unsigned_greater_eq unsigned_less)
    finally have "nat (uint x - uint y + 2 ^ LENGTH('a)) = nat (uint x) + 2 ^ LENGTH('a) - nat (uint y)" .
  }
  then show ?thesis
    by (simp add: word_size) (metis nat_diff_distrib' uint_sub_if' un_ui_le unat_eq_nat_uint unsigned_greater_eq)
qed

lemmas unat_sub_if' = unat_sub_if_size [unfolded word_size]

lemma uint_split:
  "P (uint x) = (\<forall>i. word_of_int i = x \<and> 0 \<le> i \<and> i < 2^LENGTH('a) \<longrightarrow> P i)"
  for x :: "'a::len word"
  by transfer (auto simp add: take_bit_eq_mod)

lemma uint_split_asm:
  "P (uint x) = (\<nexists>i. word_of_int i = x \<and> 0 \<le> i \<and> i < 2^LENGTH('a) \<and> \<not> P i)"
  for x :: "'a::len word"
  by (auto simp add: unsigned_of_int take_bit_int_eq_self)


subsection \<open>Some proof tool support\<close>

\<comment> \<open>use this to stop, eg. \<open>2 ^ LENGTH(32)\<close> being simplified\<close>
lemma power_False_cong: "False \<Longrightarrow> a ^ b = c ^ d"
  by auto

lemmas unat_splits = unat_split unat_split_asm

lemmas unat_arith_simps =
  word_le_nat_alt word_less_nat_alt
  word_unat_eq_iff
  unat_sub_if' unat_plus_if' unat_div unat_mod

lemmas uint_splits = uint_split uint_split_asm

lemmas uint_arith_simps =
  word_le_def word_less_alt
  word_uint_eq_iff
  uint_sub_if' uint_plus_if'

\<comment> \<open>\<open>unat_arith_tac\<close>: tactic to reduce word arithmetic to \<open>nat\<close>, try to solve via \<open>arith\<close>\<close>
ML \<open>
val unat_arith_simpset =
  @{context} (* TODO: completely explicitly determined simpset *)
  |> fold Simplifier.add_simp @{thms unat_arith_simps}
  |> fold Splitter.add_split @{thms if_split_asm}
  |> fold Simplifier.add_cong @{thms power_False_cong}
  |> simpset_of

fun unat_arith_tacs ctxt =
  let
    fun arith_tac' n t =
      Arith_Data.arith_tac ctxt n t
        handle Cooper.COOPER _ => Seq.empty;
  in
    [ clarify_tac ctxt 1,
      full_simp_tac (put_simpset unat_arith_simpset ctxt) 1,
      ALLGOALS (full_simp_tac
        (put_simpset HOL_ss ctxt
          |> fold Splitter.add_split @{thms unat_splits}
          |> fold Simplifier.add_cong @{thms power_False_cong})),
      rewrite_goals_tac ctxt @{thms word_size},
      ALLGOALS (fn n => REPEAT (resolve_tac ctxt [allI, impI] n) THEN
                         REPEAT (eresolve_tac ctxt [conjE] n) THEN
                         REPEAT (dresolve_tac ctxt @{thms of_nat_inverse} n THEN assume_tac ctxt n)),
      TRYALL arith_tac' ]
  end

fun unat_arith_tac ctxt = SELECT_GOAL (EVERY (unat_arith_tacs ctxt))
\<close>

method_setup unat_arith =
  \<open>Scan.succeed (SIMPLE_METHOD' o unat_arith_tac)\<close>
  "solving word arithmetic via natural numbers and arith"

\<comment> \<open>\<open>uint_arith_tac\<close>: reduce to arithmetic on int, try to solve by arith\<close>
ML \<open>
val uint_arith_simpset =
  @{context} (* TODO: completely explicitly determined simpset *)
  |> fold Simplifier.add_simp @{thms uint_arith_simps}
  |> fold Splitter.add_split @{thms if_split_asm}
  |> fold Simplifier.add_cong @{thms power_False_cong}
  |> simpset_of;
  
fun uint_arith_tacs ctxt =
  let
    fun arith_tac' n t =
      Arith_Data.arith_tac ctxt n t
        handle Cooper.COOPER _ => Seq.empty;
  in
    [ clarify_tac ctxt 1,
      full_simp_tac (put_simpset uint_arith_simpset ctxt) 1,
      ALLGOALS (full_simp_tac
        (put_simpset HOL_ss ctxt
          |> fold Splitter.add_split @{thms uint_splits}
          |> fold Simplifier.add_cong @{thms power_False_cong})),
      rewrite_goals_tac ctxt @{thms word_size},
      ALLGOALS  (fn n => REPEAT (resolve_tac ctxt [allI, impI] n) THEN
                         REPEAT (eresolve_tac ctxt [conjE] n) THEN
                         REPEAT (dresolve_tac ctxt @{thms word_of_int_inverse} n
                                 THEN assume_tac ctxt n
                                 THEN assume_tac ctxt n)),
      TRYALL arith_tac' ]
  end

fun uint_arith_tac ctxt = SELECT_GOAL (EVERY (uint_arith_tacs ctxt))
\<close>

method_setup uint_arith =
  \<open>Scan.succeed (SIMPLE_METHOD' o uint_arith_tac)\<close>
  "solving word arithmetic via integers and arith"


subsection \<open>More on overflows and monotonicity\<close>

lemma no_plus_overflow_uint_size: "x \<le> x + y \<longleftrightarrow> uint x + uint y < 2 ^ size x"
  for x y :: "'a::len word"
  by (auto simp add: word_size word_le_def uint_add_lem uint_sub_lem)

lemmas no_olen_add = no_plus_overflow_uint_size [unfolded word_size]

lemma no_ulen_sub: "x \<ge> x - y \<longleftrightarrow> uint y \<le> uint x"
  for x y :: "'a::len word"
  by (auto simp add: word_size word_le_def uint_add_lem uint_sub_lem)

lemma no_olen_add': "x \<le> y + x \<longleftrightarrow> uint y + uint x < 2 ^ LENGTH('a)"
  for x y :: "'a::len word"
  by (simp add: ac_simps no_olen_add)

lemmas olen_add_eqv = trans [OF no_olen_add no_olen_add' [symmetric]]

lemmas uint_plus_simple_iff = trans [OF no_olen_add uint_add_lem]
lemmas uint_plus_simple = uint_plus_simple_iff [THEN iffD1]
lemmas uint_minus_simple_iff = trans [OF no_ulen_sub uint_sub_lem]
lemmas uint_minus_simple_alt = uint_sub_lem [folded word_le_def]
lemmas word_sub_le_iff = no_ulen_sub [folded word_le_def]
lemmas word_sub_le = word_sub_le_iff [THEN iffD2]

lemma word_less_sub1: "x \<noteq> 0 \<Longrightarrow> 1 < x \<longleftrightarrow> 0 < x - 1"
  for x :: "'a::len word"
  by transfer (simp add: take_bit_decr_eq) 

lemma word_le_sub1: "x \<noteq> 0 \<Longrightarrow> 1 \<le> x \<longleftrightarrow> 0 \<le> x - 1"
  for x :: "'a::len word"
  by transfer (simp add: int_one_le_iff_zero_less less_le)

lemma sub_wrap_lt: "x < x - z \<longleftrightarrow> x < z"
  for x z :: "'a::len word"
  by (simp add: word_less_def uint_sub_lem)
   (meson linorder_not_le uint_minus_simple_iff uint_sub_lem word_less_iff_unsigned)
  
lemma sub_wrap: "x \<le> x - z \<longleftrightarrow> z = 0 \<or> x < z"
  for x z :: "'a::len word"
  by (simp add: le_less sub_wrap_lt ac_simps)

lemma plus_minus_not_NULL_ab: "x \<le> ab - c \<Longrightarrow> c \<le> ab \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> x + c \<noteq> 0"
  for x ab c :: "'a::len word"
  by uint_arith

lemma plus_minus_no_overflow_ab: "x \<le> ab - c \<Longrightarrow> c \<le> ab \<Longrightarrow> x \<le> x + c"
  for x ab c :: "'a::len word"
  by uint_arith

lemma le_minus': "a + c \<le> b \<Longrightarrow> a \<le> a + c \<Longrightarrow> c \<le> b - a"
  for a b c :: "'a::len word"
  by uint_arith

lemma le_plus': "a \<le> b \<Longrightarrow> c \<le> b - a \<Longrightarrow> a + c \<le> b"
  for a b c :: "'a::len word"
  by uint_arith

lemmas le_plus = le_plus' [rotated]

lemmas le_minus = leD [THEN thin_rl, THEN le_minus'] (* FIXME *)

lemma word_plus_mono_right: "y \<le> z \<Longrightarrow> x \<le> x + z \<Longrightarrow> x + y \<le> x + z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_minus_cancel: "y - x < z - x \<Longrightarrow> x \<le> z \<Longrightarrow> y < z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_minus_mono_left: "y < z \<Longrightarrow> x \<le> y \<Longrightarrow> y - x < z - x"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_minus_mono: "a < c \<Longrightarrow> d < b \<Longrightarrow> a - b < a \<Longrightarrow> c - d < c \<Longrightarrow> a - b < c - d"
  for a b c d :: "'a::len word"
  by uint_arith

lemma word_le_minus_cancel: "y - x \<le> z - x \<Longrightarrow> x \<le> z \<Longrightarrow> y \<le> z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_le_minus_mono_left: "y \<le> z \<Longrightarrow> x \<le> y \<Longrightarrow> y - x \<le> z - x"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_le_minus_mono:
  "a \<le> c \<Longrightarrow> d \<le> b \<Longrightarrow> a - b \<le> a \<Longrightarrow> c - d \<le> c \<Longrightarrow> a - b \<le> c - d"
  for a b c d :: "'a::len word"
  by uint_arith

lemma plus_le_left_cancel_wrap: "x + y' < x \<Longrightarrow> x + y < x \<Longrightarrow> x + y' < x + y \<longleftrightarrow> y' < y"
  for x y y' :: "'a::len word"
  by uint_arith

lemma plus_le_left_cancel_nowrap: "x \<le> x + y' \<Longrightarrow> x \<le> x + y \<Longrightarrow> x + y' < x + y \<longleftrightarrow> y' < y"
  for x y y' :: "'a::len word"
  by uint_arith

lemma word_plus_mono_right2: "a \<le> a + b \<Longrightarrow> c \<le> b \<Longrightarrow> a \<le> a + c"
  for a b c :: "'a::len word"
  by uint_arith

lemma word_less_add_right: "x < y - z \<Longrightarrow> z \<le> y \<Longrightarrow> x + z < y"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_sub_right: "x < y + z \<Longrightarrow> y \<le> x \<Longrightarrow> x - y < z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_le_plus_either: "x \<le> y \<or> x \<le> z \<Longrightarrow> y \<le> y + z \<Longrightarrow> x \<le> y + z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_nowrapI: "x < z - k \<Longrightarrow> k \<le> z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  for x z k :: "'a::len word"
  by uint_arith

lemma inc_le: "i < m \<Longrightarrow> i + 1 \<le> m"
  for i m :: "'a::len word"
  by uint_arith

lemma inc_i: "1 \<le> i \<Longrightarrow> i < m \<Longrightarrow> 1 \<le> i + 1 \<and> i + 1 \<le> m"
  for i m :: "'a::len word"
  by uint_arith

lemma udvd_incr_lem:
  "up < uq \<Longrightarrow> up = ua + n * uint K \<Longrightarrow>
    uq = ua + n' * uint K \<Longrightarrow> up + uint K \<le> uq"
  by auto (metis int_distrib(1) linorder_not_less mult.left_neutral mult_right_mono uint_nonnegative zless_imp_add1_zle)

lemma udvd_incr':
  "p < q \<Longrightarrow> uint p = ua + n * uint K \<Longrightarrow>
    uint q = ua + n' * uint K \<Longrightarrow> p + K \<le> q"
  unfolding word_less_alt word_le_def
  by (metis (full_types) order_trans udvd_incr_lem uint_add_le)

lemma udvd_decr':
  assumes "p < q" "uint p = ua + n * uint K" "uint q = ua + n' * uint K"
    shows "uint q = ua + n' * uint K \<Longrightarrow> p \<le> q - K"
proof -
  have "\<And>w wa. uint (w::'a word) \<le> uint wa + uint (w - wa)"
    by (metis (no_types) add_diff_cancel_left' diff_add_cancel uint_add_le)
  moreover have "uint K + uint p \<le> uint q"
    using assms by (metis (no_types) add_diff_cancel_left' diff_add_cancel udvd_incr_lem word_less_def)
  ultimately show ?thesis
    by (meson add_le_cancel_left order_trans word_less_eq_iff_unsigned)
qed

lemmas udvd_incr_lem0 = udvd_incr_lem [where ua=0, unfolded add_0_left]
lemmas udvd_incr0 = udvd_incr' [where ua=0, unfolded add_0_left]
lemmas udvd_decr0 = udvd_decr' [where ua=0, unfolded add_0_left]

lemma udvd_minus_le': "xy < k \<Longrightarrow> z udvd xy \<Longrightarrow> z udvd k \<Longrightarrow> xy \<le> k - z"
  unfolding udvd_unfold_int
  by (meson udvd_decr0)

lemma udvd_incr2_K:
  "p < a + s \<Longrightarrow> a \<le> a + s \<Longrightarrow> K udvd s \<Longrightarrow> K udvd p - a \<Longrightarrow> a \<le> p \<Longrightarrow>
    0 < K \<Longrightarrow> p \<le> p + K \<and> p + K \<le> a + s"
  unfolding udvd_unfold_int
  apply (simp add: uint_arith_simps split: if_split_asm)
  apply (metis (no_types, opaque_lifting) le_add_diff_inverse le_less_trans udvd_incr_lem)
  using uint_lt2p [of s] by simp


subsection \<open>Arithmetic type class instantiations\<close>

lemmas word_le_0_iff [simp] =
  word_zero_le [THEN leD, THEN antisym_conv1]

lemma word_of_int_nat: "0 \<le> x \<Longrightarrow> word_of_int x = of_nat (nat x)"
  by simp

text \<open>
  note that \<open>iszero_def\<close> is only for class \<open>comm_semiring_1_cancel\<close>,
  which requires word length \<open>\<ge> 1\<close>, ie \<open>'a::len word\<close>
\<close>
lemma iszero_word_no [simp]:
  "iszero (numeral bin :: 'a::len word) =
    iszero (take_bit LENGTH('a) (numeral bin :: int))"
  by (metis iszero_def uint_0_iff uint_bintrunc)

text \<open>Use \<open>iszero\<close> to simplify equalities between word numerals.\<close>

lemmas word_eq_numeral_iff_iszero [simp] =
  eq_numeral_iff_iszero [where 'a="'a::len word"]

lemma word_less_eq_imp_half_less_eq:
  \<open>v div 2 \<le> w div 2\<close> if \<open>v \<le> w\<close> for v w :: \<open>'a::len word\<close>
  using that by (simp add: word_le_nat_alt unat_div div_le_mono)

lemma word_half_less_imp_less_eq:
  \<open>v \<le> w\<close> if \<open>v div 2 < w div 2\<close> for v w :: \<open>'a::len word\<close>
  using that linorder_linear word_less_eq_imp_half_less_eq by fastforce


subsection \<open>Word and nat\<close>

lemma word_nchotomy: "\<forall>w :: 'a::len word. \<exists>n. w = of_nat n \<and> n < 2 ^ LENGTH('a)"
  by (metis of_nat_unat ucast_id unsigned_less)

lemma of_nat_eq: "of_nat n = w \<longleftrightarrow> (\<exists>q. n = unat w + q * 2 ^ LENGTH('a))"
  for w :: "'a::len word"
  using mod_div_mult_eq [of n "2 ^ LENGTH('a)", symmetric]
  by (auto simp flip: take_bit_eq_mod simp add: unsigned_of_nat)

lemma of_nat_eq_size: "of_nat n = w \<longleftrightarrow> (\<exists>q. n = unat w + q * 2 ^ size w)"
  unfolding word_size by (rule of_nat_eq)

lemma of_nat_0: "of_nat m = (0::'a::len word) \<longleftrightarrow> (\<exists>q. m = q * 2 ^ LENGTH('a))"
  by (simp add: of_nat_eq)

lemma of_nat_2p [simp]: "of_nat (2 ^ LENGTH('a)) = (0::'a::len word)"
  by (fact mult_1 [symmetric, THEN iffD2 [OF of_nat_0 exI]])

lemma of_nat_gt_0: "of_nat k \<noteq> 0 \<Longrightarrow> 0 < k"
  by (cases k) auto

lemma of_nat_neq_0: "0 < k \<Longrightarrow> k < 2 ^ LENGTH('a::len) \<Longrightarrow> of_nat k \<noteq> (0 :: 'a word)"
  by (auto simp add : of_nat_0)

lemma Abs_fnat_hom_add: "of_nat a + of_nat b = of_nat (a + b)"
  by simp

lemma Abs_fnat_hom_mult: "of_nat a * of_nat b = (of_nat (a * b) :: 'a::len word)"
  by (simp add: wi_hom_mult)

lemma Abs_fnat_hom_Suc: "word_succ (of_nat a) = of_nat (Suc a)"
  by transfer (simp add: ac_simps)

lemma Abs_fnat_hom_0: "(0::'a::len word) = of_nat 0"
  by simp

lemma Abs_fnat_hom_1: "(1::'a::len word) = of_nat (Suc 0)"
  by simp

lemmas Abs_fnat_homs =
  Abs_fnat_hom_add Abs_fnat_hom_mult Abs_fnat_hom_Suc
  Abs_fnat_hom_0 Abs_fnat_hom_1

lemma word_arith_nat_add: "a + b = of_nat (unat a + unat b)"
  by simp

lemma word_arith_nat_mult: "a * b = of_nat (unat a * unat b)"
  by simp

lemma word_arith_nat_Suc: "word_succ a = of_nat (Suc (unat a))"
  by (subst Abs_fnat_hom_Suc [symmetric]) simp

lemma word_arith_nat_div: "a div b = of_nat (unat a div unat b)"
  by (metis of_int_of_nat_eq of_nat_unat of_nat_div word_div_def)
  
lemma word_arith_nat_mod: "a mod b = of_nat (unat a mod unat b)"
  by (metis of_int_of_nat_eq of_nat_mod of_nat_unat word_mod_def)

lemmas word_arith_nat_defs =
  word_arith_nat_add word_arith_nat_mult
  word_arith_nat_Suc Abs_fnat_hom_0
  Abs_fnat_hom_1 word_arith_nat_div
  word_arith_nat_mod

lemma unat_cong: "x = y \<Longrightarrow> unat x = unat y"
  by (fact arg_cong)

lemma unat_of_nat:
  \<open>unat (word_of_nat x :: 'a::len word) = x mod 2 ^ LENGTH('a)\<close>
  by transfer (simp flip: take_bit_eq_mod add: nat_take_bit_eq)

lemmas unat_word_ariths = word_arith_nat_defs
  [THEN trans [OF unat_cong unat_of_nat]]

lemmas word_sub_less_iff = word_sub_le_iff
  [unfolded linorder_not_less [symmetric] Not_eq_iff]

lemma unat_add_lem:
  "unat x + unat y < 2 ^ LENGTH('a) \<longleftrightarrow> unat (x + y) = unat x + unat y"
  for x y :: "'a::len word"
  by (metis mod_less unat_word_ariths(1) unsigned_less)

lemma unat_mult_lem:
  "unat x * unat y < 2 ^ LENGTH('a) \<longleftrightarrow> unat (x * y) = unat x * unat y"
  for x y :: "'a::len word"
  by (metis mod_less unat_word_ariths(2) unsigned_less)

lemma le_no_overflow: "x \<le> b \<Longrightarrow> a \<le> a + b \<Longrightarrow> x \<le> a + b"
  for a b x :: "'a::len word"
  using word_le_plus_either by blast

lemma uint_div:
  \<open>uint (x div y) = uint x div uint y\<close>
  by (fact uint_div_distrib)

lemma uint_mod:
  \<open>uint (x mod y) = uint x mod uint y\<close>
  by (fact uint_mod_distrib)
  
lemma no_plus_overflow_unat_size: "x \<le> x + y \<longleftrightarrow> unat x + unat y < 2 ^ size x"
  for x y :: "'a::len word"
  unfolding word_size by unat_arith

lemmas no_olen_add_nat =
  no_plus_overflow_unat_size [unfolded word_size]

lemmas unat_plus_simple =
  trans [OF no_olen_add_nat unat_add_lem]

lemma word_div_mult: "\<lbrakk>0 < y; unat x * unat y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> x * y div y = x"
  for x y :: "'a::len word"
  by (simp add: unat_eq_zero unat_mult_lem word_arith_nat_div)

lemma div_lt': "i \<le> k div x \<Longrightarrow> unat i * unat x < 2 ^ LENGTH('a)"
  for i k x :: "'a::len word"
  by unat_arith (meson le_less_trans less_mult_imp_div_less not_le unsigned_less)

lemmas div_lt'' = order_less_imp_le [THEN div_lt']

lemma div_lt_mult: "\<lbrakk>i < k div x; 0 < x\<rbrakk> \<Longrightarrow> i * x < k"
  for i k x :: "'a::len word"
  by (metis div_le_mono div_lt'' not_le unat_div word_div_mult word_less_iff_unsigned)

lemma div_le_mult: "\<lbrakk>i \<le> k div x; 0 < x\<rbrakk> \<Longrightarrow> i * x \<le> k"
  for i k x :: "'a::len word"
  by (metis div_lt' less_mult_imp_div_less not_less unat_arith_simps(2) unat_div unat_mult_lem)

lemma div_lt_uint': "i \<le> k div x \<Longrightarrow> uint i * uint x < 2 ^ LENGTH('a)"
  for i k x :: "'a::len word"
  unfolding uint_nat
  by (metis div_lt' int_ops(7) of_nat_unat uint_mult_lem unat_mult_lem)

lemmas div_lt_uint'' = order_less_imp_le [THEN div_lt_uint']

lemma word_le_exists': "x \<le> y \<Longrightarrow> \<exists>z. y = x + z \<and> uint x + uint z < 2 ^ LENGTH('a)"
  for x y z :: "'a::len word"
  by (metis add.commute diff_add_cancel no_olen_add)
  
lemmas plus_minus_not_NULL = order_less_imp_le [THEN plus_minus_not_NULL_ab]

lemmas plus_minus_no_overflow =
  order_less_imp_le [THEN plus_minus_no_overflow_ab]

lemmas mcs = word_less_minus_cancel word_less_minus_mono_left
  word_le_minus_cancel word_le_minus_mono_left

lemmas word_l_diffs = mcs [where y = "w + x", unfolded add_diff_cancel] for w x
lemmas word_diff_ls = mcs [where z = "w + x", unfolded add_diff_cancel] for w x
lemmas word_plus_mcs = word_diff_ls [where y = "v + x", unfolded add_diff_cancel] for v x

lemma le_unat_uoi:
  \<open>y \<le> unat z \<Longrightarrow> unat (word_of_nat y :: 'a word) = y\<close>
  for z :: \<open>'a::len word\<close>
  by transfer (simp add: nat_take_bit_eq take_bit_nat_eq_self_iff le_less_trans)

lemmas thd = times_div_less_eq_dividend

lemmas uno_simps [THEN le_unat_uoi] = mod_le_divisor div_le_dividend

lemma word_mod_div_equality: "(n div b) * b + (n mod b) = n"
  for n b :: "'a::len word"
  by (fact div_mult_mod_eq)

lemma word_div_mult_le: "a div b * b \<le> a"
  for a b :: "'a::len word"
  by (metis div_le_mult mult_not_zero order.not_eq_order_implies_strict order_refl word_zero_le)

lemma word_mod_less_divisor: "0 < n \<Longrightarrow> m mod n < n"
  for m n :: "'a::len word"
  by (simp add: unat_arith_simps)
  
lemma word_of_int_power_hom: "word_of_int a ^ n = (word_of_int (a ^ n) :: 'a::len word)"
  by (induct n) (simp_all add: wi_hom_mult [symmetric])

lemma word_arith_power_alt: "a ^ n = (word_of_int (uint a ^ n) :: 'a::len word)"
  by (simp add : word_of_int_power_hom [symmetric])

lemma unatSuc: "1 + n \<noteq> 0 \<Longrightarrow> unat (1 + n) = Suc (unat n)"
  for n :: "'a::len word"
  by unat_arith


subsection \<open>Cardinality, finiteness of set of words\<close>

lemma inj_on_word_of_int: \<open>inj_on (word_of_int :: int \<Rightarrow> 'a word) {0..<2 ^ LENGTH('a::len)}\<close>
  unfolding inj_on_def
  by (metis atLeastLessThan_iff word_of_int_inverse)

lemma range_uint: \<open>range (uint :: 'a word \<Rightarrow> int) = {0..<2 ^ LENGTH('a::len)}\<close>
  apply transfer
  apply (auto simp add: image_iff)
  apply (metis take_bit_int_eq_self_iff)
  done

lemma UNIV_eq: \<open>(UNIV :: 'a word set) = word_of_int ` {0..<2 ^ LENGTH('a::len)}\<close>
  by (auto simp add: image_iff) (metis atLeastLessThan_iff linorder_not_le uint_split)

lemma card_word: "CARD('a word) = 2 ^ LENGTH('a::len)"
  by (simp add: UNIV_eq card_image inj_on_word_of_int)

lemma card_word_size: "CARD('a word) = 2 ^ size x"
  for x :: "'a::len word"
  unfolding word_size by (rule card_word)

end

instance word :: (len) finite
  by standard (simp add: UNIV_eq)


subsection \<open>Bitwise Operations on Words\<close>

context
  includes bit_operations_syntax
begin

lemma word_wi_log_defs:
  "NOT (word_of_int a) = word_of_int (NOT a)"
  "word_of_int a AND word_of_int b = word_of_int (a AND b)"
  "word_of_int a OR word_of_int b = word_of_int (a OR b)"
  "word_of_int a XOR word_of_int b = word_of_int (a XOR b)"
  by (transfer, rule refl)+

lemma word_no_log_defs [simp]:
  "NOT (numeral a) = word_of_int (NOT (numeral a))"
  "NOT (- numeral a) = word_of_int (NOT (- numeral a))"
  "numeral a AND numeral b = word_of_int (numeral a AND numeral b)"
  "numeral a AND - numeral b = word_of_int (numeral a AND - numeral b)"
  "- numeral a AND numeral b = word_of_int (- numeral a AND numeral b)"
  "- numeral a AND - numeral b = word_of_int (- numeral a AND - numeral b)"
  "numeral a OR numeral b = word_of_int (numeral a OR numeral b)"
  "numeral a OR - numeral b = word_of_int (numeral a OR - numeral b)"
  "- numeral a OR numeral b = word_of_int (- numeral a OR numeral b)"
  "- numeral a OR - numeral b = word_of_int (- numeral a OR - numeral b)"
  "numeral a XOR numeral b = word_of_int (numeral a XOR numeral b)"
  "numeral a XOR - numeral b = word_of_int (numeral a XOR - numeral b)"
  "- numeral a XOR numeral b = word_of_int (- numeral a XOR numeral b)"
  "- numeral a XOR - numeral b = word_of_int (- numeral a XOR - numeral b)"
  by (transfer, rule refl)+

text \<open>Special cases for when one of the arguments equals 1.\<close>

lemma word_bitwise_1_simps [simp]:
  "NOT (1::'a::len word) = -2"
  "1 AND numeral b = word_of_int (1 AND numeral b)"
  "1 AND - numeral b = word_of_int (1 AND - numeral b)"
  "numeral a AND 1 = word_of_int (numeral a AND 1)"
  "- numeral a AND 1 = word_of_int (- numeral a AND 1)"
  "1 OR numeral b = word_of_int (1 OR numeral b)"
  "1 OR - numeral b = word_of_int (1 OR - numeral b)"
  "numeral a OR 1 = word_of_int (numeral a OR 1)"
  "- numeral a OR 1 = word_of_int (- numeral a OR 1)"
  "1 XOR numeral b = word_of_int (1 XOR numeral b)"
  "1 XOR - numeral b = word_of_int (1 XOR - numeral b)"
  "numeral a XOR 1 = word_of_int (numeral a XOR 1)"
  "- numeral a XOR 1 = word_of_int (- numeral a XOR 1)"
              apply (simp_all add: word_uint_eq_iff unsigned_not_eq unsigned_and_eq unsigned_or_eq
         unsigned_xor_eq of_nat_take_bit ac_simps unsigned_of_int)
       apply (simp_all add: minus_numeral_eq_not_sub_one)
   apply (simp_all only: sub_one_eq_not_neg bit.xor_compl_right take_bit_xor bit.double_compl)
   apply simp_all
  done

text \<open>Special cases for when one of the arguments equals -1.\<close>

lemma word_bitwise_m1_simps [simp]:
  "NOT (-1::'a::len word) = 0"
  "(-1::'a::len word) AND x = x"
  "x AND (-1::'a::len word) = x"
  "(-1::'a::len word) OR x = -1"
  "x OR (-1::'a::len word) = -1"
  " (-1::'a::len word) XOR x = NOT x"
  "x XOR (-1::'a::len word) = NOT x"
  by (transfer, simp)+

lemma word_of_int_not_numeral_eq [simp]:
  \<open>(word_of_int (NOT (numeral bin)) :: 'a::len word) = - numeral bin - 1\<close>
  by transfer (simp add: not_eq_complement)

lemma uint_and:
  \<open>uint (x AND y) = uint x AND uint y\<close>
  by transfer simp

lemma uint_or:
  \<open>uint (x OR y) = uint x OR uint y\<close>
  by transfer simp

lemma uint_xor:
  \<open>uint (x XOR y) = uint x XOR uint y\<close>
  by transfer simp

\<comment> \<open>get from commutativity, associativity etc of \<open>int_and\<close> etc to same for \<open>word_and etc\<close>\<close>
lemmas bwsimps =
  wi_hom_add
  word_wi_log_defs

lemma word_bw_assocs:
  "(x AND y) AND z = x AND y AND z"
  "(x OR y) OR z = x OR y OR z"
  "(x XOR y) XOR z = x XOR y XOR z"
  for x :: "'a::len word"
  by (fact ac_simps)+

lemma word_bw_comms:
  "x AND y = y AND x"
  "x OR y = y OR x"
  "x XOR y = y XOR x"
  for x :: "'a::len word"
  by (fact ac_simps)+

lemma word_bw_lcs:
  "y AND x AND z = x AND y AND z"
  "y OR x OR z = x OR y OR z"
  "y XOR x XOR z = x XOR y XOR z"
  for x :: "'a::len word"
  by (fact ac_simps)+

lemma word_log_esimps:
  "x AND 0 = 0"
  "x AND -1 = x"
  "x OR 0 = x"
  "x OR -1 = -1"
  "x XOR 0 = x"
  "x XOR -1 = NOT x"
  "0 AND x = 0"
  "-1 AND x = x"
  "0 OR x = x"
  "-1 OR x = -1"
  "0 XOR x = x"
  "-1 XOR x = NOT x"
  for x :: "'a::len word"
  by simp_all

lemma word_not_dist:
  "NOT (x OR y) = NOT x AND NOT y"
  "NOT (x AND y) = NOT x OR NOT y"
  for x :: "'a::len word"
  by simp_all

lemma word_bw_same:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: "'a::len word"
  by simp_all

lemma word_ao_absorbs [simp]:
  "x AND (y OR x) = x"
  "x OR y AND x = x"
  "x AND (x OR y) = x"
  "y AND x OR x = x"
  "(y OR x) AND x = x"
  "x OR x AND y = x"
  "(x OR y) AND x = x"
  "x AND y OR x = x"
  for x :: "'a::len word"
  by (auto intro: bit_eqI simp add: bit_and_iff bit_or_iff)

lemma word_not_not [simp]: "NOT (NOT x) = x"
  for x :: "'a::len word"
  by (fact bit.double_compl)

lemma word_ao_dist: "(x OR y) AND z = x AND z OR y AND z"
  for x :: "'a::len word"
  by (fact bit.conj_disj_distrib2)

lemma word_oa_dist: "x AND y OR z = (x OR z) AND (y OR z)"
  for x :: "'a::len word"
  by (fact bit.disj_conj_distrib2)
  
lemma word_add_not [simp]: "x + NOT x = -1"
  for x :: "'a::len word"
  by (simp add: not_eq_complement)
  
lemma word_plus_and_or [simp]: "(x AND y) + (x OR y) = x + y"
  for x :: "'a::len word"
  by transfer (simp add: plus_and_or)

lemma leoa: "w = x OR y \<Longrightarrow> y = w AND y"
  for x :: "'a::len word"
  by auto

lemma leao: "w' = x' AND y' \<Longrightarrow> x' = x' OR w'"
  for x' :: "'a::len word"
  by auto

lemma word_ao_equiv: "w = w OR w' \<longleftrightarrow> w' = w AND w'"
  for w w' :: "'a::len word"
  by (auto intro: leoa leao)

lemma le_word_or2: "x \<le> x OR y"
  for x y :: "'a::len word"
  by (simp add: or_greater_eq uint_or word_le_def)

lemmas le_word_or1 = xtrans(3) [OF word_bw_comms (2) le_word_or2]
lemmas word_and_le1 = xtrans(3) [OF word_ao_absorbs (4) [symmetric] le_word_or2]
lemmas word_and_le2 = xtrans(3) [OF word_ao_absorbs (8) [symmetric] le_word_or2]

lemma bit_horner_sum_bit_word_iff [bit_simps]:
  \<open>bit (horner_sum of_bool (2 :: 'a::len word) bs) n
    \<longleftrightarrow> n < min LENGTH('a) (length bs) \<and> bs ! n\<close>
  by transfer (simp add: bit_horner_sum_bit_iff)

definition word_reverse :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>word_reverse w = horner_sum of_bool 2 (rev (map (bit w) [0..<LENGTH('a)]))\<close>

lemma bit_word_reverse_iff [bit_simps]:
  \<open>bit (word_reverse w) n \<longleftrightarrow> n < LENGTH('a) \<and> bit w (LENGTH('a) - Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (cases \<open>n < LENGTH('a)\<close>)
    (simp_all add: word_reverse_def bit_horner_sum_bit_word_iff rev_nth)

lemma word_rev_rev [simp] : "word_reverse (word_reverse w) = w"
  by (rule bit_word_eqI)
    (auto simp add: bit_word_reverse_iff bit_imp_le_length Suc_diff_Suc)

lemma word_rev_gal: "word_reverse w = u \<Longrightarrow> word_reverse u = w"
  by (metis word_rev_rev)

lemma word_rev_gal': "u = word_reverse w \<Longrightarrow> w = word_reverse u"
  by simp

lemma word_eq_reverseI:
  \<open>v = w\<close> if \<open>word_reverse v = word_reverse w\<close>
proof -
  from that have \<open>word_reverse (word_reverse v) = word_reverse (word_reverse w)\<close>
    by simp
  then show ?thesis
    by simp
qed

lemma uint_2p: "(0::'a::len word) < 2 ^ n \<Longrightarrow> uint (2 ^ n::'a::len word) = 2 ^ n"
  by (cases \<open>n < LENGTH('a)\<close>; transfer; force)

lemma word_of_int_2p: "(word_of_int (2 ^ n) :: 'a::len word) = 2 ^ n"
  by (induct n) (simp_all add: wi_hom_syms)


subsubsection \<open>shift functions in terms of lists of bools\<close>

lemma drop_bit_word_numeral [simp]:
  \<open>drop_bit (numeral n) (numeral k) =
    (word_of_int (drop_bit (numeral n) (take_bit LENGTH('a) (numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma drop_bit_word_Suc_numeral [simp]:
  \<open>drop_bit (Suc n) (numeral k) =
    (word_of_int (drop_bit (Suc n) (take_bit LENGTH('a) (numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma drop_bit_word_minus_numeral [simp]:
  \<open>drop_bit (numeral n) (- numeral k) =
    (word_of_int (drop_bit (numeral n) (take_bit LENGTH('a) (- numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma drop_bit_word_Suc_minus_numeral [simp]:
  \<open>drop_bit (Suc n) (- numeral k) =
    (word_of_int (drop_bit (Suc n) (take_bit LENGTH('a) (- numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma signed_drop_bit_word_numeral [simp]:
  \<open>signed_drop_bit (numeral n) (numeral k) =
    (word_of_int (drop_bit (numeral n) (signed_take_bit (LENGTH('a) - 1) (numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma signed_drop_bit_word_Suc_numeral [simp]:
  \<open>signed_drop_bit (Suc n) (numeral k) =
    (word_of_int (drop_bit (Suc n) (signed_take_bit (LENGTH('a) - 1) (numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma signed_drop_bit_word_minus_numeral [simp]:
  \<open>signed_drop_bit (numeral n) (- numeral k) =
    (word_of_int (drop_bit (numeral n) (signed_take_bit (LENGTH('a) - 1) (- numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma signed_drop_bit_word_Suc_minus_numeral [simp]:
  \<open>signed_drop_bit (Suc n) (- numeral k) =
    (word_of_int (drop_bit (Suc n) (signed_take_bit (LENGTH('a) - 1) (- numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma take_bit_word_numeral [simp]:
  \<open>take_bit (numeral n) (numeral k) =
    (word_of_int (take_bit (min LENGTH('a) (numeral n)) (numeral k)) :: 'a::len word)\<close>
  by transfer rule

lemma take_bit_word_Suc_numeral [simp]:
  \<open>take_bit (Suc n) (numeral k) =
    (word_of_int (take_bit (min LENGTH('a) (Suc n)) (numeral k)) :: 'a::len word)\<close>
  by transfer rule

lemma take_bit_word_minus_numeral [simp]:
  \<open>take_bit (numeral n) (- numeral k) =
    (word_of_int (take_bit (min LENGTH('a) (numeral n)) (- numeral k)) :: 'a::len word)\<close>
  by transfer rule

lemma take_bit_word_Suc_minus_numeral [simp]:
  \<open>take_bit (Suc n) (- numeral k) =
    (word_of_int (take_bit (min LENGTH('a) (Suc n)) (- numeral k)) :: 'a::len word)\<close>
  by transfer rule

lemma signed_take_bit_word_numeral [simp]:
  \<open>signed_take_bit (numeral n) (numeral k) =
    (word_of_int (signed_take_bit (numeral n) (take_bit LENGTH('a) (numeral k))) :: 'a::len word)\<close>
  by transfer rule

lemma signed_take_bit_word_Suc_numeral [simp]:
  \<open>signed_take_bit (Suc n) (numeral k) =
    (word_of_int (signed_take_bit (Suc n) (take_bit LENGTH('a) (numeral k))) :: 'a::len word)\<close>
  by transfer rule

lemma signed_take_bit_word_minus_numeral [simp]:
  \<open>signed_take_bit (numeral n) (- numeral k) =
    (word_of_int (signed_take_bit (numeral n) (take_bit LENGTH('a) (- numeral k))) :: 'a::len word)\<close>
  by transfer rule

lemma signed_take_bit_word_Suc_minus_numeral [simp]:
  \<open>signed_take_bit (Suc n) (- numeral k) =
    (word_of_int (signed_take_bit (Suc n) (take_bit LENGTH('a) (- numeral k))) :: 'a::len word)\<close>
  by transfer rule

lemma False_map2_or: "\<lbrakk>set xs \<subseteq> {False}; length ys = length xs\<rbrakk> \<Longrightarrow> map2 (\<or>) xs ys = ys"
  by (induction xs arbitrary: ys) (auto simp: length_Suc_conv)

lemma align_lem_or:
  assumes "length xs = n + m" "length ys = n + m" 
    and "drop m xs = replicate n False" "take m ys = replicate m False"
  shows "map2 (\<or>) xs ys = take m xs @ drop m ys"
  using assms
proof (induction xs arbitrary: ys m)
  case (Cons a xs)
  then show ?case
    by (cases m) (auto simp: length_Suc_conv False_map2_or)
qed auto

lemma False_map2_and: "\<lbrakk>set xs \<subseteq> {False}; length ys = length xs\<rbrakk> \<Longrightarrow> map2 (\<and>) xs ys = xs"
  by (induction xs arbitrary: ys) (auto simp: length_Suc_conv)

lemma align_lem_and:
  assumes "length xs = n + m" "length ys = n + m" 
    and "drop m xs = replicate n False" "take m ys = replicate m False"
  shows "map2 (\<and>) xs ys = replicate (n + m) False"
  using assms
proof (induction xs arbitrary: ys m)
  case (Cons a xs)
  then show ?case
    by (cases m) (auto simp: length_Suc_conv set_replicate_conv_if False_map2_and)
qed auto


subsubsection \<open>Mask\<close>

lemma minus_1_eq_mask:
  \<open>- 1 = (mask LENGTH('a) :: 'a::len word)\<close>
  by (rule bit_eqI) (simp add: bit_exp_iff bit_mask_iff)

lemma mask_eq_decr_exp:
  \<open>mask n = 2 ^ n - (1 :: 'a::len word)\<close>
  by (fact mask_eq_exp_minus_1)

lemma mask_Suc_rec:
  \<open>mask (Suc n) = 2 * mask n + (1 :: 'a::len word)\<close>
  by (simp add: mask_eq_exp_minus_1)

context
begin

qualified lemma bit_mask_iff [bit_simps]:
  \<open>bit (mask m :: 'a::len word) n \<longleftrightarrow> n < min LENGTH('a) m\<close>
  by (simp add: bit_mask_iff not_le)

end

lemma mask_bin: "mask n = word_of_int (take_bit n (- 1))"
  by transfer simp 

lemma and_mask_bintr: "w AND mask n = word_of_int (take_bit n (uint w))"
  by transfer (simp add: ac_simps take_bit_eq_mask)

lemma and_mask_wi: "word_of_int i AND mask n = word_of_int (take_bit n i)"
  by (simp add: take_bit_eq_mask of_int_and_eq of_int_mask_eq)

lemma and_mask_wi':
  "word_of_int i AND mask n = (word_of_int (take_bit (min LENGTH('a) n) i) :: 'a::len word)"
  by (auto simp add: and_mask_wi min_def wi_bintr)

lemma and_mask_no: "numeral i AND mask n = word_of_int (take_bit n (numeral i))"
  unfolding word_numeral_alt by (rule and_mask_wi)

lemma and_mask_mod_2p: "w AND mask n = word_of_int (uint w mod 2 ^ n)"
  by (simp only: and_mask_bintr take_bit_eq_mod)

lemma uint_mask_eq:
  \<open>uint (mask n :: 'a::len word) = mask (min LENGTH('a) n)\<close>
  by transfer simp

lemma and_mask_lt_2p: "uint (w AND mask n) < 2 ^ n"
  by (metis take_bit_eq_mask take_bit_int_less_exp unsigned_take_bit_eq)

lemma mask_eq_iff: "w AND mask n = w \<longleftrightarrow> uint w < 2 ^ n"
  apply (auto simp flip: take_bit_eq_mask)
   apply (metis take_bit_int_eq_self_iff uint_take_bit_eq)
  apply (simp add: take_bit_int_eq_self unsigned_take_bit_eq word_uint_eqI)
  done

lemma and_mask_dvd: "2 ^ n dvd uint w \<longleftrightarrow> w AND mask n = 0"
  by (simp flip: take_bit_eq_mask take_bit_eq_mod unsigned_take_bit_eq add: dvd_eq_mod_eq_0 uint_0_iff)

lemma and_mask_dvd_nat: "2 ^ n dvd unat w \<longleftrightarrow> w AND mask n = 0"
  by (simp flip: take_bit_eq_mask take_bit_eq_mod unsigned_take_bit_eq add: dvd_eq_mod_eq_0 unat_0_iff uint_0_iff)

lemma word_2p_lem: "n < size w \<Longrightarrow> w < 2 ^ n = (uint w < 2 ^ n)"
  for w :: "'a::len word"
  by transfer simp

lemma less_mask_eq:
  fixes x :: "'a::len word"
  assumes "x < 2 ^ n" shows "x AND mask n = x"
  by (metis (no_types) assms lt2p_lem mask_eq_iff not_less word_2p_lem word_size)

lemmas mask_eq_iff_w2p = trans [OF mask_eq_iff word_2p_lem [symmetric]]

lemmas and_mask_less' = iffD2 [OF word_2p_lem and_mask_lt_2p, simplified word_size]

lemma and_mask_less_size: "n < size x \<Longrightarrow> x AND mask n < 2 ^ n"
  for x :: \<open>'a::len word\<close>
  unfolding word_size by (erule and_mask_less')

lemma word_mod_2p_is_mask [OF refl]: "c = 2 ^ n \<Longrightarrow> c > 0 \<Longrightarrow> x mod c = x AND mask n"
  for c x :: "'a::len word"
  by (auto simp: word_mod_def uint_2p and_mask_mod_2p)

lemma mask_eqs:
  "(a AND mask n) + b AND mask n = a + b AND mask n"
  "a + (b AND mask n) AND mask n = a + b AND mask n"
  "(a AND mask n) - b AND mask n = a - b AND mask n"
  "a - (b AND mask n) AND mask n = a - b AND mask n"
  "a * (b AND mask n) AND mask n = a * b AND mask n"
  "(b AND mask n) * a AND mask n = b * a AND mask n"
  "(a AND mask n) + (b AND mask n) AND mask n = a + b AND mask n"
  "(a AND mask n) - (b AND mask n) AND mask n = a - b AND mask n"
  "(a AND mask n) * (b AND mask n) AND mask n = a * b AND mask n"
  "- (a AND mask n) AND mask n = - a AND mask n"
  "word_succ (a AND mask n) AND mask n = word_succ a AND mask n"
  "word_pred (a AND mask n) AND mask n = word_pred a AND mask n"
  using word_of_int_Ex [where x=a] word_of_int_Ex [where x=b]
  unfolding take_bit_eq_mask [symmetric]
  by (transfer; simp add: take_bit_eq_mod mod_simps)+

lemma mask_power_eq: "(x AND mask n) ^ k AND mask n = x ^ k AND mask n"
  for x :: \<open>'a::len word\<close>
  using word_of_int_Ex [where x=x]
  unfolding take_bit_eq_mask [symmetric]
  by (transfer; simp add: take_bit_eq_mod mod_simps)+

lemma mask_full [simp]: "mask LENGTH('a) = (- 1 :: 'a::len word)"
  by transfer simp


subsubsection \<open>Slices\<close>

definition slice1 :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>slice1 n w = (if n < LENGTH('a)
    then ucast (drop_bit (LENGTH('a) - n) w)
    else push_bit (n - LENGTH('a)) (ucast w))\<close>

lemma bit_slice1_iff [bit_simps]:
  \<open>bit (slice1 m w :: 'b::len word) n \<longleftrightarrow> m - LENGTH('a) \<le> n \<and> n < min LENGTH('b) m
    \<and> bit w (n + (LENGTH('a) - m) - (m - LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: slice1_def bit_ucast_iff bit_drop_bit_eq bit_push_bit_iff not_less not_le ac_simps
    dest: bit_imp_le_length)

definition slice :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>slice n = slice1 (LENGTH('a) - n)\<close>

lemma bit_slice_iff [bit_simps]:
  \<open>bit (slice m w :: 'b::len word) n \<longleftrightarrow> n < min LENGTH('b) (LENGTH('a) - m) \<and> bit w (n + LENGTH('a) - (LENGTH('a) - m))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: slice_def word_size bit_slice1_iff)

lemma slice1_0 [simp] : "slice1 n 0 = 0"
  unfolding slice1_def by simp

lemma slice_0 [simp] : "slice n 0 = 0"
  unfolding slice_def by auto

lemma ucast_slice1: "ucast w = slice1 (size w) w"
  unfolding slice1_def by (simp add: size_word.rep_eq)

lemma ucast_slice: "ucast w = slice 0 w"
  by (simp add: slice_def slice1_def)

lemma slice_id: "slice 0 t = t"
  by (simp only: ucast_slice [symmetric] ucast_id)

lemma rev_slice1:
  \<open>slice1 n (word_reverse w :: 'b::len word) = word_reverse (slice1 k w :: 'a::len word)\<close>
  if \<open>n + k = LENGTH('a) + LENGTH('b)\<close>
proof (rule bit_word_eqI)
  fix m
  assume *: \<open>m < LENGTH('a)\<close>
  from that have **: \<open>LENGTH('b) = n + k - LENGTH('a)\<close>
    by simp
  show \<open>bit (slice1 n (word_reverse w :: 'b word) :: 'a word) m \<longleftrightarrow> bit (word_reverse (slice1 k w :: 'a word)) m\<close>
    unfolding bit_slice1_iff bit_word_reverse_iff
    using * **
    by (cases \<open>n \<le> LENGTH('a)\<close>; cases \<open>k \<le> LENGTH('a)\<close>) auto
qed

lemma rev_slice:
  "n + k + LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow>
    slice n (word_reverse (w::'b word)) = word_reverse (slice k w :: 'a word)"
  unfolding slice_def word_size
  by (simp add: rev_slice1)


subsubsection \<open>Revcast\<close>

definition revcast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>revcast = slice1 LENGTH('b)\<close>

lemma bit_revcast_iff [bit_simps]:
  \<open>bit (revcast w :: 'b::len word) n \<longleftrightarrow> LENGTH('b) - LENGTH('a) \<le> n \<and> n < LENGTH('b)
    \<and> bit w (n + (LENGTH('a) - LENGTH('b)) - (LENGTH('b) - LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: revcast_def bit_slice1_iff)

lemma revcast_slice1 [OF refl]: "rc = revcast w \<Longrightarrow> slice1 (size rc) w = rc"
  by (simp add: revcast_def word_size)

lemma revcast_rev_ucast [OF refl refl refl]:
  "cs = [rc, uc] \<Longrightarrow> rc = revcast (word_reverse w) \<Longrightarrow> uc = ucast w \<Longrightarrow>
    rc = word_reverse uc"
  by (metis rev_slice1 revcast_slice1 ucast_slice1 word_size)

lemma revcast_ucast: "revcast w = word_reverse (ucast (word_reverse w))"
  using revcast_rev_ucast [of "word_reverse w"] by simp

lemma ucast_revcast: "ucast w = word_reverse (revcast (word_reverse w))"
  by (fact revcast_rev_ucast [THEN word_rev_gal'])

lemma ucast_rev_revcast: "ucast (word_reverse w) = word_reverse (revcast w)"
  by (fact revcast_ucast [THEN word_rev_gal'])


text "linking revcast and cast via shift"

lemmas wsst_TYs = source_size target_size word_size

lemmas sym_notr =
  not_iff [THEN iffD2, THEN not_sym, THEN not_iff [THEN iffD1]]


subsection \<open>Split and cat\<close>

lemmas word_split_bin' = word_split_def
lemmas word_cat_bin' = word_cat_eq

\<comment> \<open>this odd result is analogous to \<open>ucast_id\<close>,
      result to the length given by the result type\<close>

lemma word_cat_id: "word_cat a b = b"
  by transfer (simp add: take_bit_concat_bit_eq)

lemma word_cat_split_alt: "\<lbrakk>size w \<le> size u + size v; word_split w = (u,v)\<rbrakk> \<Longrightarrow> word_cat u v = w"
  unfolding word_split_def
  by (rule bit_word_eqI) (auto simp add: bit_word_cat_iff not_less word_size bit_ucast_iff bit_drop_bit_eq)

lemmas word_cat_split_size = sym [THEN [2] word_cat_split_alt [symmetric]]


subsubsection \<open>Split and slice\<close>

lemma split_slices:
  assumes "word_split w = (u, v)"
  shows "u = slice (size v) w \<and> v = slice 0 w"
  unfolding word_size
proof (intro conjI)
  have \<section>: "\<And>n. \<lbrakk>ucast (drop_bit LENGTH('b) w) = u; LENGTH('c) < LENGTH('b)\<rbrakk> \<Longrightarrow> \<not> bit u n"
    by (metis bit_take_bit_iff bit_word_of_int_iff diff_is_0_eq' drop_bit_take_bit less_imp_le less_nat_zero_code of_int_uint unsigned_drop_bit_eq)
  show "u = slice LENGTH('b) w"
  proof (rule bit_word_eqI)
    show "bit u n = bit ((slice LENGTH('b) w)::'a word) n" if "n < LENGTH('a)" for n
      using assms bit_imp_le_length
      unfolding word_split_def bit_slice_iff
      by (fastforce simp add: \<section> ac_simps word_size bit_ucast_iff bit_drop_bit_eq)
  qed
  show "v = slice 0 w"
    by (metis Pair_inject assms ucast_slice word_split_bin')
qed


lemma slice_cat1 [OF refl]:
  "\<lbrakk>wc = word_cat a b; size a + size b \<le> size wc\<rbrakk> \<Longrightarrow> slice (size b) wc = a"
  by (rule bit_word_eqI) (auto simp add: bit_slice_iff bit_word_cat_iff word_size)

lemmas slice_cat2 = trans [OF slice_id word_cat_id]

lemma cat_slices:
  "\<lbrakk>a = slice n c; b = slice 0 c; n = size b; size c \<le> size a + size b\<rbrakk> \<Longrightarrow> word_cat a b = c"
  by (rule bit_word_eqI) (auto simp add: bit_slice_iff bit_word_cat_iff word_size)

lemma word_split_cat_alt:
  assumes "w = word_cat u v" and size: "size u + size v \<le> size w"
  shows "word_split w = (u,v)"
proof -
  have "ucast ((drop_bit LENGTH('c) (word_cat u v))::'a word) = u" "ucast ((word_cat u v)::'a word) = v"
    using assms
    by (auto simp add: word_size bit_ucast_iff bit_drop_bit_eq bit_word_cat_iff intro: bit_eqI)
  then show ?thesis
    by (simp add: assms(1) word_split_bin')
qed

lemma horner_sum_uint_exp_Cons_eq:
  \<open>horner_sum uint (2 ^ LENGTH('a)) (w # ws) =
    concat_bit LENGTH('a) (uint w) (horner_sum uint (2 ^ LENGTH('a)) ws)\<close>
  for ws :: \<open>'a::len word list\<close>
  by (simp add: bintr_uint concat_bit_eq push_bit_eq_mult)

lemma bit_horner_sum_uint_exp_iff:
  \<open>bit (horner_sum uint (2 ^ LENGTH('a)) ws) n \<longleftrightarrow>
    n div LENGTH('a) < length ws \<and> bit (ws ! (n div LENGTH('a))) (n mod LENGTH('a))\<close>
  for ws :: \<open>'a::len word list\<close>
proof (induction ws arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons w ws)
  then show ?case
    by (cases \<open>n \<ge> LENGTH('a)\<close>)
      (simp_all only: horner_sum_uint_exp_Cons_eq, simp_all add: bit_concat_bit_iff le_div_geq le_mod_geq bit_uint_iff Cons)
qed


subsection \<open>Rotation\<close>

lemma word_rotr_word_rotr_eq: \<open>word_rotr m (word_rotr n w) = word_rotr (m + n) w\<close>
  by (rule bit_word_eqI) (simp add: bit_word_rotr_iff ac_simps mod_add_right_eq)

lemma word_rot_lem: "\<lbrakk>l + k = d + k mod l; n < l\<rbrakk> \<Longrightarrow> ((d + n) mod l) = n" for l::nat
  by (metis (no_types, lifting) add.commute add.right_neutral add_diff_cancel_left' mod_if mod_mult_div_eq mod_mult_self2 mod_self)
 
lemma word_rot_rl [simp]: \<open>word_rotl k (word_rotr k v) = v\<close>
proof (rule bit_word_eqI)
  show "bit (word_rotl k (word_rotr k v)) n = bit v n" if "n < LENGTH('a)" for n
    using that
    by (auto simp: word_rot_lem word_rotl_eq_word_rotr word_rotr_word_rotr_eq bit_word_rotr_iff algebra_simps split: nat_diff_split)
qed

lemma word_rot_lr [simp]: \<open>word_rotr k (word_rotl k v) = v\<close>
proof (rule bit_word_eqI)
  show "bit (word_rotr k (word_rotl k v)) n = bit v n" if "n < LENGTH('a)" for n
    using that
    by (auto simp add: word_rot_lem word_rotl_eq_word_rotr word_rotr_word_rotr_eq bit_word_rotr_iff algebra_simps split: nat_diff_split)
qed

lemma word_rot_gal:
  \<open>word_rotr n v = w \<longleftrightarrow> word_rotl n w = v\<close>
  by auto

lemma word_rot_gal':
  \<open>w = word_rotr n v \<longleftrightarrow> v = word_rotl n w\<close>
  by auto

lemma word_reverse_word_rotl:
  \<open>word_reverse (word_rotl n w) = word_rotr n (word_reverse w)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule bit_word_eqI)
  fix m
  assume \<open>m < LENGTH('a)\<close>
  then have \<open>int (LENGTH('a) - Suc ((m + n) mod LENGTH('a))) =
    int ((LENGTH('a) + LENGTH('a) - Suc (m + n mod LENGTH('a))) mod LENGTH('a))\<close>
    apply (simp only: of_nat_diff of_nat_mod)
    apply (simp add: Suc_le_eq add_less_le_mono of_nat_mod algebra_simps)
    apply (simp only: mod_diff_left_eq [symmetric, of \<open>int LENGTH('a) * 2\<close>] mod_mult_self1_is_0 diff_0 minus_mod_int_eq)
    apply (simp add: mod_simps)
    done
  then have \<open>LENGTH('a) - Suc ((m + n) mod LENGTH('a)) =
    (LENGTH('a) + LENGTH('a) - Suc (m + n mod LENGTH('a))) mod
    LENGTH('a)\<close>
    by simp
  with \<open>m < LENGTH('a)\<close> show \<open>bit ?lhs m \<longleftrightarrow> bit ?rhs m\<close>
    by (simp add: bit_simps)
qed

lemma word_reverse_word_rotr:
  \<open>word_reverse (word_rotr n w) = word_rotl n (word_reverse w)\<close>
  by (rule word_eq_reverseI) (simp add: word_reverse_word_rotl)

lemma word_rotl_rev:
  \<open>word_rotl n w = word_reverse (word_rotr n (word_reverse w))\<close>
  by (simp add: word_reverse_word_rotr)

lemma word_rotr_rev:
  \<open>word_rotr n w = word_reverse (word_rotl n (word_reverse w))\<close>
  by (simp add: word_reverse_word_rotl)

lemma word_roti_0 [simp]: "word_roti 0 w = w"
  by transfer simp

lemma word_roti_add: "word_roti (m + n) w = word_roti m (word_roti n w)"
  by (rule bit_word_eqI)
    (simp add: bit_word_roti_iff nat_less_iff mod_simps ac_simps)

lemma word_roti_conv_mod':
  "word_roti n w = word_roti (n mod int (size w)) w"
  by transfer simp

lemmas word_roti_conv_mod = word_roti_conv_mod' [unfolded word_size]

end


subsubsection \<open>"Word rotation commutes with bit-wise operations\<close>

\<comment> \<open>using locale to not pollute lemma namespace\<close>
locale word_rotate
begin

context
  includes bit_operations_syntax
begin

lemma word_rot_logs:
  "word_rotl n (NOT v) = NOT (word_rotl n v)"
  "word_rotr n (NOT v) = NOT (word_rotr n v)"
  "word_rotl n (x AND y) = word_rotl n x AND word_rotl n y"
  "word_rotr n (x AND y) = word_rotr n x AND word_rotr n y"
  "word_rotl n (x OR y) = word_rotl n x OR word_rotl n y"
  "word_rotr n (x OR y) = word_rotr n x OR word_rotr n y"
  "word_rotl n (x XOR y) = word_rotl n x XOR word_rotl n y"
  "word_rotr n (x XOR y) = word_rotr n x XOR word_rotr n y"
  by (rule bit_word_eqI, auto simp add: bit_word_rotl_iff bit_word_rotr_iff bit_and_iff bit_or_iff bit_xor_iff bit_not_iff algebra_simps not_le)+

end

end

lemmas word_rot_logs = word_rotate.word_rot_logs

lemma word_rotx_0 [simp] : "word_rotr i 0 = 0 \<and> word_rotl i 0 = 0"
  by transfer simp_all

lemma word_roti_0' [simp] : "word_roti n 0 = 0"
  by transfer simp

declare word_roti_eq_word_rotr_word_rotl [simp]


subsection \<open>Maximum machine word\<close>

context
  includes bit_operations_syntax
begin

lemma word_int_cases:
  fixes x :: "'a::len word"
  obtains n where "x = word_of_int n" and "0 \<le> n" and "n < 2^LENGTH('a)"
  by (rule that [of \<open>uint x\<close>]) simp_all

lemma word_nat_cases [cases type: word]:
  fixes x :: "'a::len word"
  obtains n where "x = of_nat n" and "n < 2^LENGTH('a)"
  by (rule that [of \<open>unat x\<close>]) simp_all

lemma max_word_max [intro!]:
  \<open>n \<le> - 1\<close> for n :: \<open>'a::len word\<close>
  by (fact word_order.extremum)

lemma word_of_int_2p_len: "word_of_int (2 ^ LENGTH('a)) = (0::'a::len word)"
  by simp

lemma word_pow_0: "(2::'a::len word) ^ LENGTH('a) = 0"
  by (fact word_exp_length_eq_0)

lemma max_word_wrap: 
  \<open>x + 1 = 0 \<Longrightarrow> x = - 1\<close> for x :: \<open>'a::len word\<close>
  by (simp add: eq_neg_iff_add_eq_0)

lemma word_and_max:
  \<open>x AND - 1 = x\<close> for x :: \<open>'a::len word\<close>
  by (fact word_log_esimps)

lemma word_or_max:
  \<open>x OR - 1 = - 1\<close> for x :: \<open>'a::len word\<close>
  by (fact word_log_esimps)

lemma word_ao_dist2: "x AND (y OR z) = x AND y OR x AND z"
  for x y z :: "'a::len word"
  by (fact bit.conj_disj_distrib)

lemma word_oa_dist2: "x OR y AND z = (x OR y) AND (x OR z)"
  for x y z :: "'a::len word"
  by (fact bit.disj_conj_distrib)

lemma word_and_not [simp]: "x AND NOT x = 0"
  for x :: "'a::len word"
  by (fact bit.conj_cancel_right)

lemma word_or_not [simp]:
  \<open>x OR NOT x = - 1\<close> for x :: \<open>'a::len word\<close>
  by (fact bit.disj_cancel_right)

lemma word_xor_and_or: "x XOR y = x AND NOT y OR NOT x AND y"
  for x y :: "'a::len word"
  by (fact bit.xor_def)

lemma uint_lt_0 [simp]: "uint x < 0 = False"
  by (simp add: linorder_not_less)

lemma word_less_1 [simp]: "x < 1 \<longleftrightarrow> x = 0"
  for x :: "'a::len word"
  by (simp add: word_less_nat_alt unat_0_iff)

lemma uint_plus_if_size:
  "uint (x + y) =
    (if uint x + uint y < 2^size x
     then uint x + uint y
     else uint x + uint y - 2^size x)"
  by (simp add: take_bit_eq_mod word_size uint_word_of_int_eq uint_plus_if')

lemma unat_plus_if_size:
  "unat (x + y) =
    (if unat x + unat y < 2^size x
     then unat x + unat y
     else unat x + unat y - 2^size x)"
  for x y :: "'a::len word"
  by (simp add: size_word.rep_eq unat_arith_simps)

lemma word_neq_0_conv: "w \<noteq> 0 \<longleftrightarrow> 0 < w"
  for w :: "'a::len word"
  by (fact word_coorder.not_eq_extremum)

lemma max_lt: "unat (max a b div c) = unat (max a b) div unat c"
  for c :: "'a::len word"
  by (fact unat_div)

lemma uint_sub_if_size:
  "uint (x - y) =
    (if uint y \<le> uint x
     then uint x - uint y
     else uint x - uint y + 2^size x)"
  by (simp add: size_word.rep_eq uint_sub_if')

lemma unat_sub:
  \<open>unat (a - b) = unat a - unat b\<close>
  if \<open>b \<le> a\<close>
  by (meson that unat_sub_if_size word_le_nat_alt)

lemmas word_less_sub1_numberof [simp] = word_less_sub1 [of "numeral w"] for w
lemmas word_le_sub1_numberof [simp] = word_le_sub1 [of "numeral w"] for w

lemma word_of_int_minus: "word_of_int (2^LENGTH('a) - i) = (word_of_int (-i)::'a::len word)"
  by simp

lemma word_of_int_inj:
  \<open>(word_of_int x :: 'a::len word) = word_of_int y \<longleftrightarrow> x = y\<close>
  if \<open>0 \<le> x \<and> x < 2 ^ LENGTH('a)\<close> \<open>0 \<le> y \<and> y < 2 ^ LENGTH('a)\<close>
  using that by (transfer fixing: x y) (simp add: take_bit_int_eq_self) 

lemma word_le_less_eq: "x \<le> y \<longleftrightarrow> x = y \<or> x < y"
  for x y :: "'z::len word"
  by (auto simp add: order_class.le_less)

lemma mod_plus_cong:
  fixes b b' :: int
  assumes 1: "b = b'"
    and 2: "x mod b' = x' mod b'"
    and 3: "y mod b' = y' mod b'"
    and 4: "x' + y' = z'"
  shows "(x + y) mod b = z' mod b'"
proof -
  from 1 2[symmetric] 3[symmetric] have "(x + y) mod b = (x' mod b' + y' mod b') mod b'"
    by (simp add: mod_add_eq)
  also have "\<dots> = (x' + y') mod b'"
    by (simp add: mod_add_eq)
  finally show ?thesis
    by (simp add: 4)
qed

lemma mod_minus_cong:
  fixes b b' :: int
  assumes "b = b'"
    and "x mod b' = x' mod b'"
    and "y mod b' = y' mod b'"
    and "x' - y' = z'"
  shows "(x - y) mod b = z' mod b'"
  using assms [symmetric] by (auto intro: mod_diff_cong)

lemma word_induct_less [case_names zero less]:
  \<open>P m\<close> if zero: \<open>P 0\<close> and less: \<open>\<And>n. n < m \<Longrightarrow> P n \<Longrightarrow> P (1 + n)\<close>
  for m :: \<open>'a::len word\<close>
proof -
  define q where \<open>q = unat m\<close>
  with less have \<open>\<And>n. n < word_of_nat q \<Longrightarrow> P n \<Longrightarrow> P (1 + n)\<close>
    by simp
  then have \<open>P (word_of_nat q :: 'a word)\<close>
  proof (induction q)
    case 0
    show ?case
      by (simp add: zero)
  next
    case (Suc q)
    show ?case
    proof (cases \<open>1 + word_of_nat q = (0 :: 'a word)\<close>)
      case True
      then show ?thesis
        by (simp add: zero)
    next
      case False
      then have *: \<open>word_of_nat q < (word_of_nat (Suc q) :: 'a word)\<close>
        by (simp add: unatSuc word_less_nat_alt)
      then have **: \<open>n < (1 + word_of_nat q :: 'a word) \<longleftrightarrow> n \<le> (word_of_nat q :: 'a word)\<close> for n
        by (metis (no_types, lifting) add.commute inc_le le_less_trans not_less of_nat_Suc)
      have \<open>P (word_of_nat q)\<close>
        by (simp add: "**" Suc.IH Suc.prems)
      with * have \<open>P (1 + word_of_nat q)\<close>
        by (rule Suc.prems)
      then show ?thesis
        by simp
    qed
  qed
  with \<open>q = unat m\<close> show ?thesis
    by simp
qed

lemma word_induct: "P 0 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (1 + n)) \<Longrightarrow> P m"
  for P :: "'a::len word \<Rightarrow> bool"
  by (rule word_induct_less)

lemma word_induct2 [case_names zero suc, induct type]: "P 0 \<Longrightarrow> (\<And>n. 1 + n \<noteq> 0 \<Longrightarrow> P n \<Longrightarrow> P (1 + n)) \<Longrightarrow> P n"
  for P :: "'b::len word \<Rightarrow> bool"
by (induction rule: word_induct_less; force)


subsection \<open>Recursion combinator for words\<close>

definition word_rec :: "'a \<Rightarrow> ('b::len word \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b word \<Rightarrow> 'a"
  where "word_rec forZero forSuc n = rec_nat forZero (forSuc \<circ> of_nat) (unat n)"

lemma word_rec_0 [simp]: "word_rec z s 0 = z"
  by (simp add: word_rec_def)

lemma word_rec_Suc [simp]: "1 + n \<noteq> 0 \<Longrightarrow> word_rec z s (1 + n) = s n (word_rec z s n)"
  for n :: "'a::len word"
  by (simp add: unatSuc word_rec_def)

lemma word_rec_Pred: "n \<noteq> 0 \<Longrightarrow> word_rec z s n = s (n - 1) (word_rec z s (n - 1))"
  by (metis add.commute diff_add_cancel word_rec_Suc)

lemma word_rec_in: "f (word_rec z (\<lambda>_. f) n) = word_rec (f z) (\<lambda>_. f) n"
  by (induct n) simp_all

lemma word_rec_in2: "f n (word_rec z f n) = word_rec (f 0 z) (f \<circ> (+) 1) n"
  by (induct n) simp_all

lemma word_rec_twice:
  "m \<le> n \<Longrightarrow> word_rec z f n = word_rec (word_rec z f (n - m)) (f \<circ> (+) (n - m)) m"
proof (induction n arbitrary: z f)
  case zero
  then show ?case
    by (metis diff_0_right word_le_0_iff word_rec_0)
next
  case (suc n z f)
  show ?case
  proof (cases "1 + (n - m) = 0")
    case True
    then show ?thesis
      by (simp add: add_diff_eq)
  next
    case False
    then have eq: "1 + n - m = 1 + (n - m)"
      by simp
    with False have "m \<le> n"
      by (metis "suc.prems" add.commute dual_order.antisym eq_iff_diff_eq_0 inc_le leI)
    with False "suc.hyps" show ?thesis
      using suc.IH [of "f 0 z" "f \<circ> (+) 1"] 
      by (simp add: word_rec_in2 eq add.assoc o_def)
  qed
qed

lemma word_rec_id: "word_rec z (\<lambda>_. id) n = z"
  by (induct n) auto

lemma word_rec_id_eq: "(\<And>m. m < n \<Longrightarrow> f m = id) \<Longrightarrow> word_rec z f n = z"
  by (induction n) (auto simp add: unatSuc unat_arith_simps(2))

lemma word_rec_max:
  assumes "\<forall>m\<ge>n. m \<noteq> - 1 \<longrightarrow> f m = id"
  shows "word_rec z f (- 1) = word_rec z f n"
proof -
  have \<section>: "\<And>m. \<lbrakk>m < - 1 - n\<rbrakk> \<Longrightarrow> (f \<circ> (+) n) m = id"
    using assms
    by (metis (mono_tags, lifting) add.commute add_diff_cancel_left' comp_apply less_le olen_add_eqv plus_minus_no_overflow word_n1_ge)
  have "word_rec z f (- 1) = word_rec (word_rec z f (- 1 - (- 1 - n))) (f \<circ> (+) (- 1 - (- 1 - n))) (- 1 - n)"
    by (meson word_n1_ge word_rec_twice)
  also have "... = word_rec z f n"
    by (metis (no_types, lifting) \<section> diff_add_cancel minus_diff_eq uminus_add_conv_diff word_rec_id_eq)
  finally show ?thesis .
qed

end


subsection \<open>Tool support\<close>

ML_file \<open>Tools/smt_word.ML\<close>

end
