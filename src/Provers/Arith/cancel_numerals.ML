(*  Title:      Provers/Arith/cancel_numerals.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Cancel common coefficients in balanced expressions:

     i + #m*u + j ~~ i' + #m'*u + j'  ==  #(m-m')*u + i + j ~~ i' + j'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, -).

It works by (a) massaging both sides to bring the selected term to the front:

     #m*u + (i + j) ~~ #m'*u + (i' + j')

(b) then using bal_add1 or bal_add2 to reach

     #(m-m')*u + i + j ~~ i' + j'       (if m'<=m)

or

     i + j ~~ #(m'-m)*u + i' + j'       (otherwise)
*)

signature CANCEL_NUMERALS_DATA =
sig
  (*abstract syntax*)
  val mk_sum: typ -> term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  val mk_coeff: int * term -> term
  val dest_coeff: term -> int * term
  val find_first_coeff: term -> term list -> int * term list
  (*rules*)
  val bal_add1: thm
  val bal_add2: thm
  (*proof tools*)
  val prove_conv: tactic list -> Proof.context -> thm list -> term * term -> thm option
  val trans_tac: Proof.context -> thm option -> tactic            (*applies the initial lemma*)
  val norm_tac: Proof.context -> tactic          (*proves the initial lemma*)
  val numeral_simp_tac: Proof.context -> tactic  (*proves the final theorem*)
  val simplify_meta_eq: Proof.context -> thm -> thm (*simplifies the final theorem*)
end;

signature CANCEL_NUMERALS =
sig
  val proc: Simplifier.proc
end;

functor CancelNumeralsFun(Data: CANCEL_NUMERALS_DATA): CANCEL_NUMERALS =
struct

(*For t = #n*u then put u in the table*)
fun update_by_coeff t =
  Termtab.update (#2 (Data.dest_coeff t), ());

(*a left-to-right scan of terms1, seeking a term of the form #n*u, where
  #m*u is in terms2 for some m*)
fun find_common (terms1,terms2) =
  let val tab2 = fold update_by_coeff terms2 Termtab.empty
      fun seek [] = raise TERM("find_common", [])
        | seek (t::terms) =
              let val (_,u) = Data.dest_coeff t
              in if Termtab.defined tab2 u then u else seek terms end
  in  seek terms1 end;

(*the simplification procedure*)
fun proc ctxt ct =
  let
    val prems = Simplifier.prems_of ctxt
    val t = Thm.term_of ct
    val (t', ctxt') = yield_singleton (Variable.import_terms true) t ctxt

    val (t1,t2) = Data.dest_bal t'
    val terms1 = Data.dest_sum t1
    and terms2 = Data.dest_sum t2

    val u = find_common (terms1, terms2)
    val (n1, terms1') = Data.find_first_coeff u terms1
    and (n2, terms2') = Data.find_first_coeff u terms2
    and T = Term.fastype_of u

    fun newshape (i,terms) = Data.mk_sum T (Data.mk_coeff(i,u)::terms)
    val reshape =  (*Move i*u to the front and put j*u into standard form
                       i + #m + j + k == #m + i + (j + k) *)
        if n1=0 orelse n2=0 then   (*trivial, so do nothing*)
          raise TERM("cancel_numerals", [])
        else Data.prove_conv [Data.norm_tac ctxt'] ctxt' prems
          (t', Data.mk_bal (newshape(n1,terms1'), newshape(n2,terms2')))
  in
    (if n2 <= n1 then
       Data.prove_conv
         [Data.trans_tac ctxt' reshape, resolve_tac ctxt' [Data.bal_add1] 1,
          Data.numeral_simp_tac ctxt'] ctxt' prems
         (t', Data.mk_bal (newshape(n1-n2,terms1'), Data.mk_sum T terms2'))
     else
       Data.prove_conv
         [Data.trans_tac ctxt' reshape, resolve_tac ctxt' [Data.bal_add2] 1,
          Data.numeral_simp_tac ctxt'] ctxt' prems
         (t', Data.mk_bal (Data.mk_sum T terms1', newshape(n2-n1,terms2'))))
    |> Option.map
      (Data.simplify_meta_eq ctxt' #>
        singleton (Variable.export ctxt' ctxt))
  end
  (* FIXME avoid handling of generic exceptions *)
  handle TERM _ => NONE
       | TYPE _ => NONE;   (*Typically (if thy doesn't include Numeral)
                             Undeclared type constructor "Numeral.bin"*)
end;
