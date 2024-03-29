(*  Title:      Provers/Arith/combine_numerals.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Combine coefficients in expressions:

     i + #m*u + j ... + #n*u + k  ==  #(m+n)*u + (i + (j + k))

It works by (a) massaging the sum to bring the selected terms to the front:

     #m*u + (#n*u + (i + (j + k)))

(b) then using left_distrib to reach

     #(m+n)*u + (i + (j + k))
*)

signature COMBINE_NUMERALS_DATA =
sig
  (*abstract syntax*)
  eqtype coeff
  val iszero: coeff -> bool
  val add: coeff * coeff -> coeff     (*addition (or multiplication) *)
  val mk_sum: typ -> term list -> term
  val dest_sum: term -> term list
  val mk_coeff: coeff * term -> term
  val dest_coeff: term -> coeff * term
  (*rules*)
  val left_distrib: thm
  (*proof tools*)
  val prove_conv: tactic list -> Proof.context -> term * term -> thm option
  val trans_tac: Proof.context -> thm option -> tactic            (*applies the initial lemma*)
  val norm_tac: Proof.context -> tactic          (*proves the initial lemma*)
  val numeral_simp_tac: Proof.context -> tactic  (*proves the final theorem*)
  val simplify_meta_eq: Proof.context -> thm -> thm  (*simplifies the final theorem*)
end;


functor CombineNumeralsFun(Data: COMBINE_NUMERALS_DATA):
  sig
  val proc: Simplifier.proc
  end
=
struct

(*Remove the first occurrence of #m*u from the term list*)
fun remove (_, _, []) = (*impossible, since #m*u was found by find_repeated*)
      raise TERM("combine_numerals: remove", [])
  | remove (m, u, t::terms) =
      case try Data.dest_coeff t of
          SOME(n,v) => if m=n andalso u aconv v then terms
                       else t :: remove (m, u, terms)
        | NONE      =>  t :: remove (m, u, terms);

(*a left-to-right scan of terms, seeking another term of the form #n*u, where
  #m*u is already in terms for some m*)
fun find_repeated (tab, _, []) = raise TERM("find_repeated", [])
  | find_repeated (tab, past, t::terms) =
      case try Data.dest_coeff t of
          SOME(n,u) =>
              (case Termtab.lookup tab u of
                  SOME m => (u, m, n, rev (remove (m,u,past)) @ terms)
                | NONE => find_repeated (Termtab.update (u, n) tab,
                                         t::past,  terms))
        | NONE => find_repeated (tab, t::past, terms);

(*the simplification procedure*)
fun proc ctxt ct =
  let
    val t = Thm.term_of ct
    val (t', ctxt') = yield_singleton (Variable.import_terms true) t ctxt

    val (u,m,n,terms) = find_repeated (Termtab.empty, [], Data.dest_sum t')
    val T = Term.fastype_of u

    val reshape =  (*Move i*u to the front and put j*u into standard form
                       i + #m + j + k == #m + i + (j + k) *)
      if Data.iszero m orelse Data.iszero n then   (*trivial, so do nothing*)
        raise TERM("combine_numerals", [])
      else Data.prove_conv [Data.norm_tac ctxt'] ctxt'
        (t', Data.mk_sum T ([Data.mk_coeff (m, u), Data.mk_coeff (n, u)] @ terms))
  in
    Data.prove_conv
       [Data.trans_tac ctxt' reshape, resolve_tac ctxt' [Data.left_distrib] 1,
        Data.numeral_simp_tac ctxt'] ctxt'
       (t', Data.mk_sum T (Data.mk_coeff(Data.add(m,n), u) :: terms))
    |> Option.map
      (Data.simplify_meta_eq ctxt' #>
        singleton (Variable.export ctxt' ctxt))
  end
  (* FIXME avoid handling of generic exceptions *)
  handle TERM _ => NONE
       | TYPE _ => NONE;   (*Typically (if thy doesn't include Numeral)
                             Undeclared type constructor "Numeral.bin"*)

end;
