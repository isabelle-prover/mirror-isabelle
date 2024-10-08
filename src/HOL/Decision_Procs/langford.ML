(*  Title:      HOL/Decision_Procs/langford.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature LANGFORD =
sig
  val dlo_tac : Proof.context -> int -> tactic
  val dlo_conv : Proof.context -> cterm -> thm
end

structure Langford: LANGFORD =
struct

val dest_set =
  let
    fun h acc ct =
      (case Thm.term_of ct of
        \<^Const_>\<open>bot _\<close> => acc
      | \<^Const_>\<open>insert _ for _ _\<close> => h (Thm.dest_arg1 ct :: acc) (Thm.dest_arg ct));
  in h [] end;

fun prove_finite cT u =
  let
    val [th0, th1] = map (Thm.instantiate' [SOME cT] []) @{thms finite.intros}
    fun ins x th =
      Thm.implies_elim
        (Thm.instantiate' [] [(SOME o Thm.dest_arg o Thm.dest_arg) (Thm.cprop_of th), SOME x] th1) th
  in fold ins u th0 end;

fun simp_rule ctxt =
  Conv.fconv_rule
    (Conv.arg_conv
      (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps @{thms ball_simps simp_thms})));

fun basic_dloqe ctxt stupid dlo_qeth dlo_qeth_nolb dlo_qeth_noub gather ep =
  (case Thm.term_of ep of
    \<^Const_>\<open>Ex _ for _\<close> =>
      let
        val p = Thm.dest_arg ep
        val ths =
          simplify (put_simpset HOL_basic_ss ctxt addsimps gather)
            (Thm.instantiate' [] [SOME p] stupid)
        val (L, U) =
          let val (_, q) = Thm.dest_abs_global (Thm.dest_arg (Thm.rhs_of ths))
          in (Thm.dest_arg1 q |> Thm.dest_arg1, Thm.dest_arg q |> Thm.dest_arg1) end
        fun proveneF S =
          let
            val (a, A) = Thm.dest_comb S |>> Thm.dest_arg
            val cT = Thm.ctyp_of_cterm a
            val ne = \<^instantiate>\<open>'a = cT and a and A in lemma \<open>insert a A \<noteq> {}\<close> by simp\<close>
            val f = prove_finite cT (dest_set S)
         in (ne, f) end

        val qe =
          (case (Thm.term_of L, Thm.term_of U) of
            (\<^Const_>\<open>bot _\<close>, _) =>
              let val (neU, fU) = proveneF U
              in simp_rule ctxt (Thm.transitive ths (dlo_qeth_nolb OF [neU, fU])) end
          | (_, \<^Const_>\<open>bot _\<close>) =>
              let val (neL,fL) = proveneF L
              in simp_rule ctxt (Thm.transitive ths (dlo_qeth_noub OF [neL, fL])) end
          | _ =>
              let
                val (neL, fL) = proveneF L
                val (neU, fU) = proveneF U
              in simp_rule ctxt (Thm.transitive ths (dlo_qeth OF [neL, neU, fL, fU])) end)
      in qe end
  | _ => error "dlo_qe : Not an existential formula");

val all_conjuncts =
  let
    fun h acc ct =
      (case Thm.term_of ct of
        \<^Const>\<open>HOL.conj for _ _\<close> => h (h acc (Thm.dest_arg ct)) (Thm.dest_arg1 ct)
      | _ => ct :: acc)
  in h [] end;

fun conjuncts ct =
  (case Thm.term_of ct of
    \<^Const>\<open>HOL.conj for _ _\<close> => Thm.dest_arg1 ct :: conjuncts (Thm.dest_arg ct)
  | _ => [ct]);

val list_conj =
  foldr1 (fn (A, B) => \<^instantiate>\<open>A and B in cterm \<open>A \<and> B\<close>\<close>);

fun mk_conj_tab th =
  let
    fun h acc th =
      (case Thm.prop_of th of
        \<^Const_>\<open>Trueprop for \<^Const_>\<open>HOL.conj for p q\<close>\<close> =>
          h (h acc (th RS conjunct2)) (th RS conjunct1)
      | \<^Const_>\<open>Trueprop for p\<close> => (p, th) :: acc)
  in fold (Termtab.insert Thm.eq_thm) (h [] th) Termtab.empty end;

fun is_conj \<^Const_>\<open>HOL.conj for _ _\<close> = true
  | is_conj _ = false;

fun prove_conj tab cjs =
  (case cjs of
    [c] =>
      if is_conj (Thm.term_of c)
      then prove_conj tab (conjuncts c)
      else tab c
  | c :: cs => conjI OF [prove_conj tab [c], prove_conj tab cs]);

fun conj_aci_rule eq =
  let
    val (l, r) = Thm.dest_equals eq
    fun tabl c = the (Termtab.lookup (mk_conj_tab (Thm.assume l)) (Thm.term_of c))
    fun tabr c = the (Termtab.lookup (mk_conj_tab (Thm.assume r)) (Thm.term_of c))
    val ll = Thm.dest_arg l
    val rr = Thm.dest_arg r
    val thl  = prove_conj tabl (conjuncts rr) |> Drule.implies_intr_hyps
    val thr  = prove_conj tabr (conjuncts ll) |> Drule.implies_intr_hyps
    val eqI =
      \<^instantiate>\<open>P = ll and Q = rr in lemma \<open>(P \<Longrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> P) \<Longrightarrow> P \<longleftrightarrow> Q\<close> by (rule iffI)\<close>
  in Thm.implies_elim (Thm.implies_elim eqI thl) thr |> mk_meta_eq end;

fun contains x ct =
  member (op aconv) (Misc_Legacy.term_frees (Thm.term_of ct)) (Thm.term_of x);

fun is_eqx x eq =
  (case Thm.term_of eq of
    \<^Const_>\<open>HOL.eq _ for l r\<close> =>
      l aconv Thm.term_of x orelse r aconv Thm.term_of x
  | _ => false);

local

fun reduce_ex_proc ctxt ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>Ex _ for \<open>Abs _\<close>\<close> =>
      let
        val e = Thm.dest_fun ct
        val (x,p) = Thm.dest_abs_global (Thm.dest_arg ct)
        val Free (xn, _) = Thm.term_of x
        val (eqs,neqs) = List.partition (is_eqx x) (all_conjuncts p)
      in
        (case eqs of
          [] =>
            let
              val (dx, ndx) = List.partition (contains x) neqs
            in
              case ndx of
                [] => NONE
              | _ =>
                conj_aci_rule
                  \<^instantiate>\<open>A = p and B = \<open>list_conj (ndx @ dx)\<close> in cterm \<open>Trueprop A \<equiv> Trueprop B\<close>\<close>
                |> Thm.abstract_rule xn x
                |> Drule.arg_cong_rule e
                |> Conv.fconv_rule
                  (Conv.arg_conv
                    (Simplifier.rewrite
                      (put_simpset HOL_basic_ss ctxt addsimps @{thms simp_thms ex_simps})))
                |> SOME
            end
        | _ =>
            conj_aci_rule
              \<^instantiate>\<open>A = p and B = \<open>list_conj (eqs @ neqs)\<close> in cterm \<open>Trueprop A \<equiv> Trueprop B\<close>\<close>
            |> Thm.abstract_rule xn x |> Drule.arg_cong_rule e
            |> Conv.fconv_rule
                (Conv.arg_conv
                  (Simplifier.rewrite
                    (put_simpset HOL_basic_ss ctxt addsimps @{thms simp_thms ex_simps})))
            |> SOME)
      end
  | _ => NONE);

in

val reduce_ex_simproc = \<^simproc_setup>\<open>passive reduce_ex ("\<exists>x. P x") = \<open>K reduce_ex_proc\<close>\<close>;

end;

fun raw_dlo_conv ctxt dlo_ss ({qe_bnds, qe_nolb, qe_noub, gst, gs, ...}: Langford_Data.entry) =
  let
    val ctxt' =
      Context_Position.set_visible false (put_simpset dlo_ss ctxt)
        addsimps @{thms dnf_simps} |> Simplifier.add_proc reduce_ex_simproc
    val dnfex_conv = Simplifier.rewrite ctxt'
    val pcv =
      Simplifier.rewrite
        (put_simpset dlo_ss ctxt
          addsimps @{thms simp_thms ex_simps all_simps all_not_ex not_all ex_disj_distrib})
    val mk_env = Cterms.list_set_rev o Cterms.build o Drule.add_frees_cterm
  in
    fn p =>
      Qelim.gen_qelim_conv ctxt pcv pcv dnfex_conv cons
        (mk_env p) (K Thm.reflexive) (K Thm.reflexive)
        (K (basic_dloqe ctxt gst qe_bnds qe_nolb qe_noub gs)) p
  end;

val grab_atom_bop =
  let
    fun h ctxt tm =
      (case Thm.term_of tm of
        \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for _ _\<close> => find_args ctxt tm
      | \<^Const_>\<open>Not for _\<close> => h ctxt (Thm.dest_arg tm)
      | \<^Const_>\<open>All _ for _\<close> => find_body ctxt (Thm.dest_arg tm)
      | \<^Const_>\<open>Pure.all _ for _\<close> => find_body ctxt (Thm.dest_arg tm)
      | \<^Const_>\<open>Ex _ for _\<close> => find_body ctxt (Thm.dest_arg tm)
      | \<^Const_>\<open>HOL.conj for _ _\<close> => find_args ctxt tm
      | \<^Const_>\<open>HOL.disj for _ _\<close> => find_args ctxt tm
      | \<^Const_>\<open>HOL.implies for _ _\<close> => find_args ctxt tm
      | \<^Const_>\<open>Pure.imp for _ _\<close> => find_args ctxt tm
      | \<^Const_>\<open>Pure.eq _ for _ _\<close> => find_args ctxt tm
      | \<^Const_>\<open>Trueprop for _\<close> => h ctxt (Thm.dest_arg tm)
      | _ => Thm.dest_fun2 tm)
    and find_args ctxt tm =
      (h ctxt (Thm.dest_arg tm) handle CTERM _ => h ctxt (Thm.dest_arg1 tm))
    and find_body ctxt b =
      let val ((_, b'), ctxt') = Variable.dest_abs_cterm b ctxt
      in h ctxt' b' end;
  in h end;

fun dlo_instance ctxt tm =
  (fst (Langford_Data.get ctxt), Langford_Data.match ctxt (grab_atom_bop ctxt tm));

fun dlo_conv ctxt tm =
  (case dlo_instance ctxt tm of
    (_, NONE) => raise CTERM ("dlo_conv (langford): no corresponding instance in context!", [tm])
  | (ss, SOME instance) => raw_dlo_conv ctxt ss instance tm);

fun generalize_tac ctxt f = CSUBGOAL (fn (p, _) => PRIMITIVE (fn st =>
  let
    fun all x t =
      Thm.apply (Thm.cterm_of ctxt (Logic.all_const (Thm.typ_of_cterm x))) (Thm.lambda x t)
    val ts = sort Thm.fast_term_ord (f p)
    val p' = fold_rev all ts p
  in Thm.implies_intr p' (Thm.implies_elim st (fold Thm.forall_elim ts (Thm.assume p'))) end));

fun cfrees ats ct =
  let
    val ins = insert (op aconvc)
    fun h acc t =
      (case Thm.term_of t of
        _ $ _ $ _ =>
          if member (op aconvc) ats (Thm.dest_fun2 t)
          then ins (Thm.dest_arg t) (ins (Thm.dest_arg1 t) acc)
          else h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
      | _ $ _ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
      | Abs _ => Thm.dest_abs_global t ||> h acc |> uncurry (remove (op aconvc))
      | Free _ => if member (op aconvc) ats t then acc else ins t acc
      | Var _ => if member (op aconvc) ats t then acc else ins t acc
      | _ => acc)
  in h [] ct end

fun dlo_tac ctxt = CSUBGOAL (fn (p, i) =>
  (case dlo_instance ctxt p of
    (ss, NONE) => simp_tac (put_simpset ss ctxt) i
  | (ss, SOME instance) =>
      Object_Logic.full_atomize_tac ctxt i THEN
      simp_tac (put_simpset ss ctxt) i
      THEN (CONVERSION Thm.eta_long_conversion) i
      THEN (TRY o generalize_tac ctxt (cfrees (#atoms instance))) i
      THEN Object_Logic.full_atomize_tac ctxt i
      THEN CONVERSION (Object_Logic.judgment_conv ctxt (raw_dlo_conv ctxt ss instance)) i
      THEN (simp_tac (put_simpset ss ctxt) i)));
end;
