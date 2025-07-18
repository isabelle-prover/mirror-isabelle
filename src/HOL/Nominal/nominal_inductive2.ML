(*  Title:      HOL/Nominal/nominal_inductive2.ML
    Author:     Stefan Berghofer, TU Muenchen

Infrastructure for proving equivariance and strong induction theorems
for inductive predicates involving nominal datatypes.
Experimental version that allows to avoid lists of atoms.
*)

signature NOMINAL_INDUCTIVE2 =
sig
  val prove_strong_ind: string -> string option -> (string * string list) list ->
    local_theory -> Proof.state
end

structure NominalInductive2 : NOMINAL_INDUCTIVE2 =
struct

val inductive_forall_def = @{thm HOL.induct_forall_def};
val inductive_atomize = @{thms induct_atomize};
val inductive_rulify = @{thms induct_rulify};

fun rulify_term thy = Simplifier.rewrite_term thy inductive_rulify [];

fun atomize_conv ctxt =
  Simplifier.rewrite_cterm (true, false, false) (K (K NONE))
    (put_simpset HOL_basic_ss ctxt addsimps inductive_atomize);
fun atomize_intr ctxt = Conv.fconv_rule (Conv.prems_conv ~1 (atomize_conv ctxt));
fun atomize_induct ctxt = Conv.fconv_rule (Conv.prems_conv ~1
  (Conv.params_conv ~1 (Conv.prems_conv ~1 o atomize_conv) ctxt));

fun fresh_postprocess ctxt =
  Simplifier.full_simplify (put_simpset HOL_basic_ss ctxt addsimps
    [@{thm fresh_star_set_eq}, @{thm fresh_star_Un_elim},
     @{thm fresh_star_insert_elim}, @{thm fresh_star_empty_elim}]);

fun preds_of ps t = inter (op = o apsnd dest_Free) ps (Term.add_frees t []);

val perm_bool = mk_meta_eq @{thm perm_bool_def};
val perm_boolI = @{thm perm_boolI};
val (_, [perm_boolI_pi, _]) = Drule.strip_comb (Thm.dest_arg
  (Drule.strip_imp_concl (Thm.cprop_of perm_boolI)));

fun mk_perm_bool ctxt pi th =
  th RS infer_instantiate ctxt [(#1 (dest_Var (Thm.term_of perm_boolI_pi)), pi)] perm_boolI;

fun mk_perm_bool_simproc names =
  Simplifier.make_simproc \<^context>
   {name = "perm_bool",
    kind = Simproc,
    lhss = [\<^term>\<open>perm pi x\<close>],
    proc = fn _ => fn _ => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>Nominal.perm\<close>, _) $ _ $ t =>
          if member (op =) names (the_default "" (try (dest_Const_name o head_of) t))
          then SOME perm_bool else NONE
       | _ => NONE),
    identifier = []};

fun transp ([] :: _) = []
  | transp xs = map hd xs :: transp (map tl xs);

fun add_binders thy i (t as (_ $ _)) bs = (case strip_comb t of
      (Const (s, T), ts) => (case strip_type T of
        (Ts, Type (tname, _)) =>
          (case NominalDatatype.get_nominal_datatype thy tname of
             NONE => fold (add_binders thy i) ts bs
           | SOME {descr, index, ...} => (case AList.lookup op =
                 (#3 (the (AList.lookup op = descr index))) s of
               NONE => fold (add_binders thy i) ts bs
             | SOME cargs => fst (fold (fn (xs, x) => fn (bs', cargs') =>
                 let val (cargs1, (u, _) :: cargs2) = chop (length xs) cargs'
                 in (add_binders thy i u
                   (fold (fn (u, T) =>
                      if exists (fn j => j < i) (loose_bnos u) then I
                      else AList.map_default op = (T, [])
                        (insert op aconv (incr_boundvars (~i) u)))
                          cargs1 bs'), cargs2)
                 end) cargs (bs, ts ~~ Ts))))
      | _ => fold (add_binders thy i) ts bs)
    | (u, ts) => add_binders thy i u (fold (add_binders thy i) ts bs))
  | add_binders thy i (Abs (_, _, t)) bs = add_binders thy (i + 1) t bs
  | add_binders thy i _ bs = bs;

fun split_conj f names (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ p $ q) _ = (case head_of p of
      Const (name, _) =>
        if member (op =) names name then SOME (f p q) else NONE
    | _ => NONE)
  | split_conj _ _ _ _ = NONE;

fun strip_all [] t = t
  | strip_all (_ :: xs) (Const (\<^const_name>\<open>All\<close>, _) $ Abs (s, T, t)) = strip_all xs t;

(*********************************************************************)
(* maps  R ... & (ALL pi_1 ... pi_n z. P z (pi_1 o ... o pi_n o t))  *)
(* or    ALL pi_1 ... pi_n z. P z (pi_1 o ... o pi_n o t)            *)
(* to    R ... & id (ALL z. P z (pi_1 o ... o pi_n o t))             *)
(* or    id (ALL z. P z (pi_1 o ... o pi_n o t))                     *)
(*                                                                   *)
(* where "id" protects the subformula from simplification            *)
(*********************************************************************)

fun inst_conj_all names ps pis (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ p $ q) _ =
      (case head_of p of
         Const (name, _) =>
           if member (op =) names name then SOME (HOLogic.mk_conj (p,
             Const (\<^const_name>\<open>Fun.id\<close>, HOLogic.boolT --> HOLogic.boolT) $
               (subst_bounds (pis, strip_all pis q))))
           else NONE
       | _ => NONE)
  | inst_conj_all names ps pis t u =
      if member (op aconv) ps (head_of u) then
        SOME (Const (\<^const_name>\<open>Fun.id\<close>, HOLogic.boolT --> HOLogic.boolT) $
          (subst_bounds (pis, strip_all pis t)))
      else NONE
  | inst_conj_all _ _ _ _ _ = NONE;

fun inst_conj_all_tac ctxt k = EVERY
  [TRY (EVERY [eresolve_tac ctxt [conjE] 1, resolve_tac ctxt [conjI] 1, assume_tac ctxt 1]),
   REPEAT_DETERM_N k (eresolve_tac ctxt [allE] 1),
   simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm id_apply}]) 1];

fun map_term f t u = (case f t u of
      NONE => map_term' f t u | x => x)
and map_term' f (t $ u) (t' $ u') = (case (map_term f t t', map_term f u u') of
      (NONE, NONE) => NONE
    | (SOME t'', NONE) => SOME (t'' $ u)
    | (NONE, SOME u'') => SOME (t $ u'')
    | (SOME t'', SOME u'') => SOME (t'' $ u''))
  | map_term' f (Abs (s, T, t)) (Abs (s', T', t')) = (case map_term f t t' of
      NONE => NONE
    | SOME t'' => SOME (Abs (s, T, t'')))
  | map_term' _ _ _ = NONE;

(*********************************************************************)
(*         Prove  F[f t]  from  F[t],  where F is monotone           *)
(*********************************************************************)

fun map_thm ctxt f tac monos opt th =
  let
    val prop = Thm.prop_of th;
    fun prove t =
      Goal.prove ctxt [] [] t (fn {context = goal_ctxt, ...} =>
        EVERY [cut_facts_tac [th] 1, eresolve_tac goal_ctxt [rev_mp] 1,
          REPEAT_DETERM (FIRSTGOAL (resolve_tac goal_ctxt monos)),
          REPEAT_DETERM (resolve_tac goal_ctxt [impI] 1 THEN (assume_tac goal_ctxt 1 ORELSE tac))])
  in Option.map prove (map_term f prop (the_default prop opt)) end;

fun abs_params params t =
  let val vs =  map (Var o apfst (rpair 0)) (Term.variant_bounds t params)
  in (Logic.list_all (params, t), (vs, subst_bounds (rev vs, t))) end;

fun inst_params thy (vs, p) th cts =
  let val env = Pattern.first_order_match thy (p, Thm.prop_of th)
    (Vartab.empty, Vartab.empty)
  in
    Thm.instantiate (TVars.empty, Vars.make (map (dest_Var o Envir.subst_term env) vs ~~ cts)) th
  end;

fun prove_strong_ind s alt_name avoids lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val ({names, ...}, {raw_induct, intrs, elims, ...}) =
      Inductive.the_inductive_global lthy (Sign.intern_const thy s);
    val ind_params = Inductive.params_of raw_induct;
    val raw_induct = atomize_induct lthy raw_induct;
    val elims = map (atomize_induct lthy) elims;
    val monos = Inductive.get_monos lthy;
    val eqvt_thms = NominalThmDecls.get_eqvt_thms lthy;
    val _ = (case subtract (op =) (fold (Term.add_const_names o Thm.prop_of) eqvt_thms []) names of
        [] => ()
      | xs => error ("Missing equivariance theorem for predicate(s): " ^
          commas_quote xs));
    val induct_cases = map (fst o fst) (fst (Rule_Cases.get (the
      (Induct.lookup_inductP lthy (hd names)))));
    val induct_cases' = if null induct_cases then replicate (length intrs) ""
      else induct_cases;
    val (raw_induct', ctxt') = lthy
      |> yield_singleton (Variable.import_terms false) (Thm.prop_of raw_induct);
    val concls = raw_induct' |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop |>
      HOLogic.dest_conj |> map (HOLogic.dest_imp ##> strip_comb);
    val ps = map (fst o snd) concls;

    val _ = (case duplicates (op = o apply2 fst) avoids of
        [] => ()
      | xs => error ("Duplicate case names: " ^ commas_quote (map fst xs)));
    val _ = (case subtract (op =) induct_cases (map fst avoids) of
        [] => ()
      | xs => error ("No such case(s) in inductive definition: " ^ commas_quote xs));
    fun mk_avoids params name sets =
      let
        val (_, ctxt') = Proof_Context.add_fixes
          (map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) params) lthy;
        fun mk s =
          let
            val t = Syntax.read_term ctxt' s;
            val t' = fold_rev absfree params t |>
              funpow (length params) (fn Abs (_, _, t) => t)
          in (t', HOLogic.dest_setT (fastype_of t)) end
          handle TERM _ =>
            error ("Expression " ^ quote s ^ " to be avoided in case " ^
              quote name ^ " is not a set type");
        fun add_set p [] = [p]
          | add_set (t, T) ((u, U) :: ps) =
              if T = U then
                let val S = HOLogic.mk_setT T
                in (Const (\<^const_name>\<open>sup\<close>, S --> S --> S) $ u $ t, T) :: ps
                end
              else (u, U) :: add_set (t, T) ps
      in
        fold (mk #> add_set) sets []
      end;

    val prems = map (fn (prem, name) =>
      let
        val prems = map (incr_boundvars 1) (Logic.strip_assums_hyp prem);
        val concl = incr_boundvars 1 (Logic.strip_assums_concl prem);
        val params = Logic.strip_params prem
      in
        (params,
         if null avoids then
           map (fn (T, ts) => (HOLogic.mk_set T ts, T))
             (fold (add_binders thy 0) (prems @ [concl]) [])
         else case AList.lookup op = avoids name of
           NONE => []
         | SOME sets =>
             map (apfst (incr_boundvars 1)) (mk_avoids params name sets),
         prems, strip_comb (HOLogic.dest_Trueprop concl))
      end) (Logic.strip_imp_prems raw_induct' ~~ induct_cases');

    val atomTs = distinct op = (maps (map snd o #2) prems);
    val atoms = map dest_Type_name atomTs;
    val ind_sort = if null atomTs then \<^sort>\<open>type\<close>
      else Sign.minimize_sort thy (Sign.certify_sort thy (map (fn a => Sign.intern_class thy
        ("fs_" ^ Long_Name.base_name a)) atoms));
    val (fs_ctxt_tyname, _) = Name.variant "'n" (Variable.names_of ctxt');
    val ([fs_ctxt_name], ctxt'') = Variable.variant_fixes ["z"] ctxt';
    val fsT = TFree (fs_ctxt_tyname, ind_sort);

    val inductive_forall_def' = Thm.instantiate'
      [SOME (Thm.global_ctyp_of thy fsT)] [] inductive_forall_def;

    fun lift_pred' t (Free (s, T)) ts =
      list_comb (Free (s, fsT --> T), t :: ts);
    val lift_pred = lift_pred' (Bound 0);

    fun lift_prem (t as (f $ u)) =
          let val (p, ts) = strip_comb t
          in
            if member (op =) ps p then HOLogic.mk_induct_forall fsT $
              Abs ("z", fsT, lift_pred p (map (incr_boundvars 1) ts))
            else lift_prem f $ lift_prem u
          end
      | lift_prem (Abs (s, T, t)) = Abs (s, T, lift_prem t)
      | lift_prem t = t;

    fun mk_fresh (x, T) = HOLogic.mk_Trueprop
      (NominalDatatype.fresh_star_const T fsT $ x $ Bound 0);

    val (prems', prems'') = split_list (map (fn (params, sets, prems, (p, ts)) =>
      let
        val params' = params @ [("y", fsT)];
        val prem = Logic.list_implies
          (map mk_fresh sets @
           map (fn prem =>
             if null (preds_of ps prem) then prem
             else lift_prem prem) prems,
           HOLogic.mk_Trueprop (lift_pred p ts));
      in abs_params params' prem end) prems);

    val ind_vars =
      (Case_Translation.indexify_names (replicate (length atomTs) "pi") ~~
       map NominalAtoms.mk_permT atomTs) @ [("z", fsT)];
    val ind_Ts = rev (map snd ind_vars);

    val concl = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
      (map (fn (prem, (p, ts)) => HOLogic.mk_imp (prem,
        HOLogic.list_all (ind_vars, lift_pred p
          (map (fold_rev (NominalDatatype.mk_perm ind_Ts)
            (map Bound (length atomTs downto 1))) ts)))) concls));

    val concl' = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
      (map (fn (prem, (p, ts)) => HOLogic.mk_imp (prem,
        lift_pred' (Free (fs_ctxt_name, fsT)) p ts)) concls));

    val (vc_compat, vc_compat') = map (fn (params, sets, prems, (p, ts)) =>
      map (fn q => abs_params params (incr_boundvars ~1 (Logic.list_implies
          (map_filter (fn prem =>
             if null (preds_of ps prem) then SOME prem
             else map_term (split_conj (K o I) names) prem prem) prems, q))))
        (maps (fn (t, T) => map (fn (u, U) => HOLogic.mk_Trueprop
           (NominalDatatype.fresh_star_const U T $ u $ t)) sets)
             (ts ~~ binder_types (fastype_of p)) @
         map (fn (u, U) => HOLogic.mk_Trueprop (Const (\<^const_name>\<open>finite\<close>,
           HOLogic.mk_setT U --> HOLogic.boolT) $ u)) sets) |>
      split_list) prems |> split_list;

    val perm_pi_simp = Global_Theory.get_thms thy "perm_pi_simp";
    val pt2_atoms = map (fn a => Global_Theory.get_thm thy
      ("pt_" ^ Long_Name.base_name a ^ "2")) atoms;
    fun eqvt_ss ctxt =
      put_simpset HOL_basic_ss ctxt
        addsimps (eqvt_thms @ perm_pi_simp @ pt2_atoms)
        |> Simplifier.add_proc (mk_perm_bool_simproc [\<^const_name>\<open>Fun.id\<close>])
        |> Simplifier.add_proc NominalPermeq.perm_app_simproc
        |> Simplifier.add_proc NominalPermeq.perm_fun_simproc;
    val fresh_star_bij = Global_Theory.get_thms thy "fresh_star_bij";
    val pt_insts = map (NominalAtoms.pt_inst_of thy) atoms;
    val at_insts = map (NominalAtoms.at_inst_of thy) atoms;
    val dj_thms = maps (fn a =>
      map (NominalAtoms.dj_thm_of thy a) (remove (op =) a atoms)) atoms;
    val finite_ineq = map2 (fn th => fn th' => th' RS (th RS
      @{thm pt_set_finite_ineq})) pt_insts at_insts;
    val perm_set_forget =
      map (fn th => th RS @{thm dj_perm_set_forget}) dj_thms;
    val perm_freshs_freshs = atomTs ~~ map2 (fn th => fn th' => th' RS (th RS
      @{thm pt_freshs_freshs})) pt_insts at_insts;

    fun obtain_fresh_name ts sets (T, fin) (freshs, ths1, ths2, ths3, ctxt) =
      let
        val thy = Proof_Context.theory_of ctxt;
        (** protect terms to avoid that fresh_star_prod_set interferes with  **)
        (** pairs used in introduction rules of inductive predicate          **)
        fun protect t =
          let val T = fastype_of t in Const (\<^const_name>\<open>Fun.id\<close>, T --> T) $ t end;
        val p = foldr1 HOLogic.mk_prod (map protect ts);
        val atom = dest_Type_name T;
        val {at_inst, ...} = NominalAtoms.the_atom_info thy atom;
        val fs_atom = Global_Theory.get_thm thy
          ("fs_" ^ Long_Name.base_name atom ^ "1");
        val avoid_th = Thm.instantiate'
          [SOME (Thm.global_ctyp_of thy (fastype_of p))] [SOME (Thm.global_cterm_of thy p)]
          ([at_inst, fin, fs_atom] MRS @{thm at_set_avoiding});
        val (([(_, cx)], th1 :: th2 :: ths), ctxt') = Obtain.result
          (fn ctxt' => EVERY
            [resolve_tac ctxt' [avoid_th] 1,
             full_simp_tac (put_simpset HOL_ss ctxt' addsimps [@{thm fresh_star_prod_set}]) 1,
             full_simp_tac (put_simpset HOL_basic_ss ctxt' addsimps [@{thm id_apply}]) 1,
             rotate_tac 1 1,
             REPEAT (eresolve_tac ctxt' [conjE] 1)])
          [] ctxt;
        val (Ts1, _ :: Ts2) = chop_prefix (not o equal T) (map snd sets);
        val pTs = map NominalAtoms.mk_permT (Ts1 @ Ts2);
        val (pis1, pis2) = chop (length Ts1)
          (map Bound (length pTs - 1 downto 0));
        val _ $ (f $ (_ $ pi $ l) $ r) = Thm.prop_of th2
        val th2' =
          Goal.prove ctxt' [] []
            (Logic.list_all (map (pair "pi") pTs, HOLogic.mk_Trueprop
               (f $ fold_rev (NominalDatatype.mk_perm (rev pTs))
                  (pis1 @ pi :: pis2) l $ r)))
            (fn {context = goal_ctxt, ...} =>
              cut_facts_tac [th2] 1 THEN
              full_simp_tac (put_simpset HOL_basic_ss goal_ctxt addsimps perm_set_forget) 1) |>
          Simplifier.simplify (eqvt_ss ctxt')
      in
        (freshs @ [Thm.term_of cx],
         ths1 @ ths, ths2 @ [th1], ths3 @ [th2'], ctxt')
      end;

    fun mk_ind_proof ctxt thss =
      Goal.prove ctxt [] prems' concl' (fn {prems = ihyps, context = goal_ctxt} =>
        let val th = Goal.prove goal_ctxt [] [] concl (fn {context = goal_ctxt1, ...} =>
          resolve_tac goal_ctxt1 [raw_induct] 1 THEN
          EVERY (maps (fn (((((_, sets, oprems, _),
              vc_compat_ths), vc_compat_vs), ihyp), vs_ihypt) =>
            [REPEAT (resolve_tac goal_ctxt1 [allI] 1), simp_tac (eqvt_ss goal_ctxt1) 1,
             SUBPROOF (fn {prems = gprems, params, concl, context = goal_ctxt2, ...} =>
               let
                 val (cparams', (pis, z)) =
                   chop (length params - length atomTs - 1) (map #2 params) ||>
                   (map Thm.term_of #> split_last);
                 val params' = map Thm.term_of cparams'
                 val sets' = map (apfst (curry subst_bounds (rev params'))) sets;
                 val pi_sets = map (fn (t, _) =>
                   fold_rev (NominalDatatype.mk_perm []) pis t) sets';
                 val (P, ts) = strip_comb (HOLogic.dest_Trueprop (Thm.term_of concl));
                 val gprems1 = map_filter (fn (th, t) =>
                   if null (preds_of ps t) then SOME th
                   else
                     map_thm goal_ctxt2 (split_conj (K o I) names)
                       (eresolve_tac goal_ctxt2 [conjunct1] 1) monos NONE th)
                   (gprems ~~ oprems);
                 val vc_compat_ths' = map2 (fn th => fn p =>
                   let
                     val th' = gprems1 MRS inst_params thy p th cparams';
                     val (h, ts) =
                       strip_comb (HOLogic.dest_Trueprop (Thm.concl_of th'))
                   in
                     Goal.prove goal_ctxt2 [] []
                       (HOLogic.mk_Trueprop (list_comb (h,
                          map (fold_rev (NominalDatatype.mk_perm []) pis) ts)))
                       (fn {context = goal_ctxt3, ...} =>
                         simp_tac (put_simpset HOL_basic_ss goal_ctxt3 addsimps
                          (fresh_star_bij @ finite_ineq)) 1 THEN resolve_tac goal_ctxt3 [th'] 1)
                   end) vc_compat_ths vc_compat_vs;
                 val (vc_compat_ths1, vc_compat_ths2) =
                   chop (length vc_compat_ths - length sets) vc_compat_ths';
                 val vc_compat_ths1' = map
                   (Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv
                      (Simplifier.rewrite (eqvt_ss goal_ctxt2))))) vc_compat_ths1;
                 val (pis', fresh_ths1, fresh_ths2, fresh_ths3, ctxt'') = fold
                   (obtain_fresh_name ts sets)
                   (map snd sets' ~~ vc_compat_ths2) ([], [], [], [], goal_ctxt2);
                 fun concat_perm pi1 pi2 =
                   let val T = fastype_of pi1
                   in if T = fastype_of pi2 then
                       Const (\<^const_name>\<open>append\<close>, T --> T --> T) $ pi1 $ pi2
                     else pi2
                   end;
                 val pis'' = fold_rev (concat_perm #> map) pis' pis;
                 val ihyp' = inst_params thy vs_ihypt ihyp
                   (map (fold_rev (NominalDatatype.mk_perm [])
                      (pis' @ pis) #> Thm.global_cterm_of thy) params' @ [Thm.global_cterm_of thy z]);
                 fun mk_pi th =
                   Simplifier.simplify
                     (put_simpset HOL_basic_ss ctxt'' addsimps [@{thm id_apply}]
                       |> Simplifier.add_proc NominalDatatype.perm_simproc)
                     (Simplifier.simplify (eqvt_ss ctxt'')
                       (fold_rev (mk_perm_bool ctxt'' o Thm.cterm_of ctxt'')
                         (pis' @ pis) th));
                 val gprems2 = map (fn (th, t) =>
                   if null (preds_of ps t) then mk_pi th
                   else
                     mk_pi (the (map_thm ctxt'' (inst_conj_all names ps (rev pis''))
                       (inst_conj_all_tac ctxt'' (length pis'')) monos (SOME t) th)))
                   (gprems ~~ oprems);
                 val perm_freshs_freshs' = map (fn (th, (_, T)) =>
                   th RS the (AList.lookup op = perm_freshs_freshs T))
                     (fresh_ths2 ~~ sets);
                 val th = Goal.prove ctxt'' [] []
                   (HOLogic.mk_Trueprop (list_comb (P $ hd ts,
                     map (fold_rev (NominalDatatype.mk_perm []) pis') (tl ts))))
                   (fn {context = goal_ctxt4, ...} =>
                     EVERY ([simp_tac (eqvt_ss goal_ctxt4) 1,
                     resolve_tac goal_ctxt4 [ihyp'] 1] @
                     map (fn th => resolve_tac goal_ctxt4 [th] 1) fresh_ths3 @
                     [REPEAT_DETERM_N (length gprems)
                       (simp_tac (put_simpset HOL_basic_ss goal_ctxt4
                          addsimps [inductive_forall_def']
                          |> Simplifier.add_proc NominalDatatype.perm_simproc) 1 THEN
                        resolve_tac goal_ctxt4 gprems2 1)]));
                 val final = Goal.prove ctxt'' [] [] (Thm.term_of concl)
                   (fn {context = goal_ctxt5, ...} =>
                     cut_facts_tac [th] 1 THEN full_simp_tac (put_simpset HOL_ss goal_ctxt5
                     addsimps vc_compat_ths1' @ fresh_ths1 @
                       perm_freshs_freshs') 1);
                 val final' = Proof_Context.export ctxt'' goal_ctxt2 [final];
               in resolve_tac goal_ctxt2 final' 1 end) goal_ctxt1 1])
                 (prems ~~ thss ~~ vc_compat' ~~ ihyps ~~ prems'')))
        in
          cut_facts_tac [th] 1 THEN REPEAT (eresolve_tac goal_ctxt [conjE] 1) THEN
          REPEAT (REPEAT (resolve_tac goal_ctxt [conjI, impI] 1) THEN
            eresolve_tac goal_ctxt [impE] 1 THEN
            assume_tac goal_ctxt 1 THEN REPEAT (eresolve_tac goal_ctxt @{thms allE_Nil} 1) THEN
            asm_full_simp_tac goal_ctxt 1)
        end) |>
        fresh_postprocess ctxt |>
        singleton (Proof_Context.export ctxt lthy);
  in
    ctxt'' |>
    Proof.theorem NONE (fn thss => fn lthy1 =>
      let
        val rec_name = space_implode "_" (map Long_Name.base_name names);
        val rec_qualified = Binding.qualify false rec_name;
        val ind_case_names = Rule_Cases.case_names induct_cases;
        val induct_cases' = Inductive.partition_rules' raw_induct
          (intrs ~~ induct_cases); 
        val thss' = map (map (atomize_intr lthy1)) thss;
        val thsss = Inductive.partition_rules' raw_induct (intrs ~~ thss');
        val strong_raw_induct =
          mk_ind_proof lthy1 thss' |> Inductive.rulify lthy1;
        val strong_induct_atts =
          map (Attrib.internal \<^here> o K)
            [ind_case_names, Rule_Cases.consumes (~ (Thm.nprems_of strong_raw_induct))];
        val strong_induct =
          if length names > 1 then strong_raw_induct
          else strong_raw_induct RSN (2, rev_mp);
        val (induct_name, inducts_name) =
          case alt_name of
            NONE => (rec_qualified (Binding.name "strong_induct"),
                     rec_qualified (Binding.name "strong_inducts"))
          | SOME s => (Binding.name s, Binding.name (s ^ "s"));
        val ((_, [strong_induct']), lthy2) = lthy1 |> Local_Theory.note
          ((induct_name, strong_induct_atts), [strong_induct]);
        val strong_inducts =
          Project_Rule.projects lthy2 (1 upto length names) strong_induct'
      in
        lthy2 |>
        Local_Theory.notes [((inducts_name, []),
          strong_inducts |> map (fn th => ([th],
            [Attrib.internal \<^here> (K ind_case_names),
             Attrib.internal \<^here> (K (Rule_Cases.consumes (1 - Thm.nprems_of th)))])))] |> snd
      end)
      (map (map (rulify_term thy #> rpair [])) vc_compat)
  end;


(* outer syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>nominal_inductive2\<close>
    "prove strong induction theorem for inductive predicate involving nominal datatypes"
    (Parse.name -- 
     Scan.option (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.name --| \<^keyword>\<open>)\<close>)) --
     (Scan.optional (\<^keyword>\<open>avoids\<close> |-- Parse.enum1 "|" (Parse.name --
      (\<^keyword>\<open>:\<close> |-- Parse.and_list1 Parse.term))) []) >> (fn ((name, rule_name), avoids) =>
        prove_strong_ind name rule_name avoids));

end
