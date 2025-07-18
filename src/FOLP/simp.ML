(*  Title:      FOLP/simp.ML
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

FOLP version of...

Generic simplifier, suitable for most logics.  (from Provers)

This version allows instantiation of Vars in the subgoal, since the proof
term must change.
*)

signature SIMP_DATA =
sig
  val case_splits  : (thm * string) list
  val dest_red     : term -> term * term * term
  val mk_rew_rules : thm -> thm list
  val norm_thms    : (thm*thm) list (* [(?x>>norm(?x), norm(?x)>>?x), ...] *)
  val red1         : thm        (*  ?P>>?Q  ==>  ?P  ==>  ?Q  *)
  val red2         : thm        (*  ?P>>?Q  ==>  ?Q  ==>  ?P  *)
  val refl_thms    : thm list
  val subst_thms   : thm list   (* [ ?a>>?b ==> ?P(?a) ==> ?P(?b), ...] *)
  val trans_thms   : thm list
end;


infix 4 addcongs delrews delcongs setauto;

signature SIMP =
sig
  type simpset
  val empty_ss  : simpset
  val addcongs  : simpset * thm list -> simpset
  val addrew    : Proof.context -> thm -> simpset -> simpset
  val delcongs  : simpset * thm list -> simpset
  val delrews   : simpset * thm list -> simpset
  val dest_ss   : simpset -> thm list * thm list
  val print_ss  : Proof.context -> simpset -> unit
  val setauto   : simpset * (Proof.context -> int -> tactic) -> simpset
  val ASM_SIMP_CASE_TAC : Proof.context -> simpset -> int -> tactic
  val ASM_SIMP_TAC      : Proof.context -> simpset -> int -> tactic
  val CASE_TAC          : Proof.context -> simpset -> int -> tactic
  val SIMP_CASE2_TAC    : Proof.context -> simpset -> int -> tactic
  val SIMP_THM          : Proof.context -> simpset -> thm -> thm
  val SIMP_TAC          : Proof.context -> simpset -> int -> tactic
  val SIMP_CASE_TAC     : Proof.context -> simpset -> int -> tactic
  val mk_congs          : Proof.context -> string list -> thm list
  val mk_typed_congs    : Proof.context -> (string * string) list -> thm list
(* temporarily disabled:
  val extract_free_congs        : unit -> thm list
*)
  val tracing   : bool Unsynchronized.ref
end;

functor SimpFun (Simp_data: SIMP_DATA) : SIMP =
struct

local open Simp_data in

(*For taking apart reductions into left, right hand sides*)
val lhs_of = #2 o dest_red;
val rhs_of = #3 o dest_red;

(*** Indexing and filtering of theorems ***)

fun eq_brl ((b1 : bool, th1), (b2, th2)) = b1 = b2 andalso Thm.eq_thm_prop (th1, th2);

(*insert a thm in a discrimination net by its lhs*)
fun lhs_insert_thm th net =
    Net.insert_term eq_brl (lhs_of (Thm.concl_of th), (false,th)) net
    handle  Net.INSERT => net;

(*match subgoal i against possible theorems in the net.
  Similar to match_from_nat_tac, but the net does not contain numbers;
  rewrite rules are not ordered.*)
fun net_tac ctxt net =
  SUBGOAL(fn (prem, i) =>
    resolve_tac ctxt (Net.unify_term net (Logic.strip_assums_concl prem)) i);

(*match subgoal i against possible theorems indexed by lhs in the net*)
fun lhs_net_tac ctxt net =
  SUBGOAL(fn (prem,i) =>
          biresolve_tac ctxt (Net.unify_term net
                       (lhs_of (Logic.strip_assums_concl prem))) i);

fun goal_concl i thm = Logic.strip_assums_concl (Thm.prem_of thm i);

fun lhs_of_eq i thm = lhs_of(goal_concl i thm)
and rhs_of_eq i thm = rhs_of(goal_concl i thm);

fun var_lhs(thm,i) =
let fun var(Var _) = true
      | var(Abs(_,_,t)) = var t
      | var(f$_) = var f
      | var _ = false;
in var(lhs_of_eq i thm) end;

fun contains_op opns =
    let fun contains(Const(s,_)) = member (op =) opns s |
            contains(s$t) = contains s orelse contains t |
            contains(Abs(_,_,t)) = contains t |
            contains _ = false;
    in contains end;

fun may_match(match_ops,i) = contains_op match_ops o lhs_of_eq i;

val (normI_thms,normE_thms) = split_list norm_thms;

(*Get the norm constants from norm_thms*)
val norms =
  let fun norm thm =
      case lhs_of (Thm.concl_of thm) of
          Const(n,_)$_ => n
        | _ => error "No constant in lhs of a norm_thm"
  in map norm normE_thms end;

fun lhs_is_NORM(thm,i) = case lhs_of_eq i thm of
        Const(s,_)$_ => member (op =) norms s | _ => false;

fun refl_tac ctxt = resolve_tac ctxt refl_thms;

fun find_res thms thm =
    let fun find [] = error "Check Simp_Data"
          | find(th::thms) = thm RS th handle THM _ => find thms
    in find thms end;

val mk_trans = find_res trans_thms;

fun mk_trans2 thm =
let fun mk[] = error"Check transitivity"
      | mk(t::ts) = (thm RSN (2,t))  handle THM _  => mk ts
in mk trans_thms end;

(*Applies tactic and returns the first resulting state, FAILS if none!*)
fun one_result(tac,thm) = case Seq.pull(tac thm) of
        SOME(thm',_) => thm'
      | NONE => raise THM("Simplifier: could not continue", 0, [thm]);

fun res1 ctxt (thm,thms,i) = one_result (resolve_tac ctxt thms i,thm);


(**** Adding "NORM" tags ****)

(*get name of the constant from conclusion of a congruence rule*)
fun cong_const cong =
    case head_of (lhs_of (Thm.concl_of cong)) of
        Const(c,_) => c
      | _ => ""                 (*a placeholder distinct from const names*);

(*true if the term is an atomic proposition (no ==> signs) *)
val atomic = null o Logic.strip_assums_hyp;

(*ccs contains the names of the constants possessing congruence rules*)
fun add_hidden_vars ccs =
  let fun add_hvars tm hvars = case tm of
              Abs(_,_,body) => Misc_Legacy.add_term_vars(body,hvars)
            | _$_ => let val (f,args) = strip_comb tm
                     in case f of
                            Const(c,_) =>
                                if member (op =) ccs c
                                then fold_rev add_hvars args hvars
                                else Misc_Legacy.add_term_vars (tm, hvars)
                          | _ => Misc_Legacy.add_term_vars (tm, hvars)
                     end
            | _ => hvars;
  in add_hvars end;

fun add_new_asm_vars new_asms =
    let fun itf (tm, at) vars =
                if at then vars else Misc_Legacy.add_term_vars(tm,vars)
        fun add_list(tm,al,vars) = let val (_,tml) = strip_comb tm
                in if length(tml)=length(al)
                   then fold_rev itf (tml ~~ al) vars
                   else vars
                end
        fun add_vars (tm,vars) = case tm of
                  Abs (_,_,body) => add_vars(body,vars)
                | r$s => (case head_of tm of
                          Const(c,_) => (case AList.lookup (op =) new_asms c of
                                  NONE => add_vars(r,add_vars(s,vars))
                                | SOME(al) => add_list(tm,al,vars))
                        | _ => add_vars(r,add_vars(s,vars)))
                | _ => vars
    in add_vars end;


fun add_norms ctxt (congs,ccs,new_asms) thm =
let val thm' = mk_trans2 thm;
(* thm': [?z -> l; Prems; r -> ?t] ==> ?z -> ?t *)
    val nops = Thm.nprems_of thm'
    val lhs = rhs_of_eq 1 thm'
    val rhs = lhs_of_eq nops thm'
    val asms = tl(rev(tl(Thm.prems_of thm')))
    val hvars = fold_rev (add_hidden_vars ccs) (lhs::rhs::asms) []
    val hvars = add_new_asm_vars new_asms (rhs,hvars)
    fun it_asms asm hvars =
        if atomic asm then add_new_asm_vars new_asms (asm,hvars)
        else Misc_Legacy.add_term_frees(asm,hvars)
    val hvars = fold_rev it_asms asms hvars
    val hvs = map (#1 o dest_Var) hvars
    fun norm_step_tac st = st |>
         (case head_of(rhs_of_eq 1 st) of
            Var(ixn,_) => if member (op =) hvs ixn then refl_tac ctxt 1
                          else resolve_tac ctxt normI_thms 1 ORELSE refl_tac ctxt 1
          | Const _ => resolve_tac ctxt normI_thms 1 ORELSE
                       resolve_tac ctxt congs 1 ORELSE refl_tac ctxt 1
          | Free _ => resolve_tac ctxt congs 1 ORELSE refl_tac ctxt 1
          | _ => refl_tac ctxt 1)
    val add_norm_tac = DEPTH_FIRST (has_fewer_prems nops) norm_step_tac
    val SOME(thm'',_) = Seq.pull(add_norm_tac thm')
in thm'' end;

fun add_norm_tags ctxt congs =
    let val ccs = map cong_const congs
        val new_asms = filter (exists not o #2)
                (ccs ~~ (map (map atomic o Thm.prems_of) congs));
    in add_norms ctxt (congs,ccs,new_asms) end;

fun normed_rews ctxt congs =
  let
    val add_norms = add_norm_tags ctxt congs
    fun normed thm =
      let
        val ctxt' = Variable.declare_thm thm ctxt;
      in Variable.tradeT (K (map (add_norms o mk_trans) o maps mk_rew_rules)) ctxt [thm] end
  in normed end;

fun NORM ctxt norm_lhs_tac = EVERY' [resolve_tac ctxt [red2], norm_lhs_tac, refl_tac ctxt];

val trans_norms = map mk_trans normE_thms;


(* SIMPSET *)

datatype simpset =
        SS of {auto_tac: Proof.context -> int -> tactic,
               congs: thm list,
               cong_net: thm Net.net,
               mk_simps: Proof.context -> thm -> thm list,
               simps: (thm * thm list) list,
               simp_net: thm Net.net}

val empty_ss = SS{auto_tac= K (K no_tac), congs=[], cong_net=Net.empty,
                  mk_simps = fn ctxt => normed_rews ctxt [], simps=[], simp_net=Net.empty};

(** Insertion of congruences and rewrites **)

(*insert a thm in a thm net*)
fun insert_thm th net =
  Net.insert_term Thm.eq_thm_prop (Thm.concl_of th, th) net
    handle Net.INSERT => net;

val insert_thms = fold_rev insert_thm;

fun addrew ctxt thm (SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net}) =
let val thms = map Thm.trim_context (mk_simps ctxt thm)
in SS{auto_tac=auto_tac,congs=congs, cong_net=cong_net, mk_simps=mk_simps,
      simps = (thm,thms)::simps, simp_net = insert_thms thms simp_net}
end;

fun op addcongs(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net}, thms) =
let val congs' = map Thm.trim_context thms @ congs;
in SS{auto_tac=auto_tac, congs= congs',
      cong_net= insert_thms (map mk_trans thms) cong_net,
      mk_simps = fn ctxt => normed_rews ctxt congs', simps=simps, simp_net=simp_net}
end;

(** Deletion of congruences and rewrites **)

fun delete_thm th net =
  Net.delete_term_safe Thm.eq_thm_prop (Thm.concl_of th, th) net;

val delete_thms = fold_rev delete_thm;

fun op delcongs(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net}, thms) =
let val congs' = fold (remove Thm.eq_thm_prop) thms congs
in SS{auto_tac=auto_tac, congs= congs',
      cong_net= delete_thms (map mk_trans thms) cong_net,
      mk_simps= fn ctxt => normed_rews ctxt congs', simps=simps, simp_net=simp_net}
end;

fun delrew thm (SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net}) =
let fun find((p as (th,ths))::ps',ps) =
          if Thm.eq_thm_prop(thm,th) then (ths,ps@ps') else find(ps',p::ps)
      | find([],simps') = ([], simps')
    val (thms,simps') = find(simps,[])
in SS{auto_tac=auto_tac, congs=congs, cong_net=cong_net, mk_simps=mk_simps,
      simps = simps', simp_net = delete_thms thms simp_net }
end;

fun ss delrews thms = fold delrew thms ss;


fun op setauto(SS{congs,cong_net,mk_simps,simps,simp_net,...}, auto_tac) =
    SS{auto_tac=auto_tac, congs=congs, cong_net=cong_net, mk_simps=mk_simps,
       simps=simps, simp_net=simp_net};


(** Inspection of a simpset **)

fun dest_ss(SS{congs,simps,...}) = (congs, map #1 simps);

fun print_ss ctxt (SS{congs,simps,...}) =
  writeln (cat_lines
   (["Congruences:"] @ map (Thm.string_of_thm ctxt) congs @
    ["Rewrite Rules:"] @ map (Thm.string_of_thm ctxt o #1) simps));


(* Rewriting with conditionals *)

val (case_thms,case_consts) = split_list case_splits;
val case_rews = map mk_trans case_thms;

fun if_rewritable ifc i thm =
    let val tm = goal_concl i thm
        fun nobound(Abs(_,_,tm),j,k) = nobound(tm,j,k+1)
          | nobound(s$t,j,k) = nobound(s,j,k) andalso nobound(t,j,k)
          | nobound(Bound n,j,k) = n < k orelse k+j <= n
          | nobound(_) = true;
        fun check_args(al,j) = forall (fn t => nobound(t,j,0)) al
        fun find_if(Abs(_,_,tm),j) = find_if(tm,j+1)
          | find_if(tm as s$t,j) = let val (f,al) = strip_comb tm in
                case f of Const(c,_) => if c=ifc then check_args(al,j)
                        else find_if(s,j) orelse find_if(t,j)
                | _ => find_if(s,j) orelse find_if(t,j) end
          | find_if(_) = false;
    in find_if(tm,0) end;

fun IF1_TAC ctxt cong_tac i =
    let fun seq_try (ifth::ifths,ifc::ifcs) thm =
                (COND (if_rewritable ifc i) (DETERM(resolve_tac ctxt [ifth] i))
                        (seq_try(ifths,ifcs))) thm
              | seq_try([],_) thm = no_tac thm
        and try_rew thm = (seq_try(case_rews,case_consts) ORELSE one_subt) thm
        and one_subt thm =
                let val test = has_fewer_prems (Thm.nprems_of thm + 1)
                    fun loop thm =
                        COND test no_tac
                          ((try_rew THEN DEPTH_FIRST test (refl_tac ctxt i))
                           ORELSE (refl_tac ctxt i THEN loop)) thm
                in (cong_tac THEN loop) thm end
    in COND (may_match(case_consts,i)) try_rew no_tac end;

fun CASE_TAC ctxt (SS{cong_net,...}) i =
  let val cong_tac = net_tac ctxt cong_net i
  in NORM ctxt (IF1_TAC ctxt cong_tac) i end;


(* Rewriting Automaton *)

datatype cntrl = STOP | MK_EQ | ASMS of int | SIMP_LHS | REW | REFL | TRUE
               | PROVE | POP_CS | POP_ARTR | IF;

fun simp_refl([],_,ss) = ss
  | simp_refl(a'::ns,a,ss) = if a'=a then simp_refl(ns,a,SIMP_LHS::REFL::ss)
        else simp_refl(ns,a,ASMS(a)::SIMP_LHS::REFL::POP_ARTR::ss);

(** Tracing **)

val tracing = Unsynchronized.ref false;

(*Replace parameters by Free variables in P*)
fun variants_abs ([],P) = P
  | variants_abs ((a,T)::aTs, P) =
      variants_abs (aTs, #2 (Term.dest_abs_global (Abs (a,T,P))));

(*Select subgoal i from proof state; substitute parameters, for printing*)
fun prepare_goal i st =
    let val subgi = Thm.prem_of st i
        val params = rev (Logic.strip_params subgi)
    in variants_abs (params, Logic.strip_assums_concl subgi) end;

(*print lhs of conclusion of subgoal i*)
fun pr_goal_lhs ctxt i st =
    writeln (Syntax.string_of_term ctxt (lhs_of (prepare_goal i st)));

(*print conclusion of subgoal i*)
fun pr_goal_concl ctxt i st =
    writeln (Syntax.string_of_term ctxt (prepare_goal i st))

(*print subgoals i to j (inclusive)*)
fun pr_goals ctxt (i,j) st =
    if i>j then ()
    else (pr_goal_concl ctxt i st;  pr_goals ctxt (i+1,j) st);

(*Print rewrite for tracing; i=subgoal#, n=number of new subgoals,
  thm=old state, thm'=new state *)
fun pr_rew ctxt (i,n,thm,thm',not_asms) =
    if !tracing
    then (if not_asms then () else writeln"Assumption used in";
          pr_goal_lhs ctxt i thm; writeln"->"; pr_goal_lhs ctxt (i+n) thm';
          if n>0 then (writeln"Conditions:"; pr_goals ctxt (i, i+n-1) thm')
          else ();
          writeln"" )
    else ();

(* Skip the first n hyps of a goal, and return the rest in generalized form *)
fun strip_varify(\<^Const_>\<open>Pure.imp for H B\<close>, n, vs) =
        if n=0 then subst_bounds(vs,H)::strip_varify(B,0,vs)
        else strip_varify(B,n-1,vs)
  | strip_varify(\<^Const_>\<open>Pure.all _ for \<open>Abs(_,T,t)\<close>\<close>, n, vs) =
        strip_varify(t,n,Var(("?",length vs),T)::vs)
  | strip_varify  _  = [];

fun execute ctxt (ss,if_fl,auto_tac,cong_tac,net,i,thm) =
let

fun simp_lhs(thm,ss,anet,ats,cs) =
    if var_lhs(thm,i) then (ss,thm,anet,ats,cs) else
    if lhs_is_NORM(thm,i) then (ss, res1 ctxt (thm,trans_norms,i), anet,ats,cs)
    else case Seq.pull(cong_tac i thm) of
            SOME(thm',_) =>
                    let val ps = Thm.prems_of thm
                        and ps' = Thm.prems_of thm';
                        val n = length(ps')-length(ps);
                        val a = length(Logic.strip_assums_hyp(nth ps (i - 1)))
                        val l = map (length o Logic.strip_assums_hyp) (take n (drop (i-1) ps'));
                    in (simp_refl(rev(l),a,REW::ss),thm',anet,ats,cs) end
          | NONE => (REW::ss,thm,anet,ats,cs);

(*NB: the "Adding rewrites:" trace will look strange because assumptions
      are represented by rules, generalized over their parameters*)
fun add_asms(ss,thm,a,anet,ats,cs) =
    let val As = strip_varify(Thm.prem_of thm i, a, []);
        val thms = map (Thm.trivial o Thm.cterm_of ctxt) As;
        val new_rws = maps mk_rew_rules thms;
        val rwrls = map mk_trans (maps mk_rew_rules thms);
        val anet' = fold_rev lhs_insert_thm rwrls anet;
    in (ss,thm,anet',anet::ats,cs) end;

fun rew(seq,thm,ss,anet,ats,cs, more) = case Seq.pull seq of
      SOME(thm',seq') =>
            let val n = (Thm.nprems_of thm') - (Thm.nprems_of thm)
            in pr_rew ctxt (i,n,thm,thm',more);
               if n=0 then (SIMP_LHS::ss, thm', anet, ats, cs)
               else ((replicate n PROVE) @ (POP_CS::SIMP_LHS::ss),
                     thm', anet, ats, (ss,thm,anet,ats,seq',more)::cs)
            end
    | NONE => if more
            then rew((lhs_net_tac ctxt anet i THEN assume_tac ctxt i) thm,
                     thm,ss,anet,ats,cs,false)
            else (ss,thm,anet,ats,cs);

fun try_true(thm,ss,anet,ats,cs) =
    case Seq.pull(auto_tac ctxt i thm) of
      SOME(thm',_) => (ss,thm',anet,ats,cs)
    | NONE => let val (ss0,thm0,anet0,ats0,seq,more)::cs0 = cs
              in if !tracing
                 then (writeln"*** Failed to prove precondition. Normal form:";
                       pr_goal_concl ctxt i thm;  writeln"")
                 else ();
                 rew(seq,thm0,ss0,anet0,ats0,cs0,more)
              end;

fun if_exp(thm,ss,anet,ats,cs) =
        case Seq.pull (IF1_TAC ctxt (cong_tac i) i thm) of
                SOME(thm',_) => (SIMP_LHS::IF::ss,thm',anet,ats,cs)
              | NONE => (ss,thm,anet,ats,cs);

fun step(s::ss, thm, anet, ats, cs) = case s of
          MK_EQ => (ss, res1 ctxt (thm,[red2],i), anet, ats, cs)
        | ASMS(a) => add_asms(ss,thm,a,anet,ats,cs)
        | SIMP_LHS => simp_lhs(thm,ss,anet,ats,cs)
        | REW => rew(net_tac ctxt net i thm,thm,ss,anet,ats,cs,true)
        | REFL => (ss, res1 ctxt (thm,refl_thms,i), anet, ats, cs)
        | TRUE => try_true(res1 ctxt (thm,refl_thms,i),ss,anet,ats,cs)
        | PROVE => (if if_fl then MK_EQ::SIMP_LHS::IF::TRUE::ss
                    else MK_EQ::SIMP_LHS::TRUE::ss, thm, anet, ats, cs)
        | POP_ARTR => (ss,thm,hd ats,tl ats,cs)
        | POP_CS => (ss,thm,anet,ats,tl cs)
        | IF => if_exp(thm,ss,anet,ats,cs);

fun exec(state as (s::ss, thm, _, _, _)) =
        if s=STOP then thm else exec(step(state));

in exec(ss, thm, Net.empty, [], []) end;


fun EXEC_TAC ctxt (ss,fl) (SS{auto_tac,cong_net,simp_net,...}) =
let val cong_tac = net_tac ctxt cong_net
in fn i =>
    (fn thm =>
     if i <= 0 orelse Thm.nprems_of thm < i then Seq.empty
     else Seq.single(execute ctxt (ss,fl,auto_tac,cong_tac,simp_net,i,thm)))
    THEN TRY(auto_tac ctxt i)
end;

fun SIMP_TAC ctxt = EXEC_TAC ctxt ([MK_EQ,SIMP_LHS,REFL,STOP],false);
fun SIMP_CASE_TAC ctxt = EXEC_TAC ctxt ([MK_EQ,SIMP_LHS,IF,REFL,STOP],false);

fun ASM_SIMP_TAC ctxt = EXEC_TAC ctxt ([ASMS(0),MK_EQ,SIMP_LHS,REFL,STOP],false);
fun ASM_SIMP_CASE_TAC ctxt = EXEC_TAC ctxt ([ASMS(0),MK_EQ,SIMP_LHS,IF,REFL,STOP],false);

fun SIMP_CASE2_TAC ctxt = EXEC_TAC ctxt ([MK_EQ,SIMP_LHS,IF,REFL,STOP],true);

fun REWRITE ctxt (ss,fl) (SS{auto_tac,cong_net,simp_net,...}) =
let val cong_tac = net_tac ctxt cong_net
in fn thm => let val state = thm RSN (2,red1)
             in execute ctxt (ss,fl,auto_tac,cong_tac,simp_net,1,state) end
end;

fun SIMP_THM ctxt = REWRITE ctxt ([ASMS(0),SIMP_LHS,IF,REFL,STOP],false);


(* Compute Congruence rules for individual constants using the substition
   rules *)

val subst_thms = map Drule.export_without_context subst_thms;


fun exp_app(0,t) = t
  | exp_app(i,t) = exp_app(i-1,t $ Bound (i-1));

fun exp_abs(\<^Type>\<open>fun T1 T2\<close>,t,i) =
        Abs("x"^string_of_int i,T1,exp_abs(T2,t,i+1))
  | exp_abs(T,t,i) = exp_app(i,t);

fun eta_Var(ixn,T) = exp_abs(T,Var(ixn,T),0);


fun Pinst(f,fT,(eq,eqT),k,i,T,yik,Ts) =
let fun xn_list(x,n) =
        let val ixs = map_range (fn i => (x^(radixstring(26,"a",i)),0)) (n - 1);
        in ListPair.map eta_Var (ixs, take (n+1) Ts) end
    val lhs = list_comb(f,xn_list("X",k-1))
    val rhs = list_comb(f,xn_list("X",i-1) @ [Bound 0] @ yik)
in Abs("", T, Const(eq,[fT,fT]--->eqT) $ lhs $ rhs) end;

fun find_subst ctxt T =
let fun find (thm::thms) =
        let val (Const(_,cT), va, vb) = dest_red(Thm.prem_of thm 1);
            val [P] = subtract (op =) [va, vb] (Misc_Legacy.add_term_vars (Thm.concl_of thm, []));
            val eqT::_ = binder_types cT
        in if Sign.typ_instance (Proof_Context.theory_of ctxt) (T,eqT) then SOME(thm,va,vb,P)
           else find thms
        end
      | find [] = NONE
in find subst_thms end;

fun mk_cong ctxt (f,aTs,rT) (refl,eq) =
let val k = length aTs;
    fun ri((subst,va as Var(a,Ta),vb as Var(b,Tb), Var (P, _)),i,si,T,yik) =
        let val cx = Thm.cterm_of ctxt (eta_Var(("X"^si,0),T))
            val cb = Thm.cterm_of ctxt vb
            val cy = Thm.cterm_of ctxt (eta_Var(("Y"^si,0),T))
            val cp = Thm.cterm_of ctxt (Pinst(f,rT,eq,k,i,T,yik,aTs))
        in infer_instantiate ctxt [(a,cx),(b,cy),(P,cp)] subst end;
    fun mk(c,T::Ts,i,yik) =
        let val si = radixstring(26,"a",i)
        in case find_subst ctxt T of
             NONE => mk(c,Ts,i-1,eta_Var(("X"^si,0),T)::yik)
           | SOME s => let val c' = c RSN (2,ri(s,i,si,T,yik))
                       in mk(c',Ts,i-1,eta_Var(("Y"^si,0),T)::yik) end
        end
      | mk(c,[],_,_) = c;
in mk(refl,rev aTs,k-1,[]) end;

fun mk_cong_type ctxt (f,T) =
let val (aTs,rT) = strip_type T;
    fun find_refl(r::rs) =
        let val (Const(eq,eqT),_,_) = dest_red(Thm.concl_of r)
        in if Sign.typ_instance (Proof_Context.theory_of ctxt) (rT, hd(binder_types eqT))
           then SOME(r,(eq,body_type eqT)) else find_refl rs
        end
      | find_refl([]) = NONE;
in case find_refl refl_thms of
     NONE => []  |  SOME(refl) => [mk_cong ctxt (f,aTs,rT) refl]
end;

fun mk_congs' ctxt f =
let val T = case Sign.const_type (Proof_Context.theory_of ctxt) f of
                NONE => error(f^" not declared") | SOME(T) => T;
    val T' = Logic.incr_tvar 9 T;
in mk_cong_type ctxt (Const(f,T'),T') end;

val mk_congs = maps o mk_congs';

fun mk_typed_congs ctxt =
let
  fun readfT(f,s) =
    let
      val T = Logic.incr_tvar 9 (Syntax.read_typ ctxt s);
      val t = case Sign.const_type (Proof_Context.theory_of ctxt) f of
                  SOME(_) => Const(f,T) | NONE => Free(f,T)
    in (t,T) end
in maps (mk_cong_type ctxt o readfT) end;

end;
end;
