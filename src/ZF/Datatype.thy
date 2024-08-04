(*  Title:      ZF/Datatype.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

section\<open>Datatype and CoDatatype Definitions\<close>

theory Datatype
imports Inductive Univ QUniv
keywords "datatype" "codatatype" :: thy_decl
begin

ML_file \<open>Tools/datatype_package.ML\<close>

ML \<open>
(*Typechecking rules for most datatypes involving univ*)
structure Data_Arg =
  struct
  val intrs =
      [@{thm SigmaI}, @{thm InlI}, @{thm InrI},
       @{thm Pair_in_univ}, @{thm Inl_in_univ}, @{thm Inr_in_univ},
       @{thm zero_in_univ}, @{thm A_into_univ}, @{thm nat_into_univ}, @{thm UnCI}];


  val elims = [make_elim @{thm InlD}, make_elim @{thm InrD},   (*for mutual recursion*)
               @{thm SigmaE}, @{thm sumE}];                    (*allows * and + in spec*)
  end;


structure Data_Package =
  Add_datatype_def_Fun
   (structure Fp=Lfp and Pr=Standard_Prod and CP=Standard_CP
    and Su=Standard_Sum
    and Ind_Package = Ind_Package
    and Datatype_Arg = Data_Arg
    val coind = false);


(*Typechecking rules for most codatatypes involving quniv*)
structure CoData_Arg =
  struct
  val intrs =
      [@{thm QSigmaI}, @{thm QInlI}, @{thm QInrI},
       @{thm QPair_in_quniv}, @{thm QInl_in_quniv}, @{thm QInr_in_quniv},
       @{thm zero_in_quniv}, @{thm A_into_quniv}, @{thm nat_into_quniv}, @{thm UnCI}];

  val elims = [make_elim @{thm QInlD}, make_elim @{thm QInrD},   (*for mutual recursion*)
               @{thm QSigmaE}, @{thm qsumE}];                    (*allows * and + in spec*)
  end;

structure CoData_Package =
  Add_datatype_def_Fun
   (structure Fp=Gfp and Pr=Quine_Prod and CP=Quine_CP
    and Su=Quine_Sum
    and Ind_Package = CoInd_Package
    and Datatype_Arg = CoData_Arg
    val coind = true);



(* Simproc for freeness reasoning: compare datatype constructors for equality *)

structure Data_Free:
sig
  val trace: bool Config.T
  val proc: Simplifier.proc
end =
struct

val trace = Attrib.setup_config_bool \<^binding>\<open>data_free_trace\<close> (K false);

fun mk_new ([],[]) = \<^Const>\<open>True\<close>
  | mk_new (largs,rargs) =
      Balanced_Tree.make FOLogic.mk_conj
                 (map FOLogic.mk_eq (ListPair.zip (largs,rargs)));

val datatype_ss = simpset_of \<^context>;

fun proc ctxt ct =
  let
    val old = Thm.term_of ct
    val thy = Proof_Context.theory_of ctxt
    val _ =
      if Config.get ctxt trace then tracing ("data_free: OLD = " ^ Syntax.string_of_term ctxt old)
      else ()
    val (lhs,rhs) = FOLogic.dest_eq old
    val (lhead, largs) = strip_comb lhs
    and (rhead, rargs) = strip_comb rhs
    val lname = dest_Const_name lhead handle TERM _ => raise Match;
    val rname = dest_Const_name rhead handle TERM _ => raise Match;
    val lcon_info = the (Symtab.lookup (ConstructorsData.get thy) lname)
      handle Option.Option => raise Match;
    val rcon_info = the (Symtab.lookup (ConstructorsData.get thy) rname)
      handle Option.Option => raise Match;
    val new =
      if #big_rec_name lcon_info = #big_rec_name rcon_info
          andalso not (null (#free_iffs lcon_info)) then
        if lname = rname then mk_new (largs, rargs)
        else \<^Const>\<open>False\<close>
      else raise Match;
     val _ =
       if Config.get ctxt trace then tracing ("NEW = " ^ Syntax.string_of_term ctxt new)
       else ();
     val goal = Logic.mk_equals (old, new);
     val thm = Goal.prove ctxt [] [] goal
       (fn _ => resolve_tac ctxt @{thms iff_reflection} 1 THEN
         simp_tac (put_simpset datatype_ss ctxt addsimps
          (map (Thm.transfer thy) (#free_iffs lcon_info))) 1)
       handle ERROR msg =>
       (warning (msg ^ "\ndata_free simproc:\nfailed to prove " ^ Syntax.string_of_term ctxt goal);
        raise Match)
  in SOME thm end
  handle Match => NONE;

end;
\<close>

simproc_setup data_free ("(x::i) = y") = \<open>fn _ => Data_Free.proc\<close>

end
