(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_atp.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

ATPs as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_ATP =
sig
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover

  val atp_problem_dest_dir : string Config.T
  val atp_proof_dest_dir : string Config.T
  val atp_problem_prefix : string Config.T
  val atp_completish : int Config.T
  val atp_full_names : bool Config.T

  val run_atp : mode -> string -> prover
end;

structure Sledgehammer_Prover_ATP : SLEDGEHAMMER_PROVER_ATP =
struct

open ATP_Util
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover

(* Empty string means create files in Isabelle's temporary files directory. *)
val atp_problem_dest_dir =
  Attrib.setup_config_string \<^binding>\<open>sledgehammer_atp_problem_dest_dir\<close> (K "")
val atp_proof_dest_dir =
  Attrib.setup_config_string \<^binding>\<open>sledgehammer_atp_proof_dest_dir\<close> (K "")
val atp_problem_prefix =
  Attrib.setup_config_string \<^binding>\<open>sledgehammer_atp_problem_prefix\<close> (K "prob")
val atp_completish = Attrib.setup_config_int \<^binding>\<open>sledgehammer_atp_completish\<close> (K 0)
(* In addition to being easier to read, readable names are often much shorter, especially if types
   are mangled in names. This makes a difference for some provers (e.g., E). For these reason, short
   names are enabled by default. *)
val atp_full_names = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_atp_full_names\<close> (K false)

fun choose_type_enc strictness format good_type_enc =
  type_enc_of_string strictness good_type_enc
  |> adjust_type_enc format

fun has_bound_or_var_of_type pred =
  exists_subterm (fn Var (_, T as Type _) => pred T
                   | Abs (_, T as Type _, _) => pred T
                   | _ => false)

(* Unwanted equalities are those between a (bound or schematic) variable that does not properly
   occur in the second operand. *)
val is_exhaustive_finite =
  let
    fun is_bad_equal (Var z) t =
        not (exists_subterm (fn Var z' => z = z' | _ => false) t)
      | is_bad_equal (Bound j) t = not (loose_bvar1 (t, j))
      | is_bad_equal _ _ = false
    fun do_equals t1 t2 = is_bad_equal t1 t2 orelse is_bad_equal t2 t1
    fun do_formula pos t =
      (case (pos, t) of
        (_, \<^Const_>\<open>Trueprop for t1\<close>) => do_formula pos t1
      | (true, Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, t')) => do_formula pos t'
      | (true, Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t')) => do_formula pos t'
      | (false, Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, t')) => do_formula pos t'
      | (_, \<^Const_>\<open>Pure.imp for t1 t2\<close>) =>
        do_formula (not pos) t1 andalso (t2 = \<^prop>\<open>False\<close> orelse do_formula pos t2)
      | (_, \<^Const_>\<open>implies for t1 t2\<close>) =>
        do_formula (not pos) t1 andalso (t2 = \<^Const>\<open>False\<close> orelse do_formula pos t2)
      | (_, \<^Const_>\<open>Not for t1\<close>) => do_formula (not pos) t1
      | (true, \<^Const_>\<open>disj for t1 t2\<close>) => forall (do_formula pos) [t1, t2]
      | (false, \<^Const_>\<open>conj for t1 t2\<close>) => forall (do_formula pos) [t1, t2]
      | (true, Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2) => do_equals t1 t2
      | (true, Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t1 $ t2) => do_equals t1 t2
      | _ => false)
  in do_formula true end

(* Facts containing variables of finite types such as "unit" or "bool" or of the form
   "ALL x. x = A | x = B | x = C" are likely to lead to untypable proofs for unsound type
   encodings. *)
fun is_dangerous_prop ctxt =
  transform_elim_prop
  #> (has_bound_or_var_of_type (is_type_surely_finite ctxt) orf is_exhaustive_finite)

val mono_max_privileged_facts = 10

fun suffix_of_mode Auto_Try = "_try"
  | suffix_of_mode Try = "_try"
  | suffix_of_mode Normal = ""
  | suffix_of_mode MaSh = ""
  | suffix_of_mode Minimize = "_min"

fun run_atp mode name
    ({debug, verbose, overlord, abduce = abduce_max_candidates, strict, max_mono_iters,
      max_new_mono_instances, isar_proofs, compress, try0, smt_proofs, minimize, slices, timeout,
      preplay_timeout, spy, ...} : params)
    ({comment, state, goal, subgoal, subgoal_count, factss, has_already_found_something,
      found_something} : prover_problem)
    slice =
  let
    val (basic_slice as (slice_size, abduce, _, _, _),
        ATP_Slice (good_format, good_type_enc, good_lam_trans, good_uncurried_aliases, extra)) =
      slice
    val facts = facts_of_basic_slice basic_slice factss
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val {exec, arguments, proof_delims, known_failures, prem_role, generate_isabelle_info,
      good_max_mono_iters, good_max_new_mono_instances, ...} = get_atp thy name ()

    val full_proofs = isar_proofs |> the_default (mode = Minimize)
    val local_name = perhaps (try (unprefix remote_prefix)) name

    val completish = Config.get ctxt atp_completish
    val atp_mode = if completish > 0 then Sledgehammer_Completish completish else Sledgehammer
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal ctxt
    val (problem_dest_dir, proof_dest_dir, problem_prefix) =
      if overlord then
        overlord_file_location_of_prover name
        |> (fn (dir, prefix) => (dir, dir, prefix))
      else
        (Config.get ctxt atp_problem_dest_dir,
         Config.get ctxt atp_proof_dest_dir,
         Config.get ctxt atp_problem_prefix)
    val problem_file_name =
      Path.basic (problem_prefix ^ (if overlord then "" else serial_string ()) ^
        suffix_of_mode mode ^ "_" ^ string_of_int subgoal)
      |> Path.ext "p"
    val prob_path =
      if problem_dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode problem_dest_dir) then
        Path.explode problem_dest_dir + problem_file_name
      else
        error ("No such directory: " ^ quote problem_dest_dir)
    val executable =
      (case find_first (fn var => getenv var <> "") (fst exec) of
        SOME var =>
        let
          val pref = getenv var ^ "/"
          val paths =
            map (Path.explode o prefix pref)
              (if ML_System.platform_is_windows then
                map (suffix ".exe") (snd exec) @ snd exec
               else snd exec);
        in
          (case find_first File.exists paths of
            SOME path => path
          | NONE => error ("Bad executable: " ^ Path.print (hd paths)))
        end
      | NONE => error ("The environment variable " ^ quote (List.last (fst exec)) ^ " is not set"))

    fun run () =
      let
        fun monomorphize_facts facts =
          let
            val ctxt =
              ctxt
              |> repair_monomorph_context max_mono_iters good_max_mono_iters max_new_mono_instances
                   good_max_new_mono_instances
            (* pseudo-theorem involving the same constants as the subgoal *)
            val subgoal_th =
              Logic.list_implies (hyp_ts, concl_t) |> Skip_Proof.make_thm thy
            val rths =
              facts |> chop mono_max_privileged_facts
                    |>> map (pair 1 o snd)
                    ||> map (pair 2 o snd)
                    |> op @
                    |> cons (0, subgoal_th)
          in
            Monomorph.monomorph atp_schematic_consts_of ctxt rths
            |> tl |> curry ListPair.zip (map fst facts)
            |> maps (fn (name, rths) => map (pair name o zero_var_indexes o snd) rths)
          end

        val strictness = if strict then Strict else Non_Strict
        val type_enc = choose_type_enc strictness good_format good_type_enc
        val run_timeout = slice_timeout slice_size slices timeout
        val generous_run_timeout =
          if mode = MaSh then one_day
          else if abduce then run_timeout + seconds 5.0
          else run_timeout
        val ({elapsed, ...}, atp_problem_data as (atp_problem, _, _, _)) = Timing.timing (fn () =>
          let val readable_names = not (Config.get ctxt atp_full_names) in
            facts
            |> not (is_type_enc_sound type_enc) ?
              filter_out (is_dangerous_prop ctxt o Thm.prop_of o snd)
            |> not (is_type_enc_polymorphic type_enc) ? monomorphize_facts
            |> map (apsnd Thm.prop_of)
            |> generate_atp_problem ctxt generate_isabelle_info good_format prem_role type_enc
              atp_mode good_lam_trans good_uncurried_aliases readable_names true hyp_ts concl_t
          end) ()

        val () = spying spy (fn () =>
          (state, subgoal, name, "Generating ATP problem in " ^
             string_of_int (Time.toMilliseconds elapsed) ^ " ms"))

        val args = arguments abduce full_proofs extra run_timeout prob_path
        val command = implode_space (File.bash_path executable :: args)

        fun run_command () =
          if exec = isabelle_scala_function then
            let val {output, timing} = SystemOnTPTP.run_system_encoded args
            in (output, timing) end
          else
            let val res = Isabelle_System.bash_process (Bash.script command |> Bash.redirect)
            in (Process_Result.out res, Process_Result.timing_elapsed res) end

        val _ = atp_problem
          |> lines_of_atp_problem good_format (fn () => atp_problem_term_order_info atp_problem)
          |> (exec <> isabelle_scala_function) ?
            cons ("% " ^ command ^ "\n" ^ (if comment = "" then "" else "% " ^ comment ^ "\n"))
          |> File.write_list prob_path

        val local_name = name |> perhaps (try (unprefix remote_prefix))

        val ((output, run_time), ((atp_proof, tstplike_proof), outcome)) =
          Timeout.apply generous_run_timeout run_command ()
          |>> overlord ?
            (fn output => prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n") output)
          |> (fn accum as (output, _) =>
            (accum,
             extract_tstplike_proof_and_outcome verbose proof_delims known_failures output
             |>> `(atp_proof_of_tstplike_proof false local_name atp_problem)
             handle UNRECOGNIZED_ATP_PROOF () => (([], ""), SOME ProofUnparsable)))
          handle Timeout.TIMEOUT _ => (("", run_timeout), (([], ""), SOME TimedOut))
            | ERROR msg => (("", Time.zeroTime), (([], ""), SOME (UnknownError msg)))

        val atp_abduce_candidates =
          if abduce andalso outcome <> NONE andalso not (has_already_found_something ()) then
            atp_abduce_candidates_of_output local_name atp_problem output
          else
            []

        val () = spying spy (fn () =>
          (state, subgoal, name, "Running command in " ^
             string_of_int (Time.toMilliseconds run_time) ^ " ms"))

        val outcome =
          (case outcome of
            NONE => (found_something name; NONE)
          | _ => outcome)
      in
        (atp_problem_data,
         (output, run_time, facts, atp_problem, tstplike_proof, atp_proof, atp_abduce_candidates,
          outcome),
         (good_format, type_enc))
      end

    (* If the problem file has not been exported, remove it; otherwise, export the proof file
       too. *)
    fun clean_up () = if problem_dest_dir = "" then (try File.rm prob_path; ()) else ()
    fun export (_, (output, _, _, _, _, _, _, _), _) =
      let
        val proof_dest_dir_path = Path.explode proof_dest_dir
        val make_export_file_name =
          Path.split_ext
          #> apfst (Path.explode o suffix "_proof" o Path.implode)
          #> swap
          #> uncurry Path.ext
      in
        if proof_dest_dir = "" then
          Output.system_message "don't export proof"
        else if File.exists proof_dest_dir_path then
          File.write (proof_dest_dir_path + make_export_file_name problem_file_name) output
        else
          error ("No such directory: " ^ quote proof_dest_dir)
      end

    val ((_, pool, lifted, sym_tab),
         (_, run_time, used_from, atp_problem, tstplike_proof, atp_proof,
          atp_abduce_candidates, outcome),
         (format, type_enc)) =
      \<^try>\<open>run () finally clean_up ()\<close> |> tap export

    val (outcome, used_facts, preferred_methss, message) =
      (case outcome of
        NONE =>
        let
          val used_facts = sort_by fst (used_facts_in_atp_proof ctxt (map fst used_from) atp_proof)
          val _ =
            if mode = Normal andalso not (is_conjecture_used_in_proof atp_proof)
               andalso not (Logic.get_goal (Thm.prop_of goal) subgoal aconv @{prop False}) then
              warning ("Derived \"False\" from these facts alone: " ^
                implode_space (map fst used_facts))
            else
              ()

          val needs_full_types = is_typed_helper_used_in_atp_proof atp_proof
          val preferred = Metis_Method (NONE, NONE)
          val preferred_methss =
            (preferred,
             if try0 then
               bunches_of_proof_methods ctxt smt_proofs needs_full_types
                 (if atp_proof_prefers_lifting atp_proof then liftingN else opaque_liftingN)
             else
               [[preferred]])
        in
          (NONE, used_facts, preferred_methss,
           fn preplay =>
              let
                val _ = if verbose then writeln "Generating proof text..." else ()

                fun isar_params () =
                  let
                    val full_atp_proof =
                      atp_proof_of_tstplike_proof true (perhaps (try (unprefix remote_prefix)) name)
                        atp_problem tstplike_proof
                    val metis_type_enc =
                      if is_typed_helper_used_in_atp_proof full_atp_proof then
                        SOME full_typesN
                      else
                        NONE
                    val metis_lam_trans =
                      if atp_proof_prefers_lifting full_atp_proof then SOME liftingN else NONE
                    val full_atp_proof =
                      full_atp_proof
                      |> termify_atp_proof ctxt name format type_enc pool lifted sym_tab
                      |> local_name = spassN ? introduce_spass_skolems
                      |> local_name = zipperpositionN ? regroup_zipperposition_skolems
                      |> factify_atp_proof (map fst used_from) hyp_ts concl_t
                  in
                    (verbose, (metis_type_enc, metis_lam_trans), preplay_timeout, compress, try0,
                     minimize, full_atp_proof, goal)
                  end

                val one_line_params = (preplay (), proof_banner mode name, subgoal, subgoal_count)
                val num_chained = length (#facts (Proof.goal state))
              in
                proof_text ctxt debug isar_proofs smt_proofs isar_params num_chained
                  one_line_params
              end)
        end
      | SOME failure =>
        let
          val max_abduce_candidates_factor = 3 (* FUDGE *)
          val max_abduce_candidates =
            the_default default_abduce_max_candidates abduce_max_candidates
          val abduce_candidates = atp_abduce_candidates
            |> map (termify_atp_abduce_candidate ctxt name format type_enc pool lifted sym_tab)
            |> top_abduce_candidates (max_abduce_candidates * max_abduce_candidates_factor)
            |> sort_propositions_by_provability ctxt
            |> take max_abduce_candidates
        in
          if null abduce_candidates then
            (SOME failure, [], (Auto_Method (* dummy *), []), fn _ => string_of_atp_failure failure)
          else
            (NONE, [], (Auto_Method (* dummy *), []), fn _ =>
               abduce_text ctxt abduce_candidates)
        end)
  in
    {outcome = outcome, used_facts = used_facts, used_from = used_from,
     preferred_methss = preferred_methss, run_time = run_time, message = message}
  end

end;
