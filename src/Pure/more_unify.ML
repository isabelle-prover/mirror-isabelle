(*  Title:      Pure/more_unify.ML
    Author:     Makarius

Add-ons to Higher-Order Unification, outside the inference kernel.
*)

signature UNIFY =
sig
  include UNIFY
  val matchers: Context.generic -> (term * term) list -> Envir.env Seq.seq
  val matcher: Context.generic -> term list -> term list -> Envir.env option
end;

structure Unify: UNIFY =
struct

(*Pattern matching*)
fun first_order_matchers thy pairs (Envir.Envir {maxidx, tenv, tyenv}) =
  let val (tyenv', tenv') = fold (Pattern.first_order_match thy) pairs (tyenv, tenv)
  in Seq.single (Envir.Envir {maxidx = maxidx, tenv = tenv', tyenv = tyenv'}) end
  handle Pattern.MATCH => Seq.empty;

(*General matching -- keep variables disjoint*)
fun matchers _ [] = Seq.single Envir.init
  | matchers context pairs =
      let
        val thy = Context.theory_of context;

        val maxidx = fold (Term.maxidx_term o #2) pairs ~1;
        val offset = maxidx + 1;
        val pairs' = map (apfst (Logic.incr_indexes ([], offset))) pairs;
        val maxidx' = fold (fn (t, u) => Term.maxidx_term t #> Term.maxidx_term u) pairs' ~1;

        val pat_tvars = TVars.build (fold (TVars.add_tvars o #1) pairs');
        val pat_vars = Vars.build (fold (Vars.add_vars o #1) pairs');

        val decr_indexesT_same =
          Term.map_atyps_same
            (fn TVar ((x, i), S) =>
                if i > maxidx then TVar ((x, i - offset), S) else raise Same.SAME
              | _ => raise Same.SAME);
        val decr_indexesT = Same.commit decr_indexesT_same;
        val decr_indexes =
          Term.map_types decr_indexesT_same #>
          Term.map_aterms
            (fn Var ((x, i), T) =>
                if i > maxidx then Var ((x, i - offset), T) else raise Same.SAME
              | _ => raise Same.SAME);

        fun norm_tvar env ((x, i), S) =
          let
            val tyenv = Envir.type_env env;
            val T' = Envir.norm_type tyenv (TVar ((x, i), S));
          in
            if (case T' of TVar (v, _) => v = (x, i) | _ => false) then I
            else Vartab.update ((x, i - offset), (S, decr_indexesT T'))
          end;

        fun norm_var env ((x, i), T) =
          let
            val tyenv = Envir.type_env env;
            val T' = Envir.norm_type tyenv T;
            val t' = Envir.norm_term env (Var ((x, i), T'));
          in
            if (case t' of Var (v, _) => v = (x, i) | _ => false) then I
            else Vartab.update ((x, i - offset), (decr_indexesT T', decr_indexes t'))
          end;

        fun result env =
          if Envir.above env maxidx then   (* FIXME proper handling of generated vars!? *)
            SOME (Envir.Envir {maxidx = maxidx,
              tyenv = Vartab.build (TVars.fold (norm_tvar env o #1) pat_tvars),
              tenv = Vartab.build (Vars.fold (norm_var env o #1) pat_vars)})
          else NONE;

        val empty = Envir.empty maxidx';
      in
        Seq.append
          (Seq.map_filter result (Unify.smash_unifiers context pairs' empty))
          (first_order_matchers thy pairs empty)
      end;

fun matcher context ps os =
  if length ps <> length os then NONE
  else Seq.pull (matchers context (ps ~~ os)) |> Option.map #1;

open Unify;

end;
