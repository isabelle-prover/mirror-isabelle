theory HOL_Specific
imports
  Base
  "~~/src/HOL/Library/Old_Datatype"
  "~~/src/HOL/Library/Old_Recdef"
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Dlist"
  "~~/src/HOL/Library/FSet"
begin


chapter \<open>Higher-Order Logic\<close>

text \<open>Isabelle/HOL is based on Higher-Order Logic, a polymorphic
  version of Church's Simple Theory of Types.  HOL can be best
  understood as a simply-typed version of classical set theory.  The
  logic was first implemented in Gordon's HOL system
  @{cite "mgordon-hol"}.  It extends Church's original logic
  @{cite "church40"} by explicit type variables (naive polymorphism) and
  a sound axiomatization scheme for new types based on subsets of
  existing types.

  Andrews's book @{cite andrews86} is a full description of the
  original Church-style higher-order logic, with proofs of correctness
  and completeness wrt.\ certain set-theoretic interpretations.  The
  particular extensions of Gordon-style HOL are explained semantically
  in two chapters of the 1993 HOL book @{cite pitts93}.

  Experience with HOL over decades has demonstrated that higher-order
  logic is widely applicable in many areas of mathematics and computer
  science.  In a sense, Higher-Order Logic is simpler than First-Order
  Logic, because there are fewer restrictions and special cases.  Note
  that HOL is \<^emph>\<open>weaker\<close> than FOL with axioms for ZF set theory,
  which is traditionally considered the standard foundation of regular
  mathematics, but for most applications this does not matter.  If you
  prefer ML to Lisp, you will probably prefer HOL to ZF.

  \<^medskip>
  The syntax of HOL follows @{text "\<lambda>"}-calculus and
  functional programming.  Function application is curried.  To apply
  the function @{text f} of type @{text "\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2 \<Rightarrow> \<tau>\<^sub>3"} to the
  arguments @{text a} and @{text b} in HOL, you simply write @{text "f
  a b"} (as in ML or Haskell).  There is no ``apply'' operator; the
  existing application of the Pure @{text "\<lambda>"}-calculus is re-used.
  Note that in HOL @{text "f (a, b)"} means ``@{text "f"} applied to
  the pair @{text "(a, b)"} (which is notation for @{text "Pair a
  b"}).  The latter typically introduces extra formal efforts that can
  be avoided by currying functions by default.  Explicit tuples are as
  infrequent in HOL formalizations as in good ML or Haskell programs.

  \<^medskip>
  Isabelle/HOL has a distinct feel, compared to other
  object-logics like Isabelle/ZF.  It identifies object-level types
  with meta-level types, taking advantage of the default
  type-inference mechanism of Isabelle/Pure.  HOL fully identifies
  object-level functions with meta-level functions, with native
  abstraction and application.

  These identifications allow Isabelle to support HOL particularly
  nicely, but they also mean that HOL requires some sophistication
  from the user.  In particular, an understanding of Hindley-Milner
  type-inference with type-classes, which are both used extensively in
  the standard libraries and applications.\<close>


chapter \<open>Derived specification elements\<close>

section \<open>Inductive and coinductive definitions \label{sec:hol-inductive}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "inductive"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "inductive_set"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "coinductive"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "coinductive_set"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_inductives"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) mono} & : & @{text attribute} \\
  \end{matharray}

  An \<^emph>\<open>inductive definition\<close> specifies the least predicate or set
  @{text R} closed under given rules: applying a rule to elements of
  @{text R} yields a result within @{text R}.  For example, a
  structural operational semantics is an inductive definition of an
  evaluation relation.

  Dually, a \<^emph>\<open>coinductive definition\<close> specifies the greatest
  predicate or set @{text R} that is consistent with given rules:
  every element of @{text R} can be seen as arising by applying a rule
  to elements of @{text R}.  An important example is using
  bisimulation relations to formalise equivalence of processes and
  infinite data structures.

  Both inductive and coinductive definitions are based on the
  Knaster-Tarski fixed-point theorem for complete lattices.  The
  collection of introduction rules given by the user determines a
  functor on subsets of set-theoretic relations.  The required
  monotonicity of the recursion scheme is proven as a prerequisite to
  the fixed-point definition and the resulting consequences.  This
  works by pushing inclusion through logical connectives and any other
  operator that might be wrapped around recursive occurrences of the
  defined relation: there must be a monotonicity theorem of the form
  @{text "A \<le> B \<Longrightarrow> \<M> A \<le> \<M> B"}, for each premise @{text "\<M> R t"} in an
  introduction rule.  The default rule declarations of Isabelle/HOL
  already take care of most common situations.

  @{rail \<open>
    (@@{command (HOL) inductive} | @@{command (HOL) inductive_set} |
      @@{command (HOL) coinductive} | @@{command (HOL) coinductive_set})
      @{syntax "fixes"} @{syntax "for_fixes"} \<newline>
      (@'where' clauses)? (@'monos' @{syntax thmrefs})?
    ;
    clauses: (@{syntax thmdecl}? @{syntax prop} + '|')
    ;
    @@{command print_inductives} ('!'?)
    ;
    @@{attribute (HOL) mono} (() | 'add' | 'del')
  \<close>}

  \<^descr> @{command (HOL) "inductive"} and @{command (HOL)
  "coinductive"} define (co)inductive predicates from the introduction
  rules.

  The propositions given as @{text "clauses"} in the @{keyword
  "where"} part are either rules of the usual @{text "\<And>/\<Longrightarrow>"} format
  (with arbitrary nesting), or equalities using @{text "\<equiv>"}.  The
  latter specifies extra-logical abbreviations in the sense of
  @{command_ref abbreviation}.  Introducing abstract syntax
  simultaneously with the actual introduction rules is occasionally
  useful for complex specifications.

  The optional @{keyword "for"} part contains a list of parameters of
  the (co)inductive predicates that remain fixed throughout the
  definition, in contrast to arguments of the relation that may vary
  in each occurrence within the given @{text "clauses"}.

  The optional @{keyword "monos"} declaration contains additional
  \<^emph>\<open>monotonicity theorems\<close>, which are required for each operator
  applied to a recursive set in the introduction rules.

  \<^descr> @{command (HOL) "inductive_set"} and @{command (HOL)
  "coinductive_set"} are wrappers for to the previous commands for
  native HOL predicates.  This allows to define (co)inductive sets,
  where multiple arguments are simulated via tuples.

  \<^descr> @{command "print_inductives"} prints (co)inductive definitions and
  monotonicity rules; the ``@{text "!"}'' option indicates extra verbosity.

  \<^descr> @{attribute (HOL) mono} declares monotonicity rules in the
  context.  These rule are involved in the automated monotonicity
  proof of the above inductive and coinductive definitions.
\<close>


subsection \<open>Derived rules\<close>

text \<open>A (co)inductive definition of @{text R} provides the following
  main theorems:

  \<^descr> @{text R.intros} is the list of introduction rules as proven
  theorems, for the recursive predicates (or sets).  The rules are
  also available individually, using the names given them in the
  theory file;

  \<^descr> @{text R.cases} is the case analysis (or elimination) rule;

  \<^descr> @{text R.induct} or @{text R.coinduct} is the (co)induction
  rule;

  \<^descr> @{text R.simps} is the equation unrolling the fixpoint of the
  predicate one step.


  When several predicates @{text "R\<^sub>1, \<dots>, R\<^sub>n"} are defined simultaneously,
  the list of introduction rules is called @{text "R\<^sub>1_\<dots>_R\<^sub>n.intros"}, the
  case analysis rules are called @{text "R\<^sub>1.cases, \<dots>, R\<^sub>n.cases"}, and the
  list of mutual induction rules is called @{text "R\<^sub>1_\<dots>_R\<^sub>n.inducts"}.
\<close>


subsection \<open>Monotonicity theorems\<close>

text \<open>The context maintains a default set of theorems that are used
  in monotonicity proofs.  New rules can be declared via the
  @{attribute (HOL) mono} attribute.  See the main Isabelle/HOL
  sources for some examples.  The general format of such monotonicity
  theorems is as follows:

  \<^item> Theorems of the form @{text "A \<le> B \<Longrightarrow> \<M> A \<le> \<M> B"}, for proving
  monotonicity of inductive definitions whose introduction rules have
  premises involving terms such as @{text "\<M> R t"}.

  \<^item> Monotonicity theorems for logical operators, which are of the
  general form @{text "(\<dots> \<longrightarrow> \<dots>) \<Longrightarrow> \<dots> (\<dots> \<longrightarrow> \<dots>) \<Longrightarrow> \<dots> \<longrightarrow> \<dots>"}.  For example, in
  the case of the operator @{text "\<or>"}, the corresponding theorem is
  \[
  \infer{@{text "P\<^sub>1 \<or> P\<^sub>2 \<longrightarrow> Q\<^sub>1 \<or> Q\<^sub>2"}}{@{text "P\<^sub>1 \<longrightarrow> Q\<^sub>1"} & @{text "P\<^sub>2 \<longrightarrow> Q\<^sub>2"}}
  \]

  \<^item> De Morgan style equations for reasoning about the ``polarity''
  of expressions, e.g.
  \[
  @{prop "\<not> \<not> P \<longleftrightarrow> P"} \qquad\qquad
  @{prop "\<not> (P \<and> Q) \<longleftrightarrow> \<not> P \<or> \<not> Q"}
  \]

  \<^item> Equations for reducing complex operators to more primitive
  ones whose monotonicity can easily be proved, e.g.
  \[
  @{prop "(P \<longrightarrow> Q) \<longleftrightarrow> \<not> P \<or> Q"} \qquad\qquad
  @{prop "Ball A P \<equiv> \<forall>x. x \<in> A \<longrightarrow> P x"}
  \]
\<close>

subsubsection \<open>Examples\<close>

text \<open>The finite powerset operator can be defined inductively like this:\<close>

(*<*)experiment begin(*>*)
inductive_set Fin :: "'a set \<Rightarrow> 'a set set" for A :: "'a set"
where
  empty: "{} \<in> Fin A"
| insert: "a \<in> A \<Longrightarrow> B \<in> Fin A \<Longrightarrow> insert a B \<in> Fin A"

text \<open>The accessible part of a relation is defined as follows:\<close>

inductive acc :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<prec>" 50)
where acc: "(\<And>y. y \<prec> x \<Longrightarrow> acc r y) \<Longrightarrow> acc r x"
(*<*)end(*>*)

text \<open>Common logical connectives can be easily characterized as
  non-recursive inductive definitions with parameters, but without
  arguments.\<close>

(*<*)experiment begin(*>*)
inductive AND for A B :: bool
where "A \<Longrightarrow> B \<Longrightarrow> AND A B"

inductive OR for A B :: bool
where "A \<Longrightarrow> OR A B"
  | "B \<Longrightarrow> OR A B"

inductive EXISTS for B :: "'a \<Rightarrow> bool"
where "B a \<Longrightarrow> EXISTS B"
(*<*)end(*>*)

text \<open>Here the @{text "cases"} or @{text "induct"} rules produced by the
  @{command inductive} package coincide with the expected elimination rules
  for Natural Deduction. Already in the original article by Gerhard Gentzen
  @{cite "Gentzen:1935"} there is a hint that each connective can be
  characterized by its introductions, and the elimination can be constructed
  systematically.\<close>


section \<open>Recursive functions \label{sec:recursion}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "primrec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "fun"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "function"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def (HOL) "termination"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def (HOL) "fun_cases"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) primrec} @{syntax "fixes"} @'where' equations
    ;
    (@@{command (HOL) fun} | @@{command (HOL) function}) functionopts?
      @{syntax "fixes"} \<newline> @'where' equations
    ;

    equations: (@{syntax thmdecl}? @{syntax prop} + '|')
    ;
    functionopts: '(' (('sequential' | 'domintros') + ',') ')'
    ;
    @@{command (HOL) termination} @{syntax term}?
    ;
    @@{command (HOL) fun_cases} (@{syntax thmdecl}? @{syntax prop} + @'and')
  \<close>}

  \<^descr> @{command (HOL) "primrec"} defines primitive recursive functions
  over datatypes (see also @{command_ref (HOL) datatype}). The given @{text
  equations} specify reduction rules that are produced by instantiating the
  generic combinator for primitive recursion that is available for each
  datatype.

  Each equation needs to be of the form:

  @{text [display] "f x\<^sub>1 \<dots> x\<^sub>m (C y\<^sub>1 \<dots> y\<^sub>k) z\<^sub>1 \<dots> z\<^sub>n = rhs"}

  such that @{text C} is a datatype constructor, @{text rhs} contains only
  the free variables on the left-hand side (or from the context), and all
  recursive occurrences of @{text "f"} in @{text "rhs"} are of the form
  @{text "f \<dots> y\<^sub>i \<dots>"} for some @{text i}. At most one reduction rule for
  each constructor can be given. The order does not matter. For missing
  constructors, the function is defined to return a default value, but this
  equation is made difficult to access for users.

  The reduction rules are declared as @{attribute simp} by default, which
  enables standard proof methods like @{method simp} and @{method auto} to
  normalize expressions of @{text "f"} applied to datatype constructions, by
  simulating symbolic computation via rewriting.

  \<^descr> @{command (HOL) "function"} defines functions by general wellfounded
  recursion. A detailed description with examples can be found in @{cite
  "isabelle-function"}. The function is specified by a set of (possibly
  conditional) recursive equations with arbitrary pattern matching. The
  command generates proof obligations for the completeness and the
  compatibility of patterns.

  The defined function is considered partial, and the resulting
  simplification rules (named @{text "f.psimps"}) and induction rule (named
  @{text "f.pinduct"}) are guarded by a generated domain predicate @{text
  "f_dom"}. The @{command (HOL) "termination"} command can then be used to
  establish that the function is total.

  \<^descr> @{command (HOL) "fun"} is a shorthand notation for ``@{command (HOL)
  "function"}~@{text "(sequential)"}'', followed by automated proof attempts
  regarding pattern matching and termination. See @{cite
  "isabelle-function"} for further details.

  \<^descr> @{command (HOL) "termination"}~@{text f} commences a termination
  proof for the previously defined function @{text f}. If this is omitted,
  the command refers to the most recent function definition. After the proof
  is closed, the recursive equations and the induction principle is
  established.

  \<^descr> @{command (HOL) "fun_cases"} generates specialized elimination rules
  for function equations. It expects one or more function equations and
  produces rules that eliminate the given equalities, following the cases
  given in the function definition.


  Recursive definitions introduced by the @{command (HOL) "function"}
  command accommodate reasoning by induction (cf.\ @{method induct}): rule
  @{text "f.induct"} refers to a specific induction rule, with parameters
  named according to the user-specified equations. Cases are numbered
  starting from 1. For @{command (HOL) "primrec"}, the induction principle
  coincides with structural recursion on the datatype where the recursion is
  carried out.

  The equations provided by these packages may be referred later as theorem
  list @{text "f.simps"}, where @{text f} is the (collective) name of the
  functions defined. Individual equations may be named explicitly as well.

  The @{command (HOL) "function"} command accepts the following options.

  \<^descr> @{text sequential} enables a preprocessor which disambiguates
  overlapping patterns by making them mutually disjoint. Earlier equations
  take precedence over later ones. This allows to give the specification in
  a format very similar to functional programming. Note that the resulting
  simplification and induction rules correspond to the transformed
  specification, not the one given originally. This usually means that each
  equation given by the user may result in several theorems. Also note that
  this automatic transformation only works for ML-style datatype patterns.

  \<^descr> @{text domintros} enables the automated generation of introduction
  rules for the domain predicate. While mostly not needed, they can be
  helpful in some proofs about partial functions.
\<close>


subsubsection \<open>Example: evaluation of expressions\<close>

text \<open>Subsequently, we define mutual datatypes for arithmetic and boolean
  expressions, and use @{command primrec} for evaluation functions that
  follow the same recursive structure.\<close>

(*<*)experiment begin(*>*)
datatype 'a aexp =
    IF "'a bexp"  "'a aexp"  "'a aexp"
  | Sum "'a aexp"  "'a aexp"
  | Diff "'a aexp"  "'a aexp"
  | Var 'a
  | Num nat
and 'a bexp =
    Less "'a aexp"  "'a aexp"
  | And "'a bexp"  "'a bexp"
  | Neg "'a bexp"

text \<open>\<^medskip> Evaluation of arithmetic and boolean expressions\<close>

primrec evala :: "('a \<Rightarrow> nat) \<Rightarrow> 'a aexp \<Rightarrow> nat"
  and evalb :: "('a \<Rightarrow> nat) \<Rightarrow> 'a bexp \<Rightarrow> bool"
where
  "evala env (IF b a1 a2) = (if evalb env b then evala env a1 else evala env a2)"
| "evala env (Sum a1 a2) = evala env a1 + evala env a2"
| "evala env (Diff a1 a2) = evala env a1 - evala env a2"
| "evala env (Var v) = env v"
| "evala env (Num n) = n"
| "evalb env (Less a1 a2) = (evala env a1 < evala env a2)"
| "evalb env (And b1 b2) = (evalb env b1 \<and> evalb env b2)"
| "evalb env (Neg b) = (\<not> evalb env b)"

text \<open>Since the value of an expression depends on the value of its
  variables, the functions @{const evala} and @{const evalb} take an
  additional parameter, an \<^emph>\<open>environment\<close> that maps variables to their
  values.

  \<^medskip>
  Substitution on expressions can be defined similarly. The mapping
  @{text f} of type @{typ "'a \<Rightarrow> 'a aexp"} given as a parameter is lifted
  canonically on the types @{typ "'a aexp"} and @{typ "'a bexp"},
  respectively.
\<close>

primrec substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp"
  and substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp"
where
  "substa f (IF b a1 a2) = IF (substb f b) (substa f a1) (substa f a2)"
| "substa f (Sum a1 a2) = Sum (substa f a1) (substa f a2)"
| "substa f (Diff a1 a2) = Diff (substa f a1) (substa f a2)"
| "substa f (Var v) = f v"
| "substa f (Num n) = Num n"
| "substb f (Less a1 a2) = Less (substa f a1) (substa f a2)"
| "substb f (And b1 b2) = And (substb f b1) (substb f b2)"
| "substb f (Neg b) = Neg (substb f b)"

text \<open>In textbooks about semantics one often finds substitution theorems,
  which express the relationship between substitution and evaluation. For
  @{typ "'a aexp"} and @{typ "'a bexp"}, we can prove such a theorem by
  mutual induction, followed by simplification.
\<close>

lemma subst_one:
  "evala env (substa (Var (v := a')) a) = evala (env (v := evala env a')) a"
  "evalb env (substb (Var (v := a')) b) = evalb (env (v := evala env a')) b"
  by (induct a and b) simp_all

lemma subst_all:
  "evala env (substa s a) = evala (\<lambda>x. evala env (s x)) a"
  "evalb env (substb s b) = evalb (\<lambda>x. evala env (s x)) b"
  by (induct a and b) simp_all
(*<*)end(*>*)


subsubsection \<open>Example: a substitution function for terms\<close>

text \<open>Functions on datatypes with nested recursion are also defined
  by mutual primitive recursion.\<close>

(*<*)experiment begin(*>*)
datatype ('a, 'b) "term" = Var 'a | App 'b "('a, 'b) term list"

text \<open>A substitution function on type @{typ "('a, 'b) term"} can be
  defined as follows, by working simultaneously on @{typ "('a, 'b)
  term list"}:\<close>

primrec subst_term :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term" and
  subst_term_list :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term list \<Rightarrow> ('a, 'b) term list"
where
  "subst_term f (Var a) = f a"
| "subst_term f (App b ts) = App b (subst_term_list f ts)"
| "subst_term_list f [] = []"
| "subst_term_list f (t # ts) = subst_term f t # subst_term_list f ts"

text \<open>The recursion scheme follows the structure of the unfolded
  definition of type @{typ "('a, 'b) term"}.  To prove properties of this
  substitution function, mutual induction is needed:
\<close>

lemma "subst_term (subst_term f1 \<circ> f2) t =
    subst_term f1 (subst_term f2 t)" and
  "subst_term_list (subst_term f1 \<circ> f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  by (induct t and ts rule: subst_term.induct subst_term_list.induct) simp_all
(*<*)end(*>*)


subsubsection \<open>Example: a map function for infinitely branching trees\<close>

text \<open>Defining functions on infinitely branching datatypes by primitive
  recursion is just as easy.\<close>

(*<*)experiment begin(*>*)
datatype 'a tree = Atom 'a | Branch "nat \<Rightarrow> 'a tree"

primrec map_tree :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tree \<Rightarrow> 'b tree"
where
  "map_tree f (Atom a) = Atom (f a)"
| "map_tree f (Branch ts) = Branch (\<lambda>x. map_tree f (ts x))"

text \<open>Note that all occurrences of functions such as @{text ts} above must
  be applied to an argument. In particular, @{term "map_tree f \<circ> ts"} is not
  allowed here.

  \<^medskip>
  Here is a simple composition lemma for @{term map_tree}:
\<close>

lemma "map_tree g (map_tree f t) = map_tree (g \<circ> f) t"
  by (induct t) simp_all
(*<*)end(*>*)


subsection \<open>Proof methods related to recursive definitions\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) pat_completeness} & : & @{text method} \\
    @{method_def (HOL) relation} & : & @{text method} \\
    @{method_def (HOL) lexicographic_order} & : & @{text method} \\
    @{method_def (HOL) size_change} & : & @{text method} \\
    @{method_def (HOL) induction_schema} & : & @{text method} \\
  \end{matharray}

  @{rail \<open>
    @@{method (HOL) relation} @{syntax term}
    ;
    @@{method (HOL) lexicographic_order} (@{syntax clasimpmod} * )
    ;
    @@{method (HOL) size_change} ( orders (@{syntax clasimpmod} * ) )
    ;
    @@{method (HOL) induction_schema}
    ;
    orders: ( 'max' | 'min' | 'ms' ) *
  \<close>}

  \<^descr> @{method (HOL) pat_completeness} is a specialized method to
  solve goals regarding the completeness of pattern matching, as
  required by the @{command (HOL) "function"} package (cf.\
  @{cite "isabelle-function"}).

  \<^descr> @{method (HOL) relation}~@{text R} introduces a termination
  proof using the relation @{text R}.  The resulting proof state will
  contain goals expressing that @{text R} is wellfounded, and that the
  arguments of recursive calls decrease with respect to @{text R}.
  Usually, this method is used as the initial proof step of manual
  termination proofs.

  \<^descr> @{method (HOL) "lexicographic_order"} attempts a fully
  automated termination proof by searching for a lexicographic
  combination of size measures on the arguments of the function. The
  method accepts the same arguments as the @{method auto} method,
  which it uses internally to prove local descents.  The @{syntax
  clasimpmod} modifiers are accepted (as for @{method auto}).

  In case of failure, extensive information is printed, which can help
  to analyse the situation (cf.\ @{cite "isabelle-function"}).

  \<^descr> @{method (HOL) "size_change"} also works on termination goals,
  using a variation of the size-change principle, together with a
  graph decomposition technique (see @{cite krauss_phd} for details).
  Three kinds of orders are used internally: @{text max}, @{text min},
  and @{text ms} (multiset), which is only available when the theory
  @{text Multiset} is loaded. When no order kinds are given, they are
  tried in order. The search for a termination proof uses SAT solving
  internally.

  For local descent proofs, the @{syntax clasimpmod} modifiers are
  accepted (as for @{method auto}).

  \<^descr> @{method (HOL) induction_schema} derives user-specified
  induction rules from well-founded induction and completeness of
  patterns. This factors out some operations that are done internally
  by the function package and makes them available separately. See
  @{file "~~/src/HOL/ex/Induction_Schema.thy"} for examples.
\<close>


subsection \<open>Functions with explicit partiality\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "partial_function"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def (HOL) "partial_function_mono"} & : & @{text attribute} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) partial_function} '(' @{syntax nameref} ')' @{syntax "fixes"} \<newline>
      @'where' @{syntax thmdecl}? @{syntax prop}
  \<close>}

  \<^descr> @{command (HOL) "partial_function"}~@{text "(mode)"} defines
  recursive functions based on fixpoints in complete partial
  orders. No termination proof is required from the user or
  constructed internally. Instead, the possibility of non-termination
  is modelled explicitly in the result type, which contains an
  explicit bottom element.

  Pattern matching and mutual recursion are currently not supported.
  Thus, the specification consists of a single function described by a
  single recursive equation.

  There are no fixed syntactic restrictions on the body of the
  function, but the induced functional must be provably monotonic
  wrt.\ the underlying order.  The monotonicity proof is performed
  internally, and the definition is rejected when it fails. The proof
  can be influenced by declaring hints using the
  @{attribute (HOL) partial_function_mono} attribute.

  The mandatory @{text mode} argument specifies the mode of operation
  of the command, which directly corresponds to a complete partial
  order on the result type. By default, the following modes are
  defined:

    \<^descr> @{text option} defines functions that map into the @{type
    option} type. Here, the value @{term None} is used to model a
    non-terminating computation. Monotonicity requires that if @{term
    None} is returned by a recursive call, then the overall result must
    also be @{term None}. This is best achieved through the use of the
    monadic operator @{const "Option.bind"}.

    \<^descr> @{text tailrec} defines functions with an arbitrary result
    type and uses the slightly degenerated partial order where @{term
    "undefined"} is the bottom element.  Now, monotonicity requires that
    if @{term undefined} is returned by a recursive call, then the
    overall result must also be @{term undefined}. In practice, this is
    only satisfied when each recursive call is a tail call, whose result
    is directly returned. Thus, this mode of operation allows the
    definition of arbitrary tail-recursive functions.

  Experienced users may define new modes by instantiating the locale
  @{const "partial_function_definitions"} appropriately.

  \<^descr> @{attribute (HOL) partial_function_mono} declares rules for
  use in the internal monotonicity proofs of partial function
  definitions.
\<close>


subsection \<open>Old-style recursive function definitions (TFL)\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "recdef"} & : & @{text "theory \<rightarrow> theory)"} \\
  \end{matharray}

  The old TFL command @{command (HOL) "recdef"} for defining recursive is
  mostly obsolete; @{command (HOL) "function"} or @{command (HOL) "fun"}
  should be used instead.

  @{rail \<open>
    @@{command (HOL) recdef} ('(' @'permissive' ')')? \<newline>
      @{syntax name} @{syntax term} (@{syntax prop} +) hints?
    ;
    hints: '(' @'hints' ( recdefmod * ) ')'
    ;
    recdefmod: (('recdef_simp' | 'recdef_cong' | 'recdef_wf')
      (() | 'add' | 'del') ':' @{syntax thmrefs}) | @{syntax clasimpmod}
  \<close>}

  \<^descr> @{command (HOL) "recdef"} defines general well-founded
  recursive functions (using the TFL package), see also
  @{cite "isabelle-HOL"}.  The ``@{text "(permissive)"}'' option tells
  TFL to recover from failed proof attempts, returning unfinished
  results.  The @{text recdef_simp}, @{text recdef_cong}, and @{text
  recdef_wf} hints refer to auxiliary rules to be used in the internal
  automated proof process of TFL.  Additional @{syntax clasimpmod}
  declarations may be given to tune the context of the Simplifier
  (cf.\ \secref{sec:simplifier}) and Classical reasoner (cf.\
  \secref{sec:classical}).


  \<^medskip>
  Hints for @{command (HOL) "recdef"} may be also declared
  globally, using the following attributes.

  \begin{matharray}{rcl}
    @{attribute_def (HOL) recdef_simp} & : & @{text attribute} \\
    @{attribute_def (HOL) recdef_cong} & : & @{text attribute} \\
    @{attribute_def (HOL) recdef_wf} & : & @{text attribute} \\
  \end{matharray}

  @{rail \<open>
    (@@{attribute (HOL) recdef_simp} | @@{attribute (HOL) recdef_cong} |
      @@{attribute (HOL) recdef_wf}) (() | 'add' | 'del')
  \<close>}
\<close>


section \<open>Adhoc overloading of constants\<close>

text \<open>
  \begin{tabular}{rcll}
  @{command_def "adhoc_overloading"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "no_adhoc_overloading"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{attribute_def "show_variants"} & : & @{text "attribute"} & default @{text false} \\
  \end{tabular}

  \<^medskip>
  Adhoc overloading allows to overload a constant depending on
  its type. Typically this involves the introduction of an
  uninterpreted constant (used for input and output) and the addition
  of some variants (used internally). For examples see
  @{file "~~/src/HOL/ex/Adhoc_Overloading_Examples.thy"} and
  @{file "~~/src/HOL/Library/Monad_Syntax.thy"}.

  @{rail \<open>
    (@@{command adhoc_overloading} | @@{command no_adhoc_overloading})
      (@{syntax nameref} (@{syntax term} + ) + @'and')
  \<close>}

  \<^descr> @{command "adhoc_overloading"}~@{text "c v\<^sub>1 ... v\<^sub>n"}
  associates variants with an existing constant.

  \<^descr> @{command "no_adhoc_overloading"} is similar to
  @{command "adhoc_overloading"}, but removes the specified variants
  from the present context.

  \<^descr> @{attribute "show_variants"} controls printing of variants
  of overloaded constants. If enabled, the internally used variants
  are printed instead of their respective overloaded constants. This
  is occasionally useful to check whether the system agrees with a
  user's expectations about derived variants.
\<close>


section \<open>Definition by specification \label{sec:hol-specification}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "specification"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) specification} '(' (decl +) ')' \<newline>
      (@{syntax thmdecl}? @{syntax prop} +)
    ;
    decl: (@{syntax name} ':')? @{syntax term} ('(' @'overloaded' ')')?
  \<close>}

  \<^descr> @{command (HOL) "specification"}~@{text "decls \<phi>"} sets up a
  goal stating the existence of terms with the properties specified to
  hold for the constants given in @{text decls}.  After finishing the
  proof, the theory will be augmented with definitions for the given
  constants, as well as with theorems stating the properties for these
  constants.

  @{text decl} declares a constant to be defined by the
  specification given.  The definition for the constant @{text c} is
  bound to the name @{text c_def} unless a theorem name is given in
  the declaration.  Overloaded constants should be declared as such.
\<close>


section \<open>Old-style datatypes \label{sec:hol-datatype}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "old_datatype"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "old_rep_datatype"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) old_datatype} (spec + @'and')
    ;
    @@{command (HOL) old_rep_datatype} ('(' (@{syntax name} +) ')')? (@{syntax term} +)
    ;

    spec: @{syntax typespec_sorts} @{syntax mixfix}? '=' (cons + '|')
    ;
    cons: @{syntax name} (@{syntax type} * ) @{syntax mixfix}?
  \<close>}

  \<^descr> @{command (HOL) "old_datatype"} defines old-style inductive
  datatypes in HOL.

  \<^descr> @{command (HOL) "old_rep_datatype"} represents existing types as
  old-style datatypes.


  These commands are mostly obsolete; @{command (HOL) "datatype"}
  should be used instead.

  See @{cite "isabelle-HOL"} for more details on datatypes, but beware of
  the old-style theory syntax being used there!  Apart from proper
  proof methods for case-analysis and induction, there are also
  emulations of ML tactics @{method (HOL) case_tac} and @{method (HOL)
  induct_tac} available, see \secref{sec:hol-induct-tac}; these admit
  to refer directly to the internal structure of subgoals (including
  internally bound parameters).
\<close>


subsubsection \<open>Examples\<close>

text \<open>We define a type of finite sequences, with slightly different names
  than the existing @{typ "'a list"} that is already in @{theory Main}:\<close>

(*<*)experiment begin(*>*)
datatype 'a seq = Empty | Seq 'a "'a seq"

text \<open>We can now prove some simple lemma by structural induction:\<close>

lemma "Seq x xs \<noteq> xs"
proof (induct xs arbitrary: x)
  case Empty
  txt \<open>This case can be proved using the simplifier: the freeness
    properties of the datatype are already declared as @{attribute
    simp} rules.\<close>
  show "Seq x Empty \<noteq> Empty"
    by simp
next
  case (Seq y ys)
  txt \<open>The step case is proved similarly.\<close>
  show "Seq x (Seq y ys) \<noteq> Seq y ys"
    using \<open>Seq y ys \<noteq> ys\<close> by simp
qed

text \<open>Here is a more succinct version of the same proof:\<close>

lemma "Seq x xs \<noteq> xs"
  by (induct xs arbitrary: x) simp_all
(*<*)end(*>*)


section \<open>Records \label{sec:hol-record}\<close>

text \<open>
  In principle, records merely generalize the concept of tuples, where
  components may be addressed by labels instead of just position.  The
  logical infrastructure of records in Isabelle/HOL is slightly more
  advanced, though, supporting truly extensible record schemes.  This
  admits operations that are polymorphic with respect to record
  extension, yielding ``object-oriented'' effects like (single)
  inheritance.  See also @{cite "NaraschewskiW-TPHOLs98"} for more
  details on object-oriented verification and record subtyping in HOL.
\<close>


subsection \<open>Basic concepts\<close>

text \<open>
  Isabelle/HOL supports both \<^emph>\<open>fixed\<close> and \<^emph>\<open>schematic\<close> records
  at the level of terms and types.  The notation is as follows:

  \begin{center}
  \begin{tabular}{l|l|l}
    & record terms & record types \\ \hline
    fixed & @{text "\<lparr>x = a, y = b\<rparr>"} & @{text "\<lparr>x :: A, y :: B\<rparr>"} \\
    schematic & @{text "\<lparr>x = a, y = b, \<dots> = m\<rparr>"} &
      @{text "\<lparr>x :: A, y :: B, \<dots> :: M\<rparr>"} \\
  \end{tabular}
  \end{center}

  The ASCII representation of @{text "\<lparr>x = a\<rparr>"} is @{text
  "(| x = a |)"}.

  A fixed record @{text "\<lparr>x = a, y = b\<rparr>"} has field @{text x} of value
  @{text a} and field @{text y} of value @{text b}.  The corresponding
  type is @{text "\<lparr>x :: A, y :: B\<rparr>"}, assuming that @{text "a :: A"}
  and @{text "b :: B"}.

  A record scheme like @{text "\<lparr>x = a, y = b, \<dots> = m\<rparr>"} contains fields
  @{text x} and @{text y} as before, but also possibly further fields
  as indicated by the ``@{text "\<dots>"}'' notation (which is actually part
  of the syntax).  The improper field ``@{text "\<dots>"}'' of a record
  scheme is called the \<^emph>\<open>more part\<close>.  Logically it is just a free
  variable, which is occasionally referred to as ``row variable'' in
  the literature.  The more part of a record scheme may be
  instantiated by zero or more further components.  For example, the
  previous scheme may get instantiated to @{text "\<lparr>x = a, y = b, z =
  c, \<dots> = m'\<rparr>"}, where @{text m'} refers to a different more part.
  Fixed records are special instances of record schemes, where
  ``@{text "\<dots>"}'' is properly terminated by the @{text "() :: unit"}
  element.  In fact, @{text "\<lparr>x = a, y = b\<rparr>"} is just an abbreviation
  for @{text "\<lparr>x = a, y = b, \<dots> = ()\<rparr>"}.

  \<^medskip>
  Two key observations make extensible records in a simply
  typed language like HOL work out:

  \<^enum> the more part is internalized, as a free term or type
  variable,

  \<^enum> field names are externalized, they cannot be accessed within
  the logic as first-class values.


  \<^medskip>
  In Isabelle/HOL record types have to be defined explicitly,
  fixing their field names and types, and their (optional) parent
  record.  Afterwards, records may be formed using above syntax, while
  obeying the canonical order of fields as given by their declaration.
  The record package provides several standard operations like
  selectors and updates.  The common setup for various generic proof
  tools enable succinct reasoning patterns.  See also the Isabelle/HOL
  tutorial @{cite "isabelle-hol-book"} for further instructions on using
  records in practice.
\<close>


subsection \<open>Record specifications\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "record"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) record} @{syntax "overloaded"}? @{syntax typespec_sorts} '=' \<newline>
      (@{syntax type} '+')? (constdecl +)
    ;
    constdecl: @{syntax name} '::' @{syntax type} @{syntax mixfix}?
  \<close>}

  \<^descr> @{command (HOL) "record"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t = \<tau> + c\<^sub>1 :: \<sigma>\<^sub>1
  \<dots> c\<^sub>n :: \<sigma>\<^sub>n"} defines extensible record type @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"},
  derived from the optional parent record @{text "\<tau>"} by adding new
  field components @{text "c\<^sub>i :: \<sigma>\<^sub>i"} etc.

  The type variables of @{text "\<tau>"} and @{text "\<sigma>\<^sub>i"} need to be
  covered by the (distinct) parameters @{text "\<alpha>\<^sub>1, \<dots>,
  \<alpha>\<^sub>m"}.  Type constructor @{text t} has to be new, while @{text
  \<tau>} needs to specify an instance of an existing record type.  At
  least one new field @{text "c\<^sub>i"} has to be specified.
  Basically, field names need to belong to a unique record.  This is
  not a real restriction in practice, since fields are qualified by
  the record name internally.

  The parent record specification @{text \<tau>} is optional; if omitted
  @{text t} becomes a root record.  The hierarchy of all records
  declared within a theory context forms a forest structure, i.e.\ a
  set of trees starting with a root record each.  There is no way to
  merge multiple parent records!

  For convenience, @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"} is made a
  type abbreviation for the fixed record type @{text "\<lparr>c\<^sub>1 ::
  \<sigma>\<^sub>1, \<dots>, c\<^sub>n :: \<sigma>\<^sub>n\<rparr>"}, likewise is @{text
  "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m, \<zeta>) t_scheme"} made an abbreviation for
  @{text "\<lparr>c\<^sub>1 :: \<sigma>\<^sub>1, \<dots>, c\<^sub>n :: \<sigma>\<^sub>n, \<dots> ::
  \<zeta>\<rparr>"}.
\<close>


subsection \<open>Record operations\<close>

text \<open>Any record definition of the form presented above produces certain
  standard operations. Selectors and updates are provided for any field,
  including the improper one ``@{text more}''. There are also cumulative
  record constructor functions. To simplify the presentation below, we
  assume for now that @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"} is a root record with fields
  @{text "c\<^sub>1 :: \<sigma>\<^sub>1, \<dots>, c\<^sub>n :: \<sigma>\<^sub>n"}.

  \<^medskip>
  \<^bold>\<open>Selectors\<close> and \<^bold>\<open>updates\<close> are available for any
  field (including ``@{text more}''):

  \begin{matharray}{lll}
    @{text "c\<^sub>i"} & @{text "::"} & @{text "\<lparr>\<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<sigma>\<^sub>i"} \\
    @{text "c\<^sub>i_update"} & @{text "::"} & @{text "\<sigma>\<^sub>i \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr>"} \\
  \end{matharray}

  There is special syntax for application of updates: @{text "r\<lparr>x := a\<rparr>"}
  abbreviates term @{text "x_update a r"}. Further notation for repeated
  updates is also available: @{text "r\<lparr>x := a\<rparr>\<lparr>y := b\<rparr>\<lparr>z := c\<rparr>"} may be
  written @{text "r\<lparr>x := a, y := b, z := c\<rparr>"}. Note that because of postfix
  notation the order of fields shown here is reverse than in the actual
  term. Since repeated updates are just function applications, fields may be
  freely permuted in @{text "\<lparr>x := a, y := b, z := c\<rparr>"}, as far as logical
  equality is concerned. Thus commutativity of independent updates can be
  proven within the logic for any two fields, but not as a general theorem.

  \<^medskip>
  The \<^bold>\<open>make\<close> operation provides a cumulative record
  constructor function:

  \begin{matharray}{lll}
    @{text "t.make"} & @{text "::"} & @{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>n \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
  \end{matharray}

  \<^medskip>
  We now reconsider the case of non-root records, which are derived
  of some parent. In general, the latter may depend on another parent as
  well, resulting in a list of \<^emph>\<open>ancestor records\<close>. Appending the lists
  of fields of all ancestors results in a certain field prefix. The record
  package automatically takes care of this by lifting operations over this
  context of ancestor fields. Assuming that @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"} has
  ancestor fields @{text "b\<^sub>1 :: \<rho>\<^sub>1, \<dots>, b\<^sub>k :: \<rho>\<^sub>k"}, the above record
  operations will get the following types:

  \<^medskip>
  \begin{tabular}{lll}
    @{text "c\<^sub>i"} & @{text "::"} & @{text "\<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<sigma>\<^sub>i"} \\
    @{text "c\<^sub>i_update"} & @{text "::"} & @{text "\<sigma>\<^sub>i \<Rightarrow>
      \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow>
      \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr>"} \\
    @{text "t.make"} & @{text "::"} & @{text "\<rho>\<^sub>1 \<Rightarrow> \<dots> \<rho>\<^sub>k \<Rightarrow> \<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>n \<Rightarrow>
      \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
  \end{tabular}
  \<^medskip>

  Some further operations address the extension aspect of a
  derived record scheme specifically: @{text "t.fields"} produces a record
  fragment consisting of exactly the new fields introduced here (the result
  may serve as a more part elsewhere); @{text "t.extend"} takes a fixed
  record and adds a given more part; @{text "t.truncate"} restricts a record
  scheme to a fixed record.

  \<^medskip>
  \begin{tabular}{lll}
    @{text "t.fields"} & @{text "::"} & @{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>n \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
    @{text "t.extend"} & @{text "::"} & @{text "\<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>\<rparr> \<Rightarrow>
      \<zeta> \<Rightarrow> \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr>"} \\
    @{text "t.truncate"} & @{text "::"} & @{text "\<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
  \end{tabular}
  \<^medskip>

  Note that @{text "t.make"} and @{text "t.fields"} coincide for
  root records.
\<close>


subsection \<open>Derived rules and proof tools\<close>

text \<open>
  The record package proves several results internally, declaring
  these facts to appropriate proof tools.  This enables users to
  reason about record structures quite conveniently.  Assume that
  @{text t} is a record type as specified above.

  \<^enum> Standard conversions for selectors or updates applied to record
  constructor terms are made part of the default Simplifier context; thus
  proofs by reduction of basic operations merely require the @{method simp}
  method without further arguments. These rules are available as @{text
  "t.simps"}, too.

  \<^enum> Selectors applied to updated records are automatically reduced by an
  internal simplification procedure, which is also part of the standard
  Simplifier setup.

  \<^enum> Inject equations of a form analogous to @{prop "(x, y) = (x', y') \<equiv>
  x = x' \<and> y = y'"} are declared to the Simplifier and Classical Reasoner as
  @{attribute iff} rules. These rules are available as @{text "t.iffs"}.

  \<^enum> The introduction rule for record equality analogous to @{text "x r =
  x r' \<Longrightarrow> y r = y r' \<dots> \<Longrightarrow> r = r'"} is declared to the Simplifier, and as the
  basic rule context as ``@{attribute intro}@{text "?"}''. The rule is
  called @{text "t.equality"}.

  \<^enum> Representations of arbitrary record expressions as canonical
  constructor terms are provided both in @{method cases} and @{method
  induct} format (cf.\ the generic proof methods of the same name,
  \secref{sec:cases-induct}). Several variations are available, for fixed
  records, record schemes, more parts etc.

  The generic proof methods are sufficiently smart to pick the most sensible
  rule according to the type of the indicated record expression: users just
  need to apply something like ``@{text "(cases r)"}'' to a certain proof
  problem.

  \<^enum> The derived record operations @{text "t.make"}, @{text "t.fields"},
  @{text "t.extend"}, @{text "t.truncate"} are \<^emph>\<open>not\<close> treated
  automatically, but usually need to be expanded by hand, using the
  collective fact @{text "t.defs"}.
\<close>


subsubsection \<open>Examples\<close>

text \<open>See @{file "~~/src/HOL/ex/Records.thy"}, for example.\<close>


section \<open>Semantic subtype definitions \label{sec:hol-typedef}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "typedef"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  A type definition identifies a new type with a non-empty subset of an
  existing type. More precisely, the new type is defined by exhibiting an
  existing type @{text \<tau>}, a set @{text "A :: \<tau> set"}, and proving @{prop
  "\<exists>x. x \<in> A"}. Thus @{text A} is a non-empty subset of @{text \<tau>}, and the
  new type denotes this subset. New functions are postulated that establish
  an isomorphism between the new type and the subset. In general, the type
  @{text \<tau>} may involve type variables @{text "\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n"} which means
  that the type definition produces a type constructor @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n)
  t"} depending on those type arguments.

  @{rail \<open>
    @@{command (HOL) typedef} @{syntax "overloaded"}? abs_type '=' rep_set
    ;
    @{syntax_def "overloaded"}: ('(' @'overloaded' ')')
    ;
    abs_type: @{syntax typespec_sorts} @{syntax mixfix}?
    ;
    rep_set: @{syntax term} (@'morphisms' @{syntax name} @{syntax name})?
  \<close>}

  To understand the concept of type definition better, we need to recount
  its somewhat complex history. The HOL logic goes back to the ``Simple
  Theory of Types'' (STT) of A. Church @{cite "church40"}, which is further
  explained in the book by P. Andrews @{cite "andrews86"}. The overview
  article by W. Farmer @{cite "Farmer:2008"} points out the ``seven
  virtues'' of this relatively simple family of logics. STT has only ground
  types, without polymorphism and without type definitions.

  \<^medskip>
  M. Gordon @{cite "Gordon:1985:HOL"} augmented Church's STT by
  adding schematic polymorphism (type variables and type constructors) and a
  facility to introduce new types as semantic subtypes from existing types.
  This genuine extension of the logic was explained semantically by A. Pitts
  in the book of the original Cambridge HOL88 system @{cite "pitts93"}. Type
  definitions work in this setting, because the general model-theory of STT
  is restricted to models that ensure that the universe of type
  interpretations is closed by forming subsets (via predicates taken from
  the logic).

  \<^medskip>
  Isabelle/HOL goes beyond Gordon-style HOL by admitting overloaded
  constant definitions @{cite "Wenzel:1997:TPHOL" and
  "Haftmann-Wenzel:2006:classes"}, which are actually a concept of
  Isabelle/Pure and do not depend on particular set-theoretic semantics of
  HOL. Over many years, there was no formal checking of semantic type
  definitions in Isabelle/HOL versus syntactic constant definitions in
  Isabelle/Pure. So the @{command typedef} command was described as
  ``axiomatic'' in the sense of \secref{sec:axiomatizations}, only with some
  local checks of the given type and its representing set.

  Recent clarification of overloading in the HOL logic proper @{cite
  "Kuncar-Popescu:2015"} demonstrate how the dissimilar concepts of constant
  definitions versus type definitions may be understood uniformly. This
  requires an interpretation of Isabelle/HOL that substantially reforms the
  set-theoretic model of A. Pitts @{cite "pitts93"}, by taking a schematic
  view on polymorphism and interpreting only ground types in the
  set-theoretic sense of HOL88. Moreover, type-constructors may be
  explicitly overloaded, e.g.\ by making the subset depend on type-class
  parameters (cf.\ \secref{sec:class}). This is semantically like a
  dependent type: the meaning relies on the operations provided by different
  type-class instances.

  \<^descr> @{command (HOL) "typedef"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = A"} defines a
  new type @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} from the set @{text A} over an existing
  type. The set @{text A} may contain type variables @{text "\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n"}
  as specified on the LHS, but no term variables. Non-emptiness of @{text A}
  needs to be proven on the spot, in order to turn the internal conditional
  characterization into usable theorems.

  The ``@{text "(overloaded)"}'' option allows the @{command
  "typedef"} specification to depend on constants that are not (yet)
  specified and thus left open as parameters, e.g.\ type-class parameters.

  Within a local theory specification, the newly introduced type constructor
  cannot depend on parameters or assumptions of the context: this is
  syntactically impossible in HOL. The non-emptiness proof may formally
  depend on local assumptions, but this has little practical relevance.

  For @{command (HOL) "typedef"}~@{text "t = A"} the newly introduced
  type @{text t} is accompanied by a pair of morphisms to relate it to
  the representing set over the old type.  By default, the injection
  from type to set is called @{text Rep_t} and its inverse @{text
  Abs_t}: An explicit @{keyword (HOL) "morphisms"} specification
  allows to provide alternative names.

  The logical characterization of @{command typedef} uses the predicate of
  locale @{const type_definition} that is defined in Isabelle/HOL. Various
  basic consequences of that are instantiated accordingly, re-using the
  locale facts with names derived from the new type constructor. Thus the
  generic theorem @{thm type_definition.Rep} is turned into the specific
  @{text "Rep_t"}, for example.

  Theorems @{thm type_definition.Rep}, @{thm
  type_definition.Rep_inverse}, and @{thm type_definition.Abs_inverse}
  provide the most basic characterization as a corresponding
  injection/surjection pair (in both directions).  The derived rules
  @{thm type_definition.Rep_inject} and @{thm
  type_definition.Abs_inject} provide a more convenient version of
  injectivity, suitable for automated proof tools (e.g.\ in
  declarations involving @{attribute simp} or @{attribute iff}).
  Furthermore, the rules @{thm type_definition.Rep_cases}~/ @{thm
  type_definition.Rep_induct}, and @{thm type_definition.Abs_cases}~/
  @{thm type_definition.Abs_induct} provide alternative views on
  surjectivity.  These rules are already declared as set or type rules
  for the generic @{method cases} and @{method induct} methods,
  respectively.
\<close>


subsubsection \<open>Examples\<close>

text \<open>The following trivial example pulls a three-element type into
existence within the formal logical environment of Isabelle/HOL.\<close>

(*<*)experiment begin(*>*)
typedef three = "{(True, True), (True, False), (False, True)}"
  by blast

definition "One = Abs_three (True, True)"
definition "Two = Abs_three (True, False)"
definition "Three = Abs_three (False, True)"

lemma three_distinct: "One \<noteq> Two"  "One \<noteq> Three"  "Two \<noteq> Three"
  by (simp_all add: One_def Two_def Three_def Abs_three_inject)

lemma three_cases:
  fixes x :: three obtains "x = One" | "x = Two" | "x = Three"
  by (cases x) (auto simp: One_def Two_def Three_def Abs_three_inject)
(*<*)end(*>*)

text \<open>Note that such trivial constructions are better done with
  derived specification mechanisms such as @{command datatype}:\<close>

(*<*)experiment begin(*>*)
datatype three = One | Two | Three
(*<*)end(*>*)

text \<open>This avoids re-doing basic definitions and proofs from the
  primitive @{command typedef} above.\<close>



section \<open>Functorial structure of types\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "functor"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) functor} (@{syntax name} ':')? @{syntax term}
  \<close>}

  \<^descr> @{command (HOL) "functor"}~@{text "prefix: m"} allows to prove and
  register properties about the functorial structure of type constructors.
  These properties then can be used by other packages to deal with those
  type constructors in certain type constructions. Characteristic theorems
  are noted in the current local theory. By default, they are prefixed with
  the base name of the type constructor, an explicit prefix can be given
  alternatively.

  The given term @{text "m"} is considered as \<^emph>\<open>mapper\<close> for the
  corresponding type constructor and must conform to the following type
  pattern:

  \begin{matharray}{lll}
    @{text "m"} & @{text "::"} &
      @{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>k \<Rightarrow> (\<^vec>\<alpha>\<^sub>n) t \<Rightarrow> (\<^vec>\<beta>\<^sub>n) t"} \\
  \end{matharray}

  where @{text t} is the type constructor, @{text "\<^vec>\<alpha>\<^sub>n"}
  and @{text "\<^vec>\<beta>\<^sub>n"} are distinct type variables free in the local
  theory and @{text "\<sigma>\<^sub>1"}, \ldots, @{text "\<sigma>\<^sub>k"} is a subsequence of @{text
  "\<alpha>\<^sub>1 \<Rightarrow> \<beta>\<^sub>1"}, @{text "\<beta>\<^sub>1 \<Rightarrow> \<alpha>\<^sub>1"}, \ldots, @{text "\<alpha>\<^sub>n \<Rightarrow> \<beta>\<^sub>n"}, @{text
  "\<beta>\<^sub>n \<Rightarrow> \<alpha>\<^sub>n"}.
\<close>


section \<open>Quotient types with lifting and transfer\<close>

text \<open>The quotient package defines a new quotient type given a raw type and
  a partial equivalence relation (\secref{sec:quotient-type}). The package
  also historically includes automation for transporting definitions and
  theorems (\secref{sec:old-quotient}), but most of this automation was
  superseded by the Lifting (\secref{sec:lifting}) and Transfer
  (\secref{sec:transfer}) packages.\<close>


subsection \<open>Quotient type definition \label{sec:quotient-type}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "quotient_type"} & : & @{text "local_theory \<rightarrow> proof(prove)"}\\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) quotient_type} @{syntax "overloaded"}? \<newline>
      @{syntax typespec} @{syntax mixfix}? '=' quot_type \<newline>
      quot_morphisms? quot_parametric?
    ;
    quot_type: @{syntax type} '/' ('partial' ':')? @{syntax term}
    ;
    quot_morphisms: @'morphisms' @{syntax name} @{syntax name}
    ;
    quot_parametric: @'parametric' @{syntax thmref}
  \<close>}

  \<^descr> @{command (HOL) "quotient_type"} defines a new quotient type @{text
  \<tau>}. The injection from a quotient type to a raw type is called @{text
  rep_\<tau>}, its inverse @{text abs_\<tau>} unless explicit @{keyword (HOL)
  "morphisms"} specification provides alternative names. @{command (HOL)
  "quotient_type"} requires the user to prove that the relation is an
  equivalence relation (predicate @{text equivp}), unless the user specifies
  explicitly @{text partial} in which case the obligation is @{text
  part_equivp}. A quotient defined with @{text partial} is weaker in the
  sense that less things can be proved automatically.

  The command internally proves a Quotient theorem and sets up the Lifting
  package by the command @{command (HOL) setup_lifting}. Thus the Lifting
  and Transfer packages can be used also with quotient types defined by
  @{command (HOL) "quotient_type"} without any extra set-up. The
  parametricity theorem for the equivalence relation R can be provided as an
  extra argument of the command and is passed to the corresponding internal
  call of @{command (HOL) setup_lifting}. This theorem allows the Lifting
  package to generate a stronger transfer rule for equality.
\<close>


subsection \<open>Lifting package \label{sec:lifting}\<close>

text \<open>
  The Lifting package allows users to lift terms of the raw type to the
  abstract type, which is a necessary step in building a library for an
  abstract type. Lifting defines a new constant by combining coercion
  functions (@{term Abs} and @{term Rep}) with the raw term. It also proves
  an appropriate transfer rule for the Transfer (\secref{sec:transfer})
  package and, if possible, an equation for the code generator.

  The Lifting package provides two main commands: @{command (HOL)
  "setup_lifting"} for initializing the package to work with a new type, and
  @{command (HOL) "lift_definition"} for lifting constants. The Lifting
  package works with all four kinds of type abstraction: type copies,
  subtypes, total quotients and partial quotients.

  Theoretical background can be found in @{cite
  "Huffman-Kuncar:2013:lifting_transfer"}.

  \begin{matharray}{rcl}
    @{command_def (HOL) "setup_lifting"} & : & @{text "local_theory \<rightarrow> local_theory"}\\
    @{command_def (HOL) "lift_definition"} & : & @{text "local_theory \<rightarrow> proof(prove)"}\\
    @{command_def (HOL) "lifting_forget"} & : & @{text "local_theory \<rightarrow> local_theory"}\\
    @{command_def (HOL) "lifting_update"} & : & @{text "local_theory \<rightarrow> local_theory"}\\
    @{command_def (HOL) "print_quot_maps"} & : & @{text "context \<rightarrow>"}\\
    @{command_def (HOL) "print_quotients"} & : & @{text "context \<rightarrow>"}\\
    @{attribute_def (HOL) "quot_map"} & : & @{text attribute} \\
    @{attribute_def (HOL) "relator_eq_onp"} & : & @{text attribute} \\
    @{attribute_def (HOL) "relator_mono"} & : & @{text attribute} \\
    @{attribute_def (HOL) "relator_distr"} & : & @{text attribute} \\
    @{attribute_def (HOL) "quot_del"} & : & @{text attribute} \\
    @{attribute_def (HOL) "lifting_restore"} & : & @{text attribute} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) setup_lifting} @{syntax thmref} @{syntax thmref}? \<newline>
      (@'parametric' @{syntax thmref})?
    ;
    @@{command (HOL) lift_definition} ('(' 'code_dt' ')')? \<newline>
      @{syntax name} '::' @{syntax type} @{syntax mixfix}? 'is' @{syntax term} \<newline>
      (@'parametric' (@{syntax thmref}+))?
    ;
    @@{command (HOL) lifting_forget} @{syntax nameref}
    ;
    @@{command (HOL) lifting_update} @{syntax nameref}
    ;
    @@{attribute (HOL) lifting_restore}
      @{syntax thmref} (@{syntax thmref} @{syntax thmref})?
  \<close>}

  \<^descr> @{command (HOL) "setup_lifting"} Sets up the Lifting package to work
  with a user-defined type. The command supports two modes.

    \<^enum> The first one is a low-level mode when the user must provide as a
    first argument of @{command (HOL) "setup_lifting"} a quotient theorem
    @{term "Quotient R Abs Rep T"}. The package configures a transfer rule for
    equality, a domain transfer rules and sets up the @{command_def (HOL)
    "lift_definition"} command to work with the abstract type. An optional
    theorem @{term "reflp R"}, which certifies that the equivalence relation R
    is total, can be provided as a second argument. This allows the package to
    generate stronger transfer rules. And finally, the parametricity theorem
    for @{term R} can be provided as a third argument. This allows the package
    to generate a stronger transfer rule for equality.

    Users generally will not prove the @{text Quotient} theorem manually for
    new types, as special commands exist to automate the process.

    \<^enum> When a new subtype is defined by @{command (HOL) typedef}, @{command
    (HOL) "lift_definition"} can be used in its second mode, where only the
    @{term type_definition} theorem @{term "type_definition Rep Abs A"} is
    used as an argument of the command. The command internally proves the
    corresponding @{term Quotient} theorem and registers it with @{command
    (HOL) setup_lifting} using its first mode.

  For quotients, the command @{command (HOL) quotient_type} can be used. The
  command defines a new quotient type and similarly to the previous case,
  the corresponding Quotient theorem is proved and registered by @{command
  (HOL) setup_lifting}.

  \<^medskip>
  The command @{command (HOL) "setup_lifting"} also sets up the
  code generator for the new type. Later on, when a new constant is defined
  by @{command (HOL) "lift_definition"}, the Lifting package proves and
  registers a code equation (if there is one) for the new constant.

  \<^descr> @{command (HOL) "lift_definition"} @{text "f :: \<tau>"} @{keyword (HOL)
  "is"} @{text t} Defines a new function @{text f} with an abstract type
  @{text \<tau>} in terms of a corresponding operation @{text t} on a
  representation type. More formally, if @{text "t :: \<sigma>"}, then the command
  builds a term @{text "F"} as a corresponding combination of abstraction
  and representation functions such that @{text "F :: \<sigma> \<Rightarrow> \<tau>" } and defines
  @{text "f \<equiv> F t"}. The term @{text t} does not have to be necessarily a
  constant but it can be any term.

  The command opens a proof and the user must discharge a respectfulness
  proof obligation. For a type copy, i.e.\ a typedef with @{text UNIV}, the
  obligation is discharged automatically. The proof goal is presented in a
  user-friendly, readable form. A respectfulness theorem in the standard
  format @{text f.rsp} and a transfer rule @{text f.transfer} for the
  Transfer package are generated by the package.

  The user can specify a parametricity theorems for @{text t} after the
  keyword @{keyword "parametric"}, which allows the command to generate
  parametric transfer rules for @{text f}.

  For each constant defined through trivial quotients (type copies or
  subtypes) @{text f.rep_eq} is generated. The equation is a code
  certificate that defines @{text f} using the representation function.

  For each constant @{text f.abs_eq} is generated. The equation is
  unconditional for total quotients. The equation defines @{text f} using
  the abstraction function.

  \<^medskip>
  Integration with [@{attribute code} abstract]: For subtypes
  (e.g.\ corresponding to a datatype invariant, such as @{typ "'a dlist"}),
  @{command (HOL) "lift_definition"} uses a code certificate theorem @{text
  f.rep_eq} as a code equation. Because of the limitation of the code
  generator, @{text f.rep_eq} cannot be used as a code equation if the
  subtype occurs inside the result type rather than at the top level (e.g.\
  function returning @{typ "'a dlist option"} vs. @{typ "'a dlist"}).

  In this case, an extension of @{command (HOL) "lift_definition"} can be
  invoked by specifying the flag @{text "code_dt"}. This extension enables
  code execution through series of internal type and lifting definitions if
  the return type @{text "\<tau>"} meets the following inductive conditions:

    \<^descr> @{text "\<tau>"} is a type variable

    \<^descr> @{text "\<tau> = \<tau>\<^sub>1 \<dots> \<tau>\<^sub>n \<kappa>"},
    where @{text "\<kappa>"} is an abstract type constructor and @{text "\<tau>\<^sub>1 \<dots> \<tau>\<^sub>n"}
    do not contain abstract types (i.e.\ @{typ "int dlist"} is allowed whereas
    @{typ "int dlist dlist"} not)

    \<^descr> @{text "\<tau> = \<tau>\<^sub>1 \<dots> \<tau>\<^sub>n \<kappa>"}, @{text "\<kappa>"} is a type constructor that
    was defined as a (co)datatype whose constructor argument types do not
    contain either non-free datatypes or the function type.

  Integration with [@{attribute code} equation]: For total quotients,
  @{command (HOL) "lift_definition"} uses @{text f.abs_eq} as a code
  equation.

  \<^descr> @{command (HOL) lifting_forget} and @{command (HOL) lifting_update}
  These two commands serve for storing and deleting the set-up of the
  Lifting package and corresponding transfer rules defined by this package.
  This is useful for hiding of type construction details of an abstract type
  when the construction is finished but it still allows additions to this
  construction when this is later necessary.

  Whenever the Lifting package is set up with a new abstract type @{text
  "\<tau>"} by @{command_def (HOL) "lift_definition"}, the package defines a new
  bundle that is called @{text "\<tau>.lifting"}. This bundle already includes
  set-up for the Lifting package. The new transfer rules introduced by
  @{command (HOL) "lift_definition"} can be stored in the bundle by the
  command @{command (HOL) "lifting_update"} @{text "\<tau>.lifting"}.

  The command @{command (HOL) "lifting_forget"} @{text "\<tau>.lifting"} deletes
  set-up of the Lifting package for @{text \<tau>} and deletes all the transfer
  rules that were introduced by @{command (HOL) "lift_definition"} using
  @{text \<tau>} as an abstract type.

  The stored set-up in a bundle can be reintroduced by the Isar commands for
  including a bundle (@{command "include"}, @{keyword "includes"} and
  @{command "including"}).

  \<^descr> @{command (HOL) "print_quot_maps"} prints stored quotient map
  theorems.

  \<^descr> @{command (HOL) "print_quotients"} prints stored quotient theorems.

  \<^descr> @{attribute (HOL) quot_map} registers a quotient map theorem, a
  theorem showing how to ``lift'' quotients over type constructors. E.g.\
  @{term "Quotient R Abs Rep T \<Longrightarrow> Quotient (rel_set R) (image Abs) (image
  Rep) (rel_set T)"}. For examples see @{file "~~/src/HOL/Lifting_Set.thy"}
  or @{file "~~/src/HOL/Lifting.thy"}. This property is proved automatically
  if the involved type is BNF without dead variables.

  \<^descr> @{attribute (HOL) relator_eq_onp} registers a theorem that shows
  that a relator applied to an equality restricted by a predicate @{term P}
  (i.e.\ @{term "eq_onp P"}) is equal to a predicator applied to the @{term
  P}. The combinator @{const eq_onp} is used for internal encoding of proper
  subtypes. Such theorems allows the package to hide @{text eq_onp} from a
  user in a user-readable form of a respectfulness theorem. For examples see
  @{file "~~/src/HOL/Lifting_Set.thy"} or @{file "~~/src/HOL/Lifting.thy"}.
  This property is proved automatically if the involved type is BNF without
  dead variables.

  \<^descr> @{attribute (HOL) "relator_mono"} registers a property describing a
  monotonicity of a relator. E.g.\ @{prop "A \<le> B \<Longrightarrow> rel_set A \<le> rel_set B"}.
  This property is needed for proving a stronger transfer rule in
  @{command_def (HOL) "lift_definition"} when a parametricity theorem for
  the raw term is specified and also for the reflexivity prover. For
  examples see @{file "~~/src/HOL/Lifting_Set.thy"} or @{file
  "~~/src/HOL/Lifting.thy"}. This property is proved automatically if the
  involved type is BNF without dead variables.

  \<^descr> @{attribute (HOL) "relator_distr"} registers a property describing a
  distributivity of the relation composition and a relator. E.g.\ @{text
  "rel_set R \<circ>\<circ> rel_set S = rel_set (R \<circ>\<circ> S)"}. This property is needed for
  proving a stronger transfer rule in @{command_def (HOL) "lift_definition"}
  when a parametricity theorem for the raw term is specified. When this
  equality does not hold unconditionally (e.g.\ for the function type), the
  user can specified each direction separately and also register multiple
  theorems with different set of assumptions. This attribute can be used
  only after the monotonicity property was already registered by @{attribute
  (HOL) "relator_mono"}. For examples see @{file
  "~~/src/HOL/Lifting_Set.thy"} or @{file "~~/src/HOL/Lifting.thy"}. This
  property is proved automatically if the involved type is BNF without dead
  variables.

  \<^descr> @{attribute (HOL) quot_del} deletes a corresponding Quotient theorem
  from the Lifting infrastructure and thus de-register the corresponding
  quotient. This effectively causes that @{command (HOL) lift_definition}
  will not do any lifting for the corresponding type. This attribute is
  rather used for low-level manipulation with set-up of the Lifting package
  because @{command (HOL) lifting_forget} is preferred for normal usage.

  \<^descr> @{attribute (HOL) lifting_restore} @{text "Quotient_thm pcr_def
  pcr_cr_eq_thm"} registers the Quotient theorem @{text Quotient_thm} in the
  Lifting infrastructure and thus sets up lifting for an abstract type
  @{text \<tau>} (that is defined by @{text Quotient_thm}). Optional theorems
  @{text pcr_def} and @{text pcr_cr_eq_thm} can be specified to register the
  parametrized correspondence relation for @{text \<tau>}. E.g.\ for @{typ "'a
  dlist"}, @{text pcr_def} is @{text "pcr_dlist A \<equiv> list_all2 A \<circ>\<circ>
  cr_dlist"} and @{text pcr_cr_eq_thm} is @{text "pcr_dlist (op =) = (op
  =)"}. This attribute is rather used for low-level manipulation with set-up
  of the Lifting package because using of the bundle @{text \<tau>.lifting}
  together with the commands @{command (HOL) lifting_forget} and @{command
  (HOL) lifting_update} is preferred for normal usage.

  \<^descr> Integration with the BNF package @{cite "isabelle-datatypes"}: As
  already mentioned, the theorems that are registered by the following
  attributes are proved and registered automatically if the involved type is
  BNF without dead variables: @{attribute (HOL) quot_map}, @{attribute (HOL)
  relator_eq_onp}, @{attribute (HOL) "relator_mono"}, @{attribute (HOL)
  "relator_distr"}. Also the definition of a relator and predicator is
  provided automatically. Moreover, if the BNF represents a datatype,
  simplification rules for a predicator are again proved automatically.
\<close>


subsection \<open>Transfer package \label{sec:transfer}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) "transfer"} & : & @{text method} \\
    @{method_def (HOL) "transfer'"} & : & @{text method} \\
    @{method_def (HOL) "transfer_prover"} & : & @{text method} \\
    @{attribute_def (HOL) "Transfer.transferred"} & : & @{text attribute} \\
    @{attribute_def (HOL) "untransferred"} & : & @{text attribute} \\
    @{method_def (HOL) "transfer_start"} & : & @{text method} \\
    @{method_def (HOL) "transfer_prover_start"} & : & @{text method} \\
    @{method_def (HOL) "transfer_step"} & : & @{text method} \\
    @{method_def (HOL) "transfer_end"} & : & @{text method} \\
    @{method_def (HOL) "transfer_prover_end"} & : & @{text method} \\
    @{attribute_def (HOL) "transfer_rule"} & : & @{text attribute} \\
    @{attribute_def (HOL) "transfer_domain_rule"} & : & @{text attribute} \\
    @{attribute_def (HOL) "relator_eq"} & : & @{text attribute} \\
    @{attribute_def (HOL) "relator_domain"} & : & @{text attribute} \\
  \end{matharray}

  \<^descr> @{method (HOL) "transfer"} method replaces the current subgoal with
  a logically equivalent one that uses different types and constants. The
  replacement of types and constants is guided by the database of transfer
  rules. Goals are generalized over all free variables by default; this is
  necessary for variables whose types change, but can be overridden for
  specific variables with e.g. @{text "transfer fixing: x y z"}.

  \<^descr> @{method (HOL) "transfer'"} is a variant of @{method (HOL) transfer}
  that allows replacing a subgoal with one that is logically stronger
  (rather than equivalent). For example, a subgoal involving equality on a
  quotient type could be replaced with a subgoal involving equality (instead
  of the corresponding equivalence relation) on the underlying raw type.

  \<^descr> @{method (HOL) "transfer_prover"} method assists with proving a
  transfer rule for a new constant, provided the constant is defined in
  terms of other constants that already have transfer rules. It should be
  applied after unfolding the constant definitions.

  \<^descr> @{method (HOL) "transfer_start"}, @{method (HOL) "transfer_step"},
  @{method (HOL) "transfer_end"}, @{method (HOL) "transfer_prover_start"}
  and @{method (HOL) "transfer_prover_end"} methods are meant to be used
  for debugging of @{method (HOL) "transfer"} and @{method (HOL) "transfer_prover"},
  which we can decompose as follows:
  @{method (HOL) "transfer"} = (@{method (HOL) "transfer_start"}, 
  @{method (HOL) "transfer_step"}+, @{method (HOL) "transfer_end"}) and
  @{method (HOL) "transfer_prover"} = (@{method (HOL) "transfer_prover_start"}, 
  @{method (HOL) "transfer_step"}+, @{method (HOL) "transfer_prover_end"}).
  For usage examples see @{file "~~/src/HOL/ex/Transfer_Debug.thy"} 

  \<^descr> @{attribute (HOL) "untransferred"} proves the same equivalent
  theorem as @{method (HOL) "transfer"} internally does.

  \<^descr> @{attribute (HOL) Transfer.transferred} works in the opposite
  direction than @{method (HOL) "transfer'"}. E.g.\ given the transfer
  relation @{text "ZN x n \<equiv> (x = int n)"}, corresponding transfer rules and
  the theorem @{text "\<forall>x::int \<in> {0..}. x < x + 1"}, the attribute would
  prove @{text "\<forall>n::nat. n < n + 1"}. The attribute is still in experimental
  phase of development.

  \<^descr> @{attribute (HOL) "transfer_rule"} attribute maintains a collection
  of transfer rules, which relate constants at two different types. Typical
  transfer rules may relate different type instances of the same polymorphic
  constant, or they may relate an operation on a raw type to a corresponding
  operation on an abstract type (quotient or subtype). For example:

    @{text "((A ===> B) ===> list_all2 A ===> list_all2 B) map map"} \\
    @{text "(cr_int ===> cr_int ===> cr_int) (\<lambda>(x,y) (u,v). (x+u, y+v)) plus"}

  Lemmas involving predicates on relations can also be registered using the
  same attribute. For example:

    @{text "bi_unique A \<Longrightarrow> (list_all2 A ===> op =) distinct distinct"} \\
    @{text "\<lbrakk>bi_unique A; bi_unique B\<rbrakk> \<Longrightarrow> bi_unique (rel_prod A B)"}

  Preservation of predicates on relations (@{text "bi_unique, bi_total,
  right_unique, right_total, left_unique, left_total"}) with the respect to
  a relator is proved automatically if the involved type is BNF @{cite
  "isabelle-datatypes"} without dead variables.

  \<^descr> @{attribute (HOL) "transfer_domain_rule"} attribute maintains a
  collection of rules, which specify a domain of a transfer relation by a
  predicate. E.g.\ given the transfer relation @{text "ZN x n \<equiv> (x = int
  n)"}, one can register the following transfer domain rule: @{text "Domainp
  ZN = (\<lambda>x. x \<ge> 0)"}. The rules allow the package to produce more readable
  transferred goals, e.g.\ when quantifiers are transferred.

  \<^descr> @{attribute (HOL) relator_eq} attribute collects identity laws for
  relators of various type constructors, e.g. @{term "rel_set (op =) = (op
  =)"}. The @{method (HOL) transfer} method uses these lemmas to infer
  transfer rules for non-polymorphic constants on the fly. For examples see
  @{file "~~/src/HOL/Lifting_Set.thy"} or @{file "~~/src/HOL/Lifting.thy"}.
  This property is proved automatically if the involved type is BNF without
  dead variables.

  \<^descr> @{attribute_def (HOL) "relator_domain"} attribute collects rules
  describing domains of relators by predicators. E.g.\ @{term "Domainp
  (rel_set T) = (\<lambda>A. Ball A (Domainp T))"}. This allows the package to lift
  transfer domain rules through type constructors. For examples see @{file
  "~~/src/HOL/Lifting_Set.thy"} or @{file "~~/src/HOL/Lifting.thy"}. This
  property is proved automatically if the involved type is BNF without dead
  variables.


  Theoretical background can be found in @{cite
  "Huffman-Kuncar:2013:lifting_transfer"}.
\<close>


subsection \<open>Old-style definitions for quotient types \label{sec:old-quotient}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (HOL) "quotient_definition"} & : & @{text "local_theory \<rightarrow> proof(prove)"}\\
    @{command_def (HOL) "print_quotmapsQ3"} & : & @{text "context \<rightarrow>"}\\
    @{command_def (HOL) "print_quotientsQ3"} & : & @{text "context \<rightarrow>"}\\
    @{command_def (HOL) "print_quotconsts"} & : & @{text "context \<rightarrow>"}\\
    @{method_def (HOL) "lifting"} & : & @{text method} \\
    @{method_def (HOL) "lifting_setup"} & : & @{text method} \\
    @{method_def (HOL) "descending"} & : & @{text method} \\
    @{method_def (HOL) "descending_setup"} & : & @{text method} \\
    @{method_def (HOL) "partiality_descending"} & : & @{text method} \\
    @{method_def (HOL) "partiality_descending_setup"} & : & @{text method} \\
    @{method_def (HOL) "regularize"} & : & @{text method} \\
    @{method_def (HOL) "injection"} & : & @{text method} \\
    @{method_def (HOL) "cleaning"} & : & @{text method} \\
    @{attribute_def (HOL) "quot_thm"} & : & @{text attribute} \\
    @{attribute_def (HOL) "quot_lifted"} & : & @{text attribute} \\
    @{attribute_def (HOL) "quot_respect"} & : & @{text attribute} \\
    @{attribute_def (HOL) "quot_preserve"} & : & @{text attribute} \\
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) quotient_definition} constdecl? @{syntax thmdecl}? \<newline>
    @{syntax term} 'is' @{syntax term}
    ;
    constdecl: @{syntax name} ('::' @{syntax type})? @{syntax mixfix}?
    ;
    @@{method (HOL) lifting} @{syntax thmrefs}?
    ;
    @@{method (HOL) lifting_setup} @{syntax thmrefs}?
  \<close>}

  \<^descr> @{command (HOL) "quotient_definition"} defines a constant on the
  quotient type.

  \<^descr> @{command (HOL) "print_quotmapsQ3"} prints quotient map functions.

  \<^descr> @{command (HOL) "print_quotientsQ3"} prints quotients.

  \<^descr> @{command (HOL) "print_quotconsts"} prints quotient constants.

  \<^descr> @{method (HOL) "lifting"} and @{method (HOL) "lifting_setup"}
  methods match the current goal with the given raw theorem to be lifted
  producing three new subgoals: regularization, injection and cleaning
  subgoals. @{method (HOL) "lifting"} tries to apply the heuristics for
  automatically solving these three subgoals and leaves only the subgoals
  unsolved by the heuristics to the user as opposed to @{method (HOL)
  "lifting_setup"} which leaves the three subgoals unsolved.

  \<^descr> @{method (HOL) "descending"} and @{method (HOL) "descending_setup"}
  try to guess a raw statement that would lift to the current subgoal. Such
  statement is assumed as a new subgoal and @{method (HOL) "descending"}
  continues in the same way as @{method (HOL) "lifting"} does. @{method
  (HOL) "descending"} tries to solve the arising regularization, injection
  and cleaning subgoals with the analogous method @{method (HOL)
  "descending_setup"} which leaves the four unsolved subgoals.

  \<^descr> @{method (HOL) "partiality_descending"} finds the regularized
  theorem that would lift to the current subgoal, lifts it and leaves as a
  subgoal. This method can be used with partial equivalence quotients where
  the non regularized statements would not be true. @{method (HOL)
  "partiality_descending_setup"} leaves the injection and cleaning subgoals
  unchanged.

  \<^descr> @{method (HOL) "regularize"} applies the regularization heuristics
  to the current subgoal.

  \<^descr> @{method (HOL) "injection"} applies the injection heuristics to the
  current goal using the stored quotient respectfulness theorems.

  \<^descr> @{method (HOL) "cleaning"} applies the injection cleaning heuristics
  to the current subgoal using the stored quotient preservation theorems.

  \<^descr> @{attribute (HOL) quot_lifted} attribute tries to automatically
  transport the theorem to the quotient type. The attribute uses all the
  defined quotients types and quotient constants often producing undesired
  results or theorems that cannot be lifted.

  \<^descr> @{attribute (HOL) quot_respect} and @{attribute (HOL) quot_preserve}
  attributes declare a theorem as a respectfulness and preservation theorem
  respectively. These are stored in the local theory store and used by the
  @{method (HOL) "injection"} and @{method (HOL) "cleaning"} methods
  respectively.

  \<^descr> @{attribute (HOL) quot_thm} declares that a certain theorem is a
  quotient extension theorem. Quotient extension theorems allow for
  quotienting inside container types. Given a polymorphic type that serves
  as a container, a map function defined for this container using @{command
  (HOL) "functor"} and a relation map defined for for the container type,
  the quotient extension theorem should be @{term "Quotient3 R Abs Rep \<Longrightarrow>
  Quotient3 (rel_map R) (map Abs) (map Rep)"}. Quotient extension theorems
  are stored in a database and are used all the steps of lifting theorems.
\<close>


chapter \<open>Proof tools\<close>

section \<open>Proving propositions\<close>

text \<open>
  In addition to the standard proof methods, a number of diagnosis
  tools search for proofs and provide an Isar proof snippet on success.
  These tools are available via the following commands.

  \begin{matharray}{rcl}
    @{command_def (HOL) "solve_direct"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "try"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "try0"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "sledgehammer"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "sledgehammer_params"} & : & @{text "theory \<rightarrow> theory"}
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) try}
    ;

    @@{command (HOL) try0} ( ( ( 'simp' | 'intro' | 'elim' | 'dest' ) ':' @{syntax thmrefs} ) + ) ?
      @{syntax nat}?
    ;

    @@{command (HOL) sledgehammer} ( '[' args ']' )? facts? @{syntax nat}?
    ;

    @@{command (HOL) sledgehammer_params} ( ( '[' args ']' ) ? )
    ;
    args: ( @{syntax name} '=' value + ',' )
    ;
    facts: '(' ( ( ( ( 'add' | 'del' ) ':' ) ? @{syntax thmrefs} ) + ) ? ')'
  \<close>} % FIXME check args "value"

  \<^descr> @{command (HOL) "solve_direct"} checks whether the current
  subgoals can be solved directly by an existing theorem. Duplicate
  lemmas can be detected in this way.

  \<^descr> @{command (HOL) "try0"} attempts to prove a subgoal
  using a combination of standard proof methods (@{method auto},
  @{method simp}, @{method blast}, etc.).  Additional facts supplied
  via @{text "simp:"}, @{text "intro:"}, @{text "elim:"}, and @{text
  "dest:"} are passed to the appropriate proof methods.

  \<^descr> @{command (HOL) "try"} attempts to prove or disprove a subgoal
  using a combination of provers and disprovers (@{command (HOL)
  "solve_direct"}, @{command (HOL) "quickcheck"}, @{command (HOL)
  "try0"}, @{command (HOL) "sledgehammer"}, @{command (HOL)
  "nitpick"}).

  \<^descr> @{command (HOL) "sledgehammer"} attempts to prove a subgoal
  using external automatic provers (resolution provers and SMT
  solvers). See the Sledgehammer manual @{cite "isabelle-sledgehammer"}
  for details.

  \<^descr> @{command (HOL) "sledgehammer_params"} changes @{command (HOL)
  "sledgehammer"} configuration options persistently.
\<close>


section \<open>Checking and refuting propositions\<close>

text \<open>
  Identifying incorrect propositions usually involves evaluation of
  particular assignments and systematic counterexample search.  This
  is supported by the following commands.

  \begin{matharray}{rcl}
    @{command_def (HOL) "value"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "values"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "quickcheck"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "nitpick"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "quickcheck_params"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "nitpick_params"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "quickcheck_generator"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "find_unused_assms"} & : & @{text "context \<rightarrow>"}
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) value} ( '[' @{syntax name} ']' )? modes? @{syntax term}
    ;

    @@{command (HOL) values} modes? @{syntax nat}? @{syntax term}
    ;

    (@@{command (HOL) quickcheck} | @@{command (HOL) nitpick})
      ( '[' args ']' )? @{syntax nat}?
    ;

    (@@{command (HOL) quickcheck_params} |
      @@{command (HOL) nitpick_params}) ( '[' args ']' )?
    ;

    @@{command (HOL) quickcheck_generator} @{syntax nameref} \<newline>
      'operations:' ( @{syntax term} +)
    ;

    @@{command (HOL) find_unused_assms} @{syntax name}?
    ;
    modes: '(' (@{syntax name} +) ')'
    ;
    args: ( @{syntax name} '=' value + ',' )
  \<close>} % FIXME check "value"

  \<^descr> @{command (HOL) "value"}~@{text t} evaluates and prints a
  term; optionally @{text modes} can be specified, which are appended
  to the current print mode; see \secref{sec:print-modes}.
  Evaluation is tried first using ML, falling
  back to normalization by evaluation if this fails.
  Alternatively a specific evaluator can be selected using square
  brackets; typical evaluators use the current set of code equations
  to normalize and include @{text simp} for fully symbolic evaluation
  using the simplifier, @{text nbe} for \<^emph>\<open>normalization by
  evaluation\<close> and \<^emph>\<open>code\<close> for code generation in SML.

  \<^descr> @{command (HOL) "values"}~@{text t} enumerates a set
  comprehension by evaluation and prints its values up to the given
  number of solutions; optionally @{text modes} can be specified,
  which are appended to the current print mode; see
  \secref{sec:print-modes}.

  \<^descr> @{command (HOL) "quickcheck"} tests the current goal for
  counterexamples using a series of assignments for its free
  variables; by default the first subgoal is tested, an other can be
  selected explicitly using an optional goal index.  Assignments can
  be chosen exhausting the search space up to a given size, or using a
  fixed number of random assignments in the search space, or exploring
  the search space symbolically using narrowing.  By default,
  quickcheck uses exhaustive testing.  A number of configuration
  options are supported for @{command (HOL) "quickcheck"}, notably:

    \<^descr>[@{text tester}] specifies which testing approach to apply.
    There are three testers, @{text exhaustive}, @{text random}, and
    @{text narrowing}.  An unknown configuration option is treated as
    an argument to tester, making @{text "tester ="} optional.  When
    multiple testers are given, these are applied in parallel.  If no
    tester is specified, quickcheck uses the testers that are set
    active, i.e.\ configurations @{attribute
    quickcheck_exhaustive_active}, @{attribute
    quickcheck_random_active}, @{attribute
    quickcheck_narrowing_active} are set to true.

    \<^descr>[@{text size}] specifies the maximum size of the search space
    for assignment values.

    \<^descr>[@{text genuine_only}] sets quickcheck only to return genuine
    counterexample, but not potentially spurious counterexamples due
    to underspecified functions.

    \<^descr>[@{text abort_potential}] sets quickcheck to abort once it
    found a potentially spurious counterexample and to not continue
    to search for a further genuine counterexample.
    For this option to be effective, the @{text genuine_only} option
    must be set to false.

    \<^descr>[@{text eval}] takes a term or a list of terms and evaluates
    these terms under the variable assignment found by quickcheck.
    This option is currently only supported by the default
    (exhaustive) tester.

    \<^descr>[@{text iterations}] sets how many sets of assignments are
    generated for each particular size.

    \<^descr>[@{text no_assms}] specifies whether assumptions in
    structured proofs should be ignored.

    \<^descr>[@{text locale}] specifies how to process conjectures in
    a locale context, i.e.\ they can be interpreted or expanded.
    The option is a whitespace-separated list of the two words
    @{text interpret} and @{text expand}. The list determines the
    order they are employed. The default setting is to first use
    interpretations and then test the expanded conjecture.
    The option is only provided as attribute declaration, but not
    as parameter to the command.

    \<^descr>[@{text timeout}] sets the time limit in seconds.

    \<^descr>[@{text default_type}] sets the type(s) generally used to
    instantiate type variables.

    \<^descr>[@{text report}] if set quickcheck reports how many tests
    fulfilled the preconditions.

    \<^descr>[@{text use_subtype}] if set quickcheck automatically lifts
    conjectures to registered subtypes if possible, and tests the
    lifted conjecture.

    \<^descr>[@{text quiet}] if set quickcheck does not output anything
    while testing.

    \<^descr>[@{text verbose}] if set quickcheck informs about the current
    size and cardinality while testing.

    \<^descr>[@{text expect}] can be used to check if the user's
    expectation was met (@{text no_expectation}, @{text
    no_counterexample}, or @{text counterexample}).

  These option can be given within square brackets.

  Using the following type classes, the testers generate values and convert
  them back into Isabelle terms for displaying counterexamples.

    \<^descr>[@{text exhaustive}] The parameters of the type classes @{class exhaustive}
    and @{class full_exhaustive} implement the testing. They take a
    testing function as a parameter, which takes a value of type @{typ "'a"}
    and optionally produces a counterexample, and a size parameter for the test values.
    In @{class full_exhaustive}, the testing function parameter additionally
    expects a lazy term reconstruction in the type @{typ Code_Evaluation.term}
    of the tested value.

    The canonical implementation for @{text exhaustive} testers calls the given
    testing function on all values up to the given size and stops as soon
    as a counterexample is found.

    \<^descr>[@{text random}] The operation @{const Quickcheck_Random.random}
    of the type class @{class random} generates a pseudo-random
    value of the given size and a lazy term reconstruction of the value
    in the type @{typ Code_Evaluation.term}. A pseudo-randomness generator
    is defined in theory @{theory Random}.

    \<^descr>[@{text narrowing}] implements Haskell's Lazy Smallcheck @{cite "runciman-naylor-lindblad"}
    using the type classes @{class narrowing} and @{class partial_term_of}.
    Variables in the current goal are initially represented as symbolic variables.
    If the execution of the goal tries to evaluate one of them, the test engine
    replaces it with refinements provided by @{const narrowing}.
    Narrowing views every value as a sum-of-products which is expressed using the operations
    @{const Quickcheck_Narrowing.cons} (embedding a value),
    @{const Quickcheck_Narrowing.apply} (product) and @{const Quickcheck_Narrowing.sum} (sum).
    The refinement should enable further evaluation of the goal.

    For example, @{const narrowing} for the list type @{typ "'a :: narrowing list"}
    can be recursively defined as
    @{term "Quickcheck_Narrowing.sum (Quickcheck_Narrowing.cons [])
              (Quickcheck_Narrowing.apply
                (Quickcheck_Narrowing.apply
                  (Quickcheck_Narrowing.cons (op #))
                  narrowing)
                narrowing)"}.
    If a symbolic variable of type @{typ "_ list"} is evaluated, it is replaced by (i)~the empty
    list @{term "[]"} and (ii)~by a non-empty list whose head and tail can then be recursively
    refined if needed.

    To reconstruct counterexamples, the operation @{const partial_term_of} transforms
    @{text narrowing}'s deep representation of terms to the type @{typ Code_Evaluation.term}.
    The deep representation models symbolic variables as
    @{const Quickcheck_Narrowing.Narrowing_variable}, which are normally converted to
    @{const Code_Evaluation.Free}, and refined values as
    @{term "Quickcheck_Narrowing.Narrowing_constructor i args"}, where @{term "i :: integer"}
    denotes the index in the sum of refinements. In the above example for lists,
    @{term "0"} corresponds to @{term "[]"} and @{term "1"}
    to @{term "op #"}.

    The command @{command (HOL) "code_datatype"} sets up @{const partial_term_of}
    such that the @{term "i"}-th refinement is interpreted as the @{term "i"}-th constructor,
    but it does not ensures consistency with @{const narrowing}.

  \<^descr> @{command (HOL) "quickcheck_params"} changes @{command (HOL)
  "quickcheck"} configuration options persistently.

  \<^descr> @{command (HOL) "quickcheck_generator"} creates random and
  exhaustive value generators for a given type and operations.  It
  generates values by using the operations as if they were
  constructors of that type.

  \<^descr> @{command (HOL) "nitpick"} tests the current goal for
  counterexamples using a reduction to first-order relational
  logic. See the Nitpick manual @{cite "isabelle-nitpick"} for details.

  \<^descr> @{command (HOL) "nitpick_params"} changes @{command (HOL)
  "nitpick"} configuration options persistently.

  \<^descr> @{command (HOL) "find_unused_assms"} finds potentially superfluous
  assumptions in theorems using quickcheck.
  It takes the theory name to be checked for superfluous assumptions as
  optional argument. If not provided, it checks the current theory.
  Options to the internal quickcheck invocations can be changed with
  common configuration declarations.
\<close>


section \<open>Coercive subtyping\<close>

text \<open>
  \begin{matharray}{rcl}
    @{attribute_def (HOL) coercion} & : & @{text attribute} \\
    @{attribute_def (HOL) coercion_delete} & : & @{text attribute} \\
    @{attribute_def (HOL) coercion_enabled} & : & @{text attribute} \\
    @{attribute_def (HOL) coercion_map} & : & @{text attribute} \\
    @{attribute_def (HOL) coercion_args} & : & @{text attribute} \\
  \end{matharray}

  Coercive subtyping allows the user to omit explicit type
  conversions, also called \<^emph>\<open>coercions\<close>.  Type inference will add
  them as necessary when parsing a term. See
  @{cite "traytel-berghofer-nipkow-2011"} for details.

  @{rail \<open>
    @@{attribute (HOL) coercion} (@{syntax term})
    ;
    @@{attribute (HOL) coercion_delete} (@{syntax term})
    ;
    @@{attribute (HOL) coercion_map} (@{syntax term})
    ;
    @@{attribute (HOL) coercion_args} (@{syntax const}) (('+' | '0' | '-')+)
  \<close>}

  \<^descr> @{attribute (HOL) "coercion"}~@{text "f"} registers a new
  coercion function @{text "f :: \<sigma>\<^sub>1 \<Rightarrow> \<sigma>\<^sub>2"} where @{text "\<sigma>\<^sub>1"} and
  @{text "\<sigma>\<^sub>2"} are type constructors without arguments.  Coercions are
  composed by the inference algorithm if needed.  Note that the type
  inference algorithm is complete only if the registered coercions
  form a lattice.

  \<^descr> @{attribute (HOL) "coercion_delete"}~@{text "f"} deletes a
  preceding declaration (using @{attribute (HOL) "coercion"}) of the
  function @{text "f :: \<sigma>\<^sub>1 \<Rightarrow> \<sigma>\<^sub>2"} as a coercion.

  \<^descr> @{attribute (HOL) "coercion_map"}~@{text "map"} registers a
  new map function to lift coercions through type constructors. The
  function @{text "map"} must conform to the following type pattern

  \begin{matharray}{lll}
    @{text "map"} & @{text "::"} &
      @{text "f\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> f\<^sub>n \<Rightarrow> (\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t \<Rightarrow> (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n) t"} \\
  \end{matharray}

  where @{text "t"} is a type constructor and @{text "f\<^sub>i"} is of type
  @{text "\<alpha>\<^sub>i \<Rightarrow> \<beta>\<^sub>i"} or @{text "\<beta>\<^sub>i \<Rightarrow> \<alpha>\<^sub>i"}.  Registering a map function
  overwrites any existing map function for this particular type
  constructor.

  \<^descr> @{attribute (HOL) "coercion_args"} can be used to disallow
  coercions to be inserted in certain positions in a term. For example,
  given the constant @{text "c :: \<sigma>\<^sub>1 \<Rightarrow> \<sigma>\<^sub>2 \<Rightarrow> \<sigma>\<^sub>3 \<Rightarrow> \<sigma>\<^sub>4"} and the list
  of policies @{text "- + 0"} as arguments, coercions will not be
  inserted in the first argument of @{text "c"} (policy @{text "-"});
  they may be inserted in the second argument (policy @{text "+"})
  even if the constant @{text "c"} itself is in a position where
  coercions are disallowed; the third argument inherits the allowance
  of coercsion insertion from the position of the constant @{text "c"}
  (policy @{text "0"}). The standard usage of policies is the definition
  of syntatic constructs (usually extralogical, i.e., processed and
  stripped during type inference), that should not be destroyed by the
  insertion of coercions (see, for example, the setup for the case syntax
  in @{theory Ctr_Sugar}). 

  \<^descr> @{attribute (HOL) "coercion_enabled"} enables the coercion
  inference algorithm.
\<close>


section \<open>Arithmetic proof support\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) arith} & : & @{text method} \\
    @{attribute_def (HOL) arith} & : & @{text attribute} \\
    @{attribute_def (HOL) arith_split} & : & @{text attribute} \\
  \end{matharray}

  \<^descr> @{method (HOL) arith} decides linear arithmetic problems (on
  types @{text nat}, @{text int}, @{text real}).  Any current facts
  are inserted into the goal before running the procedure.

  \<^descr> @{attribute (HOL) arith} declares facts that are supplied to
  the arithmetic provers implicitly.

  \<^descr> @{attribute (HOL) arith_split} attribute declares case split
  rules to be expanded before @{method (HOL) arith} is invoked.


  Note that a simpler (but faster) arithmetic prover is already
  invoked by the Simplifier.
\<close>


section \<open>Intuitionistic proof search\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) iprover} & : & @{text method} \\
  \end{matharray}

  @{rail \<open>
    @@{method (HOL) iprover} (@{syntax rulemod} *)
  \<close>}

  \<^descr> @{method (HOL) iprover} performs intuitionistic proof search,
  depending on specifically declared rules from the context, or given
  as explicit arguments.  Chained facts are inserted into the goal
  before commencing proof search.

  Rules need to be classified as @{attribute (Pure) intro},
  @{attribute (Pure) elim}, or @{attribute (Pure) dest}; here the
  ``@{text "!"}'' indicator refers to ``safe'' rules, which may be
  applied aggressively (without considering back-tracking later).
  Rules declared with ``@{text "?"}'' are ignored in proof search (the
  single-step @{method (Pure) rule} method still observes these).  An
  explicit weight annotation may be given as well; otherwise the
  number of rule premises will be taken into account here.
\<close>


section \<open>Model Elimination and Resolution\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) "meson"} & : & @{text method} \\
    @{method_def (HOL) "metis"} & : & @{text method} \\
  \end{matharray}

  @{rail \<open>
    @@{method (HOL) meson} @{syntax thmrefs}?
    ;
    @@{method (HOL) metis}
      ('(' ('partial_types' | 'full_types' | 'no_types' | @{syntax name}) ')')?
      @{syntax thmrefs}?
  \<close>}

  \<^descr> @{method (HOL) meson} implements Loveland's model elimination
  procedure @{cite "loveland-78"}.  See @{file
  "~~/src/HOL/ex/Meson_Test.thy"} for examples.

  \<^descr> @{method (HOL) metis} combines ordered resolution and ordered
  paramodulation to find first-order (or mildly higher-order) proofs.
  The first optional argument specifies a type encoding; see the
  Sledgehammer manual @{cite "isabelle-sledgehammer"} for details.  The
  directory @{file "~~/src/HOL/Metis_Examples"} contains several small
  theories developed to a large extent using @{method (HOL) metis}.
\<close>


section \<open>Algebraic reasoning via Gr\"obner bases\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) "algebra"} & : & @{text method} \\
    @{attribute_def (HOL) algebra} & : & @{text attribute} \\
  \end{matharray}

  @{rail \<open>
    @@{method (HOL) algebra}
      ('add' ':' @{syntax thmrefs})?
      ('del' ':' @{syntax thmrefs})?
    ;
    @@{attribute (HOL) algebra} (() | 'add' | 'del')
  \<close>}

  \<^descr> @{method (HOL) algebra} performs algebraic reasoning via
  Gr\"obner bases, see also @{cite "Chaieb-Wenzel:2007"} and
  @{cite \<open>\S3.2\<close> "Chaieb-thesis"}. The method handles deals with two main
  classes of problems:

    \<^enum> Universal problems over multivariate polynomials in a
    (semi)-ring/field/idom; the capabilities of the method are augmented
    according to properties of these structures. For this problem class
    the method is only complete for algebraically closed fields, since
    the underlying method is based on Hilbert's Nullstellensatz, where
    the equivalence only holds for algebraically closed fields.

    The problems can contain equations @{text "p = 0"} or inequations
    @{text "q \<noteq> 0"} anywhere within a universal problem statement.

    \<^enum> All-exists problems of the following restricted (but useful)
    form:

    @{text [display] "\<forall>x\<^sub>1 \<dots> x\<^sub>n.
      e\<^sub>1(x\<^sub>1, \<dots>, x\<^sub>n) = 0 \<and> \<dots> \<and> e\<^sub>m(x\<^sub>1, \<dots>, x\<^sub>n) = 0 \<longrightarrow>
      (\<exists>y\<^sub>1 \<dots> y\<^sub>k.
        p\<^sub>1\<^sub>1(x\<^sub>1, \<dots> ,x\<^sub>n) * y\<^sub>1 + \<dots> + p\<^sub>1\<^sub>k(x\<^sub>1, \<dots>, x\<^sub>n) * y\<^sub>k = 0 \<and>
        \<dots> \<and>
        p\<^sub>t\<^sub>1(x\<^sub>1, \<dots>, x\<^sub>n) * y\<^sub>1 + \<dots> + p\<^sub>t\<^sub>k(x\<^sub>1, \<dots>, x\<^sub>n) * y\<^sub>k = 0)"}

    Here @{text "e\<^sub>1, \<dots>, e\<^sub>n"} and the @{text "p\<^sub>i\<^sub>j"} are multivariate
    polynomials only in the variables mentioned as arguments.

  The proof method is preceded by a simplification step, which may be
  modified by using the form @{text "(algebra add: ths\<^sub>1 del: ths\<^sub>2)"}.
  This acts like declarations for the Simplifier
  (\secref{sec:simplifier}) on a private simpset for this tool.

  \<^descr> @{attribute algebra} (as attribute) manages the default
  collection of pre-simplification rules of the above proof method.
\<close>


subsubsection \<open>Example\<close>

text \<open>The subsequent example is from geometry: collinearity is
  invariant by rotation.\<close>

(*<*)experiment begin(*>*)
type_synonym point = "int \<times> int"

fun collinear :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "collinear (Ax, Ay) (Bx, By) (Cx, Cy) \<longleftrightarrow>
    (Ax - Bx) * (By - Cy) = (Ay - By) * (Bx - Cx)"

lemma collinear_inv_rotation:
  assumes "collinear (Ax, Ay) (Bx, By) (Cx, Cy)" and "c\<^sup>2 + s\<^sup>2 = 1"
  shows "collinear (Ax * c - Ay * s, Ay * c + Ax * s)
    (Bx * c - By * s, By * c + Bx * s) (Cx * c - Cy * s, Cy * c + Cx * s)"
  using assms by (algebra add: collinear.simps)
(*<*)end(*>*)

text \<open>
 See also @{file "~~/src/HOL/ex/Groebner_Examples.thy"}.
\<close>


section \<open>Coherent Logic\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def (HOL) "coherent"} & : & @{text method} \\
  \end{matharray}

  @{rail \<open>
    @@{method (HOL) coherent} @{syntax thmrefs}?
  \<close>}

  \<^descr> @{method (HOL) coherent} solves problems of \<^emph>\<open>Coherent
  Logic\<close> @{cite "Bezem-Coquand:2005"}, which covers applications in
  confluence theory, lattice theory and projective geometry.  See
  @{file "~~/src/HOL/ex/Coherent.thy"} for some examples.
\<close>


section \<open>Unstructured case analysis and induction \label{sec:hol-induct-tac}\<close>

text \<open>
  The following tools of Isabelle/HOL support cases analysis and
  induction in unstructured tactic scripts; see also
  \secref{sec:cases-induct} for proper Isar versions of similar ideas.

  \begin{matharray}{rcl}
    @{method_def (HOL) case_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def (HOL) induct_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def (HOL) ind_cases}@{text "\<^sup>*"} & : & @{text method} \\
    @{command_def (HOL) "inductive_cases"}@{text "\<^sup>*"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail \<open>
    @@{method (HOL) case_tac} @{syntax goal_spec}? @{syntax term} rule?
    ;
    @@{method (HOL) induct_tac} @{syntax goal_spec}? (@{syntax insts} * @'and') rule?
    ;
    @@{method (HOL) ind_cases} (@{syntax prop}+) @{syntax for_fixes}
    ;
    @@{command (HOL) inductive_cases} (@{syntax thmdecl}? (@{syntax prop}+) + @'and')
    ;
    rule: 'rule' ':' @{syntax thmref}
  \<close>}

  \<^descr> @{method (HOL) case_tac} and @{method (HOL) induct_tac} admit
  to reason about inductive types.  Rules are selected according to
  the declarations by the @{attribute cases} and @{attribute induct}
  attributes, cf.\ \secref{sec:cases-induct}.  The @{command (HOL)
  datatype} package already takes care of this.

  These unstructured tactics feature both goal addressing and dynamic
  instantiation.  Note that named rule cases are \<^emph>\<open>not\<close> provided
  as would be by the proper @{method cases} and @{method induct} proof
  methods (see \secref{sec:cases-induct}).  Unlike the @{method
  induct} method, @{method induct_tac} does not handle structured rule
  statements, only the compact object-logic conclusion of the subgoal
  being addressed.

  \<^descr> @{method (HOL) ind_cases} and @{command (HOL)
  "inductive_cases"} provide an interface to the internal @{ML_text
  mk_cases} operation.  Rules are simplified in an unrestricted
  forward manner.

  While @{method (HOL) ind_cases} is a proof method to apply the
  result immediately as elimination rules, @{command (HOL)
  "inductive_cases"} provides case split theorems at the theory level
  for later use.  The @{keyword "for"} argument of the @{method (HOL)
  ind_cases} method allows to specify a list of variables that should
  be generalized before applying the resulting rule.
\<close>


section \<open>Adhoc tuples\<close>

text \<open>
  \begin{matharray}{rcl}
    @{attribute_def (HOL) split_format}@{text "\<^sup>*"} & : & @{text attribute} \\
  \end{matharray}

  @{rail \<open>
    @@{attribute (HOL) split_format} ('(' 'complete' ')')?
  \<close>}

  \<^descr> @{attribute (HOL) split_format}\ @{text "(complete)"} causes
  arguments in function applications to be represented canonically
  according to their tuple type structure.

  Note that this operation tends to invent funny names for new local
  parameters introduced.
\<close>


chapter \<open>Executable code\<close>

text \<open>For validation purposes, it is often useful to \<^emph>\<open>execute\<close>
  specifications. In principle, execution could be simulated by Isabelle's
  inference kernel, i.e. by a combination of resolution and simplification.
  Unfortunately, this approach is rather inefficient. A more efficient way
  of executing specifications is to translate them into a functional
  programming language such as ML.

  Isabelle provides a generic framework to support code generation from
  executable specifications. Isabelle/HOL instantiates these mechanisms in a
  way that is amenable to end-user applications. Code can be generated for
  functional programs (including overloading using type classes) targeting
  SML @{cite SML}, OCaml @{cite OCaml}, Haskell @{cite
  "haskell-revised-report"} and Scala @{cite "scala-overview-tech-report"}.
  Conceptually, code generation is split up in three steps: \<^emph>\<open>selection\<close>
  of code theorems, \<^emph>\<open>translation\<close> into an abstract executable view and
  \<^emph>\<open>serialization\<close> to a specific \<^emph>\<open>target language\<close>. Inductive
  specifications can be executed using the predicate compiler which operates
  within HOL. See @{cite "isabelle-codegen"} for an introduction.

  \begin{matharray}{rcl}
    @{command_def (HOL) "export_code"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) code} & : & @{text attribute} \\
    @{command_def (HOL) "code_datatype"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "print_codesetup"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) code_unfold} & : & @{text attribute} \\
    @{attribute_def (HOL) code_post} & : & @{text attribute} \\
    @{attribute_def (HOL) code_abbrev} & : & @{text attribute} \\
    @{command_def (HOL) "print_codeproc"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "code_thms"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "code_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "code_reserved"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_printing"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_identifier"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_monad"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_reflect"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_pred"} & : & @{text "theory \<rightarrow> proof(prove)"}
  \end{matharray}

  @{rail \<open>
    @@{command (HOL) export_code} ( @'open' ) ? ( constexpr + ) \<newline>
       ( ( @'in' target ( @'module_name' @{syntax string} ) ? \<newline>
        ( @'file' @{syntax string} ) ? ( '(' args ')' ) ?) + ) ?
    ;
    const: @{syntax term}
    ;
    constexpr: ( const | 'name._' | '_' )
    ;
    typeconstructor: @{syntax nameref}
    ;
    class: @{syntax nameref}
    ;
    target: 'SML' | 'OCaml' | 'Haskell' | 'Scala' | 'Eval'
    ;
    @@{attribute (HOL) code} ( 'del' | 'equation' | 'abstype' | 'abstract'
      | 'drop:' ( const + ) | 'abort:' ( const + ) )?
    ;
    @@{command (HOL) code_datatype} ( const + )
    ;
    @@{attribute (HOL) code_unfold} ( 'del' ) ?
    ;
    @@{attribute (HOL) code_post} ( 'del' ) ?
    ;
    @@{attribute (HOL) code_abbrev}
    ;
    @@{command (HOL) code_thms} ( constexpr + ) ?
    ;
    @@{command (HOL) code_deps} ( constexpr + ) ?
    ;
    @@{command (HOL) code_reserved} target ( @{syntax string} + )
    ;
    symbol_const: ( @'constant' const )
    ;
    symbol_typeconstructor: ( @'type_constructor' typeconstructor )
    ;
    symbol_class: ( @'type_class' class )
    ;
    symbol_class_relation: ( @'class_relation' class ( '<' | '\<subseteq>' ) class )
    ;
    symbol_class_instance: ( @'class_instance' typeconstructor @'::' class )
    ;
    symbol_module: ( @'code_module' name )
    ;
    syntax: @{syntax string} | ( @'infix' | @'infixl' | @'infixr' ) @{syntax nat} @{syntax string}
    ;
    printing_const: symbol_const ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' syntax ? + @'and' )
    ;
    printing_typeconstructor: symbol_typeconstructor ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' syntax ? + @'and' )
    ;
    printing_class: symbol_class ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' @{syntax string} ? + @'and' )
    ;
    printing_class_relation: symbol_class_relation ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' @{syntax string} ? + @'and' )
    ;
    printing_class_instance: symbol_class_instance ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' '-' ? + @'and' )
    ;
    printing_module: symbol_module ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' ( @{syntax string} ( @'attach' ( const + ) ) ? ) ? + @'and' )
    ;
    @@{command (HOL) code_printing} ( ( printing_const | printing_typeconstructor
      | printing_class | printing_class_relation | printing_class_instance
      | printing_module ) + '|' )
    ;
    @@{command (HOL) code_identifier} ( ( symbol_const | symbol_typeconstructor
      | symbol_class | symbol_class_relation | symbol_class_instance
      | symbol_module ) ( '\<rightharpoonup>' | '=>' ) \<newline>
      ( '(' target ')' @{syntax string} ? + @'and' ) + '|' )
    ;
    @@{command (HOL) code_monad} const const target
    ;
    @@{command (HOL) code_reflect} @{syntax string} \<newline>
      ( @'datatypes' ( @{syntax string} '=' ( '_' | ( @{syntax string} + '|' ) + @'and' ) ) ) ? \<newline>
      ( @'functions' ( @{syntax string} + ) ) ? ( @'file' @{syntax string} ) ?
    ;
    @@{command (HOL) code_pred} \<newline> ('(' @'modes' ':' modedecl ')')? \<newline> const
    ;
    modedecl: (modes | ((const ':' modes) \<newline>
        (@'and' ((const ':' modes @'and') +))?))
    ;
    modes: mode @'as' const
  \<close>}

  \<^descr> @{command (HOL) "export_code"} generates code for a given list of
  constants in the specified target language(s). If no serialization
  instruction is given, only abstract code is generated internally.

  Constants may be specified by giving them literally, referring to all
  executable constants within a certain theory by giving @{text "name._"},
  or referring to \<^emph>\<open>all\<close> executable constants currently available by
  giving @{text "_"}.

  By default, exported identifiers are minimized per module. This can be
  suppressed by prepending @{keyword "open"} before the list of constants.

  By default, for each involved theory one corresponding name space module
  is generated. Alternatively, a module name may be specified after the
  @{keyword "module_name"} keyword; then \<^emph>\<open>all\<close> code is placed in this
  module.

  For \<^emph>\<open>SML\<close>, \<^emph>\<open>OCaml\<close> and \<^emph>\<open>Scala\<close> the file specification
  refers to a single file; for \<^emph>\<open>Haskell\<close>, it refers to a whole
  directory, where code is generated in multiple files reflecting the module
  hierarchy. Omitting the file specification denotes standard output.

  Serializers take an optional list of arguments in parentheses. For
  \<^emph>\<open>Haskell\<close> a module name prefix may be given using the ``@{text
  "root:"}'' argument; ``@{text string_classes}'' adds a ``@{verbatim
  "deriving (Read, Show)"}'' clause to each appropriate datatype
  declaration.

  \<^descr> @{attribute (HOL) code} declare code equations for code generation.
  Variant @{text "code equation"} declares a conventional equation as code
  equation. Variants @{text "code abstype"} and @{text "code abstract"}
  declare abstract datatype certificates or code equations on abstract
  datatype representations respectively. Vanilla @{text "code"} falls back
  to @{text "code equation"} or @{text "code abstype"} depending on the
  syntactic shape of the underlying equation. Variant @{text "code del"}
  deselects a code equation for code generation.

  Variants @{text "code drop:"} and @{text "code abort:"} take a list of
  constant as arguments and drop all code equations declared for them. In
  the case of {text abort}, these constants then are are not required to
  have a definition by means of code equations; if needed these are
  implemented by program abort (exception) instead.

  Usually packages introducing code equations provide a reasonable default
  setup for selection.

  \<^descr> @{command (HOL) "code_datatype"} specifies a constructor set for a
  logical type.

  \<^descr> @{command (HOL) "print_codesetup"} gives an overview on selected
  code equations and code generator datatypes.

  \<^descr> @{attribute (HOL) code_unfold} declares (or with option ``@{text
  "del"}'' removes) theorems which during preprocessing are applied as
  rewrite rules to any code equation or evaluation input.

  \<^descr> @{attribute (HOL) code_post} declares (or with option ``@{text
  "del"}'' removes) theorems which are applied as rewrite rules to any
  result of an evaluation.

  \<^descr> @{attribute (HOL) code_abbrev} declares (or with option ``@{text
  "del"}'' removes) equations which are applied as rewrite rules to any
  result of an evaluation and symmetrically during preprocessing to any code
  equation or evaluation input.

  \<^descr> @{command (HOL) "print_codeproc"} prints the setup of the code
  generator preprocessor.

  \<^descr> @{command (HOL) "code_thms"} prints a list of theorems representing
  the corresponding program containing all given constants after
  preprocessing.

  \<^descr> @{command (HOL) "code_deps"} visualizes dependencies of theorems
  representing the corresponding program containing all given constants
  after preprocessing.

  \<^descr> @{command (HOL) "code_reserved"} declares a list of names as
  reserved for a given target, preventing it to be shadowed by any generated
  code.

  \<^descr> @{command (HOL) "code_printing"} associates a series of symbols
  (constants, type constructors, classes, class relations, instances, module
  names) with target-specific serializations; omitting a serialization
  deletes an existing serialization.

  \<^descr> @{command (HOL) "code_monad"} provides an auxiliary mechanism to
  generate monadic code for Haskell.

  \<^descr> @{command (HOL) "code_identifier"} associates a a series of symbols
  (constants, type constructors, classes, class relations, instances, module
  names) with target-specific hints how these symbols shall be named. These
  hints gain precedence over names for symbols with no hints at all.
  Conflicting hints are subject to name disambiguation. \<^emph>\<open>Warning:\<close> It
  is at the discretion of the user to ensure that name prefixes of
  identifiers in compound statements like type classes or datatypes are
  still the same.

  \<^descr> @{command (HOL) "code_reflect"} without a ``@{text "file"}''
  argument compiles code into the system runtime environment and modifies
  the code generator setup that future invocations of system runtime code
  generation referring to one of the ``@{text "datatypes"}'' or ``@{text
  "functions"}'' entities use these precompiled entities. With a ``@{text
  "file"}'' argument, the corresponding code is generated into that
  specified file without modifying the code generator setup.

  \<^descr> @{command (HOL) "code_pred"} creates code equations for a predicate
  given a set of introduction rules. Optional mode annotations determine
  which arguments are supposed to be input or output. If alternative
  introduction rules are declared, one must prove a corresponding
  elimination rule.
\<close>

end
