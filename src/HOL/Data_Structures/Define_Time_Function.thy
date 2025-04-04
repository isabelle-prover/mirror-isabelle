(*
Author: Jonas Stahl

Automatic definition of step-counting running-time functions from HOL functions
following the translation described in Section 1.5, Running Time, of the book
Functional Data Structures and Algorithms. A Proof Assistant Approach.
See https://functional-algorithms-verified.org
*)

theory Define_Time_Function
  imports Main
  keywords "time_fun" :: thy_decl
    and    "time_function" :: thy_decl
    and    "time_definition" :: thy_decl
    and    "time_partial_function" :: thy_decl
    and    "equations"
    and    "time_fun_0" :: thy_decl
begin

ML_file Define_Time_0.ML
ML_file Define_Time_Function.ML

declare [[time_prefix = "T_"]]

text \<open>
This theory provides commands for the automatic definition of step-counting running-time functions
from HOL functions following the translation described in Section 1.5, Running Time, of the book
"Functional Data Structures and Algorithms. A Proof Assistant Approach."
See @{url "https://functional-algorithms-verified.org"}

Command \<open>time_fun f\<close> retrieves the definition of \<open>f\<close> and defines a corresponding step-counting
running-time function \<open>T_f\<close>. For all auxiliary functions used by \<open>f\<close> (excluding constructors),
running time functions must already have been defined.
If the definition of the function requires a manual termination proof,
use \<open>time_function\<close> accompanied by a \<open>termination\<close> command.
Limitation: The commands do not work properly in locales yet.

The pre-defined functions below are assumed to have constant running time.
In fact, we make that constant 0.
This does not change the asymptotic running time of user-defined functions using the
pre-defined functions because 1 is added for every user-defined function call.

Many of the functions below are polymorphic and reside in type classes.
The constant-time assumption is justified only for those types where the hardware offers
suitable support, e.g. numeric types. The argument size is implicitly bounded, too.

The constant-time assumption for \<open>(=)\<close> is justified for recursive data types such as lists and trees
as long as the comparison is of the form \<open>t = c\<close> where \<open>c\<close> is a constant term, for example \<open>xs = []\<close>.

Users of this running time framework need to ensure that 0-time functions are used only
within the above restrictions.\<close>

time_fun_0 "min"
time_fun_0 "max"
time_fun_0 "(+)"
time_fun_0 "(-)"
time_fun_0 "(*)"
time_fun_0 "(/)"
time_fun_0 "(div)"
time_fun_0 "(<)"
time_fun_0 "(\<le>)"
time_fun_0 "Not"
time_fun_0 "(\<and>)"
time_fun_0 "(\<or>)"
time_fun_0 "Num.numeral_class.numeral"
time_fun_0 "(=)"

end