(*  Title:      HOL/Import/HOL_Light_Import.thy
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH
*)

section \<open>Main HOL Light importer\<close>

theory HOL_Light_Import
  imports HOL_Light_Maps
  options [condition = "$HOL_LIGHT_BUNDLE"]
begin

import_file "$HOL_LIGHT_BUNDLE"

end

