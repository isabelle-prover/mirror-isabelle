(*  Title:      HOL/Bali/DeclConcepts.thy
    Author:     Norbert Schirmer
*)
subsection \<open>Advanced concepts on Java declarations like overriding, inheritance,
dynamic method lookup\<close>

theory DeclConcepts imports TypeRel begin

subsubsection "access control (cf. 6.6), overriding and hiding (cf. 8.4.6.1)"

definition is_public :: "prog \<Rightarrow> qtname \<Rightarrow> bool" where
"is_public G qn = (case class G qn of
                     None       \<Rightarrow> (case iface G qn of
                                      None       \<Rightarrow> False
                                    | Some i \<Rightarrow> access i = Public)
                   | Some c \<Rightarrow> access c = Public)"

subsection "accessibility of types (cf. 6.6.1)"
text \<open>
Primitive types are always accessible, interfaces and classes are accessible
in their package or if they are defined public, an array type is accessible if
its element type is accessible\<close>
 
primrec
  accessible_in :: "prog \<Rightarrow> ty \<Rightarrow> pname \<Rightarrow> bool"  (\<open>_ \<turnstile> _ accessible'_in _\<close> [61,61,61] 60) and
  rt_accessible_in :: "prog \<Rightarrow> ref_ty \<Rightarrow> pname \<Rightarrow> bool"  (\<open>_ \<turnstile> _ accessible'_in'' _\<close> [61,61,61] 60)
where
  "G\<turnstile>(PrimT p) accessible_in pack = True"
| accessible_in_RefT_simp:
  "G\<turnstile>(RefT  r) accessible_in pack = G\<turnstile>r accessible_in' pack"
| "G\<turnstile>(NullT) accessible_in' pack = True"
| "G\<turnstile>(IfaceT I) accessible_in' pack = ((pid I = pack) \<or> is_public G I)"
| "G\<turnstile>(ClassT C) accessible_in' pack = ((pid C = pack) \<or> is_public G C)"
| "G\<turnstile>(ArrayT ty) accessible_in' pack = G\<turnstile>ty accessible_in pack"

declare accessible_in_RefT_simp [simp del]

definition
  is_acc_class :: "prog \<Rightarrow> pname \<Rightarrow> qtname \<Rightarrow> bool"
  where "is_acc_class G P C = (is_class G C \<and> G\<turnstile>(Class C) accessible_in P)"

definition
  is_acc_iface :: "prog \<Rightarrow> pname \<Rightarrow> qtname \<Rightarrow> bool"
  where "is_acc_iface G P I = (is_iface G I \<and> G\<turnstile>(Iface I) accessible_in P)"

definition
  is_acc_type :: "prog \<Rightarrow> pname \<Rightarrow> ty \<Rightarrow> bool"
  where "is_acc_type  G P T = (is_type G T  \<and> G\<turnstile>T accessible_in P)"

definition
  is_acc_reftype  :: "prog \<Rightarrow> pname \<Rightarrow> ref_ty \<Rightarrow> bool"
  where "is_acc_reftype G P T = (isrtype G T  \<and> G\<turnstile>T accessible_in' P)"

lemma is_acc_classD:
 "is_acc_class G P C \<Longrightarrow>  is_class G C \<and> G\<turnstile>(Class C) accessible_in P"
by (simp add: is_acc_class_def)

lemma is_acc_class_is_class: "is_acc_class G P C \<Longrightarrow> is_class G C"
by (auto simp add: is_acc_class_def)

lemma is_acc_ifaceD:
  "is_acc_iface G P I \<Longrightarrow> is_iface G I \<and> G\<turnstile>(Iface I) accessible_in P"
by (simp add: is_acc_iface_def)

lemma is_acc_typeD:
 "is_acc_type  G P T \<Longrightarrow> is_type G T  \<and> G\<turnstile>T accessible_in P"
by (simp add: is_acc_type_def)

lemma is_acc_reftypeD:
"is_acc_reftype  G P T \<Longrightarrow> isrtype G T  \<and> G\<turnstile>T accessible_in' P"
by (simp add: is_acc_reftype_def)

subsection "accessibility of members"
text \<open>
The accessibility of members is more involved as the accessibility of types.
We have to distinguish several cases to model the different effects of 
accessibility during inheritance, overriding and ordinary member access 
\<close>

subsubsection \<open>Various technical conversion and selection functions\<close>

text \<open>overloaded selector \<open>accmodi\<close> to select the access modifier 
out of various HOL types\<close>

class has_accmodi =
  fixes accmodi:: "'a \<Rightarrow> acc_modi"

instantiation acc_modi :: has_accmodi
begin

definition
  acc_modi_accmodi_def: "accmodi (a::acc_modi) = a"

instance ..

end

lemma acc_modi_accmodi_simp[simp]: "accmodi (a::acc_modi) = a"
by (simp add: acc_modi_accmodi_def)

instantiation decl_ext :: (type) has_accmodi
begin

definition
  decl_acc_modi_def: "accmodi (d::('a:: type) decl_scheme) = access d"

instance ..

end

lemma decl_acc_modi_simp[simp]: "accmodi (d::('a::type) decl_scheme) = access d"
by (simp add: decl_acc_modi_def)

instantiation prod :: (type, has_accmodi) has_accmodi
begin

definition
  pair_acc_modi_def: "accmodi p = accmodi (snd p)"

instance ..

end

lemma pair_acc_modi_simp[simp]: "accmodi (x,a) = (accmodi a)"
by (simp add: pair_acc_modi_def)

instantiation memberdecl :: has_accmodi
begin

definition
  memberdecl_acc_modi_def: "accmodi m = (case m of
                                          fdecl f \<Rightarrow> accmodi f
                                        | mdecl m \<Rightarrow> accmodi m)"

instance ..

end

lemma memberdecl_fdecl_acc_modi_simp[simp]:
 "accmodi (fdecl m) = accmodi m"
by (simp add: memberdecl_acc_modi_def)

lemma memberdecl_mdecl_acc_modi_simp[simp]:
 "accmodi (mdecl m) = accmodi m"
by (simp add: memberdecl_acc_modi_def)

text \<open>overloaded selector \<open>declclass\<close> to select the declaring class 
out of various HOL types\<close>

class has_declclass =
  fixes declclass:: "'a \<Rightarrow> qtname"

instantiation qtname_ext :: (type) has_declclass
begin

definition
  "declclass q = \<lparr> pid = pid q, tid = tid q \<rparr>"

instance ..

end

lemma qtname_declclass_def:
  "declclass q \<equiv> (q::qtname)"
  by (induct q) (simp add: declclass_qtname_ext_def)

lemma qtname_declclass_simp[simp]: "declclass (q::qtname) = q"
by (simp add: qtname_declclass_def)

instantiation prod :: (has_declclass, type) has_declclass
begin

definition
  pair_declclass_def: "declclass p = declclass (fst p)"

instance ..

end

lemma pair_declclass_simp[simp]: "declclass (c,x) = declclass c" 
by (simp add: pair_declclass_def)

text \<open>overloaded selector \<open>is_static\<close> to select the static modifier 
out of various HOL types\<close>

class has_static =
  fixes is_static :: "'a \<Rightarrow> bool"

instantiation decl_ext :: (has_static) has_static
begin

instance ..

end

instantiation member_ext :: (type) has_static
begin

instance ..

end

axiomatization where
  static_field_type_is_static_def: "is_static (m::('a member_scheme)) \<equiv> static m"

lemma member_is_static_simp: "is_static (m::'a member_scheme) = static m"
by (simp add: static_field_type_is_static_def)

instantiation prod :: (type, has_static) has_static
begin

definition
  pair_is_static_def: "is_static p = is_static (snd p)"

instance ..

end

lemma pair_is_static_simp [simp]: "is_static (x,s) = is_static s"
by (simp add: pair_is_static_def)

lemma pair_is_static_simp1: "is_static p = is_static (snd p)"
by (simp add: pair_is_static_def)

instantiation memberdecl :: has_static
begin

definition
memberdecl_is_static_def: 
 "is_static m = (case m of
                    fdecl f \<Rightarrow> is_static f
                  | mdecl m \<Rightarrow> is_static m)"

instance ..

end

lemma memberdecl_is_static_fdecl_simp[simp]:
 "is_static (fdecl f) = is_static f"
by (simp add: memberdecl_is_static_def)

lemma memberdecl_is_static_mdecl_simp[simp]:
 "is_static (mdecl m) = is_static m"
by (simp add: memberdecl_is_static_def)

lemma mhead_static_simp [simp]: "is_static (mhead m) = is_static m"
by (cases m) (simp add: mhead_def member_is_static_simp)

\<comment> \<open>some mnemotic selectors for various pairs\<close> 

definition
  decliface :: "qtname \<times> 'a decl_scheme \<Rightarrow> qtname" where
  "decliface = fst"          \<comment> \<open>get the interface component\<close>

definition
  mbr :: "qtname \<times> memberdecl \<Rightarrow> memberdecl" where
  "mbr = snd"            \<comment> \<open>get the memberdecl component\<close>

definition
  mthd :: "'b \<times> 'a \<Rightarrow> 'a" where
  "mthd = snd"              \<comment> \<open>get the method component\<close>
    \<comment> \<open>also used for mdecl, mhead\<close>

definition
  fld :: "'b \<times> 'a decl_scheme \<Rightarrow> 'a decl_scheme" where
  "fld = snd"               \<comment> \<open>get the field component\<close>
    \<comment> \<open>also used for \<open>((vname \<times> qtname)\<times> field)\<close>\<close>

\<comment> \<open>some mnemotic selectors for \<open>(vname \<times> qtname)\<close>\<close>

definition
  fname:: "vname \<times> 'a \<Rightarrow> vname"
  where "fname = fst"
    \<comment> \<open>also used for fdecl\<close>

definition
  declclassf:: "(vname \<times> qtname) \<Rightarrow> qtname"
  where "declclassf = snd"


lemma decliface_simp[simp]: "decliface (I,m) = I"
by (simp add: decliface_def) 

lemma mbr_simp[simp]: "mbr (C,m) = m"
by (simp add: mbr_def)

lemma access_mbr_simp [simp]: "(accmodi (mbr m)) = accmodi m"
by (cases m) (simp add:  mbr_def) 

lemma mthd_simp[simp]: "mthd (C,m) = m"
by (simp add: mthd_def)

lemma fld_simp[simp]: "fld (C,f) = f"
by (simp add: fld_def)

lemma accmodi_simp[simp]: "accmodi (C,m) = access m"
by (simp )

lemma access_mthd_simp [simp]: "(access (mthd m)) = accmodi m"
by (cases m) (simp add: mthd_def) 

lemma access_fld_simp [simp]: "(access (fld f)) = accmodi f"
by (cases f) (simp add:  fld_def) 

lemma static_mthd_simp[simp]: "static (mthd m) = is_static m"
by (cases m) (simp add:  mthd_def member_is_static_simp)

lemma mthd_is_static_simp [simp]: "is_static (mthd m) = is_static m"
by (cases m) simp

lemma static_fld_simp[simp]: "static (fld f) = is_static f"
by (cases f) (simp add:  fld_def member_is_static_simp)

lemma ext_field_simp [simp]: "(declclass f,fld f) = f"
by (cases f) (simp add:  fld_def)

lemma ext_method_simp [simp]: "(declclass m,mthd m) = m"
by (cases m) (simp add:  mthd_def)

lemma ext_mbr_simp [simp]: "(declclass m,mbr m) = m"
by (cases m) (simp add: mbr_def)

lemma fname_simp[simp]:"fname (n,c) = n"
by (simp add: fname_def)

lemma declclassf_simp[simp]:"declclassf (n,c) = c"
by (simp add: declclassf_def)

  \<comment> \<open>some mnemotic selectors for \<open>(vname \<times> qtname)\<close>\<close>

definition
  fldname :: "vname \<times> qtname \<Rightarrow> vname"
  where "fldname = fst"

definition
  fldclass :: "vname \<times> qtname \<Rightarrow> qtname"
  where "fldclass = snd"

lemma fldname_simp[simp]: "fldname (n,c) = n"
by (simp add: fldname_def)

lemma fldclass_simp[simp]: "fldclass (n,c) = c"
by (simp add: fldclass_def)

lemma ext_fieldname_simp[simp]: "(fldname f,fldclass f) = f"
by (simp add: fldname_def fldclass_def)

text \<open>Convert a qualified method declaration (qualified with its declaring 
class) to a qualified member declaration:  \<open>methdMembr\<close>\<close>

definition
  methdMembr :: "qtname \<times> mdecl \<Rightarrow> qtname \<times> memberdecl"
  where "methdMembr m = (fst m, mdecl (snd m))"

lemma methdMembr_simp[simp]: "methdMembr (c,m) = (c,mdecl m)"
by (simp add: methdMembr_def)

lemma accmodi_methdMembr_simp[simp]: "accmodi (methdMembr m) = accmodi m"
by (cases m) (simp add: methdMembr_def)

lemma is_static_methdMembr_simp[simp]: "is_static (methdMembr m) = is_static m"
by (cases m) (simp add: methdMembr_def)

lemma declclass_methdMembr_simp[simp]: "declclass (methdMembr m) = declclass m"
by (cases m) (simp add: methdMembr_def)

text \<open>Convert a qualified method (qualified with its declaring 
class) to a qualified member declaration:  \<open>method\<close>\<close>

definition
  "method" :: "sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> (qtname \<times> memberdecl)"
  where "method sig m = (declclass m, mdecl (sig, mthd m))"

lemma method_simp[simp]: "method sig (C,m) = (C,mdecl (sig,m))"
by (simp add: method_def)

lemma accmodi_method_simp[simp]: "accmodi (method sig m) = accmodi m"
by (simp add: method_def)

lemma declclass_method_simp[simp]: "declclass (method sig m) = declclass m"
by (simp add: method_def)

lemma is_static_method_simp[simp]: "is_static (method sig m) = is_static m"
by (cases m) (simp add: method_def)

lemma mbr_method_simp[simp]: "mbr (method sig m) = mdecl (sig,mthd m)"
by (simp add: mbr_def method_def)

lemma memberid_method_simp[simp]:  "memberid (method sig m) = mid sig"
  by (simp add: method_def) 

definition
  fieldm :: "vname \<Rightarrow> (qtname \<times> field) \<Rightarrow> (qtname \<times> memberdecl)"
  where "fieldm n f = (declclass f, fdecl (n, fld f))"

lemma fieldm_simp[simp]: "fieldm n (C,f) = (C,fdecl (n,f))"
by (simp add: fieldm_def)

lemma accmodi_fieldm_simp[simp]: "accmodi (fieldm n f) = accmodi f"
by (simp add: fieldm_def)

lemma declclass_fieldm_simp[simp]: "declclass (fieldm n f) = declclass f"
by (simp add: fieldm_def)

lemma is_static_fieldm_simp[simp]: "is_static (fieldm n f) = is_static f"
by (cases f) (simp add: fieldm_def)

lemma mbr_fieldm_simp[simp]: "mbr (fieldm n f) = fdecl (n,fld f)"
by (simp add: mbr_def fieldm_def)

lemma memberid_fieldm_simp[simp]:  "memberid (fieldm n f) = fid n"
by (simp add: fieldm_def) 

text \<open>Select the signature out of a qualified method declaration:
 \<open>msig\<close>\<close>

definition
  msig :: "(qtname \<times> mdecl) \<Rightarrow> sig"
  where "msig m = fst (snd m)"

lemma msig_simp[simp]: "msig (c,(s,m)) = s"
by (simp add: msig_def)

text \<open>Convert a qualified method (qualified with its declaring 
class) to a qualified method declaration:  \<open>qmdecl\<close>\<close>

definition
  qmdecl :: "sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> (qtname \<times> mdecl)"
  where "qmdecl sig m = (declclass m, (sig,mthd m))"

lemma qmdecl_simp[simp]: "qmdecl sig (C,m) = (C,(sig,m))"
by (simp add: qmdecl_def)

lemma declclass_qmdecl_simp[simp]: "declclass (qmdecl sig m) = declclass m"
by (simp add: qmdecl_def)

lemma accmodi_qmdecl_simp[simp]: "accmodi (qmdecl sig m) = accmodi m"
by (simp add: qmdecl_def)

lemma is_static_qmdecl_simp[simp]: "is_static (qmdecl sig m) = is_static m"
by (cases m) (simp add: qmdecl_def)

lemma msig_qmdecl_simp[simp]: "msig (qmdecl sig m) = sig"
by (simp add: qmdecl_def)

lemma mdecl_qmdecl_simp[simp]:  
 "mdecl (mthd (qmdecl sig new)) = mdecl (sig, mthd new)" 
by (simp add: qmdecl_def) 

lemma methdMembr_qmdecl_simp [simp]: 
 "methdMembr (qmdecl sig old) = method sig old"
by (simp add: methdMembr_def qmdecl_def method_def)

text \<open>overloaded selector \<open>resTy\<close> to select the result type 
out of various HOL types\<close>

class has_resTy =
  fixes resTy:: "'a \<Rightarrow> ty"

instantiation decl_ext :: (has_resTy) has_resTy
begin

instance ..

end

instantiation member_ext :: (has_resTy) has_resTy
begin

instance ..

end

instantiation mhead_ext :: (type) has_resTy
begin

instance ..

end

axiomatization where
  mhead_ext_type_resTy_def: "resTy (m::('b mhead_scheme)) \<equiv> resT m"

lemma mhead_resTy_simp: "resTy (m::'a mhead_scheme) = resT m"
by (simp add: mhead_ext_type_resTy_def)

lemma resTy_mhead [simp]:"resTy (mhead m) = resTy m"
by (simp add: mhead_def mhead_resTy_simp)

instantiation prod :: (type, has_resTy) has_resTy
begin

definition
  pair_resTy_def: "resTy p = resTy (snd p)"

instance ..

end

lemma pair_resTy_simp[simp]: "resTy (x,m) = resTy m"
by (simp add: pair_resTy_def)

lemma qmdecl_resTy_simp [simp]: "resTy (qmdecl sig m) = resTy m"
by (cases m) (simp)

lemma resTy_mthd [simp]:"resTy (mthd m) = resTy m"
by (cases m) (simp add: mthd_def )

subsubsection "inheritable-in"
text \<open>
\<open>G\<turnstile>m inheritable_in P\<close>: m can be inherited by
classes in package P if:
\begin{itemize} 
\item the declaration class of m is accessible in P and
\item the member m is declared with protected or public access or if it is
      declared with default (package) access, the package of the declaration 
      class of m is also P. If the member m is declared with private access
      it is not accessible for inheritance at all.
\end{itemize}
\<close>
definition
  inheritable_in :: "prog \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> pname \<Rightarrow> bool" (\<open>_ \<turnstile> _ inheritable'_in _\<close> [61,61,61] 60)
where
"G\<turnstile>membr inheritable_in pack =
  (case (accmodi membr) of
     Private   \<Rightarrow> False
   | Package   \<Rightarrow> (pid (declclass membr)) = pack
   | Protected \<Rightarrow> True
   | Public    \<Rightarrow> True)"

abbreviation
Method_inheritable_in_syntax::
 "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> pname \<Rightarrow> bool"
                (\<open>_ \<turnstile>Method _ inheritable'_in _ \<close> [61,61,61] 60)
 where "G\<turnstile>Method m inheritable_in p == G\<turnstile>methdMembr m inheritable_in p"

abbreviation
Methd_inheritable_in::
 "prog \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> pname \<Rightarrow> bool"
                (\<open>_ \<turnstile>Methd _ _ inheritable'_in _ \<close> [61,61,61,61] 60)
 where "G\<turnstile>Methd s m inheritable_in p == G\<turnstile>(method s m) inheritable_in p"

subsubsection "declared-in/undeclared-in"

definition
  cdeclaredmethd :: "prog \<Rightarrow> qtname \<Rightarrow> (sig,methd) table" where
  "cdeclaredmethd G C =
    (case class G C of
       None \<Rightarrow> \<lambda> sig. None
     | Some c \<Rightarrow> table_of (methods c))"

definition
  cdeclaredfield :: "prog \<Rightarrow> qtname \<Rightarrow> (vname,field) table" where
  "cdeclaredfield G C =
    (case class G C of
      None \<Rightarrow> \<lambda> sig. None
    | Some c \<Rightarrow> table_of (cfields c))"

definition
  declared_in :: "prog  \<Rightarrow> memberdecl \<Rightarrow> qtname \<Rightarrow> bool" (\<open>_\<turnstile> _ declared'_in _\<close> [61,61,61] 60)
where
  "G\<turnstile>m declared_in C = (case m of
                          fdecl (fn,f ) \<Rightarrow> cdeclaredfield G C fn  = Some f
                        | mdecl (sig,m) \<Rightarrow> cdeclaredmethd G C sig = Some m)"

abbreviation
method_declared_in:: "prog  \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> qtname \<Rightarrow> bool"
                                 (\<open>_\<turnstile>Method _ declared'_in _\<close> [61,61,61] 60)
 where "G\<turnstile>Method m declared_in C == G\<turnstile>mdecl (mthd m) declared_in C"

abbreviation
methd_declared_in:: "prog  \<Rightarrow> sig  \<Rightarrow>(qtname \<times> methd) \<Rightarrow> qtname \<Rightarrow> bool"
                               (\<open>_\<turnstile>Methd _  _ declared'_in _\<close> [61,61,61,61] 60)
 where "G\<turnstile>Methd s m declared_in C == G\<turnstile>mdecl (s,mthd m) declared_in C"

lemma declared_in_classD:
 "G\<turnstile>m declared_in C \<Longrightarrow> is_class G C"
by (cases m) 
   (auto simp add: declared_in_def cdeclaredmethd_def cdeclaredfield_def)

definition
  undeclared_in :: "prog  \<Rightarrow> memberid \<Rightarrow> qtname \<Rightarrow> bool" (\<open>_\<turnstile> _ undeclared'_in _\<close> [61,61,61] 60)
where
  "G\<turnstile>m undeclared_in C = (case m of
                           fid fn  \<Rightarrow> cdeclaredfield G C fn  = None
                         | mid sig \<Rightarrow> cdeclaredmethd G C sig = None)"


subsubsection "members"

(* Can't just take a function: prog \<Rightarrow> qtname \<Rightarrow> memberdecl set because
   the class qtname changes to the superclass in the inductive definition
   below
*)

inductive
  members :: "prog \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> bool"
    (\<open>_ \<turnstile> _ member'_of _\<close> [61,61,61] 60)
  for G :: prog
where

  Immediate: "\<lbrakk>G\<turnstile>mbr m declared_in C;declclass m = C\<rbrakk> \<Longrightarrow> G\<turnstile>m member_of C"
| Inherited: "\<lbrakk>G\<turnstile>m inheritable_in (pid C); G\<turnstile>memberid m undeclared_in C; 
               G\<turnstile>C \<prec>\<^sub>C1 S; G\<turnstile>(Class S) accessible_in (pid C);G\<turnstile>m member_of S 
              \<rbrakk> \<Longrightarrow> G\<turnstile>m member_of C"
text \<open>Note that in the case of an inherited member only the members of the
direct superclass are concerned. If a member of a superclass of the direct
superclass isn't inherited in the direct superclass (not member of the
direct superclass) than it can't be a member of the class. E.g. If a
member of a class A is defined with package access it isn't member of a 
subclass S if S isn't in the same package as A. Any further subclasses 
of S will not inherit the member, regardless if they are in the same
package as A or not.\<close>

abbreviation
method_member_of:: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> qtname \<Rightarrow> bool"
                           (\<open>_ \<turnstile>Method _ member'_of _\<close> [61,61,61] 60)
 where "G\<turnstile>Method m member_of C == G\<turnstile>(methdMembr m) member_of C"

abbreviation
methd_member_of:: "prog \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> qtname \<Rightarrow> bool"
                           (\<open>_ \<turnstile>Methd _ _ member'_of _\<close> [61,61,61,61] 60)
 where "G\<turnstile>Methd s m member_of C == G\<turnstile>(method s m) member_of C" 

abbreviation
fieldm_member_of:: "prog \<Rightarrow> vname \<Rightarrow> (qtname \<times> field) \<Rightarrow> qtname \<Rightarrow> bool"
                           (\<open>_ \<turnstile>Field _  _ member'_of _\<close> [61,61,61] 60)
 where "G\<turnstile>Field n f member_of C == G\<turnstile>fieldm n f member_of C"

definition
  inherits :: "prog \<Rightarrow> qtname \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> bool" (\<open>_ \<turnstile> _ inherits _\<close> [61,61,61] 60)
where
  "G\<turnstile>C inherits m =
    (G\<turnstile>m inheritable_in (pid C) \<and> G\<turnstile>memberid m undeclared_in C \<and> 
      (\<exists>S. G\<turnstile>C \<prec>\<^sub>C1 S \<and> G\<turnstile>(Class S) accessible_in (pid C) \<and> G\<turnstile>m member_of S))"

lemma inherits_member: "G\<turnstile>C inherits m \<Longrightarrow> G\<turnstile>m member_of C"
by (auto simp add: inherits_def intro: members.Inherited)


definition
  member_in :: "prog \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> bool" (\<open>_ \<turnstile> _ member'_in _\<close> [61,61,61] 60)
  where "G\<turnstile>m member_in C = (\<exists> provC. G\<turnstile> C \<preceq>\<^sub>C provC \<and> G \<turnstile> m member_of provC)"
text \<open>A member is in a class if it is member of the class or a superclass.
If a member is in a class we can select this member. This additional notion
is necessary since not all members are inherited to subclasses. So such
members are not member-of the subclass but member-in the subclass.\<close>

abbreviation
method_member_in:: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> qtname \<Rightarrow> bool"
                           (\<open>_ \<turnstile>Method _ member'_in _\<close> [61,61,61] 60)
 where "G\<turnstile>Method m member_in C == G\<turnstile>(methdMembr m) member_in C"

abbreviation
methd_member_in:: "prog \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> qtname \<Rightarrow> bool"
                           (\<open>_ \<turnstile>Methd _ _ member'_in _\<close> [61,61,61,61] 60)
 where "G\<turnstile>Methd s m member_in C == G\<turnstile>(method s m) member_in C"

lemma member_inD: "G\<turnstile>m member_in C 
 \<Longrightarrow> \<exists> provC. G\<turnstile> C \<preceq>\<^sub>C provC \<and> G \<turnstile> m member_of provC"
by (auto simp add: member_in_def)

lemma member_inI: "\<lbrakk>G \<turnstile> m member_of provC;G\<turnstile> C \<preceq>\<^sub>C provC\<rbrakk> \<Longrightarrow>  G\<turnstile>m member_in C"
by (auto simp add: member_in_def)

lemma member_of_to_member_in: "G \<turnstile> m member_of C \<Longrightarrow> G \<turnstile>m member_in C"
by (auto intro: member_inI)


subsubsection "overriding"

text \<open>Unfortunately the static notion of overriding (used during the
typecheck of the compiler) and the dynamic notion of overriding (used during
execution in the JVM) are not exactly the same. 
\<close>

text \<open>Static overriding (used during the typecheck of the compiler)\<close>

inductive
  stat_overridesR :: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> bool"
    (\<open>_ \<turnstile> _ overrides\<^sub>S _\<close> [61,61,61] 60)
  for G :: prog
where

  Direct: "\<lbrakk>\<not> is_static new; msig new = msig old; 
           G\<turnstile>Method new declared_in (declclass new);  
           G\<turnstile>Method old declared_in (declclass old); 
           G\<turnstile>Method old inheritable_in pid (declclass new);
           G\<turnstile>(declclass new) \<prec>\<^sub>C1 superNew;
           G \<turnstile>Method old member_of superNew
           \<rbrakk> \<Longrightarrow> G\<turnstile>new overrides\<^sub>S old"

| Indirect: "\<lbrakk>G\<turnstile>new overrides\<^sub>S intr; G\<turnstile>intr overrides\<^sub>S old\<rbrakk>
             \<Longrightarrow> G\<turnstile>new overrides\<^sub>S old"

text \<open>Dynamic overriding (used during the typecheck of the compiler)\<close>

inductive
  overridesR :: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> bool"
    (\<open>_ \<turnstile> _ overrides _\<close> [61,61,61] 60)
  for G :: prog
where

  Direct: "\<lbrakk>\<not> is_static new; \<not> is_static old; accmodi new \<noteq> Private;
           msig new = msig old; 
           G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old);
           G\<turnstile>Method new declared_in (declclass new);  
           G\<turnstile>Method old declared_in (declclass old);    
           G\<turnstile>Method old inheritable_in pid (declclass new);
           G\<turnstile>resTy new \<preceq> resTy old
           \<rbrakk> \<Longrightarrow> G\<turnstile>new overrides old"

| Indirect: "\<lbrakk>G\<turnstile>new overrides intr; G\<turnstile>intr overrides old\<rbrakk>
            \<Longrightarrow> G\<turnstile>new overrides old"

abbreviation (input)
sig_stat_overrides:: 
 "prog  \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> (qtname \<times> methd) \<Rightarrow> bool" 
                                  (\<open>_,_\<turnstile> _ overrides\<^sub>S _\<close> [61,61,61,61] 60)
 where "G,s\<turnstile>new overrides\<^sub>S old == G\<turnstile>(qmdecl s new) overrides\<^sub>S (qmdecl s old)" 

abbreviation (input)
sig_overrides:: "prog  \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> (qtname \<times> methd) \<Rightarrow> bool" 
                                  (\<open>_,_\<turnstile> _ overrides _\<close> [61,61,61,61] 60)
 where "G,s\<turnstile>new overrides old == G\<turnstile>(qmdecl s new) overrides (qmdecl s old)"

subsubsection "Hiding"

definition
  hides :: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> bool" (\<open>_\<turnstile> _ hides _\<close> [61,61,61] 60)
where 
  "G\<turnstile>new hides old =
    (is_static new \<and> msig new = msig old \<and>
      G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old) \<and>
      G\<turnstile>Method new declared_in (declclass new) \<and>
      G\<turnstile>Method old declared_in (declclass old) \<and> 
      G\<turnstile>Method old inheritable_in pid (declclass new))"

abbreviation
sig_hides:: "prog  \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> (qtname \<times> methd) \<Rightarrow> bool" 
                                  (\<open>_,_\<turnstile> _ hides _\<close> [61,61,61,61] 60)
 where "G,s\<turnstile>new hides old == G\<turnstile>(qmdecl s new) hides (qmdecl s old)"

lemma hidesI:
"\<lbrakk>is_static new; msig new = msig old;
  G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old);
  G\<turnstile>Method new declared_in (declclass new);
  G\<turnstile>Method old declared_in (declclass old);
  G\<turnstile>Method old inheritable_in pid (declclass new)
 \<rbrakk> \<Longrightarrow> G\<turnstile>new hides old"
by (auto simp add: hides_def)

lemma hidesD:
"\<lbrakk>G\<turnstile>new hides old\<rbrakk> \<Longrightarrow>  
  declclass new \<noteq> Object \<and> is_static new \<and> msig new = msig old \<and> 
  G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old) \<and>
  G\<turnstile>Method new declared_in (declclass new) \<and>   
  G\<turnstile>Method old declared_in (declclass old)"
by (auto simp add: hides_def)

lemma overrides_commonD:
"\<lbrakk>G\<turnstile>new overrides old\<rbrakk> \<Longrightarrow>  
  declclass new \<noteq> Object \<and> \<not> is_static new \<and> \<not> is_static old \<and>
  accmodi new \<noteq> Private \<and> 
  msig new = msig old  \<and>
  G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old) \<and>
  G\<turnstile>Method new declared_in (declclass new) \<and>   
  G\<turnstile>Method old declared_in (declclass old)"
by (induct set: overridesR) (auto intro: trancl_trans)

lemma ws_overrides_commonD:
"\<lbrakk>G\<turnstile>new overrides old;ws_prog G\<rbrakk> \<Longrightarrow>  
  declclass new \<noteq> Object \<and> \<not> is_static new \<and> \<not> is_static old \<and>
  accmodi new \<noteq> Private \<and> G\<turnstile>resTy new \<preceq> resTy old \<and>
  msig new = msig old  \<and>
  G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old) \<and>
  G\<turnstile>Method new declared_in (declclass new) \<and>   
  G\<turnstile>Method old declared_in (declclass old)"
by (induct set: overridesR) (auto intro: trancl_trans ws_widen_trans)

lemma overrides_eq_sigD: 
 "\<lbrakk>G\<turnstile>new overrides old\<rbrakk> \<Longrightarrow> msig old=msig new"
by (auto dest: overrides_commonD)

lemma hides_eq_sigD: 
 "\<lbrakk>G\<turnstile>new hides old\<rbrakk> \<Longrightarrow> msig old=msig new"
by (auto simp add: hides_def)

subsubsection "permits access" 
definition
  permits_acc :: "prog \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool" (\<open>_ \<turnstile> _ in _ permits'_acc'_from _\<close> [61,61,61,61] 60)
where
  "G\<turnstile>membr in cls permits_acc_from accclass =
    (case (accmodi membr) of
      Private   \<Rightarrow> (declclass membr = accclass)
    | Package   \<Rightarrow> (pid (declclass membr) = pid accclass)
    | Protected \<Rightarrow> (pid (declclass membr) = pid accclass)
                    \<or>
                    (G\<turnstile>accclass \<prec>\<^sub>C declclass membr 
                     \<and> (G\<turnstile>cls \<preceq>\<^sub>C accclass \<or> is_static membr)) 
    | Public    \<Rightarrow> True)"
text \<open>
The subcondition of the \<^term>\<open>Protected\<close> case: 
\<^term>\<open>G\<turnstile>accclass \<prec>\<^sub>C declclass membr\<close> could also be relaxed to:
\<^term>\<open>G\<turnstile>accclass \<preceq>\<^sub>C declclass membr\<close> since in case both classes are the
same the other condition \<^term>\<open>(pid (declclass membr) = pid accclass)\<close>
holds anyway.
\<close> 

text \<open>Like in case of overriding, the static and dynamic accessibility 
of members is not uniform.
\begin{itemize}
\item Statically the class/interface of the member must be accessible for the
      member to be accessible. During runtime this is not necessary. For
      Example, if a class is accessible and we are allowed to access a member
      of this class (statically) we expect that we can access this member in 
      an arbitrary subclass (during runtime). It's not intended to restrict
      the access to accessible subclasses during runtime.
\item Statically the member we want to access must be "member of" the class.
      Dynamically it must only be "member in" the class.
\end{itemize} 
\<close> 

inductive
  accessible_fromR :: "prog \<Rightarrow> qtname \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> bool"
  and accessible_from :: "prog \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
    (\<open>_ \<turnstile> _ of _ accessible'_from _\<close> [61,61,61,61] 60)
  and method_accessible_from :: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
    (\<open>_ \<turnstile>Method _ of _ accessible'_from _\<close> [61,61,61,61] 60)
  for G :: prog and accclass :: qtname
where
  "G\<turnstile>membr of cls accessible_from accclass \<equiv> accessible_fromR G accclass membr cls"

| "G\<turnstile>Method m of cls accessible_from accclass \<equiv> accessible_fromR G accclass (methdMembr m) cls"

| Immediate:  "!!membr class.
               \<lbrakk>G\<turnstile>membr member_of class;
                G\<turnstile>(Class class) accessible_in (pid accclass);
                G\<turnstile>membr in class permits_acc_from accclass 
               \<rbrakk> \<Longrightarrow> G\<turnstile>membr of class accessible_from accclass"

| Overriding: "!!membr class C new old supr.
               \<lbrakk>G\<turnstile>membr member_of class;
                G\<turnstile>(Class class) accessible_in (pid accclass);
                membr=(C,mdecl new);
                G\<turnstile>(C,new) overrides\<^sub>S old; 
                G\<turnstile>class \<prec>\<^sub>C supr;
                G\<turnstile>Method old of supr accessible_from accclass
               \<rbrakk>\<Longrightarrow> G\<turnstile>membr of class accessible_from accclass"

abbreviation
methd_accessible_from:: 
 "prog \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
                 (\<open>_ \<turnstile>Methd _ _ of _ accessible'_from _\<close> [61,61,61,61,61] 60)
 where
 "G\<turnstile>Methd s m of cls accessible_from accclass ==
   G\<turnstile>(method s m) of cls accessible_from accclass"

abbreviation
field_accessible_from:: 
 "prog \<Rightarrow> vname \<Rightarrow> (qtname \<times> field) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
                 (\<open>_ \<turnstile>Field _  _ of _ accessible'_from _\<close> [61,61,61,61,61] 60)
 where
 "G\<turnstile>Field fn f of C accessible_from accclass ==
  G\<turnstile>(fieldm fn f) of C accessible_from accclass"

inductive
  dyn_accessible_fromR :: "prog \<Rightarrow> qtname \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> bool"
  and dyn_accessible_from' ::  "prog \<Rightarrow> (qtname \<times> memberdecl) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
    (\<open>_ \<turnstile> _ in _ dyn'_accessible'_from _\<close> [61,61,61,61] 60)
  and method_dyn_accessible_from :: "prog \<Rightarrow> (qtname \<times> mdecl) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
    (\<open>_ \<turnstile>Method _ in _ dyn'_accessible'_from _\<close> [61,61,61,61] 60)
  for G :: prog and accclass :: qtname
where
  "G\<turnstile>membr in C dyn_accessible_from accC \<equiv> dyn_accessible_fromR G accC membr C"

| "G\<turnstile>Method m in C dyn_accessible_from accC \<equiv> dyn_accessible_fromR G accC (methdMembr m) C"

| Immediate:  "!!class. \<lbrakk>G\<turnstile>membr member_in class;
                G\<turnstile>membr in class permits_acc_from accclass 
               \<rbrakk> \<Longrightarrow> G\<turnstile>membr in class dyn_accessible_from accclass"

| Overriding: "!!class. \<lbrakk>G\<turnstile>membr member_in class;
                membr=(C,mdecl new);
                G\<turnstile>(C,new) overrides old; 
                G\<turnstile>class \<prec>\<^sub>C supr;
                G\<turnstile>Method old in supr dyn_accessible_from accclass
               \<rbrakk>\<Longrightarrow> G\<turnstile>membr in class dyn_accessible_from accclass"

abbreviation
methd_dyn_accessible_from:: 
 "prog \<Rightarrow> sig \<Rightarrow> (qtname \<times> methd) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
             (\<open>_ \<turnstile>Methd _ _ in _ dyn'_accessible'_from _\<close> [61,61,61,61,61] 60)
 where
 "G\<turnstile>Methd s m in C dyn_accessible_from accC ==
  G\<turnstile>(method s m) in C dyn_accessible_from accC"  

abbreviation
field_dyn_accessible_from:: 
 "prog \<Rightarrow> vname \<Rightarrow> (qtname \<times> field) \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
         (\<open>_ \<turnstile>Field _ _ in _ dyn'_accessible'_from _\<close> [61,61,61,61,61] 60)
 where
 "G\<turnstile>Field fn f in dynC dyn_accessible_from accC ==
  G\<turnstile>(fieldm fn f) in dynC dyn_accessible_from accC"


lemma accessible_from_commonD: "G\<turnstile>m of C accessible_from S
 \<Longrightarrow> G\<turnstile>m member_of C \<and> G\<turnstile>(Class C) accessible_in (pid S)"
by (auto elim: accessible_fromR.induct)

lemma unique_declaration: 
 "\<lbrakk>G\<turnstile>m declared_in C;  G\<turnstile>n declared_in C; memberid m = memberid n \<rbrakk> 
  \<Longrightarrow> m = n"
apply (cases m)
apply (cases n,
        auto simp add: declared_in_def cdeclaredmethd_def cdeclaredfield_def)+
done

lemma declared_not_undeclared:
  "G\<turnstile>m declared_in C \<Longrightarrow> \<not> G\<turnstile> memberid m undeclared_in C"
by (cases m) (auto simp add: declared_in_def undeclared_in_def)

lemma undeclared_not_declared:
 "G\<turnstile> memberid m undeclared_in C \<Longrightarrow> \<not> G\<turnstile> m declared_in C" 
by (cases m) (auto simp add: declared_in_def undeclared_in_def)

lemma not_undeclared_declared:
  "\<not> G\<turnstile> membr_id undeclared_in C \<Longrightarrow> (\<exists> m. G\<turnstile>m declared_in C \<and> 
                                           membr_id = memberid m)"
proof -
  assume not_undecl:"\<not> G\<turnstile> membr_id undeclared_in C"
  show ?thesis (is "?P membr_id")
  proof (cases membr_id)
    case (fid vname)
    with not_undecl
    obtain fld where
      "G\<turnstile>fdecl (vname,fld) declared_in C" 
      by (auto simp add: undeclared_in_def declared_in_def
                         cdeclaredfield_def)
    with fid show ?thesis 
      by auto
  next
    case (mid sig)
    with not_undecl
    obtain mthd where
      "G\<turnstile>mdecl (sig,mthd) declared_in C" 
      by (auto simp add: undeclared_in_def declared_in_def
                         cdeclaredmethd_def)
    with mid show ?thesis 
      by auto
  qed
qed

lemma unique_declared_in:
 "\<lbrakk>G\<turnstile>m declared_in C; G\<turnstile>n declared_in C; memberid m = memberid n\<rbrakk>
 \<Longrightarrow> m = n"
by (auto simp add: declared_in_def cdeclaredmethd_def cdeclaredfield_def
            split: memberdecl.splits)

lemma unique_member_of: 
  assumes n: "G\<turnstile>n member_of C" and  
          m: "G\<turnstile>m member_of C" and
       eqid: "memberid n = memberid m"
  shows "n=m"
proof -
  from n m eqid  
  show "n=m"
  proof (induct)
    case (Immediate n C)
    assume member_n: "G\<turnstile> mbr n declared_in C" "declclass n = C"
    assume eqid: "memberid n = memberid m"
    assume "G \<turnstile> m member_of C"
    then show "n=m"
    proof (cases)
      case Immediate
      with eqid member_n
      show ?thesis
        by (cases n, cases m) 
           (auto simp add: declared_in_def 
                           cdeclaredmethd_def cdeclaredfield_def
                    split: memberdecl.splits)
    next
      case Inherited
      with eqid member_n
      show ?thesis
        by (cases n) (auto dest: declared_not_undeclared)
    qed
  next
    case (Inherited n C S)
    assume undecl: "G\<turnstile> memberid n undeclared_in C"
    assume  super: "G\<turnstile>C\<prec>\<^sub>C1S"
    assume    hyp: "\<lbrakk>G \<turnstile> m member_of S; memberid n = memberid m\<rbrakk> \<Longrightarrow> n = m"
    assume   eqid: "memberid n = memberid m"
    assume "G \<turnstile> m member_of C"
    then show "n=m"
    proof (cases)
      case Immediate
      then have "G\<turnstile> mbr m declared_in C" by simp
      with eqid undecl
      show ?thesis
        by (cases m) (auto dest: declared_not_undeclared)
    next
      case Inherited 
      with super have "G \<turnstile> m member_of S"
        by (auto dest!: subcls1D)
      with eqid hyp
      show ?thesis 
        by blast
    qed
  qed
qed

lemma member_of_is_classD: "G\<turnstile>m member_of C \<Longrightarrow> is_class G C"
proof (induct set: members)
  case (Immediate m C)
  assume "G\<turnstile> mbr m declared_in C"
  then show "is_class G C"
    by (cases "mbr m")
       (auto simp add: declared_in_def cdeclaredmethd_def cdeclaredfield_def)
next
  case (Inherited m C S)  
  show "is_class G C" if "G\<turnstile>C\<prec>\<^sub>C1S" and "is_class G S"
    by (rule subcls_is_class2) (use that in auto)
qed

lemma member_of_declC: 
 "G\<turnstile>m member_of C 
  \<Longrightarrow> G\<turnstile>mbr m declared_in (declclass m)"
by (induct set: members) auto

lemma member_of_member_of_declC:
 "G\<turnstile>m member_of C 
  \<Longrightarrow> G\<turnstile>m member_of (declclass m)"
by (auto dest: member_of_declC intro: members.Immediate)

lemma member_of_class_relation:
  "G\<turnstile>m member_of C \<Longrightarrow> G\<turnstile>C \<preceq>\<^sub>C declclass m"
proof (induct set: members)
  case (Immediate m C)
  then show "G\<turnstile>C \<preceq>\<^sub>C declclass m" by simp
next
  case (Inherited m C S)
  then show "G\<turnstile>C \<preceq>\<^sub>C declclass m" 
    by (auto dest: r_into_rtrancl intro: rtrancl_trans)
qed

lemma member_in_class_relation:
  "G\<turnstile>m member_in C \<Longrightarrow> G\<turnstile>C \<preceq>\<^sub>C declclass m"
by (auto dest: member_inD member_of_class_relation
        intro: rtrancl_trans)

lemma stat_override_declclasses_relation: 
"\<lbrakk>G\<turnstile>(declclass new) \<prec>\<^sub>C1 superNew; G \<turnstile>Method old member_of superNew \<rbrakk>
\<Longrightarrow> G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old)"
apply (rule trancl_rtrancl_trancl)
apply (erule r_into_trancl)
apply (cases old)
apply (auto dest: member_of_class_relation)
done

lemma stat_overrides_commonD:
"\<lbrakk>G\<turnstile>new overrides\<^sub>S old\<rbrakk> \<Longrightarrow>  
  declclass new \<noteq> Object \<and> \<not> is_static new \<and> msig new = msig old \<and> 
  G\<turnstile>(declclass new) \<prec>\<^sub>C (declclass old) \<and>
  G\<turnstile>Method new declared_in (declclass new) \<and>   
  G\<turnstile>Method old declared_in (declclass old)"
apply (induct set: stat_overridesR) 
apply (frule (1) stat_override_declclasses_relation) 
apply (auto intro: trancl_trans)
done

lemma member_of_Package: 
  assumes "G\<turnstile>m member_of C"
    and "accmodi m = Package"
  shows "pid (declclass m) = pid C"
  using assms
proof induct
  case Immediate
  then show ?case by simp
next
  case Inherited
  then show ?case by (auto simp add: inheritable_in_def)
qed

lemma member_in_declC: "G\<turnstile>m member_in C\<Longrightarrow> G\<turnstile>m member_in (declclass m)"
proof -
  assume member_in_C:  "G\<turnstile>m member_in C"
  from member_in_C
  obtain provC where
    subclseq_C_provC: "G\<turnstile> C \<preceq>\<^sub>C provC" and
     member_of_provC: "G \<turnstile> m member_of provC"
    by (auto simp add: member_in_def)
  from member_of_provC
  have "G \<turnstile> m member_of declclass m"
    by (rule member_of_member_of_declC)
  moreover
  from member_in_C
  have "G\<turnstile>C \<preceq>\<^sub>C declclass m"
    by (rule member_in_class_relation)
  ultimately
  show ?thesis
    by (auto simp add: member_in_def)
qed

lemma dyn_accessible_from_commonD: "G\<turnstile>m in C dyn_accessible_from S
 \<Longrightarrow> G\<turnstile>m member_in C"
by (auto elim: dyn_accessible_fromR.induct)

lemma no_Private_stat_override: 
 "\<lbrakk>G\<turnstile>new overrides\<^sub>S old\<rbrakk> \<Longrightarrow> accmodi old \<noteq> Private"
by (induct set:  stat_overridesR) (auto simp add: inheritable_in_def)

lemma no_Private_override: "\<lbrakk>G\<turnstile>new overrides old\<rbrakk> \<Longrightarrow> accmodi old \<noteq> Private"
by (induct set: overridesR) (auto simp add: inheritable_in_def)

lemma permits_acc_inheritance:
 "\<lbrakk>G\<turnstile>m in statC permits_acc_from accC; G\<turnstile>dynC \<preceq>\<^sub>C statC
  \<rbrakk> \<Longrightarrow> G\<turnstile>m in dynC permits_acc_from accC"
by (cases "accmodi m")
   (auto simp add: permits_acc_def
            intro: subclseq_trans) 

lemma permits_acc_static_declC:
 "\<lbrakk>G\<turnstile>m in C permits_acc_from accC; G\<turnstile>m member_in C; is_static m
  \<rbrakk> \<Longrightarrow> G\<turnstile>m in (declclass m) permits_acc_from accC"
by (cases "accmodi m") (auto simp add: permits_acc_def)

lemma dyn_accessible_from_static_declC: 
  assumes  acc_C: "G\<turnstile>m in C dyn_accessible_from accC" and
           static: "is_static m"
  shows "G\<turnstile>m in (declclass m) dyn_accessible_from accC"
proof -
  from acc_C static
  show "G\<turnstile>m in (declclass m) dyn_accessible_from accC"
  proof (induct)
    case (Immediate m C)
    then show ?case 
      by (auto intro!: dyn_accessible_fromR.Immediate
                 dest: member_in_declC permits_acc_static_declC) 
  next 
    case (Overriding m C declCNew new old sup)
    then have "\<not> is_static m"
      by (auto dest: overrides_commonD)
    moreover
    assume "is_static m"
    ultimately show ?case 
      by contradiction
  qed
qed

lemma field_accessible_fromD:
 "\<lbrakk>G\<turnstile>membr of C accessible_from accC;is_field membr\<rbrakk> 
  \<Longrightarrow> G\<turnstile>membr member_of C \<and>
      G\<turnstile>(Class C) accessible_in (pid accC) \<and>
      G\<turnstile>membr in C permits_acc_from accC"
by (cases set: accessible_fromR)
   (auto simp add: is_field_def split: memberdecl.splits) 

lemma field_accessible_from_permits_acc_inheritance:
"\<lbrakk>G\<turnstile>membr of statC accessible_from accC; is_field membr; G \<turnstile> dynC \<preceq>\<^sub>C statC\<rbrakk>
\<Longrightarrow> G\<turnstile>membr in dynC permits_acc_from accC"
by (auto dest: field_accessible_fromD intro: permits_acc_inheritance)


(*
lemma accessible_Package:
 "\<lbrakk>G \<turnstile> m of C accessible_from S;accmodi m = Package;
   \<And> new old. G\<turnstile>new overrides\<^sub>S old \<Longrightarrow> accmodi old \<le> accmodi new\<rbrakk>
  \<Longrightarrow> pid S = pid C \<and> pid C = pid (declclass m)"
proof -
  assume wf: "\<And> new old. G\<turnstile>new overrides\<^sub>S old \<Longrightarrow> accmodi old \<le> accmodi new"
  assume "G \<turnstile> m of C accessible_from S"
  then show "accmodi m = Package \<Longrightarrow> pid S = pid C \<and> pid C = pid (declclass m)"
    (is "?Pack m \<Longrightarrow> ?P C m")
  proof (induct rule: accessible_fromR.induct)
    fix C m
    assume "G\<turnstile>m member_of C"
           "G \<turnstile> m in C permits_acc_from S"
           "accmodi m = Package"      
    then show "?P C m"
      by (auto dest: member_of_Package simp add: permits_acc_def)
  next
    fix declC C new newm old Sup
    assume member_new: "G \<turnstile> new member_of C" and 
                acc_C: "G \<turnstile> Class C accessible_in pid S" and
                  new: "new = (declC, mdecl newm)" and
             override: "G \<turnstile> (declC, newm) overrides\<^sub>S old" and
         subcls_C_Sup: "G\<turnstile>C \<prec>\<^sub>C Sup" and
              acc_old: "G \<turnstile> methdMembr old of Sup accessible_from S" and
                  hyp: "?Pack (methdMembr old) \<Longrightarrow> ?P Sup (methdMembr old)" and
          accmodi_new: "accmodi new = Package"
    from override wf 
    have accmodi_weaken: "accmodi old \<le> accmodi newm"
      by (cases old,cases newm) auto
    from override new
    have "accmodi old \<noteq> Private"
      by (simp add: no_Private_stat_override)
    with accmodi_weaken accmodi_new new
    have accmodi_old: "accmodi old = Package"
      by (cases "accmodi old") (auto simp add: le_acc_def less_acc_def) 
    with hyp 
    have P_sup: "?P Sup (methdMembr old)"
      by (simp)
    from wf override new accmodi_old accmodi_new
    have eq_pid_new_old: "pid (declclass new) = pid (declclass old)"
      by (auto dest: stat_override_Package) 
    from member_new accmodi_new
    have "pid (declclass new) = pid C"
      by (auto dest: member_of_Package)
    with eq_pid_new_old P_sup show "?P C new"
      by auto
  qed
qed
*)

lemma accessible_fieldD: 
 "\<lbrakk>G\<turnstile>membr of C accessible_from accC; is_field membr\<rbrakk>
 \<Longrightarrow> G\<turnstile>membr member_of C \<and>
     G\<turnstile>(Class C) accessible_in (pid accC) \<and>
     G\<turnstile>membr in C permits_acc_from accC"
by (induct rule: accessible_fromR.induct) (auto dest: is_fieldD)
      


lemma member_of_Private:
"\<lbrakk>G\<turnstile>m member_of C; accmodi m = Private\<rbrakk> \<Longrightarrow> declclass m = C"
by (induct set: members) (auto simp add: inheritable_in_def)

lemma member_of_subclseq_declC:
  "G\<turnstile>m member_of C \<Longrightarrow> G\<turnstile>C \<preceq>\<^sub>C declclass m"
by (induct set: members) (auto dest: r_into_rtrancl intro: rtrancl_trans)

lemma member_of_inheritance:
  assumes       m: "G\<turnstile>m member_of D" and
     subclseq_D_C: "G\<turnstile>D \<preceq>\<^sub>C C" and
     subclseq_C_m: "G\<turnstile>C \<preceq>\<^sub>C declclass m" and
               ws: "ws_prog G" 
  shows "G\<turnstile>m member_of C"
proof -
  from m subclseq_D_C subclseq_C_m
  show ?thesis
  proof (induct)
    case (Immediate m D)
    assume "declclass m = D" and
           "G\<turnstile>D\<preceq>\<^sub>C C" and "G\<turnstile>C\<preceq>\<^sub>C declclass m"
    with ws have "D=C" 
      by (auto intro: subclseq_acyclic)
    with Immediate 
    show "G\<turnstile>m member_of C"
      by (auto intro: members.Immediate)
  next
    case (Inherited m D S)
    assume member_of_D_props: 
            "G \<turnstile> m inheritable_in pid D" 
            "G\<turnstile> memberid m undeclared_in D"  
            "G \<turnstile> Class S accessible_in pid D" 
            "G \<turnstile> m member_of S"
    assume super: "G\<turnstile>D\<prec>\<^sub>C1S"
    assume hyp: "\<lbrakk>G\<turnstile>S\<preceq>\<^sub>C C; G\<turnstile>C\<preceq>\<^sub>C declclass m\<rbrakk> \<Longrightarrow> G \<turnstile> m member_of C"
    assume subclseq_C_m: "G\<turnstile>C\<preceq>\<^sub>C declclass m"
    assume "G\<turnstile>D\<preceq>\<^sub>C C"
    then show "G\<turnstile>m member_of C"
    proof (cases rule: subclseq_cases)
      case Eq
      assume "D=C" 
      with super member_of_D_props 
      show ?thesis
        by (auto intro: members.Inherited)
    next
      case Subcls
      assume "G\<turnstile>D\<prec>\<^sub>C C"
      with super 
      have "G\<turnstile>S\<preceq>\<^sub>C C"
        by (auto dest: subcls1D subcls_superD)
      with subclseq_C_m hyp show ?thesis
        by blast
    qed
  qed
qed

lemma member_of_subcls:
  assumes     old: "G\<turnstile>old member_of C" and 
              new: "G\<turnstile>new member_of D" and
             eqid: "memberid new = memberid old" and
     subclseq_D_C: "G\<turnstile>D \<preceq>\<^sub>C C" and 
   subcls_new_old: "G\<turnstile>declclass new \<prec>\<^sub>C declclass old" and
               ws: "ws_prog G"
  shows "G\<turnstile>D \<prec>\<^sub>C C"
proof -
  from old 
  have subclseq_C_old: "G\<turnstile>C \<preceq>\<^sub>C declclass old"
    by (auto dest: member_of_subclseq_declC)
  from new 
  have subclseq_D_new: "G\<turnstile>D \<preceq>\<^sub>C declclass new"
    by (auto dest: member_of_subclseq_declC)
  from subcls_new_old ws
  have neq_new_old: "new\<noteq>old"
    by (cases new,cases old) (auto dest: subcls_irrefl)
  from subclseq_D_new subclseq_D_C
  have "G\<turnstile>(declclass new) \<preceq>\<^sub>C C \<or> G\<turnstile>C \<preceq>\<^sub>C (declclass new)" 
    by (rule subcls_compareable)
  then have "G\<turnstile>(declclass new) \<preceq>\<^sub>C C"
  proof
    assume "G\<turnstile>declclass new\<preceq>\<^sub>C C" then show ?thesis .
  next
    assume "G\<turnstile>C \<preceq>\<^sub>C (declclass new)"
    with new subclseq_D_C ws 
    have "G\<turnstile>new member_of C"
      by (blast intro: member_of_inheritance)
    with eqid old 
    have "new=old"
      by (blast intro: unique_member_of)
    with neq_new_old 
    show ?thesis
      by contradiction
  qed
  then show ?thesis
  proof (cases rule: subclseq_cases)
    case Eq
    assume "declclass new = C"
    with new have "G\<turnstile>new member_of C"
      by (auto dest: member_of_member_of_declC)
    with eqid old 
    have "new=old"
      by (blast intro: unique_member_of)
    with neq_new_old 
    show ?thesis
      by contradiction
  next
    case Subcls
    assume "G\<turnstile>declclass new\<prec>\<^sub>C C"
    with subclseq_D_new
    show "G\<turnstile>D\<prec>\<^sub>C C"
      by (rule rtrancl_trancl_trancl)
  qed
qed

corollary member_of_overrides_subcls:
 "\<lbrakk>G\<turnstile>Methd sig old member_of C; G\<turnstile>Methd sig new member_of D;G\<turnstile>D \<preceq>\<^sub>C C;
   G,sig\<turnstile>new overrides old; ws_prog G\<rbrakk>
 \<Longrightarrow> G\<turnstile>D \<prec>\<^sub>C C"
by (drule overrides_commonD) (auto intro: member_of_subcls)    

corollary member_of_stat_overrides_subcls:
 "\<lbrakk>G\<turnstile>Methd sig old member_of C; G\<turnstile>Methd sig new member_of D;G\<turnstile>D \<preceq>\<^sub>C C;
   G,sig\<turnstile>new overrides\<^sub>S old; ws_prog G\<rbrakk>
 \<Longrightarrow> G\<turnstile>D \<prec>\<^sub>C C"
by (drule stat_overrides_commonD) (auto intro: member_of_subcls)    



lemma inherited_field_access: 
  assumes stat_acc: "G\<turnstile>membr of statC accessible_from accC" and
          is_field: "is_field membr" and 
          subclseq: "G \<turnstile> dynC \<preceq>\<^sub>C statC"
  shows "G\<turnstile>membr in dynC dyn_accessible_from accC"
proof -
  from stat_acc is_field subclseq 
  show ?thesis
    by (auto dest: accessible_fieldD 
            intro: dyn_accessible_fromR.Immediate 
                   member_inI 
                   permits_acc_inheritance)
qed

lemma accessible_inheritance:
  assumes stat_acc: "G\<turnstile>m of statC accessible_from accC" and
          subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
       member_dynC: "G\<turnstile>m member_of dynC" and
          dynC_acc: "G\<turnstile>(Class dynC) accessible_in (pid accC)"
  shows "G\<turnstile>m of dynC accessible_from accC"
proof -
  from stat_acc
  have member_statC: "G\<turnstile>m member_of statC" 
    by (auto dest: accessible_from_commonD)
  from stat_acc
  show ?thesis
  proof (cases)
    case Immediate
    with member_dynC member_statC subclseq dynC_acc
    show ?thesis
      by (auto intro: accessible_fromR.Immediate permits_acc_inheritance)
  next
    case Overriding
    with member_dynC subclseq dynC_acc
    show ?thesis
      by (auto intro: accessible_fromR.Overriding rtrancl_trancl_trancl)
  qed
qed

subsubsection "fields and methods"


type_synonym
  fspec = "vname \<times> qtname"

translations 
  (type) "fspec" <= (type) "vname \<times> qtname" 

definition
  imethds :: "prog \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> mhead) tables" where
  "imethds G I =
    iface_rec G I  (\<lambda>I i ts. (Un_tables ts) \<oplus>\<oplus>
                        (set_option \<circ> table_of (map (\<lambda>(s,m). (s,I,m)) (imethods i))))"
text \<open>methods of an interface, with overriding and inheritance, cf. 9.2\<close>

definition
  accimethds :: "prog \<Rightarrow> pname \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> mhead) tables" where
  "accimethds G pack I =
    (if G\<turnstile>Iface I accessible_in pack 
     then imethds G I
     else (\<lambda> k. {}))"
text \<open>only returns imethds if the interface is accessible\<close>

definition
  methd :: "prog \<Rightarrow> qtname  \<Rightarrow> (sig,qtname \<times> methd) table" where
  "methd G C =
    class_rec G C Map.empty
             (\<lambda>C c subcls_mthds. 
               filter_tab (\<lambda>sig m. G\<turnstile>C inherits method sig m)
                          subcls_mthds 
               ++ 
               table_of (map (\<lambda>(s,m). (s,C,m)) (methods c)))"
text \<open>\<^term>\<open>methd G C\<close>: methods of a class C (statically visible from C), 
     with inheritance and hiding cf. 8.4.6;
     Overriding is captured by \<open>dynmethd\<close>.
     Every new method with the same signature coalesces the
     method of a superclass.\<close>

definition
  accmethd :: "prog \<Rightarrow> qtname \<Rightarrow> qtname  \<Rightarrow> (sig,qtname \<times> methd) table" where
  "accmethd G S C =
    filter_tab (\<lambda>sig m. G\<turnstile>method sig m of C accessible_from S) (methd G C)"
text \<open>\<^term>\<open>accmethd G S C\<close>: only those methods of \<^term>\<open>methd G C\<close>, 
        accessible from S\<close>

text \<open>Note the class component in the accessibility filter. The class where
    method \<^term>\<open>m\<close> is declared (\<^term>\<open>declC\<close>) isn't necessarily accessible 
    from the current scope \<^term>\<open>S\<close>. The method can be made accessible 
    through inheritance, too.
    So we must test accessibility of method \<^term>\<open>m\<close> of class \<^term>\<open>C\<close> 
    (not \<^term>\<open>declclass m\<close>)\<close>

definition
  dynmethd :: "prog  \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> methd) table" where
  "dynmethd G statC dynC =
    (\<lambda>sig.
       (if G\<turnstile>dynC \<preceq>\<^sub>C statC
          then (case methd G statC sig of
                  None \<Rightarrow> None
                | Some statM 
                    \<Rightarrow> (class_rec G dynC Map.empty
                         (\<lambda>C c subcls_mthds. 
                            subcls_mthds
                            ++
                            (filter_tab 
                              (\<lambda> _ dynM. G,sig\<turnstile>dynM overrides statM \<or> dynM=statM)
                              (methd G C) ))
                        ) sig
                )
          else None))"

text \<open>\<^term>\<open>dynmethd G statC dynC\<close>: dynamic method lookup of a reference 
        with dynamic class \<^term>\<open>dynC\<close> and static class \<^term>\<open>statC\<close>\<close>
text \<open>Note some kind of duality between \<^term>\<open>methd\<close> and \<^term>\<open>dynmethd\<close> 
        in the \<^term>\<open>class_rec\<close> arguments. Whereas \<^term>\<open>methd\<close> filters the 
        subclass methods (to get only the inherited ones), \<^term>\<open>dynmethd\<close> 
        filters the new methods (to get only those methods which actually
        override the methods of the static class)\<close>

definition
  dynimethd :: "prog \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> methd) table" where
  "dynimethd G I dynC =
    (\<lambda>sig. if imethds G I sig \<noteq> {}
           then methd G dynC sig
           else dynmethd G Object dynC sig)"
text \<open>\<^term>\<open>dynimethd G I dynC\<close>: dynamic method lookup of a reference with 
        dynamic class dynC and static interface type I\<close>
text \<open>
   When calling an interface method, we must distinguish if the method signature
   was defined in the interface or if it must be an Object method in the other
   case. If it was an interface method we search the class hierarchy
   starting at the dynamic class of the object up to Object to find the 
   first matching method (\<^term>\<open>methd\<close>). Since all interface methods have 
   public access the method can't be coalesced due to some odd visibility 
   effects like in case of dynmethd. The method will be inherited or 
   overridden in all classes from the first class implementing the interface 
   down to the actual dynamic class.
\<close>

definition
  dynlookup :: "prog  \<Rightarrow> ref_ty \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> methd) table" where
  "dynlookup G statT dynC =
    (case statT of
      NullT        \<Rightarrow> Map.empty
    | IfaceT I     \<Rightarrow> dynimethd G I      dynC
    | ClassT statC \<Rightarrow> dynmethd  G statC  dynC
    | ArrayT ty    \<Rightarrow> dynmethd  G Object dynC)"
text \<open>\<^term>\<open>dynlookup G statT dynC\<close>: dynamic lookup of a method within the 
    static reference type statT and the dynamic class dynC. 
    In a wellformd context statT will not be NullT and in case
    statT is an array type, dynC=Object\<close>

definition
  fields :: "prog \<Rightarrow> qtname \<Rightarrow> ((vname \<times> qtname) \<times> field) list" where
  "fields G C =
    class_rec G C [] (\<lambda>C c ts. map (\<lambda>(n,t). ((n,C),t)) (cfields c) @ ts)"
text \<open>\<^term>\<open>fields G C\<close> 
     list of fields of a class, including all the fields of the superclasses
     (private, inherited and hidden ones) not only the accessible ones
     (an instance of a object allocates all these fields\<close>

definition
  accfield :: "prog \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> (vname, qtname  \<times>  field) table" where
  "accfield G S C =
    (let field_tab = table_of((map (\<lambda>((n,d),f).(n,(d,f)))) (fields G C))
      in filter_tab (\<lambda>n (declC,f). G\<turnstile> (declC,fdecl (n,f)) of C accessible_from S)
                    field_tab)"
text  \<open>\<^term>\<open>accfield G C S\<close>: fields of a class \<^term>\<open>C\<close> which are 
         accessible from scope of class
         \<^term>\<open>S\<close> with inheritance and hiding, cf. 8.3\<close>
text \<open>note the class component in the accessibility filter (see also 
        \<^term>\<open>methd\<close>).
   The class declaring field \<^term>\<open>f\<close> (\<^term>\<open>declC\<close>) isn't necessarily 
   accessible from scope \<^term>\<open>S\<close>. The field can be made visible through 
   inheritance, too. So we must test accessibility of field \<^term>\<open>f\<close> of class 
   \<^term>\<open>C\<close> (not \<^term>\<open>declclass f\<close>)\<close> 

definition
  is_methd :: "prog \<Rightarrow> qtname  \<Rightarrow> sig \<Rightarrow> bool"
  where "is_methd G = (\<lambda>C sig. is_class G C \<and> methd G C sig \<noteq> None)"

definition
  efname :: "((vname \<times> qtname) \<times> field) \<Rightarrow> (vname \<times> qtname)"
  where "efname = fst"

lemma efname_simp[simp]:"efname (n,f) = n"
by (simp add: efname_def) 


subsection "imethds"

lemma imethds_rec: "\<lbrakk>iface G I = Some i; ws_prog G\<rbrakk> \<Longrightarrow>  
  imethds G I = Un_tables ((\<lambda>J. imethds  G J)`set (isuperIfs i)) \<oplus>\<oplus>  
                      (set_option \<circ> table_of (map (\<lambda>(s,mh). (s,I,mh)) (imethods i)))"
apply (unfold imethds_def)
apply (rule iface_rec [THEN trans])
apply auto
done


(* local lemma *)
lemma imethds_norec:
  "\<lbrakk>iface G md = Some i; ws_prog G; table_of (imethods i) sig = Some mh\<rbrakk> \<Longrightarrow>  
  (md, mh) \<in> imethds G md sig"
apply (subst imethds_rec)
apply assumption+
apply (rule iffD2)
apply (rule overrides_t_Some_iff)
apply (rule disjI1)
apply (auto elim: table_of_map_SomeI)
done

lemma imethds_declI: "\<lbrakk>m \<in> imethds G I sig; ws_prog G; is_iface G I\<rbrakk> \<Longrightarrow> 
  (\<exists>i. iface G (decliface m) = Some i \<and> 
  table_of (imethods i) sig = Some (mthd m)) \<and>  
  (I,decliface m) \<in> (subint1 G)\<^sup>* \<and> m \<in> imethds G (decliface m) sig"
apply (erule rev_mp)
apply (rule ws_subint1_induct, assumption, assumption)
apply (subst imethds_rec, erule conjunct1, assumption)
apply (force elim: imethds_norec intro: rtrancl_into_rtrancl2)
done

lemma imethds_cases:
  assumes im: "im \<in> imethds G I sig"
    and ifI: "iface G I = Some i"
    and ws: "ws_prog G"
  obtains (NewMethod) "table_of (map (\<lambda>(s, mh). (s, I, mh)) (imethods i)) sig = Some im"
    | (InheritedMethod) J where "J \<in> set (isuperIfs i)" and "im \<in> imethds G J sig"
using assms by (auto simp add: imethds_rec)


subsection "accimethd"

lemma accimethds_simp [simp]: 
"G\<turnstile>Iface I accessible_in pack \<Longrightarrow> accimethds G pack I = imethds G I"
by (simp add: accimethds_def)

lemma accimethdsD:
 "im \<in> accimethds G pack I sig 
  \<Longrightarrow> im \<in> imethds G I sig \<and> G\<turnstile>Iface I accessible_in pack"
by (auto simp add: accimethds_def)

lemma accimethdsI: 
"\<lbrakk>im \<in> imethds G I sig;G\<turnstile>Iface I accessible_in pack\<rbrakk>
 \<Longrightarrow> im \<in> accimethds G pack I sig"
by simp

subsection "methd"

lemma methd_rec: "\<lbrakk>class G C = Some c; ws_prog G\<rbrakk> \<Longrightarrow>  
  methd G C 
    = (if C = Object 
          then Map.empty 
          else filter_tab (\<lambda>sig m. G\<turnstile>C inherits method sig m)
                          (methd G (super c))) 
      ++ table_of (map (\<lambda>(s,m). (s,C,m)) (methods c))"
apply (unfold methd_def)
apply (erule class_rec [THEN trans], assumption)
apply (simp)
done

(* local lemma *)
lemma methd_norec: 
 "\<lbrakk>class G declC = Some c; ws_prog G;table_of (methods c) sig = Some m\<rbrakk> 
  \<Longrightarrow> methd G declC sig = Some (declC, m)"
apply (simp only: methd_rec)
apply (rule disjI1 [THEN map_add_Some_iff [THEN iffD2]])
apply (auto elim: table_of_map_SomeI)
done


lemma methd_declC: 
"\<lbrakk>methd G C sig = Some m; ws_prog G;is_class G C\<rbrakk> \<Longrightarrow>
 (\<exists>d. class G (declclass m)=Some d \<and> table_of (methods d) sig=Some (mthd m)) \<and> 
 G\<turnstile>C \<preceq>\<^sub>C (declclass m) \<and> methd G (declclass m) sig = Some m"   
apply (erule rev_mp)
apply (rule ws_subcls1_induct, assumption, assumption)
apply (subst methd_rec, assumption)
apply (case_tac "Ca=Object")
apply   (force elim: methd_norec )

apply   simp
apply   (case_tac "table_of (map (\<lambda>(s, m). (s, Ca, m)) (methods c)) sig")
apply     (force intro: rtrancl_into_rtrancl2)

apply     (auto intro: methd_norec)
done

lemma methd_inheritedD:
  "\<lbrakk>class G C = Some c; ws_prog G;methd G C sig = Some m\<rbrakk>
  \<Longrightarrow>  (declclass m \<noteq> C \<longrightarrow> G \<turnstile>C inherits method sig m)"
by (auto simp add: methd_rec)

lemma methd_diff_cls:
"\<lbrakk>ws_prog G; is_class G C; is_class G D;
 methd G C sig = m; methd G D sig = n; m\<noteq>n
\<rbrakk> \<Longrightarrow> C\<noteq>D"
by (auto simp add: methd_rec)

lemma method_declared_inI: 
 "\<lbrakk>table_of (methods c) sig = Some m; class G C = Some c\<rbrakk>
  \<Longrightarrow> G\<turnstile>mdecl (sig,m) declared_in C"
by (auto simp add: cdeclaredmethd_def declared_in_def)

lemma methd_declared_in_declclass: 
 "\<lbrakk>methd G C sig = Some m; ws_prog G;is_class G C\<rbrakk> 
 \<Longrightarrow> G\<turnstile>Methd sig m declared_in (declclass m)"
by (auto dest: methd_declC method_declared_inI)

lemma member_methd:
  assumes member_of: "G\<turnstile>Methd sig m member_of C" and
                 ws: "ws_prog G"
  shows "methd G C sig = Some m"
proof -
  from member_of 
  have iscls_C: "is_class G C" 
    by (rule member_of_is_classD)
  from iscls_C ws member_of
  show ?thesis (is "?Methd C")
  proof (induct rule: ws_class_induct')
    case (Object co)
    assume "G \<turnstile>Methd sig m member_of Object"
    then have "G\<turnstile>Methd sig m declared_in Object \<and> declclass m = Object"
      by (cases set: members) (cases m, auto dest: subcls1D)
    with ws Object 
    show "?Methd Object"
      by (cases m)
         (auto simp add: declared_in_def cdeclaredmethd_def methd_rec
                  intro:  table_of_mapconst_SomeI)
  next
    case (Subcls C c)
    assume clsC: "class G C = Some c" and
      neq_C_Obj: "C \<noteq> Object" and
            hyp: "G \<turnstile>Methd sig m member_of super c \<Longrightarrow> ?Methd (super c)" and
      member_of: "G \<turnstile>Methd sig m member_of C"
    from member_of
    show "?Methd C"
    proof (cases)
      case Immediate
      with clsC 
      have "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c)) sig = Some m"
        by (cases m)
           (auto simp add: declared_in_def cdeclaredmethd_def
                    intro: table_of_mapconst_SomeI)
      with clsC neq_C_Obj ws 
      show ?thesis
        by (simp add: methd_rec)
    next
      case (Inherited S)
      with clsC
      have  undecl: "G\<turnstile>mid sig undeclared_in C" and
             super: "G \<turnstile>Methd sig m member_of (super c)"
        by (auto dest: subcls1D)
      from clsC undecl 
      have "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c)) sig = None"
        by (auto simp add: undeclared_in_def cdeclaredmethd_def
                    intro: table_of_mapconst_NoneI)
      moreover
      from Inherited have "G \<turnstile> C inherits (method sig m)"
        by (auto simp add: inherits_def)
      moreover
      note clsC neq_C_Obj ws super hyp 
      ultimately
      show ?thesis
        by (auto simp add: methd_rec intro: filter_tab_SomeI)
    qed
  qed
qed

(*unused*)
lemma finite_methd:"ws_prog G \<Longrightarrow> finite {methd G C sig |sig C. is_class G C}"
apply (rule finite_is_class [THEN finite_SetCompr2])
apply (intro strip)
apply (erule_tac ws_subcls1_induct, assumption)
apply (subst methd_rec)
apply (assumption)
apply (auto intro!: finite_range_map_of finite_range_filter_tab finite_range_map_of_map_add)
done

lemma finite_dom_methd:
 "\<lbrakk>ws_prog G; is_class G C\<rbrakk> \<Longrightarrow> finite (dom (methd G C))"
apply (erule_tac ws_subcls1_induct)
apply assumption
apply (subst methd_rec)
apply (assumption)
apply (auto intro!: finite_dom_map_of finite_dom_filter_tab)
done


subsection "accmethd"

lemma accmethd_SomeD:
"accmethd G S C sig = Some m
 \<Longrightarrow> methd G C sig = Some m \<and> G\<turnstile>method sig m of C accessible_from S"
by (auto simp add: accmethd_def)

lemma accmethd_SomeI:
"\<lbrakk>methd G C sig = Some m; G\<turnstile>method sig m of C accessible_from S\<rbrakk> 
 \<Longrightarrow> accmethd G S C sig = Some m"
by (auto simp add: accmethd_def intro: filter_tab_SomeI)

lemma accmethd_declC: 
"\<lbrakk>accmethd G S C sig = Some m; ws_prog G; is_class G C\<rbrakk> \<Longrightarrow>
 (\<exists>d. class G (declclass m)=Some d \<and> 
  table_of (methods d) sig=Some (mthd m)) \<and> 
 G\<turnstile>C \<preceq>\<^sub>C (declclass m) \<and> methd G (declclass m) sig = Some m \<and> 
 G\<turnstile>method sig m of C accessible_from S"
by (auto dest: accmethd_SomeD methd_declC accmethd_SomeI)


lemma finite_dom_accmethd:
 "\<lbrakk>ws_prog G; is_class G C\<rbrakk> \<Longrightarrow> finite (dom (accmethd G S C))"
by (auto simp add: accmethd_def intro: finite_dom_filter_tab finite_dom_methd)


subsection "dynmethd"

lemma dynmethd_rec:
"\<lbrakk>class G dynC = Some c; ws_prog G\<rbrakk> \<Longrightarrow>  
 dynmethd G statC dynC sig
   = (if G\<turnstile>dynC \<preceq>\<^sub>C statC
        then (case methd G statC sig of
                None \<Rightarrow> None
              | Some statM 
                  \<Rightarrow> (case methd G dynC sig of
                        None \<Rightarrow> dynmethd G statC (super c) sig
                      | Some dynM \<Rightarrow> 
                          (if G,sig\<turnstile> dynM overrides statM \<or> dynM = statM 
                              then Some dynM
                              else (dynmethd G statC (super c) sig)
                      )))
         else None)" 
   (is "_ \<Longrightarrow> _ \<Longrightarrow> ?Dynmethd_def dynC sig  = ?Dynmethd_rec dynC c sig") 
proof -
  assume clsDynC: "class G dynC = Some c" and 
              ws: "ws_prog G"
  then show "?Dynmethd_def dynC sig  = ?Dynmethd_rec dynC c sig" 
  proof (induct rule: ws_class_induct'')
    case (Object co)
    show "?Dynmethd_def Object sig = ?Dynmethd_rec Object co sig"
    proof (cases "G\<turnstile>Object \<preceq>\<^sub>C statC") 
      case False
      then show ?thesis by (simp add: dynmethd_def)
    next
      case True
      then have eq_statC_Obj: "statC = Object" ..
      show ?thesis 
      proof (cases "methd G statC sig")
        case None then show ?thesis by (simp add: dynmethd_def)
      next
        case Some
        with True Object ws eq_statC_Obj 
        show ?thesis
          by (auto simp add: dynmethd_def class_rec
                      intro: filter_tab_SomeI)
      qed
    qed
  next  
    case (Subcls dynC c sc)
    show "?Dynmethd_def dynC sig = ?Dynmethd_rec dynC c sig"
    proof (cases "G\<turnstile>dynC \<preceq>\<^sub>C statC") 
      case False
      then show ?thesis by (simp add: dynmethd_def)
    next
      case True
      note subclseq_dynC_statC = True
      show ?thesis
      proof (cases "methd G statC sig")
        case None then show ?thesis by (simp add: dynmethd_def)
      next
        case (Some statM)
        note statM = Some
        let ?filter = 
              "\<lambda>C. filter_tab
                (\<lambda>_ dynM. G,sig \<turnstile> dynM overrides statM \<or> dynM = statM)
                (methd G C)"
        let ?class_rec =
              "\<lambda>C. class_rec G C Map.empty
                           (\<lambda>C c subcls_mthds. subcls_mthds ++ (?filter C))"
        from statM Subcls ws subclseq_dynC_statC
        have dynmethd_dynC_def:
             "?Dynmethd_def dynC sig =
                ((?class_rec (super c)) 
                 ++
                (?filter dynC)) sig"
         by (simp (no_asm_simp) only: dynmethd_def class_rec)
            auto
       show ?thesis
       proof (cases "dynC = statC")
         case True
         with subclseq_dynC_statC statM dynmethd_dynC_def
         have "?Dynmethd_def dynC sig = Some statM"
           by (auto intro: map_add_find_right filter_tab_SomeI)
         with subclseq_dynC_statC True Some 
         show ?thesis
           by auto
       next
         case False
         with subclseq_dynC_statC Subcls 
         have subclseq_super_statC: "G\<turnstile>(super c) \<preceq>\<^sub>C statC"
           by (blast dest: subclseq_superD)
         show ?thesis
         proof (cases "methd G dynC sig") 
           case None
           then have "?filter dynC sig = None"
             by (rule filter_tab_None)
           then have "?Dynmethd_def dynC sig=?class_rec (super c) sig"
             by (simp add: dynmethd_dynC_def)
           with  subclseq_super_statC statM None
           have "?Dynmethd_def dynC sig = ?Dynmethd_def (super c) sig"
             by (auto simp add: empty_def dynmethd_def)
           with None subclseq_dynC_statC statM
           show ?thesis 
             by simp
         next
           case (Some dynM)
           note dynM = Some
           let ?Termination = "G \<turnstile> qmdecl sig dynM overrides qmdecl sig statM \<or>
                               dynM = statM"
           show ?thesis
           proof (cases "?filter dynC sig")
             case None
             with dynM 
             have no_termination: "\<not> ?Termination"
               by (simp add: filter_tab_def)
             from None 
             have "?Dynmethd_def dynC sig=?class_rec (super c) sig"
               by (simp add: dynmethd_dynC_def)
             with subclseq_super_statC statM dynM no_termination
             show ?thesis
               by (auto simp add: empty_def dynmethd_def)
           next
             case Some
             with dynM
             have "termination": "?Termination"
               by (auto)
             with Some dynM
             have "?Dynmethd_def dynC sig=Some dynM"
              by (auto simp add: dynmethd_dynC_def)
             with subclseq_super_statC statM dynM "termination"
             show ?thesis
               by (auto simp add: dynmethd_def)
           qed
         qed
       qed
     qed
   qed
 qed
qed
               
lemma dynmethd_C_C:"\<lbrakk>is_class G C; ws_prog G\<rbrakk> 
\<Longrightarrow> dynmethd G C C sig = methd G C sig"          
apply (auto simp add: dynmethd_rec)
done
 
lemma dynmethdSomeD: 
 "\<lbrakk>dynmethd G statC dynC sig = Some dynM; is_class G dynC; ws_prog G\<rbrakk> 
  \<Longrightarrow> G\<turnstile>dynC \<preceq>\<^sub>C statC \<and> (\<exists> statM. methd G statC sig = Some statM)"
by (auto simp add: dynmethd_rec)
 
lemma dynmethd_Some_cases:
  assumes dynM: "dynmethd G statC dynC sig = Some dynM"
    and is_cls_dynC: "is_class G dynC"
    and ws: "ws_prog G"
  obtains (Static) "methd G statC sig = Some dynM"
    | (Overrides) statM
      where "methd G statC sig = Some statM"
        and "dynM \<noteq> statM"
        and "G,sig\<turnstile>dynM overrides statM"
proof -
  from is_cls_dynC obtain dc where clsDynC: "class G dynC = Some dc" by blast
  from clsDynC ws dynM Static Overrides
  show ?thesis
  proof (induct rule: ws_class_induct)
    case (Object co)
    with ws  have "statC = Object" 
      by (auto simp add: dynmethd_rec)
    with ws Object show ?thesis by (auto simp add: dynmethd_C_C)
  next
    case (Subcls C c)
    with ws show ?thesis
      by (auto simp add: dynmethd_rec)
  qed
qed

lemma no_override_in_Object:
  assumes          dynM: "dynmethd G statC dynC sig = Some dynM" and
            is_cls_dynC: "is_class G dynC" and
                     ws: "ws_prog G" and
                  statM: "methd G statC sig = Some statM" and
         neq_dynM_statM: "dynM\<noteq>statM"
  shows "dynC \<noteq> Object"
proof -
  from is_cls_dynC obtain dc where clsDynC: "class G dynC = Some dc" by blast
  from clsDynC ws dynM statM neq_dynM_statM 
  show ?thesis (is "?P dynC")
  proof (induct rule: ws_class_induct)
    case (Object co)
    with ws  have "statC = Object" 
      by (auto simp add: dynmethd_rec)
    with ws Object show "?P Object" by (auto simp add: dynmethd_C_C)
  next
    case (Subcls dynC c)
    with ws show "?P dynC"
      by (auto simp add: dynmethd_rec)
  qed
qed


lemma dynmethd_Some_rec_cases:
  assumes dynM: "dynmethd G statC dynC sig = Some dynM"
    and clsDynC: "class G dynC = Some c"
    and ws: "ws_prog G"
  obtains (Static) "methd G statC sig = Some dynM"
    | (Override) statM where "methd G statC sig = Some statM"
        and "methd G dynC sig = Some dynM" and "statM \<noteq> dynM"
        and "G,sig\<turnstile> dynM overrides statM"
    | (Recursion) "dynC \<noteq> Object" and "dynmethd G statC (super c) sig = Some dynM"
proof -
  from clsDynC have *: "is_class G dynC" by simp
  from ws clsDynC dynM Static Override Recursion
  show ?thesis
    by (auto simp add: dynmethd_rec dest: no_override_in_Object [OF dynM * ws])
qed

lemma dynmethd_declC: 
"\<lbrakk>dynmethd G statC dynC sig = Some m;
  is_class G statC;ws_prog G
 \<rbrakk> \<Longrightarrow>
  (\<exists>d. class G (declclass m)=Some d \<and> table_of (methods d) sig=Some (mthd m)) \<and>
  G\<turnstile>dynC \<preceq>\<^sub>C (declclass m) \<and> methd G (declclass m) sig = Some m"
proof - 
  assume  is_cls_statC: "is_class G statC" 
  assume            ws: "ws_prog G"  
  assume             m: "dynmethd G statC dynC sig = Some m"
  from m 
  have "G\<turnstile>dynC \<preceq>\<^sub>C statC" by (auto simp add: dynmethd_def)
  from this is_cls_statC 
  have is_cls_dynC: "is_class G dynC" by (rule subcls_is_class2)
  from is_cls_dynC ws m  
  show ?thesis (is "?P dynC") 
  proof (induct rule: ws_class_induct')
    case (Object co)
    with ws have "statC=Object" by (auto simp add: dynmethd_rec)
    with ws Object  
    show "?P Object" 
      by (auto simp add: dynmethd_C_C dest: methd_declC)
  next
    case (Subcls dynC c)
    assume   hyp: "dynmethd G statC (super c) sig = Some m \<Longrightarrow> ?P (super c)" and
         clsDynC: "class G dynC = Some c"  and
              m': "dynmethd G statC dynC sig = Some m" and
    neq_dynC_Obj: "dynC \<noteq> Object"
    from ws this obtain statM where
      subclseq_dynC_statC: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and 
                     statM: "methd G statC sig = Some statM"
      by (blast dest: dynmethdSomeD)
    from clsDynC neq_dynC_Obj 
    have subclseq_dynC_super: "G\<turnstile>dynC \<preceq>\<^sub>C (super c)" 
      by (auto intro: subcls1I) 
    from m' clsDynC ws 
    show "?P dynC"
    proof (cases rule: dynmethd_Some_rec_cases) 
      case Static
      with is_cls_statC ws subclseq_dynC_statC 
      show ?thesis 
        by (auto intro: rtrancl_trans dest: methd_declC)
    next
      case Override
      with clsDynC ws 
      show ?thesis 
        by (auto dest: methd_declC)
    next
      case Recursion
      with hyp subclseq_dynC_super 
      show ?thesis 
        by (auto intro: rtrancl_trans) 
    qed
  qed
qed

lemma methd_Some_dynmethd_Some:
  assumes     statM: "methd G statC sig = Some statM" and
           subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
       is_cls_statC: "is_class G statC" and
                 ws: "ws_prog G"
  shows "\<exists> dynM. dynmethd G statC dynC sig = Some dynM"
    (is "?P dynC")
proof -
  from subclseq is_cls_statC 
  have is_cls_dynC: "is_class G dynC" by (rule subcls_is_class2)
  then obtain dc where
    clsDynC: "class G dynC = Some dc" by blast
  from clsDynC ws subclseq 
  show "?thesis"
  proof (induct rule: ws_class_induct)
    case (Object co)
    with ws  have "statC = Object" 
      by (auto)
    with ws Object statM
    show "?P Object"  
      by (auto simp add: dynmethd_C_C)
  next
    case (Subcls dynC dc)
    assume clsDynC': "class G dynC = Some dc"
    assume neq_dynC_Obj: "dynC \<noteq> Object"
    assume hyp: "G\<turnstile>super dc\<preceq>\<^sub>C statC \<Longrightarrow> ?P (super dc)"
    assume subclseq': "G\<turnstile>dynC\<preceq>\<^sub>C statC"
    then
    show "?P dynC"
    proof (cases rule: subclseq_cases)
      case Eq
      with ws statM clsDynC' 
      show ?thesis
        by (auto simp add: dynmethd_rec)
    next
      case Subcls
      assume "G\<turnstile>dynC\<prec>\<^sub>C statC"
      from this clsDynC' 
      have "G\<turnstile>super dc\<preceq>\<^sub>C statC" by (rule subcls_superD)
      with hyp ws clsDynC' subclseq' statM
      show ?thesis
        by (auto simp add: dynmethd_rec)
    qed
  qed
qed

lemma dynmethd_cases:
  assumes statM: "methd G statC sig = Some statM"
    and subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC"
    and is_cls_statC: "is_class G statC"
    and ws: "ws_prog G"
  obtains (Static) "dynmethd G statC dynC sig = Some statM"
    | (Overrides) dynM where "dynmethd G statC dynC sig = Some dynM"
        and "dynM \<noteq> statM" and "G,sig\<turnstile>dynM overrides statM"
proof -
  note hyp_static = Static and hyp_override = Overrides
  from subclseq is_cls_statC 
  have is_cls_dynC: "is_class G dynC" by (rule subcls_is_class2)
  then obtain dc where
    clsDynC: "class G dynC = Some dc" by blast
  from statM subclseq is_cls_statC ws 
  obtain dynM where dynM: "dynmethd G statC dynC sig = Some dynM"
    by (blast dest: methd_Some_dynmethd_Some)
  from dynM is_cls_dynC ws 
  show ?thesis
  proof (cases rule: dynmethd_Some_cases)
    case Static
    with hyp_static dynM statM show ?thesis by simp
  next
    case Overrides
    with hyp_override dynM statM show ?thesis by simp
  qed
qed

lemma ws_dynmethd:
  assumes  statM: "methd G statC sig = Some statM" and
        subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
    is_cls_statC: "is_class G statC" and
              ws: "ws_prog G"
  shows
    "\<exists> dynM. dynmethd G statC dynC sig = Some dynM \<and>
             is_static dynM = is_static statM \<and> G\<turnstile>resTy dynM\<preceq>resTy statM"
proof - 
  from statM subclseq is_cls_statC ws
  show ?thesis
  proof (cases rule: dynmethd_cases)
    case Static
    with statM 
    show ?thesis
      by simp
  next
    case Overrides
    with ws
    show ?thesis
      by (auto dest: ws_overrides_commonD)
  qed
qed

subsection "dynlookup"

lemma dynlookup_cases:
  assumes "dynlookup G statT dynC sig = x"
  obtains (NullT) "statT = NullT" and "Map.empty sig = x"
    | (IfaceT) I where "statT = IfaceT I" and "dynimethd G I dynC sig = x"
    | (ClassT) statC where "statT = ClassT statC" and "dynmethd G statC dynC sig = x"
    | (ArrayT) ty where "statT = ArrayT ty" and "dynmethd G Object dynC sig = x"
using assms by (cases statT) (auto simp add: dynlookup_def)

subsection "fields"

lemma fields_rec: "\<lbrakk>class G C = Some c; ws_prog G\<rbrakk> \<Longrightarrow>  
  fields G C = map (\<lambda>(fn,ft). ((fn,C),ft)) (cfields c) @  
  (if C = Object then [] else fields G (super c))"
apply (simp only: fields_def)
apply (erule class_rec [THEN trans])
apply assumption
apply clarsimp
done

(* local lemma *)
lemma fields_norec: 
"\<lbrakk>class G fd = Some c; ws_prog G;  table_of (cfields c) fn = Some f\<rbrakk> 
 \<Longrightarrow> table_of (fields G fd) (fn,fd) = Some f"
apply (subst fields_rec)
apply assumption+
apply (subst map_of_append)
apply (rule disjI1 [THEN map_add_Some_iff [THEN iffD2]])
apply (auto elim: table_of_map2_SomeI)
done

(* local lemma *)
lemma table_of_fieldsD:
"table_of (map (\<lambda>(fn,ft). ((fn,C),ft)) (cfields c)) efn = Some f
\<Longrightarrow> (declclassf efn) = C \<and> table_of (cfields c) (fname efn) = Some f"
apply (case_tac "efn")
by auto

lemma fields_declC: 
 "\<lbrakk>table_of (fields G C) efn = Some f; ws_prog G; is_class G C\<rbrakk> \<Longrightarrow>  
  (\<exists>d. class G (declclassf efn) = Some d \<and> 
                    table_of (cfields d) (fname efn)=Some f) \<and> 
  G\<turnstile>C \<preceq>\<^sub>C (declclassf efn)  \<and> table_of (fields G (declclassf efn)) efn = Some f"
apply (erule rev_mp)
apply (rule ws_subcls1_induct, assumption, assumption)
apply (subst fields_rec, assumption)
apply clarify
apply (simp only: map_of_append)
apply (case_tac "table_of (map (case_prod (\<lambda>fn. Pair (fn, Ca))) (cfields c)) efn") 
apply   (force intro:rtrancl_into_rtrancl2 simp add: map_add_def)

apply   (frule_tac fd="Ca" in fields_norec)
apply     assumption
apply     blast
apply   (frule table_of_fieldsD)  
apply   (frule_tac n="table_of (map (case_prod (\<lambda>fn. Pair (fn, Ca))) (cfields c))"
              and  m="table_of (if Ca = Object then [] else fields G (super c))"
         in map_add_find_right)
apply   (case_tac "efn")
apply   (simp)
done

lemma fields_emptyI: "\<And>y. \<lbrakk>ws_prog G; class G C = Some c;cfields c = [];  
  C \<noteq> Object \<longrightarrow> class G (super c) = Some y \<and> fields G (super c) = []\<rbrakk> \<Longrightarrow>  
  fields G C = []"
apply (subst fields_rec)
apply assumption
apply auto
done

(* easier than with table_of *)
lemma fields_mono_lemma: 
"\<lbrakk>x \<in> set (fields G C); G\<turnstile>D \<preceq>\<^sub>C C; ws_prog G\<rbrakk> 
 \<Longrightarrow> x \<in> set (fields G D)"
apply (erule rev_mp)
apply (erule converse_rtrancl_induct)
apply  fast
apply (drule subcls1D)
apply clarsimp
apply (subst fields_rec)
apply   auto
done


lemma ws_unique_fields_lemma: 
 "\<lbrakk>(efn,fd)  \<in> set (fields G (super c)); fc \<in> set (cfields c); ws_prog G;  
   fname efn = fname fc; declclassf efn = C;
   class G C = Some c; C \<noteq> Object; class G (super c) = Some d\<rbrakk> \<Longrightarrow> R"
apply (frule_tac ws_prog_cdeclD [THEN conjunct2], assumption, assumption)
apply (drule_tac weak_map_of_SomeI)
apply (frule_tac subcls1I [THEN subcls1_irrefl], assumption, assumption)
apply (auto dest: fields_declC [THEN conjunct2 [THEN conjunct1[THEN rtranclD]]])
done

lemma ws_unique_fields: "\<lbrakk>is_class G C; ws_prog G; 
       \<And>C c. \<lbrakk>class G C = Some c\<rbrakk> \<Longrightarrow> unique (cfields c) \<rbrakk> \<Longrightarrow>
      unique (fields G C)" 
apply (rule ws_subcls1_induct, assumption, assumption)
apply (subst fields_rec, assumption)            
apply (auto intro!: unique_map_inj inj_onI 
            elim!: unique_append ws_unique_fields_lemma fields_norec)
done


subsection "accfield"

lemma accfield_fields: 
 "accfield G S C fn = Some f 
  \<Longrightarrow> table_of (fields G C) (fn, declclass f) = Some (fld f)"
apply (simp only: accfield_def Let_def)
apply (rule table_of_remap_SomeD)
apply auto
done


lemma accfield_declC_is_class: 
 "\<lbrakk>is_class G C; accfield G S C en = Some (fd, f); ws_prog G\<rbrakk> \<Longrightarrow>  
   is_class G fd"
apply (drule accfield_fields)
apply (drule fields_declC [THEN conjunct1], assumption)
apply auto
done

lemma accfield_accessibleD: 
  "accfield G S C fn = Some f \<Longrightarrow> G\<turnstile>Field fn f of C accessible_from S"
by (auto simp add: accfield_def Let_def)

subsection "is methd"

lemma is_methdI: 
"\<lbrakk>class G C = Some y; methd G C sig = Some b\<rbrakk> \<Longrightarrow> is_methd G C sig"
apply (unfold is_methd_def)
apply auto
done

lemma is_methdD: 
"is_methd G C sig \<Longrightarrow> class G C \<noteq> None \<and> methd G C sig \<noteq> None"
apply (unfold is_methd_def)
apply auto
done

lemma finite_is_methd: 
 "ws_prog G \<Longrightarrow> finite (Collect (case_prod (is_methd G)))"
apply (unfold is_methd_def)
apply (subst Collect_case_prod_Sigma)
apply (rule finite_is_class [THEN finite_SigmaI])
apply (simp only: mem_Collect_eq)
apply (fold dom_def)
apply (erule finite_dom_methd)
apply assumption
done

subsubsection "calculation of the superclasses of a class"

definition
  superclasses :: "prog \<Rightarrow> qtname \<Rightarrow> qtname set" where
 "superclasses G C = class_rec G C {} 
                       (\<lambda> C c superclss. (if C=Object 
                                            then {} 
                                            else insert (super c) superclss))"
   
lemma superclasses_rec: "\<lbrakk>class G C = Some c; ws_prog G\<rbrakk> \<Longrightarrow>  
 superclasses G C 
 = (if (C=Object) 
       then {}
       else insert (super c) (superclasses G (super c)))"
apply (unfold superclasses_def)
apply (erule class_rec [THEN trans], assumption)
apply (simp)
done

lemma superclasses_mono:
  assumes clsrel: "G\<turnstile>C\<prec>\<^sub>C D"
  and ws: "ws_prog G"
  and cls_C: "class G C = Some c"
  and wf: "\<And>C c. \<lbrakk>class G C = Some c; C \<noteq> Object\<rbrakk>
    \<Longrightarrow> \<exists>sc. class G (super c) = Some sc"
  and x: "x\<in>superclasses G D"
  shows "x\<in>superclasses G C" using clsrel cls_C x
proof (induct arbitrary: c rule: converse_trancl_induct)
  case (base C)
  with wf ws show ?case
    by (auto    intro: no_subcls1_Object 
             simp add: superclasses_rec subcls1_def)
next
  case (step C S)
  moreover note wf ws
  moreover from calculation 
  have "x\<in>superclasses G S"
    by (force intro: no_subcls1_Object simp add: subcls1_def)
  moreover from calculation 
  have "super c = S" 
    by (auto intro: no_subcls1_Object simp add: subcls1_def)
  ultimately show ?case 
    by (auto intro: no_subcls1_Object simp add: superclasses_rec)
qed

lemma subclsEval:
  assumes clsrel: "G\<turnstile>C\<prec>\<^sub>C D"
  and ws: "ws_prog G"
  and cls_C: "class G C = Some c"
  and wf: "\<And>C c. \<lbrakk>class G C = Some c; C \<noteq> Object\<rbrakk>
    \<Longrightarrow> \<exists>sc. class G (super c) = Some sc"
  shows "D\<in>superclasses G C" using clsrel cls_C
proof (induct arbitrary: c rule: converse_trancl_induct)
  case (base C)
  show ?case
    by (use ws wf base in \<open>auto intro: no_subcls1_Object simp add: superclasses_rec subcls1_def\<close>)
next
  case (step C S)
  show ?case
    by (rule superclasses_mono)
      (use ws wf step in \<open>auto dest: no_subcls1_Object simp add: subcls1_def\<close>)
qed

end
