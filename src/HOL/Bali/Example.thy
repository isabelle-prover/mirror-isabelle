(*  Title:      HOL/Bali/Example.thy
    Author:     David von Oheimb
*)
subsection \<open>Example Bali program\<close>

theory Example
imports Eval WellForm
begin

text \<open>
The following example Bali program includes:
\begin{itemize}
\item class and interface declarations with inheritance, hiding of fields,
    overriding of methods (with refined result type), array type,
\item method call (with dynamic binding), parameter access, return expressions,
\item expression statements, sequential composition, literal values, 
    local assignment, local access, field assignment, type cast,
\item exception generation and propagation, try and catch statement, throw 
      statement
\item instance creation and (default) static initialization
\end{itemize}
\begin{verbatim}
package java_lang

public interface HasFoo {
  public Base foo(Base z);
}

public class Base implements HasFoo {
  static boolean arr[] = new boolean[2];
  public HasFoo vee;
  public Base foo(Base z) {
    return z;
  }
}

public class Ext extends Base {
  public int vee;
  public Ext foo(Base z) {
    ((Ext)z).vee = 1;
    return null;
  }
}

public class Main {
  public static void main(String args[]) throws Throwable {
    Base e = new Ext();
    try {e.foo(null); }
    catch(NullPointerException z) { 
      while(Ext.arr[2]) ;
    }
  }
}
\end{verbatim}
\<close>
declare widen.null [intro]

lemma wf_fdecl_def2: "\<And>fd. wf_fdecl G P fd = is_acc_type G P (type (snd fd))"
apply (unfold wf_fdecl_def)
apply (simp (no_asm))
done

declare wf_fdecl_def2 [iff]


subsubsection "type and expression names"

(** unfortunately cannot simply instantiate tnam **)
datatype tnam'  = HasFoo' | Base' | Ext' | Main'
datatype vnam'  = arr' | vee' | z' | e'
datatype label' = lab1'

axiomatization
  tnam' :: "tnam'  \<Rightarrow> tnam" and
  vnam' :: "vnam'  \<Rightarrow> vname" and
  label':: "label' \<Rightarrow> label"
where
  (** tnam', vnam' and label are intended to be isomorphic 
            to tnam, vname and label **)

  inj_tnam'  [simp]: "\<And>x y. (tnam'  x = tnam'  y) = (x = y)" and
  inj_vnam'  [simp]: "\<And>x y. (vnam'  x = vnam'  y) = (x = y)" and
  inj_label' [simp]: "\<And>x y. (label' x = label' y) = (x = y)" and
    
  surj_tnam':  "\<And>n. \<exists>m. n = tnam'  m" and
  surj_vnam':  "\<And>n. \<exists>m. n = vnam'  m" and
  surj_label':" \<And>n. \<exists>m. n = label' m"

abbreviation
  HasFoo :: qtname where
  "HasFoo == \<lparr>pid=java_lang,tid=TName (tnam' HasFoo')\<rparr>"

abbreviation
  Base :: qtname where
  "Base == \<lparr>pid=java_lang,tid=TName (tnam' Base')\<rparr>"

abbreviation
  Ext :: qtname where
  "Ext == \<lparr>pid=java_lang,tid=TName (tnam' Ext')\<rparr>"

abbreviation
  Main :: qtname where
  "Main == \<lparr>pid=java_lang,tid=TName (tnam' Main')\<rparr>"

abbreviation
  arr :: vname where
  "arr == (vnam' arr')"

abbreviation
  vee :: vname where
  "vee == (vnam' vee')"

abbreviation
  z :: vname where
  "z == (vnam' z')"

abbreviation
  e :: vname where
  "e == (vnam' e')"

abbreviation
  lab1:: label where
  "lab1 == label' lab1'"


lemma neq_Base_Object [simp]: "Base\<noteq>Object"
by (simp add: Object_def)

lemma neq_Ext_Object [simp]: "Ext\<noteq>Object"
by (simp add: Object_def)

lemma neq_Main_Object [simp]: "Main\<noteq>Object"
by (simp add: Object_def)

lemma neq_Base_SXcpt [simp]: "Base\<noteq>SXcpt xn"
by (simp add: SXcpt_def)

lemma neq_Ext_SXcpt [simp]: "Ext\<noteq>SXcpt xn"
by (simp add: SXcpt_def)

lemma neq_Main_SXcpt [simp]: "Main\<noteq>SXcpt xn"
by (simp add: SXcpt_def)


subsubsection "classes and interfaces"

overloading
  Object_mdecls \<equiv> Object_mdecls
  SXcpt_mdecls \<equiv> SXcpt_mdecls
begin
  definition "Object_mdecls \<equiv> []"
  definition "SXcpt_mdecls  \<equiv> []"
end

axiomatization  
  foo    :: mname

definition
  foo_sig :: sig
  where "foo_sig = \<lparr>name=foo,parTs=[Class Base]\<rparr>"
  
definition
  foo_mhead :: mhead
  where "foo_mhead = \<lparr>access=Public,static=False,pars=[z],resT=Class Base\<rparr>"

definition
  Base_foo :: mdecl
  where "Base_foo = (foo_sig, \<lparr>access=Public,static=False,pars=[z],resT=Class Base,
                        mbody=\<lparr>lcls=[],stmt=Return (!!z)\<rparr>\<rparr>)"

definition Ext_foo :: mdecl
  where "Ext_foo = (foo_sig, 
              \<lparr>access=Public,static=False,pars=[z],resT=Class Ext,
               mbody=\<lparr>lcls=[]
                     ,stmt=Expr({Ext,Ext,False}Cast (Class Ext) (!!z)..vee := 
                                                             Lit (Intg 1)) ;;
                                Return (Lit Null)\<rparr>
              \<rparr>)"

definition
  arr_viewed_from :: "qtname \<Rightarrow> qtname \<Rightarrow> var"
  where "arr_viewed_from accC C = {accC,Base,True}StatRef (ClassT C)..arr"

definition
  BaseCl :: "class" where
  "BaseCl = \<lparr>access=Public,
           cfields=[(arr, \<lparr>access=Public,static=True ,type=PrimT Boolean.[]\<rparr>),
                    (vee, \<lparr>access=Public,static=False,type=Iface HasFoo    \<rparr>)],
           methods=[Base_foo],
           init=Expr(arr_viewed_from Base Base 
                     :=New (PrimT Boolean)[Lit (Intg 2)]),
           super=Object,
           superIfs=[HasFoo]\<rparr>"
  
definition
  ExtCl  :: "class" where
  "ExtCl = \<lparr>access=Public,
           cfields=[(vee, \<lparr>access=Public,static=False,type= PrimT Integer\<rparr>)], 
           methods=[Ext_foo],
           init=Skip,
           super=Base,
           superIfs=[]\<rparr>"

definition
  MainCl :: "class" where
  "MainCl = \<lparr>access=Public,
           cfields=[], 
           methods=[], 
           init=Skip,
           super=Object,
           superIfs=[]\<rparr>"
(* The "main" method is modeled seperately (see tprg) *)

definition
  HasFooInt :: iface
  where "HasFooInt = \<lparr>access=Public,imethods=[(foo_sig, foo_mhead)],isuperIfs=[]\<rparr>"

definition
  Ifaces ::"idecl list"
  where "Ifaces = [(HasFoo,HasFooInt)]"

definition
  "Classes" ::"cdecl list"
  where "Classes = [(Base,BaseCl),(Ext,ExtCl),(Main,MainCl)]@standard_classes"

lemmas table_classes_defs = 
     Classes_def standard_classes_def ObjectC_def SXcptC_def

lemma table_ifaces [simp]: "table_of Ifaces = Map.empty(HasFoo\<mapsto>HasFooInt)"
apply (unfold Ifaces_def)
apply (simp (no_asm))
done

lemma table_classes_Object [simp]: 
 "table_of Classes Object = Some \<lparr>access=Public,cfields=[]
                                 ,methods=Object_mdecls
                                 ,init=Skip,super=undefined,superIfs=[]\<rparr>"
apply (unfold table_classes_defs)
apply (simp (no_asm) add:Object_def)
done

lemma table_classes_SXcpt [simp]: 
  "table_of Classes (SXcpt xn) 
    = Some \<lparr>access=Public,cfields=[],methods=SXcpt_mdecls,
            init=Skip,
            super=if xn = Throwable then Object else SXcpt Throwable,
            superIfs=[]\<rparr>"
apply (unfold table_classes_defs)
apply (induct_tac xn)
apply (simp add: Object_def SXcpt_def)+
done

lemma table_classes_HasFoo [simp]: "table_of Classes HasFoo = None"
apply (unfold table_classes_defs)
apply (simp (no_asm) add: Object_def SXcpt_def)
done

lemma table_classes_Base [simp]: "table_of Classes Base = Some BaseCl"
apply (unfold table_classes_defs )
apply (simp (no_asm) add: Object_def SXcpt_def)
done

lemma table_classes_Ext [simp]: "table_of Classes Ext = Some ExtCl"
apply (unfold table_classes_defs )
apply (simp (no_asm) add: Object_def SXcpt_def)
done

lemma table_classes_Main [simp]: "table_of Classes Main = Some MainCl"
apply (unfold table_classes_defs )
apply (simp (no_asm) add: Object_def SXcpt_def)
done

subsubsection "program"

abbreviation
  tprg :: prog where
  "tprg == \<lparr>ifaces=Ifaces,classes=Classes\<rparr>"

definition
  test :: "(ty)list \<Rightarrow> stmt" where
  "test pTs = (e:==NewC Ext;; 
           Try Expr({Main,ClassT Base,IntVir}!!e\<cdot>foo({pTs}[Lit Null]))
           Catch((SXcpt NullPointer) z)
           (lab1\<bullet> While(Acc 
                        (Acc (arr_viewed_from Main Ext).[Lit (Intg 2)])) Skip))"


subsubsection "well-structuredness"

lemma not_Object_subcls_any [elim!]: "(Object, C) \<in> (subcls1 tprg)\<^sup>+ \<Longrightarrow> R"
apply (auto dest!: tranclD subcls1D)
done

lemma not_Throwable_subcls_SXcpt [elim!]: 
  "(SXcpt Throwable, SXcpt xn) \<in> (subcls1 tprg)\<^sup>+ \<Longrightarrow> R"
apply (auto dest!: tranclD subcls1D) 
apply (simp add: Object_def SXcpt_def)
done

lemma not_SXcpt_n_subcls_SXcpt_n [elim!]: 
  "(SXcpt xn, SXcpt xn)  \<in> (subcls1 tprg)\<^sup>+ \<Longrightarrow> R"
apply (auto dest!: tranclD subcls1D)
apply (drule rtranclD)
apply auto
done

lemma not_Base_subcls_Ext [elim!]: "(Base, Ext) \<in> (subcls1 tprg)\<^sup>+  \<Longrightarrow> R"
apply (auto dest!: tranclD subcls1D simp add: BaseCl_def)
done

lemma not_TName_n_subcls_TName_n [rule_format (no_asm), elim!]: 
  "(\<lparr>pid=java_lang,tid=TName tn\<rparr>, \<lparr>pid=java_lang,tid=TName tn\<rparr>) 
   \<in> (subcls1 tprg)\<^sup>+ \<longrightarrow> R"
apply (rule_tac n1 = "tn" in surj_tnam' [THEN exE])
apply (erule ssubst)
apply (rule tnam'.induct)
apply  safe
apply (auto dest!: tranclD subcls1D simp add: BaseCl_def ExtCl_def MainCl_def)
apply (drule rtranclD)
apply auto
done


lemma ws_idecl_HasFoo: "ws_idecl tprg HasFoo []"
apply (unfold ws_idecl_def)
apply (simp (no_asm))
done

lemma ws_cdecl_Object: "ws_cdecl tprg Object any"
apply (unfold ws_cdecl_def)
apply auto
done

lemma ws_cdecl_Throwable: "ws_cdecl tprg (SXcpt Throwable) Object"
apply (unfold ws_cdecl_def)
apply auto
done

lemma ws_cdecl_SXcpt: "ws_cdecl tprg (SXcpt xn) (SXcpt Throwable)"
apply (unfold ws_cdecl_def)
apply auto
done

lemma ws_cdecl_Base: "ws_cdecl tprg Base Object"
apply (unfold ws_cdecl_def)
apply auto
done

lemma ws_cdecl_Ext: "ws_cdecl tprg Ext Base"
apply (unfold ws_cdecl_def)
apply auto
done

lemma ws_cdecl_Main: "ws_cdecl tprg Main Object"
apply (unfold ws_cdecl_def)
apply auto
done

lemmas ws_cdecls = ws_cdecl_SXcpt ws_cdecl_Object ws_cdecl_Throwable
                   ws_cdecl_Base ws_cdecl_Ext ws_cdecl_Main

declare not_Object_subcls_any [rule del]
          not_Throwable_subcls_SXcpt [rule del] 
          not_SXcpt_n_subcls_SXcpt_n [rule del] 
          not_Base_subcls_Ext [rule del] not_TName_n_subcls_TName_n [rule del]

lemma ws_idecl_all: 
 "G=tprg \<Longrightarrow> (\<forall>(I,i)\<in>set Ifaces. ws_idecl G I (isuperIfs i))"
apply (simp (no_asm) add: Ifaces_def HasFooInt_def)
apply (auto intro!: ws_idecl_HasFoo)
done

lemma ws_cdecl_all: "G=tprg \<Longrightarrow> (\<forall>(C,c)\<in>set Classes. ws_cdecl G C (super c))"
apply (simp (no_asm) add: Classes_def BaseCl_def ExtCl_def MainCl_def)
apply (auto intro!: ws_cdecls simp add: standard_classes_def ObjectC_def 
        SXcptC_def)
done

lemma ws_tprg: "ws_prog tprg"
apply (unfold ws_prog_def)
apply (auto intro!: ws_idecl_all ws_cdecl_all)
done


subsubsection "misc program properties (independent of well-structuredness)"

lemma single_iface [simp]: "is_iface tprg I = (I = HasFoo)"
apply (unfold Ifaces_def)
apply (simp (no_asm))
done

lemma empty_subint1 [simp]: "subint1 tprg = {}"
apply (unfold subint1_def Ifaces_def HasFooInt_def)
apply auto
done

lemma unique_ifaces: "unique Ifaces"
apply (unfold Ifaces_def)
apply (simp (no_asm))
done

lemma unique_classes: "unique Classes"
apply (unfold table_classes_defs )
apply (simp )
done

lemma SXcpt_subcls_Throwable [simp]: "tprg\<turnstile>SXcpt xn\<preceq>\<^sub>C SXcpt Throwable"
apply (rule SXcpt_subcls_Throwable_lemma)
apply auto
done

lemma Ext_subclseq_Base [simp]: "tprg\<turnstile>Ext \<preceq>\<^sub>C Base"
apply (rule subcls_direct1)
apply  (simp (no_asm) add: ExtCl_def)
apply  (simp add: Object_def)
apply (simp (no_asm))
done

lemma Ext_subcls_Base [simp]: "tprg\<turnstile>Ext \<prec>\<^sub>C Base"
apply (rule subcls_direct2)
apply  (simp (no_asm) add: ExtCl_def)
apply  (simp add: Object_def)
apply (simp (no_asm))
done



subsubsection "fields and method lookup"

lemma fields_tprg_Object [simp]: "DeclConcepts.fields tprg Object = []"
by (rule ws_tprg [THEN fields_emptyI], force+)

lemma fields_tprg_Throwable [simp]: 
  "DeclConcepts.fields tprg (SXcpt Throwable) = []"
by (rule ws_tprg [THEN fields_emptyI], force+)

lemma fields_tprg_SXcpt [simp]: "DeclConcepts.fields tprg (SXcpt xn) = []"
apply (case_tac "xn = Throwable")
apply  (simp (no_asm_simp))
by (rule ws_tprg [THEN fields_emptyI], force+)

lemmas fields_rec' = fields_rec [OF _ ws_tprg]

lemma fields_Base [simp]: 
"DeclConcepts.fields tprg Base 
  = [((arr,Base), \<lparr>access=Public,static=True ,type=PrimT Boolean.[]\<rparr>),
     ((vee,Base), \<lparr>access=Public,static=False,type=Iface HasFoo    \<rparr>)]"
apply (subst fields_rec')
apply   (auto simp add: BaseCl_def)
done

lemma fields_Ext [simp]: 
 "DeclConcepts.fields tprg Ext  
  = [((vee,Ext), \<lparr>access=Public,static=False,type= PrimT Integer\<rparr>)] 
    @ DeclConcepts.fields tprg Base"
apply (rule trans)
apply (rule fields_rec')
apply   (auto simp add: ExtCl_def Object_def)
done

lemmas imethds_rec' = imethds_rec [OF _ ws_tprg]
lemmas methd_rec'  = methd_rec  [OF _ ws_tprg]

lemma imethds_HasFoo [simp]: 
  "imethds tprg HasFoo = set_option \<circ> Map.empty(foo_sig\<mapsto>(HasFoo, foo_mhead))"
apply (rule trans)
apply (rule imethds_rec')
apply  (auto simp add: HasFooInt_def)
done

lemma methd_tprg_Object [simp]: "methd tprg Object = Map.empty"
apply (subst methd_rec')
apply (auto simp add: Object_mdecls_def)
done

lemma methd_Base [simp]: 
  "methd tprg Base = table_of [(\<lambda>(s,m). (s, Base, m)) Base_foo]"
apply (rule trans)
apply (rule methd_rec')
apply   (auto simp add: BaseCl_def)
done

lemma memberid_Base_foo_simp [simp]:
 "memberid (mdecl Base_foo) = mid foo_sig"
by (simp add: Base_foo_def)

lemma memberid_Ext_foo_simp [simp]:
 "memberid (mdecl Ext_foo) = mid foo_sig"
by (simp add: Ext_foo_def)

lemma Base_declares_foo:
  "tprg\<turnstile>mdecl Base_foo declared_in Base"
by (auto simp add: declared_in_def cdeclaredmethd_def BaseCl_def Base_foo_def)

lemma foo_sig_not_undeclared_in_Base:
  "\<not> tprg\<turnstile>mid foo_sig undeclared_in Base"
proof -
  from Base_declares_foo
  show ?thesis
    by (auto dest!: declared_not_undeclared )
qed

lemma Ext_declares_foo:
  "tprg\<turnstile>mdecl Ext_foo declared_in Ext"
by (auto simp add: declared_in_def cdeclaredmethd_def ExtCl_def Ext_foo_def)

lemma foo_sig_not_undeclared_in_Ext:
  "\<not> tprg\<turnstile>mid foo_sig undeclared_in Ext"
proof -
  from Ext_declares_foo
  show ?thesis
    by (auto dest!: declared_not_undeclared )
qed

lemma Base_foo_not_inherited_in_Ext:
 "\<not> tprg \<turnstile> Ext inherits (Base,mdecl Base_foo)"
by (auto simp add: inherits_def foo_sig_not_undeclared_in_Ext)

lemma Ext_method_inheritance:
 "filter_tab (\<lambda>sig m. tprg \<turnstile> Ext inherits method sig m)
     (Map.empty(fst ((\<lambda>(s, m). (s, Base, m)) Base_foo)\<mapsto>
      snd ((\<lambda>(s, m). (s, Base, m)) Base_foo)))
  = Map.empty"
proof -
  from Base_foo_not_inherited_in_Ext
  show ?thesis
    by (auto intro: filter_tab_all_False simp add: Base_foo_def)
qed


lemma methd_Ext [simp]: "methd tprg Ext =   
  table_of [(\<lambda>(s,m). (s, Ext, m)) Ext_foo]"
apply (rule trans)
apply (rule methd_rec')
apply   (auto simp add: ExtCl_def Object_def Ext_method_inheritance)
done

subsubsection "accessibility"

lemma classesDefined: 
 "\<lbrakk>class tprg C = Some c; C\<noteq>Object\<rbrakk> \<Longrightarrow> \<exists> sc. class tprg (super c) = Some sc"
apply (auto simp add: Classes_def standard_classes_def 
                      BaseCl_def ExtCl_def MainCl_def
                      SXcptC_def ObjectC_def) 
done

lemma superclassesBase [simp]: "superclasses tprg Base={Object}"
proof -
  have ws: "ws_prog tprg" by (rule ws_tprg)
  then show ?thesis
    by (auto simp add: superclasses_rec  BaseCl_def)
qed

lemma superclassesExt [simp]: "superclasses tprg Ext={Base,Object}"
proof -
  have ws: "ws_prog tprg" by (rule ws_tprg)
  then show ?thesis
    by (auto simp add: superclasses_rec  ExtCl_def BaseCl_def)
qed

lemma superclassesMain [simp]: "superclasses tprg Main={Object}"
proof -
  have ws: "ws_prog tprg" by (rule ws_tprg)
  then show ?thesis
    by (auto simp add: superclasses_rec  MainCl_def)
qed

lemma HasFoo_accessible[simp]:"tprg\<turnstile>(Iface HasFoo) accessible_in P" 
by (simp add: accessible_in_RefT_simp is_public_def HasFooInt_def)

lemma HasFoo_is_acc_iface[simp]: "is_acc_iface tprg P HasFoo"
by (simp add: is_acc_iface_def)

lemma HasFoo_is_acc_type[simp]: "is_acc_type tprg P (Iface HasFoo)"
by (simp add: is_acc_type_def)

lemma Base_accessible[simp]:"tprg\<turnstile>(Class Base) accessible_in P" 
by (simp add: accessible_in_RefT_simp is_public_def BaseCl_def)

lemma Base_is_acc_class[simp]: "is_acc_class tprg P Base"
by (simp add: is_acc_class_def)

lemma Base_is_acc_type[simp]: "is_acc_type tprg P (Class Base)"
by (simp add: is_acc_type_def)

lemma Ext_accessible[simp]:"tprg\<turnstile>(Class Ext) accessible_in P" 
by (simp add: accessible_in_RefT_simp is_public_def ExtCl_def)

lemma Ext_is_acc_class[simp]: "is_acc_class tprg P Ext"
by (simp add: is_acc_class_def)

lemma Ext_is_acc_type[simp]: "is_acc_type tprg P (Class Ext)"
by (simp add: is_acc_type_def)

lemma accmethd_tprg_Object [simp]: "accmethd tprg S Object = Map.empty"
apply (unfold accmethd_def)
apply (simp)
done

lemma  snd_special_simp: "snd ((\<lambda>(s, m). (s, a, m)) x) = (a,snd x)"
by (cases x) (auto)

lemma  fst_special_simp: "fst ((\<lambda>(s, m). (s, a, m)) x) = fst x"
by (cases x) (auto)

lemma foo_sig_undeclared_in_Object:
  "tprg\<turnstile>mid foo_sig undeclared_in Object"
by (auto simp add: undeclared_in_def cdeclaredmethd_def Object_mdecls_def)

lemma unique_sig_Base_foo:
 "tprg\<turnstile> mdecl (sig, snd Base_foo) declared_in Base \<Longrightarrow> sig=foo_sig"
by (auto simp add: declared_in_def cdeclaredmethd_def 
                   Base_foo_def BaseCl_def)

lemma Base_foo_no_override:
 "tprg,sig\<turnstile>(Base,(snd Base_foo)) overrides old \<Longrightarrow> P"
apply (drule overrides_commonD)
apply (clarsimp)
apply (frule subclsEval)
apply    (rule ws_tprg)
apply    (simp)
apply    (rule classesDefined) 
apply    assumption+
apply (frule unique_sig_Base_foo) 
apply (auto dest!: declared_not_undeclared intro: foo_sig_undeclared_in_Object
            dest: unique_sig_Base_foo)
done

lemma Base_foo_no_stat_override:
 "tprg,sig\<turnstile>(Base,(snd Base_foo)) overrides\<^sub>S old \<Longrightarrow> P"
apply (drule stat_overrides_commonD)
apply (clarsimp)
apply (frule subclsEval)
apply    (rule ws_tprg)
apply    (simp)
apply    (rule classesDefined) 
apply    assumption+
apply (frule unique_sig_Base_foo) 
apply (auto dest!: declared_not_undeclared intro: foo_sig_undeclared_in_Object
            dest: unique_sig_Base_foo)
done


lemma Base_foo_no_hide:
 "tprg,sig\<turnstile>(Base,(snd Base_foo)) hides old \<Longrightarrow> P"
by (auto dest: hidesD simp add: Base_foo_def member_is_static_simp)

lemma Ext_foo_no_hide:
 "tprg,sig\<turnstile>(Ext,(snd Ext_foo)) hides old \<Longrightarrow> P"
by (auto dest: hidesD simp add: Ext_foo_def member_is_static_simp)

lemma unique_sig_Ext_foo:
 "tprg\<turnstile> mdecl (sig, snd Ext_foo) declared_in Ext \<Longrightarrow> sig=foo_sig"
by (auto simp add: declared_in_def cdeclaredmethd_def 
                   Ext_foo_def ExtCl_def)

lemma Ext_foo_override:
 "tprg,sig\<turnstile>(Ext,(snd Ext_foo)) overrides old 
  \<Longrightarrow> old = (Base,(snd Base_foo))"
apply (drule overrides_commonD)
apply (clarsimp)
apply (frule subclsEval)
apply    (rule ws_tprg)
apply    (simp)
apply    (rule classesDefined) 
apply    assumption+
apply (frule unique_sig_Ext_foo) 
apply (case_tac "old")
apply (insert Base_declares_foo foo_sig_undeclared_in_Object) 
apply (auto simp add: ExtCl_def Ext_foo_def
                      BaseCl_def Base_foo_def Object_mdecls_def
                      split_paired_all
                      member_is_static_simp
           dest: declared_not_undeclared unique_declaration)
done

lemma Ext_foo_stat_override:
 "tprg,sig\<turnstile>(Ext,(snd Ext_foo)) overrides\<^sub>S old 
  \<Longrightarrow> old = (Base,(snd Base_foo))"
apply (drule stat_overrides_commonD)
apply (clarsimp)
apply (frule subclsEval)
apply    (rule ws_tprg)
apply    (simp)
apply    (rule classesDefined) 
apply    assumption+
apply (frule unique_sig_Ext_foo) 
apply (case_tac "old")
apply (insert Base_declares_foo foo_sig_undeclared_in_Object) 
apply (auto simp add: ExtCl_def Ext_foo_def
                      BaseCl_def Base_foo_def Object_mdecls_def
                      split_paired_all
                      member_is_static_simp
           dest: declared_not_undeclared unique_declaration)
done

lemma Base_foo_member_of_Base: 
  "tprg\<turnstile>(Base,mdecl Base_foo) member_of Base"
by (auto intro!: members.Immediate Base_declares_foo)

lemma Base_foo_member_in_Base: 
  "tprg\<turnstile>(Base,mdecl Base_foo) member_in Base"
by (rule member_of_to_member_in [OF Base_foo_member_of_Base])

lemma Ext_foo_member_of_Ext: 
  "tprg\<turnstile>(Ext,mdecl Ext_foo) member_of Ext"
by (auto intro!: members.Immediate Ext_declares_foo)

lemma Ext_foo_member_in_Ext: 
  "tprg\<turnstile>(Ext,mdecl Ext_foo) member_in Ext"
by (rule member_of_to_member_in [OF Ext_foo_member_of_Ext])

lemma Base_foo_permits_acc:
 "tprg \<turnstile> (Base, mdecl Base_foo) in Base permits_acc_from S"
by ( simp add: permits_acc_def Base_foo_def)

lemma Base_foo_accessible [simp]:
 "tprg\<turnstile>(Base,mdecl Base_foo) of Base accessible_from S"
by (auto intro: accessible_fromR.Immediate 
                Base_foo_member_of_Base Base_foo_permits_acc)

lemma Base_foo_dyn_accessible [simp]:
 "tprg\<turnstile>(Base,mdecl Base_foo) in Base dyn_accessible_from S"
apply (rule dyn_accessible_fromR.Immediate)
apply   (rule Base_foo_member_in_Base)
apply   (rule Base_foo_permits_acc)
done

lemma accmethd_Base [simp]: 
  "accmethd tprg S Base = methd tprg Base"
apply (simp add: accmethd_def)
apply (rule filter_tab_all_True)
apply (simp add: snd_special_simp fst_special_simp)
done

lemma Ext_foo_permits_acc:
 "tprg \<turnstile> (Ext, mdecl Ext_foo) in Ext permits_acc_from S"
by ( simp add: permits_acc_def Ext_foo_def)

lemma Ext_foo_accessible [simp]:
 "tprg\<turnstile>(Ext,mdecl Ext_foo) of Ext accessible_from S"
by (auto intro: accessible_fromR.Immediate 
                Ext_foo_member_of_Ext Ext_foo_permits_acc)

lemma Ext_foo_dyn_accessible [simp]:
 "tprg\<turnstile>(Ext,mdecl Ext_foo) in Ext dyn_accessible_from S"
apply (rule dyn_accessible_fromR.Immediate) 
apply   (rule Ext_foo_member_in_Ext)
apply   (rule Ext_foo_permits_acc)
done

lemma Ext_foo_overrides_Base_foo:
 "tprg\<turnstile>(Ext,Ext_foo) overrides (Base,Base_foo)"
proof (rule overridesR.Direct, simp_all)
  show "\<not> is_static Ext_foo" 
    by (simp add: member_is_static_simp Ext_foo_def)
  show "\<not> is_static Base_foo"
    by (simp add: member_is_static_simp Base_foo_def)
  show "accmodi Ext_foo \<noteq> Private"
    by (simp add: Ext_foo_def)
  show "msig (Ext, Ext_foo) = msig (Base, Base_foo)"
    by (simp add: Ext_foo_def Base_foo_def)
  show "tprg\<turnstile>mdecl Ext_foo declared_in Ext"
    by (auto intro: Ext_declares_foo)
  show "tprg\<turnstile>mdecl Base_foo declared_in Base"
    by (auto intro: Base_declares_foo)
  show "tprg \<turnstile>(Base, mdecl Base_foo) inheritable_in java_lang"
    by (simp add: inheritable_in_def Base_foo_def)
  show "tprg\<turnstile>resTy Ext_foo\<preceq>resTy Base_foo"
    by (simp add: Ext_foo_def Base_foo_def mhead_resTy_simp)
qed

lemma accmethd_Ext [simp]: 
  "accmethd tprg S Ext = methd tprg Ext"
apply (simp add: accmethd_def)
apply (rule filter_tab_all_True)
apply (auto simp add: snd_special_simp fst_special_simp)
done

lemma cls_Ext: "class tprg Ext = Some ExtCl"
by simp
lemma dynmethd_Ext_foo:
 "dynmethd tprg Base Ext \<lparr>name = foo, parTs = [Class Base]\<rparr> 
  = Some (Ext,snd Ext_foo)"
proof -
  have "methd tprg Base \<lparr>name = foo, parTs = [Class Base]\<rparr> 
          = Some (Base,snd Base_foo)" and
       "methd tprg Ext \<lparr>name = foo, parTs = [Class Base]\<rparr> 
          = Some (Ext,snd Ext_foo)" 
    by (auto simp add: Ext_foo_def Base_foo_def foo_sig_def)
  with cls_Ext ws_tprg Ext_foo_overrides_Base_foo
  show ?thesis
    by (auto simp add: dynmethd_rec simp add: Ext_foo_def Base_foo_def)
qed

lemma Base_fields_accessible[simp]:
 "accfield tprg S Base 
  = table_of((map (\<lambda>((n,d),f).(n,(d,f)))) (DeclConcepts.fields tprg Base))"
apply (auto simp add: accfield_def fun_eq_iff Let_def 
                      accessible_in_RefT_simp
                      is_public_def
                      BaseCl_def
                      permits_acc_def
                      declared_in_def 
                      cdeclaredfield_def
               intro!: filter_tab_all_True_Some filter_tab_None
                       accessible_fromR.Immediate
               intro: members.Immediate)
done


lemma arr_member_of_Base:
  "tprg\<turnstile>(Base, fdecl (arr, 
                 \<lparr>access = Public, static = True, type = PrimT Boolean.[]\<rparr>))
          member_of Base"
by (auto intro: members.Immediate 
       simp add: declared_in_def cdeclaredfield_def BaseCl_def)
 
lemma arr_member_in_Base:
  "tprg\<turnstile>(Base, fdecl (arr, 
                 \<lparr>access = Public, static = True, type = PrimT Boolean.[]\<rparr>))
          member_in Base"
by (rule member_of_to_member_in [OF arr_member_of_Base])

lemma arr_member_of_Ext:
  "tprg\<turnstile>(Base, fdecl (arr, 
                    \<lparr>access = Public, static = True, type = PrimT Boolean.[]\<rparr>))
             member_of Ext"
apply (rule members.Inherited)
apply   (simp add: inheritable_in_def)
apply   (simp add: undeclared_in_def cdeclaredfield_def ExtCl_def)
apply   (auto intro: arr_member_of_Base simp add: subcls1_def ExtCl_def)
done

lemma arr_member_in_Ext:
  "tprg\<turnstile>(Base, fdecl (arr, 
                 \<lparr>access = Public, static = True, type = PrimT Boolean.[]\<rparr>))
          member_in Ext"
by (rule member_of_to_member_in [OF arr_member_of_Ext])

lemma Ext_fields_accessible[simp]:
"accfield tprg S Ext 
  = table_of((map (\<lambda>((n,d),f).(n,(d,f)))) (DeclConcepts.fields tprg Ext))"
apply (auto simp add: accfield_def fun_eq_iff Let_def 
                      accessible_in_RefT_simp
                      is_public_def
                      BaseCl_def
                      ExtCl_def
                      permits_acc_def
               intro!: filter_tab_all_True_Some filter_tab_None
                       accessible_fromR.Immediate)
apply (auto intro: members.Immediate arr_member_of_Ext
            simp add: declared_in_def cdeclaredfield_def ExtCl_def)
done

lemma arr_Base_dyn_accessible [simp]:
"tprg\<turnstile>(Base, fdecl (arr, \<lparr>access=Public,static=True ,type=PrimT Boolean.[]\<rparr>)) 
       in Base dyn_accessible_from S"
apply (rule dyn_accessible_fromR.Immediate)
apply   (rule arr_member_in_Base)
apply   (simp add: permits_acc_def)
done

lemma arr_Ext_dyn_accessible[simp]:
"tprg\<turnstile>(Base, fdecl (arr, \<lparr>access=Public,static=True ,type=PrimT Boolean.[]\<rparr>)) 
       in Ext dyn_accessible_from S"
apply (rule dyn_accessible_fromR.Immediate)
apply   (rule arr_member_in_Ext)
apply   (simp add: permits_acc_def)
done

lemma array_of_PrimT_acc [simp]:
 "is_acc_type tprg java_lang (PrimT t.[])"
apply (simp add: is_acc_type_def accessible_in_RefT_simp)
done

lemma PrimT_acc [simp]: 
 "is_acc_type tprg java_lang (PrimT t)"
apply (simp add: is_acc_type_def accessible_in_RefT_simp)
done

lemma Object_acc [simp]:
 "is_acc_class tprg java_lang Object"
apply (auto simp add: is_acc_class_def accessible_in_RefT_simp is_public_def)
done


subsubsection "well-formedness"


lemma wf_HasFoo: "wf_idecl tprg (HasFoo, HasFooInt)"
apply (unfold wf_idecl_def HasFooInt_def)
apply (auto intro!: wf_mheadI ws_idecl_HasFoo 
            simp add: foo_sig_def foo_mhead_def mhead_resTy_simp
                      member_is_static_simp )
done


declare member_is_static_simp [simp]
declare wt.Skip [rule del] wt.Init [rule del]
ML \<open>ML_Thms.bind_thms ("wt_intros", map (rewrite_rule \<^context> @{thms id_def}) @{thms wt.intros})\<close>
lemmas wtIs = wt_Call wt_Super wt_FVar wt_StatRef wt_intros
lemmas daIs = assigned.select_convs da_Skip da_NewC da_Lit da_Super da.intros

lemmas Base_foo_defs = Base_foo_def foo_sig_def foo_mhead_def
lemmas Ext_foo_defs  = Ext_foo_def  foo_sig_def




lemma wf_Base_foo: "wf_mdecl tprg Base Base_foo"
apply (unfold Base_foo_defs )
apply (auto intro!: wf_mdeclI wf_mheadI intro!: wtIs 
            simp add: mhead_resTy_simp)
(* for definite assignment *)
apply (rule exI)
apply (simp add: parameters_def)
apply (rule conjI)
apply  (rule da.Comp)
apply     (rule da.Expr)
apply     (rule da.AssLVar)
apply       (rule da.AccLVar)
apply         (simp)
apply        (rule assigned.select_convs)
apply       (simp)
apply      (rule assigned.select_convs)
apply     (simp)
apply    (simp)
apply    (rule da.Jmp)
apply      (simp)
apply     (rule assigned.select_convs)
apply    (simp)
apply   (rule assigned.select_convs)
apply  (simp)
apply (simp)
done


lemma wf_Ext_foo: "wf_mdecl tprg Ext Ext_foo"
apply (unfold Ext_foo_defs )
apply (auto intro!: wf_mdeclI wf_mheadI intro!: wtIs 
            simp add: mhead_resTy_simp )
apply  (rule wt.Cast)
prefer 2
apply    simp
apply   (rule_tac [2] narrow.subcls [THEN cast.narrow])
apply   (auto intro!: wtIs)
(* for definite assignment *)
apply (rule exI)
apply (simp add: parameters_def)
apply (rule conjI)
apply  (rule da.Comp)
apply     (rule da.Expr)
apply     (rule da.Ass)   
apply       simp
apply      (rule da.FVar)
apply      (rule da.Cast)
apply      (rule da.AccLVar)
apply        simp
apply       (rule assigned.select_convs)
apply      simp
apply     (rule da_Lit)
apply     (simp)
apply    (rule da.Comp)
apply       (rule da.Expr)
apply       (rule da.AssLVar)
apply         (rule da.Lit)                  
apply        (rule assigned.select_convs)
apply       simp
apply      (rule da.Jmp)
apply        simp
apply       (rule assigned.select_convs)
apply      simp
apply     (rule assigned.select_convs)
apply    (simp)
apply   (rule assigned.select_convs)
apply  simp
apply simp
done

declare mhead_resTy_simp [simp add]

lemma wf_BaseC: "wf_cdecl tprg (Base,BaseCl)"
apply (unfold wf_cdecl_def BaseCl_def arr_viewed_from_def)
apply (auto intro!: wf_Base_foo)
apply        (auto intro!: ws_cdecl_Base simp add: Base_foo_def foo_mhead_def)
apply   (auto intro!: wtIs)
(* for definite assignment *)
apply   (rule exI)
apply   (rule da.Expr)
apply  (rule da.Ass)
apply    (simp)
apply   (rule da.FVar)
apply   (rule da.Cast)
apply   (rule da_Lit)
apply   simp
apply  (rule da.NewA)
apply  (rule da.Lit)
apply (auto simp add: Base_foo_defs entails_def Let_def)
apply   (insert Base_foo_no_stat_override, simp add: Base_foo_def,blast)+
apply (insert Base_foo_no_hide         , simp add: Base_foo_def,blast)
done


lemma wf_ExtC: "wf_cdecl tprg (Ext,ExtCl)"
apply (unfold wf_cdecl_def ExtCl_def)
apply (auto intro!: wf_Ext_foo ws_cdecl_Ext)
apply  (auto simp add: entails_def snd_special_simp)
apply      (insert Ext_foo_stat_override)
apply      (rule exI,rule da.Skip)      
apply     (force simp add: qmdecl_def Ext_foo_def Base_foo_def)
apply    (force simp add: qmdecl_def Ext_foo_def Base_foo_def)
apply   (force simp add: qmdecl_def Ext_foo_def Base_foo_def)
apply  (insert Ext_foo_no_hide)
apply  (simp_all add: qmdecl_def)
apply  blast+
done

lemma wf_MainC: "wf_cdecl tprg (Main,MainCl)"
apply (unfold wf_cdecl_def MainCl_def)
apply (auto intro: ws_cdecl_Main)
apply (rule exI,rule da.Skip)
done

lemma wf_idecl_all: "p=tprg \<Longrightarrow> Ball (set Ifaces) (wf_idecl p)"
apply (simp (no_asm) add: Ifaces_def)
apply (simp (no_asm_simp))
apply (rule wf_HasFoo)
done

lemma wf_cdecl_all_standard_classes: 
  "Ball (set standard_classes) (wf_cdecl tprg)"
apply (unfold standard_classes_def Let_def 
       ObjectC_def SXcptC_def Object_mdecls_def SXcpt_mdecls_def)
apply (simp (no_asm) add: wf_cdecl_def ws_cdecls)
apply (auto simp add:is_acc_class_def accessible_in_RefT_simp SXcpt_def 
            intro: da.Skip)
apply (auto simp add: Object_def Classes_def standard_classes_def 
                      SXcptC_def SXcpt_def)
done

lemma wf_cdecl_all: "p=tprg \<Longrightarrow> Ball (set Classes) (wf_cdecl p)"
apply (simp (no_asm) add: Classes_def)
apply (simp (no_asm_simp))
apply    (rule wf_BaseC [THEN conjI])
apply   (rule wf_ExtC [THEN conjI])
apply  (rule wf_MainC [THEN conjI])
apply (rule wf_cdecl_all_standard_classes)
done

theorem wf_tprg: "wf_prog tprg"
apply (unfold wf_prog_def Let_def)
apply (simp (no_asm) add: unique_ifaces unique_classes)
apply (rule conjI)
apply  ((simp (no_asm) add: Classes_def standard_classes_def))
apply (rule conjI)
apply (simp add: Object_mdecls_def)
apply safe
apply  (cut_tac xn_cases)   
apply  (simp (no_asm_simp) add: Classes_def standard_classes_def)
apply  (insert wf_idecl_all)
apply  (insert wf_cdecl_all)
apply  auto
done

subsubsection "max spec"

lemma appl_methds_Base_foo: 
"appl_methds tprg S (ClassT Base) \<lparr>name=foo, parTs=[NT]\<rparr> =  
  {((ClassT Base, \<lparr>access=Public,static=False,pars=[z],resT=Class Base\<rparr>)
    ,[Class Base])}"
apply (unfold appl_methds_def)
apply (simp (no_asm))
apply (subgoal_tac "tprg\<turnstile>NT\<preceq> Class Base")
apply  (auto simp add: cmheads_def Base_foo_defs)
done

lemma max_spec_Base_foo: "max_spec tprg S (ClassT Base) \<lparr>name=foo,parTs=[NT]\<rparr> = 
  {((ClassT Base, \<lparr>access=Public,static=False,pars=[z],resT=Class Base\<rparr>)
   , [Class Base])}"
by (simp add: max_spec_def appl_methds_Base_foo Collect_conv_if)

subsubsection "well-typedness"

schematic_goal wt_test: "\<lparr>prg=tprg,cls=Main,lcl=Map.empty(VName e\<mapsto>Class Base)\<rparr>\<turnstile>test ?pTs\<Colon>\<surd>"
apply (unfold test_def arr_viewed_from_def)
(* ?pTs = [Class Base] *)
apply (rule wtIs (* ;; *))
apply  (rule wtIs (* Ass *))
apply  (rule wtIs (* NewC *))
apply     (rule wtIs (* LVar *))
apply      (simp)
apply     (simp)
apply    (simp)
apply   (rule wtIs (* NewC *))
apply   (simp)
apply  (simp)
apply (rule wtIs (* Try *))
prefer 4
apply    (simp)
defer
apply    (rule wtIs (* Expr *))
apply    (rule wtIs (* Call *))
apply       (rule wtIs (* Acc *))
apply       (rule wtIs (* LVar *))
apply        (simp)
apply       (simp)
apply      (rule wtIs (* Cons *))
apply       (rule wtIs (* Lit *))
apply       (simp)
apply      (rule wtIs (* Nil *))
apply     (simp)
apply     (rule max_spec_Base_foo)
apply    (simp)
apply   (simp)
apply  (simp)
apply  (simp)
apply  (simp)
apply (rule wtIs (* While *))
apply  (rule wtIs (* Acc *))
apply   (rule wtIs (* AVar *))
apply   (rule wtIs (* Acc *))
apply   (rule wtIs (* FVar *))
apply    (rule wtIs (* StatRef *))
apply    (simp)
apply   (simp)
apply   (simp )
apply   (simp)
apply   (simp)
apply  (rule wtIs (* LVar *))
apply  (simp)
apply (rule wtIs (* Skip *))
done

subsubsection "definite assignment"

schematic_goal da_test: "\<lparr>prg=tprg,cls=Main,lcl=Map.empty(VName e\<mapsto>Class Base)\<rparr>
                  \<turnstile>{} \<guillemotright>\<langle>test ?pTs\<rangle>\<guillemotright> \<lparr>nrm={VName e},brk=\<lambda> l. UNIV\<rparr>"
apply (unfold test_def arr_viewed_from_def)
apply (rule da.Comp)
apply    (rule da.Expr)
apply    (rule da.AssLVar)
apply      (rule da.NewC)
apply     (rule assigned.select_convs)
apply    (simp)
apply   (rule da.Try)
apply      (rule da.Expr)
apply      (rule da.Call)
apply       (rule da.AccLVar)
apply         (simp)   
apply        (rule assigned.select_convs)
apply       (simp)
apply      (rule da.Cons)
apply       (rule da.Lit)
apply      (rule da.Nil)
apply     (rule da.Loop)
apply        (rule da.Acc)
apply         (simp)
apply        (rule da.AVar)
apply         (rule da.Acc)
apply          simp
apply         (rule da.FVar)
apply         (rule da.Cast)
apply         (rule da.Lit)
apply        (rule da.Lit)
apply       (rule da_Skip)
apply       (simp)
apply      (simp,rule assigned.select_convs)
apply     (simp)
apply    (simp,rule assigned.select_convs)
apply   (simp)
apply  simp
apply simp
apply (simp add: intersect_ts_def)
done


subsubsection "execution"

lemma alloc_one: "\<And>a obj. \<lbrakk>the (new_Addr h) = a; atleast_free h (Suc n)\<rbrakk> \<Longrightarrow>  
  new_Addr h = Some a \<and> atleast_free (h(a\<mapsto>obj)) n"
apply (frule atleast_free_SucD)
apply (drule atleast_free_Suc [THEN iffD1])
apply clarsimp
apply (frule new_Addr_SomeI)
apply force
done

declare fvar_def2 [simp] avar_def2 [simp] init_lvars_def2 [simp]
declare init_obj_def [simp] var_tys_def [simp] fields_table_def [simp]
declare BaseCl_def [simp] ExtCl_def [simp] Ext_foo_def [simp]
        Base_foo_defs  [simp]

ML \<open>ML_Thms.bind_thms ("eval_intros", map 
        (simplify (\<^context> |> Simplifier.del_simps @{thms Skip_eq}
          |> Simplifier.add_simps @{thms lvar_def}) o 
         rewrite_rule \<^context> [@{thm assign_def}, @{thm Let_def}]) @{thms eval.intros})\<close>
lemmas eval_Is = eval_Init eval_StatRef AbruptIs eval_intros

axiomatization
  a :: loc and
  b :: loc and
  c :: loc

abbreviation "one == Suc 0"
abbreviation "two == Suc one"
abbreviation "three == Suc two"
abbreviation "four == Suc three"

abbreviation
  "obj_a == \<lparr>tag=Arr (PrimT Boolean) 2
                ,values= Map.empty(Inr 0\<mapsto>Bool False, Inr 1\<mapsto>Bool False)\<rparr>"

abbreviation
  "obj_b == \<lparr>tag=CInst Ext
                ,values=(Map.empty(Inl (vee, Base)\<mapsto>Null, Inl (vee, Ext )\<mapsto>Intg 0))\<rparr>"

abbreviation
  "obj_c == \<lparr>tag=CInst (SXcpt NullPointer),values=CONST Map.empty\<rparr>"

abbreviation "arr_N == Map.empty(Inl (arr, Base)\<mapsto>Null)"
abbreviation "arr_a == Map.empty(Inl (arr, Base)\<mapsto>Addr a)"

abbreviation
  "globs1 == Map.empty(Inr Ext   \<mapsto>\<lparr>tag=undefined, values=Map.empty\<rparr>,
                     Inr Base  \<mapsto>\<lparr>tag=undefined, values=arr_N\<rparr>,
                     Inr Object\<mapsto>\<lparr>tag=undefined, values=Map.empty\<rparr>)"

abbreviation
  "globs2 == Map.empty(Inr Ext   \<mapsto>\<lparr>tag=undefined, values=Map.empty\<rparr>,
                     Inr Object\<mapsto>\<lparr>tag=undefined, values=Map.empty\<rparr>,
                     Inl a\<mapsto>obj_a,
                     Inr Base  \<mapsto>\<lparr>tag=undefined, values=arr_a\<rparr>)"

abbreviation "globs3 == globs2(Inl b\<mapsto>obj_b)"
abbreviation "globs8 == globs3(Inl c\<mapsto>obj_c)"
abbreviation "locs3 == Map.empty(VName e\<mapsto>Addr b)"
abbreviation "locs8 == locs3(VName z\<mapsto>Addr c)"

abbreviation "s0 == st Map.empty Map.empty"
abbreviation "s0' == Norm  s0"
abbreviation "s1 == st globs1 Map.empty"
abbreviation "s1' == Norm s1"
abbreviation "s2 == st globs2 Map.empty"
abbreviation "s2' == Norm s2"
abbreviation "s3 == st globs3 locs3"
abbreviation "s3' == Norm s3"
abbreviation "s7' == (Some (Xcpt (Std NullPointer)), s3)"
abbreviation "s8 == st globs8 locs8"
abbreviation "s8' == Norm s8"
abbreviation "s9' == (Some (Xcpt (Std IndOutBound)), s8)"


declare prod.inject [simp del]
schematic_goal exec_test: 
"\<lbrakk>the (new_Addr (heap  s1)) = a;  
  the (new_Addr (heap ?s2)) = b;  
  the (new_Addr (heap ?s3)) = c\<rbrakk> \<Longrightarrow>  
  atleast_free  (heap s0) four \<Longrightarrow>  
  tprg\<turnstile>s0' \<midarrow>test [Class Base]\<rightarrow> ?s9'"
apply (unfold test_def arr_viewed_from_def)
(* ?s9' = s9' *)
apply (simp (no_asm_use))
apply (drule (1) alloc_one,clarsimp)
apply (rule eval_Is (* ;; *))
apply  (erule_tac V = "the (new_Addr _) = c" in thin_rl)
apply  (erule_tac [2] V = "new_Addr _ = Some a" in thin_rl)
apply  (erule_tac [2] V = "atleast_free _ four" in thin_rl)
apply  (rule eval_Is (* Expr *))
apply  (rule eval_Is (* Ass *))
apply   (rule eval_Is (* LVar *))
apply  (rule eval_Is (* NewC *))
      (* begin init Ext *)
apply   (erule_tac V = "the (new_Addr _) = b" in thin_rl)
apply   (erule_tac V = "atleast_free _ three" in thin_rl)
apply   (erule_tac [2] V = "atleast_free _ four" in thin_rl)
apply   (erule_tac [2] V = "new_Addr _ = Some a" in thin_rl)
apply   (rule eval_Is (* Init Ext *))
apply   (simp)
apply   (rule conjI)
prefer 2 apply (rule conjI HOL.refl)+
apply   (rule eval_Is (* Init Base *))
apply   (simp add: arr_viewed_from_def)
apply   (rule conjI)
apply    (rule eval_Is (* Init Object *))
apply    (simp)
apply   (simp)
apply   (rule conjI, rule_tac [2] HOL.refl)
apply   (rule eval_Is (* Expr *))
apply   (rule eval_Is (* Ass *))
apply    (rule eval_Is (* FVar *))
apply         (rule init_done, simp)
apply        (rule eval_Is (* StatRef *))
apply       (simp)
apply     (simp add: check_field_access_def Let_def) 
apply   (rule eval_Is (* NewA *))
apply     (simp)
apply    (rule eval_Is (* Lit *))
apply   (simp)
apply   (rule halloc.New)
apply    (simp (no_asm_simp))
apply   (drule atleast_free_weaken,drule atleast_free_weaken)
apply   (simp (no_asm_simp))
apply  (simp add: upd_gobj_def)
      (* end init Ext *)
apply  (rule halloc.New)
apply   (drule alloc_one)
prefer 2 apply fast
apply   (simp (no_asm_simp))
apply  (drule atleast_free_weaken)
apply  force
apply (simp)
apply (drule alloc_one)
apply  (simp (no_asm_simp))
apply clarsimp
apply (erule_tac V = "atleast_free _ three" in thin_rl)
apply (drule_tac x = "a" in new_AddrD2 [THEN spec])
apply (simp (no_asm_use))
apply (rule eval_Is (* Try *))
apply   (rule eval_Is (* Expr *))
      (* begin method call *)
apply   (rule eval_Is (* Call *))
apply      (rule eval_Is (* Acc *))
apply      (rule eval_Is (* LVar *))
apply     (rule eval_Is (* Cons *))
apply      (rule eval_Is (* Lit *))
apply     (rule eval_Is (* Nil *))
apply    (simp)
apply    (simp)
apply    (subgoal_tac
             "tprg\<turnstile>(Ext,mdecl Ext_foo) in Ext dyn_accessible_from Main")
apply      (simp add: check_method_access_def Let_def
                      invocation_declclass_def dynlookup_def dynmethd_Ext_foo)
apply      (rule Ext_foo_dyn_accessible)
apply   (rule eval_Is (* Methd *))
apply   (simp add: body_def Let_def)
apply   (rule eval_Is (* Body *))
apply     (rule init_done, simp)
apply       (simp add: invocation_declclass_def dynlookup_def dynmethd_Ext_foo)
apply    (simp add: invocation_declclass_def dynlookup_def dynmethd_Ext_foo)
apply    (rule eval_Is (* Comp *))
apply     (rule eval_Is (* Expr *))
apply     (rule eval_Is (* Ass *))
apply      (rule eval_Is (* FVar *))
apply         (rule init_done, simp)
apply        (rule eval_Is (* Cast *))
apply         (rule eval_Is (* Acc *))
apply         (rule eval_Is (* LVar *))
apply        (simp)
apply       (simp split del: if_split)
apply      (simp add: check_field_access_def Let_def)
apply     (rule eval_Is (* XcptE *))
apply    (simp)
apply    (rule conjI)
apply     (simp)
apply    (rule eval_Is (* Comp *))
apply   (simp)
      (* end method call *)
apply  simp
apply  (rule sxalloc.intros)
apply  (rule halloc.New)
apply   (erule alloc_one [THEN conjunct1])
apply   (simp (no_asm_simp))
apply  (simp (no_asm_simp))
apply (simp add: gupd_def lupd_def obj_ty_def split del: if_split)
apply (drule alloc_one [THEN conjunct1])
apply  (simp (no_asm_simp))
apply (erule_tac V = "atleast_free _ two" in thin_rl)
apply (drule_tac x = "a" in new_AddrD2 [THEN spec])
apply simp
apply (rule eval_Is (* While *))
apply  (rule eval_Is (* Acc *))
apply  (rule eval_Is (* AVar *))
apply    (rule eval_Is (* Acc *))
apply    (rule eval_Is (* FVar *))
apply      (rule init_done, simp)
apply     (rule eval_Is (* StatRef *))
apply    (simp)
apply    (simp add: check_field_access_def Let_def)
apply   (rule eval_Is (* Lit *))
apply  (simp (no_asm_simp))
apply (auto simp add: in_bounds_def)
done
declare prod.inject [simp]

end
