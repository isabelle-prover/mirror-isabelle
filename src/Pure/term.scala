/*  Title:      Pure/term.scala
    Author:     Makarius

Lambda terms, types, sorts.

Note: Isabelle/ML is the primary environment for logical operations.
*/

package isabelle


object Term {
  /* types and terms */

  sealed case class Indexname(name: String, index: Int = 0) {
    private lazy val hash: Int = (name, index).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      if (index == -1) name
      else {
        val dot =
          Symbol.explode(name).reverse match {
            case _ :: s :: _ if s == Symbol.sub_decoded || s == Symbol.sub => false
            case c :: _ => Symbol.is_digit(c)
            case _ => true
          }
        if (dot) "?" + name + "." + index
        else if (index != 0) "?" + name + index
        else "?" + name
      }
  }

  type Class = String
  type Sort = List[Class]

  sealed abstract class Typ
  case class Type(name: String, args: List[Typ] = Nil) extends Typ {
    private lazy val hash: Int = ("Type", name, args).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      if (this == dummyT) "_"
      else "Type(" + name + if_proper(args, "," + args) + ")"
  }
  case class TFree(name: String, sort: Sort = Nil) extends Typ {
    private lazy val hash: Int = ("TFree", name, sort).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      "TFree(" + name + if_proper(sort, "," + sort) + ")"
  }
  case class TVar(name: Indexname, sort: Sort = Nil) extends Typ {
    private lazy val hash: Int = ("TVar", name, sort).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      "TVar(" + name + if_proper(sort, "," + sort) + ")"
  }
  val dummyT: Type = Type("dummy")

  sealed abstract class Term {
    def head: Term =
      this match {
        case App(fun, _) => fun.head
        case _ => this
      }
  }
  case class Const(name: String, typargs: List[Typ] = Nil) extends Term {
    private lazy val hash: Int = ("Const", name, typargs).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      if (this == dummy) "_"
      else "Const(" + name + if_proper(typargs, "," + typargs) + ")"
  }
  case class Free(name: String, typ: Typ = dummyT) extends Term {
    private lazy val hash: Int = ("Free", name, typ).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      "Free(" + name + (if (typ == dummyT) "" else "," + typ) + ")"
  }
  case class Var(name: Indexname, typ: Typ = dummyT) extends Term {
    private lazy val hash: Int = ("Var", name, typ).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      "Var(" + name + (if (typ == dummyT) "" else "," + typ) + ")"
  }
  case class Bound(index: Int) extends Term
  case class Abs(name: String, typ: Typ, body: Term) extends Term {
    private lazy val hash: Int = ("Abs", name, typ, body).hashCode()
    override def hashCode(): Int = hash
  }
  case class App(fun: Term, arg: Term) extends Term {
    private lazy val hash: Int = ("App", fun, arg).hashCode()
    override def hashCode(): Int = hash

    override def toString: String =
      this match {
        case OFCLASS(ty, c) => "OFCLASS(" + ty + "," + c + ")"
        case _ => "App(" + fun + "," + arg + ")"
      }
  }

  def dummy_pattern(ty: Typ): Term = Const("Pure.dummy_pattern", List(ty))
  val dummy: Term = dummy_pattern(dummyT)

  sealed abstract class Proof
  case object MinProof extends Proof
  case class PBound(index: Int) extends Proof
  case class Abst(name: String, typ: Typ, body: Proof) extends Proof {
    private lazy val hash: Int = ("Abst", name, typ, body).hashCode()
    override def hashCode(): Int = hash
  }
  case class AbsP(name: String, hyp: Term, body: Proof) extends Proof {
    private lazy val hash: Int = ("AbsP", name, hyp, body).hashCode()
    override def hashCode(): Int = hash
  }
  case class Appt(fun: Proof, arg: Term) extends Proof {
    private lazy val hash: Int = ("Appt", fun, arg).hashCode()
    override def hashCode(): Int = hash
  }
  case class AppP(fun: Proof, arg: Proof) extends Proof {
    private lazy val hash: Int = ("AppP", fun, arg).hashCode()
    override def hashCode(): Int = hash
  }
  case class Hyp(hyp: Term) extends Proof {
    private lazy val hash: Int = ("Hyp", hyp).hashCode()
    override def hashCode(): Int = hash
  }
  case class PAxm(name: String, types: List[Typ]) extends Proof {
    private lazy val hash: Int = ("PAxm", name, types).hashCode()
    override def hashCode(): Int = hash
  }
  case class PClass(typ: Typ, cls: Class) extends Proof {
    private lazy val hash: Int = ("PClass", typ, cls).hashCode()
    override def hashCode(): Int = hash
  }
  case class Oracle(name: String, prop: Term, types: List[Typ]) extends Proof {
    private lazy val hash: Int = ("Oracle", name, prop, types).hashCode()
    override def hashCode(): Int = hash
  }
  case class PThm(serial: Long, theory_name: String, thm_name: Thm_Name, types: List[Typ]) extends Proof {
    private lazy val hash: Int = ("PThm", serial, theory_name, thm_name, types).hashCode()
    override def hashCode(): Int = hash
  }


  /* type classes within the logic */

  object Class_Const {
    val suffix = "_class"
    def apply(c: Class): String = c + suffix
    def unapply(s: String): Option[Class] =
      if (s.endsWith(suffix)) Some(s.substring(0, s.length - suffix.length)) else None
  }

  object OFCLASS {
    def apply(ty: Typ, s: Sort): List[Term] = s.map(c => apply(ty, c))

    def apply(ty: Typ, c: Class): Term =
      App(Const(Class_Const(c), List(ty)), Const(Pure_Thy.TYPE, List(ty)))

    def unapply(t: Term): Option[(Typ, String)] =
      t match {
        case App(Const(Class_Const(c), List(ty)), Const(Pure_Thy.TYPE, List(ty1)))
        if ty == ty1 => Some((ty, c))
        case _ => None
      }
  }



  /** cache **/

  object Cache {
    def make(
        compress: Compress.Cache = Compress.Cache.make(),
        max_string: Int = isabelle.Cache.default_max_string,
        initial_size: Int = isabelle.Cache.default_initial_size): Cache =
      new Cache(compress, initial_size, max_string)

    val none: Cache = make(max_string = 0)
  }

  class Cache(compress: Compress.Cache, max_string: Int, initial_size: Int)
  extends XML.Cache(compress, max_string, initial_size) {
    protected def cache_indexname(x: Indexname): Indexname =
      lookup(x) getOrElse store(Indexname(cache_string(x.name), x.index))

    protected def cache_sort(x: Sort): Sort =
      if (x.isEmpty) Nil
      else lookup(x) getOrElse store(x.map(cache_string))

    protected def cache_typ(x: Typ): Typ = {
      if (x == dummyT) dummyT
      else
        lookup(x) match {
          case Some(y) => y
          case None =>
            x match {
              case Type(name, args) => store(Type(cache_string(name), cache_typs(args)))
              case TFree(name, sort) => store(TFree(cache_string(name), cache_sort(sort)))
              case TVar(name, sort) => store(TVar(cache_indexname(name), cache_sort(sort)))
            }
        }
    }

    protected def cache_typs(x: List[Typ]): List[Typ] = {
      if (x.isEmpty) Nil
      else {
        lookup(x) match {
          case Some(y) => y
          case None => store(x.map(cache_typ))
        }
      }
    }

    protected def cache_term(x: Term): Term = {
      lookup(x) match {
        case Some(y) => y
        case None =>
          x match {
            case Const(name, typargs) => store(Const(cache_string(name), cache_typs(typargs)))
            case Free(name, typ) => store(Free(cache_string(name), cache_typ(typ)))
            case Var(name, typ) => store(Var(cache_indexname(name), cache_typ(typ)))
            case Bound(_) => store(x)
            case Abs(name, typ, body) =>
              store(Abs(cache_string(name), cache_typ(typ), cache_term(body)))
            case App(fun, arg) => store(App(cache_term(fun), cache_term(arg)))
          }
      }
    }

    protected def cache_thm_name(x: Thm_Name): Thm_Name =
      if (x == Thm_Name.empty) Thm_Name.empty
      else lookup(x) getOrElse store(Thm_Name(cache_string(x.name), x.index))

    protected def cache_proof(x: Proof): Proof = {
      if (x == MinProof) MinProof
      else {
        lookup(x) match {
          case Some(y) => y
          case None =>
            (x: @unchecked) match {
              case PBound(_) => store(x)
              case Abst(name, typ, body) =>
                store(Abst(cache_string(name), cache_typ(typ), cache_proof(body)))
              case AbsP(name, hyp, body) =>
                store(AbsP(cache_string(name), cache_term(hyp), cache_proof(body)))
              case Appt(fun, arg) => store(Appt(cache_proof(fun), cache_term(arg)))
              case AppP(fun, arg) => store(AppP(cache_proof(fun), cache_proof(arg)))
              case Hyp(hyp) => store(Hyp(cache_term(hyp)))
              case PAxm(name, types) => store(PAxm(cache_string(name), cache_typs(types)))
              case PClass(typ, cls) => store(PClass(cache_typ(typ), cache_string(cls)))
              case Oracle(name, prop, types) =>
                store(Oracle(cache_string(name), cache_term(prop), cache_typs(types)))
              case PThm(serial, theory_name, thm_name, types) =>
                store(PThm(serial, cache_string(theory_name), cache_thm_name(thm_name),
                  cache_typs(types)))
            }
        }
      }
    }

    // main methods
    def indexname(x: Indexname): Indexname =
      if (no_cache) x else synchronized { cache_indexname(x) }
    def sort(x: Sort): Sort =
      if (no_cache) x else synchronized { cache_sort(x) }
    def typ(x: Typ): Typ =
      if (no_cache) x else synchronized { cache_typ(x) }
    def term(x: Term): Term =
      if (no_cache) x else synchronized { cache_term(x) }
    def proof(x: Proof): Proof =
      if (no_cache) x else synchronized { cache_proof(x) }

    def position(x: Position.T): Position.T =
      if (no_cache) x
      else synchronized { x.map({ case (a, b) => (cache_string(a), cache_string(b)) }) }
  }
}
