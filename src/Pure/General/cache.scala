/*  Title:      Pure/General/cache.scala
    Author:     Makarius

Cache for partial sharing (weak table).
*/

package isabelle


import java.util.{Collections, WeakHashMap, Map => JMap}
import java.lang.ref.WeakReference


object Cache {
  val default_max_string = 100
  val default_initial_size = 131071

  def make(
      max_string: Int = default_max_string,
      initial_size: Int = default_initial_size): Cache =
    new Memory_Cache(max_string, initial_size)

  val none: Cache = new Cache { }
}

trait Cache {
  def no_cache: Boolean = true
  def string(x: String): String = x
}

class Memory_Cache(max_string: Int, initial_size: Int) extends Cache {
  override val no_cache: Boolean = max_string == 0

  private type Table = JMap[Any, WeakReference[Any]]
  protected val table: Table | Null =
    if (max_string == 0) null
    else Collections.synchronizedMap(new WeakHashMap[Any, WeakReference[Any]](initial_size))

  override def toString: String =
    proper_value(table) match {
      case None => "Cache.none"
      case Some(t) => "Cache(size = " + t.size + ")"
    }

  protected def lookup[A](x: A): Option[A] = {
    if (table == null) None
    else {
      val ref = table.asInstanceOf[Table].get(x)
      if (ref == null) None
      else proper_value(ref.asInstanceOf[WeakReference[A]].get)
    }
  }

  protected def store[A](x: A): A = {
    if (table == null || x.asInstanceOf[Any] == null) x
    else {
      table.asInstanceOf[Table].put(x, new WeakReference[Any](x))
      x
    }
  }

  protected def cache_string(x: String): String = {
    if (x.asInstanceOf[Any] == null) x
    else if (x == "") ""
    else if (x == "true") "true"
    else if (x == "false") "false"
    else if (x == "0.0") "0.0"
    else if (Symbol.is_static_spaces(x)) Symbol.spaces(x.length)
    else if (Library.is_small_int(x)) Library.signed_string_of_int(Integer.parseInt(x))
    else {
      lookup(x) match {
        case Some(y) => y
        case None =>
          val z = Library.isolate_substring(x)
          if (z.length > max_string) z else store(z)
      }
    }
  }

  // main methods
  override def string(x: String): String = synchronized { cache_string(x) }
}
