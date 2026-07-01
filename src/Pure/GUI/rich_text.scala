/*  Title:      Pure/GUI/rich_text.scala
    Author:     Makarius

Support for rendering of rich text, based on individual messages (XML.Elem).
*/

package isabelle


import java.lang.ref.WeakReference

import javax.swing.JComponent

import scala.collection.mutable


object Rich_Text {
  /* margin */

  def make_margin(metric: Font_Metric, margin: Int, limit: Int = -1): Int = {
    val m = (margin * metric.average).toInt
    (if (limit < 0) m else m min limit) max 20
  }

  def component_margin(metric: Font_Metric, component: JComponent): Int =
    make_margin(metric, (component.getWidth.toDouble / metric.average_width).toInt)


  /* format */

  sealed case class Formatted(id: Document_ID.Generic, body: XML.Body) {
    lazy val text: String = XML.content(body)
    lazy val markups: Command.Markups = Command.Markups.init(Markup_Tree.from_XML(body))
    def command(results: Command.Results): Command =
      Command.unparsed(text, id = id, results = results, markups = markups)
  }

  def format(
    msgs: List[XML.Elem],
    margin: Double,
    metric: Font_Metric,
    unicode_symbols: Boolean,
    cache: Cache = Cache.none
  ): List[Formatted] = {
    def recode(s: String): String = Symbol.output(unicode_symbols, s)

    def run(msg: XML.Elem): Formatted =
      Formatted(Protocol_Message.get_serial(msg),
        cache.body(Pretty.formatted(List(msg), recode = recode, margin = margin, metric = metric)))

    val result = new mutable.ListBuffer[Formatted]
    for (msg <- msgs) {
      if (result.nonEmpty) result += Formatted(Document_ID.make(), Pretty.Separator)
      result += cache.formatted(Cache.Args(msg, margin, metric, unicode_symbols), run(msg))
      Exn.Interrupt.expose()
    }
    result.toList
  }

  def formatted_lines(formatted: List[Formatted]): Int =
    if (formatted.isEmpty) 0
    else {
      1 + formatted.iterator.map(form =>
        XML.traverse_text(form.body, 0, (n, s) => n + Library.count_newlines(s))).sum
    }

  def formatted_margin(metric: Font_Metric, formatted: List[Formatted]): Double =
    split_lines(formatted.map(_.text).mkString)
      .foldLeft(0.0) { case (m, line) => m max metric(line) }


  /* cache */

  object Cache {
    def make(
        compress: Compress.Cache = Compress.Cache.make(),
        max_string: Int = isabelle.Cache.default_max_string,
        initial_size: Int = isabelle.Cache.default_initial_size): Cache =
      new Memory_Cache(compress, initial_size, max_string)

    val none: Cache = new Cache { }

    sealed case class Args(
      msg: XML.Elem, margin: Double, metric: Font_Metric, unicode_symbols: Boolean)
  }

  trait Cache extends Term.Cache {
    def formatted(args: Cache.Args, run: => Formatted): Formatted = run
  }

  class Memory_Cache(compress: Compress.Cache, max_string: Int, initial_size: Int)
  extends Term.Memory_Cache(compress, max_string, initial_size) with Cache {
    override def formatted(x: Cache.Args, run: => Formatted): Formatted = {
      if (table == null) run
      else {
        val get: Option[Formatted] =
          table.get(x) match {
            case ref: WeakReference[Any] => proper_value(ref.get.asInstanceOf[Formatted])
            case null => None
        }

        val y = get.getOrElse(run)
        table.synchronized { if (get.isEmpty) table.put(x, new WeakReference[Any](y)) }
        y
      }
    }
  }
}
