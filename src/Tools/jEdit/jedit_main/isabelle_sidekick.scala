/*  Title:      Tools/jEdit/jedit_main/isabelle_sidekick.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

SideKick parsers for Isabelle proof documents.
*/

package isabelle.jedit_main


import isabelle._
import isabelle.jedit._

import javax.swing.text.Position
import javax.swing.Icon

import org.gjt.sp.jedit.Buffer
import sidekick.{SideKickParser, SideKickParsedData, IAsset}


object Isabelle_Sidekick {
  def int_to_pos(offset: Text.Offset): Position =
    new Position {
      def getOffset: Text.Offset = offset
      override def toString: String = offset.toString
    }

  def root_data(buffer: Buffer): SideKickParsedData = {
    val data = new SideKickParsedData(buffer.getName)
    data.getAsset(data.root).setEnd(int_to_pos(buffer.getLength))
    data
  }

  class Keyword_Asset(keyword: String, text: String, range: Text.Range) extends IAsset {
    private val style = GUI.Style_HTML
    private val css = GUI.imitate_font_css(GUI.label_font())

    protected var _name: String = text
    protected var _start: Position = int_to_pos(range.start)
    protected var _end: Position = int_to_pos(range.stop)
    override def getIcon: Icon = null
    override def getShortString: String = {
      val n = keyword.length
      val s =
        _name.indexOf(keyword) match {
          case i if i >= 0 && n > 0 =>
            style.make_text(_name.substring(0, i)) +
            style.make_bold(keyword) +
            style.make_text(_name.substring(i + n))
          case _ => style.make_text(_name)
        }
      style.enclose_style(css, s)
    }
    override def getLongString: String = _name
    override def getName: String = _name
    override def setName(name: String): Unit = _name = name
    override def getStart: Position = _start
    override def setStart(start: Position): Unit = _start = start
    override def getEnd: Position = _end
    override def setEnd(end: Position): Unit = _end = end
    override def toString: String = _name
  }

  class Asset(name: String, range: Text.Range) extends Keyword_Asset("", name, range)

  def swing_markup_tree(
    tree: Markup_Tree,
    parent: Tree_View.Node,
    swing_node: Text.Info[List[XML.Elem]] => Tree_View.Node
  ): Unit = {
    for ((_, entry) <- tree.branches) {
      val node = swing_node(Text.Info(entry.range, entry.markup))
      swing_markup_tree(entry.subtree, node, swing_node)
      parent.add(node)
    }
  }
}


class Isabelle_Sidekick(name: String) extends SideKickParser(name) {
  override def supportsCompletion = false


  /* parsing */

  @volatile protected var stopped = false
  override def stop(): Unit = { stopped = true }

  def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean = false

  def parse(buffer: Buffer, error_source: errorlist.DefaultErrorSource): SideKickParsedData = {
    stopped = false

    // FIXME lock buffer (!??)
    val data = Isabelle_Sidekick.root_data(buffer)
    val syntax = Isabelle.buffer_syntax(buffer)
    val ok =
      if (syntax.isDefined) {
        val ok = parser(buffer, syntax.get, data)
        if (stopped) { data.root.add(Tree_View.Node("<stopped>")); true }
        else ok
      }
      else false
    if (!ok) data.root.add(Tree_View.Node("<ignored>"))

    data
  }
}


class Isabelle_Sidekick_Structure(
  name: String,
  node_name: Buffer => Option[Document.Node.Name],
  parse: (Outer_Syntax, Document.Node.Name, CharSequence) => List[Document_Structure.Document]
) extends Isabelle_Sidekick(name) {
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean = {
    def make_tree(
      parent: Tree_View.Node,
      offset: Text.Offset,
      documents: List[Document_Structure.Document]
    ): Unit = {
      documents.foldLeft(offset) {
        case (i, document) =>
          document match {
            case Document_Structure.Block(name, text, body) =>
              val range = Text.Range(i, i + document.length)
              val node =
                Tree_View.Node(
                  new Isabelle_Sidekick.Keyword_Asset(name, Library.first_line(text), range))
              parent.add(node)
              make_tree(node, i, body)
            case _ =>
          }
          i + document.length
      }
    }

    node_name(buffer) match {
      case Some(name) =>
        make_tree(data.root, 0, parse(syntax, name, JEdit_Lib.buffer_text(buffer)))
        true
      case None =>
        false
    }
  }
}

class Isabelle_Sidekick_Default extends
  Isabelle_Sidekick_Structure("isabelle",
    PIDE.resources.theory_node_name, Document_Structure.parse_sections)

class Isabelle_Sidekick_Context extends
  Isabelle_Sidekick_Structure("isabelle-context",
    PIDE.resources.theory_node_name, Document_Structure.parse_blocks)

class Isabelle_Sidekick_Options extends
  Isabelle_Sidekick_Structure("isabelle-options",
    _ => Some(Document.Node.Name("options")), Document_Structure.parse_sections)

class Isabelle_Sidekick_Root extends
  Isabelle_Sidekick_Structure("isabelle-root",
    _ => Some(Document.Node.Name("ROOT")), Document_Structure.parse_sections)

class Isabelle_Sidekick_ML extends
  Isabelle_Sidekick_Structure("isabelle-ml",
    buffer => Some(PIDE.resources.node_name(buffer)),
    (_, _, text) => Document_Structure.parse_ml_sections(false, text))

class Isabelle_Sidekick_SML extends
  Isabelle_Sidekick_Structure("isabelle-sml",
    buffer => Some(PIDE.resources.node_name(buffer)),
    (_, _, text) => Document_Structure.parse_ml_sections(true, text))


class Isabelle_Sidekick_Markup extends Isabelle_Sidekick("isabelle-markup") {
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean = {
    val opt_snapshot =
      Document_Model.get_model(buffer) match {
        case Some(model) if model.is_theory =>
          GUI_Thread.now { Some(Document_Model.snapshot(model)) }
        case _ => None
      }
    opt_snapshot match {
      case Some(snapshot) =>
        for ((command, command_start) <- snapshot.node.command_iterator() if !stopped) {
          val markup =
            snapshot.state.command_markup(
              snapshot.version, command, Command.Markup_Index.markup,
                command.range, Markup.Elements.full)
          Isabelle_Sidekick.swing_markup_tree(markup, data.root,
            { (info: Text.Info[List[XML.Elem]]) =>
              val range = info.range + command_start
              val content = command.source(info.range).replace('\n', ' ')
              val info_text = Pretty.formatted(Pretty.fbreaks(info.info), margin = 40.0).mkString

              Tree_View.Node(
                new Isabelle_Sidekick.Asset(command.toString, range) {
                  override def getShortString: String = content
                  override def getLongString: String = info_text
                  override def toString: String = quote(content) + " " + range.toString
                })
            })
        }
        true
      case None => false
    }
  }
}


class Isabelle_Sidekick_News extends Isabelle_Sidekick("isabelle-news") {
  private val Heading1 = """^New in (.*)\w*$""".r
  private val Heading2 = """^\*\*\*\w*(.*)\w*\*\*\*\w*$""".r

  private def make_node(s: String, start: Text.Offset, stop: Text.Offset): Tree_View.Node =
    Tree_View.Node(new Isabelle_Sidekick.Asset(s, Text.Range(start, stop)))

  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean = {
    var offset = 0
    var end_offset = 0

    var start1: Option[(Int, String, Vector[Tree_View.Node])] = None
    var start2: Option[(Int, String)] = None

    def close1(): Unit =
      start1 match {
        case Some((start_offset, s, body)) =>
          val node = make_node(s, start_offset, end_offset)
          body.foreach(node.add(_))
          data.root.add(node)
          start1 = None
        case None =>
      }

    def close2(): Unit =
      start2 match {
        case Some((start_offset, s)) =>
          start1 match {
            case Some((start_offset1, s1, body)) =>
              val node = make_node(s, start_offset, end_offset)
              start1 = Some((start_offset1, s1, body :+ node))
            case None =>
          }
          start2 = None
        case None =>
      }

    for (line <- split_lines(JEdit_Lib.buffer_text(buffer)) if !stopped) {
      line match {
        case Heading1(s) => close2(); close1(); start1 = Some((offset, s, Vector()))
        case Heading2(s) => close2(); start2 = Some((offset, s))
        case _ =>
      }
      offset += line.length + 1
      if (!line.forall(Character.isSpaceChar)) end_offset = offset
    }
    if (!stopped) { close2(); close1() }

    true
  }
}

class Isabelle_Sidekick_Bibtex extends SideKickParser("bibtex") {
  override def supportsCompletion = false

  private class Asset(label: String, label_html: String, range: Text.Range, source: String)
    extends Isabelle_Sidekick.Asset(label, range) {
      override def getShortString: String = label_html
      override def getLongString: String = source
    }

  def parse(buffer: Buffer, error_source: errorlist.DefaultErrorSource): SideKickParsedData = {
    val data = Isabelle_Sidekick.root_data(buffer)

    try {
      val style = GUI.Style_HTML
      var offset = 0
      for (chunk <- Bibtex.parse(JEdit_Lib.buffer_text(buffer))) {
        val kind = chunk.kind
        val name = chunk.name
        val source = chunk.source
        if (kind != "") {
          val label = kind + if_proper(name, " " + name)
          val label_html = style.enclose(GUI.Name(name, kind = kind, style = style).toString)
          val range = Text.Range(offset, offset + source.length)
          val asset = new Asset(label, label_html, range, source)
          data.root.add(Tree_View.Node(asset))
        }
        offset += source.length
      }
      data
    }
    catch { case ERROR(msg) => Output.warning(msg); null }
  }
}
