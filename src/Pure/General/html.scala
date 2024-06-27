/*  Title:      Pure/General/html.scala
    Author:     Makarius

HTML presentation elements.
*/

package isabelle


import org.jsoup.nodes.{Entities => Jsoup_Entities, Document => Jsoup_Document}
import org.jsoup.Jsoup


object HTML {
  /* attributes */

  class Attribute(val name: String, value: String) {
    def xml: XML.Attribute = name -> value
    def apply(elem: XML.Elem): XML.Elem = elem + xml
  }

  def id(s: String): Attribute = new Attribute("id", s)
  def class_(name: String): Attribute = new Attribute("class", name)

  def width(w: Int): Attribute = new Attribute("width", w.toString)
  def height(h: Int): Attribute = new Attribute("height", h.toString)
  def size(w: Int, h: Int)(elem: XML.Elem): XML.Elem = width(w)(height(h)(elem))

  val entity_def: Attribute = class_("entity_def")
  val entity_ref: Attribute = class_("entity_ref")


  /* structured markup operators */

  def text(txt: String): XML.Body = if (txt.isEmpty) Nil else List(XML.Text(txt))
  val break: XML.Body = List(XML.elem("br"))
  val nl: XML.Body = List(XML.Text("\n"))

  class Operator(val name: String) {
    def apply(body: XML.Body): XML.Elem = XML.elem(name, body)
    def apply(att: Attribute, body: XML.Body): XML.Elem = att(apply(body))
    def apply(c: String, body: XML.Body): XML.Elem = apply(class_(c), body)
  }

  class Heading(name: String) extends Operator(name) {
    def apply(txt: String): XML.Elem = super.apply(text(txt))
    def apply(att: Attribute, txt: String): XML.Elem = super.apply(att, text(txt))
    def apply(c: String, txt: String): XML.Elem = super.apply(c, text(txt))
  }

  val div = new Operator("div")
  val span = new Operator("span")
  val pre = new Operator("pre")
  val par = new Operator("p")
  val sub = new Operator("sub")
  val sup = new Operator("sup")
  val emph = new Operator("em")
  val bold = new Operator("b")
  val code = new Operator("code")
  val item = new Operator("li")
  val list = new Operator("ul")
  val `enum` = new Operator("ol")
  val descr = new Operator("dl")
  val dt = new Operator("dt")
  val dd = new Operator("dd")

  val title = new Heading("title")
  val chapter = new Heading("h1")
  val section = new Heading("h2")
  val subsection = new Heading("h3")
  val subsubsection = new Heading("h4")
  val paragraph = new Heading("h5")
  val subparagraph = new Heading("h6")

  def itemize(items: List[XML.Body]): XML.Elem = list(items.map(item(_)))
  def enumerate(items: List[XML.Body]): XML.Elem = `enum`(items.map(item(_)))
  def description(items: List[(XML.Body, XML.Body)]): XML.Elem =
    descr(items.flatMap({ case (x, y) => List(dt(x), dd(y)) }))

  def link(href: String, body: XML.Body): XML.Elem =
    XML.Elem(Markup("a", List("href" -> href)), if (body.isEmpty) text(href) else body)

  def link(path: Path, body: XML.Body): XML.Elem = link(path.implode, body)

  def image(src: String, alt: String = ""): XML.Elem =
    XML.Elem(Markup("img", List("src" -> src) ::: proper_string(alt).map("alt" -> _).toList), Nil)

  def source(body: XML.Body): XML.Elem = pre("source", body)
  def source(src: String): XML.Elem = source(text(src))

  def style(s: String): XML.Elem = XML.elem("style", text(s))
  def style_file(href: String): XML.Elem =
    XML.Elem(Markup("link", List("rel" -> "stylesheet", "type" -> "text/css", "href" -> href)), Nil)
  def style_file(path: Path): XML.Elem = style_file(Url.print_file(path.file))

  def script(s: String): XML.Elem = XML.elem("script", List(raw(text(s))))
  def script_file(href: String): XML.Elem = XML.Elem(Markup("script", List("src" -> href)), Nil)
  def script_file(path: Path): XML.Elem = script_file(Url.print_file(path.file))


  /* href */

  def relative_href(location: Path, base: Option[Path] = None): String = {
    val path =
      base match {
        case None =>
          val path = location.expand
          if (path.is_absolute) Exn.error("Relative href location expected: " + path) else path
        case Some(base_dir) =>
          val path1 = base_dir.absolute_file.toPath
          val path2 = location.absolute_file.toPath
          try { File.path(path1.relativize(path2).toFile) }
          catch {
            case _: IllegalArgumentException =>
              Exn.error("Failed to relativize href location " + path2 + " with wrt. base " + path1)
          }
      }
    if (path.is_current) "" else path.implode
  }


  /* output text with control symbols */

  private val control: Map[Symbol.Symbol, Operator] =
    Map(
      Symbol.sub -> sub, Symbol.sub_decoded -> sub,
      Symbol.sup -> sup, Symbol.sup_decoded -> sup,
      Symbol.bold -> bold, Symbol.bold_decoded -> bold)

  private val control_block_begin: Map[Symbol.Symbol, Operator] =
    Map(
      Symbol.bsub -> sub, Symbol.bsub_decoded -> sub,
      Symbol.bsup -> sup, Symbol.bsup_decoded -> sup)

  private val control_block_end: Map[Symbol.Symbol, Operator] =
    Map(
      Symbol.esub -> sub, Symbol.esub_decoded -> sub,
      Symbol.esup -> sup, Symbol.esup_decoded -> sup)

  def is_control(sym: Symbol.Symbol): Boolean = control.isDefinedAt(sym)

  def is_control_block_begin(sym: Symbol.Symbol): Boolean = control_block_begin.isDefinedAt(sym)
  def is_control_block_end(sym: Symbol.Symbol): Boolean = control_block_end.isDefinedAt(sym)
  def is_control_block_pair(bg: Symbol.Symbol, en: Symbol.Symbol): Boolean = {
    val bg_decoded = Symbol.decode(bg)
    val en_decoded = Symbol.decode(en)
    bg_decoded == Symbol.bsub_decoded && en_decoded == Symbol.esub_decoded ||
    bg_decoded == Symbol.bsup_decoded && en_decoded == Symbol.esup_decoded
  }

  def check_control_blocks(body: XML.Body): Boolean = {
    var ok = true
    var open = List.empty[Symbol.Symbol]
    for { case XML.Text(text) <- body; sym <- Symbol.iterator(text) } {
      if (is_control_block_begin(sym)) open ::= sym
      else if (is_control_block_end(sym)) {
        open match {
          case bg :: rest if is_control_block_pair(bg, sym) => open = rest
          case _ => ok = false
        }
      }
    }
    ok && open.isEmpty
  }

  def output(
    s: StringBuilder,
    text: String,
    control_blocks: Boolean,
    hidden: Boolean,
    permissive: Boolean
  ): Unit = {
    val xml_output = new XML.Output(s)

    def output_string(str: String): Unit =
      xml_output.string(str, permissive = permissive)

    def output_hidden(body: => Unit): Unit =
      if (hidden) { s ++= "<span class=\"hidden\">"; body; s ++= "</span>" }

    def output_symbol(sym: Symbol.Symbol): Unit =
      if (sym != "") {
        control_block_begin.get(sym) match {
          case Some(op) if control_blocks =>
            output_hidden(output_string(sym))
            xml_output.elem(Markup(op.name, Nil))
          case _ =>
            control_block_end.get(sym) match {
              case Some(op) if control_blocks =>
                xml_output.end_elem(op.name)
                output_hidden(output_string(sym))
              case _ =>
                if (hidden && Symbol.is_control_encoded(sym)) {
                  output_hidden(output_string(Symbol.control_prefix))
                  s ++= "<span class=\"control\">"
                  output_string(Symbol.control_name(sym).get)
                  s ++= "</span>"
                  output_hidden(output_string(Symbol.control_suffix))
                }
                else output_string(sym)
            }
        }
      }

    var ctrl = ""
    for (sym <- Symbol.iterator(text)) {
      if (is_control(sym)) { output_symbol(ctrl); ctrl = sym }
      else {
        control.get(ctrl) match {
          case Some(op) if Symbol.is_controllable(sym) =>
            output_hidden(output_symbol(ctrl))
            xml_output.elem(Markup(op.name, Nil))
            output_symbol(sym)
            xml_output.end_elem(op.name)
          case _ =>
            output_symbol(ctrl)
            output_symbol(sym)
        }
        ctrl = ""
      }
    }
    output_symbol(ctrl)
  }

  def output(text: String): String = {
    val control_blocks = check_control_blocks(List(XML.Text(text)))
    Library.make_string(output(_, text,
      control_blocks = control_blocks, hidden = false, permissive = true))
  }


  /* output XML as HTML */

  private val structural_elements =
    Set("head", "body", "meta", "div", "pre", "p", "title", "h1", "h2", "h3", "h4", "h5", "h6",
      "ul", "ol", "dl", "li", "dt", "dd")

  def output(s: StringBuilder, xml: XML.Body, hidden: Boolean, structural: Boolean): Unit = {
    val xml_output = new XML.Output(s)

    def output_body(body: XML.Body): Unit = {
      val control_blocks = check_control_blocks(body)
      body foreach {
        case XML.Elem(markup, Nil) =>
          xml_output.elem(markup, end = true)
        case XML.Elem(Markup(Markup.RAW_HTML, _), body) =>
          XML.traverse_text(body)(()) { case (_, raw) => s.append(raw) }
        case XML.Elem(markup, ts) =>
          if (structural && structural_elements(markup.name)) s += '\n'
          xml_output.elem(markup)
          output_body(ts)
          xml_output.end_elem(markup.name)
          if (structural && structural_elements(markup.name)) s += '\n'
        case XML.Text(txt) =>
          output(s, txt, control_blocks = control_blocks, hidden = hidden, permissive = true)
      }
    }
    output_body(xml)
  }

  def output(body: XML.Body, hidden: Boolean, structural: Boolean): String =
    Library.make_string(output(_, body, hidden, structural), capacity = XML.text_length(body) * 2)

  def output(tree: XML.Tree, hidden: Boolean, structural: Boolean): String =
    output(List(tree), hidden, structural)


  /* input */

  def input_raw(text: String): XML.Elem = raw(HTML.text(input(text)))
  def input(text: String): String = Jsoup_Entities.unescape(text)
  def raw(body: XML.Body): XML.Elem = XML.elem(Markup.RAW_HTML, body)

  def parse_document(html: String): Jsoup_Document = Jsoup.parse(html)
  def get_document(url: String): Jsoup_Document = Jsoup.connect(url).get()


  /* messages */

  // background
  val writeln_message: Attribute = class_("writeln_message")
  val warning_message: Attribute = class_("warning_message")
  val error_message: Attribute = class_("error_message")

  // underline
  val writeln: Attribute = class_("writeln")
  val warning: Attribute = class_("warning")
  val error: Attribute = class_("error")


  /* tooltips */

  def tooltip(item: XML.Body, tip: XML.Body): XML.Elem =
    span(item ::: List(div("tooltip", tip)))

  def tooltip_errors(item: XML.Body, msgs: List[XML.Body]): XML.Elem =
    HTML.error(tooltip(item, msgs.map(msg => error_message(pre(msg)))))


  /* GUI elements */

  object GUI {
    private def optional_value(text: String): XML.Attributes =
      proper_string(text).map(a => "value" -> a).toList

    private def optional_name(name: String): XML.Attributes =
      proper_string(name).map(a => "name" -> a).toList

    private def optional_title(tooltip: String): XML.Attributes =
      proper_string(tooltip).map(a => "title" -> a).toList

    private def optional_submit(submit: Boolean): XML.Attributes =
      if (submit) List("onChange" -> "this.form.submit()") else Nil

    private def optional_checked(selected: Boolean): XML.Attributes =
      if (selected) List("checked" -> "") else Nil

    private def optional_action(action: String): XML.Attributes =
      proper_string(action).map(a => "action" -> a).toList

    private def optional_onclick(script: String): XML.Attributes =
      proper_string(script).map(a => "onclick" -> a).toList

    private def optional_onchange(script: String): XML.Attributes =
      proper_string(script).map(a => "onchange" -> a).toList

    def button(body: XML.Body, name: String = "", tooltip: String = "", submit: Boolean = false,
        script: String = ""): XML.Elem =
      XML.Elem(
        Markup("button",
          List("type" -> (if (submit) "submit" else "button"), "value" -> "true") :::
          optional_name(name) ::: optional_title(tooltip) ::: optional_onclick(script)), body)

    def checkbox(body: XML.Body, name: String = "", tooltip: String = "", submit: Boolean = false,
        selected: Boolean = false, script: String = ""): XML.Elem =
      XML.elem("label",
        XML.elem(
          Markup("input",
            List("type" -> "checkbox", "value" -> "true") ::: optional_name(name) :::
              optional_title(tooltip) ::: optional_submit(submit) :::
              optional_checked(selected) ::: optional_onchange(script))) :: body)

    def text_field(columns: Int = 0, text: String = "", name: String = "", tooltip: String = "",
        submit: Boolean = false, script: String = ""): XML.Elem =
      XML.elem(Markup("input",
        List("type" -> "text") :::
          (if (columns > 0) List("size" -> columns.toString) else Nil) :::
          optional_value(text) ::: optional_name(name) ::: optional_title(tooltip) :::
          optional_submit(submit) ::: optional_onchange(script)))

    def parameter(text: String = "", name: String = ""): XML.Elem =
      XML.elem(
        Markup("input", List("type" -> "hidden") ::: optional_value(text) ::: optional_name(name)))

    def form(body: XML.Body, name: String = "", action: String = "", http_post: Boolean = false)
        : XML.Elem =
      XML.Elem(
        Markup("form", optional_name(name) ::: optional_action(action) :::
          (if (http_post) List("method" -> "post") else Nil)), body)
  }


  /* GUI layout */

  object Wrap_Panel {
    enum Alignment { case left, right, center }

    def apply(
      contents: List[XML.Elem],
      name: String = "",
      action: String = "",
      alignment: Alignment = Alignment.right
    ): XML.Elem = {
      val body = Library.separate(XML.Text(" "), contents)
      GUI.form(List(div(body) + ("style" -> ("text-align: " + alignment))),
        name = name, action = action)
    }
  }


  /* document */

  val header: String =
    XML.header +
    """<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">"""

  val footer: String = """</html>"""

  val head_meta: XML.Elem =
    XML.Elem(Markup("meta",
      List("http-equiv" -> "Content-Type", "content" -> "text/html; charset=utf-8")), Nil)

  def output_document(
    head: XML.Body,
    body: XML.Body,
    css: String = "isabelle.css",
    hidden: Boolean = true,
    structural: Boolean = true
  ): String = {
    cat_lines(
      List(
        header,
        output(
          XML.elem("head", head_meta :: (if (css == "") Nil else List(style_file(css))) ::: head),
          hidden = hidden, structural = structural),
        output(XML.elem("body", body),
          hidden = hidden, structural = structural),
        footer))
  }


  /* fonts */

  val fonts_path: Path = Path.explode("fonts")

  def init_fonts(dir: Path): Unit = {
    val fonts_dir = Isabelle_System.make_directory(dir + HTML.fonts_path)
    for (entry <- Isabelle_Fonts.fonts(hidden = true))
      Isabelle_System.copy_file(entry.path, fonts_dir)
  }

  def fonts_dir(prefix: String)(ttf_name: String): String = prefix + "/" + ttf_name

  def fonts_url(): String => String =
    (for (entry <- Isabelle_Fonts.fonts(hidden = true))
     yield (entry.path.file_name -> Url.print_file(entry.path.file))).toMap

  def fonts_css(make_url: String => String = fonts_url()): String = {
    def font_face(entry: Isabelle_Fonts.Entry): String =
      cat_lines(
        List(
          "@font-face {",
          "  font-family: '" + entry.family + "';",
          "  src: url('" + make_url(entry.path.file_name) + "') format('truetype');") :::
        (if (entry.is_bold) List("  font-weight: bold;") else Nil) :::
        (if (entry.is_italic) List("  font-style: italic;") else Nil) :::
        List("}"))

    ("/* Isabelle fonts */" :: Isabelle_Fonts.fonts(hidden = true).map(font_face))
      .mkString("", "\n\n", "\n")
  }

  def fonts_css_dir(prefix: String = ""): String =
    fonts_css(fonts_dir(Url.append_path(prefix, fonts_path.implode)))


  /* document directory context (fonts + css) */

  def isabelle_css: Path = Path.explode("~~/etc/isabelle.css")

  def write_document(base_dir: Path, name: String, head: XML.Body, body: XML.Body,
    root: Option[Path] = None,
    css: String = isabelle_css.file_name,
    hidden: Boolean = true,
    structural: Boolean = true
  ): Unit = {
    Isabelle_System.make_directory(base_dir)
    val fonts_prefix = relative_href(root getOrElse base_dir, base = Some(base_dir))
    val fonts = fonts_css_dir(fonts_prefix)
    File.write(base_dir + isabelle_css.base, fonts + "\n\n" + File.read(isabelle_css))
    File.write(base_dir + Path.basic(name),
      output_document(head, body, css = css, hidden = hidden, structural = structural))
  }
}
