/*  Title:      Tools/VSCode/extension/pretty_text_view.scala
    Author:     Fabian Huch

Webview for pretty-printed text with markup.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._
import isabelle.vscode._


object Pretty_Text_View {
  private val vscode = Webview_Api.acquire
  private val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)

  private val node_context =
    new Browser_Info.Node_Context {
      override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
        for {
          json <-
            props match {
              case Position.Item_Def_File(file, line, offset) =>
                Some(LSP.Goto_Source_File(file, line, offset.start))
              case Position.Item_Def_Id(id, offset) =>
                Some(LSP.Goto_Command(id, offset.start))
              case _ => None
            }
        } yield {
          val script = Webview_Api.Post.function(JSON.Format(json))
          HTML.entity_ref(HTML.GUI.onclick(script)(HTML.link("#", body)))
        }

      override def make_file_ref(file: String, body: XML.Body): Option[XML.Elem] = {
        val script = Webview_Api.Post.function(JSON.Format(LSP.Goto_File(file)))
        Some(HTML.GUI.onclick(script)(HTML.link("#", body)))
      }
    }

  private var on_update: XML.Body => Unit = { _ => }
  def on_update(f: XML.Body => Unit): Unit = { on_update = f }


  /* gui state */

  private var current_output: XML.Body = Nil
  private var current_margin: Int = get_window_margin()
  private var resize_timeout: Option[Int] = None
  private var window_loaded = false


  /* update */

  def on_resize(): Unit =
    if (window_loaded) {
      resize_timeout.foreach(dom.window.clearTimeout)
      resize_timeout = Some(dom.window.setTimeout(() => handle_resize(), 500.0))
    }

  def on_load(): Unit = {
    handle_resize()
    window_loaded = true
    update()
  }

  def get_symbol_width(): Double = {
    val test_string = "mix"
    val test_span = dom.document.createElement("span")
    test_span.textContent = test_string
    dom.document.body.appendChild(test_span)
    val symbol_width = test_span.getBoundingClientRect().width / test_string.length
    dom.document.body.removeChild(test_span)
    symbol_width
  }

  def get_window_margin(): Int = {
    val width = dom.window.innerWidth / get_symbol_width()
    Math.max(width.toInt - 16, 1)
  }

  private def update(): Unit = {
    if (window_loaded) {
      val formatted =
        Pretty.formatted(Pretty.separate(current_output), margin = current_margin,
          metric = Symbol.Metric)
      on_update(List(HTML.source(node_context.make_html(elements, formatted))))
    }
  }

  def handle_update(output: XML.Body): Unit = {
    if (current_output != output) {
      current_output = output
      update()
    }
  }

  def handle_resize(): Unit = {
    val margin = get_window_margin()

    if (margin != current_margin) {
      current_margin = margin
      update()
    }
  }
}
