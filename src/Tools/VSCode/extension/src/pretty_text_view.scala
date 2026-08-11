/*  Title:      Tools/VSCode/extension/pretty_text_view.scala
    Author:     Fabian Huch

Webview for pretty-printed text with markup.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Pretty_Text_View {
  private val vscode = Webview_Api.acquire

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
    handle_links()
    window_loaded = true
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

  def handle_update(output: XML.Body): Unit = {
    if (current_output != output) {
      current_output = output
      on_update(List(HTML.source(current_output)))
      handle_links()
    }
  }

  def handle_resize(): Unit = {
    val margin = get_window_margin()

    if (margin != current_margin) {
      current_margin = margin

      if (current_output.nonEmpty) {
        vscode.post(JSON.Object("command" -> "resize", "margin" -> margin))
      }
    }
  }

  def handle_links(): Unit =
    for (link <- dom.document.querySelectorAll("""a[href^="file:"]""")) {
      link.addEventListener("click", { _ =>
        vscode.post(JSON.Object("command" -> "open", "link" -> link.getAttribute("href")))
      })
    }
}
