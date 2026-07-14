/*  Title:      Tools/VSCode/extension/pretty_text_view.scala
    Author:     Fabian Huch

Webview for pretty-printed text with markup.
 */
package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Pretty_Text_View {
  private val vscode = Webview_Api.acquire

  private var resize_timeout: Option[Int] = None

  def on_resize(): Unit = {
    resize_timeout.foreach(dom.window.clearTimeout)
    resize_timeout = Some(dom.window.setTimeout(() => handle_resize(), 500.0))
  }

  def on_load(): Unit = handle_resize()

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

  def handle_resize(): Unit = {
    vscode.post(JSON.Object("command" -> "resize", "margin" -> get_window_margin()))
  }


  /* main */

  def init(): Unit = {
    for (link <- dom.document.querySelectorAll("""a[href^="file:"]""")) {
      link.addEventListener("click", { _ =>
        vscode.post(JSON.Object("command" -> "open", "link" -> link.getAttribute("href")))
      })
    }

    dom.window.onresize = { _ => on_resize() }
    dom.window.onload = { _ => on_load() }
  }
}
