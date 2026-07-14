/*  Title:      Tools/VSCode/extension/pretty_text_view.scala
    Author:     Fabian Huch

Webview for pretty-printed text with markup.
 */
package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Pretty_Text_View {
  private val vscode = Webview_Api.acquire

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

  def update_window_width(): Unit = {
    vscode.post(JSON.Object("command" -> "resize", "margin" -> get_window_margin()))
  }

  private var timeout: Option[Int] = None

  def init(): Unit = {
    for (link <- dom.document.querySelectorAll("""a[href^="file:"]""")) {
      link.addEventListener("click", { _ =>
        vscode.post(JSON.Object("command" -> "open", "link" -> link.getAttribute("href")))
      })
    }

    dom.window.onresize = { _ =>
      timeout.foreach(dom.window.clearTimeout)
      timeout = Some(dom.window.setTimeout(() => update_window_width(), 500.0))
    }
    dom.window.onload = { _ => update_window_width() }
  }
}
