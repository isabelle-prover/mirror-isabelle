/*  Title:      Tools/VSCode/extension/output_view.scala
    Author:     Fabian Huch

Output view within Isabelle/VSCode extension.
 */
package isabelle.vscode.extension

import scala.language.unsafeNulls

import scala.scalajs.js
import org.scalajs.dom

import isabelle._


object Output_View {
  def get_symbol_width(): Double = {
    val test_string = "mix"
    val test_span = dom.document.createElement("span")
    test_span.textContent = test_string
    dom.document.body.appendChild(test_span)
    val symbol_width = test_span.getBoundingClientRect().width / test_string.length
    dom.document.body.removeChild(test_span)
    symbol_width
  }

  def get_window_margin(symbol_width: Double): Int = {
    val width = dom.window.innerWidth / symbol_width
    Math.max(width.toInt - 16, 1)
  }

  def main(): Unit = {
    val vscode = Webview_Api.acquire

    for (link <- dom.document.querySelectorAll("""a[href^="file:"]""")) {
      link.addEventListener("click", { _ =>
        vscode.post(JSON.Object("command" -> "open", "link" -> link.getAttribute("href")))
      })
    }

    val auto_update = dom.document.getElementById("auto_update")
    if (auto_update != null) {
      auto_update.addEventListener("change", { e =>
        val target = e.target.asInstanceOf[dom.html.Input]
        vscode.post(JSON.Object("command" -> "auto_update", "enabled" -> target.checked))
      })
    }

    val update_button = dom.document.getElementById("update_button")
    if (update_button != null) {
      update_button.addEventListener("click", { _ =>
        vscode.post(JSON.Object("command" -> "update"))
      })
    }

    val locate_button = dom.document.getElementById("locate_button")
    if (locate_button != null) {
      locate_button.addEventListener("click", { _ =>
        vscode.post(JSON.Object("command" -> "locate"))
      })
    }

    val symbol_width = get_symbol_width()
    def update_window_width(): Unit = {
      vscode.post(JSON.Object("command" -> "resize", "margin" -> get_window_margin(symbol_width)))
    }

    var timeout: Option[Int] = None
    dom.window.onresize = { _ =>
      timeout.foreach(dom.window.clearTimeout)
      timeout = Some(dom.window.setTimeout(() => update_window_width(), 500.0))
    }
    dom.window.onload = { _ => update_window_width() }
  }
}
