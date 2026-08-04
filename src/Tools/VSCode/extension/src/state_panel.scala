/*  Title:      Tools/VSCode/extension/state_panel.scala
    Author:     Fabian Huch

State panel within Isabelle/VSCode extension.
 */
package isabelle.vscode.extension

import scala.language.unsafeNulls

import org.scalajs.dom

import isabelle._


object State_Panel {
  private val vscode = Webview_Api.acquire


  /* main */

  def main(): Unit = {
    Pretty_Text_View.init()

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
  }
}
