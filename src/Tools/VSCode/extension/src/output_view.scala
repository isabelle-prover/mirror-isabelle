/*  Title:      Tools/VSCode/extension/output_view.scala
    Author:     Fabian Huch

Output view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Output_View {
  private val vscode = Webview_Api.acquire


  /* main */

  def main(): Unit = {
    Pretty_Text_View.on_update { output =>
      dom.document.body.innerHTML = XML.string_of_body(output)
    }

    dom.window.onresize = { _ => Pretty_Text_View.on_resize() }
    dom.window.onload = { _ => Pretty_Text_View.on_load() }

    Webview_Api.on_message { e =>
      Pretty_Text_View.handle_update(YXML.parse_body(YXML.Source(e.data.toString)))
    }

    vscode.post(JSON.Object("command" -> "ready"))
  }
}
