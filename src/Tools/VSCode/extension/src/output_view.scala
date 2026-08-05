/*  Title:      Tools/VSCode/extension/output_view.scala
    Author:     Fabian Huch

Output view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Output_View {
  /* main */

  def main(): Unit = {
    dom.window.onresize = { _ => Pretty_Text_View.on_resize() }
    dom.window.onload = { _ => Pretty_Text_View.on_load() }
  }
}
