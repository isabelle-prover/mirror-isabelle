/*  Title:      Tools/VSCode/extension/output_view.scala
    Author:     Fabian Huch

Output view within Isabelle/VSCode extension.
 */
package isabelle.vscode.extension

import isabelle._


object Output_View {
  /* main */

  def main(): Unit = {
    Pretty_Text_View.init()
  }
}
