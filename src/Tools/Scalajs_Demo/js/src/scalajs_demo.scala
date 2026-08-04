/*  Title:      Tools/Scalajs_Demo/js/src/scalajs_demo.scala
    Author:     Fabian Huch

Isabelle Scalajs demo (JS side).
*/

package isabelle.scalajs_demo

import isabelle._


object Scalajs_Demo {
  def main(): Unit = {
    Output.writeln("Welcome from " + Platform.jvm_name, stdout = true)
  }
}
