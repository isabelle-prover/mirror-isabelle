/*  Title:      Pure/General/symbol_files.scala
    Author:     Fabian Huch

Isabelle text symbols from symbols files.
 */

package isabelle.platform

import isabelle._


object Symbol_Files {
  def symbols: Symbol.Symbols =
    Symbol.Symbols.make(cat_lines(Symbol.Symbols.files().map(File.read)))
}

val symbol_provider = Symbol_Files
