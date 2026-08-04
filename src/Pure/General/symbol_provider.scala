/*  Title:      Pure/General/symbol_provider.scala
    Author:     Fabian Huch

File-based provider for Isabelle text symbols.
 */
package isabelle


object Symbol_Provider {
  def symbols: Symbol.Symbols =
    Symbol.Symbols.make(cat_lines(Symbol.Symbols.files().map(File.read)))
}