/*  Title:      Pure/PIDE/document_id.scala
    Author:     Makarius

Unique identifiers for document structure.

NB: ML ticks forwards > 0, JVM ticks backwards < 0.
*/

package isabelle


object Document_ID {
  type Generic = Long
  type Version = Generic
  type Command = Generic
  type Exec = Generic

  val none: Generic = 0
  val make: Counter = Counter.make()

  def apply(id: Generic): String = Value.Long.apply(id)
  def unapply(s: String): Option[Generic] = Value.Long.unapply(s)

  def encode(id: Generic): XML.Body = XML.Encode.long(id)
}
