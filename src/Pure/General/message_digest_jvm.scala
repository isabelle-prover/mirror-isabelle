/*  Title:      Pure/General/message_digest_jvm.scala
    Author:     Fabian Huch

Message digest builder based on java.security.
*/

package isabelle.platform

import java.security.MessageDigest

import isabelle._


object Message_Digest_JVM {
  class Builder private[Message_Digest_JVM](rep: MessageDigest) extends Message_Digest.Builder {
    def update(input: Array[Byte], offset: Int, length: Int) = rep.update(input, offset, length)
    def digest(): Array[Byte] = rep.digest().nn
  }

  def builder(kind: String): Builder = new Builder(MessageDigest.getInstance(kind).nn)
}

val message_digest_provider = Message_Digest_JVM
