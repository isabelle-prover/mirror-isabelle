/*  Title:      Pure/General/compress.scala
    Author:     Makarius

Support for generic data compression.
*/

package isabelle


import org.tukaani.xz
import com.github.luben.zstd


object Compress {
  /* options */

  object Options {
    def apply(): Options = Options_Zstd()
  }
  sealed abstract class Options
  case class Options_XZ(level: Int = 3) extends Options {
    def make: xz.LZMA2Options = {
      val opts = new xz.LZMA2Options
      opts.setPreset(level)
      opts
    }
  }
  case class Options_Zstd(level: Int = 3) extends Options


  /* cache */

  class Cache private(val for_xz: xz.ArrayCache, zstd_pool: Option[zstd.BufferPool]) {
    def for_zstd: zstd.BufferPool =
      zstd_pool getOrElse {
        Zstd.init()
        zstd.NoPool.INSTANCE.nn
      }
  }

  object Cache {
    def none: Cache = new Cache(xz.ArrayCache.getDummyCache().nn, None)

    def make(): Cache = {
      Zstd.init()
      val pool = Untyped.constructor(classOf[zstd.RecyclingBufferPool]).newInstance().nn
      new Cache(new xz.BasicArrayCache, Some(pool))
    }
  }


  /* Scala functions in ML */

  object XZ_Compress extends Scala.Fun_Bytes("XZ.compress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.compress(Options_XZ())
  }

  object XZ_Uncompress extends Scala.Fun_Bytes("XZ.uncompress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.uncompress_xz()
  }

  object Zstd_Compress extends Scala.Fun_Bytes("Zstd.compress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.compress(Options_Zstd())
  }

  object Zstd_Uncompress extends Scala.Fun_Bytes("Zstd.uncompress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.uncompress_zstd()
  }
}
