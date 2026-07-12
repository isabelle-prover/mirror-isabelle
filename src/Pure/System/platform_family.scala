/*  Title:      Pure/System/platform_family.scala
    Author:     Makarius

Abstract platform family, with correlation to Isabelle distribution bundles.
*/

package isabelle

sealed abstract class Platform_Family {
  family =>

  def standard: String =
    family match {
      case Platform_Family.linux_arm => "arm64-linux"
      case Platform_Family.linux => "x86_64-linux"
      case Platform_Family.macos | Platform_Family.macos_arm => "x86_64-darwin"
      case Platform_Family.windows => "x86_64-cygwin"
    }

  def native: String =
    family match {
      case Platform_Family.macos_arm => "arm64-darwin"
      case Platform_Family.windows => "x86_64-windows"
      case _ => standard
    }
}

object Platform_Family {
  case object linux_arm extends Platform_Family { override def toString: String = "linux_arm" }
  case object linux extends Platform_Family { override def toString: String = "linux" }
  case object macos extends Platform_Family { override def toString: String = "macos" }
  case object macos_arm extends Platform_Family { override def toString: String = "macos_arm" }
  case object windows extends Platform_Family { override def toString: String = "windows" }

  val list: List[Platform_Family] =
    List(
      linux,
      linux_arm,
      windows,
      macos,
      macos_arm)

  def unapply(name: String): Option[Platform_Family] =
    list.find(family => family.toString == name)

  def parse(name: String): Platform_Family =
    unapply(name) getOrElse error("Bad platform family: " + quote(name))

  def from_platform(platform: String): Platform_Family =
    list.find(family => platform == family.standard || platform == family.native)
      .getOrElse(error("Bad platform " + quote(platform)))
}
