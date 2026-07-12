/*  Title:      Pure/System/platform_family.scala
    Author:     Makarius

Abstract platform family, with correlation to Isabelle distribution bundles.
*/

package isabelle

enum Platform_Family { case linux_arm, linux, macos, macos_arm, windows }

object Platform_Family {
  val list: List[Platform_Family] =
    List(
      Platform_Family.linux,
      Platform_Family.linux_arm,
      Platform_Family.windows,
      Platform_Family.macos,
      Platform_Family.macos_arm)

  def unapply(name: String): Option[Platform_Family] =
    try { Some(Platform_Family.valueOf(name)) }
    catch { case _: IllegalArgumentException => None }

  def parse(name: String): Platform_Family =
    unapply(name) getOrElse error("Bad platform family: " + quote(name))

  val standard: Platform_Family => String =
    {
      case Platform_Family.linux_arm => "arm64-linux"
      case Platform_Family.linux => "x86_64-linux"
      case Platform_Family.macos | Platform_Family.macos_arm => "x86_64-darwin"
      case Platform_Family.windows => "x86_64-cygwin"
    }

  val native: Platform_Family => String =
    {
      case Platform_Family.macos_arm => "arm64-darwin"
      case Platform_Family.windows => "x86_64-windows"
      case platform => standard(platform)
    }

  def from_platform(platform: String): Platform_Family =
    list.find(family => platform == standard(family) || platform == native(family))
      .getOrElse(error("Bad platform " + quote(platform)))
}
