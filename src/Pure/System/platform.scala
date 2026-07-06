/*  Title:      Pure/System/platform.scala
    Author:     Makarius

Java platform information, based on system properties.
*/

package isabelle


object Platform {
  /* platform family */

  val is_windows: Boolean = isabelle.setup.Environment.is_windows()
  val is_linux: Boolean = isabelle.setup.Environment.is_linux()
  val is_macos: Boolean = isabelle.setup.Environment.is_macos()
  val is_unix: Boolean = is_linux || is_macos

  enum Family { case linux_arm, linux, macos, macos_arm, windows }

  def family: Family = {
    val arch = Isabelle_System.get_property("os.arch")
    val is_arm = arch.containsSlice("arm64") || arch.containsSlice("aarch64")

    if (is_linux && is_arm) Family.linux_arm
    else if (is_linux) Family.linux
    else if (is_macos && is_arm) Family.macos_arm
    else if (is_macos) Family.macos
    else if (is_windows) Family.windows
    else error("Failed to determine current platform family")
  }

  def jvm_platform: String = Family.native(family)

  object Family {
    val list: List[Family] =
      List(Family.linux, Family.linux_arm, Family.windows, Family.macos, Family.macos_arm)

    def unapply(name: String): Option[Family] =
      try { Some(Family.valueOf(name)) }
      catch { case _: IllegalArgumentException => None }

    def parse(name: String): Family =
      unapply(name) getOrElse error("Bad platform family: " + quote(name))

    val standard: Family => String =
      {
        case Family.linux_arm => "arm64-linux"
        case Family.linux => "x86_64-linux"
        case Family.macos | Family.macos_arm => "x86_64-darwin"
        case Family.windows => "x86_64-cygwin"
      }

    val native: Family => String =
      {
        case Family.macos_arm => "arm64-darwin"
        case Family.windows => "x86_64-windows"
        case platform => standard(platform)
      }

    def from_platform(platform: String): Family =
      list.find(family => platform == standard(family) || platform == native(family))
        .getOrElse(error("Bad platform " + quote(platform)))
  }


  /* platform info */

  object Info {
    val ALL = "all"

    def check(infos: List[Info], spec: String): String = {
      val specs = Library.distinct(ALL :: infos.map(_.family_name) ::: infos.map(_.platform))
      if (specs.contains(spec)) spec
      else {
        error("Bad platform specification " + quote(spec) +
          "\n  expected " + commas_quote(specs))
      }
    }
  }

  trait Info {
    def platform: String
    override def toString: String = platform
    def path: Path = Path.explode(platform)

    val family: Family = Family.from_platform(platform)
    def family_name: String = family.toString

    def is_linux_arm: Boolean = family == Family.linux_arm
    def is_linux: Boolean = family == Family.linux
    def is_macos_arm: Boolean = family == Family.macos_arm
    def is_macos: Boolean = family == Family.macos
    def is_windows: Boolean = family == Family.windows

    def test(spec: String): Boolean =
      Info.ALL == spec || platform == spec || family_name == spec
  }


  /* JVM version */

  private val Version = """1\.(\d+)\.0_(\d+)""".r
  lazy val jvm_version: String =
    Isabelle_System.get_property("java.version") match {
      case Version(a, b) => a + "u" + b
      case a => a
    }


  /* JVM name */

  val jvm_name: String = Isabelle_System.get_property("java.vm.name")
}
