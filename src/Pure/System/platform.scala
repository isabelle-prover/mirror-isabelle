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

  def family: Platform_Family = {
    val arch = Isabelle_System.get_property("os.arch")
    val is_arm = arch.containsSlice("arm64") || arch.containsSlice("aarch64")

    if (is_linux && is_arm) Platform_Family.linux_arm
    else if (is_linux) Platform_Family.linux
    else if (is_macos && is_arm) Platform_Family.macos_arm
    else if (is_macos) Platform_Family.macos
    else if (is_windows) Platform_Family.windows
    else error("Failed to determine current platform family")
  }

  def jvm_platform: String = family.native

  def check_jvm_platform(): Unit = {
    val family0 = Platform_Family.parse(Isabelle_Platform.local.ISABELLE_PLATFORM_FAMILY)
    if (family != family0) {
      def print(fam: Platform_Family): String = quote(fam.toString) + " (" + fam.native + ")"
      error("The Java platform is running as " + print(family) +
        ", but the system is " + print(family0) + ":" +
        "\nPlease use the correct Isabelle application for " + quote(family0.toString))
    }
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

    val family: Platform_Family = Platform_Family.from_platform(platform)
    def family_name: String = family.toString

    def is_linux_arm: Boolean = family == Platform_Family.linux_arm
    def is_linux: Boolean = family == Platform_Family.linux
    def is_macos_arm: Boolean = family == Platform_Family.macos_arm
    def is_macos: Boolean = family == Platform_Family.macos
    def is_windows: Boolean = family == Platform_Family.windows

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
