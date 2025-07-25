/*  Title:      Pure/System/isabelle_platform.scala
    Author:     Makarius

Isabelle/Scala platform information, based on settings environment.
*/

package isabelle


object Isabelle_Platform {
  val settings: List[String] =
    List(
      "ISABELLE_PLATFORM_FAMILY",
      "ISABELLE_PLATFORM64",
      "ISABELLE_WINDOWS_PLATFORM32",
      "ISABELLE_WINDOWS_PLATFORM64",
      "ISABELLE_APPLE_PLATFORM64")

  def make(env: Isabelle_System.Settings = Isabelle_System.Settings()): Isabelle_Platform =
    new Isabelle_Platform(settings.map(a => (a, Isabelle_System.getenv(a, env = env))))

  lazy val local: Isabelle_Platform = make()

  def remote(ssh: SSH.Session): Isabelle_Platform = {
    val script =
      File.read(Path.explode("~~/lib/scripts/isabelle-platform")) + "\n" +
        settings.map(a => "echo \"" + Bash.string(a) + "=$" + Bash.string(a) + "\"").mkString("\n")
    val result = ssh.execute("bash -c " + Bash.string(script)).check
    new Isabelle_Platform(
      result.out_lines.map(line =>
        Properties.Eq.unapply(line) getOrElse error("Bad output: " + quote(result.out))))
  }


  /* system context for progress/process */

  object Context {
    def apply(
      isabelle_platform: Isabelle_Platform = local,
      mingw: MinGW = MinGW.none,
      progress: Progress = new Progress
    ): Context = {
      val context_platform = isabelle_platform
      val context_mingw = mingw
      val context_progress = progress
      new Context {
        override def isabelle_platform: Isabelle_Platform = context_platform
        override def mingw: MinGW = context_mingw
        override def progress: Progress = context_progress
      }
    }
  }

  trait Context {
    def isabelle_platform: Isabelle_Platform
    def mingw: MinGW
    def progress: Progress

    def standard_path(path: Path): String =
      mingw.standard_path(File.standard_path(path))

    def execute(cwd: Path, script_lines: String*): Process_Result = {
      val script = cat_lines("set -e" :: script_lines.toList)
      val script1 =
        if (isabelle_platform.is_arm && isabelle_platform.is_macos) {
          "arch -arch arm64 bash -c " + Bash.string(script)
        }
        else mingw.bash_script(script)
      progress.bash(script1, cwd = cwd, echo = progress.verbose).check
    }
  }
}

class Isabelle_Platform private(val settings: List[(String, String)]) {
  private def get(name: String): String =
    settings.collectFirst({ case (a, b) if a == name => b }).
      getOrElse(error("Bad platform settings variable: " + quote(name)))

  val ISABELLE_PLATFORM64: String = get("ISABELLE_PLATFORM64")
  val ISABELLE_WINDOWS_PLATFORM64: String = get("ISABELLE_WINDOWS_PLATFORM64")
  val ISABELLE_APPLE_PLATFORM64: String = get("ISABELLE_APPLE_PLATFORM64")

  def ISABELLE_PLATFORM(windows: Boolean = false, apple: Boolean = false): String =
    proper_string(if_proper(windows, ISABELLE_WINDOWS_PLATFORM64)) orElse
    proper_string(if_proper(apple, ISABELLE_APPLE_PLATFORM64)) orElse
    proper_string(ISABELLE_PLATFORM64) getOrElse error("Missing ISABELLE_PLATFORM64")

  def is_arm: Boolean =
    ISABELLE_PLATFORM64.startsWith("arm64-") ||
    ISABELLE_APPLE_PLATFORM64.startsWith("arm64-")

  val ISABELLE_PLATFORM_FAMILY: String = {
    val family0 = get("ISABELLE_PLATFORM_FAMILY")
    if (family0 == "linux" && is_arm) "linux_arm" else family0
  }

  def is_linux: Boolean = ISABELLE_PLATFORM_FAMILY.startsWith("linux")
  def is_macos: Boolean = ISABELLE_PLATFORM_FAMILY.startsWith("macos")
  def is_windows: Boolean = ISABELLE_PLATFORM_FAMILY.startsWith("windows")

  def arch_64: String = if (is_arm) "arm64" else "x86_64"
  def arch_64_32: String = if (is_arm) "arm64_32" else "x86_64_32"

  def os_name: String = if (is_macos) "darwin" else if (is_windows) "windows" else "linux"

  override def toString: String = ISABELLE_PLATFORM_FAMILY
}
