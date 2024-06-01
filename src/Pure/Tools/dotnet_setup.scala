/*  Title:      Pure/Tools/dotnet_setup.scala
    Author:     Makarius

Dynamic setup of Dotnet component.
*/

package isabelle


object Dotnet_Setup {
  /* platforms */

  sealed case class Platform_Info(
    platform: String,
    os: String = "",
    arch: String = "x64",
    ext: String = "sh",
    exec: String = "bash",
    check: () => Unit = () => ()
  ) extends Platform.Info

  val all_platforms: List[Platform_Info] =
    List(
      Platform_Info("arm64-linux", os = "linux", arch = "arm64"),
      Platform_Info("x86_64-linux", os = "linux"),
      Platform_Info("arm64-darwin", os = "osx", arch = "arm64"),
      Platform_Info("x86_64-darwin", os = "osx"),
      Platform_Info("x86_64-windows",
        ext = "ps1",
        exec = "powershell -ExecutionPolicy ByPass",
        check = () => Isabelle_System.require_command("powershell", "-NoProfile -Command Out-Null")))

  def check_platform(spec: String): String = Platform.Info.check(all_platforms, spec)


  /* dotnet download and setup */

  def default_platform: String =
    Isabelle_Platform.self.ISABELLE_PLATFORM(windows = true, apple = true)
  def default_target_dir: Path = Components.default_components_base
  def default_install_url: String = "https://dot.net/v1/dotnet-install"
  def default_version: String = Isabelle_System.getenv_strict("ISABELLE_DOTNET_VERSION")

  def dotnet_setup(
    platforms: List[String] = List(default_platform),
    target_dir: Path = default_target_dir,
    install_url: String = default_install_url,
    version: String = default_version,
    force: Boolean = false,
    dry_run: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    platforms.foreach(check_platform)


    /* component directory */

    val component_dir =
      Components.Directory(
        target_dir + Path.explode(if (version.isEmpty) "dotnet-latest" else "dotnet-" + version))

    if (!dry_run) {
      progress.echo("Component directory " + component_dir)
      component_dir.create(permissive = true)

      component_dir.write_settings("""
ISABELLE_DOTNET_ROOT="$COMPONENT"

if [ -n "$ISABELLE_WINDOWS_PLATFORM64" -a -d "$ISABELLE_DOTNET_ROOT/$ISABELLE_WINDOWS_PLATFORM64" ]; then
  ISABELLE_DOTNET="$ISABELLE_DOTNET_ROOT/$ISABELLE_WINDOWS_PLATFORM64/dotnet.exe"
elif [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$ISABELLE_DOTNET_ROOT/$ISABELLE_APPLE_PLATFORM64" ]; then
  ISABELLE_DOTNET="$ISABELLE_DOTNET_ROOT/$ISABELLE_APPLE_PLATFORM64/dotnet"
elif [ -d "$ISABELLE_DOTNET_ROOT/$ISABELLE_PLATFORM64" ]; then
  ISABELLE_DOTNET="$ISABELLE_DOTNET_ROOT/$ISABELLE_PLATFORM64/dotnet"
fi

DOTNET_CLI_TELEMETRY_OPTOUT="true"
DOTNET_CLI_HOME="$(platform_path "$ISABELLE_HOME_USER/dotnet")"
""")

      File.write(component_dir.README,
        """This installation of Dotnet has been produced via "isabelle dotnet_setup".


      Makarius
      """ + Date.Format.date(Date.now()) + "\n")

      for (old <- proper_string(Isabelle_System.getenv("ISABELLE_DOTNET_ROOT"))) {
        Components.update_components(false, Path.explode(old))
      }

      Components.update_components(true, component_dir.path)
    }


    /* platform directories */

    for (platform <- all_platforms if platforms.exists(platform.is)) {
      progress.expose_interrupt()

      Isabelle_System.with_tmp_file("install", ext = platform.ext) { install =>
        Isabelle_System.download_file(install_url + "." + platform.ext, install)

        val platform_dir = component_dir.path + platform.path
        if (platform_dir.is_dir && !force) {
          progress.echo_warning("Platform " + platform + " already installed")
        }
        else {
          progress.echo("Platform " + platform + " ...")
          platform.check()
          if (platform_dir.is_dir && force) Isabelle_System.rm_tree(platform_dir)
          val script =
            platform.exec + " " + File.bash_platform_path(install) +
              if_proper(version, " -Version " + Bash.string(version)) +
              " -Architecture " + Bash.string(platform.arch) +
              if_proper(platform.os, " -OS " + Bash.string(platform.os)) +
              " -InstallDir " + File.bash_path(platform.path) +
              (if (dry_run) " -DryRun" else "") +
              " -NoPath"
          progress.bash(script, echo = progress.verbose,
            cwd = if (dry_run) Path.current else component_dir.path).check
          for (exe <- File.find_files(platform_dir.file, pred = _.getName.endsWith(".exe"))) {
            File.set_executable(File.path(exe))
          }
        }
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dotnet_setup", "dynamic setup of Dotnet component (for Fsharp)",
      Scala_Project.here,
      { args =>

        var target_dir = default_target_dir
        var install_url = default_install_url
        var version = default_version
        var force = false
        var dry_run = false
        var platforms = List(default_platform)
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle dotnet_setup [OPTIONS]

  Options are:
    -D DIR       target directory (default: """ + default_target_dir.expand + """)
    -I URL       URL for install script without extension
                 (default: """ + quote(default_install_url) + """)
    -V VERSION   version: empty means "latest"
                 (default: ISABELLE_DOTNET_VERSION=""" + quote(default_version) + """)
    -f           force fresh installation of specified platforms
    -n           dry run: try download without installation
    -p PLATFORMS comma-separated list of platform specifications: "all" or
                 as family or formal name (default: """ + quote(default_platform) + """)
    -v           verbose

  Download the Dotnet / Fsharp platform and configure it as Isabelle component.

  See also:
    https://fsharp.org
    https://learn.microsoft.com/en-us/dotnet/core/tools/dotnet-install-script
    https://learn.microsoft.com/en-us/dotnet/core/tools/telemetry
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "I:" -> (arg => install_url = arg),
          "V:" -> (arg => version = arg),
          "f" -> (_ => force = true),
          "n" -> (_ => dry_run = true),
          "p:" -> (arg => platforms = space_explode(',', arg).map(check_platform)),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        dotnet_setup(platforms = platforms, target_dir = target_dir, install_url = install_url,
          version = version, force = force, dry_run = dry_run, progress = progress)
      })
}

class Dotnet_Setup extends Setup_Tool("dotnet_setup", "ISABELLE_DOTNET_SETUP") {
  override val test_file: Path = Path.explode("lib/Tools/dotnet")
}
