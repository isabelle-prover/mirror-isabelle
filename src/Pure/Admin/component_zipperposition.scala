/*  Title:      Pure/Admin/component_zipperposition.scala
    Author:     Makarius

Build Isabelle Zipperposition component from OPAM repository.
*/

package isabelle


object Component_Zipperposition {
  val default_version = "2.1"


  /* build Zipperposition */

  def build_zipperposition(
    version: String = default_version,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { build_dir =>
      if (Platform.is_linux) Isabelle_System.require_command("patchelf")


      /* component */

      val component_name = "zipperposition-" + version
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


      /* platform */

      val platform_name = Isabelle_Platform.self.ISABELLE_PLATFORM()
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* build */

      progress.echo("OCaml/OPAM setup ...")
      progress.bash("isabelle ocaml_setup", echo = progress.verbose).check

      progress.echo("Building Zipperposition for " + platform_name + " ...")
      progress.bash(cwd = build_dir, echo = progress.verbose,
        script = "isabelle_opam install -y --destdir=" + File.bash_path(build_dir) +
          " zipperposition=" + Bash.string(version)).check


      /* install */

      Isabelle_System.copy_file(build_dir + Path.explode("doc/zipperposition/LICENSE"),
        component_dir.path)

      val prg_path = Path.basic("zipperposition")
      val exe_path = prg_path.platform_exe
      Isabelle_System.copy_file(build_dir + Path.basic("bin") + prg_path, platform_dir + exe_path)

      if (!Platform.is_windows) {
        Executable.libraries_closure(platform_dir + exe_path, filter = Set("libgmp"))
      }


      /* settings */

      component_dir.write_settings("""
ZIPPERPOSITION_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
""")


      /* README */

      File.write(component_dir.README,
"""This is Zipperposition """ + version + """ from the OCaml/OPAM repository.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_zipperposition", "build prover component from OPAM repository",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var version = default_version
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_zipperposition [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -V VERSION   version (default: """" + default_version + """")
    -v           verbose

  Build prover component from OPAM repository.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "V:" -> (arg => version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_zipperposition(version = version, progress = progress, target_dir = target_dir)
      })
}
