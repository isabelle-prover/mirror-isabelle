/*  Title:      Pure/Admin/component_e.scala
    Author:     Makarius

Build Isabelle E prover component from official downloads.
*/

package isabelle


object Component_E {
  /* build E prover */

  val default_version = "3.2"
  val default_download_url = "https://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD"

  def build_e(
    version: String = default_version,
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val component_name = "e-" + version
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

      val platform_name = Isabelle_Platform.local.ISABELLE_PLATFORM(apple = true)
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download source */

      val archive_url = download_url + "/V_" + version + "/E.tgz"
      val archive_path = tmp_dir + Path.explode("E.tgz")
      Isabelle_System.download_file(archive_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = archive_url)

      Isabelle_System.extract(archive_path, component_dir.src, strip = true)


      /* build */

      progress.echo("Building E prover for " + platform_name + " ...")

      // adhoc patch wrt. https://github.com/eprover/eprover/commit/d40e1db7d786
      // obsolete after https://github.com/eprover/eprover/commit/5ae1a2c66da6
      if (Platform.is_windows) {
        File.change_lines(source_dir + Path.explode("PROVER/eprover.c"), strict = true) {
          _.map(line => if (line.containsSlice("setpgid(0, 0)")) "" else line)
        }
      }

      val build_script = "./configure --enable-ho && make"
      Isabelle_System.bash(build_script, cwd = source_dir,
        progress_stdout = progress.echo(_, verbose = true),
        progress_stderr = progress.echo(_, verbose = true)).check


      /* install */

      Isabelle_System.copy_file(source_dir + Path.basic("COPYING"), component_dir.LICENSE)

      val install_files = List("epclextract", "eprover-ho")
      for (name <- install_files ::: install_files.map(_ + ".exe")) {
        val path = source_dir + Path.basic("PROVER") + Path.basic(name)
        if (path.is_file) Isabelle_System.copy_file(path, platform_dir)
      }
      Isabelle_System.bash("mv eprover-ho eprover", cwd = platform_dir).check


      /* settings */

      component_dir.write_settings("""
E_HOME="$COMPONENT/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}"
E_VERSION=""" + quote(version) + """
""")


      /* README */

      File.write(component_dir.README,
        "This is E prover " + version + " from\n" + archive_url + """

* On Windows/Cygwin, the sources have been patched to remove setpgid in
  PROVER/eprover.c

* The distribution has been built like this:

    cd src && """ + build_script + """

* Some executables from PROVERS/ have been moved to the platform-specific
Isabelle component directory: x86_64-linux etc.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_e", "build prover component from source distribution", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var version = default_version
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_e [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -V VERSION   version (default: """ + default_version + """)
    -v           verbose

  Build prover component from the specified source distribution.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_e(version = version, download_url = download_url,
          progress = progress, target_dir = target_dir)
      })
}
