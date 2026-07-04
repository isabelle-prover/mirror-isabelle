/*  Title:      Pure/Admin/build_app.scala
    Author:     Makarius

Build official macOS app from Isabelle distribution archive.
*/

package isabelle

import java.io.IOException
import java.nio.file.Files


object Build_App {
  /** resources **/

  val ADMIN_MACOS_ENTITLEMENTS: Path =
    Path.explode("~~/Admin/macOS/app/entitlements.plist")


  /** build app **/

  def build_app(dist_archive: String,
    target_dir: Path = Path.current,
    codesign_keychain: String = "",
    codesign_user: String = "",
    progress: Progress = new Progress
  ): Unit = {
    require(codesign_user.nonEmpty, "Missing codesign_user")
    require(Platform.is_unix, "macOS platform required")


    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* target directory */

      Isabelle_System.make_directory(target_dir)

      def execute(script: String): Process_Result = {
        progress.echo_if(progress.verbose, script)
        progress.bash(script, cwd = target_dir, echo = progress.verbose).check
      }

      def jpackage(args: String): Process_Result =
        execute("isabelle_java jpackage " + args)

      val jpackage_version = Library.trim_line(jpackage("--version").check.out)


      /* Isabelle distribution directory */

      val dist_dir = {
        val dist_archive_path =
          Url.get_base_name(dist_archive) match {
            case Some(name) if Url.is_wellformed(dist_archive) =>
              val download_dir = Isabelle_System.make_directory(tmp_dir + Path.basic("download"))
              val download_path = download_dir + Path.basic(name)
              Isabelle_System.download_file(dist_archive, download_path, progress = progress)
              download_path
            case _ => Path.explode(dist_archive)
          }
        val dist_parent = Isabelle_System.new_directory(tmp_dir + Path.explode("dist"))
        Isabelle_System.extract(dist_archive_path, dist_parent)
        File.get_dir(dist_parent, title = dist_archive)
      }

      val app_name = File.read(dist_dir + Build_Release.ISABELLE_IDENTIFIER)


      /* java app package */

      val app_target = target_dir.absolute + Path.basic(app_name)
      val app_root = app_target.app
      val app_contents = app_root + Path.explode("Contents")
      val app_resources = app_contents + Path.explode("Resources")
      val app_identifier = "isabelle." + app_name

      progress.echo("Preparing Isabelle directory structure ...")

      Isabelle_System.new_directory(app_root)
      Isabelle_System.copy_dir(dist_dir, app_root, direct = true)

      for (name <- File.read_dir(app_root) if name != "Contents") {
        (app_root + Path.basic(name)).file.delete
      }

      File.change_lines(app_resources + Path.explode("etc/settings")) { lines =>
        lines.map(line =>
          line.replacing(
            "$USER_HOME/.isabelle" ->
            "$USER_HOME/Library/Application Support/Isabelle"))
      }

      val bad_files =
        File.find_files(app_root, pred = { file =>
          try { Files.getPosixFilePermissions(file.java_path); false }
          catch { case _: IOException => true }
        })
      for (path <- bad_files) {
        progress.echo_warning("Suppressing bad " + path)
        path.file.delete
      }


      /* macOS signing and packaging */

      progress.echo("Building signed dmg ...")

      File.write(app_contents + Path.explode("app/.jpackage.xml"),
"""<?xml version="1.0" ?>
<jpackage-state version="{VERSION}" platform="macOS">
  <app-version>1.0</app-version>
  <main-launcher>{NAME}</main-launcher>
  <main-class>isabelle.jedit.JEdit_Main</main-class>
  <app-store>false</app-store>
  <signed>false</signed>
</jpackage-state>
""".replacing("{NAME}" -> XML.text(app_name), "{VERSION}" -> XML.text(jpackage_version)))

      jpackage(
        " --app-image " + File.bash_path(app_root) +
        " --type dmg" +
        " --type app-image" +
        " --mac-sign" +
        " --mac-package-signing-prefix " + Bash.string(app_identifier) +
        " --mac-entitlements " + File.bash_path(ADMIN_MACOS_ENTITLEMENTS) +
        " --mac-signing-key-user-name " + Bash.string(codesign_user) +
        if_proper(codesign_keychain,
          " --mac-signing-keychain " + Bash.string(codesign_keychain)) +
        if_proper(progress.verbose, " --verbose"))

      Isabelle_System.move_file(
        app_target.dir + Path.basic(app_target.file_name + "-1.0").ext("dmg"),
        app_target.ext("dmg"))
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_app", "build standalone desktop app from Isabelle distribution archive",
      Scala_Project.here,
      { args =>
          var target_dir = Path.current
          var codesign_keychain = ""
          var codesign_user = ""
          var verbose = false

          val getopts = Getopts("""
Usage: isabelle build_app [OPTIONS] ARCHIVE

  Options are:
    -D DIR       target directory (default ".")
    -K NAME      macOS codesign keychain name (e.g. "login.keychain")
    -S NAME      macOS codesign user name (e.g. "John Doe (M2NGOH5LAE)")
    -v           verbose

  Build standalone desktop app from Isabelle distribution archive (file or URL).
""",
            "D:" -> (arg => target_dir = Path.explode(arg)),
            "K:" -> (arg => codesign_keychain = arg),
            "S:" -> (arg => codesign_user = arg),
            "v" -> (_ => verbose = true))

          val more_args = getopts(args)
          val dist_archive =
            more_args match {
              case List(a) => a
              case _ => getopts.usage()
            }

          val progress = new Console_Progress(verbose = verbose)

          build_app(dist_archive, target_dir = target_dir, codesign_keychain = codesign_keychain,
            codesign_user = codesign_user, progress = progress)
        })
}
