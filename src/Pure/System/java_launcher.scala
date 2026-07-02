/*  Title:      Pure/System/java_launcher.scala
    Author:     Makarius

Java app launcher, based on resources of "jpackage".
*/

package isabelle

import java.util.zip.{ZipFile, ZipEntry}


object Java_Launcher {
  private sealed case class Item(name: String, output: String, executable: Boolean = false) {
    def zip_entry: ZipEntry = new ZipEntry(name)
  }

  private sealed case class Info(
    home: String = "",
    cfg_dir: String = "",
    splash: String = "",
    items: List[Item] = Nil,
    links: List[(String, String)] = Nil)

  private val info_linux: Info =
    Info(
      cfg_dir = "lib/app",
      splash = "lib/logo/isabelle.gif",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncher",
            "bin/{N}",
            executable = true),
          Item(
            "classes/jdk/jpackage/internal/resources/libjpackageapplauncheraux.so",
            "lib/libapplauncher.so")),
      links = List("bin/{N}" -> "{N}", "lib/app/{N}.cfg" -> "{N}.cfg"))

  private val info_macos: Info = Info(home = "Contents/Home")  // FIXME

  private val info_windows: Info =
    Info(
      cfg_dir = "app",
      splash = "lib/logo/isabelle.gif",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncherw.exe",
            "{N}.exe",
            executable = true)))

  private val exe_manifest =
  """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<assembly xmlns="urn:schemas-microsoft-com:asm.v1" manifestVersion="1.0" xmlns:asmv3="urn:schemas-microsoft-com:asm.v3" >
 <asmv3:application>
   <asmv3:windowsSettings xmlns="http://schemas.microsoft.com/SMI/2005/WindowsSettings">
    <dpiAware>true</dpiAware>
   </asmv3:windowsSettings>
 </asmv3:application>
</assembly>
"""

  def setup(
    platform: Platform.Family,
    isabelle_home: Path,
    jdk_home: Path,
    classpath: List[String] = Nil,
    java_options: List[String] = Nil,
    main_class: String = "isabelle.jedit.JEdit_Main"
  ): Unit = {
    val launcher =
      platform match {
        case Platform.Family.linux | Platform.Family.linux_arm => info_linux
        case Platform.Family.macos | Platform.Family.macos_arm => info_macos
        case Platform.Family.windows => info_windows
      }
    val platform_root = Path.basic(Platform.Family.native(platform))
    val platform_home = Path.explode(launcher.home)

    val java_home = isabelle_home + jdk_home + platform_root + platform_home

    val app_name = isabelle_home.file_name
    def app_path(s: String): Path = Path.explode(s.replacing("{N}" -> app_name))

    val zip_path = java_home + Path.explode("jmods/jdk.jpackage.jmod")
    using(new ZipFile(zip_path.file)) { zip_file =>
      for (item <- launcher.items) {
        val path = isabelle_home + app_path(item.output)
        val bytes = using(zip_file.getInputStream(item.zip_entry))(Bytes.read_stream(_))
        Bytes.write(path, bytes)
        if (item.executable) File.set_executable(path)
      }
    }

    if (platform == Platform.Family.windows) {
      File.write(isabelle_home + Path.basic(app_name + "exe.manifest"), exe_manifest)
    }

    val cfg_lines =
      List("[Application]") :::
      (if (launcher.splash.isEmpty) Nil else List("app.splash=$ROOTDIR/" + launcher.splash)) :::
      List("app.mainclass=" + main_class) :::
      List("app.runtime=$ROOTDIR/" + File.perhaps_relative_path(isabelle_home, java_home).implode) :::
      classpath.map("app.classpath=$ROOTDIR/" + _) :::
      List("", "[JavaOptions]") :::
      ("-Disabelle.root=$ROOTDIR" :: java_options).map("java-options=" + _)

    val cfg_path = isabelle_home + Path.explode(launcher.cfg_dir) + Path.basic(app_name + ".cfg")
    Isabelle_System.make_directory(cfg_path.dir)
    File.write(cfg_path, Library.terminate_lines(cfg_lines))

    for ((a, b) <- launcher.links) {
      Isabelle_System.symlink(app_path(a), isabelle_home + app_path(b), force = true)
    }
  }
}
