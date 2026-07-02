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
    resources: String = "",
    cfg_dir: String = "",
    splash: String = "",
    items: List[Item] = Nil,
    links: List[(String, String)] = Nil
  ) {
    def home_path: Path = Path.explode(home)
    def resources_path: Path = Path.explode(resources)
  }

  private val info_linux: Info =
    Info(
      cfg_dir = "lib/app",
      splash = "lib/logo/isabelle.gif",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncher",
            "bin/{NAME}",
            executable = true),
          Item(
            "classes/jdk/jpackage/internal/resources/libjpackageapplauncheraux.so",
            "lib/libapplauncher.so")),
      links = List("bin/{NAME}" -> "{NAME}", "lib/app/{NAME}.cfg" -> "{NAME}.cfg"))

  private val info_macos: Info =
    Info(
      home = "Contents/Home",
      resources = "Contents/Resources",
      cfg_dir = "Contents/app",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncher",
            "Contents/MacOS/{NAME}",
            executable = true)),
      links = List("Contents/app/{NAME}.cfg" -> "{NAME}.cfg"))

  private val info_windows: Info =
    Info(
      cfg_dir = "app",
      splash = "lib/logo/isabelle.gif",
      items =
        List(
          Item(
            "classes/jdk/jpackage/internal/resources/jpackageapplauncherw.exe",
            "{NAME}.exe",
            executable = true)))

  private val info_plist =
    """<?xml version="1.0" ?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
<key>CFBundleDevelopmentRegion</key>
<string>English</string>
<key>CFBundleExecutable</key>
<string>{NAME}</string>
<key>CFBundleIconFile</key>
<string>lib/logo/isabelle.icns</string>
<key>CFBundleIdentifier</key>
<string>isabelle.{NAME}</string>
<key>CFBundleDisplayName</key>
<string>{NAME}</string>
<key>CFBundleInfoDictionaryVersion</key>
<string>6.0</string>
<key>CFBundleName</key>
<string>{NAME}</string>
<key>CFBundlePackageType</key>
<string>APPL</string>
<key>CFBundleShortVersionString</key>
<string>{VERSION}</string>
<key>CFBundleSignature</key>
<string>????</string>
<key>CFBundleVersion</key>
<string>{VERSION}</string>
<key>NSHumanReadableCopyright</key>
<string>Isabelle contributors: various open-source licenses</string>
<key>LSMinimumSystemVersion</key>
<string>10.11</string>
<key>LSApplicationCategoryType</key>
<string>public.app-category.developer-tools</string>
<key>NSHighResolutionCapable</key>
<string>true</string>
<key>NSSupportsAutomaticGraphicsSwitching</key>
<string>true</string>
<key>CFBundleDocumentTypes</key>
<array>
<dict>
<key>CFBundleTypeExtensions</key>
<array>
<string>thy</string>
</array>
<key>CFBundleTypeIconFile</key>
<string>lib/logo/theory.icns</string>
<key>CFBundleTypeName</key>
<string>Isabelle theory file</string>
<key>CFBundleTypeRole</key>
<string>Editor</string>
<key>LSTypeIsPackage</key>
<false/>
</dict>
</array>
</dict>
</plist>
"""

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
    app_root: Path,
    jdk_home: Path,
    app_version: String = "",
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

    val app_name = app_root.drop_ext.file_name
    val isabelle_home = app_root + launcher.resources_path
    val java_home = isabelle_home + jdk_home + platform_root + launcher.home_path

    def app_path(s: String, relative: Boolean = false): Path =
      (if (relative) Path.current else app_root) + Path.explode(s.replacing("{NAME}" -> app_name))

    val zip_path = java_home + Path.explode("jmods/jdk.jpackage.jmod")
    using(new ZipFile(zip_path.file)) { zip_file =>
      for (item <- launcher.items) {
        val path = app_path(item.output)
        val bytes = using(zip_file.getInputStream(item.zip_entry))(Bytes.read_stream(_))
        Isabelle_System.make_directory(path.dir)
        Bytes.write(path, bytes)
        if (item.executable) File.set_executable(path)
      }
    }

    platform match {
      case Platform.Family.macos | Platform.Family.macos_arm =>
        val app_contents = app_root + Path.explode("Contents")
        File.write(app_contents + Path.explode("Info.plist"),
          info_plist.replacing(
            "{NAME}" -> app_name,
            "{VERSION}" -> proper_string(app_version).getOrElse("1.0")))
        File.write(app_contents + Path.explode("PkgInfo"), "APPL????")
      case Platform.Family.windows =>
        File.write(app_root + Path.basic(app_name + ".exe.manifest"), exe_manifest)
      case _ =>
    }

    val cfg_lines =
      List("[Application]") :::
      (if (launcher.splash.isEmpty) Nil else List("app.splash=$ROOTDIR/" + launcher.splash)) :::
      List("app.mainclass=" + main_class) :::
      List("app.runtime=$ROOTDIR/" + File.perhaps_relative_path(app_root, java_home).implode) :::
      classpath.map("app.classpath=$ROOTDIR/" + _) :::
      List("", "[JavaOptions]") :::
      ("-Disabelle.root=$ROOTDIR" :: java_options).map("java-options=" + _)

    val cfg_path = app_root + Path.explode(launcher.cfg_dir) + Path.basic(app_name + ".cfg")
    Isabelle_System.make_directory(cfg_path.dir)
    File.write(cfg_path, Library.terminate_lines(cfg_lines))

    for ((a, b) <- launcher.links) {
      Isabelle_System.symlink(app_path(a, relative = true), app_path(b), force = true)
    }
  }
}
