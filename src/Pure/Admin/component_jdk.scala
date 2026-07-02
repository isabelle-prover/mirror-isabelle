/*  Title:      Pure/Admin/component_jdk.scala
    Author:     Makarius

Build Isabelle jdk component using downloads from Azul.
*/

package isabelle


import java.nio.file.Files
import java.nio.file.attribute.PosixFilePermission

import java.util.zip.{ZipFile, ZipEntry}


object Component_JDK {
  /* Java app launcher */

  private object Launcher {
    sealed case class Item(name: String, output: String, executable: Boolean = false) {
      def zip_entry: ZipEntry = new ZipEntry(name)
    }

    sealed case class Info(
      cfg_dir: String = "",
      splash: String = "",
      items: List[Item] = Nil,
      links: List[(String, String)] = Nil)

    val info_linux: Info =
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

    val info_macos: Info = Info()  // FIXME

    val info_windows: Info =
      Info(
        cfg_dir = "app",
        splash = "lib/logo/isabelle.gif",
        items =
          List(
            Item(
              "classes/jdk/jpackage/internal/resources/jpackageapplauncherw.exe",
              "{N}.exe",
              executable = true)))

    val exe_manifest =
    """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<assembly xmlns="urn:schemas-microsoft-com:asm.v1" manifestVersion="1.0" xmlns:asmv3="urn:schemas-microsoft-com:asm.v3" >
 <asmv3:application>
   <asmv3:windowsSettings xmlns="http://schemas.microsoft.com/SMI/2005/WindowsSettings">
    <dpiAware>true</dpiAware>
   </asmv3:windowsSettings>
 </asmv3:application>
</assembly>
"""
  }

  def setup_launcher(
    platform: Platform.Family,
    isabelle_home: Path,
    jdk_home: Path,
    classpath: List[String] = Nil,
    java_options: List[String] = Nil,
    main_class: String = "isabelle.jedit.JEdit_Main"
  ): Unit = {
    val platform_name = Platform.Family.native(platform)
    val (platform_home, launcher) =
      platform match {
        case Platform.Family.linux | Platform.Family.linux_arm =>
          (Path.current, Launcher.info_linux)
        case Platform.Family.macos | Platform.Family.macos_arm =>
          (Path.explode("Contents/Home"), Launcher.info_macos)
        case Platform.Family.windows =>
          (Path.current, Launcher.info_windows)
      }

    val java_home = isabelle_home + jdk_home + Path.basic(platform_name) + platform_home

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
      File.write(isabelle_home + Path.basic(app_name + "exe.manifest"), Launcher.exe_manifest)
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


  /* platform prerequisites */

  val linux_packages: List[String] =
    List("autoconf", "build-essential", "curl", "file", "g++", "gcc", "libasound2-dev",
      "libcups2-dev", "libfontconfig1-dev", "libx11-dev", "libxext-dev", "libxrandr-dev",
      "libxrender-dev", "libxt-dev", "libxtst-dev", "make", "openjdk-21-jdk", "patch", "zip")

  val cygwin_packages: List[String] =
    List("autoconf", "make", "patch", "zip")


  /* defaults */

  val default_jdk_version = "25.0.3"
  val default_jdk_variant = "+9"
  val default_zulu_version = "25.34.17-ca"
  val default_zulu_url = "https://cdn.azul.com/zulu/bin"
  val default_source_url =
    "https://github.com/openjdk/jdk{M}u-dev/archive/refs/tags/jdk-{V}{W}.tar.gz"


  /* platform information */

  sealed case class Download_Platform(name: String, url_template: String) {
    override def toString: String = name
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "zulu{Z}-jdk{V}-macosx_aarch64.tar.gz"),
      Download_Platform("arm64-linux", "zulu{Z}-jdk{V}-linux_aarch64.tar.gz"),
      Download_Platform("x86_64-darwin", "zulu{Z}-jdk{V}-macosx_x64.tar.gz"),
      Download_Platform("x86_64-linux", "zulu{Z}-jdk{V}-linux_x64.tar.gz"),
      Download_Platform("x86_64-windows", "zulu{Z}-jdk{V}-win_x64.zip"))


  /* build from source */

  def major_version(version: String): String = {
    val Major = """^(\d+)\..*$""".r
    version match {
      case Major(m) => m
      case _ => error("Cannot determine major version from " + quote(version))
    }
  }

  val patch = """diff -Nru -- jdk/src/jdk.accessibility/windows/classes/com/sun/java/accessibility/internal/AccessBridge.java jdk-patched/src/jdk.accessibility/windows/classes/com/sun/java/accessibility/internal/AccessBridge.java
--- jdk/src/jdk.accessibility/windows/classes/com/sun/java/accessibility/internal/AccessBridge.java	2026-04-17 21:08:13.000000000 +0200
+++ jdk-patched/src/jdk.accessibility/windows/classes/com/sun/java/accessibility/internal/AccessBridge.java	2026-06-04 15:10:21.215067676 +0200
@@ -72,6 +72,7 @@
 import javax.accessibility.AccessibleEditableText;
 import javax.accessibility.AccessibleExtendedComponent;
 import javax.accessibility.AccessibleExtendedTable;
+import javax.accessibility.AccessibleExtendedText;
 import javax.accessibility.AccessibleHyperlink;
 import javax.accessibility.AccessibleHypertext;
 import javax.accessibility.AccessibleIcon;
@@ -84,6 +85,7 @@
 import javax.accessibility.AccessibleStateSet;
 import javax.accessibility.AccessibleTable;
 import javax.accessibility.AccessibleText;
+import javax.accessibility.AccessibleTextSequence;
 import javax.accessibility.AccessibleValue;
 
 import javax.swing.Icon;
@@ -2127,7 +2129,13 @@
             @Override
             public Integer call() throws Exception {
                 AccessibleText at = ac.getAccessibleText();
-                if (at != null) {
+                if (at instanceof AccessibleExtendedText) {
+                  AccessibleTextSequence s =
+                    ((AccessibleExtendedText) ac.getAccessibleText())
+                      .getTextSequenceAt(AccessibleExtendedText.LINE, index);
+                  return s != null ? s.startIndex : -1;
+                }
+                else if (at != null) {
                     int lineStart;
                     int offset;
                     Rectangle charRect;
@@ -2189,7 +2197,13 @@
             @Override
             public Integer call() throws Exception {
                 AccessibleText at = ac.getAccessibleText();
-                if (at != null) {
+                if (at instanceof AccessibleExtendedText) {
+                  AccessibleTextSequence s =
+                    ((AccessibleExtendedText) ac.getAccessibleText())
+                      .getTextSequenceAt(AccessibleExtendedText.LINE, index);
+                  return s != null ? s.endIndex : -1;
+                }
+                else if (at != null) {
                     int lineEnd;
                     int offset;
                     Rectangle charRect;
"""

  def make_jdk(
    target_dir: Path = Path.current,
    source_url: String = default_source_url,
    jdk_version: String = default_jdk_version,
    jdk_variant: String = default_jdk_variant,
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Unit = {
    /* platform */

    val ssh_platform = ssh.isabelle_platform
    require(ssh_platform.is_linux || ssh_platform.is_windows, "Bad platform " + ssh_platform)

    val platform_dir = target_dir + Path.basic(ssh_platform.ISABELLE_PLATFORM(windows = true))
    Isabelle_System.make_directory(target_dir)

    progress.echo("Output directory " + platform_dir.absolute)
    Isabelle_System.new_directory(platform_dir)

    ssh.with_tmp_dir { ssh_dir =>
      val jdk_path = Path.basic("jdk")
      val jdk_patched_path = Path.basic("jdk-patched")


      /* prepare sources */

      ssh.require_patch()

      ssh.download_file(
        source_url.replacing(
          "{M}" -> major_version(jdk_version), "{V}" -> jdk_version, "{W}" -> jdk_variant),
        ssh_dir + Path.explode("jdk.tar.gz"),
        progress = progress)

      progress.echo("Extracting ...")
      for (path <- List(jdk_path, jdk_patched_path)) {
        ssh.bash(
          "mkdir -p " + ssh.bash_path(path) +
          " && tar -xzf jdk.tar.gz --strip-components=1 -C " + ssh.bash_path(path),
          cwd = ssh_dir).check
      }

      ssh.apply_patch(ssh_dir + jdk_patched_path, patch, progress = progress)

      File.write(platform_dir.patch, ssh.make_patch(ssh_dir, jdk_path, jdk_patched_path))


      /* build */

      progress.echo("Building jdk ...")
      progress.bash(
        Library.make_lines(
          "set -e",
          "mkdir tmp",
          """export TMPDIR="$PWD/tmp"""",
          """bash configure --with-version-pre=isabelle --with-version-opt="" --disable-warnings-as-errors --with-native-debug-symbols=none --with-stdc++lib=static""",
          "make images"),
        cwd = ssh_dir + jdk_patched_path, ssh = ssh, echo = progress.verbose).check

      val build_dir = ssh_dir + jdk_patched_path + Path.explode("build")
      val result_dir =
        ssh.read_dir(build_dir).filterNot(_.startsWith(".")) match {
          case List(name) => build_dir + Path.basic(name) + Path.explode("images/jdk")
          case bad =>
            error("Cannot determine images directory" + if_proper(bad, " from " + commas_quote(bad)))
        }

      progress.echo("Getting jdk ...")
      ssh.read_directory(result_dir, platform_dir, direct = true)

      if (ssh_platform.is_windows) {
        for (path <- File.find_files(platform_dir)) {
          val exe = File.is_exe(path) || File.is_dll(path)
          File.set_executable(path, reset = !exe)
        }
      }
    }
  }


  /* build jdk */

  def build_jdk(
    target_dir: Path = Path.current,
    zulu_url: String = default_zulu_url,
    jdk_version: String = default_jdk_version,
    jdk_variant: String = default_jdk_variant,
    zulu_version: String = default_zulu_version,
    progress: Progress = new Progress,
  ): Unit = {
    if (Platform.is_windows) error("Cannot build on Windows")


    /* component */

    val component = "jdk-" + jdk_version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download */

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download", component_dir.path.file) { dir =>
        val url =
          zulu_url + "/" +
          platform.url_template.replacing(
            "{V}" -> jdk_version, "{W}" -> jdk_variant, "{Z}" -> zulu_version)
        val name = Library.take_suffix(_ != '/', url.toList)._2.mkString
        val file = dir + Path.basic(name)
        Isabelle_System.download_file(url, file, progress = progress)

        val platform_dir = component_dir.path + Path.basic(platform.name)
        Isabelle_System.extract(file, platform_dir, strip = true)
      }
    }


    /* permissions */

    for (file <- File.find_files(component_dir.path, include_dirs = true)) {
      val path = file.java_path
      val perms = Files.getPosixFilePermissions(path).nn
      perms.add(PosixFilePermission.OWNER_READ)
      perms.add(PosixFilePermission.GROUP_READ)
      perms.add(PosixFilePermission.OTHERS_READ)
      perms.add(PosixFilePermission.OWNER_WRITE)
      if (File.is_dll(file) || File.is_exe(file) || file.is_dir) {
        perms.add(PosixFilePermission.OWNER_EXECUTE)
        perms.add(PosixFilePermission.GROUP_EXECUTE)
        perms.add(PosixFilePermission.OTHERS_EXECUTE)
      }
      Files.setPosixFilePermissions(path, perms)
    }


    /* settings */

    component_dir.write_settings("""
case "$ISABELLE_PLATFORM_FAMILY" in
  linux*)
    ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  windows*)
    ISABELLE_JAVA_PLATFORM="$ISABELLE_WINDOWS_PLATFORM64"
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM"
    ;;
  macos*)
    if [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$COMPONENT/$ISABELLE_APPLE_PLATFORM64" ]
    then
      ISABELLE_JAVA_PLATFORM="$ISABELLE_APPLE_PLATFORM64"
    else
      ISABELLE_JAVA_PLATFORM="$ISABELLE_PLATFORM64"
    fi
    ISABELLE_JDK_HOME="$COMPONENT/$ISABELLE_JAVA_PLATFORM/Contents/Home"
    ;;
esac
""")

    File.write(component_dir.platform_props,
      "windows = x86_64-windows x86_64-windows.patch\n")


    /* README */

    File.write(component_dir.README,
      """This is OpenJDK {V}{W} based on downloads by Azul, see also
https://www.azul.com/downloads/?package=jdk

The main license is GPL2, but some modules are covered by other (more liberal)
licenses, see legal/* for details.

Linux, Windows, macOS all work uniformly, depending on platform-specific
subdirectories.
""".replacing("{V}" -> jdk_version, "{W}" -> jdk_variant))
  }


  /* Isabelle tool wrappers */

  val isabelle_tool1 =
    Isabelle_Tool("make_jdk", "build jdk from sources",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var build_host = SSH.LOCAL
        var source_url = default_source_url
        var jdk_version = default_jdk_version
        var jdk_variant = default_jdk_variant
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle make_jdk [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -H HOST      remote build host (default: local)
    -S URL       source archive URL template
                 (default: """" + default_source_url + """")
    -V NAME      JDK version (default: """" + default_jdk_version + """")
    -W NAME      JDK variant (default: """" + default_jdk_variant + """")
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose

  Build jdk from sources.

  Linux prerequisites:
    - Ubuntu 20.04 LTS
    - apt packages:
      apt-get update && apt-get upgrade -y && apt autoremove -y
      apt install -y """ + linux_packages.mkString(" ") + """

  Windows prerequisites:
    - install Cygwin packages: """ + cygwin_packages.mkString(" ") + """
    - install Visual Studio 2022
        + see https://visualstudio.microsoft.com/downloads
        + Desktop development with C++
    - install current JDK (for bootstrap)
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "H:" -> (arg => build_host = arg),
          "S:" -> (arg => source_url = arg),
          "V:" -> (arg => jdk_version = arg),
          "W:" -> (arg => jdk_variant = arg),
          "o:" -> (arg => options = options + arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        using(SSH.open_system(options, build_host)) { ssh =>
          make_jdk(target_dir = target_dir, source_url = source_url, jdk_version = jdk_version,
            jdk_variant = jdk_variant, ssh = ssh, progress = progress)
        }
      })

  val isabelle_tool2 =
    Isabelle_Tool("component_jdk", "build Isabelle jdk component using downloads from Azul",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var zulu_url = default_zulu_url
        var jdk_version = default_jdk_version
        var jdk_variant = default_jdk_variant
        var zulu_version = default_zulu_version

        val getopts = Getopts("""
Usage: isabelle component_jdk [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       Zulu base URL (default: """" + default_zulu_url + """")
    -V NAME      JDK version (default: """" + default_jdk_version + """")
    -W NAME      JDK variant (default: """" + default_jdk_variant + """")
    -Z NAME      Zulu version (default: """" + default_zulu_version + """")

  Build Isabelle jdk component using downloads from Azul.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => zulu_url = arg),
          "V:" -> (arg => jdk_version = arg),
          "W:" -> (arg => jdk_variant = arg),
          "Z:" -> (arg => zulu_version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_jdk(target_dir = target_dir, zulu_url = zulu_url, jdk_version = jdk_version,
          jdk_variant = jdk_variant, zulu_version = zulu_version, progress = progress)
      })
}
