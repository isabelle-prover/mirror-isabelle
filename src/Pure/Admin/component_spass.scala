/*  Title:      Pure/Admin/component_spass.scala
    Author:     Makarius

Build Isabelle SPASS component from unofficial download.
*/

package isabelle


object Component_SPASS {
  /* build SPASS */

  val default_download_url = "https://www.cs.vu.nl/~jbe248/spass-3.8ds-src.tar.gz"
  val standard_version = "3.8ds"

  private val source_patch = """diff -Nru src-orig/makefile src/makefile
--- src-orig/makefile	2015-01-06 12:11:07.000000000 +0100
+++ src/makefile	2026-07-14 13:06:41.166559181 +0200
@@ -77,7 +77,7 @@
 # Enables catching of some common signals (segmentation fault ...)
 
 
-WARNINGS = -pedantic -Wall -Wshadow -Wpointer-arith -Wwrite-strings -std=c99 #-Wconversion  
+WARNINGS = -Wno-error=implicit-function-declaration -pedantic -Wall -Wshadow -Wpointer-arith -Wwrite-strings -std=c99 #-Wconversion  
 # Turn off some warnings for scanner files
 SCANNERFLAGS=-Wno-implicit -Wno-uninitialized
 
diff -Nru src-orig/misc.c src/misc.c
--- src-orig/misc.c	2015-01-06 12:11:07.000000000 +0100
+++ src/misc.c	2026-07-14 12:58:56.588589600 +0200
@@ -44,7 +44,9 @@
 
 #include "misc.h"
 #include "strings.h" /* Cannot be moved to misc.h as long as there is no separate type.h, e.g. for pointers */
+#ifndef __CYGWIN__
 #include "execinfo.h" //backtrace and backtrade_symbols, for dump
+#endif
 /**************************************************************/
 /* Functions                                                  */
 /**************************************************************/
@@ -132,6 +134,7 @@
   EFFECT:  Flushes the streams then dumps a core.
 ***************************************************************/
 {
+#ifndef __CYGWIN__
 	void *array[150];
 	size_t size;
 	char **strings;
@@ -151,6 +154,7 @@
   fflush(misc_ERROROUT);
   fflush(stdout);
   fflush(stderr);
+#endif
   abort();
 }
 

"""

  def build_spass(
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      Isabelle_System.require_patch()
      Isabelle_System.require_command("bison")
      Isabelle_System.require_command("flex")


      /* component */

      val archive_name =
        Url.get_base_name(download_url)
          .getOrElse(error("Failed to determine source archive name from " + quote(download_url)))

      val component_name =
        Library.try_unsuffix("-src.tar.gz", archive_name)
          .getOrElse(error("Failed to determine component name from " + quote(archive_name)))

      val Version = """^[^-]+-([^-]+)$""".r
      val version =
        component_name match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(component_name))
        }

      if (version != standard_version) {
        progress.echo_warning("Odd SPASS version " + version + " (expected " + standard_version + ")")
      }

      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

      val platform_name = Isabelle_Platform.local.ISABELLE_PLATFORM()
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      val source_dir = Isabelle_System.new_directory(tmp_dir + Path.explode("src"))

      for (src <- List(source_dir, component_dir.src)) {
        Isabelle_System.extract(archive_path, src, strip = true)
        Isabelle_System.apply_patch(src, source_patch, progress = progress)
      }


      /* build */

      progress.echo("Building SPASS for " + platform_name + " ...")

      Isabelle_System.bash("make", cwd = source_dir,
        progress_stdout = progress.echo(_, verbose = true),
        progress_stderr = progress.echo(_, verbose = true)).check

      Isabelle_System.copy_file(source_dir + Path.explode("SPASS").platform_exe, platform_dir)
      Isabelle_System.copy_file(source_dir + Path.basic("LICENCE"), component_dir.LICENSE)


      /* settings */

      component_dir.write_settings("""
SPASS_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
SPASS_VERSION=""" + quote(version) + """
""")


      /* README */

      File.write(component_dir.README,
"""This distribution of SPASS 3.8ds, described in Blanchette, Popescu, Wand, and
Weidenbach's ITP 2012 paper "More SPASS with Isabelle", has been compiled from
sources available at """ + download_url + """
via "make".

For compatibility with current Isabelle platforms, these sources have been
patched as follows:

""" + source_patch + """Note that regular SPASS sources can be downloaded from
https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench/classic-spass-theorem-prover
--- but official SPASS releases do not work with Isabelle.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_spass", "build prover component from source distribution",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_spass [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build prover component from the specified source distribution.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_spass(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
