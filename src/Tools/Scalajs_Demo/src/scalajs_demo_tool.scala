/*  Title:      Tools/Scalajs_Demo/src/scalajs_demo_tool.scala
    Author:     Fabian Huch

Isabelle Scalajs demo tool.
*/

package isabelle.scalajs_demo

import scala.jdk.CollectionConverters._

import isabelle._


object Scalajs_Demo_Tool {
  def js_home: Path = Path.explode("$ISABELLE_SCALAJS_DEMO_HOME/js")

  def scalajs_demo(progress: Progress = new Progress): Unit =
    Isabelle_System.with_tmp_dir("scalajs_demo") { dir =>
      val context = setup.Build.component_context(js_home.java_path).nn
      val sources =
        for (name <- context.sources.nn.asScala.toList if File.is_scala(name))
        yield (js_home + Path.explode(name)).file

      val module = Scalajs.Module("scalajs_demo", "isabelle.scalajs_demo.Scalajs_Demo")
      val scalajs_result = Scalajs.compile(sources, List(module), dir)

      scalajs_result.messages.foreach(_.output(progress))
      if (!scalajs_result.ok) error("Failed to compile scalajs sources")

      val js = File.read(Library.the_single(scalajs_result.outputs))
      val nodejs_result = Nodejs.execute(js)

      nodejs_result.out_lines.foreach(progress.echo(_))
      nodejs_result.err_lines.foreach(progress.echo_error_message(_))
      if (!nodejs_result.ok) error("Nodejs process failed")
    }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("scalajs_demo", "Isabelle/Scala on JS demo", Scala_Project.here,
      { args =>
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle scalajs_demo [OPTIONS]

  Options are:
    -v           verbose mode: print more explanations

  Compile Isabelle/Scala demo sources to JS and run them on Nodejs.
""",
          "v" -> (_ => verbose = true))

        if (getopts(args).nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        scalajs_demo(progress = progress)
      })
}

class Tools extends Isabelle_Scala_Tools(Scalajs_Demo_Tool.isabelle_tool)
