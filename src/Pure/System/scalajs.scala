/*  Title:      Pure/System/scalajs.scala
    Author:     Fabian Huch

Support for compiling Scala to JavaScript.
 */
package isabelle

import scala.language.unsafeNulls

import java.io.{File => JFile}

import scala.jdk.CollectionConverters._
import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.scalajs.js
import scala.scalajs.js.JSConverters._

import org.scalajs.logging
import org.scalajs.linker.{PathIRContainer, StandardImpl, PathOutputDirectory}
import org.scalajs.linker.interface.{Report, StandardConfig, ModuleInitializer}

import dotty.tools.dotc.Driver
import dotty.tools.dotc.interfaces.{Diagnostic, SimpleReporter}


object Scalajs {
  /* compilation */

  final case class Module(name: String, class_name: String, main: String = "main") {
    def js_path: Path = Path.basic(name).ext("js")
  }

  object Message {
    enum Phase { case compilation, linking }
    enum Kind { case error, warning, info, debug, other }

    def compilation(diagnostic: Diagnostic): Message = {
      val kind =
        diagnostic.level() match {
         case Diagnostic.ERROR => Kind.error
         case Diagnostic.WARNING => Kind.warning
         case Diagnostic.INFO => Kind.info
         case _ => Kind.other
        }
      Message(Phase.compilation, kind, diagnostic.message().nn)
    }

    def linking(level: logging.Level, text: String): Message = {
      val kind =
        level match {
          case logging.Level.Error => Kind.error
          case logging.Level.Warn => Kind.warning
          case logging.Level.Info => Kind.info
          case logging.Level.Debug => Kind.debug
        }
      Message(Phase.linking, kind, text)
    }
  }

  sealed case class Message(phase: Message.Phase, kind: Message.Kind, text: String) {
    def is_error: Boolean = kind == Message.Kind.error
    override def toString: String = text

    def output(progress: Progress): Unit = kind match {
      case Message.Kind.error => progress.echo_error_message(text)
      case Message.Kind.warning => progress.echo_warning(text)
      case Message.Kind.info => progress.echo(text)
      case Message.Kind.debug => progress.echo(text, verbose = true)
      case Message.Kind.other =>
    }
  }

  sealed case class Result(
    messages: List[Message] = Nil,
    report: Option[Report] = None,
    outputs: List[Path] = Nil
  ) {
    val errors: List[String] = messages.flatMap(msg => if (msg.is_error) Some(msg.text) else None)
    def ok: Boolean = errors.isEmpty
    override def toString: String =
      if (ok) "Result(outputs=" + outputs.map(_.absolute).mkString(", ") + ")" else "Result(error)"
  }

  def compile(
    sources: List[JFile],
    modules: List[Module],
    output_dir: Path,
    more_settings: List[String] = Nil,
    classpath: Classpath = Classpath()
  ): Result = {
    if (!sources.exists(s => File.is_scala(s.file_name))) Result()
    else Isabelle_System.with_tmp_dir("scalajs") { dir =>
      val ir_dir = Isabelle_System.make_directory(dir + Path.basic("ir")).java_path.nn

      val settings =
        Word.explode(Isabelle_System.getenv_strict("ISABELLE_SCALAC_OPTIONS")) ::: more_settings :::
          List("-d", ir_dir.toString, "-bootclasspath", classpath.platform_path, "-scalajs")

      val msgs = new mutable.ListBuffer[Message]()
      val reporter =
        new SimpleReporter {
          def report(diagnostic: Diagnostic): Unit = { msgs += Message.compilation(diagnostic.nn) }
        }

      val args = settings ::: "--" :: sources.map(_.toString)
      val result = new Driver().process(args.toArray, reporter, null)

      if (result.hasErrors) Result(msgs.toList)
      else {
        val linker = StandardImpl.linker(StandardConfig())
        val cache = StandardImpl.irFileCache().newCache

        val logger =
          new logging.Logger {
            def trace(t: => Throwable): Unit = {
              msgs += Message(Message.Phase.linking, Message.Kind.error, Exn.trace(t))
            }
            def log(level: logging.Level, message: => String): Unit = {
              msgs += Message.linking(level, message)
            }
          }

        val js_dir = Isabelle_System.make_directory(dir + Path.basic("js"))
        val output = PathOutputDirectory(js_dir.java_path.nn)

        val initializers =
          for (m <- modules)
          yield ModuleInitializer.mainMethod(m.class_name, m.main).withModuleID(m.name)

        val futures = 
          for {
            containers <- PathIRContainer.fromClasspath(ir_dir :: classpath.jars.map(_.toPath.nn))
            ir_files <- cache.cached(containers._1)
            result <- linker.link(ir_files, initializers, output, logger)
          } yield result

        val report =
         Exn.capture { Await.result(futures, scala.concurrent.duration.Duration.Inf) } match {
           case Exn.Res(res) => Some(res)
           case Exn.Exn(t) =>
             msgs += Message(Message.Phase.linking, Message.Kind.error, Exn.trace(t))
             None
         }

        val results =
          for (name <- File.read_dir(js_dir) if name.endsWith(".js"))
          yield {
            Isabelle_System.copy_file(js_dir + Path.basic(name), output_dir)
            output_dir + Path.basic(name)
          }
        Result(msgs.toList, report, results)
      }
    }
  }


  /* json conversions */

  object JSON {
    def apply(json: isabelle.JSON.T): js.Any =
      json match {
        case x: String => x
        case x: Double => x
        case x: Long => x.toDouble
        case x: Int => x
        case x: Boolean => x
        case null => null
        case xs: List[isabelle.JSON.T] => xs.map(apply).toJSArray
        case isabelle.JSON.Object(obj) => Object(obj)
        case x => error("Bad JSON value: " + x.toString)
      }

    def unapply(json: Any): Option[isabelle.JSON.T] =
      json match {
        case x: String => Some(x)
        case x: Double => Some(x)
        case x: Int => Some(x)
        case x: Boolean => Some(x)
        case null => Some(null)
        case xs: js.Array[_] =>
          val arr = xs.map(unapply)
          if (arr.forall(_.isDefined)) Some(arr.map(_.get)) else None
        case Object(m) => Some(m)
        case _ => None
      }

    object Object {
      def apply(json: isabelle.JSON.Object.T): js.Object =
        js.Dynamic.literal(json.toList.map((k, v) => k -> JSON(v)): _*)

      def unapply(json: js.Object): Option[isabelle.JSON.Object.T] = {
        val entries = js.Object.entries(json).map(t => t._1 -> JSON.unapply(t._2))
        if (entries.forall(_._2.isDefined)) Some(entries.toMap) else None
      }
    }
  }
}
