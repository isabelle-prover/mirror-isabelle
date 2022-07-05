/*  Title:      Pure/System/scala.scala
    Author:     Makarius

Support for Scala at runtime.
*/

package isabelle


import java.io.{File => JFile, PrintStream, ByteArrayOutputStream, OutputStream}

import scala.collection.mutable
import scala.annotation.tailrec

import dotty.tools.dotc.CompilationUnit
import dotty.tools.dotc.ast.Trees.PackageDef
import dotty.tools.dotc.ast.untpd
import dotty.tools.dotc.core.Contexts.{Context => CompilerContext}
import dotty.tools.dotc.core.NameOps.moduleClassName
import dotty.tools.dotc.core.{Phases, StdNames}
import dotty.tools.dotc.interfaces
import dotty.tools.dotc.reporting.{Diagnostic, ConsoleReporter}
import dotty.tools.dotc.util.{SourceFile, SourcePosition, NoSourcePosition}
import dotty.tools.repl
import dotty.tools.repl.{ReplCompiler, ReplDriver}


object Scala {
  /** registered functions **/

  abstract class Fun(val name: String, val thread: Boolean = false) {
    override def toString: String = name
    def single: Boolean = false
    def bytes: Boolean = false
    def position: Properties.T = here.position
    def here: Scala_Project.Here
    def invoke(args: List[Bytes]): List[Bytes]
  }

  trait Single_Fun extends Fun { override def single: Boolean = true }
  trait Bytes_Fun extends Fun { override def bytes: Boolean = true }

  abstract class Fun_Strings(name: String, thread: Boolean = false)
  extends Fun(name, thread = thread) {
    override def invoke(args: List[Bytes]): List[Bytes] =
      apply(args.map(_.text)).map(Bytes.apply)
    def apply(args: List[String]): List[String]
  }

  abstract class Fun_String(name: String, thread: Boolean = false)
  extends Fun_Strings(name, thread = thread) with Single_Fun {
    override def apply(args: List[String]): List[String] =
      List(apply(Library.the_single(args)))
    def apply(arg: String): String
  }

  abstract class Fun_Bytes(name: String, thread: Boolean = false)
    extends Fun(name, thread = thread) with Single_Fun with Bytes_Fun {
    override def invoke(args: List[Bytes]): List[Bytes] =
      List(apply(Library.the_single(args)))
    def apply(arg: Bytes): Bytes
  }

  val encode_fun: XML.Encode.T[Fun] = { fun =>
    import XML.Encode._
    pair(string, pair(pair(bool, bool), properties))(
      fun.name, ((fun.single, fun.bytes), fun.position))
  }

  class Functions(val functions: Fun*) extends Isabelle_System.Service

  lazy val functions: List[Fun] =
    Isabelle_System.make_services(classOf[Functions]).flatMap(_.functions)



  /** demo functions **/

  object Echo extends Fun_String("echo") {
    val here = Scala_Project.here
    def apply(arg: String): String = arg
  }

  object Sleep extends Fun_String("sleep") {
    val here = Scala_Project.here
    def apply(seconds: String): String = {
      val t =
        seconds match {
          case Value.Double(s) => Time.seconds(s)
          case _ => error("Malformed argument: " + quote(seconds))
        }
      val t0 = Time.now()
      t.sleep()
      val t1 = Time.now()
      (t1 - t0).toString
    }
  }



  /** compiler **/

  def class_path(): List[String] =
    space_explode(JFile.pathSeparatorChar, System.getProperty("java.class.path", ""))
      .filter(_.nonEmpty)

  object Compiler {
    object Message {
      object Kind extends Enumeration {
        val error, warning, info, other = Value
      }
      private val Header = """^--.* (Error|Warning|Info): .*$""".r
      val header_kind: String => Kind.Value =
        {
          case "Error" => Kind.error
          case "Warning" => Kind.warning
          case "Info" => Kind.info
          case _ => Kind.other
        }

      // see compiler/src/dotty/tools/dotc/reporting/MessageRendering.scala
      def split(str: String): List[Message] = {
        var kind = Kind.other
        val text = new mutable.StringBuilder
        val result = new mutable.ListBuffer[Message]

        def flush(): Unit = {
          if (text.nonEmpty) { result += Message(kind, text.toString) }
          kind = Kind.other
          text.clear()
        }

        for (line <- Library.trim_split_lines(str)) {
          line match {
            case Header(k) => flush(); kind = header_kind(k)
            case _ => if (line.startsWith("-- ")) flush()
          }
          if (text.nonEmpty) { text += '\n' }
          text ++= line
        }
        flush()
        result.toList
      }
    }

    sealed case class Message(kind: Message.Kind.Value, text: String)
    {
      def is_error: Boolean = kind == Message.Kind.error
      override def toString: String = text
    }

    sealed case class Result(
      state: repl.State,
      messages: List[Message],
      unit: Option[CompilationUnit] = None
    ) {
      val errors: List[String] = messages.flatMap(msg => if (msg.is_error) Some(msg.text) else None)
      def ok: Boolean = errors.isEmpty
      def check_state: repl.State = if (ok) state else error(cat_lines(errors))
      override def toString: String = if (ok) "Result(ok)" else "Result(error)"
    }

    def context(
      settings: List[String] = Nil,
      jar_dirs: List[JFile] = Nil,
      class_loader: Option[ClassLoader] = None
    ): Context = {
      val isabelle_settings =
        Word.explode(Isabelle_System.getenv_strict("ISABELLE_SCALAC_OPTIONS"))

      def find_jars(dir: JFile): List[String] =
        File.find_files(dir, file => file.getName.endsWith(".jar")).
          map(File.absolute_name)

      val classpath = (class_path() ::: jar_dirs.flatMap(find_jars)).mkString(JFile.pathSeparator)
      val settings1 = isabelle_settings ::: settings ::: List("-classpath", classpath)
      new Context(settings1, class_loader)
    }

    class Context private [Compiler](
      val settings: List[String],
      val class_loader: Option[ClassLoader] = None
    ) {
      private val out_stream = new ByteArrayOutputStream(1024)
      private val out = new PrintStream(out_stream)
      private val driver: ReplDriver = new ReplDriver(settings.toArray, out, class_loader)

      def init_state: repl.State = driver.initialState

      def compile(source: String, state: repl.State = init_state): Result = {
        out.flush()
        out_stream.reset()
        val state1 = driver.run(source)(state)
        out.flush()
        val messages = Message.split(out_stream.toString(UTF8.charset))
        out_stream.reset()
        Result(state1, messages)
      }
    }
  }

  object Toplevel extends Fun_String("scala_toplevel") {
    val here = Scala_Project.here
    def apply(source: String): String = {
      val errors =
        try { Compiler.context().compile(source).errors.map("Scala error: " + _) }
        catch { case ERROR(msg) => List(msg) }
      locally { import XML.Encode._; YXML.string_of_body(list(string)(errors)) }
    }
  }



  /** interpreter thread **/

  object Interpreter {
    /* requests */

    sealed abstract class Request
    case class Execute(command: (Compiler.Context, repl.State) => repl.State) extends Request
    case object Shutdown extends Request


    /* known interpreters */

    private val known = Synchronized(Set.empty[Interpreter])

    def add(interpreter: Interpreter): Unit = known.change(_ + interpreter)
    def del(interpreter: Interpreter): Unit = known.change(_ - interpreter)

    def get[A](which: PartialFunction[Interpreter, A]): Option[A] =
      known.value.collectFirst(which)
  }

  class Interpreter(context: Compiler.Context, out: OutputStream = Console.out) {
    interpreter =>

    private val running = Synchronized[Option[Thread]](None)
    def running_thread(thread: Thread): Boolean = running.value.contains(thread)
    def interrupt_thread(): Unit = running.change({ opt => opt.foreach(_.interrupt()); opt })

    private var state = context.init_state

    private lazy val thread: Consumer_Thread[Interpreter.Request] =
      Consumer_Thread.fork("Scala.Interpreter") {
        case Interpreter.Execute(command) =>
          try {
            running.change(_ => Some(Thread.currentThread()))
            state = command(context, state)
          }
          finally {
            running.change(_ => None)
            Exn.Interrupt.dispose()
          }
          true
        case Interpreter.Shutdown =>
          Interpreter.del(interpreter)
          false
      }

    def shutdown(): Unit = {
      thread.send(Interpreter.Shutdown)
      interrupt_thread()
      thread.shutdown()
    }

    def execute(command: (Compiler.Context, repl.State) => repl.State): Unit =
      thread.send(Interpreter.Execute(command))

    def reset(): Unit =
      thread.send(Interpreter.Execute((context, _) => context.init_state))

    Interpreter.add(interpreter)
    thread
  }



  /** invoke Scala functions from ML **/

  /* invoke function */

  object Tag extends Enumeration {
    val NULL, OK, ERROR, FAIL, INTERRUPT = Value
  }

  def function_thread(name: String): Boolean =
    functions.find(fun => fun.name == name) match {
      case Some(fun) => fun.thread
      case None => false
    }

  def function_body(name: String, args: List[Bytes]): (Tag.Value, List[Bytes]) =
    functions.find(fun => fun.name == name) match {
      case Some(fun) =>
        Exn.capture { fun.invoke(args) } match {
          case Exn.Res(null) => (Tag.NULL, Nil)
          case Exn.Res(res) => (Tag.OK, res)
          case Exn.Exn(Exn.Interrupt()) => (Tag.INTERRUPT, Nil)
          case Exn.Exn(e) => (Tag.ERROR, List(Bytes(Exn.message(e))))
        }
      case None => (Tag.FAIL, List(Bytes("Unknown Isabelle/Scala function: " + quote(name))))
    }


  /* protocol handler */

  class Handler extends Session.Protocol_Handler {
    private var session: Session = null
    private var futures = Map.empty[String, Future[Unit]]

    override def init(session: Session): Unit =
      synchronized { this.session = session }

    override def exit(): Unit = synchronized {
      for ((id, future) <- futures) cancel(id, future)
      futures = Map.empty
    }

    private def result(id: String, tag: Scala.Tag.Value, res: List[Bytes]): Unit =
      synchronized {
        if (futures.isDefinedAt(id)) {
          session.protocol_command_raw("Scala.result", Bytes(id) :: Bytes(tag.id.toString) :: res)
          futures -= id
        }
      }

    private def cancel(id: String, future: Future[Unit]): Unit = {
      future.cancel()
      result(id, Scala.Tag.INTERRUPT, Nil)
    }

    private def invoke_scala(msg: Prover.Protocol_Output): Boolean = synchronized {
      msg.properties match {
        case Markup.Invoke_Scala(name, id) =>
          def body(): Unit = {
            val (tag, res) = Scala.function_body(name, msg.chunks)
            result(id, tag, res)
          }
          val future =
            if (Scala.function_thread(name)) {
              Future.thread(name = Isabelle_Thread.make_name(base = "invoke_scala"))(body())
            }
            else Future.fork(body())
          futures += (id -> future)
          true
        case _ => false
      }
    }

    private def cancel_scala(msg: Prover.Protocol_Output): Boolean = synchronized {
      msg.properties match {
        case Markup.Cancel_Scala(id) =>
          futures.get(id) match {
            case Some(future) => cancel(id, future)
            case None =>
          }
          true
        case _ => false
      }
    }

    override val functions: Session.Protocol_Functions =
      List(
        Markup.Invoke_Scala.name -> invoke_scala,
        Markup.Cancel_Scala.name -> cancel_scala)
  }
}

class Scala_Functions extends Scala.Functions(
  Scala.Echo,
  Scala.Sleep,
  Scala.Toplevel,
  Base64.Decode,
  Base64.Encode,
  XZ.Compress,
  XZ.Uncompress,
  Doc.Doc_Names,
  Bibtex.Check_Database,
  Isabelle_System.Make_Directory,
  Isabelle_System.Copy_Dir,
  Isabelle_System.Copy_File,
  Isabelle_System.Copy_File_Base,
  Isabelle_System.Rm_Tree,
  Isabelle_System.Download,
  Isabelle_System.Isabelle_Id,
  Isabelle_Tool.Isabelle_Tools,
  isabelle.atp.SystemOnTPTP.List_Systems,
  isabelle.atp.SystemOnTPTP.Run_System)
