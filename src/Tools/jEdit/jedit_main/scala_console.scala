/*  Title:      Tools/jEdit/jedit_main/scala_console.scala
    Author:     Makarius

Scala instance of Console plugin.
*/

package isabelle.jedit_main


import isabelle._
import isabelle.jedit._

import console.{Console, ConsolePane, Shell, Output}
import org.gjt.sp.jedit.JARClassLoader
import java.io.OutputStream


object Scala_Console {
  class Interpreter(context: Scala.Compiler.Context, val console: Console)
    extends Scala.Interpreter(context)

  def console_interpreter(console: Console): Option[Interpreter] =
    Scala.Interpreter.get { case int: Interpreter if int.console == console => int }

  def running_interpreter(): Interpreter = {
    val self = Thread.currentThread()
    Scala.Interpreter.get { case int: Interpreter if int.running_thread(self) => int }
      .getOrElse(error("Bad Scala interpreter thread"))
  }

  def running_console(): Console = running_interpreter().console

  val init = """
import isabelle._
import isabelle.jedit._
val console = isabelle.jedit_main.Scala_Console.running_console()
val view = console.getView()
"""
}

class Scala_Console extends Shell("Scala") {
  /* global state -- owned by GUI thread */

  @volatile private var global_console: Console = null
  @volatile private var global_out: Output = null
  @volatile private var global_err: Output = null

  private val console_stream = new OutputStream {
    val buf = new StringBuilder(100)

    override def flush(): Unit = {
      val s = buf.synchronized { val s = buf.toString; buf.clear(); s }
      val str = UTF8.decode_permissive(Bytes.raw(s))
      GUI_Thread.later {
        if (global_out == null) java.lang.System.out.print(str)
        else global_out.writeAttrs(null, str)
      }
      Time.seconds(0.01).sleep()  // FIXME adhoc delay to avoid loosing output
    }

    override def close(): Unit = flush()

    def write(byte: Int): Unit = {
      val c = byte.toChar
      buf.synchronized { buf.append(c) }
      if (c == '\n') flush()
    }
  }

  private def with_console[A](console: Console, out: Output, err: Output)(e: => A): A = {
    global_console = console
    global_out = out
    global_err = if (err == null) out else err
    try {
      scala.Console.withErr(console_stream) {
        scala.Console.withOut(console_stream) { e }
      }
    }
    finally {
      console_stream.flush()
      global_console = null
      global_out = null
      global_err = null
    }
  }


  /* jEdit console methods */

  override def openConsole(console: Console): Unit = {
    val context =
      Scala.Compiler.context(
      jar_files = JEdit_Lib.directories,
      class_loader = Some(new JARClassLoader))

    val interpreter = new Scala_Console.Interpreter(context, console)
    interpreter.execute((context, state) =>
      context.compile(Scala_Console.init, state = state).state)
  }

  override def closeConsole(console: Console): Unit =
    Scala_Console.console_interpreter(console).foreach(_.shutdown())

  override def printInfoMessage(out: Output): Unit = {
    out.print(null,
     "This shell evaluates Isabelle/Scala expressions.\n\n" +
     "The contents of package isabelle and isabelle.jedit are imported.\n" +
     "The following special toplevel bindings are provided:\n" +
     "  view    -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  console -- jEdit Console plugin\n" +
     "  PIDE    -- Isabelle/PIDE plugin (e.g. PIDE.session, PIDE.snapshot, PIDE.rendering)\n")
  }

  override def printPrompt(console: Console, out: Output): Unit = {
    out.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor), "scala>")
    out.writeAttrs(ConsolePane.colorAttributes(console.getPlainColor), " ")
  }

  override def execute(
    console: Console,
    input: String,
    out: Output,
    err: Output,
    command: String
  ): Unit = {
    Scala_Console.console_interpreter(console).foreach(interpreter =>
      interpreter.execute { (context, state) =>
        val result = with_console(console, out, err) { context.compile(command, state) }
        GUI_Thread.later {
          val diag = if (err == null) out else err
          for (message <- result.messages) {
            val color = if (message.is_error) console.getErrorColor else null
            diag.print(color, message.text + "\n")
          }
          Option(err).foreach(_.commandDone())
          out.commandDone()
        }
        result.state
      })
  }

  override def stop(console: Console): Unit =
    Scala_Console.console_interpreter(console).foreach(_.shutdown())
}
