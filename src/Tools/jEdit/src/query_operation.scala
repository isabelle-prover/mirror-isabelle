/*  Title:      Tools/jEdit/src/query_operation.scala
    Author:     Makarius

One-shot query operations via asynchronous print functions and temporary
document overlays.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import org.gjt.sp.jedit.View


object Query_Operation
{
  object Status extends Enumeration
  {
    val WAITING = Value("waiting")
    val RUNNING = Value("running")
    val FINISHED = Value("finished")
  }
}

class Query_Operation(
  editor: Editor[View],
  view: View,
  operation_name: String,
  consume_status: Query_Operation.Status.Value => Unit,
  consume_output: (Document.Snapshot, Command.Results, XML.Body) => Unit)
{
  private val instance = Document_ID.make().toString


  /* implicit state -- owned by Swing thread */

  private var current_location: Option[Command] = None
  private var current_query: List[String] = Nil
  private var current_update_pending = false
  private var current_output: List[XML.Tree] = Nil
  private var current_status = Query_Operation.Status.FINISHED
  private var current_exec_id = Document_ID.none

  private def reset_state()
  {
    current_location = None
    current_query = Nil
    current_update_pending = false
    current_output = Nil
    current_status = Query_Operation.Status.FINISHED
    current_exec_id = Document_ID.none
  }

  private def remove_overlay()
  {
    Swing_Thread.require()

    for {
      command <- current_location
      buffer <- JEdit_Lib.jedit_buffer(command.node_name.node)
      model <- PIDE.document_model(buffer)
    } model.remove_overlay(command, operation_name, instance :: current_query)
  }


  /* content update */

  private def content_update()
  {
    Swing_Thread.require()


    /* snapshot */

    val (snapshot, state, removed) =
      current_location match {
        case Some(cmd) =>
          val snapshot = editor.node_snapshot(cmd.node_name)
          val state = snapshot.state.command_state(snapshot.version, cmd)
          val removed = !snapshot.version.nodes(cmd.node_name).commands.contains(cmd)
          (snapshot, state, removed)
        case None =>
          (Document.Snapshot.init, Command.empty.init_state, true)
      }

    val results =
      (for {
        (_, elem @ XML.Elem(Markup(Markup.RESULT, props), _)) <- state.results.entries
        if props.contains((Markup.INSTANCE, instance))
      } yield elem).toList


    /* output */

    val new_output =
      for {
        XML.Elem(_, List(XML.Elem(markup, body))) <- results
        if Markup.messages.contains(markup.name)
      } yield XML.Elem(Markup(Markup.message(markup.name), markup.properties), body)


    /* status */

    def get_status(name: String, status: Query_Operation.Status.Value)
        : Option[Query_Operation.Status.Value] =
      results.collectFirst({ case XML.Elem(_, List(elem: XML.Elem)) if elem.name == name => status })

    val new_status =
      if (removed) Query_Operation.Status.FINISHED
      else
        get_status(Markup.FINISHED, Query_Operation.Status.FINISHED) orElse
        get_status(Markup.RUNNING, Query_Operation.Status.RUNNING) getOrElse
        Query_Operation.Status.WAITING

    if (new_status == Query_Operation.Status.RUNNING)
      results.collectFirst(
      {
        case XML.Elem(Markup(_, Position.Id(id)), List(elem: XML.Elem))
        if elem.name == Markup.RUNNING => id
      }).foreach(id => current_exec_id = id)


    /* state update */

    if (current_output != new_output || current_status != new_status) {
      if (snapshot.is_outdated)
        current_update_pending = true
      else {
        current_update_pending = false
        if (current_output != new_output && !removed) {
          current_output = new_output
          consume_output(snapshot, state.results, new_output)
        }
        if (current_status != new_status) {
          current_status = new_status
          consume_status(new_status)
          if (new_status == Query_Operation.Status.FINISHED) {
            remove_overlay()
            editor.flush()
          }
        }
      }
    }
  }


  /* query operations */

  def cancel_query(): Unit =
    Swing_Thread.require { editor.session.cancel_exec(current_exec_id) }

  def apply_query(query: List[String])
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        val snapshot = doc_view.model.snapshot()
        remove_overlay()
        reset_state()
        consume_output(Document.Snapshot.init, Command.Results.empty, Nil)
        snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
          case Some(command) =>
            current_location = Some(command)
            current_query = query
            current_status = Query_Operation.Status.WAITING
            doc_view.model.insert_overlay(command, operation_name, instance :: query)
          case None =>
        }
        consume_status(current_status)
        editor.flush()
      case None =>
    }
  }

  def locate_query()
  {
    Swing_Thread.require()

    current_location match {
      case Some(command) =>
        val snapshot = editor.node_snapshot(command.node_name)
        val commands = snapshot.node.commands
        if (commands.contains(command)) {
          // FIXME revert offset (!?)
          val sources = commands.iterator.takeWhile(_ != command).map(_.source)
          val (line, column) = ((1, 1) /: sources)(Symbol.advance_line_column)
          Hyperlink(command.node_name.node, line, column).follow(view)
        }
      case None =>
    }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case changed: Session.Commands_Changed =>
          current_location match {
            case Some(command)
            if current_update_pending ||
              (current_status != Query_Operation.Status.FINISHED &&
                changed.commands.contains(command)) =>
              Swing_Thread.later { content_update() }
            case _ =>
          }
        case bad =>
          java.lang.System.err.println("Query_Operation: ignoring bad message " + bad)
      }
    }
  }

  def activate() { editor.session.commands_changed += main_actor }
  def deactivate() { editor.session.commands_changed -= main_actor }
}
