/*  Title:      Tools/jEdit/src/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}
import javax.swing.event.TreeSelectionEvent

import org.gjt.sp.jedit.View


class Output_Dockable(view: View, position: String) extends Dockable(view, position) {
  dockable =>


  /* component state -- owned by GUI thread */

  private var do_update = true
  private var current_output: List[XML.Elem] = Nil


  /* pretty text area */

  private val output: Output_Area =
    new Output_Area(view, root_name = "Search results") {
      override def handle_search(search: Pretty_Text_Area.Search_Results): Unit = {
        tree.clear()
        for (result <- search.results) tree.root.add(Tree_View.Node(result))
        tree.reload_model()
        tree.expandRow(0)
        tree.revalidate()
      }
      override def handle_update(): Unit = dockable.handle_update(true)
    }

  override def detach_operation: Option[() => Unit] =
    output.pretty_text_area.detach_operation

  private def handle_update(follow: Boolean, restriction: Option[Set[Command]] = None): Unit = {
    GUI_Thread.require {}

    for {
      snapshot <- PIDE.editor.current_node_snapshot(view)
      if follow && !snapshot.is_outdated
    } {
      val (command, results) =
        PIDE.editor.current_command(view, snapshot) match {
          case Some(command) => (command, snapshot.command_results(command))
          case None => (Command.empty, Command.Results.empty)
        }

      val new_output =
        if (restriction.isEmpty || restriction.get.contains(command))
          Rendering.output_messages(results, JEdit_Options.output_state())
        else current_output

      if (current_output != new_output) {
        output.pretty_text_area.update(snapshot, results, new_output)
        current_output = new_output
      }
    }
  }


  /* tree view */

  private def tree_selection(): Option[Pretty_Text_Area.Search_Result] =
    output.tree.get_selection({ case x: Pretty_Text_Area.Search_Result => x })

  output.tree.addTreeSelectionListener({ (e: TreeSelectionEvent) =>
    for (result <- tree_selection()) {
      output.pretty_text_area.setCaretPosition(result.line_range.start)
      JEdit_Lib.scroll_to_caret(output.pretty_text_area)
    }
  })

  output.init_gui(dockable, split = true)


  /* controls */

  private val output_state_button = new JEdit_Options.output_state.GUI

  private val auto_hovering_button = new JEdit_Options.auto_hovering.GUI

  private val auto_update_button = new GUI.Check("Auto update", init = do_update) {
    tooltip = "Indicate automatic update following cursor movement"
    override def clicked(state: Boolean): Unit = {
      do_update = state
      handle_update(do_update)
    }
  }

  private val update_button = new GUI.Button("Update") {
    tooltip = "Update display according to the command at cursor position"
    override def clicked(): Unit = handle_update(true)
  }

  private val controls =
    Wrap_Panel(
      List(output_state_button, auto_hovering_button, auto_update_button, update_button) :::
      output.pretty_text_area.search_zoom_components)

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          output.handle_resize()
          output_state_button.load()
          auto_hovering_button.load()
          handle_update(do_update)
        }

      case changed: Session.Commands_Changed =>
        val restriction = if (changed.assignment) None else Some(changed.commands)
        GUI_Thread.later { handle_update(do_update, restriction = restriction) }

      case Session.Caret_Focus =>
        GUI_Thread.later { handle_update(do_update) }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    output.init()
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    PIDE.session.caret_focus -= main
    output.exit()
  }
}
