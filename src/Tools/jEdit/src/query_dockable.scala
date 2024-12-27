/*  Title:      Tools/jEdit/src/query_dockable.scala
    Author:     Makarius

Dockable window for query operations.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}
import javax.swing.JComponent

import scala.swing.{Component, TextField, Label, TabbedPane, BorderPanel}
import scala.swing.event.{SelectionChanged, Key, KeyPressed}

import org.gjt.sp.jedit.View


object Query_Dockable {
  private abstract class Operation(view: View) {
    val pretty_text_area = new Pretty_Text_Area(view)
    def query_operation: Query_Operation[View]
    def query: JComponent
    def select(): Unit
    def page: TabbedPane.Page
  }
}

class Query_Dockable(view: View, position: String) extends Dockable(view, position) {
  /* common GUI components */

  private val zoom = new Font_Info.Zoom { override def changed(): Unit = handle_resize() }

  private def make_query(
    property: String,
    tooltip: String,
    apply_query: () => Unit
  ): Completion_Popup.History_Text_Field = {
    new Completion_Popup.History_Text_Field(property) {
      override def processKeyEvent(evt: KeyEvent): Unit = {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) apply_query()
        super.processKeyEvent(evt)
      }
      { val max = getPreferredSize; max.width = Int.MaxValue; setMaximumSize(max) }
      setColumns(40)
      setToolTipText(tooltip)
      setFont(GUI.imitate_font(getFont, scale = 1.2))
    }
  }


  /* consume status */

  def consume_status(
    process_indicator: Process_Indicator,
    status: Query_Operation.Status
  ): Unit = {
    status match {
      case Query_Operation.Status.waiting =>
        process_indicator.update("Waiting for evaluation of context ...", 5)
      case Query_Operation.Status.running =>
        process_indicator.update("Running find operation ...", 15)
      case Query_Operation.Status.finished =>
        process_indicator.update(null, 0)
    }
  }


  /* find theorems */

  private val find_theorems: Query_Dockable.Operation = new Query_Dockable.Operation(view) {
    /* query */

    private val process_indicator = new Process_Indicator

    val query_operation =
      new Query_Operation(PIDE.editor, view, "find_theorems",
        consume_status(process_indicator, _), pretty_text_area.update)

    private def apply_query(): Unit = {
      query.addCurrentToHistory()
      query_operation.apply_query(List(limit.text, allow_dups.selected.toString, query.getText))
    }

    private val query_label = new Label("Find:") {
      tooltip =
        GUI.tooltip_lines(
          "Search criteria for find operation, e.g.\n\"_ = _\" \"(+)\" name: Group -name: monoid")
    }

    val query: Completion_Popup.History_Text_Field =
      make_query("isabelle-find-theorems", query_label.tooltip, apply_query _)


    /* GUI page */

    private val limit = new TextField(PIDE.options.int("find_theorems_limit").toString, 5) {
      tooltip = "Limit of displayed results"
      verifier = { case Value.Int(x) => x >= 0 case _ => false }
      listenTo(keys)
      reactions += { case KeyPressed(_, Key.Enter, 0, _) => apply_query() }
    }

    private val allow_dups = new GUI.Check("Duplicates") {
      tooltip = "Show all versions of matching theorems"
      override def clicked(): Unit = apply_query()
    }

    private val apply_button = new GUI.Button(GUI.Style_HTML.enclose_bold("Apply")) {
      tooltip = "Find theorems meeting specified criteria"
      override def clicked(): Unit = apply_query()
    }

    private val control_panel =
      Wrap_Panel(
        List(query_label, Component.wrap(query), limit, allow_dups,
          process_indicator.component, apply_button) :::
        pretty_text_area.search_components)

    def select(): Unit = { control_panel.contents += zoom }

    val page =
      new TabbedPane.Page("Find Theorems", new BorderPanel {
        layout(control_panel) = BorderPanel.Position.North
        layout(Component.wrap(pretty_text_area)) = BorderPanel.Position.Center
      }, apply_button.tooltip)
  }


  /* find consts */

  private val find_consts: Query_Dockable.Operation = new Query_Dockable.Operation(view) {
    /* query */

    private val process_indicator = new Process_Indicator

    val query_operation =
      new Query_Operation(PIDE.editor, view, "find_consts",
        consume_status(process_indicator, _), pretty_text_area.update)

    private val query_label = new Label("Find:") {
      tooltip = GUI.tooltip_lines("Name / type patterns for constants")
    }

    val query: Completion_Popup.History_Text_Field =
      make_query("isabelle-find-consts", query_label.tooltip, apply_query _)

    private def apply_query(): Unit = {
      query.addCurrentToHistory()
      query_operation.apply_query(List(query.getText))
    }


    /* GUI page */

    private val apply_button = new GUI.Button(GUI.Style_HTML.enclose_bold("Apply")) {
      tooltip = "Find constants by name / type patterns"
      override def clicked(): Unit = apply_query()
    }

    private val control_panel =
      Wrap_Panel(
        List(query_label, Component.wrap(query), process_indicator.component, apply_button) :::
        pretty_text_area.search_components)

    def select(): Unit = { control_panel.contents += zoom }

    val page =
      new TabbedPane.Page("Find Constants", new BorderPanel {
        layout(control_panel) = BorderPanel.Position.North
        layout(Component.wrap(pretty_text_area)) = BorderPanel.Position.Center
      }, apply_button.tooltip)
  }


  /* print operation */

  private val print_operation = new Query_Dockable.Operation(view) {
    /* items */

    private class Item(val name: String, description: String, selected: Boolean) {
      val gui: GUI.Check = new GUI.Check(name, init = selected) {
        tooltip = "Print " + description
        override def clicked(): Unit = apply_query()
      }
    }

    private var _items: List[Item] = Nil

    private def selected_items(): List[String] =
      for (item <- _items if item.gui.selected) yield item.name

    private def update_items(): List[Item] = {
      val old_items = _items
      def was_selected(name: String): Boolean =
        old_items.find(item => item.name == name) match {
          case None => false
          case Some(item) => item.gui.selected
        }

      _items =
        for ((name, description) <- Print_Operation.get(PIDE.session))
        yield new Item(name, description, was_selected(name))
      _items
    }


    /* query */

    private val process_indicator = new Process_Indicator

    val query_operation =
      new Query_Operation(PIDE.editor, view, "print_operation",
        consume_status(process_indicator, _), pretty_text_area.update)

    private def apply_query(): Unit =
      query_operation.apply_query(selected_items())

    private val query_label = new Label("Print:")
    def query: JComponent = apply_button.peer

    update_items()


    /* GUI page */

    private val apply_button = new GUI.Button(GUI.Style_HTML.enclose_bold("Apply")) {
      tooltip = "Apply to current context"
      override def clicked(): Unit = apply_query()

      listenTo(keys)
      reactions += {
        case evt @ KeyPressed(_, Key.Enter, 0, _) =>
          evt.peer.consume()
          apply_query()
      }
    }

    private val control_panel = Wrap_Panel()

    def select(): Unit = {
      control_panel.contents.clear()
      control_panel.contents += query_label
      update_items().foreach(item => control_panel.contents += item.gui)
      control_panel.contents ++=
        List(process_indicator.component, apply_button) :::
        pretty_text_area.search_components ::: List(zoom)
    }

    val page =
      new TabbedPane.Page("Print Context", new BorderPanel {
        layout(control_panel) = BorderPanel.Position.North
        layout(Component.wrap(pretty_text_area)) = BorderPanel.Position.Center
      }, "Print information from context")
  }


  /* operations */

  private val operations = List(find_theorems, find_consts, print_operation)

  private val operations_pane = new TabbedPane {
    pages ++= operations.map(_.page)
    listenTo(selection)
    reactions += { case SelectionChanged(_) => select_operation() }
  }

  private def get_operation(): Option[Query_Dockable.Operation] =
    try { Some(operations(operations_pane.selection.index)) }
    catch { case _: IndexOutOfBoundsException => None }

  private def select_operation(): Unit = {
    for (op <- get_operation()) { op.select(); op.query.requestFocus() }
    operations_pane.revalidate()
  }

  override def focusOnDefaultComponent(): Unit = {
    for (op <- get_operation()) op.query.requestFocus()
  }

  select_operation()
  set_content(operations_pane)

  override def detach_operation: Option[() => Unit] =
    get_operation() match {
      case None => None
      case Some(op) => op.pretty_text_area.detach_operation
    }


  /* resize */

  private def handle_resize(): Unit =
    GUI_Thread.require {
      if (operations != null) operations.foreach(_.pretty_text_area.zoom(zoom = zoom))
    }

  private val delay_resize =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options => GUI_Thread.later { handle_resize() }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    handle_resize()
    operations.foreach(op => op.query_operation.activate())
  }

  override def exit(): Unit = {
    operations.foreach(op => op.query_operation.deactivate())
    PIDE.session.global_options -= main
    delay_resize.revoke()
  }
}

