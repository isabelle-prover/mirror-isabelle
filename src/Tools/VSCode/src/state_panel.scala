/*  Title:      Tools/VSCode/src/state_panel.scala
    Author:     Makarius

Show proof state.
*/

package isabelle.vscode


import isabelle._


object State_Panel {
  private val make_id = Counter.make()
  private val instances = Synchronized(Map.empty[Counter.ID, State_Panel])

  def init(id: LSP.Id, server: Language_Server): Unit = {
    val instance = new State_Panel(server)
    instances.change(_ + (instance.id -> instance))
    instance.init()
    instance.init_response(id)
  }

  def exit(id: Counter.ID): Unit = {
    instances.change(map =>
      map.get(id) match {
        case None => map
        case Some(instance) => instance.exit(); map - id
      })
  }

  def locate(id: Counter.ID): Unit =
    instances.value.get(id).foreach(state =>
      state.server.editor.send_dispatcher(state.locate()))

  def update(id: Counter.ID): Unit =
    instances.value.get(id).foreach(state =>
      state.server.editor.send_dispatcher(state.update()))

  def auto_update(id: Counter.ID, enabled: Boolean): Unit =
    instances.value.get(id).foreach(state =>
      state.server.editor.send_dispatcher(state.auto_update(Some(enabled))))

  def set_margin(id: Counter.ID, margin: Double): Unit =
    instances.value.get(id).foreach(state => {
      state.margin.change(_ => margin)
      state.delay_margin.invoke()
    })
}


class State_Panel private(val server: Language_Server) {
  /* output */

  val id: Counter.ID = State_Panel.make_id()
  private val margin: Synchronized[Double] = Synchronized(server.resources.message_margin)

  private val delay_margin = Delay.last(server.resources.output_delay, server.channel.Error_Logger) {
    server.editor.send_dispatcher(update(force = true))
  }

  private def output(content: String, decorations: Option[LSP.Decoration_List] = None): Unit =
    server.channel.write(LSP.State_Output(id, content, auto_update_enabled.value, decorations))

  private def init_response(id: LSP.Id): Unit =
    server.channel.write(LSP.State_Init.reply(id, this.id))


  /* query operation */

  private val output_active = Synchronized(true)

  private val print_state =
    new Query_Operation(server.editor, (), "print_state", _ => (),
      (_, _, body) =>
        if (output_active.value && body.nonEmpty) {
          val (result, decorations) = server.resources.output_pretty_panel(body, margin.value)
          output(result, decorations)
        })

  def locate(): Unit = print_state.locate_query()

  def update(force: Boolean = false): Unit = {
    server.editor.current_node_snapshot(()) match {
      case Some(snapshot) =>
        if (force) {
          print_state.apply_query(Nil)
        } else {
          (server.editor.current_command((), snapshot), print_state.get_location) match {
            case (Some(command1), Some(command2)) if command1.id == command2.id =>
            case _ => print_state.apply_query(Nil)
          }
        }
      case None =>
    }
  }


  /* auto update */

  private val auto_update_enabled = Synchronized(true)

  def auto_update(set: Option[Boolean] = None): Unit = {
    val enabled =
      auto_update_enabled.guarded_access(a =>
        set match {
          case None => Some((a, a))
          case Some(b) => Some((b, b))
        })
    if (enabled) update()
  }



  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        if (changed.assignment) auto_update()

      case Session.Caret_Focus =>
        auto_update()
    }

  def init(): Unit = {
    server.session.commands_changed += main
    server.session.caret_focus += main
    server.editor.send_wait_dispatcher { print_state.activate() }
    server.editor.send_dispatcher { auto_update() }
  }

  def exit(): Unit = {
    output_active.change(_ => false)
    server.session.commands_changed -= main
    server.session.caret_focus -= main
    server.editor.send_wait_dispatcher { print_state.deactivate() }
  }
}
