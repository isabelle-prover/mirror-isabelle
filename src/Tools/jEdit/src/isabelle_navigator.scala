/*  Title:      Tools/jEdit/src/isabelle_navigator.scala
    Author:     Makarius

Navigate history of notable source positions.
*/

package isabelle.jedit


import org.gjt.sp.jedit.{View, Buffer, EditPane}


import isabelle._

object Isabelle_Navigator {
  object Pos {
    val none: Pos = new Pos(Document_ID.none, "", 0)
    def make(name: String, offset: Int): Pos = new Pos(Document_ID.make(), name, offset)

    def apply(buffer: Buffer): Pos =
      if (buffer == null) Pos.none else make(JEdit_Lib.buffer_name(buffer), 0)

    def apply(edit_pane: EditPane): Pos =
      if (edit_pane == null) none
      else {
        val buffer = edit_pane.getBuffer
        if (buffer != null && buffer.isLoaded && !buffer.isUntitled) {
          make(JEdit_Lib.buffer_name(buffer), edit_pane.getTextArea.getCaretPosition)
        }
        else none
      }

    def apply(view: View): Pos =
      if (view == null) none else apply(view.getEditPane)
  }

  final class Pos private(
    val id: Document_ID.Generic,
    val name: String,
    val offset: Int
  ) {
    def defined: Boolean = id != Document_ID.none

    override def toString: String =
      if (defined) "(offset " + offset + " of " + quote(name) + ")" else "Pos.none"

    override def hashCode: Int = id.hashCode
    override def equals(other: Any): Boolean =
      other match {
        case that: Pos => id == that.id
        case _ => false
      }

    def equiv(that: Pos): Boolean = name == that.name && offset == that.offset

    def convert(edit_name: String, edit: Text.Edit): Pos = {
      if (name == edit_name) {
        val offset1 = edit.convert(offset)
        if (offset == offset1) this else Pos.make(name, offset1)
      }
      else this
    }

    def goto(view: View): Unit = GUI_Thread.require {
      PIDE.editor.goto_file(true, view, name, offset = offset)
    }
  }

  object History {
    val limit: Int = 500
    val empty: History = new History(Linear_Set.empty)
  }

  class History(hist: Linear_Set[Pos]) {
    override def toString: String =
      size match {
        case 0 => "History.empty"
        case n => "History(" + n + ")"
      }
    def is_empty: Boolean = hist.isEmpty
    def size: Int = hist.size
    def iterator: Iterator[Pos] = hist.iterator

    def top: Pos = if (hist.isEmpty) Pos.none else hist.head
    def pop: History = if (hist.isEmpty) this else new History(hist.delete_after(None))

    def push(pos: Pos): History =
      if (!pos.defined || pos.equiv(top)) this
      else {
        val hist1 =
          if (hist.size < History.limit) hist
          else hist.delete_after(hist.prev(hist.last))
        new History(hist1.insert_after(None, pos))
      }

    def convert(name: String, edit: Text.Edit): History =
      new History(
        hist.foldLeft(hist) {
          case (h, pos) =>
            val prev = h.prev(pos)
            val pos0 = prev.getOrElse(Pos.none)
            val pos1 = pos.convert(name, edit)
            if (pos1.equiv(pos0)) h.delete_after(prev)
            else if (pos1.equiv(pos)) h
            else h.delete_after(prev).insert_after(prev, pos1)
        }
      )

    def close(names: Set[String]): History =
      new History(
        hist.foldLeft(hist) {
          case (h, pos) =>
            val prev = h.prev(pos)
            val pos0 = prev.getOrElse(Pos.none)
            if (names.contains(pos.name) || pos.equiv(pos0)) h.delete_after(prev)
            else h
        }
      )
  }

  final class State private[Isabelle_Navigator](view: View) {
  }
}

class Isabelle_Navigator {
  import Isabelle_Navigator.{Pos, History}

  // owned by GUI thread
  private var _bypass = false
  var _current: Pos = Pos.none
  var _backward = History.empty
  var _forward = History.empty

  override def toString: String = {
    val size = (if (_current.defined) 1 else 0) + _backward.size + _forward.size
    "Isabelle_Navigator(" + (if (size == 0) "" else size.toString) + ")"
  }

  private def convert(name: String, edit: Text.Edit): Unit = GUI_Thread.require {
    _current = _current.convert(name, edit)
    _backward = _backward.convert(name, edit)
    _forward = _forward.convert(name, edit)
  }

  private def close(names: Set[String]): Unit = GUI_Thread.require {
    if (names.contains(_current.name)) _current = Pos.none
    _backward = _backward.close(names)
    _forward = _forward.close(names)
  }

  private val buffer_listener =
    JEdit_Lib.buffer_listener((buffer, edit) => convert(JEdit_Lib.buffer_name(buffer), edit))

  def exit(buffers: IterableOnce[Buffer]): Unit = GUI_Thread.require {
    buffers.iterator.foreach(_.removeBufferListener(buffer_listener))
    close(buffers.iterator.map(JEdit_Lib.buffer_name).toSet)
  }

  def init(buffers: IterableOnce[Buffer]): Unit = GUI_Thread.require {
    exit(buffers)
    buffers.iterator.foreach(_.addBufferListener(buffer_listener))
  }

  def reset(): Unit = GUI_Thread.require {
    _current = Pos.none
    _backward = History.empty
    _forward = History.empty
  }

  def record(pos: Pos): Unit = GUI_Thread.require {
    if (!_bypass && pos.defined && !pos.equiv(_current)) {
      _backward = _backward.push(_current)
      _forward = History.empty
      _current = pos
    }
  }

  def record(buffer: Buffer): Unit = record(Pos(buffer))
  def record(edit_pane: EditPane): Unit = record(Pos(edit_pane))
  def record(view: View): Unit = record(Pos(view))

  def goto_current(view: View): Unit = GUI_Thread.require {
    if (_current.defined) {
      val b = _bypass
      try { _bypass = true; _current.goto(view) }
      finally { _bypass = b }
    }
  }

  def forward(view: View): Unit = GUI_Thread.require {
    if (!_forward.is_empty) {
      _backward = _backward.push(_current)
      _current = _forward.top
      _forward = _forward.pop
      goto_current(view)
    }
  }

  def backward(view: View): Unit = GUI_Thread.require {
    if (!_backward.is_empty) {
      val pos0 = _current
      val pos1 = Pos(view)

      def move(pos: Pos): Unit = {
        _forward = _forward.push(pos)
        _current = _backward.top
        _backward = _backward.pop
      }

      if (pos0.defined) move(pos0)
      if (pos1.defined && !pos1.equiv(pos0)) move(pos1)

      goto_current(view)
    }
  }
}
