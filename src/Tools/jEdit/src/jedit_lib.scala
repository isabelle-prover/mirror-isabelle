/*  Title:      Tools/jEdit/src/jedit_lib.scala
    Author:     Makarius

Misc library functions for jEdit.
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile}
import java.awt.{Component, Container, Toolkit}
import java.awt.event.{InputEvent, KeyEvent, KeyListener}
import java.awt.font.FontRenderContext
import javax.swing.{ImageIcon, JScrollBar, JWindow}

import scala.util.parsing.input.CharSequenceReader
import scala.util.matching.Regex
import scala.jdk.CollectionConverters._
import scala.annotation.tailrec

import org.gjt.sp.jedit.{jEdit, Buffer, View, GUIUtilities, Debug, EditPane}
import org.gjt.sp.jedit.io.{FileVFS, VFSManager}
import org.gjt.sp.jedit.gui.{KeyEventWorkaround, KeyEventTranslator}
import org.gjt.sp.jedit.buffer.{BufferListener, BufferAdapter, JEditBuffer, LineManager}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaPainter, Selection, AntiAlias}

import com.formdev.flatlaf.extras.FlatSVGIcon


object JEdit_Lib {
  /* jEdit directories */

  def directories: List[JFile] =
    (Option(jEdit.getSettingsDirectory).toList ::: List(jEdit.getJEditHome)).map(new JFile(_))


  /* window geometry measurement */

  private lazy val dummy_window = new JWindow

  final case class Window_Geometry(width: Int, height: Int, inner_width: Int, inner_height: Int) {
    def deco_width: Int = width - inner_width
    def deco_height: Int = height - inner_height
  }

  def window_geometry(outer: Container, inner: Component): Window_Geometry = {
    GUI_Thread.require {}

    val old_content = dummy_window.getContentPane

    dummy_window.setContentPane(outer)
    dummy_window.pack()
    dummy_window.revalidate()

    val geometry =
      Window_Geometry(
        dummy_window.getWidth, dummy_window.getHeight, inner.getWidth, inner.getHeight)

    dummy_window.setContentPane(old_content)

    geometry
  }


  /* plain files */

  def is_file(name: String): Boolean =
    name != null && name.nonEmpty && VFSManager.getVFSForPath(name).isInstanceOf[FileVFS]

  def check_file(name: String): Option[JFile] =
    if (is_file(name)) Some(new JFile(name)) else None


  /* buffers */

  def buffer_text(buffer: JEditBuffer): String =
    buffer_lock(buffer) { buffer.getText(0, buffer.getLength) }

  def buffer_reader(buffer: JEditBuffer): CharSequenceReader =
    Scan.char_reader(buffer.getSegment(0, buffer.getLength))

  def buffer_mode(buffer: JEditBuffer): String = {
    val mode = buffer.getMode
    if (mode == null) ""
    else {
      val name = mode.getName
      if (name == null) "" else name
    }
  }

  def buffer_line_manager(buffer: JEditBuffer): LineManager =
    Untyped.get[LineManager](buffer, "lineMgr")

  def buffer_name(buffer: Buffer): String = buffer.getSymlinkPath

  def buffer_file(buffer: Buffer): Option[JFile] = check_file(buffer_name(buffer))


  /* main jEdit components */

  def jedit_buffers(): Iterator[Buffer] =
    jEdit.getBufferManager().getBuffers().asScala.iterator

  def jedit_buffer(name: String): Option[Buffer] =
    jedit_buffers().find(buffer => buffer_name(buffer) == name)

  def jedit_buffer(name: Document.Node.Name): Option[Buffer] =
    jedit_buffer(name.node)

  def jedit_views(): Iterator[View] =
    jEdit.getViewManager().getViews().asScala.iterator

  def jedit_view(view: View = null): View =
    if (view == null) jEdit.getActiveView else view

  def jedit_edit_panes(view: View): Iterator[EditPane] =
    if (view == null) Iterator.empty
    else view.getEditPanes().iterator.filter(_ != null)

  def jedit_text_areas(view: View): Iterator[JEditTextArea] =
    if (view == null) Iterator.empty
    else view.getEditPanes().iterator.filter(_ != null).map(_.getTextArea).filter(_ != null)

  def jedit_text_areas(): Iterator[JEditTextArea] =
    jedit_views().flatMap(jedit_text_areas)

  def jedit_text_areas(buffer: JEditBuffer): Iterator[JEditTextArea] =
    jedit_text_areas().filter(_.getBuffer == buffer)

  def buffer_lock[A](buffer: JEditBuffer)(body: => A): A = {
    try { buffer.readLock(); body }
    finally { buffer.readUnlock() }
  }

  def buffer_edit[A](buffer: JEditBuffer)(body: => A): A = {
    try { buffer.beginCompoundEdit(); body }
    finally { buffer.endCompoundEdit() }
  }


  /* buffer text */

  def get_text(buffer: JEditBuffer, range: Text.Range): Option[String] =
    try { Some(buffer.getText(range.start, range.length)) }
    catch { case _: ArrayIndexOutOfBoundsException => None }

  def can_search_text(buffer: JEditBuffer, range: Text.Range, regex: Regex): Boolean =
    try { regex.findFirstIn(buffer.getSegment(range.start, range.length)).nonEmpty }
    catch { case _: ArrayIndexOutOfBoundsException => false }

  def search_text(buffer: JEditBuffer, range: Text.Range, regex: Regex): List[Text.Range] =
    List.from(
      for {
        s <- get_text(buffer, range).iterator
        m <- regex.findAllMatchIn(s)
      } yield Text.Range(range.start + m.start, range.start + m.end))

  def set_text(buffer: JEditBuffer, text: List[String]): Int = {
    val old = buffer.isUndoInProgress
    def set(b: Boolean): Unit = Untyped.set[Boolean](buffer, "undoInProgress", b)

    val length = buffer.getLength
    var offset = 0

    @tailrec def drop_common_prefix(list: List[String]): List[String] =
      list match {
        case s :: rest
          if offset + s.length <= length &&
          CharSequence.compare(buffer.getSegment(offset, s.length), s) == 0 =>
            offset += s.length
            drop_common_prefix(rest)
        case _ => list
      }

    def insert(list: List[String]): Unit =
      for (s <- list) {
        buffer.insert(offset, s)
        offset += s.length
      }

    try {
      set(true)
      buffer.beginCompoundEdit()
      val rest = drop_common_prefix(text)
      val update_start = offset
      if (offset < length) buffer.remove(offset, length - offset)
      insert(rest)
      update_start
    }
    finally {
      buffer.endCompoundEdit()
      set(old)
    }
  }


  /* point range */

  def point_range(buffer: JEditBuffer, offset: Text.Offset): Text.Range =
    if (offset < 0) Text.Range.offside
    else
      buffer_lock(buffer) {
        def text(i: Text.Offset): Char = buffer.getText(i, 1).charAt(0)
        try {
          val c = text(offset)
          if (Character.isHighSurrogate(c) && Character.isLowSurrogate(text(offset + 1)))
            Text.Range(offset, offset + 2)
          else if (Character.isLowSurrogate(c) && Character.isHighSurrogate(text(offset - 1)))
            Text.Range(offset - 1, offset + 1)
          else
            Text.Range(offset, offset + 1)
        }
        catch { case _: ArrayIndexOutOfBoundsException => Text.Range(offset, offset + 1) }
      }


  /* text ranges */

  def buffer_range(buffer: JEditBuffer): Text.Range =
    Text.Range(0, buffer.getLength)

  def line_range(buffer: JEditBuffer, line: Int): Text.Range =
    Text.Range(buffer.getLineStartOffset(line), buffer.getLineEndOffset(line) min buffer.getLength)

  def caret_range(text_area: TextArea): Text.Range =
    point_range(text_area.getBuffer, text_area.getCaretPosition)

  def selection_ranges(text_area: TextArea): List[Text.Range] = {
    val buffer = text_area.getBuffer
    text_area.getSelection.toList.flatMap(
      {
        case rect: Selection.Rect =>
          List.from(
            for {
              l <- (rect.getStartLine to rect.getEndLine).iterator
              r = Text.Range(rect.getStart(buffer, l), rect.getEnd(buffer, l))
              if !r.is_singularity
            } yield r)
        case sel: Selection => List(Text.Range(sel.getStart, sel.getEnd))
      })
  }

  def visible_range(text_area: TextArea): Option[Text.Range] = {
    val buffer = text_area.getBuffer
    val n = text_area.getVisibleLines
    if (n > 0) {
      val start = text_area.getScreenLineStartOffset(0)
      val raw_end = text_area.getScreenLineEndOffset(n - 1)
      val end = if (raw_end >= 0) raw_end min buffer.getLength else buffer.getLength
      Some(Text.Range(start, end))
    }
    else None
  }

  def invalidate_range(text_area: TextArea, range: Text.Range): Unit = {
    val buffer = text_area.getBuffer
    buffer_range(buffer).try_restrict(range) match {
      case Some(range1) if !range1.is_singularity =>
        try {
          text_area.invalidateLineRange(
            buffer.getLineOfOffset(range1.start),
            buffer.getLineOfOffset(range1.stop))
        }
        catch { case _: ArrayIndexOutOfBoundsException => }
      case _ =>
    }
  }

  def invalidate_screen(text_area: TextArea, start: Int = -1, end: Int = -1): Unit = {
    val visible_lines = text_area.getVisibleLines
    if (visible_lines > 0) {
      val start_line = if (start >= 0) start else 0
      val end_line = if (end >= 0) end else visible_lines
      text_area.invalidateScreenLineRange(start_line, end_line)
    }
  }


  /* scrolling */

  def vertical_scrollbar(text_area: TextArea): JScrollBar =
    Untyped.get[JScrollBar](text_area, "vertical")

  def horizontal_scrollbar(text_area: TextArea): JScrollBar =
    Untyped.get[JScrollBar](text_area, "horizontal")

  def scrollbar_at_end(scrollbar: JScrollBar): Boolean =
    scrollbar.getValue > 0 &&
      scrollbar.getValue + scrollbar.getVisibleAmount == scrollbar.getMaximum

  def scrollbar_bottom(text_area: TextArea): Boolean =
    scrollbar_at_end(vertical_scrollbar(text_area))

  def scrollbar_start(text_area: TextArea): Int =
    text_area.getBuffer.getLineStartOffset(vertical_scrollbar(text_area).getValue)

  def bottom_line_offset(buffer: JEditBuffer): Int =
    buffer.getLineStartOffset(buffer.getLineOfOffset(buffer.getLength))

  def scroll_to_caret(text_area: TextArea): Unit = {
    val caret_line = text_area.getCaretLine()
    val display_manager = text_area.getDisplayManager
    if (!display_manager.isLineVisible(caret_line)) {
      display_manager.expandFold(caret_line, true)
    }
    text_area.scrollToCaret(true)
  }


  /* font */

  def init_font_context(view: View, painter: TextAreaPainter): Unit = {
    painter.setAntiAlias(new AntiAlias(jEdit.getProperty("view.antiAlias")))
    painter.setFractionalFontMetricsEnabled(jEdit.getBooleanProperty("view.fracFontMetrics"))
    val old = painter.getFontRenderContext
    Untyped.set[FontRenderContext](painter, "fontRenderContext",
      new FontRenderContext(view.getGraphicsConfiguration.getDefaultTransform,
        old.getAntiAliasingHint, old.getFractionalMetricsHint))
  }

  def font_metric(painter: TextAreaPainter): Font_Metric =
    new Font_Metric(
      font = painter.getFont,
      context = painter.getFontRenderContext)


  /* graphics range */

  case class Gfx_Range(x: Int, y: Int, length: Int)

  // NB: jEdit always normalizes \r\n and \r to \n
  // NB: last line lacks \n
  def gfx_range(text_area: TextArea): Text.Range => Option[Gfx_Range] = {
    val metric = font_metric(text_area.getPainter)
    val char_width = metric.average_width.round.toInt

    val buffer = text_area.getBuffer
    val end = buffer.getLength

    { (range: Text.Range) =>
      val stop = range.stop
      try {
        val p = text_area.offsetToXY(range.start)
        val (q, r) =
          if (get_text(buffer, Text.Range(stop - 1, stop)).contains("\n")) {
            (text_area.offsetToXY(stop - 1), char_width)
          }
          else if (stop >= end) {
            (text_area.offsetToXY(end), char_width * (stop - end))
          }
          else (text_area.offsetToXY(stop), 0)

        if (p != null && q != null && p.x < q.x + r && p.y == q.y) {
          Some(Gfx_Range(p.x, p.y, q.x + r - p.x))
        }
        else None
      }
      catch { case _: ArrayIndexOutOfBoundsException => None }
    }
  }


  /* pixel range */

  def pixel_range(text_area: TextArea, x: Int, y: Int): Option[Text.Range] = {
    // coordinates wrt. inner painter component
    val painter = text_area.getPainter
    val buffer = text_area.getBuffer
    if (0 <= x && x < painter.getWidth && 0 <= y && y < painter.getHeight) {
      val offset = text_area.xyToOffset(x, y, false)
      if (offset >= 0) {
        val range = point_range(buffer, offset)
        gfx_range(text_area)(range) match {
          case Some(g) if g.x <= x && x < g.x + g.length =>
            range.try_restrict(buffer_range(buffer))
          case _ => None
        }
      }
      else None
    }
    else None
  }


  /* icons */

  def load_icon(spec: String): ImageIcon =
    GUIUtilities.loadIcon(spec).asInstanceOf[ImageIcon]


  /* buffer event handling */

  private def buffer_edit(ins: Boolean, buf: JEditBuffer, i: Text.Offset, n: Int): Text.Edit = {
    val try_range = Text.Range(i, i + n.max(0)).try_restrict(buffer_range(buf))
    val edit_range = try_range.getOrElse(Text.Range.zero)
    val edit_text = try_range.flatMap(get_text(buf, _)).getOrElse("")
    Text.Edit.make(ins, edit_range.start, edit_text)
  }

  def buffer_listener(handle: (Buffer, Text.Edit) => Unit): BufferListener =
    new BufferAdapter {
      override def contentInserted(buf: JEditBuffer, line: Int, i: Int, lines: Int, n: Int): Unit =
        handle(buf.asInstanceOf[Buffer], buffer_edit(true, buf, i, n))
      override def preContentRemoved(buf: JEditBuffer, line: Int, i: Int, lines: Int, n: Int): Unit =
        handle(buf.asInstanceOf[Buffer], buffer_edit(false, buf, i, n))
    }


  /* key event handling */

  def request_focus_view(alt_view: View = null): Unit = {
    val view = if (alt_view != null) alt_view else jEdit.getActiveView
    if (view != null) {
      val text_area = view.getTextArea
      if (text_area != null) text_area.requestFocus()
    }
  }

  def propagate_key(view: View, evt: KeyEvent): Unit = {
    if (view != null && !evt.isConsumed)
      view.getInputHandler().processKeyEvent(evt, View.ACTION_BAR, false)
  }

  def key_listener(
    key_typed: KeyEvent => Unit = _ => (),
    key_pressed: KeyEvent => Unit = _ => (),
    key_released: KeyEvent => Unit = _ => ()
  ): KeyListener = {
    def process_key_event(evt0: KeyEvent, handle: KeyEvent => Unit): Unit = {
      val evt = KeyEventWorkaround.processKeyEvent(evt0)
      if (evt != null) handle(evt)
    }

    new KeyListener {
      def keyTyped(evt: KeyEvent): Unit = process_key_event(evt, key_typed)
      def keyPressed(evt: KeyEvent): Unit = process_key_event(evt, key_pressed)
      def keyReleased(evt: KeyEvent): Unit = process_key_event(evt, key_released)
    }
  }

  def special_key(evt: KeyEvent): Boolean = {
    // cf. 5.2.0/jEdit/org/gjt/sp/jedit/gui/KeyEventWorkaround.java
    val mod = evt.getModifiersEx
    (mod & InputEvent.CTRL_DOWN_MASK) != 0 && (mod & InputEvent.ALT_DOWN_MASK) == 0 ||
    (mod & InputEvent.CTRL_DOWN_MASK) == 0 && (mod & InputEvent.ALT_DOWN_MASK) != 0 &&
      !Debug.ALT_KEY_PRESSED_DISABLED ||
    (mod & InputEvent.META_DOWN_MASK) != 0
  }

  def command_modifier(evt: InputEvent): Boolean =
    (evt.getModifiersEx & Toolkit.getDefaultToolkit.getMenuShortcutKeyMaskEx) != 0

  def shift_modifier(evt: InputEvent): Boolean =
    (evt.getModifiersEx & InputEvent.SHIFT_DOWN_MASK) != 0

  def alt_modifier(evt: InputEvent): Boolean =
    (evt.getModifiersEx & InputEvent.ALT_DOWN_MASK) != 0

  def modifier_string(evt: InputEvent): String =
    KeyEventTranslator.getModifierString(evt) match {
      case null => ""
      case s => s
    }
}
