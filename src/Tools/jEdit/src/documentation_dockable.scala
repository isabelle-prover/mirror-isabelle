/*  Title:      Tools/jEdit/src/documentation_dockable.scala
    Author:     Makarius

Dockable window for Isabelle documentation.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import java.awt.event.{KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.swing.JScrollPane

import org.gjt.sp.jedit.View


class Documentation_Dockable(view: View, position: String) extends Dockable(view, position) {
  private val doc_contents = Doc.contents(PIDE.ml_settings)

  private val tree = new Tree_View(single_selection_mode = true)
  tree.getAccessibleContext.setAccessibleName("Documentation")

  for (section <- doc_contents.sections) {
    tree.root.add(Tree_View.Node(section.title))
    val last_node = tree.root.getLastChild.asInstanceOf[Tree_View.Node]
    for (entry <- section.entries) last_node.add(Tree_View.Node(entry))
  }

  override def focusOnDefaultComponent(): Unit = tree.requestFocusInWindow

  private def action(obj: AnyRef): Unit = {
    obj match {
      case Tree_View.Node(entry: Doc.Entry) =>
        if (entry.path.is_pdf) PIDE.editor.goto_doc(view, entry.path)
        else PIDE.editor.goto_file(true, view, File.platform_path(entry.path))
      case _ =>
    }
  }

  tree.addKeyListener(new KeyAdapter {
    override def keyPressed(e: KeyEvent): Unit = {
      if (e.getKeyCode == KeyEvent.VK_ENTER) {
        e.consume()
        val path = tree.getSelectionPath
        if (path != null) action(path.getLastPathComponent)
      }
    }
  })
  tree.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent): Unit = {
      if (!e.isConsumed()) {
        val click = tree.getPathForLocation(e.getX, e.getY)
        if (click != null && e.getClickCount == 1) {
          val click_node = click.getLastPathComponent
          val path_node = tree.getLastSelectedPathComponent
          if (click_node == path_node) {
            e.consume()
            action(click_node)
          }
        }
      }
    }
  })

  {
    var expand = true
    var visible = 0
    var row = 0
    def make_visible(): Unit = { visible += 1; tree.expandRow(row) }
    for (section <- doc_contents.sections) {
      expand = section.important
      make_visible()
      row += 1
      for (_ <- section.entries) {
        if (expand) make_visible()
        row += 1
      }
    }
    tree.setRootVisible(false)
    tree.setVisibleRowCount(visible)
  }

  private val tree_scroller = new JScrollPane(tree)
  tree_scroller.setMinimumSize(new Dimension(200, 50))

  set_content(tree_scroller)
}
