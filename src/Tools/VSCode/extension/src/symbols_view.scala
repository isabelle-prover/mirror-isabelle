/*  Title:      Tools/VSCode/extension/symbols_view.scala
    Author:     Fabian Huch

Isabelle symbols view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import isabelle._


object Symbols_View {
  private val vscode = Webview_Api.acquire


  /* gui state */

  object State {
    def apply(tab: Int): JSON.Object.T = JSON.Object("active_tab" -> tab)
    def unapply(json: JSON.Object.T): Option[Int] = JSON.int(json, "active_tab")
  }

  private var abbrevs: Thy_Header.Abbrevs = Nil
  private var search_input: String = ""
  private var active_tab: Int = (for { case State(tab) <- vscode.get_state } yield tab).getOrElse(0)


  /* abbrevs */

  private def abbrev_elem(txt: String, abbrs: List[String]) = {
    def drop_caret(s: String): String = s.replacing(Completion.caret_indicator.toString -> "")

    val symbol = Symbol.decode(txt)
    val msg = JSON.Object("command" -> "insert_symbol", "symbol" -> drop_caret(symbol))
    val tooltip =
      cat_lines(drop_caret(txt) :: abbrs.filterNot(_ == "").sorted.map(a => "abbrev: " + a))

    HTML.class_("symbol-button")(
      HTML.GUI.button(HTML.text(symbol), tooltip = tooltip, script =
        Webview_Api.Post.function(JSON.Format(msg))))
  }

  private def abbrev_panel: XML.Body = {
    val entries: List[(String, List[String])] =
      Multi_Map(
        (for {
          (abbr, txt0) <- abbrevs
          txt = Symbol.encode(txt0)
          if !Symbol.iterator(txt).forall(s => s.length == 1 && s(0) != Completion.caret_indicator)
        } yield (txt, abbr)): _*).iterator_list.toList
    entries.map(abbrev_elem.tupled)
  }


  /* symbols */

  private def symbol_elem(symbol: String): XML.Elem =
    abbrev_elem(symbol, Symbol.symbols.get_abbrevs(symbol))

  private val reset_elem: XML.Elem =
    HTML.class_("reset-button")(
      HTML.GUI.button(HTML.text("Reset"),
        tooltip = "Reset control symbols within text",
        script = Webview_Api.Post.function(JSON.Format(JSON.Object("command" -> "reset_control")))))


  /* search */

  object search_changed extends Scalajs.Fun[String] {
    def apply(input: String): Unit = {
      search_input = input
      update()
    }
  }

  private val search_space =
    for (entry <- Symbol.symbols.entries if entry.code.isDefined)
    yield entry.symbol -> Word.lowercase(entry.symbol)

  private def search_panel: XML.Body = {
    val search_field = 
      HTML.GUI.text_field(columns = 10, text = search_input, name = "search-input", script =
        search_changed.function("this.value"))

    val search_words = Word.explode(Word.lowercase(search_input))
    val search_limit = 50
    val results =
      if (search_words.isEmpty) Nil
      else
        for ((sym, s) <- search_space; if search_words.forall(s.contains(_))) yield symbol_elem(sym)

    val more_results =
      if (results.length <= search_limit) Nil
      else HTML.text("(" + (results.length - search_limit) + " more ...)")

    val search_results = HTML.div("search-results", results.take(50) ::: more_results)

    List(HTML.div("search-container", List(search_field, search_results)))
  }


  /* tabs */

  object tab_clicked extends Scalajs.Fun[Int] {
    def apply(tab: Int): Unit = {
      active_tab = tab
      vscode.set_state(Some(State(active_tab)))
      update()
    }
  }

  private class Tab(name: String, content: XML.Body, tooltip: String = "") {
    def title: String = Word.implode(Word.explode('_', name).map(Word.perhaps_capitalized))

    def button(index: Int): XML.Elem =
      HTML.class_(if_proper(index == active_tab, "active ") + "tab")(
        HTML.GUI.button(HTML.text(title), tooltip = tooltip, script =
          tab_clicked.function(JS.value(index))))

    def panel(index: Int): XML.Elem =
      HTML.div(if_proper(index != active_tab, "hidden ") + "tab-content", content)
  }

  private def group_tabs: XML.Body = {
    val abbrevs_tab = new Tab("abbrevs", abbrev_panel)

    val symbols_tabs =
      Symbol.symbols.groups_code.map({ case (group, symbols) =>
        val control = group == "control"
        new Tab(group, symbols.map(symbol_elem) ::: (if (control) List(reset_elem) else Nil))
      })

    val search_tab = new Tab("search", search_panel, "Search Symbols")

    val tabs = (abbrevs_tab :: symbols_tabs ::: search_tab :: Nil).zipWithIndex

    List(
      HTML.div("tabs", for ((tab, i) <- tabs) yield tab.button(i)),
      HTML.div("content", for ((tab, i) <- tabs) yield tab.panel(i)))
  }


  /* main */

  def update(): Unit = Scalajs.DOM.update(HTML.control_markup(group_tabs, hidden = true))

  def main(): Unit = {
    Webview_Api.on_message { e =>
      val json = Scalajs.JSON.unapply(e.data).get

      abbrevs =
        for {
          abbrevs <-
            JSON.list(json, "abbrevs", JSON.Value.List.unapply(_, JSON.Value.String.unapply)).toList
          case txt :: abbr :: Nil <- abbrevs
        } yield (txt, abbr)

      update()
    }

    vscode.post(JSON.Object("command" -> "ready"))
    update()
  }
}
