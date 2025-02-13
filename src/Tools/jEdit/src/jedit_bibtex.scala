/*  Title:      Tools/jEdit/src/jedit_bibtex.scala
    Author:     Makarius

BibTeX support in Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


import java.awt.event.{ActionListener, ActionEvent}

import javax.swing.text.Segment
import javax.swing.{JMenu, JMenuItem}

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.syntax.{Token => JEditToken, TokenMarker, TokenHandler}


object JEdit_Bibtex {
  /** context menu **/

  def context_menu(text_area: JEditTextArea): List[JMenuItem] = {
    text_area.getBuffer match {
      case buffer: Buffer
      if File.is_bib(JEdit_Lib.buffer_name(buffer)) && buffer.isEditable =>
        val menu = new JMenu("BibTeX entries")
        for (entry_type <- Bibtex.known_entries) {
          val item = new JMenuItem(entry_type.kind)
          item.addActionListener(new ActionListener {
            def actionPerformed(evt: ActionEvent): Unit =
              Isabelle.insert_line_padding(text_area, entry_type.template)
          })
          menu.add(item)
        }
        List(menu)
      case _ => Nil
    }
  }



  /** token markup **/

  /* token style */

  private def token_style(context: String, token: Bibtex.Token): Byte =
    token.kind match {
      case Bibtex.Token.Kind.COMMAND => JEditToken.KEYWORD2
      case Bibtex.Token.Kind.ENTRY => JEditToken.KEYWORD1
      case Bibtex.Token.Kind.KEYWORD => JEditToken.OPERATOR
      case Bibtex.Token.Kind.NAT => JEditToken.LITERAL2
      case Bibtex.Token.Kind.STRING => JEditToken.LITERAL1
      case Bibtex.Token.Kind.NAME => JEditToken.LABEL
      case Bibtex.Token.Kind.IDENT =>
        if (Bibtex.is_month(token.source)) JEditToken.LITERAL3
        else
          Bibtex.known_entry(context) match {
            case Some(entry_type) if entry_type.is_required(token.source) => JEditToken.KEYWORD3
            case Some(entry_type) if entry_type.is_optional(token.source) => JEditToken.KEYWORD4
            case _ => JEditToken.DIGIT
          }
      case Bibtex.Token.Kind.SPACE => JEditToken.NULL
      case Bibtex.Token.Kind.COMMENT => JEditToken.COMMENT1
      case Bibtex.Token.Kind.ERROR => JEditToken.INVALID
    }


  /* line context */

  private val mode_rule_set = Token_Markup.mode_rule_set("bibtex")

  private class Line_Context(val context: Option[Bibtex.Line_Context])
  extends TokenMarker.LineContext(mode_rule_set, null) {
    override def hashCode: Int = context.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Line_Context => context == other.context
        case _ => false
      }
  }


  /* token marker */

  class Token_Marker extends TokenMarker {
    addRuleSet(mode_rule_set)

    override def markTokens(
      context: TokenMarker.LineContext,
      handler: TokenHandler,
      raw_line: Segment
    ): TokenMarker.LineContext = {
      val line_ctxt =
        context match {
          case c: Line_Context => c.context
          case _ => Some(Bibtex.Ignored)
        }
      val line = if (raw_line == null) new Segment else raw_line

      def no_markup = {
        val styled_token = (JEditToken.NULL, line.subSequence(0, line.count).toString)
        (List(styled_token), new Line_Context(None))
      }

      val context1 = {
        val (styled_tokens, context1) =
          line_ctxt match {
            case Some(ctxt) =>
              try {
                val (chunks, ctxt1) = Bibtex.parse_line(line, ctxt)
                val styled_tokens =
                  for { chunk <- chunks; tok <- chunk.tokens }
                  yield (token_style(chunk.kind, tok), tok.source)
                (styled_tokens, new Line_Context(Some(ctxt1)))
              }
              catch { case ERROR(msg) => Output.warning(msg); no_markup }
            case None => no_markup
          }

        var offset = 0
        for ((style, token) <- styled_tokens) {
          val length = token.length
          val end_offset = offset + length

          if ((offset until end_offset).exists(i => line.charAt(i) == '\t')) {
            for (i <- offset until end_offset)
              handler.handleToken(line, style, i, 1, context1)
          }
          else handler.handleToken(line, style, offset, length, context1)

          offset += length
        }
        handler.handleToken(line, JEditToken.END, line.count, 0, context1)
        context1
      }
      val context2 = context1.intern
      handler.setLineContext(context2)
      context2
    }
  }
}
