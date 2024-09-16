/*  Title:      Pure/Tools/check_keywords.scala
    Author:     Makarius

Check theory sources for conflicts with proposed keywords.
*/

package isabelle


object Check_Keywords {
  def conflicts(
    keywords: Keyword.Keywords,
    check: Set[String],
    input: CharSequence,
    start: Token.Pos
  ): List[(Token, Position.T)] = {
    object Parsers extends Parse.Parsers {
      private val conflict =
        position(token("token", tok => !(tok.is_command || tok.is_keyword) && check(tok.source)))
      private val other = token("token", _ => true)
      private val item = conflict ^^ (x => Some(x)) | other ^^ (_ => None)

      val result: List[(Token, Position.T)] =
        parse_all(rep(item), Token.reader(Token.explode(keywords, input), start)) match {
          case Success(res, _) => for (case Some(x) <- res) yield x
          case bad => error(bad.toString)
        }
    }
    Parsers.result
  }

  def check_keywords(
    progress: Progress,
    keywords: Keyword.Keywords,
    check: Set[String],
    paths: List[Path]
  ): Unit = {
    val parallel_args =
      paths.map(path => (File.read(path), Token.Pos.file(File.standard_path(path))))

    val bad =
      Par_List.map({ (arg: (String, Token.Pos)) =>
        progress.expose_interrupt()
        conflicts(keywords, check, arg._1, arg._2)
      }, parallel_args).flatten

    for ((tok, pos) <- bad) {
      progress.echo_warning(
        "keyword conflict: " + tok.kind.toString + " " + quote(tok.content) + Position.here(pos))
    }
  }
}
