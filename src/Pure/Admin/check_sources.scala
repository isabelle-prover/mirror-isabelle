/*  Title:      Pure/Admin/check_sources.scala
    Author:     Makarius

Some sanity checks for Isabelle sources.
*/

package isabelle


object Check_Sources {
  def check_file(path: Path): Unit = {
    val file_name = path.implode
    val file_pos = Position.File(File.symbolic_path(path))
    def line_pos(i: Int) = Position.Line_File(i + 1, file_name)

    if (space_explode('/', Word.lowercase(path.expand.drop_ext.implode)).contains("aux"))
      Output.warning("Illegal file-name on Windows" + Position.here(file_pos))

    val bytes = Bytes.read(path)
    val content = bytes.text

    if (Bytes(content) != bytes) {
      Output.warning("Bad UTF8 encoding" + Position.here(file_pos))
    }

    for { (line, i) <- split_lines(content).iterator.zipWithIndex } {
      try {
        Symbol.decode_strict(line)

        for { c <- Codepoint.iterator(line); if c > 128 && !Character.isAlphabetic(c) } {
          Output.warning("Suspicious Unicode character " + quote(Codepoint.string(c)) +
            Position.here(line_pos(i)))
        }
      }
      catch { case ERROR(msg) => Output.warning(msg + Position.here(line_pos(i))) }

      if (line.contains('\t'))
        Output.warning("TAB character" + Position.here(line_pos(i)))
    }

    if (content.contains('\r'))
      Output.warning("CR character" + Position.here(file_pos))

    if (Word.bidi_detect(content))
      Output.warning("Bidirectional Unicode text" + Position.here(file_pos))
  }

  def check_hg(root: Path): Unit = {
    Output.writeln("Checking " + root + " ...")
    val hg = Mercurial.repository(root)
    for {
      file <- hg.known_files()
      if File.is_scala(file) || File.is_thy(file) || File.is_ML(file) || file.endsWith("/ROOT")
    } check_file(root + Path.explode(file))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("check_sources", "some sanity checks for Isabelle sources",
      Scala_Project.here,
      { args =>
        val getopts = Getopts("""
Usage: isabelle check_sources [ROOT_DIRS...]

  Check .scala, .thy, .ML, ROOT against known files of Mercurial ROOT_DIRS.
""")

        val specs = getopts(args)
        if (specs.isEmpty) getopts.usage()

        for (root <- specs) check_hg(Path.explode(root))
      })
}
