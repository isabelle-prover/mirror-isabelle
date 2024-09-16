/*  Title:      Pure/Admin/build_doc.scala
    Author:     Makarius

Build Isabelle documentation.
*/

package isabelle


object Build_Doc {
  /* build_doc */

  def build_doc(
    options: Options,
    progress: Progress = new Progress,
    all_docs: Boolean = false,
    max_jobs: Option[Int] = None,
    sequential: Boolean = false,
    docs: List[String] = Nil,
    view: Boolean = false
  ): Unit = {
    val sessions_structure = Sessions.load_structure(options)
    val selected =
      for {
        session <- sessions_structure.build_topological_order
        info = sessions_structure(session)
        if info.groups.contains("doc")
        doc = info.options.string("document_variants")
        if all_docs || docs.contains(doc)
      } yield (doc, session)

    val documents = selected.map(_._1)
    val selection = Sessions.Selection(sessions = selected.map(_._2))

    docs.filter(doc => !documents.contains(doc)) match {
      case Nil =>
      case bad => error("No documentation session for " + commas_quote(bad))
    }

    progress.echo("Build started for sessions " + commas_quote(selection.sessions))
    val build_results =
      Build.build(options, selection = selection, progress = progress, max_jobs = max_jobs)
    if (!build_results.ok) error("Build failed")

    progress.echo("Build started for documentation " + commas_quote(documents))
    val deps = Sessions.load_structure(options + "document").selection_deps(selection)

    val errs =
      Par_List.maps[(String, String), String](
      {
        case (doc, session) =>
          try {
            progress.expose_interrupt()
            progress.echo("Documentation " + quote(doc) + " ...")

            using(Export.open_session_context(build_results.store, deps.background(session))) {
              session_context =>
                Document_Build.build_documents(
                  Document_Build.context(session_context),
                  output_pdf = Some(Path.explode("~~/doc")))
            }
            None
          }
          catch {
            case Exn.Interrupt.ERROR(msg) =>
              val sep = if (msg.contains('\n')) "\n" else " "
              Some("Documentation " + quote(doc) + " failed:" + sep + msg)
          }
      }, selected, sequential = sequential)

    if (errs.nonEmpty) error(cat_lines(errs))

    if (view) {
      for (doc <- Doc.main_contents().docs if docs.contains(doc.name)) {
        Doc.view(doc.path)
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_doc", "build Isabelle documentation", Scala_Project.here,
      { args =>
        var view = false
        var all_docs = false
        var max_jobs: Option[Int] = None
        var sequential = false
        var options = Options.init()

        val getopts =
          Getopts("""
Usage: isabelle build_doc [OPTIONS] [DOCS ...]

  Options are:
    -V           view explicitly given documents
    -a           select all documentation sessions
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           sequential LaTeX jobs

  Build Isabelle documentation from documentation sessions with
  suitable document_variants entry.
""",
            "V" -> (_ => view = true),
            "a" -> (_ => all_docs = true),
            "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
            "o:" -> (arg => options = options + arg),
            "s" -> (_ => sequential = true))

        val docs = getopts(args)

        if (!all_docs && docs.isEmpty) getopts.usage()

        val progress = new Console_Progress()

        progress.interrupt_handler {
          build_doc(options, progress = progress, all_docs = all_docs, max_jobs = max_jobs,
            sequential = sequential, docs = docs, view = view)
        }
      })
}
