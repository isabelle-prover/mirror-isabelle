/*  Title:      Pure/PIDE/command.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Prover commands with accumulated results from execution.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Command {
  /* blobs */

  sealed case class Blob(
    command_offset: Symbol.Offset,
    name: Document.Node.Name,
    src_path: Path,
    content: Option[(SHA1.Digest, Symbol.Text_Chunk)]
  ) {
    def chunk_file: Symbol.Text_Chunk.File =
      Symbol.Text_Chunk.File(name.node)
  }

  object Blobs_Info {
    val empty: Blobs_Info = Blobs_Info(Nil)

    def make(blobs: List[(Blob, Document.Blobs.Item)]): Blobs_Info =
      if (blobs.isEmpty) empty else Blobs_Info(for ((a, _) <- blobs) yield Exn.Res(a))

    def errors(msgs: List[String]): Blobs_Info =
      Blobs_Info(msgs.map(msg => Exn.Exn[Blob](ERROR(msg))))
  }

  sealed case class Blobs_Info(blobs: List[Exn.Result[Blob]], index: Int = -1)



  /** accumulated results from prover **/

  /* results */

  object Results {
    type Entry = (Long, XML.Elem)
    val empty: Results = new Results(SortedMap.empty)
    def make(args: IterableOnce[Results.Entry]): Results =
      args.iterator.foldLeft(empty)(_ + _)
    def merge(args: IterableOnce[Results]): Results =
      args.iterator.foldLeft(empty)(_ ++ _)

    def warned(entry: Entry): Boolean = Protocol.is_warning_or_legacy(entry._2)
    def failed(entry: Entry): Boolean = Protocol.is_error(entry._2)
  }

  final class Results private(private val rep: SortedMap[Long, XML.Elem]) {
    def is_empty: Boolean = rep.isEmpty
    def defined(serial: Long): Boolean = rep.isDefinedAt(serial)
    def get(serial: Long): Option[XML.Elem] = rep.get(serial)
    def iterator: Iterator[Results.Entry] = rep.iterator

    def warned: Boolean = rep.exists(Results.warned)
    def failed: Boolean = rep.exists(Results.failed)

    def + (entry: Results.Entry): Results =
      if (defined(entry._1)) this
      else new Results(rep + entry)

    def ++ (other: Results): Results =
      if (this eq other) this
      else if (rep.isEmpty) other
      else other.iterator.foldLeft(this)(_ + _)

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Results => rep == other.rep
        case _ => false
      }
    override def toString: String = iterator.mkString("Results(", ", ", ")")
  }


  /* exports */

  object Exports {
    type Entry = (Long, Export.Entry)
    val empty: Exports = new Exports(SortedMap.empty)
    def merge(args: IterableOnce[Exports]): Exports =
      args.iterator.foldLeft(empty)(_ ++ _)
  }

  final class Exports private(private val rep: SortedMap[Long, Export.Entry]) {
    def is_empty: Boolean = rep.isEmpty
    def iterator: Iterator[Exports.Entry] = rep.iterator

    def + (entry: Exports.Entry): Exports =
      if (rep.isDefinedAt(entry._1)) this
      else new Exports(rep + entry)

    def ++ (other: Exports): Exports =
      if (this eq other) this
      else if (rep.isEmpty) other
      else other.iterator.foldLeft(this)(_ + _)

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Exports => rep == other.rep
        case _ => false
      }
    override def toString: String = iterator.mkString("Exports(", ", ", ")")
  }


  /* markups */

  object Markup_Index {
    val markup: Markup_Index = Markup_Index(false, Symbol.Text_Chunk.Default)
    def blob(blob: Blob): Markup_Index = Markup_Index(false, blob.chunk_file)
    def make(blobs: List[Blob]): List[Markup_Index] = markup :: blobs.map(blob)
  }

  sealed case class Markup_Index(status: Boolean, chunk_name: Symbol.Text_Chunk.Name)

  object Markups {
    type Entry = (Markup_Index, Markup_Tree)
    val empty: Markups = new Markups(Map.empty)
    def init(markup: Markup_Tree): Markups = new Markups(Map(Markup_Index.markup -> markup))
    def make(args: IterableOnce[Entry]): Markups =
      args.iterator.foldLeft(empty)(_ + _)
    def merge(args: IterableOnce[Markups]): Markups =
      args.iterator.foldLeft(empty)(_ ++ _)
  }

  final class Markups private(private val rep: Map[Markup_Index, Markup_Tree]) {
    def is_empty: Boolean = rep.isEmpty

    def apply(index: Markup_Index): Markup_Tree =
      rep.getOrElse(index, Markup_Tree.empty)

    def add(markup: Text.Markup): Markups = add(Markup_Index.markup, markup)

    def add(index: Markup_Index, markup: Text.Markup): Markups =
      new Markups(rep + (index -> (this(index) + markup)))

    def + (entry: Markups.Entry): Markups = {
      val (index, tree) = entry
      new Markups(rep + (index -> (this(index).merge(tree, Text.Range.full, Markup.Elements.full))))
    }

    def ++ (other: Markups): Markups =
      if (this eq other) this
      else if (rep.isEmpty) other
      else other.rep.iterator.foldLeft(this)(_ + _)

    def redirection_iterator: Iterator[Document_ID.Generic] =
      for (case Markup_Index(_, Symbol.Text_Chunk.Id(id)) <- rep.keysIterator)
        yield id

    def redirect(other_id: Document_ID.Generic): Markups = {
      val rep1 =
        (for {
          case (Markup_Index(status, Symbol.Text_Chunk.Id(id)), markup) <- rep.iterator
          if other_id == id
        } yield (Markup_Index(status, Symbol.Text_Chunk.Default), markup)).toMap
      if (rep1.isEmpty) Markups.empty else new Markups(rep1)
    }

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Markups => rep == other.rep
        case _ => false
      }
    override def toString: String = rep.iterator.mkString("Markups(", ", ", ")")
  }


  /* state */

  object State {
    def get_result(states: List[State], serial: Long): Option[XML.Elem] =
      states.find(st => st.results.defined(serial)).map(st => st.results.get(serial).get)

    def get_result_proper(states: List[State], props: Properties.T): Option[Results.Entry] =
      for {
        serial <- Markup.Serial.unapply(props)
        elem <- get_result(states, serial)
        if elem.body.nonEmpty
      } yield serial -> elem

    def merge_results(states: List[State]): Results =
      Results.merge(states.map(_.results))

    def merge_exports(states: List[State]): Exports =
      Exports.merge(states.map(_.exports))

    def merge_markups(states: List[State]): Markups =
      Markups.merge(states.map(_.markups))

    def merge_markup(states: List[State], index: Markup_Index,
        range: Text.Range, elements: Markup.Elements): Markup_Tree =
      Markup_Tree.merge(states.map(_.markup(index)), range, elements)

    def merge(command: Command, states: List[State]): State =
      State(command,
        results = merge_results(states),
        exports = merge_exports(states),
        markups = merge_markups(states))

    def apply(
      command: Command,
      results: Results = Results.empty,
      exports: Exports = Exports.empty,
      markups: Markups = Markups.empty
    ): State = {
      new State(command, results, exports, markups,
        Document_Status.Command_Status.make(warned = results.warned, failed = results.failed))
    }
  }

  final class State private(
    val command: Command,
    val results: Results,
    val exports: Exports,
    val markups: Markups,
    val document_status: Document_Status.Command_Status
  ) {
    override def toString: String = "Command.State(" + command + ")"
    override def hashCode(): Int = ???
    override def equals(obj: Any): Boolean = ???

    def initialized: Boolean = document_status.initialized
    def consolidating: Boolean = document_status.consolidating
    def consolidated: Boolean = document_status.consolidated
    def maybe_consolidated: Boolean = document_status.maybe_consolidated
    def timings: Document_Status.Command_Timings = document_status.timings

    def markup(index: Markup_Index): Markup_Tree = markups(index)

    def redirect(other_command: Command): Option[State] = {
      val markups1 = markups.redirect(other_command.id)
      if (markups1.is_empty) None
      else Some(State(other_command, markups = markups1))
    }

    private def add_status(st: Markup): State = {
      val document_status1 = document_status.update(markups = List(st))
      new State(command, results, exports, markups, document_status1)
    }

    private def add_result(entry: Results.Entry): State = {
      val document_status1 =
        document_status.update(
          warned = Results.warned(entry),
          failed = Results.failed(entry))
      new State(command, results + entry, exports, markups, document_status1)
    }

    def add_export(entry: Exports.Entry): Option[State] =
      if (command.node_name.theory == entry._2.theory_name) {
        Some(new State(command, results, exports + entry, markups, document_status))
      }
      else None

    private def add_markup(
      m: Text.Markup,
      chunk_name: Symbol.Text_Chunk.Name = Symbol.Text_Chunk.Default,
      status: Boolean = false
    ): State = {
      val markups1 =
        if (status || Document_Status.Command_Status.liberal_elements(m.info.name))
          markups.add(Markup_Index(true, chunk_name), m)
        else markups
      val markups2 = markups1.add(Markup_Index(false, chunk_name), m)
      new State(command, results, exports, markups2, document_status)
    }

    def accumulate(
        self_id: Document_ID.Generic => Boolean,
        other_id: (Document.Node.Name, Document_ID.Generic) =>
          Option[(Symbol.Text_Chunk.Id, Symbol.Text_Chunk)],
        message: XML.Elem,
        cache: XML.Cache): State =
      message match {
        case XML.Elem(Markup(Markup.STATUS, _), msgs) =>
          if (command.span.is_theory) this
          else {
            msgs.foldLeft(this) {
              case (state, msg) =>
                msg match {
                  case elem @ XML.Elem(markup, Nil) =>
                    state.
                      add_status(markup).
                      add_markup(Text.Info(command.core_range, elem), status = true)
                  case _ =>
                    Output.warning("Ignored status message: " + msg)
                    state
                }
            }
          }

        case XML.Elem(Markup(Markup.REPORT, atts0), msgs) =>
          msgs.foldLeft(this) {
            case (state, msg) =>
              def bad(): Unit = Output.warning("Ignored report message: " + msg)

              msg match {
                case XML.Elem(Markup(name, atts), args) =>
                  command.reported_position(atts) orElse command.reported_position(atts0) match {
                    case Some((id, chunk_name, target_range)) =>
                      val target =
                        if (self_id(id) && command.chunks.isDefinedAt(chunk_name))
                          Some((chunk_name, command.chunks(chunk_name)))
                        else if (chunk_name == Symbol.Text_Chunk.Default)
                          other_id(command.node_name, id)
                        else None

                      (target, target_range) match {
                        case (Some((target_name, target_chunk)), Some(symbol_range))
                        if !symbol_range.is_singularity =>
                          target_chunk.incorporate(symbol_range) match {
                            case Some(range) =>
                              val props = atts.filterNot(Markup.position_property)
                              val elem = cache.elem(XML.Elem(Markup(name, props), args))
                              state.add_markup(Text.Info(range, elem), chunk_name = target_name)
                            case None => bad(); state
                          }
                        case _ =>
                          // silently ignore excessive reports
                          state
                      }

                    case _ => bad(); state
                  }
                case _ => bad(); state
              }
          }

        case XML.Elem(Markup(name, props), body) =>
          props match {
            case Markup.Serial(i) =>
              val markup_message = cache.elem(Protocol.make_message(body, name, props = props))
              val message_markup = cache.elem(XML.elem(Markup(name, Markup.Serial(i))))

              var st = add_result(i -> markup_message)
              if (Protocol.is_inlined(message)) {
                for {
                  (chunk_name, chunk) <- command.chunks.iterator
                  range <- command.message_positions(self_id, chunk_name, chunk, message)
                } st = st.add_markup(Text.Info(range, message_markup), chunk_name = chunk_name)
              }
              st

            case _ =>
              Output.warning("Ignored message without serial number: " + message)
              this
          }
      }
  }



  /** static content **/

  /* make commands */

  def apply(
    id: Document_ID.Command,
    node_name: Document.Node.Name,
    blobs_info: Blobs_Info,
    span: Command_Span.Span
  ): Command = {
    val (source, span1) = span.compact_source
    new Command(id, node_name, blobs_info, span1, source, Results.empty, Markups.empty)
  }

  val empty: Command =
    Command(Document_ID.none, Document.Node.Name.empty, Blobs_Info.empty, Command_Span.empty)

  def unparsed(
    source: String,
    theory: Boolean = false,
    id: Document_ID.Command = Document_ID.none,
    node_name: Document.Node.Name = Document.Node.Name.empty,
    blobs_info: Blobs_Info = Blobs_Info.empty,
    results: Results = Results.empty,
    markups: Markups = Markups.empty
  ): Command = {
    val span = Command_Span.unparsed(source, theory = theory)
    new Command(id, node_name, blobs_info, span, source, results, markups)
  }


  /* edits and perspective */

  type Edit = (Option[Command], Option[Command])

  object Perspective {
    val empty: Perspective = Perspective(Nil)
  }

  sealed case class Perspective(
    commands: List[Command]  // visible commands in canonical order
  ) {
    def is_empty: Boolean = commands.isEmpty

    def same(that: Perspective): Boolean = {
      val cmds1 = this.commands
      val cmds2 = that.commands
      require(!cmds1.exists(_.is_undefined), "cmds1 not defined")
      require(!cmds2.exists(_.is_undefined), "cmds2 not defined")
      cmds1.length == cmds2.length &&
        (cmds1.iterator zip cmds2.iterator).forall({ case (c1, c2) => c1.id == c2.id })
    }
  }


  /* blobs: inlined errors and auxiliary files */

  def blobs_info(
    resources: Resources,
    syntax: Outer_Syntax,
    get_blob: Document.Node.Name => Option[Document.Blobs.Item],
    can_import: Document.Node.Name => Boolean,
    node_name: Document.Node.Name,
    span: Command_Span.Span
  ): Blobs_Info = {
    span.name match {
      // inlined errors
      case Thy_Header.THEORY =>
        val reader = span.content_reader
        val header = resources.check_thy(node_name, span.content_reader)
        val imports_pos = header.imports_pos
        val raw_imports =
          try {
            val read_imports = Thy_Header.read(node_name, reader).imports.map(_._1)
            if (imports_pos.length == read_imports.length) read_imports else error("")
          }
          catch { case _: Throwable => List.fill(header.imports.length)("") }

        val errors =
          for { ((import_name, pos), s) <- imports_pos zip raw_imports if !can_import(import_name) }
          yield {
            val completion =
              if (Url.is_base_name(s)) resources.complete_import_name(node_name, s) else Nil
            "Bad theory import " +
              Markup.Path(import_name.node).markup(quote(import_name.toString)) +
              Position.here(pos) + Completion.report_theories(pos, completion)
          }
        Blobs_Info.errors(errors)

      // auxiliary files
      case _ =>
        val loaded_files = span.loaded_files(syntax)
        val blobs =
          loaded_files.files.map(file =>
            (Exn.capture {
              val src_path = Path.explode(file)
              val name = Document.Node.Name(resources.append_path(node_name.master_dir, src_path))
              val content = get_blob(name).map(blob => (blob.bytes.sha1_digest, blob.chunk))
              Blob(0, name, src_path, content)
            }).user_error)
        Blobs_Info(blobs, index = loaded_files.index)
    }
  }
}


final class Command private(
  val id: Document_ID.Command,
  val node_name: Document.Node.Name,
  val blobs_info: Command.Blobs_Info,
  val span: Command_Span.Span,
  val source: String,
  val init_results: Command.Results,
  val init_markups: Command.Markups
) {
  override def toString: String = id.toString + "/" + span.kind.toString


  /* classification */

  def is_proper: Boolean = span.kind.isInstanceOf[Command_Span.Command_Span]
  def is_ignored: Boolean = span.kind == Command_Span.Ignored_Span

  def is_undefined: Boolean = id == Document_ID.none
  lazy val is_unparsed: Boolean = span.content.exists(_.is_unparsed)
  lazy val is_unfinished: Boolean = span.content.exists(_.is_unfinished)


  /* blobs */

  def blobs: List[Exn.Result[Command.Blob]] = blobs_info.blobs
  def blobs_index: Int = blobs_info.index

  def blobs_ok: Boolean = blobs.forall(Exn.is_res)

  def blobs_names: List[Document.Node.Name] =
    for (case Exn.Res(blob) <- blobs) yield blob.name

  def blobs_files: List[(Symbol.Offset, Document.Node.Name)] =
    for (case Exn.Res(blob) <- blobs) yield (blob.command_offset, blob.name)

  def blobs_undefined: List[Document.Node.Name] =
    for (case Exn.Res(blob) <- blobs if blob.content.isEmpty) yield blob.name

  def blobs_defined: List[(Document.Node.Name, SHA1.Digest)] =
    for (case Exn.Res(blob) <- blobs; (digest, _) <- blob.content) yield (blob.name, digest)

  def blobs_changed(doc_blobs: Document.Blobs): Boolean =
    blobs.exists({ case Exn.Res(blob) => doc_blobs.changed(blob.name) case _ => false })


  /* source chunks */

  lazy val chunk: Symbol.Text_Chunk = Symbol.Text_Chunk(source)

  lazy val chunks: Map[Symbol.Text_Chunk.Name, Symbol.Text_Chunk] =
    ((Symbol.Text_Chunk.Default -> chunk) ::
      (for (case Exn.Res(blob) <- blobs; (_, file) <- blob.content)
        yield blob.chunk_file -> file)).toMap

  def length: Int = source.length
  def range: Text.Range = chunk.range

  lazy val core_range: Text.Range =
    Text.Range(0,
      span.content.reverseIterator.takeWhile(_.is_ignored).foldLeft(length)(_ - _.source.length))

  def source(range: Text.Range): String = range.substring(source)


  /* theory parents */

  def theory_parents(resources: Resources): List[Document.Node.Name] =
    if (span.name == Thy_Header.THEORY) {
      try {
        val header = Thy_Header.read(node_name, span.content_reader)
        for ((s, _) <- header.imports)
        yield {
          try { resources.import_name(node_name, s) }
          catch { case ERROR(_) => Document.Node.Name.empty }
        }
      }
      catch { case ERROR(_) => Nil }
    }
    else Nil


  /* reported positions */

  def reported_position(
    pos: Position.T
  ) : Option[(Document_ID.Generic, Symbol.Text_Chunk.Name, Option[Symbol.Range])] = {
    pos match {
      case Position.Id(id) =>
        val chunk_name =
          pos match {
            case Position.File(name) if name != node_name.node =>
              Symbol.Text_Chunk.File(name)
            case _ => Symbol.Text_Chunk.Default
          }
        Some((id, chunk_name, Position.Range.unapply(pos)))
      case _ => None
    }
  }

  def message_positions(
    self_id: Document_ID.Generic => Boolean,
    chunk_name: Symbol.Text_Chunk.Name,
    chunk: Symbol.Text_Chunk,
    message: XML.Elem
  ): Set[Text.Range] = {
    def elem(props: Properties.T, set: Set[Text.Range]): Set[Text.Range] =
      reported_position(props) match {
        case Some((id, name, reported_range)) if self_id(id) && name == chunk_name =>
          val opt_range =
            reported_range orElse {
              if (name == Symbol.Text_Chunk.Default)
                Position.Range.unapply(span.position)
              else None
            }
          opt_range match {
            case Some(symbol_range) =>
              chunk.incorporate(symbol_range) match {
                case Some(range) => set + range
                case _ => set
              }
            case None => set
          }
        case _ => set
      }
    def tree(set: Set[Text.Range], t: XML.Tree): Set[Text.Range] =
      t match {
        case XML.Wrapped_Elem(Markup(name, props), _, body) =>
          body.foldLeft(if (Rendering.position_elements(name)) elem(props, set) else set)(tree)
        case XML.Elem(Markup(name, props), body) =>
          body.foldLeft(if (Rendering.position_elements(name)) elem(props, set) else set)(tree)
        case XML.Text(_) => set
      }

    val set = tree(Set.empty, message)
    if (set.isEmpty) elem(message.markup.properties, set)
    else set
  }


  /* accumulated results */

  lazy val init_state: Command.State =
    Command.State(this, results = init_results, markups = init_markups)

  lazy val empty_state: Command.State = Command.State(this)
}
