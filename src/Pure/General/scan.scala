/*  Title:      Pure/General/scan.scala
    Author:     Makarius

Efficient scanning of keywords and tokens.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.IndexedSeq
import scala.util.matching.Regex
import scala.util.parsing.input.{OffsetPosition, Position => InputPosition,
  Reader, CharSequenceReader, PagedSeq}
import scala.util.parsing.combinator.RegexParsers
import java.io.{File => JFile, BufferedInputStream, FileInputStream, InputStream}


object Scan {
  /** context of partial line-oriented scans **/

  abstract class Line_Context
  case object Finished extends Line_Context
  case class Quoted(quote: String) extends Line_Context
  case class Cartouche(depth: Int) extends Line_Context
  case class Comment_Prefix(symbol: Symbol.Symbol) extends Line_Context
  case class Cartouche_Comment(depth: Int) extends Line_Context
  case class Comment(depth: Int) extends Line_Context



  /** parser combinators **/

  object Parsers extends Parsers

  trait Parsers extends RegexParsers {
    override val whiteSpace: Regex = "".r


    /* optional termination */

    def opt_term[T](p: => Parser[T]): Parser[Option[T]] =
      p ^^ (x => Some(x)) | """\z""".r ^^ (_ => None)


    /* repeated symbols */

    def repeated(pred: Symbol.Symbol => Boolean, min_count: Int, max_count: Int): Parser[String] =
      new Parser[String] {
        def apply(in: Input) = {
          val start = in.offset
          val end = in.source.length
          val matcher = new Symbol.Matcher(in.source)

          var i = start
          var count = 0
          var finished = false
          while (!finished && i < end && count < max_count) {
            val sym = matcher.match_symbol(i)
            if (pred(sym)) { i += sym.length; count += 1 }
            else finished = true
          }
          if (count < min_count) Failure("bad input", in)
          else Success(in.source.subSequence(start, i).toString, in.drop(i - start))
        }
      }.named("repeated")

    def one(pred: Symbol.Symbol => Boolean): Parser[String] =
      repeated(pred, 1, 1)

    def maybe(pred: Symbol.Symbol => Boolean): Parser[String] =
      repeated(pred, 0, 1)

    def many(pred: Symbol.Symbol => Boolean): Parser[String] =
      repeated(pred, 0, Int.MaxValue)

    def many1(pred: Symbol.Symbol => Boolean): Parser[String] =
      repeated(pred, 1, Int.MaxValue)


    /* character */

    def character(pred: Char => Boolean): Symbol.Symbol => Boolean =
      (s: Symbol. Symbol) => s.length == 1 && pred(s.charAt(0))


    /* quoted strings */

    private def quoted_body(quote: Symbol.Symbol): Parser[String] = {
      rep(many1(sym => sym != quote && sym != "\\") | "\\" + quote | "\\\\" |
        ("""\\\d\d\d""".r ^? { case x if x.substring(1, 4).toInt <= 255 => x })) ^^ (_.mkString)
    }

    def quoted(quote: Symbol.Symbol): Parser[String] = {
      quote ~ quoted_body(quote) ~ quote ^^ { case x ~ y ~ z => x + y + z }
    }.named("quoted")

    def quoted_content(quote: Symbol.Symbol, source: String): String = {
      require(parseAll(quoted(quote), source).successful, "no quoted text")
      val body = source.substring(1, source.length - 1)
      if (body.exists(_ == '\\')) {
        val content =
          rep(many1(sym => sym != quote && sym != "\\") |
              "\\" ~> (quote | "\\" | """\d\d\d""".r ^^ { case x => x.toInt.toChar.toString }))
        parseAll(content ^^ (_.mkString), body).get
      }
      else body
    }

    def quoted_line(quote: Symbol.Symbol, ctxt: Line_Context): Parser[(String, Line_Context)] = {
      ctxt match {
        case Finished =>
          quote ~ quoted_body(quote) ~ opt_term(quote) ^^
            { case x ~ y ~ Some(z) => (x + y + z, Finished)
              case x ~ y ~ None => (x + y, Quoted(quote)) }
        case Quoted(q) if q == quote =>
          quoted_body(quote) ~ opt_term(quote) ^^
            { case x ~ Some(y) => (x + y, Finished)
              case x ~ None => (x, ctxt) }
        case _ => failure("")
      }
    }.named("quoted_line")

    def recover_quoted(quote: Symbol.Symbol): Parser[String] =
      quote ~ quoted_body(quote) ^^ { case x ~ y => x + y }


    /* nested text cartouches */

    def cartouche_depth(depth: Int): Parser[(String, Int)] = new Parser[(String, Int)] {
      require(depth >= 0, "bad cartouche depth")

      def apply(in: Input) = {
        val start = in.offset
        val end = in.source.length
        val matcher = new Symbol.Matcher(in.source)

        var i = start
        var d = depth
        var finished = false
        while (!finished && i < end) {
          val sym = matcher.match_symbol(i)
          val n = sym.length
          if (Symbol.is_open(sym)) { i += n; d += 1 }
          else if (Symbol.is_close(sym) && d > 0) { i += n; d -= 1; if (d == 0) finished = true }
          else if (d > 0) i += n
          else finished = true
        }
        if (i == start) Failure("bad input", in)
        else Success((in.source.subSequence(start, i).toString, d), in.drop(i - start))
      }
    }.named("cartouche_depth")

    def cartouche: Parser[String] =
      cartouche_depth(0) ^? { case (x, d) if d == 0 => x }

    def cartouche_line(ctxt: Line_Context): Parser[(String, Line_Context)] = {
      def cartouche_context(d: Int): Line_Context =
        if (d == 0) Finished else Cartouche(d)

      ctxt match {
        case Finished =>
          cartouche_depth(0) ^^ { case (c, d) => (c, cartouche_context(d)) }
        case Cartouche(depth) =>
          cartouche_depth(depth) ^^ { case (c, d) => (c, cartouche_context(d)) }
        case _ => failure("")
      }
    }

    val recover_cartouche: Parser[String] =
      cartouche_depth(0) ^^ (_._1)

    def cartouche_content(source: String): String = {
      def err(): Nothing = error("Malformed text cartouche: " + quote(source))
      val source1 =
        Library.try_unprefix(Symbol.open_decoded, source) orElse
          Library.try_unprefix(Symbol.open, source) getOrElse err()
      Library.try_unsuffix(Symbol.close_decoded, source1) orElse
        Library.try_unsuffix(Symbol.close, source1) getOrElse err()
    }


    /* nested comments */

    private def comment_depth(depth: Int): Parser[(String, Int)] = new Parser[(String, Int)] {
      require(depth >= 0, "bad comment depth")

      val comment_text: Parser[List[String]] =
        rep1(many1(sym => sym != "*" && sym != "(") | """\*(?!\))|\((?!\*)""".r)

      def apply(in: Input) = {
        var rest = in
        def try_parse[A](p: Parser[A]): Boolean = {
          parse(p ^^^ (()), rest) match {
            case Success(_, next) => { rest = next; true }
            case _ => false
          }
        }
        var d = depth
        var finished = false
        while (!finished) {
          if (try_parse("(*")) d += 1
          else if (d > 0 && try_parse("*)")) { d -= 1; if (d == 0) finished = true }
          else if (d == 0 || !try_parse(comment_text)) finished = true
        }
        if (in.offset < rest.offset)
          Success((in.source.subSequence(in.offset, rest.offset).toString, d), rest)
        else Failure("comment expected", in)
      }
    }.named("comment_depth")

    def comment: Parser[String] =
      comment_depth(0) ^? { case (x, d) if d == 0 => x }

    def comment_line(ctxt: Line_Context): Parser[(String, Line_Context)] = {
      val depth =
        ctxt match {
          case Finished => 0
          case Comment(d) => d
          case _ => -1
        }
      if (depth >= 0)
        comment_depth(depth) ^^
          { case (x, 0) => (x, Finished)
            case (x, d) => (x, Comment(d)) }
      else failure("")
    }

    val recover_comment: Parser[String] =
      comment_depth(0) ^^ (_._1)

    def comment_content(source: String): String = {
      require(parseAll(comment, source).successful, "no comment")
      source.substring(2, source.length - 2)
    }


    /* control cartouches */

    val control_symbol: Parser[String] = one(Symbol.is_control)

    val control_cartouche: Parser[String] = control_symbol ~ cartouche ^^ { case a ~ b => a + b }


    /* keyword */

    def literal(lexicon: Lexicon): Parser[String] = new Parser[String] {
      def apply(in: Input) = {
        val result = lexicon.scan(in)
        if (result.isEmpty) Failure("keyword expected", in)
        else Success(result, in.drop(result.length))
      }
    }.named("keyword")
  }



  /** Lexicon -- position tree **/

  object Lexicon {
    /* representation */

    private sealed case class Tree(branches: Map[Char, (String, Tree)])
    private val empty_tree = Tree(Map())

    val empty: Lexicon = new Lexicon(empty_tree)
    def apply(elems: String*): Lexicon = empty ++ elems
  }

  final class Lexicon private(rep: Lexicon.Tree) {
    /* auxiliary operations */

    private def dest(tree: Lexicon.Tree, result: List[String]): List[String] =
      tree.branches.toList.foldLeft(result) {
        case (res, (_, (s, tr))) => if (s.isEmpty) dest(tr, res) else dest(tr, s :: res)
      }

    private def lookup(str: CharSequence): Option[(Boolean, Lexicon.Tree)] = {
      val len = str.length
      @tailrec
      def look(tree: Lexicon.Tree, tip: Boolean, i: Int): Option[(Boolean, Lexicon.Tree)] = {
        if (i < len) {
          tree.branches.get(str.charAt(i)) match {
            case Some((s, tr)) => look(tr, s.nonEmpty, i + 1)
            case None => None
          }
        }
        else Some(tip, tree)
      }
      look(rep, false, 0)
    }

    def completions(str: CharSequence): List[String] =
      lookup(str) match {
        case Some((true, tree)) => dest(tree, List(str.toString))
        case Some((false, tree)) => dest(tree, Nil)
        case None => Nil
      }


    /* pseudo Set methods */

    def raw_iterator: Iterator[String] = dest(rep, Nil).iterator
    def iterator: Iterator[String] = dest(rep, Nil).sorted.iterator

    override def toString: String = iterator.mkString("Lexicon(", ", ", ")")

    def is_empty: Boolean = rep.branches.isEmpty

    def contains(elem: String): Boolean =
      lookup(elem) match {
        case Some((tip, _)) => tip
        case _ => false
      }


    /* build lexicon */

    def + (elem: String): Lexicon =
      if (contains(elem)) this
      else {
        val len = elem.length
        def extend(tree: Lexicon.Tree, i: Int): Lexicon.Tree =
          if (i < len) {
            val c = elem.charAt(i)
            val end = (i + 1 == len)
            tree.branches.get(c) match {
              case Some((s, tr)) =>
                Lexicon.Tree(tree.branches +
                  (c -> (if (end) elem else s, extend(tr, i + 1))))
              case None =>
                Lexicon.Tree(tree.branches +
                  (c -> (if (end) elem else "", extend(Lexicon.empty_tree, i + 1))))
            }
          }
          else tree
        new Lexicon(extend(rep, 0))
      }

    def ++ (elems: IterableOnce[String]): Lexicon =
      elems.iterator.foldLeft(this)(_ + _)

    def ++ (other: Lexicon): Lexicon =
      if (this eq other) this
      else if (is_empty) other
      else this ++ other.raw_iterator

    def -- (remove: Iterable[String]): Lexicon =
      if (remove.exists(contains))
        Lexicon.empty ++ iterator.filterNot(a => remove.exists(b => a == b))
      else this


    /* scan */

    def scan(in: Reader[Char]): String = {
      val source = in.source
      val offset = in.offset
      val len = source.length - offset

      @tailrec def scan_tree(tree: Lexicon.Tree, result: String, i: Int): String = {
        if (i < len) {
          tree.branches.get(source.charAt(offset + i)) match {
            case Some((s, tr)) => scan_tree(tr, if (s.isEmpty) result else s, i + 1)
            case None => result
          }
        }
        else result
      }
      scan_tree(rep, "", 0)
    }
  }



  /** read stream without decoding: efficient length operation **/

  private class Restricted_Seq(seq: IndexedSeq[Char], start: Int, end: Int) extends CharSequence {
    def charAt(i: Int): Char =
      if (0 <= i && i < length) seq(start + i)
      else throw new IndexOutOfBoundsException

    def length: Int = end - start  // avoid expensive seq.length

    def subSequence(i: Int, j: Int): CharSequence =
      if (0 <= i && i <= j && j <= length) new Restricted_Seq(seq, start + i, start + j)
      else throw new IndexOutOfBoundsException

    override def toString: String =
      Library.string_builder(hint = length) { buf =>
        for (offset <- start until end) buf.append(seq(offset))
      }
  }

  abstract class Byte_Reader extends Reader[Char] with AutoCloseable

  private def make_byte_reader(stream: InputStream, stream_length: Int): Byte_Reader = {
    val buffered_stream = new BufferedInputStream(stream)
    val seq =
      new PagedSeq({ (buf: Array[Char], offset: Int, length: Int) =>
        var i = 0
        var c = 0
        var eof = false
        while (!eof && i < length) {
          c = buffered_stream.read
          if (c == -1) eof = true
          else { buf(offset + i) = c.toChar; i += 1 }
        }
        if (i > 0) i else -1
      })
    val restricted_seq = new Restricted_Seq(seq, 0, stream_length)

    class Paged_Reader(override val offset: Int) extends Byte_Reader {
      override lazy val source: CharSequence = restricted_seq
      def first: Char = if (seq.isDefinedAt(offset)) seq(offset) else '\u001a'
      def rest: Paged_Reader = if (seq.isDefinedAt(offset)) new Paged_Reader(offset + 1) else this
      def pos: InputPosition = new OffsetPosition(source, offset)
      def atEnd: Boolean = !seq.isDefinedAt(offset)
      override def drop(n: Int): Paged_Reader = new Paged_Reader(offset + n)
      def close(): Unit = buffered_stream.close()
    }
    new Paged_Reader(0)
  }

  def byte_reader(file: JFile): Byte_Reader =
    make_byte_reader(new FileInputStream(file), file.length.toInt)

  def byte_reader(url: Url): Byte_Reader = {
    val connection = url.open_connection()
    val stream = connection.getInputStream
    val stream_length = connection.getContentLength
    make_byte_reader(stream, stream_length)
  }

  def reader_is_utf8(reader: Reader[Char]): Boolean =
    reader.isInstanceOf[Byte_Reader]

  def reader_decode_utf8(is_utf8: Boolean, s: String): String =
    if (is_utf8) UTF8.decode_permissive(s) else s

  def reader_decode_utf8(reader: Reader[Char], s: String): String =
    reader_decode_utf8(reader_is_utf8(reader), s)


  /* plain text reader */

  def char_reader(text: CharSequence): CharSequenceReader =
    new CharSequenceReader(text)
}
