/*  Author:     Fabian Huch, TU Muenchen

Elm module for Isabelle.
*/

package isabelle


import java.io.{File => JFile}

import scala.jdk.CollectionConverters._

import org.jsoup.nodes.Element


object Elm {
  private lazy val elm_home =
    proper_string(Isabelle_System.getenv("ISABELLE_ELM")).getOrElse(error("No elm component found"))

  private lazy val exec = Path.explode(elm_home) + Path.basic("elm")

  object Project {
    def apply(
      name: String,
      dir: Path,
      main: Path = Path.explode("src/Main.elm"),
      output: Path = Path.explode("index.html"),
      head: XML.Body = Nil
    ): Project = {
      if (!dir.is_dir) error("Project directory does not exist: " + dir)
      val main_file = dir + main
      if (!main_file.is_file) error("Main elm file does not exist: " + main_file)
      new Project(name, dir, main, dir + output, head)
    }
  }

  class Project private(name: String, dir: Path, main: Path, output: Path, head: XML.Body) {
    val definition = JSON.parse(File.read(dir + Path.basic("elm.json")))
    val src_dirs =
      JSON.strings(definition, "source-directories").getOrElse(
        error("Missing source directories in elm.json"))

    def sources: List[JFile] =
      for {
        src_dir <- src_dirs
        path = dir + Path.explode(src_dir)
        file <- File.find_files(path.file, _.getName.endsWith(".elm"))
      } yield file

    def sources_shasum: SHA1.Shasum = {
      val meta_info = SHA1.shasum_meta_info(SHA1.digest(JSON.Format(definition)))
      val head_digest = SHA1.shasum(SHA1.digest(XML.string_of_body(head)), "head")
      val source_digest =
        SHA1.shasum_sorted(for (file <- sources) yield SHA1.digest(file) -> file.getCanonicalPath)
      meta_info ::: head_digest ::: source_digest
    }

    def get_digest: SHA1.Digest =
      Exn.capture {
        val html = HTML.parse_document(File.read(output))
        val elem = html.head.getElementsByTag("meta").attr("name", "shasum")
        Library.the_single(elem.eachAttr("content").asScala.toList)
      } match {
        case Exn.Res(s) => SHA1.fake_digest(s)
        case _ => SHA1.digest_empty
      }

    def build_html(progress: Progress): String = {
      val digest = sources_shasum.digest
      if (digest == get_digest) File.read(output)
      else {
        progress.echo("### Building " + name + " (" + output.canonical.implode + ") ...")

        val cmd =
          File.bash_path(exec) + " make " + File.bash_path(main) + " --optimize --output=" + output
        val res = Isabelle_System.bash(cmd, cwd = dir)

        if (!res.ok) {
          progress.echo(res.err)
          error("Failed to compile Elm sources")
        }

        val file = HTML.parse_document(File.read(output))
        file.head.appendChild(
          Element("meta").attr("name", "shasum").attr("content", digest.toString))
        file.head.append(XML.string_of_body(head))
        val html = file.html
        File.write(output, html)

        html
      }
    }
  }
}