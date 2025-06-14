/*  Title:      Pure/Admin/component_jedit.scala
    Author:     Makarius

Build component for jEdit text-editor.
*/

package isabelle


import java.nio.charset.Charset

import scala.jdk.CollectionConverters._


object Component_JEdit {
  /* modes */

  object Mode {
    val empty: Mode = new Mode("", "", Nil)

    val init: Mode =
      empty +
        ("noWordSep" -> Symbol.decode("""_'?\<^sub>\^<>""")) +
        ("unalignedOpenBrackets" -> Symbol.open_brackets_decoded) +
        ("unalignedCloseBrackets" -> Symbol.close_brackets_decoded) +
        ("tabSize" -> "2") +
        ("indentSize" -> "2")

    val list: List[Mode] = {
      val isabelle_news: Mode = init.define("isabelle-news", "Isabelle NEWS")

      val isabelle: Mode =
        init.define("isabelle", "Isabelle theory") +
          ("commentStart" -> "(*") +
          ("commentEnd" -> "*)")

      val isabelle_ml: Mode = isabelle.define("isabelle-ml", "Isabelle/ML")

      val isabelle_root: Mode = isabelle.define("isabelle-root", "Isabelle session root")

      val isabelle_options: Mode = isabelle.define("isabelle-options", "Isabelle options")

      val sml: Mode =
        init.define("sml", "Standard ML") +
          ("commentStart" -> "(*") +
          ("commentEnd" -> "*)") +
          ("noWordSep" -> "_'")

      List(isabelle_news, isabelle, isabelle_ml, isabelle_root, isabelle_options, sml)
    }
  }

  final case class Mode private(name: String, description: String, rev_props: Properties.T) {
    override def toString: String = name

    def define(a: String, b: String): Mode = new Mode(a, b, rev_props)

    def + (entry: Properties.Entry): Mode =
      new Mode(name, description, Properties.put(rev_props, entry))

    def write(dir: Path): Unit = {
      require(name.nonEmpty && description.nonEmpty, "Bad Isabelle/jEdit mode content")

      val properties =
        rev_props.reverse.map(p =>
          Symbol.spaces(4) +
          XML.string_of_tree(XML.elem(Markup("PROPERTY", List("NAME" -> p._1, "VALUE" -> p._2)))))

      File.write(dir + Path.basic(name).xml,
"""<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE MODE SYSTEM "xmode.dtd">

<!-- """ + XML.text(description) + """ mode -->
<MODE>
  <PROPS>""" + properties.mkString("\n", "\n", "") + """
  </PROPS>
</MODE>
""")
    }
  }


  /* build jEdit component */

  private val download_jars: List[(String, String)] =
    List(
      "https://repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2/jsr305-3.0.2.jar" ->
      "jsr305-3.0.2.jar")

  private val download_plugins: List[(String, String)] =
    List(
      "CommonControls" -> "1.7.4",
      "Console" -> "5.1.4",
      "ErrorList" -> "2.4.0",
      "Highlight" -> "2.5",
      "SideKick" -> "1.8")

  private def exclude_package(name: String): Boolean =
    name.startsWith("de.masters_of_disaster.ant") ||
    name == "doclet" ||
    name == "installer"

  def build_jedit(
    component_path: Path,
    version: String,
    original: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.require_command("ant", test = "-version")
    Isabelle_System.require_command("patch")

    val component_dir = Components.Directory(component_path).create(progress = progress)


    /* jEdit directory */

    val jedit = "jedit" + version
    val jedit_patched = jedit + "-patched"

    val jedit_dir = Isabelle_System.make_directory(component_path + Path.basic(jedit))
    val jedit_patched_dir = component_path + Path.basic(jedit_patched)
    val source_dir = jedit_patched_dir + Path.basic("jEdit")

    def download_jedit(dir: Path, name: String, target_name: String = ""): Path = {
      val jedit_name = jedit + name
      val url =
        "https://sourceforge.net/projects/jedit/files/jedit/" +
          version + "/" + jedit_name + "/download"
      val path = dir + Path.basic(proper_string(target_name) getOrElse jedit_name)
      Isabelle_System.download_file(url, path, progress = progress)
      path
    }

    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* original version */

      val install_path = download_jedit(tmp_dir, "install.jar")
      Isabelle_System.bash("""export CLASSPATH=""
isabelle_java java -Duser.home=""" + File.bash_platform_path(tmp_dir) +
        " -jar " + File.bash_platform_path(install_path) + " auto " +
        File.bash_platform_path(jedit_dir) + " unix-script=off unix-man=off").check

      val source_path = download_jedit(tmp_dir, "source.tar.bz2")
      Isabelle_System.extract(source_path, jedit_dir)


      /* tango icons (SVG) */

      val tango_path = Isabelle_System.make_directory(tmp_dir + Path.explode("tango"))
      Isabelle_System.download_file(
        "https://github.com/stephenc/tango-icon-theme/archive/41b8f6abd7eb.zip",
        tango_path.zip, progress = progress)
      Isabelle_System.extract(tango_path.zip, tango_path, strip = true)


      /* IntelliJ IDEA icons (SVG) */

      val idea_path = Isabelle_System.make_directory(tmp_dir + Path.explode("idea"))
      Isabelle_System.download_file(
        "https://isabelle.sketis.net/components/idea-icons-20250415.tar.gz",
        idea_path.tar.gz, progress = progress)
      Isabelle_System.extract(idea_path.tar.gz, idea_path, strip = true)


      /* patched version */

      Isabelle_System.copy_dir(jedit_dir, jedit_patched_dir)

      val source_org_dir = source_dir + Path.basic("org")
      val tmp_source_dir = tmp_dir + Path.basic("jEdit")

      progress.echo("Patching jEdit sources ...")
      for {
        file <- File.find_files(Path.explode("~~/src/Tools/jEdit/patches").file).sortBy(_.getName)
        name = file.getName
        if !File.is_backup(name)
      } {
        progress.bash("patch -p2 < " + File.bash_path(File.path(file)),
          cwd = source_dir, echo = progress.verbose).check
      }

      progress.echo("Augmenting icons ...")

      val jedit_icons_path = source_dir + Path.explode("org/gjt/sp/jedit/icons/themes")
      val jedit_classic_path = jedit_icons_path + Path.basic("classic")
      val jedit_tango_path = jedit_icons_path + Path.basic("tango")
      val jedit_idea_path = jedit_tango_path + Path.basic("idea-icons")

      for (theme <- List(jedit_classic_path, jedit_tango_path)) {
        Isabelle_System.copy_file(Path.explode("~~/lib/logo/isabelle_transparent-32.gif"),
          theme + Path.explode("32x32/apps/isabelle.gif"))
      }

      for {
        svg_file <- File.find_files(tango_path.file, pred = file => File.is_svg(file.getName))
        rel_path <- File.relative_path(tango_path, File.path(svg_file))
      } {
        val dir = Isabelle_System.make_directory(jedit_tango_path + rel_path.dir)
        Isabelle_System.copy_file(File.path(svg_file), dir + rel_path.base)
      }

      Isabelle_System.extract(idea_path + Path.explode("jar/idea-icons.jar"), jedit_tango_path)
      Isabelle_System.rm_tree(jedit_tango_path + Path.explode("META-INF"))
      Isabelle_System.copy_file(idea_path + Path.explode("README"), jedit_idea_path)

      progress.echo("Building jEdit ...")
      Isabelle_System.copy_dir(source_dir, tmp_source_dir)
      progress.bash("ant", cwd = tmp_source_dir, echo = progress.verbose).check
      Isabelle_System.copy_file(tmp_source_dir + Path.explode("build/jedit.jar"), jedit_patched_dir)

      val java_sources =
        (for {
          file <- File.find_files(source_org_dir.file, file => File.is_java(file.getName))
          package_name <- Scala_Project.package_name(File.path(file))
          if !exclude_package(package_name)
        } yield File.path(component_path.java_path.relativize(file.toPath).toFile).implode).sorted

      File.write(component_dir.build_props,
        "module = " + jedit_patched + "/jedit.jar\n" +
        "no_build = true\n" +
        "requirements = env:JEDIT_JARS\n" +
        ("sources =" :: java_sources.sorted.map("  " + _)).mkString("", " \\\n", "\n"))
    }


    /* jars */

    val jars_dir = Isabelle_System.make_directory(jedit_patched_dir + Path.basic("jars"))

    for { (url, name) <- download_jars } {
      Isabelle_System.download_file(url, jars_dir + Path.basic(name), progress = progress)
    }

    (jars_dir + Path.basic("MacOS.jar")).file.delete

    for { (name, vers) <- download_plugins } {
      Isabelle_System.with_tmp_file("tmp", ext = "zip") { zip_path =>
        val url =
          "https://sourceforge.net/projects/jedit-plugins/files/" + name + "/" + vers + "/" +
            name + "-" + vers + "-bin.zip/download"
        Isabelle_System.download_file(url, zip_path, progress = progress)
        Isabelle_System.extract(zip_path, jars_dir)
      }
    }


    /* resources */

    val keep_encodings = List("ISO-8859-1", "ISO-8859-15", "US-ASCII", "UTF-8", "windows-1252")
    val drop_encodings =
      Charset.availableCharsets().keySet().asScala.toList.sorted.filterNot(keep_encodings.contains)

    File.write(source_dir + Path.explode("properties/jEdit.props"),
"""#jEdit properties
autoReloadDialog=false
buffer.deepIndent=false
buffer.encoding=UTF-8-Isabelle
buffer.indentSize=2
buffer.lineSeparator=\n
buffer.maxLineLen=100
buffer.noTabs=true
buffer.sidekick.keystroke-parse=false
buffer.tabSize=2
buffer.undoCount=1000
close-docking-area.shortcut2=C+e C+CIRCUMFLEX
complete-word.shortcut=
console.dock-position=floating
console.encoding=UTF-8
console.font=Isabelle DejaVu Sans Mono
console.fontsize=14
console.shell.default=Scala
delete-line.shortcut=A+d
delete.shortcut2=C+d
""" + drop_encodings.map(a => "encoding.opt-out." + a + "=true").mkString("\n") + """
encodingDetectors=BOM XML-PI buffer-local-property
end.shortcut=
expand-abbrev.shortcut2=CA+SPACE
expand-folds.shortcut=
fallbackEncodings=UTF-8 ISO-8859-15 US-ASCII
firstTime=false
focus-buffer-switcher.shortcut2=A+CIRCUMFLEX
foldPainter=Circle
gatchan.highlight.overview=false
helpviewer.font=Isabelle DejaVu Serif
helpviewer.fontsize=12
home.shortcut=
hypersearch-results.dock-position=right
insert-newline-indent.shortcut=
insert-newline.shortcut=
isabelle-debugger.dock-position=floating
isabelle-documentation.dock-position=left
isabelle-export-browser.label=Browse theory exports
isabelle-output.dock-position=bottom
isabelle-output.height=174
isabelle-output.width=412
isabelle-query.dock-position=bottom
isabelle-session-browser.label=Browse session information
isabelle-simplifier-trace.dock-position=floating
isabelle-sledgehammer.dock-position=bottom
isabelle-state.dock-position=right
isabelle-symbols.dock-position=bottom
isabelle-theories.dock-position=right
isabelle.antiquoted_cartouche.label=Make antiquoted cartouche
isabelle.complete-word.label=Complete word
isabelle.complete.label=Complete Isabelle text
isabelle.complete.shortcut2=C+b
isabelle.control-bold.label=Control bold
isabelle.control-bold.shortcut=C+e RIGHT
isabelle.control-emph.label=Control emphasized
isabelle.control-emph.shortcut=C+e LEFT
isabelle.control-reset.label=Control reset
isabelle.control-reset.shortcut=C+e BACK_SPACE
isabelle.control-sub.label=Control subscript
isabelle.control-sub.shortcut=C+e DOWN
isabelle.control-sup.label=Control superscript
isabelle.control-sup.shortcut=C+e UP
isabelle.decrease-font-size.label=Decrease font size
isabelle.decrease-font-size.shortcut2=C+SUBTRACT
isabelle.decrease-font-size.shortcut=C+MINUS
isabelle.decrease-font-size2.label=Decrease font size (clone)
isabelle.draft.label=Show draft in browser
isabelle.exclude-word-permanently.label=Exclude word permanently
isabelle.exclude-word.label=Exclude word
isabelle.first-error.label=Go to first error
isabelle.first-error.shortcut=CS+a
isabelle.goto-entity.label=Go to definition of formal entity at caret
isabelle.goto-entity.shortcut=CS+d
isabelle.include-word-permanently.label=Include word permanently
isabelle.include-word.label=Include word
isabelle.increase-font-size.label=Increase font size
isabelle.increase-font-size.shortcut2=C+ADD
isabelle.increase-font-size.shortcut=C+PLUS
isabelle.increase-font-size2.label=Increase font size (clone)
isabelle.increase-font-size2.shortcut=C+EQUALS
isabelle.java-monitor.label=Java/VM monitor
isabelle.last-error.label=Go to last error
isabelle.last-error.shortcut=CS+z
isabelle.message.label=Show message
isabelle.message.shortcut=CS+m
isabelle.newline.label=Newline with indentation of Isabelle keywords
isabelle.newline.shortcut=ENTER
isabelle.next-error.label=Go to next error
isabelle.next-error.shortcut=CS+n
isabelle.options.label=Isabelle options
isabelle.prev-error.label=Go to previous error
isabelle.prev-error.shortcut=CS+p
isabelle.preview.label=Show preview in browser
isabelle.reset-continuous-checking.label=Reset continuous checking
isabelle.reset-font-size.label=Reset font size
isabelle.reset-node-required.label=Reset node required
isabelle.reset-words.label=Reset non-permanent words
isabelle.select-entity.label=Select all occurences of formal entity at caret
isabelle.select-entity.shortcut=CS+ENTER
isabelle.select-structure.label=Select structure around selection or caret
isabelle.select-structure.shortcut=C+7
isabelle.set-continuous-checking.label=Set continuous checking
isabelle.set-node-required.label=Set node required
isabelle.toggle-breakpoint.label=Toggle Breakpoint
isabelle.toggle-continuous-checking.label=Toggle continuous checking
isabelle.toggle-continuous-checking.shortcut=C+e ENTER
isabelle.toggle-node-required.label=Toggle node required
isabelle.toggle-node-required.shortcut=C+e SPACE
isabelle.tooltip.label=Show tooltip
isabelle.tooltip.shortcut=CS+b
isabelle.update-state.label=Update state output
isabelle.update-state.shortcut=S+ENTER
lang.usedefaultlocale=false
largefilemode=full
line-end.shortcut=END
line-home.shortcut=HOME
logo.icon.medium=32x32/apps/isabelle.gif
lookAndFeel=com.formdev.flatlaf.FlatLightLaf
match-bracket.shortcut2=C+9
metal.primary.font=Isabelle DejaVu Sans
metal.primary.fontsize=12
metal.secondary.font=Isabelle DejaVu Sans
metal.secondary.fontsize=12
navigate-backwards.label=Navigate backwards
navigate-backwards.shortcut=AS+LEFT
navigate-forwards.label=Navigate forwards
navigate-forwards.shortcut=AS+RIGHT
navigate-toolbar=navigate-backwards navigate-forwards
navigator.showOnToolbar=true
new-file-in-mode.shortcut=
next-bracket.shortcut2=C+e C+9
options.shortcuts.deletekeymap.label=Delete
options.shortcuts.duplicatekeymap.dialog.title=Keymap name
options.shortcuts.duplicatekeymap.label=Duplicate
options.shortcuts.resetkeymap.dialog.title=Reset keymap
options.shortcuts.resetkeymap.label=Reset
options.textarea.lineSpacing=1
plugin-blacklist.MacOSX.jar=true
plugin.MacOSXPlugin.altDispatcher=false
plugin.MacOSXPlugin.disableOption=true
prev-bracket.shortcut2=C+e C+8
print.font=Isabelle DejaVu Sans Mono
print.glyphVector=true
recent-buffer.shortcut2=C+CIRCUMFLEX
restore.remote=false
restore=false
search.subdirs.toggle=true
select-block.shortcut2=C+8
sidekick-tree.dock-position=right
sidekick.auto-complete-popup-get-focus=true
sidekick.buffer-save-parse=true
sidekick.complete-delay=0
sidekick.complete-instant.toggle=false
sidekick.complete-popup.accept-characters=\\t
sidekick.complete-popup.insert-characters=
sidekick.persistentFilter=true
sidekick.showFilter=true
sidekick.splitter.location=721
systrayicon=false
tip.show=false
toggle-full-screen.shortcut2=S+F11
toggle-multi-select.shortcut2=C+NUMBER_SIGN
toggle-rect-select.shortcut2=A+NUMBER_SIGN
twoStageSave=false
vfs.browser.dock-position=left
vfs.favorite.0.type=1
vfs.favorite.0=$ISABELLE_HOME
vfs.favorite.1.type=1
vfs.favorite.1=$ISABELLE_HOME_USER
vfs.favorite.2.type=1
vfs.favorite.2=$JEDIT_HOME
vfs.favorite.3.type=1
vfs.favorite.3=$JEDIT_SETTINGS
vfs.favorite.4.type=1
vfs.favorite.4=isabelle-export:
vfs.favorite.5.type=1
vfs.favorite.5=isabelle-session:
view.antiAlias=subpixel HRGB
view.blockCaret=true
view.caretBlink=false
view.docking.framework=PIDE
view.eolMarkers=false
view.extendedState=0
view.font=Isabelle DejaVu Sans Mono
view.fontsize=18
view.fracFontMetrics=false
view.gutter.font=Isabelle DejaVu Sans Mono
view.gutter.fontsize=12
view.gutter.lineNumbers=false
view.gutter.selectionAreaWidth=18
view.height=850
view.middleMousePaste=true
view.showSearchbar=true
view.showToolbar=false
view.status.memory.background=\#ff666699
view.status=( mode , fold , encoding ) locked wrap multiSelect rectSelect overwrite lineSep buffersets task-monitor java-status ml-status errors clock
view.thickCaret=true
view.width=1200
xml-insert-closing-tag.shortcut=

#dark theme
console.bgColor.dark=\#ff2b2b2b
console.plainColor.dark=\#ffffffff
console.caretColor.dark=\#ffffffff
console.infoColor.dark=\#ffc1dfee
console.warningColor.dark=\#ffff8c00
console.errorColor.dark=\#ffb22222
view.bgColor.dark=\#ff2b2b2b
view.caretColor.dark=\#ff99ff99
view.eolMarkerColor.dark=\#ffffcc00
view.fgColor.dark=\#ffffffff
view.gutter.bgColor.dark=\#ff282828
view.gutter.currentLineColor.dark=\#ff66cc00
view.gutter.fgColor.dark=\#ffffffff
view.gutter.focusBorderColor.dark=\#ff99ccff
view.gutter.foldColor.dark=\#ff838383
view.gutter.highlightColor.dark=\#ffffcc00
view.gutter.markerColor.dark=\#ff006666
view.gutter.noFocusBorderColor.dark=\#ffffffff
view.gutter.selectionAreaBgColor.dark=\#ff282828
view.gutter.structureHighlightColor.dark=\#ffcccccc
view.lineHighlightColor.dark=\#ff1d0a0a
view.multipleSelectionColor.dark=\#ff006622
view.selectionColor.dark=\#ff0f4982
view.status.background.dark=\#ff333333
view.status.foreground.dark=\#ffffffff
view.status.highlight.dark=\#ff141414
view.status.memory.background.dark=\#ff666699
view.status.memory.foreground.dark=\#ffcccccc
view.structureHighlightColor.dark=\#ffffff00
view.style.comment1.dark=color\:\#ff87ceeb
view.style.comment2.dark=color\:\#ffcd5c5c
view.style.comment3.dark=color\:\#ff999900
view.style.comment4.dark=color\:\#ffcc6600
view.style.digit.dark=color\:\#ffcc3300
view.style.foldLine.0.dark=color\:\#ffffffff bgColor\:\#ff452424 style\:b
view.style.foldLine.1.dark=color\:\#ffffffff bgColor\:\#ff625950 style\:b
view.style.foldLine.2.dark=color\:\#ffffffff bgColor\:\#ff3c3c67 style\:b
view.style.foldLine.3.dark=color\:\#ffffffff bgColor\:\#ff314444 style\:b
view.style.function.dark=color\:\#ff98fb98
view.style.invalid.dark=color\:\#ffff0066 bgColor\:\#ffffffcc
view.style.keyword1.dark=color\:\#fff0e68c style\:b
view.style.keyword2.dark=color\:\#ff009966 style\:b
view.style.keyword3.dark=color\:\#ffcc6600 style\:b
view.style.keyword4.dark=color\:\#ff66ccff style\:b
view.style.label.dark=color\:\#ffffdead
view.style.literal1.dark=color\:\#ffffa0a0
view.style.literal2.dark=color\:\#ffcc6600
view.style.literal3.dark=color\:\#ffffcc00
view.style.literal4.dark=color\:\#ffffffff
view.style.markup.dark=color\:\#ffbdb76b
view.style.operator.dark=color\:\#ff9b9b9b style\:b
view.wrapGuideColor.dark=\#ff8080ff
""")

    val modes_dir = source_dir + Path.basic("modes")

    Mode.list.foreach(_.write(modes_dir))

    File.change_lines(modes_dir + Path.basic("catalog")) { _.flatMap(line =>
      if (line.containsSlice("FILE=\"ml.xml\"") ||
        line.containsSlice("FILE_NAME_GLOB=\"*.{sml,ml}\"") ||
        line.containsSlice("FILE_NAME_GLOB=\"*.ftl\"")) Nil
      else if (line.containsSlice("NAME=\"jamon\"")) {
        List(
          """<MODE NAME="isabelle" FILE="isabelle.xml" FILE_NAME_GLOB="{*.thy,ROOT0.ML,ROOT.ML}"/>""",
          "",
          """<MODE NAME="isabelle-ml" FILE="isabelle-ml.xml" FILE_NAME_GLOB="*.ML"/>""",
          "",
          """<MODE NAME="isabelle-news" FILE="isabelle-news.xml"/>""",
          "",
          """<MODE NAME="isabelle-options" FILE="isabelle-options.xml"/>""",
          "",
          """<MODE NAME="isabelle-root" FILE="isabelle-root.xml" FILE_NAME_GLOB="ROOT"/>""",
          "",
          line)
      }
      else if (line.containsSlice("NAME=\"sqr\"")) {
        List(
          """<MODE NAME="sml" FILE="sml.xml" FILE_NAME_GLOB="*.{sml,sig}"/>""",
          "",
          line)
      }
      else List(line))
    }

    for (name <- List("keymaps", "macros", "modes", "properties", "startup")) {
      val path = Path.explode(name)
      Isabelle_System.rm_tree(jedit_patched_dir + path)
      Isabelle_System.copy_dir(source_dir + path, jedit_patched_dir)
    }


    /* doc */

    val doc_dir = jedit_patched_dir + Path.basic("doc")

    download_jedit(doc_dir, "manual-a4.pdf", target_name = "jedit-manual.pdf")

    Isabelle_System.copy_file(
      doc_dir + Path.basic("CHANGES.txt"), doc_dir + Path.basic("jedit-changes"))

    File.write(doc_dir + Path.basic("Contents"),
"""Original jEdit Documentation
  jedit-manual    jEdit User's Guide
  jedit-changes   jEdit Version History

""")


    /* make patch */

    File.write(component_path + Path.basic(jedit).patch,
      Isabelle_System.make_patch(component_path, Path.basic(jedit), Path.basic(jedit_patched)))

    if (!original) Isabelle_System.rm_tree(jedit_dir)


    /* settings */

    // see also https://docs.oracle.com/en/java/javase/21/troubleshoot/java-2d-properties.html

    component_dir.write_settings("""
JEDIT_HOME="$COMPONENT/""" + jedit_patched + """"
JEDIT_JARS=""" + quote(File.read_dir(jars_dir).map("$JEDIT_HOME/jars/" + _).mkString(":")) + """
JEDIT_JAR="$JEDIT_HOME/jedit.jar"
classpath "$JEDIT_JAR"

JEDIT_SETTINGS="$ISABELLE_HOME_USER/jedit"

ISABELLE_DOCS="$ISABELLE_DOCS:$JEDIT_HOME/doc"
""")


    /* README */

    File.write(component_dir.README,
"""This is a slightly patched version of jEdit """ + version + """ from
https://sourceforge.net/projects/jedit/files/jedit with some
additional plugins jars from
https://sourceforge.net/projects/jedit-plugins/files


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }



  /** Isabelle tool wrappers **/

  val default_version = "5.7.0"

  val isabelle_tool =
    Isabelle_Tool("component_jedit", "build Isabelle component from the jEdit text-editor",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var original = false
        var version = default_version
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_jedit [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -O           retain copy of original jEdit directory
    -V VERSION   jEdit version (default: """ + quote(default_version) + """)
    -v           verbose

  Build auxiliary jEdit component from original sources, with some patches.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "O" -> (_ => original = true),
          "V:" -> (arg => version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val component_dir = target_dir + Path.basic("jedit-" + Date.Format.alt_date(Date.now()))
        val progress = new Console_Progress(verbose = verbose)

        build_jedit(component_dir, version, original = original, progress = progress)
      })
}
