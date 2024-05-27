/*  Author:     Makarius
    Author:     Denis Paluca, TU Muenchen
    Author:     Fabian Huch, TU Muenchen

Isabelle/VSCode extension.
*/

'use strict';

import * as platform from './platform'
import * as library from './library'
import * as file from './file'
import * as symbol from './symbol'
import * as vscode_lib from './vscode_lib'
import * as decorations from './decorations'
import * as preview_panel from './preview_panel'
import * as lsp from './lsp'
import * as state_panel from './state_panel'
import { Uri, TextEditor, ViewColumn, Selection, Position, ExtensionContext, workspace, window,
  commands, ProgressLocation } from 'vscode'
import { LanguageClient, LanguageClientOptions, ServerOptions } from 'vscode-languageclient/node'
import { Output_View_Provider } from './output_view'
import { register_script_decorations } from './script_decorations'


let last_caret_update: lsp.Caret_Update = {}


/* command-line arguments from "isabelle vscode" */

interface Args
{
  options?: string[],
  logic?: string,
  logic_ancestor?: string,
  logic_requirements?: boolean,
  sesion_dirs?: string[],
  include_sessions?: string[],
  modes?: string[],
  log_file?: string,
  verbose?: boolean
}

function print_value(x: any): string
{
  return typeof(x) === "string" ? x : JSON.stringify(x)
}

function isabelle_options(args: Args): string[]
{
  var result: string[] = []
  function add(s: string) { result.push(s) }
  function add_value(opt: string, slot: string)
  {
    const x = args[slot]
    if (x) { add(opt); add(print_value(x)) }
  }
  function add_values(opt: string, slot: string)
  {
    const xs: any[] = args[slot]
    if (xs) {
      for (const x of xs) { add(opt); add(print_value(x)) }
    }
  }

  add("-o"); add("vscode_unicode_symbols")
  add("-o"); add("vscode_pide_extensions")
  add("-o"); add("vscode_html_output")
  add_values("-o", "options")

  add_value("-A", "logic_ancestor")
  if (args.logic) { add_value(args.logic_requirements ? "-R" : "-l", "logic") }

  add_values("-d", "session_dirs")
  add_values("-i", "include_sessions")
  add_values("-m", "modes")
  add_value("-L", "log_file")
  if (args.verbose) { add("-v") }

  return result
}


/* activate extension */

export async function activate(context: ExtensionContext)
{
  /* server */

  try {
    const isabelle_home = library.getenv_strict("ISABELLE_HOME")
    const isabelle_tool = isabelle_home + "/bin/isabelle"
    const args = JSON.parse(library.getenv("ISABELLE_VSCODIUM_ARGS") || "{}")

    const server_opts = isabelle_options(args)
    const server_options: ServerOptions =
      platform.is_windows() ?
        { command: file.cygwin_bash(),
          args: ["-l", isabelle_tool, "vscode_server"].concat(server_opts) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(server_opts) }

    const language_client_options: LanguageClientOptions = {
      documentSelector: [
        { language: "isabelle", scheme: vscode_lib.file_scheme },
        { language: "isabelle-ml", scheme: vscode_lib.file_scheme },
        { language: "bibtex", scheme: vscode_lib.file_scheme }
      ]
    }

    const language_client =
      new LanguageClient("Isabelle", server_options, language_client_options, false)


    window.withProgress({location: ProgressLocation.Notification, cancellable: false},
      async (progress) =>
        {
          progress.report({
            message: "Waiting for Isabelle language server..."
          })
          await language_client.onReady()
        })


    /* decorations */

    decorations.setup(context)
    context.subscriptions.push(
      workspace.onDidChangeConfiguration(() => decorations.setup(context)),
      workspace.onDidChangeTextDocument(event => decorations.touch_document(event.document)),
      window.onDidChangeActiveTextEditor(decorations.update_editor),
      workspace.onDidCloseTextDocument(decorations.close_document))

    language_client.onReady().then(() =>
      language_client.onNotification(lsp.decoration_type, decorations.apply_decoration))


    /* super-/subscript decorations */

    register_script_decorations(context)


    /* manual decorations */

    function request_decs()
    {
      const document_uri = window.activeTextEditor.document.uri
      const decoration_request: lsp.Decoration_Request = { uri: document_uri.toString() }
      language_client.sendNotification(lsp.decoration_request_type, decoration_request)
    }

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        window.onDidChangeActiveTextEditor(request_decs)
      )
    })


    /* caret handling */

    function update_caret()
    {
      const editor = window.activeTextEditor
      let caret_update: lsp.Caret_Update = {}
      if (editor) {
        const uri = editor.document.uri
        const cursor = editor.selection.active
        if (vscode_lib.is_file(uri) && cursor)
          caret_update = { uri: uri.toString(), line: cursor.line, character: cursor.character }
      }
      if (last_caret_update !== caret_update) {
        if (caret_update.uri) {
          language_client.sendNotification(lsp.caret_update_type, caret_update)
        }
        last_caret_update = caret_update
      }
    }

    function goto_file(caret_update: lsp.Caret_Update)
    {
      function move_cursor(editor: TextEditor)
      {
        const pos = new Position(caret_update.line || 0, caret_update.character || 0)
        editor.selections = [new Selection(pos, pos)]
      }

      if (caret_update.uri) {
        workspace.openTextDocument(Uri.parse(caret_update.uri)).then(document =>
        {
          const editor = vscode_lib.find_file_editor(document.uri)
          const column = editor ? editor.viewColumn : ViewColumn.One
          window.showTextDocument(document, column, !caret_update.focus).then(move_cursor)
        })
      }
    }

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        window.onDidChangeActiveTextEditor(_ => update_caret()),
        window.onDidChangeTextEditorSelection(_ => update_caret()))
      update_caret()

      language_client.onNotification(lsp.caret_update_type, goto_file)
    })


    /* dynamic output */

    const provider = new Output_View_Provider(context.extensionUri, language_client)
    context.subscriptions.push(
      window.registerWebviewViewProvider(Output_View_Provider.view_type, provider))

    language_client.onReady().then(() =>
    {
      language_client.onNotification(lsp.dynamic_output_type,
        params => provider.update_content(params.content))
    })


    /* state panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.state", uri => state_panel.init(uri)))

    language_client.onReady().then(() => state_panel.setup(context, language_client))


    /* preview panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.preview", uri => preview_panel.request(uri, false)),
      commands.registerCommand("isabelle.preview-split", uri => preview_panel.request(uri, true)))

    language_client.onReady().then(() => preview_panel.setup(context, language_client))


    /* spell checker */

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        commands.registerCommand("isabelle.include-word", uri =>
          language_client.sendNotification(lsp.include_word_type)),
        commands.registerCommand("isabelle.include-word-permanently", uri =>
          language_client.sendNotification(lsp.include_word_permanently_type)),
        commands.registerCommand("isabelle.exclude-word", uri =>
          language_client.sendNotification(lsp.exclude_word_type)),
        commands.registerCommand("isabelle.exclude-word-permanently", uri =>
          language_client.sendNotification(lsp.exclude_word_permanently_type)),
        commands.registerCommand("isabelle.reset-words", uri =>
          language_client.sendNotification(lsp.reset_words_type)))
    })


    /* start server */

    context.subscriptions.push(language_client.start())
  }
  catch (exn) {
    window.showErrorMessage(exn)
  }
}


export function deactivate() { }
