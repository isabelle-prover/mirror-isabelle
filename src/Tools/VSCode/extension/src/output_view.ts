/*  Author:     Denis Paluca, TU Muenchen

Isabelle output panel as web view.
*/

'use strict';

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
   CancellationToken, window, Position, Selection } from 'vscode'
import * as lsp from './lsp'
import * as webview from './webview'
import { LanguageClient } from 'vscode-languageclient/node'


class Output_View_Provider implements WebviewViewProvider {

  public static readonly view_type = 'isabelle-output'

  private _view?: WebviewView
  private content: string = ''

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  public resolveWebviewView(
    view: WebviewView,
    _context: WebviewViewResolveContext,
    _token: CancellationToken
  ) {
    this._view = view

    // Allow scripts in the webview
    view.webview.options = { enableScripts: true, localResourceRoots: [this._extension_uri]}

    view.webview.html = this._get_html(this.content)
    view.webview.onDidReceiveMessage(async message =>
      {
        switch (message.command) {
          case "open":
            open_webview_link(message.link)
            break
          case "resize":
            this._language_client.sendNotification(
              lsp.output_set_margin_type, { margin: message.margin })
            break
        }
      })
  }

  public update_content(content: string) {
    if (!this._view) {
      this.content = content
      return
    }

    this._view.webview.html = this._get_html(content)
  }

  private _get_html(content: string): string {
    return webview.get_html(this._view.webview, this._extension_uri.fsPath, "Output",
      "output_view.js", "vscode.css", content)
  }
}

function open_webview_link(link: string) {
  const uri = Uri.parse(link)
  const line = Number(uri.fragment) || 0
  const pos = new Position(line, 0)
  window.showTextDocument(
    uri.with({ fragment: '' }),
    { preserveFocus: false, selection: new Selection(pos, pos) })
}

export { Output_View_Provider, open_webview_link }
