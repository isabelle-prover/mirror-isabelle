/*  Author:     Diana Korchmar, LMU Muenchen

Isabelle documentation panel as web view.
*/

'use strict';

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
  CancellationToken, window, workspace } from 'vscode'
import * as lsp from './lsp'
import * as webview from './webview'
import { commands } from 'vscode'
import { LanguageClient } from 'vscode-languageclient/node'


class Documentation_Panel_Provider implements WebviewViewProvider {
  public static readonly view_type = 'isabelle-documentation'

  private _view?: WebviewView
  private _documentation_sections: any[] = []

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  request(language_client: LanguageClient) {
    if (language_client)  this._language_client.sendNotification(lsp.documentation_request_type)
  }

  setupDocumentation(language_client: LanguageClient) {
    language_client.onNotification(lsp.documentation_response_type, params =>
      {
        if (!params || !params.sections || !Array.isArray(params.sections)) return
        this._documentation_sections = params.sections
        if (this._view) this._update_webview()
      })
  }

  public resolveWebviewView(
    view: WebviewView,
    _context: WebviewViewResolveContext,
    _token: CancellationToken
  ): void {
    this._view = view
    this._view.webview.options =
      { enableScripts: true, localResourceRoots: [ this._extension_uri ] }

    this._view.webview.html = this._get_html()

    if (Object.keys(this._documentation_sections).length > 0) this._update_webview()

    this._view.webview.onDidReceiveMessage(async message => {
      if (message.command === 'open_document') {
        this._open_document(message.platform_path)
      }
    })
  }

  private _update_webview(): void {
    if (!this._view) { return }

    this._view.webview.postMessage({ command: 'update', sections: this._documentation_sections, })
  }

  private _open_document(platform_path: string): void {
    const uri = Uri.file(platform_path)

    if (platform_path.endsWith(".pdf")) { commands.executeCommand("vscode.open", uri) }
    else {
      workspace.openTextDocument(uri).then(document => {
        window.showTextDocument(document)
      })
    }
  }


  private _get_html(): string {
    return webview.get_html(
      this._view.webview,
      this._extension_uri.fsPath,
      "Documentation Panel",
      "documentation.js",
      "documentation.css",
      '<div id="documentation-container">Loading documentation...</div>')
  }
}

export { Documentation_Panel_Provider }
