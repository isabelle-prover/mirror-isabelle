/*  Author:     Makarius

State panel via HTML webview inside VSCode.
*/

"use strict";

import { ExtensionContext, Uri, ViewColumn, WebviewPanel, window } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as LSP from "./lsp"
import * as Output_View from "./output_view"
import * as VSCode_Lib from "./vscode_lib"
import * as Webview from "./webview"


let language_client: LanguageClient

function panel_column(): ViewColumn {
  return VSCode_Lib.adjacent_editor_column(window.activeTextEditor, true)
}

class Panel {
  private state_id: number
  private webview_panel: WebviewPanel
  private readonly _extension_path: string

  public get_id(): number { return this.state_id }
  public check_id(id: number): boolean { return this.state_id === id }

  public set_content(state: LSP.State_Output) {
    this.state_id = state.id
    this.webview_panel.webview.html = this._get_html(state.content, state.auto_update)
  }

  public reveal() {
    this.webview_panel.reveal(panel_column())
  }

  constructor(extension_path: string) {
    this._extension_path = extension_path
    this.webview_panel =
      window.createWebviewPanel("isabelle-state", "State", panel_column(), { enableScripts: true })
    this.webview_panel.onDidDispose(exit_panel)
    this.webview_panel.webview.onDidReceiveMessage(message =>
      {
        switch (message.command) {
          case "auto_update":
            language_client.sendNotification(
              LSP.state_auto_update_type, { id: this.state_id, enabled: message.enabled })
            break
          case "update":
            language_client.sendNotification(LSP.state_update_type, { id: this.state_id })
            break
          case "locate":
            language_client.sendNotification(LSP.state_locate_type, { id: this.state_id })
            break
          case "open":
            Output_View.open_webview_link(message.link)
            break
          case "resize":
            language_client.sendNotification(
              LSP.state_set_margin_type, { id: this.state_id, margin: message.margin })
            break
          default:
            break
        }
      })
  }

  private _get_html(content: string, auto_update: boolean): string {
    const checked = auto_update ? "checked" : ""
    const content_with_buttons = `<div id="controls">
      <input type="checkbox" id="auto_update" ${checked}/>
      <label for="auto_update">Auto update</label>
      <button id="update_button">Update</button>
      <button id="locate_button">Locate</button>
    </div>
    ${content}`

    return Webview.get_html(this.webview_panel.webview, this._extension_path, "Output",
      "output_view.js", "vscode.css", content_with_buttons)
  }
}

let panel: Panel

function exit_panel() {
  if (panel) {
    language_client.sendNotification(LSP.state_exit_type, { id: panel.get_id() })
    panel = null
  }
}

export function init(_uri: Uri) {
  if (language_client) {
    if (panel) panel.reveal()
    else language_client.sendRequest(LSP.state_init_type, null)
  }
}

export function setup(context: ExtensionContext, client: LanguageClient) {
  language_client = client
  language_client.onNotification(LSP.state_output_type, params =>
    {
      if (!panel) { panel = new Panel(context.extensionPath) }
      panel.set_content(params)
    })
}
