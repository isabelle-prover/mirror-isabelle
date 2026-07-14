/*  Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Isabelle symbols panel as web view.
*/

"use strict";

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
  CancellationToken, window } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as LSP from "./lsp"
import * as Symbol from "./symbol"
import * as Webview from "./webview"


export class Provider implements WebviewViewProvider {
  public static readonly view_type = "isabelle-symbols"

  private _view?: WebviewView
  private _grouped_symbols: { [key: string]: Symbol.Entry[] } = {}
  private _abbrevs: [string, string][] = []

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  request(language_client: LanguageClient) {
    if (language_client) { this._language_client.sendNotification(LSP.abbrevs_request_type) }
  }

  setup(language_client: LanguageClient) {
    language_client.onNotification(LSP.abbrevs_response_type, params => {
      this._grouped_symbols = this._group_symbols(Symbol.symbols.entries)
      this._abbrevs = params.abbrevs ?? []
      if (this._view) { this._update_webview() }
    })
  }

  public resolveWebviewView(
    view: WebviewView,
    _context: WebviewViewResolveContext,
    _token: CancellationToken
  ) {
    this._view = view

    view.webview.options = { enableScripts: true, localResourceRoots: [this._extension_uri] }

    view.webview.html = this._get_html()

    if (Object.keys(this._grouped_symbols).length > 0) { this._update_webview() }

    this._view.webview.onDidReceiveMessage(message => {
      if (message.command === "insert_symbol") { this._insert_symbol(message.symbol) }
      else if (message.command === "reset_control") { this._reset_control() }
      else if (message.command === "apply_control") { this._apply_control(message.action) }
    })
  }

  private _apply_control(action: string): void {
    const editor = window.activeTextEditor
    if (!editor) return

    const document = editor.document
    const selection = editor.selection

    const selected_text = document.getText(selection)
    if (!selected_text.trim() && !selection.isEmpty) return

    const control_symbols: { [key: string]: string } = {}
    Symbol.control_render.forEach(symbol => control_symbols[symbol.name] = symbol.decoded)

    if (!control_symbols[action]) return
    const control_symbol = control_symbols[action]
    const all_control_symbols = Object.values(control_symbols)

    editor.edit(edit_builder => {
      if (!selection.isEmpty) {
        const new_text = selected_text
          .split("")
          .map((char, _index, _arr) => {
            if (char.trim() === "") return char
            if (all_control_symbols.includes(char)) return ""

            return `${control_symbol}${char}`
          })
          .join("")

        edit_builder.replace(selection, new_text)
      }
      else {
        edit_builder.insert(selection.active, control_symbol)
      }
    }).then(success => {
      if (!success) { window.showErrorMessage("Failed to apply control effect.") }
    })
  }

  private _insert_symbol(symbol: string): void {
    const editor = window.activeTextEditor
    if (editor) {
      editor.edit(edit_builder => edit_builder.insert(editor.selection.active, symbol))
    }
  }

  private _reset_control(): void {
    const editor = window.activeTextEditor
    if (!editor) { return }

    const document = editor.document
    const selection = editor.selection

    const selected_text = document.getText(selection)
    if (!selected_text.trim() && !selection.isEmpty) return

    const control_symbols: { [key: string]: string } = {}
    Symbol.control_render.forEach(symbol => control_symbols[symbol.decoded] = symbol.name)

    const all_control_symbols = Object.keys(control_symbols)

    editor.edit(edit_builder => {
      if (!selection.isEmpty) {
        const new_text = selected_text
          .split("")
          .map(char => (all_control_symbols.includes(char) ? "" : char))
          .join("")

        edit_builder.replace(selection, new_text)
      }
    })
  }

  private _update_webview(): void {
    this._view.webview.postMessage({
      command: "update",
      symbols: this._grouped_symbols,
      abbrevs: this._abbrevs,
    })
  }

  private _group_symbols(symbols: Symbol.Entry[]): { [key: string]: Symbol.Entry[] } {
    const grouped_symbols: { [key: string]: Symbol.Entry[] } = {}
    for (const symbol of symbols) {
      if (symbol.groups && Array.isArray(symbol.groups)) {
        for (const group of symbol.groups) {
          if (!grouped_symbols[group]) { grouped_symbols[group] = [] }
          grouped_symbols[group].push(symbol)
        }
      }
    }
    return grouped_symbols
  }

  private _get_html(): string {
    return Webview.get_html(this._view.webview, this._extension_uri.fsPath, "Symbols Panel",
      "symbols.js", "symbols.css", '<div id="symbols-container"></div>')
  }
}
