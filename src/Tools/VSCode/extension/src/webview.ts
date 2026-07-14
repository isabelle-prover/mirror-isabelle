/*  Author:     Fabian Huch

Base functionality for web views.
*/

"use strict";

import {Uri, Webview} from "vscode"
import * as path from "path"
import {text_colors} from "./decorations"
import * as vscode_lib from "./vscode_lib"


export function get_html(
  webview: Webview,
  extension_path: string,
  title: string,
  script_name: string,
  css_name: string = "vscode.css",
  content: string = ""
): string {
  const script_uri = webview.asWebviewUri(Uri.file(path.join(extension_path, "media", script_name)))
  const css_uri = webview.asWebviewUri(Uri.file(path.join(extension_path, "media", css_name)))
  const font_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, "fonts", "IsabelleDejaVuSansMono.ttf")))

  return `<!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <link href="${css_uri}" rel="stylesheet" type="text/css">
        <style>
            @font-face {
                font-family: "Isabelle DejaVu Sans Mono";
                src: url(${font_uri});
            }
            ${_get_decorations()}
        </style>
        <title>${title}</title>
      </head>
      <body>
        <script src="${script_uri}"></script>
        ${content}
      </body>
    </html>`
}

function _get_decorations(): string {
  let style: string[] = []
  for (const key of text_colors) {
    style.push(`body.vscode-light .${key} { color: ${vscode_lib.get_color(key, true)} }\n`)
    style.push(`body.vscode-dark .${key} { color: ${vscode_lib.get_color(key, false)} }\n`)
  }
  return style.join("")
}
