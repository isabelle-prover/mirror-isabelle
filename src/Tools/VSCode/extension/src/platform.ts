/*  Author:     Makarius

System platform identification (see Pure/System/platform.scala).
*/

"use strict";

import * as OS from "os"


/* platform family */

export function is_windows(): boolean {
  return OS.type().startsWith("Windows")
}

export function is_linux(): boolean {
  return OS.type().startsWith("Linux")
}

export function is_macos(): boolean {
  return OS.type().startsWith("Darwin")
}

export function is_unix(): boolean {
  return is_linux() || is_macos()
}
