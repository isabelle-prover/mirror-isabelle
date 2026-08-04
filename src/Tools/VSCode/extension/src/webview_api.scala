/*  Title:      Tools/VSCode/extension/src/webview_api.scala
    Author:     Fabian Huch

VSCode Webview API: exposed within Webview environment.
 */
package isabelle.vscode.extension

import scala.scalajs.js
import scala.scalajs.js.JSConverters._

import isabelle._


object Webview_Api {
  @js.native
  private trait WebviewApi extends js.Object {
    def postMessage(message: js.Any | Null): Unit = js.native
    def getState(): js.UndefOr[js.Object] = js.native
    def setState(newState: js.UndefOr[js.Object]): js.UndefOr[js.Object] =
      js.native
  }

  @js.native
  @js.annotation.JSGlobal("acquireVsCodeApi")
  private def acquireVsCodeApi(): WebviewApi = js.native

  lazy val acquire = new Webview_Api(acquireVsCodeApi())
}

class Webview_Api private(api: Webview_Api.WebviewApi) {
  def post(json: JSON.T): Unit = api.postMessage(Scalajs.JSON(json))

  def get_state: Option[JSON.Object.T] =
    api.getState().toOption.map {
      case Scalajs.JSON.Object(json) => json
      case x => error("Bad webview state: " + x.toString)
    }

  def set_state(state: Option[JSON.Object.T]): Unit = {
    api.setState(state.map(Scalajs.JSON.Object(_)).orUndefined)
  }
}
