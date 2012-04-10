package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.cfg._

object DrawGraph {
  val namePrefix = "DotOutput"
  var fileId = 0

  //Unique IDs for annotation nodes
  var annotId = -1
  def getAnnotId = {annotId += 1; "a" + annotId}

  def apply(cfg: CFG): Unit = {
    val runTime = Runtime.getRuntime   
    val dotOutput = new java.io.FileWriter(namePrefix + fileId + ".dot")
    dotOutput.write(cfg.toDot)
    dotOutput.close
    var proc = runTime.exec( "dot -Tpng " + "DotOutput" + fileId + ".dot" + " -o graph" + fileId + ".png" )
    proc.waitFor
    fileId = fileId + 1
  }
}
