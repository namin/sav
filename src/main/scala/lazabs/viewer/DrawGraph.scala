package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.cfg._

object DrawGraph {
  def apply(cfg: CFG, name: String): Unit = {
    val runTime = Runtime.getRuntime   
    val dotOutput = new java.io.FileWriter(name + ".dot")
    dotOutput.write(cfg.toDot)
    dotOutput.close
    var proc = runTime.exec( "dot -Tpng " + name + ".dot" + " -o " + name + ".png" )
    proc.waitFor
  }
}
