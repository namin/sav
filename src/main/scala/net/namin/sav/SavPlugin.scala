package net.namin.sav

import scala.tools.nsc
import nsc.Global
import nsc.Phase
import nsc.plugins.Plugin
import nsc.plugins.PluginComponent

class SavPlugin(val global: Global) extends Plugin {
  import global._

  val name = "sav"
  val description = "synthesis, analysis, verification"
  val components = List[PluginComponent](Component)
  
  private object Component extends PluginComponent {
    val global: SavPlugin.this.global.type = SavPlugin.this.global
    val runsAfter = List[String]("refchecks");
    val phaseName = SavPlugin.this.name
    def newPhase(_prev: Phase) = new SavPhase(_prev)    
    
    class SavPhase(prev: Phase) extends StdPhase(prev) {
      override def name = SavPlugin.this.name
      def apply(unit: CompilationUnit) {
        println("SAV: TODO")
      }
    }
  }
}
