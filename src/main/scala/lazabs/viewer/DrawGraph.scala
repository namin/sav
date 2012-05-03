package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.art._
import lazabs.cfg._

object DrawGraph {
  /**
   * output files for writing the results
   */
  val dotFileName =  "DotOutput"
  val absFileName =  "AbsOutput"  
  val predFileName = "PredOutput.txt"     
  var absOutput: java.io.FileWriter = null
  var absInformation = Map[Int,String]()
  var labelInformation = List[String]()
  var predMap: Map[CFGVertex,List[(Expression,List[Int])]] = Map.empty
  
  var currentId = 0
  
  /**
   * showing a transition system
   */
  def show(transitions: String, ls: Map[String,String]): Unit = { 
    val runTime = Runtime.getRuntime   
    val dotOutput = new java.io.FileWriter(dotFileName + currentId + ".dot")
    dotOutput.write( "digraph lazabs {\n")
    dotOutput.write( transitions)
    if(!ls.isEmpty) dotOutput.write( (ls.toList.map { case (x,y) =>
        if (y.startsWith("ERR"))
                        (x + "[label=\"" + y + "\"," + "color=red];\n") 
        else (x + "[label=\"" + y + "\"];\n")}).reduceLeft[String](_+_) )               
    dotOutput.write( "}")
    dotOutput.close
    var proc = runTime.exec( "dot -Tpng " + "DotOutput" + currentId + ".dot" + " -o graph" + currentId + ".png" )
    proc.waitFor
    proc = runTime.exec( "eog graph" + currentId + ".png")
    proc.waitFor
    currentId = currentId + 1
  }
  
  var ver_num = 0
  def apply(ts: List[(CFGVertex,Set[CFGAdjacent])], predMap: Map[CFGVertex,List[(Expression,List[Int])]],absInFile: Boolean,ntsNames: Option[Map[Int,String]]): Unit = {
    val predOutput = new java.io.FileWriter(predFileName)
    labelInformation = List[String]()
    this.predMap = predMap    
    val dot = toDotCFG(ts,absInFile,ntsNames)
    if (!dot.isEmpty) {
      val transitions = dot.map(x => x.toString).reduceLeft(_+_)      
      val predicates = predMap.toList.sortWith((e1, e2) => (e1._1.getId < e2._1.getId))
      predOutput.write(predicates.map(x => (x._1, x._2.map(y => lazabs.viewer.ScalaPrinter(y._1)))).mkString("\n"))
      predOutput.close
      if(absInFile) {
        absOutput = new java.io.FileWriter(absFileName + currentId + ".txt")
        println("The transition information is in the file " + absFileName + currentId + ".txt")
        absOutput.write(labelInformation.mkString("\n"))
        absOutput.close
      }
      show(transitions, labels)
      labels = Map()
      ver_num = 0
    }
  }
  
  def apply(t: RTree, b: Boolean): Unit = {
    val dot = toDotRTree(t,b)
    if(b && absInformation.size != 0) {
      absOutput = new java.io.FileWriter(absFileName + currentId + ".txt")
      println("The abstraction information is in the file " + absFileName + currentId + ".txt")
      absOutput.write(absInformation.toList.sortBy(_._1).map(x => x._1.toString + " -> " + x._2.toString).reduceLeft(_+_))
      absOutput.close
    }
    if (!dot.isEmpty) {
      val transitions = dot.map(x => x.toString).reduceLeft(_+_)
      show( transitions, labels)
      labels = Map()
    }
  }
   
  var labels = Map[String,String]()
  def toUniqueName(o: Object): String = {         
    val ret = "n" + (o.hashCode).toString
    ret.replace( '-', '_')
  }
  
  def toDotCFG(t: List[(CFGVertex,Set[CFGAdjacent])],absInFile: Boolean,ntsNames: Option[Map[Int,String]]): Set[String] = t match {
    case  Nil => Set.empty
    case (CFGVertex(id),ends) :: rest =>
      val idString  = ntsNames match {   // mark with nts names
        case Some(m) => m.getOrElse(id,id.toString)
        case None => id.toString
      }
      val nexts = ends.map(x => {
        val xToString = ntsNames match {   // mark with nts names
          case Some(m) => m.getOrElse(x.to.id,x.to.id.toString)
          case None => x.to.id.toString
        }
        if(!t.contains(x.to)) labels += (xToString -> (if (!ntsNames.isDefined) (xToString + ",p: " + predMap.getOrElse(x.to,List()).size) else 
          (xToString + ", " + x.to.id)))
        if(!absInFile) idString + "->" + xToString + "[label=\"" + lazabs.viewer.ScalaPrinter(x.label) + "\"];\n"
        else {
          labelInformation ::= id.toString + "->" + x.to.id.toString + " : " + lazabs.viewer.ScalaPrinter(x.label) + "\n"
          idString + "->" + xToString + "[label=\"\"];\n"
        }
      })
      labels += (if (!ntsNames.isDefined) (idString -> (idString + ",p: " + predMap.getOrElse(CFGVertex(id),List()).size)) else
        (idString -> (idString + ", " + id.toString)))
      toDotCFG(rest,absInFile,ntsNames) ++ nexts
  }
  
  private def abstraction2String(abs : Set[Expression]) : String = {
    val f = lazabs.art.RTreeMethods.exprSetToFormula(abs)
    val simplified = lazabs.prover.PrincessWrapper.simplify(f)
    lazabs.viewer.ScalaPrinter(simplified)
  }

  def toDotRTree(t: RTree,absInFile: Boolean): Set[String] = {
    var result = Set[String]().empty
    for ((RNode(id, cfgId, abstraction),ends) <- t.transitions.toList) {
      labels += (if(!absInFile) (id.toString -> (cfgId + " , " + abstraction2String(abstraction))) else {
        absInformation += (id -> (abstraction2String(abstraction) + "\n"))
        (id.toString -> id.toString)
      })
      ends.foreach(a => {
        result += (if(!absInFile) (id.toString + "->" + a.to.getId.toString + "[label=\"" + lazabs.viewer.ScalaPrinter(a.label) + "\"];\n")
            else (id.toString + "->" + a.to.getId.toString) + "[label=\"" + (cfgId.toString + "->" + a.to.getCfgId.toString) + "\"];\n")
        if(t.blockedNodes.contains(a.to) && !absInFile)
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + "BLK " + abstraction2String(a.to.getAbstraction)))
        if(t.blockedNodes.contains(a.to) && absInFile) {
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + "BLK " + a.to.getId.toString))
          absInformation += (a.to.getId -> ("BLK " + abstraction2String(a.to.getAbstraction) + "\n"))
        }
        if(t.exploredNodes.contains(a.to) && !absInFile)
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + "EXP " + abstraction2String(a.to.getAbstraction)))
        if(t.exploredNodes.contains(a.to) && absInFile) {
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + "EXP " + a.to.getId.toString))
          absInformation += (a.to.getId -> ("EXP " + abstraction2String(a.to.getAbstraction) + "\n"))
        }
        if(t.errorNodes.contains(a.to) && !absInFile)
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + "ERR " + abstraction2String(a.to.getAbstraction)))
        if(t.errorNodes.contains(a.to) && absInFile) {
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + "ERR " + a.to.getId.toString))
          absInformation += (a.to.getId -> ("ERR " + abstraction2String(a.to.getAbstraction) + "\n"))
        }
        if(!t.blockedNodes.contains(a.to) && !t.exploredNodes.contains(a.to) && !t.errorNodes.contains(a.to) && !absInFile)
          labels += (a.to.getId.toString -> (a.to.cfgId + " , " + abstraction2String(a.to.getAbstraction)))
      })
    }
    result
  }
}
