package lazabs.cfg

import lazabs.ast.ASTree._
import lazabs.digraph._
import lazabs.viewer.ScalaPrinter
import scala.collection.mutable
import lazabs.ast.ASTree._
import lazabs.utils.Manip._

/**
 * The transitions in the control flow graph consists of assumes, havocs, and assignments 
 */
sealed abstract class CFGLabel
case class Assume(p: Expression) extends CFGLabel {
  override def toString = ScalaPrinter(this)
}
case class Assign(lhs: Expression, rhs: Expression) extends CFGLabel {
  override def toString = ScalaPrinter(this)
}
case class Havoc(v: Variable) extends CFGLabel {
  override def toString = ScalaPrinter(this)
}

/**
 * control flow graph
 */

class CFG extends DiGraphImp[CFGLabel] {
  val error = newVertex
  var start = error
  val variables = mutable.Set[String]()
  val asserts = mutable.Map[Vertex, Expression]()
  val predicates = mutable.Set[Expression]()

  /*
   * Convert to Graphviz format
   */
  def toDot: String = {
    //vertices
    def vToS(v:Vertex) = {
      val id = v.id
      if (v == start) id + "[label=\"START\"];"
      else if (v == error) id + "[label=\"ERROR\"];"
      else v.id + "[label=\"" + v.id + "\"];"
    }
    val vs = for { v <- getVertices } yield vToS(v)

    //edges
    val es = for {
      (Vertex(id1), l:CFGLabel, Vertex(id2)) <- getEdges 
    } yield id1 + " -> " + id2 + "[label=\"" + lazabs.viewer.ScalaPrinter(l) + "\"];"

    //asserts
    var assId = -1
    def getAssId = {assId += 1; "a" + assId}
    val ass = for {
      (Vertex(id),e) <- asserts.toSet 
      val assId = getAssId
      val vdecl:String = assId + "[label=\"" + lazabs.viewer.ScalaPrinter(e) + "\",shape=box];"
      val edecl:String= assId + " -> " + id + "[style=dotted];\n"
    } yield Set(vdecl, edecl)

    //finally
    val header = "digraph CFG {"
    val footer = "\n}"
    (header /: (vs ++ es ++ ass.flatten)) (_ + "\n" + _) + footer
  }
}
