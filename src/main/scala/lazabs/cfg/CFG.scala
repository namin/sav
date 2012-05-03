package lazabs.cfg

import lazabs.ast.ASTree._

/**
 * The transitions in the control flow graph consists of assumes and assignments 
 */
sealed abstract class Label
case class Assume(p: Expression) extends Label
case class Assign(lhs: Expression, rhs: Expression) extends Label
case class Havoc(v: Variable) extends Label
// the following labels are used in large block encoding
case class Sequence(l1: Label, l2: Label) extends Label
case class Choice(l1: Label, l2: Label) extends Label
// the following label is later accelerated
// qs are the intermediate states which will later get predicates
case class TransitiveClosure(ls: List[Label],qs: List[CFGVertex]) extends Label
// the following label is used for nts files
case class Transfer(t: Expression) extends Label

/**
 * control flow graph
 * each vertex has an id - the vertex with id = -1 is an error state.
 * predicate can have a set of parents
 */
case class CFGVertex(id: Int) {
  def getId = id
}

object FreshCFGStateId {
  def reset() = {
    curStateCounter = -1
  }
  private var curStateCounter = -1
  def apply: Int = {
    curStateCounter = curStateCounter + 1
    curStateCounter
  }
}

case class CFGAdjacent(label: Label, to: CFGVertex)

case class CFG(start: CFGVertex, 
    transitions: Map[CFGVertex,Set[CFGAdjacent]],                  // transition relation 
    parent: Map[CFGVertex,Set[CFGAdjacent]],                       // parent relation 
    predicates: Map[CFGVertex,List[(Expression,List[Int])]],       // predicates defined at each program point. The order of the predicates is important
    variables: Map[CFGVertex,Set[Variable]],                       // variables defined at each program point 
    formulas: Map[(CFGVertex,CFGVertex),Expression],               // formula corresponding to a label in the control flow graph 
    freshVars: Map[(CFGVertex,CFGVertex),Set[Variable]],           // set of fresh variables corresponding to a label in the control flow graph 
    sobject: Option[Sobject],                                      // the AST of the original Scala program (if any)
    asserts: Map[CFGVertex, Expression]) {
  def update(start: CFGVertex = start,
             transitions: Map[CFGVertex,Set[CFGAdjacent]]            = transitions,
             parent: Map[CFGVertex,Set[CFGAdjacent]]                 = parent,
             predicates: Map[CFGVertex,List[(Expression,List[Int])]] = predicates,
             variables: Map[CFGVertex,Set[Variable]]                 = variables,
             formulas: Map[(CFGVertex,CFGVertex),Expression]         = formulas,
             freshVars: Map[(CFGVertex,CFGVertex),Set[Variable]]     = freshVars,
             sobject: Option[Sobject]                                = sobject,
             asserts: Map[CFGVertex, Expression]                     = asserts): CFG =
  CFG(start,transitions,parent,predicates,variables,formulas,freshVars,sobject,asserts)
  /**
   * gets a formula between two CFG vertices
   * replaces the variables which are supposed to be fresh with fresh variables in each call 
   */
  import lazabs.utils.Manip._
  def getFormula(start: CFGVertex, end: CFGVertex, label: Label): Expression = this.formulas.get(start,end) match {
    case Some (af) =>
      val fvs = this.freshVars.getOrElse((start,end),List())
      fvs.foldLeft(af)((a,b) => substitute(a,Map(b -> freshVariable(b.stype))))
    case None =>
      val vars = if(end.getId == start.getId) this.variables.getOrElse(start, Set()) else this.variables.getOrElse(start, Set()) // Scala programs with global vars
      transFormula(label,vars)._1
  }
  def allVariables = variables.values.fold(Set.empty)(_.union(_)).map(_.name)
}