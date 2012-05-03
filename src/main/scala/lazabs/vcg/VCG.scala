package lazabs.vcg

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.digraph._
import lazabs.utils.Manip

object VCG {

  /*
   * Returns a set of verification conditions that imply the correctness of the annotations in the given CFG
   */
  def apply(cfg: CFG) : Set[Expression] = {
    var result = Set[Expression]()
    
    val init = cfg.asserts.keySet.union(Set(cfg.start))
    var processed = Set[Vertex]()
    var ready = List[Vertex]()
    var notReady =  cfg.getVertices.diff(init)
    
    var basicPaths = Map[cfg.Edge, Map[Vertex, Expression]]()
    
    def nameVariable(vertex: Vertex, variable: String) = {
      variable + "$" + vertex.id
    }
    
    def renameVariables(vertex: Vertex, f: Expression) = {
      Manip.subst(f, cfg.variables.map(v => (v, Variable(nameVariable(vertex, v)))).toMap)
    }
    
    def addEdge(e: cfg.Edge, f: Expression) = {
      val (from, label, to) = e
      val fs = label match {
        case Assume(p) => 
          renameVariables(from, p) :: cfg.variables.toList.map(v => Equality(Variable(nameVariable(from, v)), Variable(nameVariable(to, v))))
        case Assign(Variable(lhs, _), rhs: Expression) => 
           cfg.variables.toList.map(v =>
             if (v == lhs) Equality(Variable(nameVariable(to, v)), renameVariables(from, rhs))
             else Equality(Variable(nameVariable(from, v)), Variable(nameVariable(to, v))))
        case Havoc(Variable(havocVar, _)) =>
           for (v <- cfg.variables.toList; if v != havocVar) yield Equality(Variable(nameVariable(from, v)), Variable(nameVariable(to, v)))
      }
      Manip.simplify(fs.fold(f)(Conjunction(_, _)))
    }
    
    def checkChildren(v: Vertex, m: Map[Vertex, Expression]) {
      for ((label, to) <- cfg.out(v)) {
        basicPaths += ((v, label, to) -> m.mapValues(addEdge((v, label, to), _)))
        
        if (notReady.contains(to) && cfg.in(to).map(_._1).diff(processed).isEmpty) {
          notReady -= to
          ready = to :: ready
        }
        
        cfg.asserts.get(to).foreach({assertFormula =>
          for ((root, formula) <- basicPaths(v, label, to)) {
            result += Implication(formula, renameVariables(to, assertFormula))
          }
        })
      }
    }
    
    // initialization step
    for (v <- init) {
      val m = cfg.asserts.get(v) match {
        case None => Map(v -> BoolConst(true))
        case Some(e) => Map(v -> renameVariables(v, e))
      }
      processed += v
      checkChildren(v, m)
    }

    while (!ready.isEmpty) {
      // take any ready node
      val v = ready.head
      ready = ready.tail

      // merge all incoming formulas
      val es = cfg.in(v).map(t => (t._1, t._2, v))
      val ps = es.map(basicPaths)
      var m = Map[Vertex, Expression]()
      for (p <- ps) {
        for ((root, formula) <- p) {
          m.get(root) match {
            case None => m += (root -> formula)
            case Some(mFormula) => m += (root -> Disjunction(mFormula, formula))
          }
        }
      }
      m = m.mapValues(Manip.simplifyDisjuncts)
      
      // mark as processed
      processed += v
      
      // check children
      checkChildren(v, m)
    }
    
    assert(notReady.isEmpty, "The CFG is not sufficiently annotated.")
    
    result
  }
}
