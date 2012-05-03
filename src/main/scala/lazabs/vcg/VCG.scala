package lazabs.vcg

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.utils.Manip

object VCG {

  /*
   * Returns a set of verification conditions that imply the correctness of the annotations in the given CFG
   */
  def apply(cfg: CFG) : Set[Expression] = {
    var result = Set[Expression]()
    
    val parentSets = createParentSets(cfg)
    val init = cfg.asserts.keySet.union(Set(cfg.start))
    var processed = Set[CFGVertex]()
    var ready = List[CFGVertex]()
    var notReady = parentSets.keySet.diff(init)
    
    var basicPaths = Map[(CFGVertex, CFGAdjacent), Map[CFGVertex, Expression]]()
    
    def nameVariable(vertex: CFGVertex, variable: String) = {
      variable + "$" + vertex.id
    }
    
    def renameVariables(vertex: CFGVertex, f: Expression) = {
      Manip.substitute(f, cfg.allVariables.map(v => (Variable(v), Variable(nameVariable(vertex, v)))).toMap)
    }
    
    def addEdge(from: CFGVertex, e: CFGAdjacent, f: Expression) = {
      val fs = e.label match {
        case Assume(p) => 
          renameVariables(from, p) :: cfg.allVariables.toList.map(v => Equality(Variable(nameVariable(from, v)), Variable(nameVariable(e.to, v))))
        case Assign(Variable(lhs, _), rhs: Expression) => 
           cfg.allVariables.toList.map(v =>
             if (v == lhs) Equality(Variable(nameVariable(e.to, v)), renameVariables(from, rhs))
             else Equality(Variable(nameVariable(from, v)), Variable(nameVariable(e.to, v))))
        case Havoc(Variable(havocVar, _)) =>
           for (v <- cfg.allVariables.toList; if v != havocVar) yield Equality(Variable(nameVariable(from, v)), Variable(nameVariable(e.to, v)))
      }
      Manip.shortCircuit(fs.fold(f)(Conjunction(_, _)))
    }
    
    def checkChildren(v: CFGVertex, m: Map[CFGVertex, Expression]) {
      for (e <- cfg.transitions.getOrElse(v, Set())) {
        basicPaths += ((v, e) -> m.mapValues(addEdge(v, e, _)))
        
        if (notReady.contains(e.to) && parentSets(e.to).map(_._1).diff(processed).isEmpty) {
          notReady -= e.to
          ready = e.to :: ready
        }
        
        cfg.asserts.get(e.to).foreach({assertFormula =>
          for ((root, formula) <- basicPaths(v, e)) {
            result += Implication(formula, renameVariables(e.to, assertFormula))
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
      val es = parentSets(v)
      val ps = es.map(basicPaths)
      var m = Map[CFGVertex, Expression]()
      for (p <- ps) {
        for ((root, formula) <- p) {
          m.get(root) match {
            case None => m += (root -> formula)
            case Some(mFormula) => m += (root -> Conjunction(mFormula, formula))
          }
        }
      }
      m = m.mapValues(Manip.simplifyConjuncts)
      
      // mark as processed
      processed += v
      
      // check children
      checkChildren(v, m)
    }
    
    assert(notReady.isEmpty, "The CFG is not sufficiently annotated.")
    
    result
  }

  private def createParentSets(cfg: CFG): Map[CFGVertex, Set[(CFGVertex, CFGAdjacent)]] = {
    val edges = for ((v, es) <- cfg.transitions.toSet; e <- es) yield (v,e)
    edges groupBy {case (v,e) => e.to}     
  }
}
