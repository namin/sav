package lazabs.art

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.cfg._
import lazabs.utils.Manip._
import lazabs.utils.Inline._
import lazabs.art.RTreeMethods._
import lazabs.prover.Prover._


object MakeRTree {
  def reset() {
    rTree = new RTree
    cfg = CFG(CFGVertex(-1),Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,None,Map.empty)
    search = SearchMethod.DFS
    shuffle = false
    spuriousness = false
    init = List()
    time = 0
    nodeHash.clear()
  }

  var rTree: RTree = new RTree
  var cfg = CFG(CFGVertex(-1),Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,None,Map.empty)
  
  /**
   * The search method for exploration of reachability tree
   */
  import SearchMethod._
  var search: SearchMethod = DFS
  var shuffle: Boolean = false
  /**
   * check the counter-example for spuriousness or not 
   */
  var spuriousness = false
  /**
   * initial values of global variables
   */
  var init: List[(Variable,Expression)] = List()
  /**
   * used for calculating the total time of computation
   */
  var time: Long = 0
  
  /**
   * Gets a Scala object and generates the reachability tree for the main function
   * @param o object ast
   * @param start the beginning vertex
   * @param loops the vertices that start a loop
   * @param adj the adjacency list
   */    
  def apply(cfg: CFG, loops: List[CFGVertex], spuriousness: Boolean, search: SearchMethod, shuffle: Boolean): RTree = {
    this.cfg = cfg
    this.spuriousness = spuriousness
    this.search = search
    this.shuffle = shuffle
    startTimer
    var initialAbstraction: List[Boolean] = Nil
    cfg.sobject match {
      case Some(so) => 
        this.init = MakeCFG.initialValues(so)
        val initForm = init.map(x => Equality(x._1, x._2)).foldLeft[Expression](BoolConst(true))(Conjunction(_,_))
        MakeCFG.initialPredicates(so).head.map(_._1).foreach(p => initialAbstraction = initialAbstraction ::: (isSatisfiable(Conjunction(initForm,Not(p))) match {
          case Some(false) => List(true)
          case _ => List(false)
        }))
      case None =>
    }
    search match {
      case DFS => rTree.start = makeRTreeDFS(cfg.start, initialAbstraction)
      case _ => makeRTreeQueue(cfg.start, initialAbstraction)
    }
    checkFailedAssertion
    report(loops,nodeHash)
    rTree
  }
  /**
   * the hash of nodes
   */
  var nodeHash = collection.mutable.Map[CFGVertex,List[RNode]]().empty  
  /**
   * Making a reachability tree for a given control flow graph with DFS method
   */  
  def makeRTreeDFS(vertex: CFGVertex, predAbs: List[Boolean]): RNode = {
    val currentPredSet = absToPredSet(predAbs, cfg.predicates.getOrElse(vertex,List()).map(_._1))
    val currentFormula = exprSetToFormula(currentPredSet)
    val node = RNode(freshNodeID, vertex.id, currentPredSet)
    if (vertex.id == -1) currentFormula match {
      case BoolConst(b) if (b == false) =>
        rTree.blockedNodes += node
        return node
      case _ =>        
        rTree.errorNodes += node
        return node
    }
    if (currentPredSet.contains(BoolConst(false))) { // the set is empty - the predicate false is true in this state
      rTree.blockedNodes += node
      return node
    }
    if (alreadyExplored(vertex, nodeHash, currentPredSet).isDefined) {
      rTree.exploredNodes += node
      return node
    }
    nodeHash += (vertex -> (nodeHash.getOrElse(vertex, List()) ::: List(node)))      
    cfg.transitions.get(vertex) match {
      case Some(adjacencies) =>
        val adjs: List[CFGAdjacent] = if(shuffle) scala.util.Random.shuffle(adjacencies).toList else adjacencies.toList.sortWith((e1, e2) => (e1.to.getId < e2.to.getId))
        adjs.foreach(adj => {
          val (transition,nvars,_) = transFormula(adj.label,cfg.variables.getOrElse(adj.to, Set()))
          val childAbs: List[Boolean] = nextState(currentFormula, cfg.predicates.getOrElse(adj.to, List()), transition)
          val childNode = makeRTreeDFS(adj.to, childAbs)
          rTree.parent += (childNode -> (node,adj.label))
          rTree.transitions += (node -> (rTree.getTransitions.getOrElse(node,Set.empty) ++ Set(RAdjacent(adj.label,childNode))))
        })
        node
      case None =>
        node
    }
  }
  
  /**
   * Making a reachability tree for a given control flow graph with BFS method
   */  
  def makeRTreeQueue(startVertex: CFGVertex, startPredAbs: List[Boolean]) {
    val startPredSet = absToPredSet(startPredAbs, cfg.predicates.getOrElse(startVertex,List()).map(_._1))
    val startFormula = exprSetToFormula(startPredSet)
    rTree.start = RNode(freshNodeID, startVertex.id, startPredSet)
    var queue: List[(CFGVertex,RNode,List[Boolean])] = List((startVertex,rTree.start,startPredAbs))  // CFG vertex, Reachability node, predicate vector
    while(queue.size != 0) {
      val next = search match {
        case PRQ =>
          queue.minBy(_._3.count(identity))
          //scala.util.Random.shuffle(queue).minBy(_._3.count(identity))
        case RND =>
          scala.util.Random.shuffle(queue).head          
        case _ =>
          queue.head
      }
      cfg.transitions.get(next._1) match {
        case Some(adjacencies) =>
          val adjs: List[CFGAdjacent] = if(shuffle) scala.util.Random.shuffle(adjacencies).toList else adjacencies.toList.sortWith((e1, e2) => (e1.to.getId < e2.to.getId)) 
            adjs.foreach(adj => {
            val (transition,nvars,_) = transFormula(adj.label,cfg.variables.getOrElse(adj.to,Set()))
            val childAbs: List[Boolean] = nextState(exprSetToFormula(next._2.getAbstraction), cfg.predicates.getOrElse(adj.to, List()), transition)
            val childPredSet = absToPredSet(childAbs, cfg.predicates.getOrElse(adj.to,List()).map(_._1))
            val childFormula = childPredSet.reduceLeft[Expression](Conjunction(_,_))
            val childNode = RNode(freshNodeID, adj.to.id, childPredSet)
            if(adj.to.id == -1) childFormula match {  // assertions
              case BoolConst(false) =>
                rTree.blockedNodes += childNode
                nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, List()) ::: List(childNode)))
              case _ =>
                rTree.errorNodes += childNode
            } else if(alreadyExplored(adj.to, nodeHash, childPredSet).isDefined)
              rTree.exploredNodes += childNode
              else if(childAbs.head) {  // the set is empty - the predicate false is true in this state
              //nodeHash = nodeHashUnion(nodeHash, collection.mutable.Map(adj.to -> List(childPredSet)))
              rTree.blockedNodes += childNode
            } else {
              nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, List()) ::: List(childNode)))
              val dups = queue.filter(x => x._1 == adj.to)   // there is already a node for the same CFG vertex in the queue
              if(dups.size != 0)
                dups.foreach(d => if(subset(childAbs,dups.head._3)) queue = queue.filterNot(_ == d))              
              queue :+= (adj.to,childNode,childAbs)
            }
            rTree.transitions += (next._2  -> (rTree.transitions.getOrElse(next._2, Set.empty) ++ Set(RAdjacent(adj.label,childNode))))
            rTree.parent += (childNode -> (next._2,adj.label))
          })
        case None =>
      }
      queue = queue.filterNot(_ == next)
    }
  }
  
  def getFormula(start: RNode, end: RNode, label: Label): Expression = cfg.getFormula(CFGVertex(start.getCfgId),CFGVertex(end.getCfgId),label)  
 
  def checkFailedAssertion {
    rTree.errorNodes.foreach(f => {
      var errorMessage = "The assertion in node ERROR(" + lazabs.viewer.ScalaPrinter(exprSetToFormula(f.getAbstraction)) + ") can fail" 
      (if(spuriousness) {
        val spur = isSpurious(f, rTree.parent, getFormula, init)
        errorMessage = errorMessage + (if(spur._1) ", the counter example is spurious: more predicates required."
            else ", the counter example is genuine. The program has a bug.")
      })
      println(errorMessage)
    })
    stopTimer
  }
}