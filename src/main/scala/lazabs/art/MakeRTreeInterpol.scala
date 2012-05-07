package lazabs.art

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.cfg._
import lazabs.utils.Manip._
import lazabs.utils.Inline._
import lazabs.art.RTreeMethods._
import lazabs.prover.Prover._
import lazabs.prover.PrincessWrapper._
import lazabs.nts.AccelerationStrategy._
import lazabs.nts._


object MakeRTreeInterpol {
  def reset() {
    rTree = new RTree
    queue = List()
    cfg = CFG(CFGVertex(-1),Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,None,Map.empty)
    search = SearchMethod.DFS
    log = false
    accelerate = false
    underApproximate = false
    bapaRewrite = false
    init = List()
    reusableRoots = Set()
    predMap = collection.mutable.Map().empty
    hasBug = false
    cacheReuse = 0
    nodeHash = collection.mutable.Map().empty
  }

  var rTree: RTree = new RTree
  var queue: List[RNode] = List()
  var cfg = CFG(CFGVertex(-1),Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,None,Map.empty)
  /**
   * The search method for exploration of reachability tree
   */
  import SearchMethod._
  var search: SearchMethod = DFS
  /**
   * Putting the interpolants in a log file
   */
  var log: Boolean = false
  /**
   * Dynamic acceleration
   */
  var accelerate: Boolean = false
  /**
   * under-approximation of loops
   */
  var underApproximate: Boolean = false
  /**
   * Rewriting a BAPA formula into Presburger
   */
  var bapaRewrite: Boolean = false
  /**
   * initial values of global variables
   */
  var init: List[(Variable,Expression)] = List()  
  /**
   * caching previous nodes
   */
  var reusableRoots = Set[RNode]()
  /**
   * mapping from CFG vertex to the set of predicates
   */
  var predMap = collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]]().empty
  /**
   * if the program has a bug or not
   */
  var hasBug = false
 
  /**
   * Gets a control flow graph and generates the reachability tree
   * @param cfg control flow graph
   * @param loops the vertices that start a loop
   * @param log writes the abstraction information in a file when drawing reachability tree 
   */  
  def apply(cfg: CFG, loops: List[CFGVertex], search: SearchMethod, bapaRewrite: Boolean, accelerate: Boolean, underApproximate: Boolean, log: Boolean): RTree = {
    this.cfg = cfg
    this.search = search
    this.accelerate = accelerate
    this.underApproximate = underApproximate
    this.log = log
    this.bapaRewrite = bapaRewrite
    this.predMap = collection.mutable.Map() ++ cfg.predicates   // the predicates change during refinement
    cfg.sobject match {
      case Some(so) => init = MakeCFG.initialValues(so)
      case None =>
    }
    startTimer
    queue ::= constructARTNode(cfg.start,BoolConst(true))
    makeRTree
    rTree.start = rTree.getTransitions.keys.find(_.cfgId == cfg.start.id) match{
      case Some(n) => n
      case None => RNode(-1,cfg.start.id,Set[Expression]().empty)
    }    
    checkFailedAssertion
    if(!hasBug)
      println("==================== No Error Found ====================")
    report(loops,nodeHash)
    rTree
  }
  
  /**
   * constructs a reachability node from the given vertex
   */
  def constructARTNode(st: CFGVertex, initAbs: Expression): RNode = {
    var initialAbstraction: List[Boolean] = Nil
    var currentPredicates = predMap.getOrElse(st,List((BoolConst(false),List())))
    var initForm: Expression = initAbs
    if(st == cfg.start) cfg.sobject match {
      case Some(so) =>
        initForm = init.map(x => Equality(x._1, x._2)).foldLeft[Expression](BoolConst(true))(Conjunction(_,_))
        currentPredicates = (currentPredicates ::: MakeCFG.initialPredicates(so).head).distinct
      case None =>
    }
    currentPredicates.map(_._1).foreach(p => initialAbstraction = initialAbstraction :::
      (if(p == Variable("sc_LBE",None)) List(false) else (lazabs.prover.Prover.isSatisfiable(Conjunction(initForm,Not(p))) match {
        case Some(false) => List(true)
        case _ => List(false)
    })))
    RNode(freshNodeID, st.id, absToPredSet(initialAbstraction, predMap.getOrElse(st,List()).map(_._1)))
  }
  
  var cacheReuse = 0
  /**
   * adds a subtree to the current reachability tree  
   */
  def addSubtree(root: RNode): Unit = {
    alreadyExplored(CFGVertex(root.getCfgId), nodeHash, root.getAbstraction) match {
      case Some(weaker) if(!rTree.getBlockedNodes.contains(root)) =>
        val explored = RNode(freshNodeID, root.getCfgId, root.getAbstraction)
        rTree.subsumptionRelation += (weaker -> (rTree.subsumptionRelation.getOrElse(weaker,Set()) + explored))
        rTree.getParent.get(root) match {
          case Some(papa) =>
            rTree.transitions = (rTree.transitions + (papa._1 -> (rTree.transitions.getOrElse(papa._1, Set.empty) + RAdjacent(papa._2,explored) - RAdjacent(papa._2,root)))).filterNot(_._2.size == 0)
            rTree.parent += (explored -> (papa._1,papa._2))          
          case None =>
        }
        pruneChildren(root)
        rTree.setTransitions(rTree.getTransitions - root)
        rTree.setParent(rTree.getParent - root)        
      case _ =>
        nodeHash += (CFGVertex(root.getCfgId) -> (nodeHash.getOrElse(CFGVertex(root.getCfgId), Set()) + root))
        cacheReuse += 1
        rTree.getTransitions.get(root) match {
          case Some(adjs) =>
            val cacheSubsumedAdjs = adjs.filter(adj => rTree.cacheSubsumedNodes.exists(_ == adj.to))
            if(cacheSubsumedAdjs.size != 0) {
              val cacheUnsubsumedAdjs = adjs.filterNot(adj => rTree.cacheSubsumedNodes.exists(_ == adj.to))
              rTree.transitions = (rTree.transitions + (root -> (rTree.transitions.getOrElse(root, Set.empty) -- cacheSubsumedAdjs))).filterNot(_._2.size == 0)
              cacheSubsumedAdjs.map(_.to).foreach{cSub =>
                rTree.cacheSubsumedNodes -= cSub
                rTree.parent -= cSub
              }
              cacheUnsubsumedAdjs.map(_.to).map(addSubtree)
              queue +:= root
            } else
              adjs.map(adj => addSubtree(adj.to))
          case None =>
            if(!rTree.getBlockedNodes.contains(root) && !rTree.cacheSubsumedNodes(root))
              queue :+= root
        }
    }
  }
  
  /**
   * the hash of nodes
   */
  var nodeHash = collection.mutable.Map[CFGVertex,Set[RNode]]().empty
  /**
   * Making a reachability tree for a given control flow graph
   */  
  def makeRTree {
    while(queue.size != 0 && rTree.errorNodes.size == 0) {
      val reusableRootsM = reusableRoots.map(_.getCfgId)
      val cur = queue.find(rr => !reusableRootsM.contains(rr.getCfgId)) match {
        case Some(n) => n
        case None => search match {
          case PRQ =>
            queue.minBy(_.getAbstraction.size)
          case RND =>
            scala.util.Random.shuffle(queue).head
          case _ =>
            queue.head
        }
      }
      cfg.transitions.get(CFGVertex(cur.getCfgId)) match {
        case Some(adjs) =>
          //val adjs: List[CFGAdjacent] = if(shuffle) scala.util.Random.shuffle(adjacencies).toList else adjacencies.toList.sortWith((e1, e2) => (e1.to.getId < e2.to.getId))
          val it = adjs.toList.iterator
          while(rTree.errorNodes.size == 0 && it.hasNext) {
            val adj = it.next
            if(rTree.transitions.get(cur) match {
                case Some(ina) => (if (ina.map(_.to.getCfgId).contains(adj.to.id)) false else true)
                case None => true}) {
              val childAbs: List[Boolean] = nextState(exprSetToFormula(cur.getAbstraction), predMap.getOrElse(adj.to, List()), cfg.getFormula(CFGVertex(cur.getCfgId),adj.to,adj.label))
              val childPredSet = absToPredSet(childAbs, predMap.getOrElse(adj.to,List()).map(_._1))
              val childFormula = exprSetToFormula(childPredSet)
              var childNode: RNode = if(childPredSet.contains(BoolConst(false))) {
                val blocked = RNode(freshNodeID, adj.to.id, childPredSet)
                rTree.blockedNodes += blocked
                nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, Set()) + blocked))
                blocked
              } else {
                if(adj.to.id == -1) {
                  val error = RNode(freshNodeID, adj.to.id, childPredSet)
                  rTree.errorNodes += error
                  error
                } else {
                  alreadyExplored(adj.to, nodeHash, childPredSet) match {
                    case Some(weaker) =>
                      val explored = RNode(freshNodeID, adj.to.id, childPredSet)
                      rTree.subsumptionRelation += (weaker -> (rTree.subsumptionRelation.getOrElse(weaker,Set()) + explored))
                      explored
                    case None =>
                      reusableRoots.find(rr => rr.getCfgId == adj.to.id && rr.getAbstraction == childPredSet) match {
                        case Some(reuse) =>
                          addSubtree(reuse)
                          reusableRoots -= reuse
                          reuse
                        case None =>
                          val unfinished = RNode(freshNodeID, adj.to.id, childPredSet)
                          nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, Set()) + unfinished))
                          val dups = queue.filter(x => x.getCfgId == adj.to.getId)   // there is already a node for the same CFG vertex in the queue
                          if(dups.size != 0) {
                            dups.foreach{
                              d => if(childPredSet.subsetOf(d.getAbstraction)) {
                                queue = queue.filterNot(_ == d)
                                rTree.subsumptionRelation += (unfinished -> (rTree.subsumptionRelation.getOrElse(unfinished,Set()) + d))
                                nodeHash = (nodeHash + (adj.to -> (nodeHash.getOrElse(adj.to,Set()) - d))).filterNot(_._2.size == 0)
                              }
                            }
                          }
                          queue :+= unfinished
                          unfinished
                      }
                  }
                }
              }
              rTree.transitions += (cur -> (rTree.transitions.getOrElse(cur, Set.empty) ++ Set(RAdjacent(adj.label,childNode))))
              rTree.parent += (childNode -> (cur,adj.label))
            }
          }
        case None =>
      }
      queue = queue.filterNot(_ == cur)
    }
  }
  
  /**
   * Prunes the reachability tree from the prune node
   * @post: Every children from prune are removed
   * @invariant: Does not change the subsumption relation
   */
  def pruneChildren(prune: RNode): Unit = {
    if(reusableRoots.contains(prune))
      return
    rTree.getTransitions.get(prune) match {
      case Some(s) =>
        rTree.setTransitions(rTree.getTransitions - prune)         
        s.foreach(ra => {
          queue = queue.filterNot(_ == ra.to)
          rTree.setParent(rTree.getParent - ra.to)
          nodeHash = (nodeHash + (CFGVertex(ra.to.getCfgId) -> (nodeHash.getOrElse(CFGVertex(ra.to.getCfgId),Set()) - ra.to))).filterNot(_._2.size == 0)
          pruneChildren(ra.to)
        })
      case None =>
        rTree.setBlockedNodes(rTree.getBlockedNodes - prune)
        rTree.setErrorNodes(rTree.getErrorNodes - prune)
    }
  }
  
  /**
   * Adjusts the subsumption relation after pruning
   */
  def adjustSubsumption(mainTreeNodes: Set[RNode], cacheNodes: Set[RNode]) {
    // ############# marking the explored nodes in the cache nodes #############
    rTree.getSubsumptionRelation.map(el => (el._1,el._2.filter(cacheNodes.contains))).values.foldLeft(Set[RNode]())(_++_).foreach {cSub =>
      val os = RNode(freshNodeID, cSub.getCfgId, cSub.getAbstraction)
      rTree.cacheSubsumedNodes += os
      rTree.getParent.get(cSub) match {
        case Some(papa) =>
          rTree.transitions += (papa._1 -> (rTree.transitions.getOrElse(papa._1, Set.empty) + RAdjacent(papa._2,os) - (RAdjacent(papa._2,cSub))))
          rTree.parent += (os -> (papa._1,papa._2))
        case None =>
      }
      rTree.setTransitions(rTree.getTransitions - cSub)
      rTree.setParent(rTree.getParent - cSub)
    }
    // ############# removing the explored nodes in the main tree #############
    val mainPushBackNodes = rTree.getSubsumptionRelation.filter(el => !mainTreeNodes.contains(el._1)).map(el => (el._1,el._2.filter(mainTreeNodes.contains))).values.foldLeft(Set[RNode]())(_++_)
    mainPushBackNodes.foreach {mSub =>
      rTree.getParent.get(mSub) match {
        case Some(papa) =>
          rTree.transitions = (rTree.transitions + (papa._1 -> (rTree.transitions.getOrElse(papa._1, Set.empty) - (RAdjacent(papa._2,mSub))))).filterNot(_._2.size == 0)
          if(!queue.contains(papa._1))
            queue +:= papa._1
        case None =>
      }
      rTree.setParent(rTree.getParent - mSub)
    }
    rTree.setSubsumptionRelation(rTree.getSubsumptionRelation.filter(el => mainTreeNodes.contains(el._1)).map(el => (el._1,el._2.filter(mainTreeNodes.contains))).filter(_._2.size != 0))
  }
   
  /**
   * returns the roots of the directly connected subtree to the spurious path
   */
  def subtreesRoots(p: List[RNode]): Set[RNode] = p.map(rTree.getTransitions.get(_) match {
    case Some(adjs) => adjs.filterNot(x => (p.contains(x.to) || (x.to.getCfgId == -1) || (rTree.getSubsumptionRelation.values.foldLeft(Set[RNode]())(_++_).exists(_ == x.to)) || (rTree.getBlockedNodes.contains(x.to)))).map(_.to)
    case None => Set()
  }).foldLeft[Set[RNode]](Set())(_++_)
  
  /**
   * returns 
   * 1- every node in the subtree
   * 2- unfinished leaves
   */
  def allNodes(root: RNode): (Set[RNode],Set[RNode]) = rTree.getTransitions.get(root) match {
    case Some(adjs) =>
      val rest = adjs.map(adj => allNodes(adj.to))
      (Set(root) ++ rest.map(_._1).foldLeft[Set[RNode]](Set())(_ union _),
          (if(queue.contains(root)) Set(root) ++ rest.map(_._2).foldLeft[Set[RNode]](Set())(_ union _) else rest.map(_._2).foldLeft[Set[RNode]](Set())(_ union _)))
    case None =>
      if(!rTree.getBlockedNodes.contains(root) && !rTree.getSubsumptionRelation.values.foldLeft(Set[RNode]())(_++_).exists(_ == root))
        (Set(root),Set(root))
      else 
        (Set(root),Set())
  }  
  /**
   * It looks for repeated subpaths and labels the repeated subpaths with TransitiveClosure
   */
  def findRepetitivePaths(path: List[(RNode,Label)]): List[(RNode,Label)] = {
    var suffixes = new Array[List[(RNode,Label)]](path.size)
    for (i <- 0 until path.size)
      suffixes(i) = path.takeRight(path.size - i)
    var i, j = 0
    var startLoopIndex,finishLoopIndex = 0
    var found = false
    while((i < suffixes.size) && !found) {
      j = i + 1
      while((j < (i + 1 + suffixes(i).size / 2)) && !found) {
        if(suffixes(i).take(j - i).map(x => (x._1.getCfgId,x._2)) == suffixes(j).take(j - i).map(x => (x._1.getCfgId,x._2))) {
          found = true
          startLoopIndex = i
          finishLoopIndex = j
        }
        j = j + 1
      }
      i = i + 1
    }
    if(found) {
      println("dynamic acceleration")
      val loop = path.slice(startLoopIndex,finishLoopIndex)
      val label = TransitiveClosure(loop.map(_._2),loop.tail.map(x => CFGVertex(x._1.getCfgId)))
      (path.take(startLoopIndex) ::: List((path(startLoopIndex)._1,label)) ::: path.slice(2*finishLoopIndex-startLoopIndex,path.size))
    }
    else path
  }

  /**
   * gets the index of a loop in a path
   */
  def getLoopIndex(path: List[(RNode,Label)]): Int = path.indexWhere(_._2 match {
    case TransitiveClosure(_,_) =>
      true
    case _ => false
  })
  
  /**
   * get formulas of a path leading to error
   */
  def getPathToErrorFormula(path: List[(RNode,Label)]): List[Expression] = {
    (path.zip(path.tail).map(el => getFormula(el._1._1,el._2._1,el._1._2)) :+ getFormula(path.last._1,rTree.errorNodes.head,path.last._2)).map(shortCircuit)    
  }
  
  /**
   * get formulas of a path
   */
  def getPathFormula(path: List[(RNode,Label)], end: RNode): List[Expression] = {
    (path.zip(path.tail).map(el => getFormula(el._1._1,el._2._1,el._1._2)) :+ getFormula(path.last._1,end,path.last._2)).map(shortCircuit)    
  }  
  /**
   * Replace transitive closure by approximation
   * @return the list of formulas containing approximation, the formula for acceleration, preciseness of the result 
   */
  def approximatePath(path: List[(RNode,Label)],method: AccelerationStrategy): (List[Expression],Expression,Boolean) = {
    val loopIndex = getLoopIndex(path)
    if(loopIndex < 0) return (getPathToErrorFormula(path),BoolConst(false),true)
    var precise = false
    var acceleratedExpr: Expression = BoolConst(false)
    val prefix = if(loopIndex == 0) List(BoolConst(true)) else path.slice(0,loopIndex).zip(path).map(el => getFormula(el._1._1,el._2._1,el._1._2))
    ((path.zip(path.tail).map (el => el._1._2 match {
      case TransitiveClosure(t,_) =>
        val (v: Expression, p: Boolean) = FlataWrapper.accelerate(lazabs.cfg.AccelerationRule.label2lists(t.reduceLeft(Sequence(_,_))),method,prefix)
        precise = p
        acceleratedExpr = elimQuantifiers(v)
        acceleratedExpr
      case _ => getFormula(el._1._1,el._2._1,el._1._2)
    }) :+ getFormula(path.last._1,rTree.errorNodes.head,path.last._2)).map(shortCircuit),acceleratedExpr,precise) 
  }
  
  def getFormula(start: RNode, end: RNode, label: Label): Expression = cfg.getFormula(CFGVertex(start.getCfgId),CFGVertex(end.getCfgId),label)
  
  def checkFailedAssertion {
    if(rTree.errorNodes.size == 0) {
      stopTimer
      return
    }
    val (spur,path) = isSpurious(rTree.errorNodes.head,rTree.parent,getFormula,init)
    val wholePath = pathToRoot(rTree.errorNodes.head,rTree.parent) 
    val pathRest = wholePath.dropRight(path.size)
    val repetitivePath = (if(accelerate && spur) findRepetitivePaths(path) else path)
    val loopId = if(getLoopIndex(repetitivePath) >= 0) repetitivePath(getLoopIndex(repetitivePath))._1.getId 
    // getting the formulas of a path. The last formula is between the last state in the path to the error state
    if(repetitivePath.head._1.getId == -1)  // there are global variables inside Scala input
      rTree.transitions += (repetitivePath.head._1 -> (rTree.transitions.getOrElse(repetitivePath.head._1, Set.empty) + RAdjacent(repetitivePath.head._2,repetitivePath.tail.head._1)))
    val (formulas,e:Expression, precise: Boolean) = approximatePath(repetitivePath,OVER_APPROX)
    if(spur && getLoopIndex(repetitivePath) >= 0) {
      if(precise)
        exactAcc
      val sPath = pathRest ::: (repetitivePath.map(_._1).zip(formulas.map(Transfer(_))))
      val parent: Map[RNode,(RNode,Label)] = (((pathRest ::: repetitivePath).tail.map(_._1) :+ rTree.errorNodes.head).zip(sPath)).toMap
      def localGetFormula(r1: RNode,r2: RNode,l: Label): Expression = {
        val rr = ((if(pathRest.size == 0) List() else pathRest.map(_._1).zip(getPathFormula(pathRest,repetitivePath.head._1))) ::: repetitivePath.map(_._1).zip(formulas)) :+ (rTree.errorNodes.head,BoolConst(false))
        rr.zip(rr.tail).find {
          case (a,b) => 
            (a._1 == r1) && (b._1 == r2)
        } match {
          case Some(ss) => ss._1._2
          case None =>
            BoolConst(false)
        }
      }
      val (newSpur,newPath) = isSpurious(rTree.errorNodes.head,parent,localGetFormula,init)
      (newSpur,precise) match {
        case (false,true) =>
          stopTimer
          println("The program has a bug")
          report
          sys.exit(0)
        case (false,false) =>
          println("Retreating from over-approximation")
          unsuccessfulOverAcc
          if(underApproximate) {
            println("under-approximation")
            val (uFormulas,uAccExpr,_) = approximatePath(repetitivePath,UNDER_APPROX)
            refinement(repetitivePath.map(_._1).zip(uFormulas),repetitivePath(getLoopIndex(repetitivePath))._1.getId,repetitivePath(getLoopIndex(repetitivePath))._2)
          } else {
            refinement(path.map(_._1).zip(getPathToErrorFormula(path)))
          }
          reconstructTree(path.map(_._1))
        case _ =>
          if(!precise)
            successfulOverAcc
          val removalPath = if(wholePath.indexWhere(_ == newPath.head) >= 0)
            wholePath.slice(wholePath.indexWhere(_ == newPath.head),wholePath.size) else path
          val newLoopIndex = newPath.indexWhere(_._1.getId == loopId)
          refinement(newPath.map{
            case (rn,Transfer(t)) => (rn,t)
            case (rn,la@_) => (rn,transFormula(la, Set())._1)
          },repetitivePath(getLoopIndex(repetitivePath))._1.getId,repetitivePath(getLoopIndex(repetitivePath))._2)
          reconstructTree(removalPath.map(_._1))
      }
    } else if(spur && !(getLoopIndex(repetitivePath) >= 0)) {
        //if(bapaRewrite) formulas = formulas.map(lazabs.bapa.BapaRewrite(_))
      refinement((path.map(_._1)).zip(getPathToErrorFormula(path)))
      reconstructTree(path.map(_._1))
    }
    else if(!spur) {
      stopTimer
      hasBug = true
      if(lazabs.nts.NtsWrapper.stateNameMap.size != 0) {
        def errorPath(current: RNode): List[RNode] = rTree.getParent.get(current) match {
          case Some(papa) => errorPath(papa._1) :+ current
          case None => List(current)
        }
        println("The program has a bug in the following path: " + errorPath(rTree.errorNodes.head).map(x => lazabs.nts.NtsWrapper.stateNameMap.getOrElse(x.getCfgId,"")))
      }
      else
        println("The program has a bug")
    }
  }
  
  /**
   * finds the interpolants for a spurious path and populates the predicate map with new predicates
   * @return true if approximated acceleration succeeds 
   */
  def refinement(oPath: List[(RNode,Expression)], loopNodeId: Int = -1, loopLabel: Label = Assume(BoolConst(true))) {
    val oInterpolants = pathInterpols(forwardSSA(oPath.map(_._2)).map(shortCircuit))
    if(oInterpolants.size == 0) {
      println("Fatal Error: No interpolants found")
      sys.exit(0)
    }
    if(log) println("Interpolants: " + oInterpolants.map(lazabs.viewer.ScalaPrinter(_)).mkString(" , "))
    val path = oPath.drop(oInterpolants.indexWhere(_ != BoolConst(true)))     // getting the shortest suffix, if any
    var interpolants = oInterpolants.dropWhile(_ == BoolConst(true))          // getting the shortest suffix, if any
    //lazabs.viewer.DrawGraph(rTree,false)
    //Console.readLine
    val loopIndex = path.zip(path.tail).indexWhere{
      case (a,b) => 
        (a._1.getId == loopNodeId)
    }
    if(loopIndex >= 0) {
      val accelerationImage = sp((if(loopIndex == 0) BoolConst(true) else interpolants(loopIndex - 1)),Transfer(path(loopIndex)._2))
      val interpolantFreeVars1 = (if(loopIndex == 0) Set() else freeVars(interpolants(loopIndex - 1)))
      val interpolantFreeVars2 = freeVars(interpolants(loopIndex))
      val imageFreeVars = freeVars(accelerationImage)
      val inductiveInterpolant = elimQuantifiers(deBruijnIndex((imageFreeVars -- (interpolantFreeVars1 ++ interpolantFreeVars2)).foldLeft[Expression](accelerationImage)((a,b) => Existential(BinderVariable(b.name).stype(b.stype),a))))
      interpolants = interpolants.updated(loopIndex,inductiveInterpolant)
      if(loopIndex != 0) interpolants = interpolants.updated(loopIndex - 1,BoolConst(false))
      loopLabel match {
        case TransitiveClosure(labels,states) if (labels.size > 1) =>
          val localPath = (List(CFGVertex(path(loopIndex)._1.getCfgId)) ::: states ::: List(CFGVertex(path(loopIndex)._1.getCfgId))).zip(labels :+ Assume(BoolConst(true)))
          val localPathFormulas: List[Expression] = List(prime(inductiveInterpolant)) ::: ((localPath).zip(localPath.tail)).map(el => cfg.getFormula(el._1._1,el._2._1,el._1._2)) ::: List(Not(inductiveInterpolant))
          val interInterpols = pathInterpols(forwardSSA(localPathFormulas).map(shortCircuit))
          (states.zip(interInterpols.slice(1,interInterpols.size - 1))).foreach(sti => {
            predMap.update(sti._1,(predMap.getOrElse(sti._1,List((BoolConst(false),List()))) ::: List((sti._2,List()))).distinct)
          })
        case _ =>
      }
    }
    path.tail.zip(interpolants).filterNot(_._2 == BoolConst(false)).foreach(p => {
      val vertex = CFGVertex(p._1._1.getCfgId)
      predMap.update(vertex,(predMap.getOrElse(vertex,List((BoolConst(false),List()))) ::: List((p._2,List()))).distinct)
    })
  }
  
  /**
   * reconstruct a tree after a spurious path is found
   * it should normally come after interpolation finds new predicates
   */  
  def reconstructTree(path: List[RNode]) {
    // ************** start of caching **************
    reusableRoots ++= subtreesRoots(path)
    val reusableRootChildren = reusableRoots.map(allNodes)  // all nodes in the subtree,  unfinished leaves
    val allNodesInSubtrees =
      (for (l <- reusableRootChildren.map(_._1).iterator; e <- l.iterator) yield e).toSeq
    val openNodesInSubtrees =
      (for ((_, s) <- reusableRootChildren.iterator; e <- s.iterator) yield e).toSet
    queue = queue.filterNot(openNodesInSubtrees.contains)  // removing the unfinished nodes
    nodeHash = collection.mutable.Map().empty ++ nodeHash.mapValues(_ -- allNodesInSubtrees).filterNot(_._2.size == 0)
    // ************** end of caching **************
    //lazabs.viewer.DrawGraph(rTree,true)
    //Console.readLine
    pruneChildren(path.head)
    adjustSubsumption(allNodes(rTree.getStart)._1,(allNodesInSubtrees.toSet -- openNodesInSubtrees.toSet))
    if (path.head.getCfgId == cfg.start.getId || path.head.getId == -1) {  // path.head is -1 when there are global variables in the original Scala file 
      queue :+= constructARTNode(cfg.start,BoolConst(true))
      makeRTree
    }
    else {
      rTree.getParent.get(path.head) match {
        case Some(par) =>
          val newNode = constructARTNode(CFGVertex(path.head.getCfgId),exprSetToFormula(par._1.getAbstraction))
          queue :+= newNode
          rTree.transitions += (par._1 -> (rTree.transitions.getOrElse(par._1, Set.empty) + RAdjacent(par._2,newNode)))
          nodeHash += (CFGVertex(newNode.getCfgId) -> (nodeHash.getOrElse(CFGVertex(newNode.getCfgId), Set()) + newNode))
          rTree.parent += (newNode -> (par._1,par._2))          
          rTree.transitions = (rTree.transitions + (par._1 -> (rTree.transitions.getOrElse(par._1, Set.empty) - (RAdjacent(par._2,path.head))))).filterNot(_._2.size == 0)
          nodeHash = (nodeHash + (CFGVertex(path.head.getCfgId) -> (nodeHash.getOrElse(CFGVertex(path.head.getCfgId),Set()) - path.head))).filterNot(_._2.size == 0)
          rTree.transitions = rTree.getTransitions.filterNot(_._1 == path.head)
          rTree.parent -= path.head
          queue = queue.filterNot(_ == path.head)
          makeRTree
        case None =>
      }
    }
    checkFailedAssertion
  }
}
