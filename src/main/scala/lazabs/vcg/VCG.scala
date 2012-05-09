package lazabs.vcg

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.digraph._
import lazabs.utils.Manip

object VCG {
  class Node(val vertices: Set[Int], val from: Int, val to: Int, val e: Expression) {
    override def equals(o: Any) = {
      val no = o.asInstanceOf[Node]
      no != null && no.from == from && no.to == to
    }
    override def hashCode() = {
      from + 7*to
    }
    override def toString() = {
      "Node(" + from + ", " + to + ")"
    }
  }
  class Graph(val nodes: Set[Node], val transitions: Map[Node, Set[(Node,Expression)]]) {
    def merge(a: Node, b: Node) = {
      val fromA = transitions(a)
      assert(fromA.nonEmpty && fromA.forall(_._1 == b))
      val exps = fromA.map(_._2)
 
      val ab = new Node(a.vertices union b.vertices, a.from, b.to, Manip.simplify(
          Conjunction(a.e, Conjunction(b.e, exps.fold(BoolConst(false))(Disjunction(_, _))))))
      val new_nodes = nodes - a - b + ab
      assert(new_nodes.size == nodes.size-1)

      val fromB = transitions(b)

      var new_transitions = transitions
      new_transitions -= a
      new_transitions -= b
      new_transitions += (ab -> fromB)
      new_transitions = new_transitions.map({case (from, s) =>
        assert(!s.exists(_._1 == b))
        (from -> s.map({case (to, e) => (if (to == a) ab else to, e)}))
      })

      new Graph(new_nodes, new_transitions)
    }
    
    def mergeAll(except: Set[Int]) = {
      var did = true
      var graph = this
      while (did) {
        did = false

        val seq = for (a <- graph.nodes.toSeq;
        if !a.vertices.exists(except.contains(_));
        fromA = graph.transitions(a);
        if fromA.nonEmpty;
        b = fromA.first._1;
        if !b.vertices.exists(except.contains(_));
        if fromA.forall(_._1 == b);
        if graph.transitions.forall({case (from, s) => from == a || s.forall(_._1 != b)})) yield (a, b)
        
        if (seq.nonEmpty) {
          val (a, b) = seq.first
          did = true
          graph = graph.merge(a, b)
        }
      }
      graph
    }
  }

  def build(cfg: CFG) = {
    def nameVariable(vertex: Vertex, variable: String) = {
      variable + "$" + vertex.id
    }

    def renameVariables(vertex: Vertex, f: Expression) = {
      Manip.subst(f, cfg.variables.map(v => (v, Variable(nameVariable(vertex, v)))).toMap)
    }

    def edge2expr(edge: cfg.Edge) = {
      val (from, label, to) = edge
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
      Manip.simplify(fs.fold(BoolConst(true))(Conjunction(_, _)))
    }
    
    def vertex2node(v: Vertex) = {
      new Node(Set(v.id), v.id, v.id, BoolConst(true))
    }

    val nodes = cfg.getVertices.map(vertex2node)
    val transitions = cfg.getVertices.map(from => (vertex2node(from) -> cfg.out(from).map({ case(label, to) =>
      (vertex2node(to), edge2expr((from, label, to)))
    }))).toMap
    val asserts = for ((v,e) <- cfg.asserts.toMap) yield (v.id -> renameVariables(v, e))
    (new Graph(nodes, transitions), asserts)
  }
  
 
  /*
   * Returns a set of verification conditions that imply the correctness of the annotations in the given CFG
   * or null if the CFG is not sufficiently annotated.
   */
  def apply(cfg: CFG) : Set[Expression] = {
    val (graph, asserts) = build(cfg)
    val mergedGraph = graph.mergeAll(asserts.keySet)
    vcs(mergedGraph, cfg.start.id, asserts)
  }
  
  def vcs(graph: Graph, start: Int, asserts: Map[Int, Expression]): Set[Expression] = {
    var result = Set[Expression]()
    
    val parents = 
      (for ((from, s) <- graph.transitions.toSet;
       (to, e) <- s) yield (to -> (from, e))).groupBy(_._1).mapValues(_.map(_._2))
    
    val initVertices = asserts.keySet.union(Set(start))
    val init = graph.nodes.filter(node => node.vertices.exists(initVertices.contains(_)))
    var processed = Set[Node]()
    var ready = List[Node]()
    var notReady = graph.nodes.diff(init)

    var basicPaths = Map[(Node, Node), Map[Node, Expression]]()
    
    def addEdge(edge: (Node, Expression, Node), f: Expression) = {
      val (from, e, to) = edge
      Manip.simplify(Conjunction(from.e, Conjunction(e, f)))
    }
    
    def checkChildren(v: Node, m: Map[Node, Expression]) {
      for ((to, e) <- graph.transitions(v)) {
        basicPaths += ((v, to) -> m.mapValues(addEdge((v, e, to), _)))
        
        if (notReady.contains(to) && parents(to).map(_._1).diff(processed).isEmpty) {
          notReady -= to
          ready = to :: ready
        }
        
        asserts.get(to.from).foreach({assertFormula =>
          for ((root, formula) <- basicPaths(v, to)) {
            result += Implication(formula, assertFormula)
          }
        })
      }
    }
    
    // initialization step
    for (v <- init) {
      val m = asserts.get(v.from) match {
        case None => Map(v -> BoolConst(true))
        case Some(e) => Map(v -> e)
      }
      processed += v
      checkChildren(v, m)
    }

    while (!ready.isEmpty) {
      // take any ready node
      val v = ready.head
      ready = ready.tail

      // merge all incoming formulas
      val es = parents(v).map(t => (t._1, v))
      val ps = es.map(basicPaths)
      var m = Map[Node, Expression]()
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
    
    if (notReady.isEmpty) result
    else null // The CFG is not sufficiently annotated.
  }
}
