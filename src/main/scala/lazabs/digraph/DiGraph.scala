package lazabs.digraph

import scala.collection.mutable

/* Mutable Directed Graph with Labels */

case class Vertex(id:Int) {
  override def toString = "v" + id
}

trait DiGraph[Label] {
  type Edge = (Vertex,Label,Vertex)
  def getVertices: Set[Vertex]
  def getEdges: Set[Edge]
  def in(v: Vertex) : Set[(Vertex, Label)]
  def out(v: Vertex) : Set[(Label, Vertex)]
  def += (from: Vertex, l: Label, to: Vertex) : Unit
  def -= (from: Vertex, l: Label, to: Vertex) : Unit
  //def labelMap[NewLabel](f : Label => NewLabel) : DiGraph[NewLabel]
  /*
  def merge(that: DiGraph[Label]) : Unit = {
    that.getEdges foreach { case (from, l, to) =>
      this += (from, l, to)
    }
  }
  */
  override def toString = {
    val vs = ("Vertices:" /:\ getVertices) (_ + "\n" + _)
    def edgeString(e: Edge) = e match {
      case (from, l, to) => from + " --" + l + "->" + to
    }
    val es = ("Edges:" /: getEdges) (_ + "\n" + edgeString(_))
    vs + "\n" + es
  }
}

class DiGraphImp[Label] extends DiGraph[Label] {
  private val vertices = mutable.Set[Vertex]()
  private val edges = mutable.Set[Edge]()
  private val inEdges = mutable.Map[Vertex,Set[(Vertex,Label)]]()
  private val outEdges = mutable.Map[Vertex,Set[(Label,Vertex)]]()

  def getVertices = vertices.toSet
  def getEdges = edges.toSet
  def in(v : Vertex)  = inEdges.getOrElse(v,Set())
  def out(v : Vertex) = outEdges.getOrElse(v,Set())

  private var vertexCount = 0
  def newVertex = { 
    vertexCount += 1
    new Vertex(vertexCount)
  }

  def +=(from : Vertex, l : Label, to : Vertex) = {
    edges += Tuple3(from,l,to)
    vertices += from
    vertices += to
    val os = outEdges.getOrElse(from,Set()) 
    outEdges += (from -> (os + Tuple2(l,to)))
    val ins = inEdges.getOrElse(to,Set()) 
    inEdges += (to -> (ins + Tuple2(from,l)))
  }
  def -=(from : Vertex, l : Label, to : Vertex) = {
    edges -= Tuple3(from,l,to)
    outEdges.get(from) match {
      case None =>
      case Some(es) => outEdges += (from -> (es - Tuple2(l,to)))
    }
    inEdges.get(to) match {
      case None =>
      case Some(es) => inEdges += (to -> (es - Tuple2(from,l)))
    }
  }
 
  /*
  def labelMap[NewLabel](f : Label => NewLabel) : DiGraph[NewLabel] = {
    val g = new DiGraphImp[NewLabel]
    var vertexMap = Map[Vertex, Vertex]()
    for (v <- vertices) {
      vertexMap += ((v, g.newVertex))
    }
    for (e <- edges) {
      g += (vertexMap(e.from), f(e.l), vertexMap(e.to))
    }
    g
  }
  */
}
