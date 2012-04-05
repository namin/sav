package net.namin.sav

import scala.tools.nsc
import nsc.Global
import nsc.Phase
import nsc.plugins.Plugin
import nsc.plugins.PluginComponent

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.digraph.Vertex
import lazabs.prover.Prover
import lazabs.utils.Manip._
import lazabs.vcg.VCG
import lazabs.viewer.ScalaPrinter

class SavPlugin(val global: Global) extends Plugin {
  import global._

  val name = "sav"
  val description = "synthesis, analysis, verification"
  val components = List[PluginComponent](Component)
  
  private object Component extends PluginComponent with Sav {
    val global: SavPlugin.this.global.type = SavPlugin.this.global
    override val runsAfter = List[String]("cleanup")
    val phaseName = SavPlugin.this.name
    def newPhase(_prev: Phase) = new SavPhase(_prev)    
    
    class SavPhase(prev: Phase) extends StdPhase(prev) {
      override def name = SavPlugin.this.name
      def apply(unit: CompilationUnit) = go(unit)
    }
  }
}

trait Sav extends PluginComponent {
  import global._

  def go(unit: CompilationUnit) = {
    println("SAV: GO!")

    val traverser = new ForeachDefDefTraverser(analyzeDef)
    traverser.traverse(unit.body)
    
    println("SAV: Done GO!")
  }

  class ForeachDefDefTraverser(f: DefDef => Unit) extends ForeachPartialTreeTraverser({case t : DefDef =>
    f(t)
    EmptyTree
  })

  def analyzeDef(t: DefDef) {
    if (t.name.startsWith("test")) {
      println("SAV: Analyzing " + t.name)
      
      val cfgBuilder = new DefDefCFGBuilder
      cfgBuilder.build(t) match {
        case None => println("Error: Could not build CFG")
        case Some(cfg) =>   
	      val vcgs = VCG(cfg)
	      var verified = true
	      vcgs foreach { e => 
	        println("VCG:") 
	        println(ScalaPrinter(e))
	        println("Validity:") 
	        Prover.isSatisfiable(Not(e)) match {
	          case Some(true) => {println("Invalid"); verified = false}
	          case Some(false) => println("Valid")
	          case None => {println("Unknown"); verified = false}
	        }
	      }
	      if (verified) println("Program verification successful!")
	      else println("Program verification failed")      
      }
      println("SAV: Done Analyzing " + t.name)
    } else {
      println("SAV: Skipping " + t.name)
    }
  }
  class DefDefCFGBuilder extends Traverser {
    private val cfg = new CFG()
    private var ok = true
    private var labels = Map[Name,(Vertex,Vertex)]()
    private var next = cfg.newVertex
    private var nextLabel = cfg.error
    private var afterNextLabel = cfg.error
    cfg.start = next
    
    private def newNext = {
      val from = next
      next = cfg.newVertex
      (from, next)
    }

    private def addEdge(label: CFGLabel) = {
      val (from, to) = newNext     
      cfg += (from, label, to)
    }

    private def addAssert(e: Expression) = {
      val (from, to) = newNext
      cfg.asserts += (from -> e)
      cfg += (from, Assume(e), to)
      cfg += (from, Assume(simplify(Not(e))), cfg.error)
      nextLabel = from
      afterNextLabel = to
    }

    private def addAssign(v: String, rhs: Expression) = {
      addEdge(lazabs.cfg.Assign(Variable(v), rhs))
    }

    private def addLabel(n: Name) = {
      assert(nextLabel != cfg.error && afterNextLabel == next, "while loop must be preceded by assert!")
      labels += (n -> (nextLabel, afterNextLabel))
      nextLabel = cfg.error
      afterNextLabel = cfg.error
    }

    private def jumpTo(v: Vertex) = {
      cfg += (next, Assume(BoolConst(true)), v)
      next = v
    }

    def build(t: Tree) = {
      traverse(t)
      if (ok) Some(cfg) else None
    }
 
    override def traverse(t: Tree) { t match {
        case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          println("def " + name)
          for (vparams <- vparamss)
            cfg.variables ++= vparams.map(_.name.decode)
          traverse(rhs)
        case Block(stats, expr) => super.traverse(t)
        case ValDef(mods, name, tpt, rhs)=>
          val v = name.decode
          cfg.variables += v
          addAssign(v, expr(rhs))
        case LabelDef(name, List(), rhs @ If(cond, thenp, Literal(Constant(())))) =>
          addLabel(name)
          val conde = expr(cond)
          addEdge(Assume(conde))
          traverse(thenp)
          assert(labels(name)._2 == next)
          addEdge(Assume(simplify(Not(conde))))
        case If(cond, thenp, elsep) =>
          val from = next
          val conde = expr(cond)
          addEdge(Assume(conde))
          traverse(thenp)
          val end = next
          next = from
          addEdge(Assume(simplify(Not(conde))))
          traverse(elsep)
          jumpTo(end)
        case Assign(Ident(name), Apply(Select(_, fun), List())) if fun.decode == "havoc" =>
          addEdge(Havoc(Variable(name.decode)))
        case Assign(Ident(name), rhs) =>
          addAssign(name.decode, expr(rhs))
        case Apply(Select(_, fun), List(arg)) if fun.decode == "assume" =>
          addEdge(Assume(expr(arg)))
        case Apply(Select(_, fun), List(arg)) if fun.decode == "assert" =>
          addAssert(expr(arg))
        case Apply(Ident(name), List()) if labels.contains(name) =>
          jumpTo(labels(name)._1)
          next = labels(name)._2
        case Literal(Constant(())) => ()
        case _ =>
          println("missing case: " + t.getClass + ":" + t)
          ok = false
      }
    }
        
    def expr(t: Tree) = simplify((new ExpressionBuilder).build(t))
    class ExpressionBuilder {
      def build(t: Tree): Expression = t match {
        case Literal(Constant(value)) => value match {
          case x : Int => NumericalConst(x)
          case x : Boolean => BoolConst(x)
        }
        case Ident(name) => Variable(name.decode)
        case Apply(Select(lhs, op), List(rhs)) =>
          BinaryExpression(build(lhs), binaryOps(op.decode), build(rhs))
        case _ =>
          println("missing case in expression builder: " + t.getClass)
          ok = false
          null
      }
    }
  }

  val binaryOps = Map(
    "||" -> DisjunctionOp(),
    "&&" -> ConjunctionOp(),
    "==" -> EqualityOp(),
    "!=" -> InequalityOp(),
    "<" ->  LessThanOp(),
    "<=" -> LessThanEqualOp(),
    ">" ->  GreaterThanOp(),
    ">=" -> GreaterThanEqualOp(),
    "+" ->  AdditionOp(),
    "-" ->  SubtractionOp(),
    "*" ->  MultiplicationOp(),
    "/" ->  DivisionOp(),
    "%" ->  ModuloOp()
  )
}
