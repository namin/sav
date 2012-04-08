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
import scala.collection.mutable

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

    val collector = new ForeachVerifyDefTraverser(collectDef)
    collector.traverse(unit.body)

    val analyzer = new ForeachVerifyDefTraverser(analyzeDef)
    analyzer.traverse(unit.body)
    
    println("SAV: Done GO!")
  }

  class ForeachVerifyDefTraverser(f: DefDef => Unit) extends ForeachPartialTreeTraverser(
      {case t : DefDef if verifyDef(t) => f(t); EmptyTree})

  def verifyDef(t: DefDef) = t.symbol.hasAnnotation(definitions.getClass(
      "net.namin.sav.annotation.verify"))

  case class DefContract(intParams: List[String], precondition: Option[Expression], postcondition: Option[Expression=>Expression])
  var verifiedDefs = Map[Name, DefContract]()
  def collectDef(t: DefDef) {
    val contractBuilder = new DefContractBuilder
    contractBuilder.build(t) match {
      case None => println("Error: Could not build contract")
      case Some(contract) =>
        println("contract:")
        println("precondition: " + contract.precondition.map(ScalaPrinter(_)))
        println("postcondition: " + contract.postcondition.map(f => ScalaPrinter(f(Variable("result")))))
    }
  }
  def analyzeDef(t: DefDef) {
    println("SAV: Analyzing " + t.name)

    val cfgBuilder = new DefCFGBuilder
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
  }

  class VerifyDefTraverser extends Traverser {
    protected val variables = mutable.Set[String]()
    protected var ok = true

    protected def considerValDef(t: ValDef) = {
      if (t.tpt.toString == "Int") {
        variables += t.name.decode
        true
      } else {
        println("ignoring variable " + t.name + " of type " + t.tpt)
        false
      }
    }

    def exprIfOk(t: Tree) = {
      val exprBuilder = new ExpressionBuilder(false)
      val expr = exprBuilder.build(t)
      if (exprBuilder.ok) Some(simplify(expr)) else None
    }
    def expr(t: Tree) = {
      val exprBuilder = new ExpressionBuilder(true)
      val expr = exprBuilder.build(t)
      if (exprBuilder.ok) simplify(expr)
      else { ok = false; expr }
    }
    class ExpressionBuilder(signalError: Boolean) {
      var ok = true
      def build(t: Tree): Expression = t match {
        case Literal(Constant(value)) => value match {
          case x : Int => NumericalConst(x)
          case x : Boolean => BoolConst(x)
        }
        case Ident(name) if variables.contains(name.decode) => Variable(name.decode)
        case Apply(Select(e, op), List()) if unaryOps.contains(op.decode) =>
          UnaryExpression(unaryOps(op.decode), build(e))
        case Apply(Select(lhs, op), List(rhs)) if binaryOps.contains(op.decode) =>
          BinaryExpression(build(lhs), binaryOps(op.decode), build(rhs))
        case _ =>
          if (signalError) println("missing case in expression builder: " + t.getClass + " " + t)
          ok = false
          null
      }
    }
  }

  class DefContractBuilder extends VerifyDefTraverser {
    private val intParams = mutable.ListBuffer[String]()
    private var precondition : Option[Expression] = None
    private var postcondition : Option[Expression] = None
    private var result : Option[String] = None

    def build(t: DefDef) = {
      ok = false
      traverse(t)
      val intParamsList = intParams.toList
      val intParamsSet = intParamsList.toSet
      if (!ok) None else {
      	if (precondition.exists(e => !freeVars(e).subsetOf(intParamsSet))) {
      		println("precondition has free variables")
      		ok = false
      		None
      	} else if (postcondition.exists(e => !freeVars(e).subsetOf(
      			intParamsSet union result.toSet))) {
      		println("postcondition has free variables")
      		ok = false
      		None
      	} else {
      		verifiedDefs += (t.name ->
            	DefContract(intParamsList, precondition, result match {
            		case None => postcondition.map(e => r => e)
            		case Some(v) => postcondition.map(e => r => subst(e, Map(v -> r)))
            	}))
          Some(verifiedDefs(t.name))
      	}
      }
    }

    override def traverse(t: Tree) { t match {
	      case DefDef(mods, name, tparams, vparamss, tpt, rhs @ Block(stats, r)) =>
	        ok = true
	        println("def " + name)
	        for (vparams <- vparamss; v <- vparams) {
	          if (considerValDef(v)) {
	            intParams.append(v.name.decode)
	          }
	        }
	        if (tpt.toString == "Int") {
	          r match {
	            case Ident(name) =>
	              val v = name.decode
	              variables += v
	              result = Some(v)
	            case _ => ()
	          }
	          traverseTrees(stats)
	        } else {
	          traverse(rhs)
	        }
	      case Apply(Select(_, fun), List(arg)) if fun.decode == "precondition" =>
	        val e = expr(arg)
	        precondition = precondition match {
	          case None => Some(e)
	          case Some(pe) => Some(simplify(Conjunction(pe, e)))
	        }
	      case Apply(Select(_, fun), List(arg)) if fun.decode == "postcondition" =>
	        val e = expr(arg)
	        postcondition = postcondition match {
	          case None => Some(e)
	          case Some(pe) => Some(simplify(Conjunction(pe, e)))
	        }
	      case _ => ()
      }
    }
  }

  class DefCFGBuilder extends VerifyDefTraverser {
    private val cfg = new CFG()
    override protected val variables = cfg.variables
    private var labels = Map[Name,(Vertex,Vertex)]()
    private var next = cfg.newVertex
    private var lastAssertFrom = cfg.error
    private var lastAssertTo = cfg.error
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
      val ((from, to), ce) = if (lastAssertTo == next) {
      	val pe = cfg.asserts(lastAssertFrom)
      	val ce = simplify(Conjunction(pe, e))
      	((lastAssertFrom, lastAssertTo), ce)
      } else {
      	(newNext, e)
      }
      
   	  cfg.asserts += (from -> ce)
  	  cfg += (from, Assume(ce), to)
  	  cfg += (from, Assume(simplify(Not(ce))), cfg.error)

  	  lastAssertFrom = from
  	  lastAssertTo = to
    }

    private def addAssign(v: String, rhs: Expression) = {
      addEdge(lazabs.cfg.Assign(Variable(v), rhs))
    }

    private def addWhileLabel(n: Name) = {
      assert(lastAssertFrom != cfg.error && lastAssertTo == next, "while loop must be preceded by assert!")
      labels += (n -> (lastAssertFrom, lastAssertTo))
      lastAssertFrom = cfg.error
      lastAssertTo = cfg.error
    }
    
    private def addDoWhileLabel(n: Name) = {
      labels += (n -> (next, next))
    }

    private def jumpTo(v: Vertex) = {
      cfg += (next, Assume(BoolConst(true)), v)
      next = v
    }

    def build(t: DefDef) = {
      traverse(t)
      if (ok) Some(cfg) else None
    }
 
    override def traverse(t: Tree) { t match {
        case DefDef(mods, name, tparams, vparamss, tpt, rhs @ Block(stats, r)) =>
          println("def " + name)
          for (vparams <- vparamss; v <- vparams) considerValDef(v)
          if (tpt.toString == "Unit") {
          	traverse(rhs)
          } else {
            traverseTrees(stats)
          }
        case Block(stats, expr) => super.traverse(t)
        case v @ ValDef(mods, name, tpt, rhs)=>
          if (considerValDef(v)) addAssign(name.decode, expr(rhs))
        case LabelDef(name, List(), rhs @ If(cond, thenp, Literal(Constant(())))) =>
          addWhileLabel(name)
          val conde = expr(cond)
          addEdge(Assume(conde))
          traverse(thenp)
          assert(labels(name)._2 == next)
          addEdge(Assume(simplify(Not(conde))))
        case LabelDef(name, List(), rhs @ Block(stats, If(cond, thenp, Literal(Constant(()))))) =>
          addDoWhileLabel(name)
          traverseTrees(stats)
          val from = next
          val conde = expr(cond)
          addEdge(Assume(conde))
          traverse(thenp)
          assert(labels(name)._2 == next)
          next = from
          addEdge(Assume(simplify(Not(conde))))
        case If(cond, thenp, elsep) =>
          val from = next
          val conde = exprIfOk(cond)
          conde.foreach(e => addEdge(Assume(e)))
          traverse(thenp)
          val end = next
          next = from
          conde.foreach(e => addEdge(Assume(simplify(Not(e)))))
          traverse(elsep)
          jumpTo(end)
        case Assign(Ident(name), rhs) if variables.contains(name.decode) => exprIfOk(rhs) match {
          case None =>
            rhs match {
              case Apply(Select(_, fun), args) if verifiedDefs.contains(fun.decode) =>
                val DefContract(ips, precondition, postcondition) = verifiedDefs(fun.decode)
                println("partial havoc with contract of " + fun.decode)
                precondition.foreach(e => addAssert(subst(e, ips.zip(args.map(expr)).toMap)))
                addEdge(Havoc(Variable(name.decode)))
                postcondition.foreach(f => addEdge(Assume(f(Variable(name.decode)))))
              case _ =>
                println("havoc on " + t)
                addEdge(Havoc(Variable(name.decode)))
            }
          case Some(e) => addAssign(name.decode, e)
        }
        case Assign(Ident(name), rhs) =>
          // assignment to unconsidered variable
        case Apply(Select(_, fun), List(arg)) if fun.decode == "precondition" =>
          addEdge(Assume(expr(arg)))
        case Apply(Select(_, fun), List(arg)) if fun.decode == "postcondition" =>
          addAssert(expr(arg))
        case Apply(Select(_, fun), List(arg)) if fun.decode == "assume" =>
          addEdge(Assume(expr(arg)))
        case Apply(Select(_, fun), List(arg)) if fun.decode == "assert" =>
          addAssert(expr(arg))
        case Apply(Select(_, fun), List(arg)) if fun.decode.endsWith("_=")=>
          // complex assignment -- must be (indirectly) to unconsidered variable
        case Apply(Ident(name), List()) if labels.contains(name) =>
          jumpTo(labels(name)._1)
          next = labels(name)._2
        case Literal(Constant(())) => ()
        case _ =>
          println("missing case: " + t.getClass + " " + t)
          ok = false
      }
    }
  }

  val unaryOps = Map(
    "unary_-" -> MinusOp(),
    "unary_!" -> NotOp())

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
