package lazabs.nts

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.utils.Manip._

// imports related to nts
import nts.interf._
import nts.interf.base._
import nts.interf.expr._
import nts.parser._
import nts.parser.ASTWithoutToken._

// imports related to Flata
import verimag.flata_backend.AccelerationInput
import verimag.flata_backend.BackEnd
import verimag.flata_backend.Closure
import verimag.flata_backend.Loop

object AccelerationStrategy extends Enumeration {
  type AccelerationStrategy = Value
  val PRECISE, UNDER_APPROX, OVER_APPROX = Value
}

object FlataWrapper {
  def Eldarica2Nts(sce: Expression): (nts.parser.Expr,Set[String]) = {
    var variables: Set[String] = Set()
    def e2n(ex: Expression): nts.parser.Expr = ex match {
      case Not(e) => exNot(e2n(e))
      case Minus(e) => exUnaryMinus(e2n(e))
      case Disjunction(e1,e2) => exOr(e2n(e1),e2n(e2))
      case Conjunction(e1,e2) => exAnd(e2n(e1),e2n(e2))
      case Equality(e1,e2) => exEq(e2n(e1),e2n(e2))
      case Iff(e1,e2) => exEquiv(e2n(e1),e2n(e2))    
      case Inequality(e1,e2) => exNeq(e2n(e1),e2n(e2))
      case LessThan(e1,e2) => exLt(e2n(e1),e2n(e2))
      case LessThanEqual(e1,e2) => exLeq(e2n(e1),e2n(e2))
      case GreaterThan(e1,e2) => exGt(e2n(e1),e2n(e2))
      case GreaterThanEqual(e1,e2) => exGeq(e2n(e1),e2n(e2))   
      case Addition(e1,e2) => exPlus(e2n(e1),e2n(e2))   
      case Subtraction(e1,e2) => exMinus(e2n(e1),e2n(e2))
      case Multiplication(e1,e2) => exMult(e2n(e1),e2n(e2))
      case Division(e1,e2) => exDivide(e2n(e1),e2n(e2))
      case Modulo(e1,e2) => exRemainder(e2n(e1),e2n(e2))
      case Variable(name,None) =>        
        variables += name.stripSuffix("'")
        accessBasic(name)
      case NumericalConst(num) => litInt(num)
      case BoolConst(v) => litBool(v)
      case _ =>
        println("Error in Flata conversion " + lazabs.viewer.ScalaPrinter(sce))
        litBool(false)
    }
    val result = e2n(sce)
    (result,variables)
  }
  import AccelerationStrategy._
  /**
   * if the method input is PRECISE only the acceleration is returned
   * if the acceleration input is APPROXIMATE it first try precise acceleration (isOctagon) and only if unsuccessful it will try approximation 
   */
  def accelerate(exps: List[List[Expression]], method: AccelerationStrategy, prefix: List[Expression] = List(BoolConst(true))): Any = {
    //println("\n\n\n" + exps.map(x => x.map(lazabs.viewer.ScalaPrinter(_)).mkString(" \n ")).mkString("\n------------\n") + "\n\n\n")
    verimag.flata.Main.initActions
    var table = new nts.parser.VarTable(null)
    val ntsForms = exps.map(ll => ll.map(Eldarica2Nts(_)))
    val variables = ntsForms.map(x => x.map(_._2)).reduceLeft(_++_).reduceLeft(_++_)
    val disjunctive = scala.collection.JavaConversions.seqAsJavaList(ntsForms.map(x => (new Loop(scala.collection.JavaConversions.seqAsJavaList(x.map(_._1)))).asInstanceOf[acceleration.ILoop]))
    val prefixForms = prefix.map(Eldarica2Nts(_))
    val prefixVars = prefixForms.map(_._2).reduceLeft(_++_)
    val pref = scala.collection.JavaConversions.seqAsJavaList(prefixForms.map(_._1).map(_.asInstanceOf[nts.interf.base.IExpr]))
    (variables ++ prefixVars).foreach {declareInt(table,_)}
    ntsForms.map(x => x.map(_._1)).reduceLeft(_++_).foreach(_.semanticChecks(table))
    prefixForms.map(_._1).foreach(_.semanticChecks(table))
    var ai: AccelerationInput = new AccelerationInput(pref,disjunctive,table)
    val backend = new BackEnd
    val transitiveClosure = (method,backend.isOctagon(ai)) match {
      case (AccelerationStrategy.PRECISE,true)  => Some(lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closure(ai).getClosure,List()))
      case (AccelerationStrategy.PRECISE,false) => None
      case (AccelerationStrategy.OVER_APPROX,true) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closure(ai).getClosure,List()),true)
      case (AccelerationStrategy.OVER_APPROX,false) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closureOverapprox(ai).getClosure,List()),false)
      case (AccelerationStrategy.UNDER_APPROX,true) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closure(ai).getClosure,List()),true)
      case (AccelerationStrategy.UNDER_APPROX,false) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closureUnderapprox(ai).getClosure,List()),false)
    }
    verimag.flata_backend.BackEnd.finalActions     // FLATA makes some final actions (terminating Yices)
    transitiveClosure
  }  
}