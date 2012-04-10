package lazabs.prover

import lazabs.ast.ASTree._
import lazabs.types._
import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression._
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier


object PrincessWrapper {
  
  private val api = new PrincessAPI_v1
  import api._

  /**
   * converts a list of formulas in Eldarica format to a list of formulas in Princess format
   * returns both the formulas in Princess format and the symbols used in the formulas
   */
  def formula2Princess(ts: List[Expression]) : (List[IExpression], List[ConstantTerm]) = {
    var symbols: List[ConstantTerm] = List()
    def f2p(ex: Expression): IExpression = ex match {
      case lazabs.ast.ASTree.Universal(v: BinderVariable, qe: Expression) => IQuantified(Quantifier.ALL, f2p(qe).asInstanceOf[IFormula])
      case lazabs.ast.ASTree.Existential(v: BinderVariable, qe: Expression) => IQuantified(Quantifier.EX, f2p(qe).asInstanceOf[IFormula])
      case lazabs.ast.ASTree.Conjunction(e1, e2) => f2p(e1).asInstanceOf[IFormula] & f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Disjunction(e1, e2) => f2p(e1).asInstanceOf[IFormula] | f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Implication(e1, e2) => f2p(e1).asInstanceOf[IFormula] ==> f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Iff(e1, e2) => f2p(e1).asInstanceOf[IFormula] <=> f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.LessThan(e1, e2) => f2p(e1).asInstanceOf[ITerm] < f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.LessThanEqual(e1, e2) => f2p(e1).asInstanceOf[ITerm] <= f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.GreaterThan(e1, e2) => f2p(e1).asInstanceOf[ITerm] > f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.GreaterThanEqual(e1, e2) => f2p(e1).asInstanceOf[ITerm] >= f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Addition(e1,e2) => f2p(e1).asInstanceOf[ITerm] + f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Minus(e) => -f2p(e).asInstanceOf[ITerm]    
      case lazabs.ast.ASTree.Subtraction(e1,e2) => f2p(e1).asInstanceOf[ITerm] - f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Multiplication(e1,e2) =>        
        f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
      case Division(e1,e2) => div(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case Modulo(e1,e2) => mod(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.Not(e) => !f2p(e).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Inequality(e1, e2) => f2p(lazabs.ast.ASTree.Not(lazabs.ast.ASTree.Equality(e1, e2)))
      case lazabs.ast.ASTree.Equality(e1, e2) =>
        val lhs = f2p(e1)
        val rhs = f2p(e2)
        //println("LHS :: \n" + e1 + " and the type: " + e1.stype)
        //println("RHS :: \n" + e2 + " and the type: " + e2.stype)
        if (lhs.isInstanceOf[IFormula])
          (lhs.asInstanceOf[IFormula] <=> rhs.asInstanceOf[IFormula])
        else
          (lhs.asInstanceOf[ITerm] === rhs.asInstanceOf[ITerm])
      case lazabs.ast.ASTree.Variable(vname,None) => symbols.find(_.toString == vname) match {
        case Some(ov) => ov
        case None =>
          val variable = new ConstantTerm(vname)
          symbols :+= variable
          variable
        }
      case lazabs.ast.ASTree.Variable(vname,Some(i)) => IVariable(i)
      case lazabs.ast.ASTree.NumericalConst(e) => IIntLit(e)
      case lazabs.ast.ASTree.BoolConst(v) => IBoolLit(v)
      case _ =>
        println("Error in conversion from Eldarica to Princess: " + ex)
        IBoolLit(false)
    }
    val res = ts.map(f2p)
    (res,symbols)
  }

   def deBruijnIndex(e: Expression): Expression = {
     def deBruijn(e: Expression, bounds: List[String]): Expression = e match {
       case Variable(name,_) if (bounds.contains(name)) => Variable(name,Some(bounds.takeWhile(s => (s != name)).length)).stype(e.stype)
       case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, deBruijn(e1,bounds), deBruijn(e2,bounds), deBruijn(e3,bounds)).stype(e.stype)
       case BinaryExpression(e1, op, e2) => BinaryExpression(deBruijn(e1,bounds), op, deBruijn(e2,bounds)).stype(e.stype)
       case UnaryExpression(op, e) => UnaryExpression(op, deBruijn(e,bounds)).stype(e.stype)
       case Existential(v, qe) => Existential(v, deBruijn(qe,v.name :: bounds)).stype(e.stype)
       case Universal(v, qe) => Universal(v, deBruijn(qe,v.name :: bounds)).stype(e.stype)
       case _ => e
     }
     deBruijn(e,List())    
   }

 
  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = {
    val (formulas,symbols) = formula2Princess(List(deBruijnIndex(e)))
    Some(isSat(formulas.head.asInstanceOf[IFormula], symbols))
  }

}
