package lazabs.ast

import lazabs.types._

object ASTree {
  sealed abstract class ASTree extends ScalaType
  class Declaration() extends ASTree
  class Expression() extends ASTree
  case class Sobject(name: String, defs: List[Declaration]) extends ASTree  
  case class Parameter(name: String, typ: Type) extends ASTree
  
  /**
   * @param funcName the name of the function
   * @param params the parameters
   * @param t returned type
   * @param body body of the function
   */

  case class FunctionDefinition(funcName: String, params: List[Parameter], t: Type, body: Expression) extends Declaration
  case class VarDeclaration(name: String, t: Type, value: Expression) extends Declaration
  
  // Expressions
  case class Block(declList: List[ASTree]) extends Expression
  case class FunctionCall(funcName: String, exprList: List[Expression]) extends Expression
  case class Variable(name: String, deBruijn: Option[Int] = None) extends Expression  
  case class NumericalConst(num: Int) extends Expression
  case class CreateObject(cName: String, cArgs: List[Expression]) extends Expression
  case class BoolConst(value: Boolean) extends Expression
  case class WhileLoop(cond: Expression, body: Expression) extends Expression
  case class DoWhileLoop(cond: Expression, body: Expression) extends Expression
  
  // Quantification
  case class BinderVariable(name: String) extends Expression
  case class Existential(v: BinderVariable, qe: Expression) extends Expression
  case class Universal(v: BinderVariable, qe: Expression) extends Expression
  object Quantifiers extends Enumeration {
    val Exists, Forall = Value
  }
  def quantify(q:Quantifiers.Value)(vs:List[String], e:Expression) = q match {
    case Quantifiers.Exists => (e /: vs) ( (expr, v) => Existential(BinderVariable(v), expr) )
    case Quantifiers.Forall => (e /: vs) ( (expr, v) => Universal(BinderVariable(v), expr) )
  }
  
   
  // ternary expressions
  sealed abstract class TernaryOperator(val st: String)
  case class IfThenElseOp() extends TernaryOperator ("if")
  case class ArrayUpdateOp() extends TernaryOperator ("update")  
  case class TernaryExpression(op: TernaryOperator, e1: Expression, e2: Expression, e3: Expression) extends Expression  

  // binray expressions
  sealed abstract class BinaryOperator(val st: String)
  case class IfThenOp() extends BinaryOperator ("if")
  case class AssignmentOp() extends BinaryOperator ("=")
  case class DisjunctionOp() extends BinaryOperator ("||")
  case class ConjunctionOp() extends BinaryOperator ("&&")
  case class ImplicationOp() extends BinaryOperator ("==>")
  case class EqualityOp() extends BinaryOperator ("==")
  case class IffOp() extends BinaryOperator ("===") 
  case class InequalityOp() extends BinaryOperator ("!=")
  case class LessThanOp() extends BinaryOperator ("<")
  case class LessThanEqualOp() extends BinaryOperator("<=")
  case class GreaterThanOp() extends BinaryOperator (">")
  case class GreaterThanEqualOp() extends BinaryOperator (">=")
  case class AdditionOp() extends BinaryOperator ("+")
  case class SubtractionOp() extends BinaryOperator ("-")
  case class MultiplicationOp() extends BinaryOperator ("*")
  case class DivisionOp() extends BinaryOperator ("/")
  case class ModuloOp() extends BinaryOperator ("%")
  case class UntilOp() extends BinaryOperator ("until")
  case class AnonymousFunctionOp() extends BinaryOperator ("=>") 
  case class BinaryExpression(e1: Expression, op: BinaryOperator, e2: Expression) extends Expression
  

  // unary expressions
  sealed abstract class UnaryOperator(val st: String)
  case class MinusOp() extends UnaryOperator ("-")
  case class NotOp() extends UnaryOperator ("!")
  case class UnaryExpression(op: UnaryOperator, e: Expression) extends Expression  
  
  case class Skip() extends Expression
  case class Null() extends Expression
 
  // Extractors
  
  object Minus {
    def apply(e: Expression) = UnaryExpression(MinusOp(), e) 
    def unapply(exp: Expression) : Option[(Expression)] = 
      exp match {
        case UnaryExpression(MinusOp(), e) => Some(e)
        case _ => None
      }
  }
  
  object Not {
    def apply(e: Expression) = UnaryExpression(NotOp(), e) 
    def unapply(exp: Expression) : Option[(Expression)] = 
      exp match {
        case UnaryExpression(NotOp(), e) => Some(e)
        case _ => None
      }
  }
  
  object IfThen {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, IfThenOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, IfThenOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object IfThenElse {
    def apply(cond: Expression, conseq: Expression, altern: Expression) = TernaryExpression(IfThenElseOp(), cond, conseq, altern)
    def unapply(exp: Expression) : Option[(Expression,Expression,Expression)] = 
      exp match {
        case TernaryExpression(IfThenElseOp(), cond, conseq, altern) => Some((cond, conseq, altern))
        case _ => None
      }
  }
    
  object Assignment {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AssignmentOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AssignmentOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Disjunction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, DisjunctionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, DisjunctionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Conjunction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, ConjunctionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, ConjunctionOp(), right) => Some((left, right))
        case _ => None
      }
  }

   object Implication {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, ImplicationOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, ImplicationOp(), right) => Some((left, right))
        case _ => None
      }
  }
 
  object Equality {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, EqualityOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, EqualityOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Iff {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, IffOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, IffOp(), right) => Some((left, right))
        case _ => None
      }
  }  
  
  object Inequality {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, InequalityOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, InequalityOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object LessThan {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, LessThanOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, LessThanOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object LessThanEqual {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, LessThanEqualOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, LessThanEqualOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object GreaterThan {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, GreaterThanOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, GreaterThanOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object GreaterThanEqual {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, GreaterThanEqualOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, GreaterThanEqualOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Addition {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AdditionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AdditionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Subtraction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SubtractionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, SubtractionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Multiplication {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, MultiplicationOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, MultiplicationOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Division {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, DivisionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, DivisionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Modulo {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, ModuloOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, ModuloOp(), right) => Some((left, right))
        case _ => None
      }
  }  
  
  object Range {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, UntilOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, UntilOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object AnonymousFunction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AnonymousFunctionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AnonymousFunctionOp(), right) => Some((left, right))
        case _ => None
      }
  }
 
  //Java stuff

  def makeVariable(name: String, deBruijn_java: scala.Option[java.lang.Integer]): Variable = {
    val deBruijn: Option[Int] = deBruijn_java match {
      case Some(n) => Some(n.intValue())  // convert Integer to Scala Int
      case None => None
    }
    Variable(name, deBruijn)
    }

  def makeScalaObject(name: String, defList_java: java.util.List[Declaration]): ASTree = {
    val defList = defList_java.toArray.toList   // convert java list to scala list
    Sobject(name, defList.asInstanceOf[List[Declaration]])
  }

  def makeBlock(declList_java: java.util.List[ASTree]): Expression = {
    val declList = declList_java.toArray.toList   // convert java list to scala list
    Block(declList.asInstanceOf[List[ASTree]])
  }

  def makeFunctionCall(funcName: String, exprList_java: java.util.List[Expression]): Expression = {
    val exprList = exprList_java.toArray.toList   // convert java list to scala list
    FunctionCall(funcName, exprList.asInstanceOf[List[Expression]])
  }

  def makeCreateObject(objName: String, exprList_java: java.util.List[Expression]): Expression = {
    val exprList = exprList_java.toArray.toList   // convert java list to scala list
    CreateObject(objName, exprList.asInstanceOf[List[Expression]])
  }

  def makeFunctionDefinition(funcName: String, params_java: java.util.List[Parameter], t: Type, e: Expression): ASTree = {
    val paramsList = params_java.toArray.toList   // convert java list to scala list
    FunctionDefinition(funcName, paramsList.asInstanceOf[List[Parameter]], t, e)
  }

}
