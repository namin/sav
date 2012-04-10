package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.ast._
import lazabs.types._
import lazabs.cfg._
import lazabs.utils.Manip._

object ScalaPrinter {
  def apply( o: Sobject): String = "object " + o.name + " {\n" + o.defs.map(apply).mkString("\n") + "}" 
  def apply( e: Expression): String = simplify(e) match {
    case Block(declList) => "{\n" + declList.map(apply).mkString("\n") + "}"
    case FunctionCall(funcName, exprList) if(funcName.startsWith("sc_")) => funcName.drop(3) + exprList.map(apply).mkString("(", ",", ")") 
    case FunctionCall(funcName, exprList) => funcName + exprList.map(apply).mkString("(", ",", ")")    
    case IfThenElse(cond, conseq, altern) => "if( " + this(cond) + ")" + this(conseq) + " else " + this(altern)
    case WhileLoop(cond, body) => "while( " + this(cond) + ")" + this(body)
    case CreateObject(cName, cArgs) => "new " + cName + cArgs.map(apply).mkString("(", ",", ")")
    case Existential(v, qe) => "(EX " + this(v) + ". " + this(qe) + ")"
    case Universal(v, qe) => "(ALL " + this(v) + ". " + this(qe) + ")"
    case BinderVariable(name) if(name.startsWith("sc_")) => name.drop(3)
    case BinderVariable(name) => name
    case BinaryExpression(e1, op, e2) => op.st match {
      case "if" => "if( " + this(e1) + ")" + this(e2)
      case _ => "(" + this(e1) + " " + op.st + " " + this(e2) + ")"
    } 
    case Variable(name,_) if(name.startsWith("sc_")) => name.drop(3)
    case Variable(name,_) => name
    case NumericalConst(num) => num.toString
    case BoolConst(v: Boolean) if (v == true) => "true"
    case BoolConst(v: Boolean) if (v == false) => "false"
    case UnaryExpression(op, e) => op.st + this(e)
    case _ => ""
  }
  def apply( d: Declaration):String = d match {
    case FunctionDefinition(funcName, ps, t, e) =>
      "def " + funcName + ps.map(apply).mkString("(", ",", ")") +  " : " + this(t) + " = " + this(e)      
    case VarDeclaration(name, t, value) =>
      "var " + name + " : " + this(t) + " = " + this(value)
    case _ => ""
  }
  
  def apply( t: ASTree):String = t match {
    case e: Expression => apply(e)
    case d: Declaration => apply(d)
    case _ => ""
  }
  
  def apply( t: Type): String = t match {
    case AnyType() => "Any"
    case UnitType() => "Unit"
    case IntegerType() => "Int"
    case StringType() => "String"
    case BooleanType() => "Boolean"   
    case _ => t.toString
  }
  def apply( d: Parameter): String = d.name + " : " + this(d.typ)
  
  def apply(t: CFGLabel): String  = t match {
    case Assume(p) => "[" + ScalaPrinter(p) + "]"
    case Assign(lhs, rhs) => ScalaPrinter(lhs) + "=" + ScalaPrinter(rhs)
    case Havoc(v) => "havoc(" + ScalaPrinter(v) + ")"
    case _ => ""
  }
}
