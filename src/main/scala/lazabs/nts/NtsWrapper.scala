package lazabs.nts

import lazabs.ast.ASTree._
import lazabs.types._
import java.io._
import scala.collection.JavaConversions._

import nts.interf._
import nts.interf.base._
import nts.interf.expr._
import nts.parser._


object NtsWrapper {
  /**
   * map from a control state in a subsystem to ad Id
   */
  private var stateIdMap: collection.mutable.Map[(String,String),Int] = collection.mutable.Map.empty
  /**
   * map from a CFG id to a control state name
   */
  var stateNameMap: collection.mutable.Map[Int,String] = collection.mutable.Map.empty
  private var ntsResult: nts.interf.INTS = null       // NTS implementation is completely imperative, forces to communicate via global variables
  /**
   * returns two things: CFG and the mapping from CFG ids to names
   */
  def apply(ntsFileName: String): Nts = {
    val is: InputStream = try {
      new FileInputStream(ntsFileName)
    } catch {
      case e: FileNotFoundException => println("No such file or option: " + ntsFileName + ". Use -h for usage information" )
        sys.exit(0)
    }
    val listen: ParserListener = new ParserListener
    NTSParser.parseNTS(is, listen)
    val nts:NTS = listen.nts
    val v:Visitor = new Visitor
    nts.accept(v)
    val result = if(ntsResult != null) Nts2Eldarica(ntsResult)
    else {
      println("Error in getting NTS")
      sys.exit(0)
    }
    result
  }
  def Nts2Eldarica(e: nts.interf.INTS): Nts = {
    Nts(e.varTable.visibleUnprimed.toList.map(v => Variable("sc_" + v.name).stype(IntegerType())),e.subsystems.toList.map(Nts2Eldarica))
  }
  def Nts2Eldarica(e: nts.interf.ISubsystem): NtsSubsystem = {
    val allVariables = e.varTable.visibleUnprimed.toList.filter(v => v.name != "tid").map(v => Variable("sc_" + v.name).stype(IntegerType()))
    NtsSubsystem(e.name, e.transitions.toList.map(Nts2Eldarica(_,e.marksError.toList,allVariables,e.name)), e.varIn.toList.map(v => Variable("sc_" + v.name).stype(IntegerType())), 
        e.varOut.toList.map(v => Variable("sc_" + v.name).stype(IntegerType())), allVariables, e.marksInit.toList.map(Nts2Eldarica(_,e.marksError.toList,e.name)), e.marksFinal.toList.map(Nts2Eldarica(_,e.marksError.toList,e.name)), 
        e.marksError.toList.map(Nts2Eldarica(_,e.marksError.toList,e.name)))        
  }
  /**
   * @param e the transition
   * @param errors the set of error states
   * @param variables the set of variables
   * @param name the name of the subsystem to which the transitions belong
   */
  def Nts2Eldarica(e: nts.interf.ITransition, errors: List[nts.interf.IControlState], variables: scala.collection.immutable.List[Variable], name: String): NtsTransition = {
    NtsTransition(Nts2Eldarica(e.from,errors,name), Nts2Eldarica(e.to,errors,name), Nts2Eldarica(e.label,variables))
  }
  import java.lang.reflect._
  def Nts2Eldarica(e: nts.interf.base.ILabel, variables: scala.collection.immutable.List[Variable]): Expression = e match {
    case em@(_: nts.interf.expr.IExprExists) =>
      val binders = e.asInstanceOf[nts.parser.ExExists].varTable.innermost.map(binder => 
        BinderVariable("sc_" + (binder.asInstanceOf[nts.parser.VarTableEntry].name)).stype(IntegerType()))
      val formula = Nts2Eldarica(em.asInstanceOf[nts.parser.ExExists].operand,variables)
      //(binder.asInstanceOf[nts.parser.VarTableEntry].name.replaceFirst("\\$", "d"))),
      lazabs.utils.Manip.deBruijnIndex(binders.foldLeft(formula)((a,b) => Existential(b,a)))
    case em@(_: nts.interf.expr.IExprPlus) => Addition(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprMinus) => Subtraction(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprMult) => Multiplication(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprDivide) => Division(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprRemainder) => Modulo(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprAnd) => Conjunction(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprOr) => Disjunction(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprGeq) => GreaterThanEqual(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprGt) => GreaterThan(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprLeq) => LessThanEqual(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprLt) => LessThan(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprEq) => Equality(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprNeq) => Inequality(Nts2Eldarica(em.operand1,variables),Nts2Eldarica(em.operand2,variables))
    case em@(_: nts.interf.expr.IExprNot) => Not(Nts2Eldarica(em.operand,variables))
    case em@(_: nts.interf.expr.IExprUnaryMinus) => Minus(Nts2Eldarica(em.operand,variables))
    case em@(_: nts.interf.expr.IAccessBasic) => //  A basic access to a variable -- an access without indexing
      if(em.asInstanceOf[nts.parser.Access].varName.startsWith("sc_"))
        Variable(em.asInstanceOf[nts.parser.Access].varName,None).stype(IntegerType())
      else
        Variable("sc_" + em.asInstanceOf[nts.parser.Access].varName,None).stype(IntegerType())
    case em@(_: nts.parser.Havoc) =>
      val frame = variables.diff(em.vars.map(x => Nts2Eldarica(x,variables))).map(x => Equality(x,lazabs.utils.Manip.prime(x)))
      (frame.size) match {
        case 0 => BoolConst(true)
        case 1 => frame.head
        case _ => frame.reduceLeft(Conjunction(_,_))
      }
    case em@(_: nts.parser.Call) =>
      NTSCall(em.callee.name, em.actualParameters.toList.map(Nts2Eldarica(_,variables)), em.returnVars.toList.map(x => Variable("sc_" + x.asInstanceOf[nts.parser.Access].varName,None)),
          (if(em.asInstanceOf[nts.parser.Call].hasHavoc) Some(em.asInstanceOf[nts.parser.Call].havoc.vars.toList.map(x => Nts2Eldarica(x,variables).asInstanceOf[Variable])) else None))
    case em@(_: nts.interf.expr.ILitInt) => NumericalConst(em.asInstanceOf[nts.parser.LitInt].value)
    case em@(_: nts.interf.expr.ILitBool) => BoolConst(em.asInstanceOf[nts.parser.LitBool].value)
    case _ => 
      println("Error in NTS converstion: " + e)
      sys.exit(0)
  }
  def Nts2Eldarica(ic: nts.interf.IControlState, errors: List[nts.interf.IControlState], name: String): Int = stateIdMap.get((name,ic.name)) match {
    case Some(v) => v
    case None => if(errors.contains(ic)) -1 else {
      val fresh = lazabs.cfg.FreshCFGStateId.apply
      stateIdMap += ((name,ic.name) -> fresh)
      stateNameMap += (fresh -> (name + "_" + ic.name))
      fresh
    }
  }
      
  class Visitor extends IVisitor {
    def visit(e: nts.interf.INTS) {
      ntsResult = e
    }
    def visit(e: nts.interf.ISubsystem) {
      println("ISubsystem")
    }
    def visit(e: nts.interf.ICall) {
      println("ICall")      
    }
    def visit(e: nts.interf.ITransition) {
      println("ITransition")
    }
    def visit(e: nts.interf.IControlState) {
      println("IControlState")
    }
    def visit(e: nts.interf.base.IAnnotations) {
      println("IAnnotations")
    }
    def visit(e: nts.interf.expr.IHavoc) {
      println("IHavoc")
    }
    def visit(e: nts.interf.expr.ILitReal) {
      println("ILitReal")
    }
    def visit(e: nts.interf.expr.ILitInt) {
      println("ILitInt")
    }
    def visit(e: nts.interf.expr.ILitBool) {
      println("ILitBool")
    }
    def visit(e: nts.interf.expr.IAccessMulti) {
      println("IAccessMulti")
    }
    def visit(e: nts.interf.expr.IAccessIndexed) {
      println("IAccessIndexed")
    }
    def visit(e: nts.interf.expr.IAccessBasic) {
      println("IAccessBasic")
    }
    def visit(e: nts.interf.expr.IExprList) {
      println("IExprList")
    }
    def visit(e: nts.interf.expr.IExprArraySize) {
      println("IExprArraySize")
    }
    def visit(e: nts.interf.expr.IExprUnaryMinus) {
      println("IExprUnaryMinus")
    }
    def visit(e: nts.interf.expr.IExprMinus) {
      println("IExprMinus")
    }
    def visit(e: nts.interf.expr.IExprPlus) {
      println("IExprPlus")
    }
    def visit(e: nts.interf.expr.IExprDivide) {
      println("IExprDivide")
    }    
    def visit(e: nts.interf.expr.IExprRemainder) {
      println("IExprRemainder")
    }
    def visit(e: nts.interf.expr.IExprMult) {
      println("IExprMult")
    }
    def visit(e: nts.interf.expr.IExprGt) {
      println("IExprGt")
    }
    def visit(e: nts.interf.expr.IExprGeq) {
      println("IExprGeq")
    }
    def visit(e: nts.interf.expr.IExprLt) {
      println("IExprLt")
    }
    def visit(e: nts.interf.expr.IExprLeq) {
      println("IExprLeq")
    }
    def visit(e: nts.interf.expr.IExprNeq) {
      println("IExprNeq")
    }
    def visit(e: nts.interf.expr.IExprEq) {
      println("IExprEq")
    }
    def visit(e: nts.interf.expr.IExprForall) {
      println("IExprForall")
    }
    def visit(e: nts.interf.expr.IExprExists) {
      println("IExprExists")
    }
    def visit(e: nts.interf.expr.IExprEquiv) {
      println("IExprEquiv")
    }
    def visit(e: nts.interf.expr.IExprImpl) {
      println("IExprImpl")
    }
    def visit(e: nts.interf.expr.IExprOr) {
      println("IExprOr")
    }
    def visit(e: nts.interf.expr.IExprAnd) {
      println("IExprAnd")
    }
    def visit(e: nts.interf.expr.IExprNot) {
      println("IExprNot")
    }
    def visit(e: nts.interf.base.IType) {
      println("IType")
    }
    def visit(e: nts.interf.base.IVarTableEntry) {
      println("IVarTableEntry")
    }
    def visit(e: nts.interf.base.IVarTable) {
      println("IVarTable")
    }
  }
}