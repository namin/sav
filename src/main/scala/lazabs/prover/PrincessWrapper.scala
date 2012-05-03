package lazabs.prover

import lazabs.ast.ASTree._
import lazabs.types._
import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression._
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier

import scala.collection.mutable.LinkedHashMap

object PrincessWrapper {
  
  private val api = new PrincessAPI_v1
  import api._

  // Constants used in expressions in the Princess API
  private def constantStream(num : Int) : Stream[ConstantTerm] =
    Stream.cons(new ConstantTerm("c" + num), constantStream(num + 1))
  private val globalConstants = constantStream(0)

  /**
   * converts a list of formulas in Eldarica format to a list of formulas in Princess format
   * returns both the formulas in Princess format and the symbols used in the formulas
   */
  def formula2Princess(ts: List[Expression]) : (List[IExpression], LinkedHashMap[String, ConstantTerm]) = {
    val symbolMap = new LinkedHashMap[String, ConstantTerm]
    var symbolReservoir = globalConstants

    def f2p(ex: Expression): IExpression = ex match {
      case lazabs.ast.ASTree.ArraySelect(array, ind) =>
        select(f2p(array).asInstanceOf[ITerm],
               f2p(ind).asInstanceOf[ITerm])
      case ArrayUpdate(array, index, value) =>
        store(f2p(array).asInstanceOf[ITerm],
              f2p(index).asInstanceOf[ITerm],
              f2p(value).asInstanceOf[ITerm])
      case ScArray(None, None) => 0
      case ScArray(Some(aName), _) => f2p(aName)
      case ScArray(None, Some(len)) =>
        // let's just store the size of the array at index -1
        // is this needed at all anywhere?
        store(0, -1, f2p(len).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetUnion(e1, e2) => union(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetIntersect(e1, e2) => intersection(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])      
      case lazabs.ast.ASTree.SetSubset(e1, e2) => subsetof(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetDifference(e1, e2) => difference(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetContains(e1, e2) => in(f2p(e2).asInstanceOf[ITerm], f2p(e1).asInstanceOf[ITerm])  // note that Eldarica has "contains" and princess has "in". They are reverse
      case lazabs.ast.ASTree.SetSize(e1) => size(f2p(e1).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetConst(elems) => elems.map(x => singleton(f2p(x).asInstanceOf[ITerm])).foldLeft[ITerm](emptyset)((a,b) => union(a,b))
      case lazabs.ast.ASTree.Universal(v: BinderVariable, qe: Expression) => IQuantified(Quantifier.ALL, f2p(qe).asInstanceOf[IFormula])
      case lazabs.ast.ASTree.Existential(v: BinderVariable, qe: Expression) => IQuantified(Quantifier.EX, f2p(qe).asInstanceOf[IFormula])
      case lazabs.ast.ASTree.Conjunction(e1, e2) => f2p(e1).asInstanceOf[IFormula] & f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Disjunction(e1, e2) => f2p(e1).asInstanceOf[IFormula] | f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.LessThan(e1, e2) => f2p(e1).asInstanceOf[ITerm] < f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.LessThanEqual(e1, e2) => f2p(e1).asInstanceOf[ITerm] <= f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.GreaterThan(e1, e2) => f2p(e1).asInstanceOf[ITerm] > f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.GreaterThanEqual(e1, e2) => f2p(e1).asInstanceOf[ITerm] >= f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Addition(e1,e2) if (e1.stype == SetType(IntegerType()) && e2.stype == IntegerType()) =>
        union(f2p(e1).asInstanceOf[ITerm], singleton(f2p(e2).asInstanceOf[ITerm]))
      case lazabs.ast.ASTree.Addition(e1,e2) => f2p(e1).asInstanceOf[ITerm] + f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Minus(e) => -f2p(e).asInstanceOf[ITerm]    
      case lazabs.ast.ASTree.Subtraction(e1,e2) => f2p(e1).asInstanceOf[ITerm] - f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Multiplication(e1,e2) => (e1,e2) match {
        case (NumericalConst(_), _) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case (_,NumericalConst(_)) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case (Minus(NumericalConst(_)), _) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case (_,Minus(NumericalConst(_))) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case _ =>
          println("Only multiplication by constant is supported")
          sys.exit()
      }
      case Division(e1,e2) => div(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case Modulo(e1,e2) => mod(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])

      case lazabs.ast.ASTree.Not(e) => !f2p(e).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Inequality(e1, e2) => f2p(lazabs.ast.ASTree.Not(lazabs.ast.ASTree.Equality(e1, e2)))
      case lazabs.ast.ASTree.Equality(e1, lazabs.ast.ASTree.ScSet(None)) =>
        size(f2p(e1).asInstanceOf[ITerm]) === 0
      case lazabs.ast.ASTree.Equality(lazabs.ast.ASTree.ScSet(None), e1) =>
        isEmpty(f2p(e1).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.Equality(e1, e2) =>
        val lhs = f2p(e1)
        val rhs = f2p(e2)
        //println("LHS :: \n" + e1 + " and the type: " + e1.stype)
        //println("RHS :: \n" + e2 + " and the type: " + e2.stype)
        if (lhs.isInstanceOf[IFormula])
          (lhs.asInstanceOf[IFormula] <=> rhs.asInstanceOf[IFormula])
        else if (e1.stype.isInstanceOf[SetType] && e2.stype.isInstanceOf[SetType])
          setEqual(lhs.asInstanceOf[ITerm], rhs.asInstanceOf[ITerm])
        else
          (lhs.asInstanceOf[ITerm] === rhs.asInstanceOf[ITerm])
      case lazabs.ast.ASTree.Variable(vname,None) => symbolMap.getOrElseUpdate(vname, {
        val newSym = symbolReservoir.head
        symbolReservoir = symbolReservoir.tail
        newSym
      })
      case lazabs.ast.ASTree.Variable(vname,Some(i)) => IVariable(i)
      case lazabs.ast.ASTree.NumericalConst(e) => IIntLit(e)
      case lazabs.ast.ASTree.BoolConst(v) => IBoolLit(v)
      case lazabs.ast.ASTree.ScSet(None) => emptyset
      case _ =>
        println("Error in conversion from Eldarica to Princess: " + ex)
        IBoolLit(false)
    }
    val res = ts.map(f2p)
    (res,symbolMap)
  }
  
  /**
   * converts a formula in Princess format to a formula in Eldarica format
   * It also removes the versions in the SSA conversion 
   */
  import scala.util.matching.Regex
  def formula2EldaricaRemoveVersions(t: IFormula, symMap : Map[ConstantTerm, String]): Expression = {
    def rvT(t: ITerm): Expression = t match {
      case IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2)) =>
        lazabs.ast.ASTree.Subtraction(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1) =>
        lazabs.ast.ASTree.Subtraction(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IPlus(e1,e2) => lazabs.ast.ASTree.Addition(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case ITimes(e1,e2) => lazabs.ast.ASTree.Multiplication(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IFunApp(`size`, arg) =>
        lazabs.ast.ASTree.SetSize(rvT(arg.head).stype(SetType(IntegerType())))
      case IFunApp(`singleton`, Seq(e)) =>
        lazabs.ast.ASTree.SetAdd(lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType())),rvT(e).stype(IntegerType()))
      case IFunApp(`difference`, Seq(e0,e1)) =>
        lazabs.ast.ASTree.SetDifference(rvT(e0).stype(SetType(IntegerType())),rvT(e1).stype(SetType(IntegerType())))
      case IFunApp(`union`, Seq(e0,e1)) =>
        lazabs.ast.ASTree.SetUnion(rvT(e0).stype(SetType(IntegerType())),rvT(e1).stype(SetType(IntegerType())))
      case IFunApp(`intersection`, Seq(e0,e1)) =>
        lazabs.ast.ASTree.SetIntersect(rvT(e0).stype(SetType(IntegerType())),rvT(e1).stype(SetType(IntegerType())))
      case IConstant(`emptyset`) =>
        lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType()))
      case IConstant(cterm) =>
        val pattern = """x(\d+)(\w+)""".r
        symMap(cterm) match {
          case pattern(cVersion,n) =>
            lazabs.ast.ASTree.Variable(n,None).stype(IntegerType())
          case noVersion@_ =>
            lazabs.ast.ASTree.Variable(noVersion,None).stype(IntegerType())
        }
      case IVariable(index) => lazabs.ast.ASTree.Variable("i",Some(0)).stype(IntegerType())      
      case IIntLit(value) => lazabs.ast.ASTree.NumericalConst(value.intValueSafe)
      case _ =>
        println("Error in conversion from Princess to Eldarica (ITerm): " + t + " sublcass of " + t.getClass)
        BoolConst(false)
    }

    def rvF(t: IFormula): Expression = t match {

      case IIntFormula(IIntRelation.EqZero, IPlus(IFunApp(`difference`, Seq(left, right)), ITimes(IdealInt.MINUS_ONE, `emptyset`))) =>
        lazabs.ast.ASTree.SetSubset(rvT(left).stype(SetType(IntegerType())),
          rvT(right).stype(SetType(IntegerType())))
      case IIntFormula(IIntRelation.EqZero, IFunApp(`size`, Seq(e))) =>
        lazabs.ast.ASTree.Equality(rvT(e).stype(SetType(IntegerType())),lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType())))      
      case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, `emptyset`))) =>
        lazabs.ast.ASTree.Equality(rvT(e1).stype(SetType(IntegerType())),lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType())))
      case INot(IIntFormula(IIntRelation.EqZero, IPlus(ap.parser.IIntLit(ap.basetypes.IdealInt.MINUS_ONE), 
          IFunApp(`size`, Seq(IFunApp(`difference`, Seq(IFunApp(`singleton`, Seq(e1)), e2))))))) =>
        lazabs.ast.ASTree.SetContains(rvT(e2).stype(SetType(IntegerType())),rvT(e1).stype(IntegerType()))
      //case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        //lazabs.ast.ASTree.Equality(rvT(e1).stype(SetType(IntegerType())),rvT(e2).stype(SetType(IntegerType())))

      case IIntFormula(IIntRelation.EqZero, IPlus(IIntLit(value), e)) =>
        lazabs.ast.ASTree.Equality(rvT(e), NumericalConst((-value).intValueSafe))
      case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        lazabs.ast.ASTree.Equality(rvT(e1),rvT(e2))
      case IIntFormula(IIntRelation.EqZero, IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1)) =>
        lazabs.ast.ASTree.Equality(rvT(e2),rvT(e1))
//      case IIntFormula(IIntRelation.EqZero, IPlus(e1, e2)) =>
//        lazabs.ast.ASTree.Equality(rvT(e1),lazabs.ast.ASTree.Minus(rvT(e2)))
      case IIntFormula(IIntRelation.EqZero, e) => lazabs.ast.ASTree.Equality(rvT(e).stype(IntegerType()), NumericalConst(0))

      case IIntFormula(IIntRelation.GeqZero, IPlus(IIntLit(value), ITimes(ap.basetypes.IdealInt.MINUS_ONE, e))) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e).stype(IntegerType()), NumericalConst(value.intValueSafe))
      case IIntFormula(IIntRelation.GeqZero, IPlus(IIntLit(value), e)) =>
        lazabs.ast.ASTree.GreaterThanEqual(rvT(e).stype(IntegerType()), NumericalConst((-value).intValueSafe))
      case IIntFormula(IIntRelation.GeqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        lazabs.ast.ASTree.GreaterThanEqual(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IIntFormula(IIntRelation.GeqZero, IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1)) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e2).stype(IntegerType()), rvT(e1).stype(IntegerType()))
      case IIntFormula(IIntRelation.GeqZero, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e)) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e).stype(IntegerType()), NumericalConst(0))
      case IIntFormula(IIntRelation.GeqZero, e) => lazabs.ast.ASTree.GreaterThanEqual(rvT(e).stype(IntegerType()), NumericalConst(0))

      case IBinFormula(IBinJunctor.And, e1, e2) => lazabs.ast.ASTree.Conjunction(rvF(e1).stype(BooleanType()), rvF(e2).stype(BooleanType()))
      case IBinFormula(IBinJunctor.Or, e1, e2) => lazabs.ast.ASTree.Disjunction(rvF(e1).stype(BooleanType()), rvF(e2).stype(BooleanType()))
      case IQuantified(Quantifier.EX, e) => lazabs.ast.ASTree.Existential(BinderVariable("i").stype(IntegerType()), rvF(e).stype(BooleanType()))
      case IQuantified(Quantifier.ALL, e) => lazabs.ast.ASTree.Universal(BinderVariable("i").stype(IntegerType()), rvF(e).stype(BooleanType()))
      case INot(e) => lazabs.ast.ASTree.Not(rvF(e).stype(BooleanType()))
      case IBoolLit(b) => lazabs.ast.ASTree.BoolConst(b)
      case _ =>
        println("Error in conversion from Princess to Eldarica (IFormula): " + t + " sublcass of " + t.getClass)
        BoolConst(false)
    }

    rvF(t)
  }
    
  // PartNames used in interpolation queries
  private def partNameStream(num : Int) : Stream[PartName] =
    Stream.cons(new PartName("part" + num), partNameStream(num + 1))
  private val globalPartNames = partNameStream(0)
  
  def pathInterpols(fs: List[Expression]): List[Expression] = {
    Prover.increaseInterpolationConsultation
    var (formulas,symbolMap) = formula2Princess(fs)
    val partNames = (globalPartNames take formulas.size).toList
    val path = formulas.zip(partNames).map(fn => INamedPart(fn._2, fn._1.asInstanceOf[IFormula]))
    val partitions : List[IInterpolantSpec] = (1 until partNames.size).map(i => (partNames.splitAt(i))).map(x => IInterpolantSpec(x._1,x._2)).toList
    val interpolants = interpolate(path.reduceLeft[IFormula](_&_),symbolMap.values.toSeq,partitions) match {
      case None =>
        println("No interpolants found")
        lazabs.art.RTreeMethods.stopTimer
        List()
      case Some(is) => is
    }
    val reverseSymMap = (for ((k, v) <- symbolMap.iterator) yield (v -> k)).toMap
    interpolants.map((formula2EldaricaRemoveVersions(_, reverseSymMap)))
  }
  
  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = {
    Prover.increaseTheoremProverConsultation
    val (formulas,symbolMap) = formula2Princess(List(e))
    //println("sat: " + formula.head)
    Some(isSat(formulas.head.asInstanceOf[IFormula], symbolMap.values.toSeq))
  }

  def elimQuantifiers(e : Expression) : Expression = {
    var (Seq(formula),symbolMap) = formula2Princess(List(e))
    //println("qe: " + formula)
    val rawRes = elimQuans(formula.asInstanceOf[IFormula], symbolMap.values.toSeq)
    val reverseSymMap = (for ((k, v) <- symbolMap.iterator) yield (v -> k)).toMap
    formula2EldaricaRemoveVersions(rawRes, reverseSymMap)
  }

  def simplify(e : Expression) : Expression = {
    var (Seq(formula),symbolMap) = formula2Princess(List(e))
    //println("qe: " + formula)
    val rawRes = dnfSimplify(formula.asInstanceOf[IFormula], symbolMap.values.toSeq)
    val reverseSymMap = (for ((k, v) <- symbolMap.iterator) yield (v -> k)).toMap
    formula2EldaricaRemoveVersions(rawRes, reverseSymMap)
  }

}
