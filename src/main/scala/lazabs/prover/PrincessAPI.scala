package lazabs.prover

import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression._
import ap.Signature
import ap.PresburgerTools
import ap.proof.ModelSearchProver
import ap.proof.certificates.DotLineariser
import ap.terfor.{ConstantTerm,TermOrder}
import ap.terfor.conjunctions.{Conjunction,ReduceWithConjunction,SetEliminator}
import ap.parameters.{PreprocessingSettings,GoalSettings,Param}
import ap.interpolants.{Interpolator, InterpolationContext, ProofSimplifier, InterpolantSimplifier}
import ap.terfor.conjunctions.Quantifier

abstract class PrincessAPI {

  //////////////////////////////////////////////////////////////////////////////
  // Public symbols that can be used in formulae passed to the operations of
  // this API

  // functions for arrays
  val select = new IFunction("select", 2, false, false)
  val store = new IFunction("store", 3, false, false)

  // functions for sets
  protected val emptyset_const = new ap.terfor.ConstantTerm("emptyset")
  val emptyset = new IConstant(emptyset_const)
  val singleton = new IFunction("singleton", 1, false, false)  // singleton set
  val union = new IFunction("union", 2, false, false)
  val intersection = new IFunction("intersection", 2, false, false)
  //private val subsetof = new IFunction("subsetof", 2, false, false)
  val difference = new IFunction("difference", 2, false, false)
  val size = new IFunction("size", 1, false, false)
  val complementation = new IFunction("complementation", 1, false, false)
  
  //////////////////////////////////////////////////////////////////////////////
  // Some convenience operations for frequently needed operations expressed
  // in terms of the previous more basic symbols

  def subsetof(a : ITerm, b : ITerm) : IFormula
  def setEqual(a : ITerm, b : ITerm) : IFormula
  def isEmpty(a : ITerm) : IFormula
  def in(a : ITerm, b : ITerm) : IFormula

  def div(a : ITerm, b : ITerm) : ITerm 

  def mod(a : ITerm, b : ITerm) : ITerm

  //////////////////////////////////////////////////////////////////////////////
  // Checking satisfiability of a formula
  
  def isSat(problem : IFormula, constants : Seq[ConstantTerm]) : Boolean
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing model of formulae

  def findModel(problem : IFormula,
                constants : Seq[ConstantTerm]) : Option[IFormula]
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing interpolants of formulae

  def interpolate(problem : IFormula,
                  constants : Seq[ConstantTerm],
                  partitions : List[IInterpolantSpec]) : Option[List[IFormula]]

}

////////////////////////////////////////////////////////////////////////////////

abstract class AbstractPrincessAPI extends PrincessAPI {

  ap.util.Debug enableAllAssertions false

  //////////////////////////////////////////////////////////////////////////////
  // Some convenience operations for frequently needed operations expressed
  // in terms of the previous more basic symbols

  def subsetof(a : ITerm, b : ITerm) : IFormula = (size(difference(a, b)) === 0)
//  def setEqual(a : ITerm, b : ITerm) : IFormula = (subsetof(a, b) & subsetof(b, a))
  def setEqual(a : ITerm, b : ITerm) : IFormula = (a, b) match {
    case (a : IConstant, b : IConstant) => a === b
    case _ => (subsetof(a, b) & subsetof(b, a))
  }
  def isEmpty(a : ITerm) : IFormula = (size(a) === 0)
  def in(a : ITerm, b : ITerm) : IFormula = (size(difference(singleton(a), b)) === 0)

  def div(a : ITerm, b : ITerm) : ITerm = {
    val num = VariableShiftVisitor(a, 0, 1)
    val denom = VariableShiftVisitor(b, 0, 1)
    eps((v(0) * denom <= num) &
        ((num < v(0) * denom + denom) | (num < v(0) * denom - denom)))
  }

  def mod(a : ITerm, b : ITerm) : ITerm = {
    val num = VariableShiftVisitor(a, 0, 1)
    val denom = VariableShiftVisitor(b, 0, 1)
    eps((v(0) >= 0) & ((v(0) < denom) | (v(0) < -denom)) &
        ex(VariableShiftVisitor(num, 0, 1) ===
           v(0) * VariableShiftVisitor(denom, 0, 1) + v(1)))
  }

  //////////////////////////////////////////////////////////////////////////////
  // Checking satisfiability of a formula
  
  def isSat(problem : IFormula, constants : Seq[ConstantTerm]) : Boolean = {
    // signature of the problem
    val order = backgroundOrder extend constants
    val signature = new Signature(constants.toSet, Set(), Set(), order)
    
    // preprocessing: e.g., encode functions as predicates
    val (inputFormulas, _, signature2) =
      Preprocessing(!problem,
                    List(),
                    signature,
                    preprocSettings,
                    functionEncoder)
    val order2 = signature2.order
    //println("sat check: " + problem)

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == i(true))
    
    // convert to internal representation
    val formulas =
      for (f <- inputFormulas) yield
        Conjunction.conj(InputAbsy2Internal(removePartName(f), order2),
                         order2)

    satCheckProver.conclude(formulas, order2)
                  .checkValidity(false) != Left(Conjunction.FALSE)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing model of formulae

  def findModel(problem : IFormula,
                constants : Seq[ConstantTerm]) : Option[IFormula] = {
    // signature of the problem
    val order = backgroundOrder extend constants
    val signature = new Signature(constants.toSet, Set(), Set(), order)
    
    // preprocessing: e.g., encode functions as predicates
    val (inputFormulas, _, signature2) =
      Preprocessing(!problem,
                    List(),
                    signature,
                    preprocSettings,
                    functionEncoder)
    val order2 = signature2.order

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == i(true))
    
    // convert to internal representation
    val formulas =
      for (f <- inputFormulas) yield
        Conjunction.conj(InputAbsy2Internal(removePartName(f), order2),
                         order2)

    satCheckProver.conclude(formulas, order2).checkValidity(true) match {
      case Left(Conjunction.FALSE) =>
        // unsat
        None
      case Left(model) =>
        // found a model
        Some((new Simplifier)(
          Internal2InputAbsy(model, functionEncoder.predTranslation)))
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing interpolants of formulae

  def interpolate(problem : IFormula,
                  constants : Seq[ConstantTerm],
                  partitions : List[IInterpolantSpec]) : Option[List[IFormula]] = {
    // signature of the problem
    val order = backgroundOrder extend constants
    val signature = new Signature(constants.toSet, Set(), Set(), order)
    
    // preprocessing: e.g., encode functions as predicates
    val (inputFormulas, interpolantS, signature2) =
      Preprocessing(!problem,
                    partitions,
                    signature,
                    PreprocessingSettings.DEFAULT,
                    functionEncoder)
    val order2 = signature2.order

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == i(true))
    //println("Interpolation: " + problem)
    //println(constants)

    // convert to internal representation, pre-simplify
    val formulas =
      for (f <- inputFormulas) yield
        ReduceWithConjunction(Conjunction.TRUE, order2)(
          Conjunction.conj(InputAbsy2Internal(removePartName(f), order2),
                           order2))                           

    interpolationProver.conclude(formulas, order2).checkValidity(false) match {
      case Left(_) =>
        // formula is sat
        None
      
      case Right(cert) => {
        // found a proof of unsatisfiability, extract an interpolant

        //print("Found proof (" + cert.inferenceCount + "), simplifying ")
        val simpCert = ProofSimplifier(cert) // simplify the proof if possible
        //println("(" + simpCert.inferenceCount + ")")

        val namedParts =
          (for ((INamedPart(name, _), f) <- inputFormulas zip formulas)
           yield (name -> f)).toMap + (PartName.NO_NAME -> backgroundPred)
        
        Some(for (s <- interpolantS) yield {
          val iContext = InterpolationContext(namedParts, s, order2)
          val interpolant = Internal2InputAbsy(Interpolator(simpCert, iContext, true),
                                               functionEncoder.predTranslation)
          // simplify to get rid of quantifiers that might have been introduced
          // to represent function application
          interpolantSimplifier(interpolant)
        })
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // simplifier
  class SetSimplifier(select : IFunction, store : IFunction) extends InterpolantSimplifier(select,store) {
    protected override def furtherSimplifications(expr : IExpression) = {
      def simplify(ex: IExpression): IExpression = ex match {
        case IIntFormula(IIntRelation.GeqZero,
                         IPlus(IIntLit(IdealInt.MINUS_ONE),
                         IFunApp(`size`, e1))) =>
             e1.head =/= emptyset
        case IFunApp(`intersection`, Seq(e1, IFunApp(`complementation`, Seq(e2)))) =>
             difference(e1, e2)
        case IFunApp(`intersection`, Seq(IFunApp(`complementation`, Seq(e2)), e1)) =>
             difference(e1, e2)
        case _ => ex
      }
      super.furtherSimplifications(simplify(expr))
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // set up the provers used for sat and interpolation
  
  protected val functionEncoder = new FunctionEncoder (true, false)

  // the background predicate
  protected val backgroundPred : Conjunction
  protected val backgroundOrder : TermOrder

  protected val preprocSettings : PreprocessingSettings
  protected val satCheckSettings : GoalSettings
  
  private val interpolationSettings =
    Param.PROOF_CONSTRUCTION.set(satCheckSettings, true)

  // create the incremental provers, and initialise them with the background
  // predicate
  private val satCheckProver = {
    val prover = ModelSearchProver emptyIncProver satCheckSettings
    prover.conclude(backgroundPred, backgroundOrder)
  }
  
  private val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, backgroundOrder)
  }
  
  private val interpolantSimplifier = new SetSimplifier(select, store)
      
}

////////////////////////////////////////////////////////////////////////////////

class PrincessAPI_v1 extends AbstractPrincessAPI {
  // create the background predicate
  lazy protected val (backgroundPred, backgroundOrder) = {
    // the array axioms    
    val axioms = IBoolLit(true)

    val initSignature =
      new Signature(Set(), Set(), Set(), TermOrder.EMPTY extend List())
    val (iBackgroundFors, _, baseSignature) =
      Preprocessing(!axioms, List(),
                    initSignature,
                    PreprocessingSettings.DEFAULT, functionEncoder)
    functionEncoder.clearAxioms

    val iBackgroundPred =
      connect(for (INamedPart(_, f) <- iBackgroundFors.iterator) yield f,
              IBinJunctor.Or)
    
    val order = baseSignature.order
    (ReduceWithConjunction(Conjunction.TRUE, order)(
        Conjunction.conj(InputAbsy2Internal(iBackgroundPred, order), order)),
     order)
  }

  protected lazy val preprocSettings =
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(PreprocessingSettings.DEFAULT,
       Set(select, store))

  protected lazy val satCheckSettings =
    Param.FUNCTIONAL_PREDICATES.set(GoalSettings.DEFAULT, backgroundPred.predicates)
}
