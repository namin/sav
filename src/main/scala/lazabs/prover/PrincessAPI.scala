package lazabs.prover

import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression._
import ap.Signature
import ap.PresburgerTools
import ap.proof.{ModelSearchProver, ExhaustiveProver, QuantifierElimProver}
import ap.proof.certificates.DotLineariser
import ap.terfor.{ConstantTerm,TermOrder}
import ap.terfor.conjunctions.{Conjunction,ReduceWithConjunction,
                               IterativeClauseMatcher}
//import ap.terfor.conjunctions.SetEliminator
import ap.parameters.{PreprocessingSettings,GoalSettings,Param}
import ap.interpolants.{Interpolator, InterpolationContext, ProofSimplifier,
                        InterpolantSimplifier}
import ap.terfor.conjunctions.Quantifier
import ap.util.LRUCache

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
  // Eliminate quantifiers in a formula
  
  def elimQuans(problem : IFormula, constants : Seq[ConstantTerm]) : IFormula
  
  def dnfSimplify(f : IFormula, constants : Seq[ConstantTerm]) : IFormula

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
//    println("sat check: " + problem)
//    print(".")

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == i(true))
    
    // convert to internal representation
    val Seq(formula) =
      for (f <- inputFormulas) yield
        ReduceWithConjunction(Conjunction.TRUE, order2)(
          Conjunction.conj(InputAbsy2Internal(removePartName(f), order2), order2))

    if (formula.isTrue)
      false
    else if (formula.isFalse)
      true
    else if (canUseModelCheckProver(List(formula))) {
      chooseProver(List(formula), false)._1.conclude(formula, order2)
                                        .checkValidity(false) != Left(Conjunction.FALSE)
    } else {
      val (prover, backPred) = chooseExhaustiveProver(formula)
      !prover(Conjunction.implies(backPred, formula, order2), signature2).closingConstraint.isTrue
    }
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
        ReduceWithConjunction(Conjunction.TRUE, order2)(
          Conjunction.conj(InputAbsy2Internal(removePartName(f), order2), order2))

    assert(canUseModelCheckProver(formulas)) // otherwise, we have to explicitly apply QE first

    chooseProver(formulas, false)._1.conclude(formulas, order2)
                                    .checkValidity(true) match {
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
  // Eliminate quantifiers in a formula; currently this implementation only
  // handles Presburger formulae
  
  def elimQuans(f : IFormula, constants : Seq[ConstantTerm]) : IFormula = {
    // signature of the problem
    val order = backgroundOrder extend constants

    // convert to internal representation
    val intFormula =
      Conjunction.conj(InputAbsy2Internal(f, order), order)
    
    val withoutQuans =
      PresburgerTools.elimQuantifiersWithPreds(intFormula)
    
    interpolantSimplifier(Internal2InputAbsy(withoutQuans, Map()))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def dnfSimplify(f : IFormula, constants : Seq[ConstantTerm]) : IFormula = {
    // signature of the problem
    val order = backgroundOrder extend constants

    // convert to internal representation
    val intFormula =
      Conjunction.conj(InputAbsy2Internal(f, order), order)
    
    val simplified = !QuantifierElimProver(!intFormula, true, order)
    
    interpolantSimplifier(Internal2InputAbsy(simplified, Map()))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing interpolants of formulae

  private val interpolationCache =
    new LRUCache[(List[Conjunction], List[IInterpolantSpec]), Option[List[IFormula]]](10000)

  private var interpolationCount = 0

  private def dumpInterpolationQuery(problem : IFormula,
                                     partitions : List[IInterpolantSpec],
				     signature : Signature) : Unit = {
      // output the interpolation query to a file
      val interpolationFile =
        new java.io.FileOutputStream("interpolation-query-" +
                                     interpolationCount + ".smt2")

      val partFormulas = PartExtractor(!problem)
      // extract the order of formula parts from the first
      // interpolant specification

      val IInterpolantSpec(left, right) :: _ = partitions
      val sortedFormulas =
        for (part <- left ++ right) yield
          removePartName(partFormulas.find({
                           case INamedPart(`part`, _) => true
                           case _ => false
                         }).getOrElse(false))
      
      Console.withOut(interpolationFile) {
        SMTLineariser(sortedFormulas, signature,
                      "Eldarica interpolation query " + interpolationCount)
      }
      interpolationFile.close
      interpolationCount = interpolationCount + 1
  }

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
                    preprocSettings,
                    functionEncoder)
    val order2 = signature2.order

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == i(true))
//    println("Interpolation: " + problem)
//    println(constants)

    // convert to internal representation, pre-simplify
    val formulas =
      for (f <- inputFormulas) yield
        ReduceWithConjunction(Conjunction.TRUE, order2)(
          Conjunction.conj(InputAbsy2Internal(removePartName(f), order2),
                           order2))                           
    
//    if (interpolationCache.get((formulas, interpolantS)) != None)
//      println("Interpolation cache hit")

    interpolationCache((formulas, interpolantS)) {
//      dumpInterpolationQuery(problem, partitions, signature)

      assert(canUseModelCheckProver(formulas)) // otherwise, we have to explicitly apply QE first

      val (prover, backPred) = chooseProver(formulas, true)
      prover.conclude(formulas, order2)
            .checkValidity(false) match {
      case Left(_) =>
        // formula is sat
        None
      
      case Right(cert) => {
        // found a proof of unsatisfiability, extract an interpolant

//        print("Found proof (" + cert.inferenceCount + "), simplifying ")
        val simpCert = ProofSimplifier(cert) // simplify the proof if possible
//        println("(" + simpCert.inferenceCount + ")")

        val namedParts =
          (for ((INamedPart(name, _), f) <- inputFormulas zip formulas)
           yield (name -> f)).toMap + (PartName.NO_NAME -> backPred)

        var falseIntSpec : Option[IInterpolantSpec] = None
        Some(for (s <- interpolantS) yield {
	  falseIntSpec match {
	    case Some(spec) if (spec.left.toSet subsetOf s.left.toSet) =>
              i(false)
	    case _ => {
              val iContext = InterpolationContext(namedParts, s, order2)
  	      val internalInt = Interpolator(simpCert, iContext, true)
	      if (internalInt.isFalse) {
	        falseIntSpec = Some(s)
	        i(false)
	      } else {
                val interpolant = Internal2InputAbsy(internalInt,
	                                             functionEncoder.predTranslation)
                // simplify to get rid of quantifiers that might have been introduced
                // to represent function application
                interpolantSimplifier(interpolant)
	      }
	    }
	  }
        })
      }
    }}
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
  // Stronger simplifier for Presburger formulae

  private def dnfSimplify(c : Conjunction) : Conjunction =
    if (PresburgerTools isPresburger c)
      !QuantifierElimProver(!c, true, c.order)
    else
      c

  //////////////////////////////////////////////////////////////////////////////
  // set up the provers used for sat and interpolation

  // settings for empty background predicate
  protected val basicPreprocSettings : PreprocessingSettings =
    Param.CLAUSIFIER.set(PreprocessingSettings.DEFAULT,
                         Param.ClausifierOptions.BooleanCompactify)
  protected val basicSatCheckSettings : GoalSettings =
    GoalSettings.DEFAULT
  private val basicInterpolationSettings =
    Param.PROOF_CONSTRUCTION.set(basicSatCheckSettings, true)

  protected val functionEncoder = new FunctionEncoder (true, false)

  // the array/set background predicate
  protected val backgroundPred : Conjunction
  protected val backgroundOrder : TermOrder

  // settings for array/set background predicate
  protected val preprocSettings : PreprocessingSettings
  protected val satCheckSettings : GoalSettings
  
  private val interpolationSettings =
    Param.PROOF_CONSTRUCTION.set(satCheckSettings, true)

  // create the incremental provers, and initialise them with the background
  // predicate
  private lazy val basicSatCheckProver =
    ModelSearchProver emptyIncProver basicSatCheckSettings

  private lazy val basicExhaustiveProver =
    new ExhaustiveProver (true, basicSatCheckSettings)

  private lazy val exhaustiveProver =
    new ExhaustiveProver (true, satCheckSettings)

  private lazy val basicInterpolationProver =
    ModelSearchProver emptyIncProver basicInterpolationSettings

  private lazy val satCheckProver = {
    val prover = ModelSearchProver emptyIncProver satCheckSettings
    prover.conclude(backgroundPred, backgroundOrder)
  }
  
  private lazy val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, backgroundOrder)
  }

  /**
   * Choose the prover and the background predicate,
   * given a set of formulae
   */
  private def chooseProver(formulas : Iterable[Conjunction],
                           interpolation : Boolean) =
    if (formulas forall (_.predicates.isEmpty))
      (if (interpolation) basicInterpolationProver else basicSatCheckProver,
       Conjunction.TRUE)
    else
      (if (interpolation) interpolationProver else satCheckProver,
       backgroundPred)

  private def chooseExhaustiveProver(formula : Conjunction) =
    if (formula.predicates.isEmpty)
      (basicExhaustiveProver, Conjunction.TRUE)
    else
      (exhaustiveProver, backgroundPred)

  private def canUseModelCheckProver(formulas : Iterable[Conjunction]) =
    formulas forall (IterativeClauseMatcher isMatchableRec _)

  private val interpolantSimplifier = new SetSimplifier(select, store)
      
}

////////////////////////////////////////////////////////////////////////////////

class PrincessAPI_v1 extends AbstractPrincessAPI {

  // create the background predicate
  lazy protected val (backgroundPred, backgroundOrder) = {
    // the array axioms    
    val arrayAxioms =
      all(all(all(
          ITrigger(List(store(v(0), v(1), v(2))),
                   select(store(v(0), v(1), v(2)), v(1)) === v(2))
      ))) &
      all(all(all(all(
          ITrigger(List(select(store(v(0), v(1), v(2)), v(3))),
                   (v(1) === v(3)) |
                   (select(store(v(0), v(1), v(2)), v(3)) === select(v(0), v(3))))
      )))) &
      // as a convention, we assume that array 0 is constantly zero
      all(ITrigger(List(select(0, v(0))), select(0, v(0)) === 0))
 
    // the set axioms
    val setAxioms =
      all(
          ITrigger(List(size(v(0))),
                   size(v(0)) >= 0)
      ) &
      all(
          ITrigger(List(union(v(0), emptyset)),
                   union(v(0), emptyset) === v(0))
      ) &
      all(
          ITrigger(List(intersection(v(0), emptyset)),
                   intersection(v(0), emptyset) === emptyset)
      ) &
      all(
          ITrigger(List(difference(v(0), emptyset)),
                   difference(v(0), emptyset) === v(0))
      ) &
                   (size(emptyset) === 0) &
      all(all(
          ITrigger(List(union(v(0), v(1))),
                   union(v(0), v(1)) === union(v(1), v(0)))
      )) &
      all(
          ITrigger(List(union(v(0), v(0))),
                   union(v(0), v(0)) === v(0))
      ) &
      all(all(
          ITrigger(List(intersection(v(0), v(1))),
                   intersection(v(0), v(1)) === intersection(v(1), v(0)))
      )) &
      all(
          ITrigger(List(intersection(v(0), v(0))),
                   intersection(v(0), v(0)) === v(0))
      ) &
      all(all(
          ITrigger(List(intersection(intersection(v(1), v(0)), v(0))),
                   intersection(intersection(v(1), v(0)), v(0)) === intersection(v(1), v(0)))
      )) &
      all(all(
          ITrigger(List(size(union(v(0), v(1)))),
                   size(union(v(0), v(1))) === size(v(0)) + size(v(1)) - size(intersection(v(0), v(1))))
      )) &
      all(all(all(
          ITrigger(List(intersection(union(v(0), v(1)), v(2))),
                   intersection(union(v(0), v(1)), v(2)) === union(intersection(v(0), v(2)), intersection(v(1), v(2))))
      ))) &
      all(all(all(
          ITrigger(List(difference(union(v(0), v(1)), v(2))),
                   difference(union(v(0), v(1)), v(2)) === union(difference(v(0), v(2)), difference(v(1), v(2))))
      ))) &
/*      all(all(all(
          ITrigger(List(difference(v(0), intersection(v(1), v(2)))),
                   difference(v(0), intersection(v(1), v(2))) === union(difference(v(0), v(1)), difference(v(0), v(2))))
      ))) & */
      // axiom for splitting
      all(all(
          ITrigger(List(size(intersection(v(0), v(1)))),
          ITrigger(List(size(difference(v(0), v(1)))),
                   size(v(0)) === size(intersection(v(0), v(1))) + size(difference(v(0), v(1)))))
      )) &
      // axioms for interpreted elements
      all(
          ITrigger(List(size(singleton(v(0)))),
                   size(singleton(v(0))) === 1)
      ) &
      all(all(
          ITrigger(List(singleton(v(0)), singleton(v(1))),
                   (singleton(v(0)) === singleton(v(1))) ==> (v(0) === v(1)))
      ))
    
    val axioms = arrayAxioms & setAxioms

    val initSignature =
      new Signature(Set(emptyset_const), Set(), Set(),
                    TermOrder.EMPTY extend List(emptyset_const))
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
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(basicPreprocSettings,
       Set(select, store,
           singleton, union, intersection, difference, size, complementation))

  protected lazy val satCheckSettings =
    Param.FUNCTIONAL_PREDICATES.set(basicSatCheckSettings, backgroundPred.predicates)
}

////////////////////////////////////////////////////////////////////////////////

class PrincessAPI_v2 extends AbstractPrincessAPI {

  // create the background predicate
  lazy protected val (backgroundPred, backgroundOrder) = {
    // the array axioms    
    val arrayAxioms =
      all(all(all(
          ITrigger(List(store(v(0), v(1), v(2))),
                   select(store(v(0), v(1), v(2)), v(1)) === v(2))
      ))) &
      all(all(all(all(
          ITrigger(List(select(store(v(0), v(1), v(2)), v(3))),
                   (v(1) === v(3)) |
                   (select(store(v(0), v(1), v(2)), v(3)) === select(v(0), v(3))))
      )))) &
      // as a convention, we assume that array 0 is constantly zero
      all(ITrigger(List(select(0, v(0))), select(0, v(0)) === 0))

 
    val setAxioms =

//  \forall int x, y; {intersect(x, y)} intersect(x, y) = intersect(y, x)
      all(all(
          ITrigger(List(intersection(v(0), v(1))),
                   intersection(v(0), v(1)) === intersection(v(1), v(0)))
      )) &
//  \forall int x, y, z; {intersect(x, intersect(y, z))}
//      intersect(x, intersect(y, z)) = intersect(intersect(x, y), z)
      all(all(all(
          ITrigger(List(intersection(v(0), intersection(v(1), v(2)))),
                   intersection(v(0), intersection(v(1), v(2))) ===
                   intersection(intersection(v(0), v(1)), v(2)))
      ))) &
//  \forall int x; {intersect(x, x)} intersect(x, x) = x
      all(
          ITrigger(List(intersection(v(0), v(0))),
                   intersection(v(0), v(0)) === v(0))
      ) &
//  \forall int x; {complement(complement(x))} complement(complement(x)) = x
      all(
          ITrigger(List(complementation(complementation(v(0)))),
                   complementation(complementation(v(0))) === v(0))
      ) &
//  \forall int x; {intersect(x, complement(x))} intersect(x, complement(x)) = empty
      all(
          ITrigger(List(intersection(v(0), complementation(v(0)))),
                   intersection(v(0), complementation(v(0))) === emptyset)
      ) &
//  size(empty) = 0
      (size(emptyset) === 0) &
//  \forall int x; {intersect(x, empty)} intersect(x, empty) = empty
      all(
          ITrigger(List(intersection(v(0), emptyset)),
                   intersection(v(0), emptyset) === emptyset)
      ) &
//  \forall int x, y; {size(union(x, y))}
//     size(union(x, y)) = size(x) + size(y) - size(intersect(x, y))
      all(all(
          ITrigger(List(size(union(v(0), v(1)))),
                   size(union(v(0), v(1))) ===
                   size(v(0)) + size(v(1)) - size(intersection(v(0), v(1))))
      )) &
//  \forall int x, y, z; {size(intersect(union(x, y), z))}
//     size(intersect(z, union(x, y))) =
//       size(intersect(x, z)) + size(intersect(y, z)) - size(intersect(intersect(x, y), z))
      all(all(all(
          ITrigger(List(size(intersection(union(v(1), v(2)), v(0)))),
                   size(intersection(union(v(1), v(2)), v(0))) ===
                   size(intersection(v(0), v(1))) + size(intersection(v(0), v(2))) -
                      size(intersection(intersection(v(0), v(1)), v(2))))
      ))) &
//  \forall int x, y; {size(intersect(x, y))}
//     size(x) = size(intersect(x, y)) + size(intersect(x, complement(y)))
      all(all(
          ITrigger(List(size(intersection(v(0), v(1)))),
                   size(v(0)) === size(intersection(v(0), v(1))) +
                                  size(intersection(v(0), complementation(v(1)))))
      )) &
//  \forall int x; {size(x)} size(x) >= 0
      all(
          ITrigger(List(size(v(0))),
                   size(v(0)) >= 0)
      ) &
//  \forall int x, y; {difference(x, y)}
//                    difference(x, y) = intersection(x, complementation(y))
    all(all(
          ITrigger(List(difference(v(0), v(1))),
                   difference(v(0), v(1)) === intersection(v(0), complementation(v(1))))
    )) &
      // axioms for interpreted elements
      all(
          ITrigger(List(size(singleton(v(0)))),
                   size(singleton(v(0))) === 1)
      ) &
      all(all(
          ITrigger(List(singleton(v(0)), singleton(v(1))),
                   (singleton(v(0)) === singleton(v(1))) ==> (v(0) === v(1)))
      ))

    val axioms = arrayAxioms & setAxioms

    val initSignature =
      new Signature(Set(emptyset_const), Set(), Set(),
                    TermOrder.EMPTY extend List(emptyset_const))
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
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(basicPreprocSettings,
       Set(select, store,
           singleton, union, intersection, difference, size, complementation))
	   
  protected lazy val satCheckSettings = {
    var s = basicSatCheckSettings
    s = Param.FUNCTIONAL_PREDICATES.set(s, backgroundPred.predicates)
    
    // now the function encoder contains the predicates that functions
    // are translated to
    def predForFun(f : IFunction) = (functionEncoder.predTranslation.find {
      case (_, `f`) => true
      case _ => false
    }).get._1
    
/*    val setPredicates =
      SetEliminator.SetPredicates(predForFun(intersection),
                                  predForFun(union),
				  predForFun(complementation),
				  emptyset_const)
    
    s = Param.SET_PREDICATES.set(s, Some(setPredicates)) */
    s
  }

}
