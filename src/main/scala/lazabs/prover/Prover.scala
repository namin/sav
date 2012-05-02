package lazabs.prover

import lazabs.ast.ASTree._

object TheoremProver extends Enumeration {
  type TheoremProver = Value
  val Z3, PRINCESS = Value
}

object Prover {
  import lazabs.prover.TheoremProver._
  var prover: TheoremProver = PRINCESS

  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = {
    prover match {
      case PRINCESS => PrincessWrapper.isSatisfiable(e)
      case Z3 => Z3Wrapper.isSatisfiable(e)
    }
  }
  
  def isValid(e: Expression): Option[Boolean] = isSatisfiable(Not(e)).map(!_)
}
