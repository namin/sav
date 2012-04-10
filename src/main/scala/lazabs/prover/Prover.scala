package lazabs.prover

import lazabs.ast.ASTree._

object Prover {
  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = PrincessWrapper.isSatisfiable(e)
  
  def isValid(e: Expression): Option[Boolean] = isSatisfiable(Not(e)).map(!_)
}
