package lazabs.bapa

/**
 * rewrites a bapa formula into a Presburger formula
 */

import lazabs.ast.ASTree._

object BapaRewrite {
  def apply(ex: Expression): Expression = {println("rewriting: " + lazabs.viewer.ScalaPrinter(ex)); ex match {
    case Conjunction(e1,e2) => Conjunction(BapaRewrite(e1),BapaRewrite(e2))
    case _ => ex
  }}
}
