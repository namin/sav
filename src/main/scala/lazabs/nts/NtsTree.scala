package lazabs.nts

import lazabs.ast.ASTree._
import scala.reflect._

case class Nts(aGlobalVars: List[Variable], aSystems: List[NtsSubsystem]) {
  @BeanProperty var globalVars = aGlobalVars
  @BeanProperty var systems = aSystems  
}
case class NtsTransition(source: Int, target: Int, formula: Expression)
case class NtsSubsystem(aName: String, aTransitions: List[NtsTransition], aInputVars: List[Variable], aOutputVars: List[Variable], aVars: List[Variable], aInitStates: List[Int], aFinalStates: List[Int], aErrorStates: List[Int]) {
  @BeanProperty var name = aName 
  @BeanProperty var transitions = aTransitions
  @BeanProperty var inputVars = aInputVars
  @BeanProperty var outputVars = aOutputVars 
  @BeanProperty var vars = aVars   // local variables + input variables + outputvariables + global variables
  @BeanProperty var initStates = aInitStates
  @BeanProperty var finalStates = aFinalStates
  @BeanProperty var errorStates = aErrorStates
}

case class NTSCall(aCalleeName: String, aActualParameters: List[Expression], aReturnVars: List[Variable], aHavoc: Option[List[Variable]]) extends Expression {
  @BeanProperty var calleeName = aCalleeName
  @BeanProperty var actualParameters = aActualParameters
  @BeanProperty var returnVars = aReturnVars
  @BeanProperty var havoc = aHavoc
}