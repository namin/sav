package lazabs.utils

import lazabs.ast.ASTree._
import lazabs.types._


/**
 * manipulates a formula 
 *
 */
object Manip {
  /*
   * eliminate common disjuncts
   */
  def simplifyDisjuncts(e: Expression): Expression = {
    def collect(e: Expression): Set[Expression] = {
      e match {
        case Disjunction(lhs, rhs) => collect(lhs) union collect(rhs)
        case _ => Set(e)
      }
    }
    val disjuncts = collect(e)
    simplify(disjuncts.fold(BoolConst(false))(Disjunction(_, _)))
  }
  
  /*
   * short circuits a boolean formula
   */
  def simplify(e: Expression): Expression = e match {
    case Not(Not(exp)) => simplify(exp)
    case Not(exp) => Not(simplify(exp))   
    case Conjunction(BoolConst(false),exp) => BoolConst(false) 
    case Conjunction(exp,BoolConst(false)) => BoolConst(false)
    case Conjunction(BoolConst(true),exp) => simplify(exp) 
    case Conjunction(exp,BoolConst(true)) => simplify(exp)
    case Disjunction(exp,BoolConst(true)) => BoolConst(true)    
    case Disjunction(BoolConst(true),exp) => BoolConst(true)
    case Disjunction(exp,BoolConst(false)) => simplify(exp)
    case Disjunction(BoolConst(false),exp) => simplify(exp)
    case Conjunction(exp1,exp2) =>
      val simp1 = simplify(exp1)
      val simp2 = simplify(exp2)
      if(simp1 == BoolConst(false) || simp2 == BoolConst(false)) BoolConst(false) else Conjunction(simp1,simp2)
    case Disjunction(exp1,exp2) => 
      val simp1 = simplify(exp1)
      val simp2 = simplify(exp2)
      if(simp1 == BoolConst(true) || simp2 == BoolConst(true)) BoolConst(true) else Disjunction(simp1,simp2)
    case Equality(exp1,exp2) => Equality(simplify(exp1),simplify(exp2))
    case Inequality(exp1,exp2) => Inequality(simplify(exp1),simplify(exp2))
    case Existential(BinderVariable(v),qe) => {
      if (!freeVars(qe).contains(v)) qe
      else e
    }
    case Universal(BinderVariable(v),qe) => {
      if (!freeVars(qe).contains(v)) qe
      else e
    }
    case _ => e
  }

  /*
   * computes the set of free variables of a formula
   */
  def freeVars(f: Expression): Set[String] = {
    def fv(f: Expression, bv: List[String]): Set[String] = f match {
      case BinaryExpression(e1, op, e2) => fv(e1, bv) ++ fv(e2, bv)
      case Existential(BinderVariable(name), body) => fv(body, name :: bv)
      case Universal(BinderVariable(name), body) => fv(body, name :: bv)
      case v@Variable(name,_) if !bv.contains(name)=> Set[String](v.name)
      case _ => Set()
    }
    fv(f, List[String]())
  }

  /*
   * Substitues expressions for variables in formulas
   */
  def subst(x:ASTree, substs:Map[String,Expression]):ASTree = x match {
    case e:Expression => subst(e, substs)
    case t:ASTree => t
  }
  def subst(e:Expression, substs:Map[String,Expression]) : Expression = e match {
    case Block(l) => Block(l map {subst(_, substs)})
    case FunctionCall(f, l) => FunctionCall(f,l.map {subst(_, substs)})
    case v@Variable(name, _) => substs.getOrElse(name, v)
    case Existential(v,e) => Existential(v,subst(e, substs - v.name))
    case Universal(v,e) => Universal(v,subst(e, substs - v.name))
    case TernaryExpression(op, e1, e2, e3) => 
      TernaryExpression(op, subst(e1,substs), subst(e2,substs), subst(e3,substs))
    case BinaryExpression(e1, op, e2) => 
      BinaryExpression(subst(e1,substs), op, subst(e2,substs))
    case UnaryExpression(op, e1) => 
      UnaryExpression(op, subst(e1,substs))
    case _ => e
  }
}
