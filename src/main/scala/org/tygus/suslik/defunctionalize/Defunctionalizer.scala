package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._

import scala.collection.mutable.Stack
import scala.collection.immutable.SortedSet

class Defunctionalizer (newName: Ident, pred: InductivePredicate, fs: Seq[PredicateValue]) {

  val funMap : Map[String, PredicateValue] = pred.params.filter(
    {
      case (_, PredType) => true
      case _ => false
    }).map(_._1).zip(fs).map({
      case (Var(n), f) => (n, f)
    }).toMap


  // NOTE:
  //   - In the list of functions: Ensure that no free variables exist in the
  //   result of applications of the function, other than what is passed in as an
  //   argument.
  //   This requirement is to avoid variable capture.
  //
  //   - 'newName' should be a fresh name w.r.t. the names of the other
  //   inductive predicates
  def defunctionalizeDef(): InductivePredicate = {
    val newParams = pred.params.filter(
      {
        case (_, PredType) => false
        case _ => true
      })

    val newClauses = pred.clauses.map((c: InductiveClause) => defunctionalizeClause(c))

    InductivePredicate(newName, newParams, newClauses)
  }

  private def defunctionalizeClause(clause: InductiveClause): InductiveClause = {
    InductiveClause(clause.selector, defunctionalizeAssertion(clause.asn))
  }

  private def defunctionalizeAssertion(asn: Assertion): Assertion = {
    Assertion(defunctionalizePFormula(asn.phi), defunctionalizeSFormula(asn.sigma))
  }

  private def defunctionalizePFormula(phi: PFormula): PFormula = {
    PFormula(phi.conjuncts.flatMap((e : Expr) => defunctionalizeExpr(e)))
  }

  private def defunctionalizeSFormula(sigma: SFormula): SFormula = {
    SFormula(sigma.chunks.flatMap((chunk: Heaplet) => defunctionalizeHeaplet(chunk)))
  }

  // Spatial part
  private def defunctionalizeHeaplet(chunk: Heaplet): Seq[Heaplet] = {
    chunk match {
      case SApp(predIdent, args, tag, card) =>
        if (predIdent == pred.name) {
          // Recursive call

          // NOTE: We do not currently support changing predicate abstractions
          // in recursive calls

          Seq(SApp(newName, withoutPredAbstractions(pred.params, args), tag, card))

        } else {
          funMap get predIdent match {
            case None => Seq(chunk)
            case Some(sp @ SPredicateValue(_)) => sp.apply(args)
            case Some(PPredicateValue(_)) =>
              throw new Exception("Pure predicate used as a spatial predicate: " + newName)
          }
        }

      case _ => Seq(chunk)
    }
  }


  // Pure part
  private def defunctionalizeExpr(e: Expr): SortedSet[Expr] = {
    e match {
      case PApp(predIdent, args) =>
        funMap get predIdent match {
          case None =>
            throw new Exception(s"Invalid pure predicate application: ${e}")
          case Some(SPredicateValue(_)) =>
            throw new Exception(s"Spatial predicate used as a pure predicate: ${newName}")
          case Some(p @ PPredicateValue(_)) => p.apply(args)
        }
      case _ => SortedSet[Expr](e)
    }
  }

  private def withoutPredAbstractions(params: Formals, args: Seq[Expr]): Seq[Expr] = {
    (params.toSeq, args).zipped.filter((param, _) =>
        param match {
          case (_, PredType) => false
          case _ => true
        }
      )._2
  }


}

sealed abstract class PredicateValue(abstr: PredicateAbstraction) {
  protected def handleFreeVars() = {
    val freeVars = abstr.vars.diff(abstr.args.map(Var(_)).toSet)

    if (!freeVars.isEmpty) {
      throw new Exception("Free variables in predicate abstraction (closures not yet supported)")
    }
  }
}

case class SPredicateValue(abstr: SpatialPredicateAbstraction) extends PredicateValue(abstr) {
  def apply(args: Seq[Expr]): List[Heaplet] = {
    val st = (abstr.args, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    handleFreeVars()

    abstr.body.subst(st.toMap).chunks
  }
}

case class PPredicateValue(abstr: PurePredicateAbstraction) extends PredicateValue(abstr) {
  def apply(args: Seq[Expr]): SortedSet[Expr] = {
    val st = (abstr.args, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    handleFreeVars()

    abstr.body.subst(st.toMap).conjuncts.iterator.to[SortedSet]
  }
}

