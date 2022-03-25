package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._

import scala.collection.mutable.Stack
import scala.collection.immutable.SortedSet

class Defunctionalizer (newName: Ident, pred: InductivePredicate) {

  // NOTE:
  //   - In the list of functions: Ensure that no free variables exist in the
  //   result of applications of the function, other than what is passed in as an
  //   argument.
  //   This requirement is to avoid variable capture.
  //
  //   - 'newName' should be a fresh name w.r.t. the names of the other
  //   inductive predicates
  def defunctionalizeDef(fs: Seq[PredicateValue]): InductivePredicate = {
    var params = pred.params

    val funMap = scala.collection.mutable.Map[String, PredicateValue]()

    val fStack = scala.collection.mutable.Stack[PredicateValue]()
    fStack.pushAll(fs.reverse)

    val newParams = scala.collection.mutable.Stack[(Var, SSLType)]()

    for (param <- params) {
      param match {
        case (Var(s), PredType) => {
          val f = fStack.pop()
          funMap += (s -> f)
        }

        case (_, _) => newParams.push(param)
      }
    }

    val funMapImm = funMap.toMap

    val newClauses = pred.clauses.map((c: InductiveClause) => defunctionalizeClause(c, funMapImm))

    InductivePredicate(newName, newParams.toList.reverse, newClauses)
  }

  private def defunctionalizeClause(clause: InductiveClause, funMap: Map[String, PredicateValue]): InductiveClause = {
    InductiveClause(clause.selector, defunctionalizeAssertion(clause.asn, funMap))
  }

  private def defunctionalizeAssertion(asn: Assertion, funMap: Map[String, PredicateValue]): Assertion = {
    Assertion(defunctionalizePFormula(asn.phi, funMap), defunctionalizeSFormula(asn.sigma, funMap))
  }

  private def defunctionalizePFormula(phi: PFormula, funMap: Map[String, PredicateValue]): PFormula = {
    PFormula(phi.conjuncts.flatMap((e : Expr) => defunctionalizeExpr(e, funMap)))
  }

  private def defunctionalizeSFormula(sigma: SFormula, funMap: Map[String, PredicateValue]): SFormula = {
    SFormula(sigma.chunks.flatMap((chunk: Heaplet) => defunctionalizeHeaplet(chunk, funMap)))
  }

  // Spatial part
  private def defunctionalizeHeaplet(chunk: Heaplet, funMap: Map[String, PredicateValue]): Seq[Heaplet] = {
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
            case Some(PPredicateValue(_)) => // Seq(chunk) // TODO: Generate an error here
              throw new Exception("Pure predicate used as a spatial predicate: " + newName)
          }
        }

      case _ => Seq(chunk)
    }
  }


  // Pure part
  private def defunctionalizeExpr(e: Expr, funMap: Map[String, PredicateValue]): SortedSet[Expr] = {
    e match {
      case PApp(predIdent, args) =>
        funMap get predIdent match {
          case None =>
            throw new Exception(s"Invalid pure predicate application: ${e}")
          case Some(SPredicateValue(_)) => // SortedSet[Expr](e) // TODO: Generate an error here
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

sealed abstract class PredicateValue {
}


case class SPredicateValue(abstr: SpatialPredicateAbstraction) extends PredicateValue {
  def apply(args: Seq[Expr]): List[Heaplet] = {
    val st = (abstr.args, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    abstr.body.subst(st.toMap).chunks
  }

  // private def applyInHeaplet(args: Seq[Expr], heaplet: Heaplet): Heaplet = {
  //   // heaplet match {
  //   //   case PointsTo(_, _, _) => heaplet
  //   //   case Block(_, _) => heaplet
  //   //   case SApp(fName, args, tag, card) =>
  //   //     if (fName == abstr.name) {
  //   //     } else {
  //   //     }
  //   //     heaplet
  //   // }
  // }
}

case class PPredicateValue(abstr: PurePredicateAbstraction) extends PredicateValue {
  def apply(args: Seq[Expr]): SortedSet[Expr] = {
    val st = (abstr.args, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    abstr.body.subst(st.toMap).conjuncts.iterator.to[SortedSet]
  }
}

// case class SPredicateValue(fun: Seq[Expr] => List[Heaplet]) extends PredicateValue {
// }

// case class PPredicateValue(fun: Seq[Expr] => SortedSet[Expr]) extends PredicateValue {
// }

