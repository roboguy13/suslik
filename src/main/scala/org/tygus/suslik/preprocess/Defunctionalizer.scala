package org.tygus.suslik.preprocess

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
// import org.tygus.suslik.logic.Heaplet._
import org.tygus.suslik.logic.SFormula._

import scala.collection.mutable.Stack
import scala.collection.immutable.SortedSet

class Defunctionalizer (pred : InductivePredicate) {

  // NOTE:
  //   - In the list of functions: Ensure that no free variables exist in the
  //   result of applications of the function, other than what is passed in as an
  //   argument.
  //   This requirement is to avoid variable capture.
  //
  //   - 'newName' should be a fresh name w.r.t. the names of the other
  //   inductive predicates
  def defunctionalizedDef(newName : Ident, fs : List[PredicateValue]) : InductivePredicate = {
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

    val newClauses = pred.clauses.map((c : InductiveClause) => defunctionalizeClause(c, funMapImm))

    InductivePredicate(newName, newParams.toList.reverse, newClauses)
  }

  def defunctionalizeClause(clause : InductiveClause, funMap : Map[String, PredicateValue]) : InductiveClause = {
    InductiveClause(clause.selector, defunctionalizeAssertion(clause.asn, funMap))
  }

  def defunctionalizeAssertion(asn : Assertion, funMap : Map[String, PredicateValue]) : Assertion = {
    Assertion(defunctionalizePFormula(asn.phi, funMap), asn.sigma)
  }

  def defunctionalizePFormula(phi : PFormula, funMap : Map[String, PredicateValue]) : PFormula = {
    PFormula(phi.conjuncts.map((e : Expr) => defunctionalizeExpr(e, funMap)))
  }

  def defunctionalizeSFormula(sigma : SFormula, funMap : Map[String, PredicateValue]) : SFormula = {
    SFormula(sigma.chunks.flatMap((chunk : Heaplet) => defunctionalizeHeaplet(chunk, funMap)))
  }

  // Spatial part
  def defunctionalizeHeaplet(chunk : Heaplet, funMap : Map[String, PredicateValue]) : List[Heaplet] = {
    chunk match {
      case SApp(predIdent, args, tag, card) =>
        funMap get predIdent match {
          case None => List(chunk)
          case Some(SPredicateValue(fun)) => fun(args)
          case Some(PPredicateValue(_)) => List(chunk) // TODO: Generate an error here
        }

      case _ => List(chunk)
    }
  }

  // Pure part
  def defunctionalizeExpr(e : Expr, funMap : Map[String, PredicateValue]) : Expr = {
    // TODO: Add applications to the syntax of the pure part and finish this
    throw new Exception("defunctionalizeExpr: Defunctionalization for pure parts of predicates not yet implemented")
  }

}

sealed abstract class PredicateValue {
}

case class SPredicateValue(fun : Seq[Expr] => List[Heaplet]) extends PredicateValue {
}

case class PPredicateValue(fun : Seq[Expr] => SortedSet[Expr]) extends PredicateValue {
}

