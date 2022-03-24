package org.tygus.suslik.preprocess

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import scala.collection.mutable.Stack

class Defunctionalizer (pred : InductivePredicate) {
  def defunctionalizedDef(fs : List[Expr => Expr]) : InductivePredicate =
  {
    // var predResult = pred.copy()

    var params = pred.params

    val funMap = scala.collection.mutable.Map[String, Expr => Expr]()

    val fStack = scala.collection.mutable.Stack[Expr => Expr]()
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

      // TODO: Use fresh name
    return InductivePredicate(pred.name, newParams.toList.reverse, newClauses)
  }

  def defunctionalizeClause(clause0 : InductiveClause, funMap : Map[String, Expr => Expr]) : InductiveClause =
  {
    var clause = clause0.copy()

    return clause
  }

  def defunctionalizeAssertion(asn0 : Assertion, funMap : Map[String, Expr => Expr]) : Assertion =
  {
    var asn = asn0.copy()

    return asn
  }
}

