package org.tygus.suslik.preprocess

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._

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
    InductivePredicate(pred.name, newParams.toList.reverse, newClauses)
  }

  def defunctionalizeClause(clause : InductiveClause, funMap : Map[String, Expr => Expr]) : InductiveClause =
  {
    InductiveClause(clause.selector, defunctionalizeAssertion(clause.asn, funMap))
  }

  def defunctionalizeAssertion(asn : Assertion, funMap : Map[String, Expr => Expr]) : Assertion =
  {
    Assertion(defunctionalizePFormula(asn.phi, funMap), asn.sigma)
  }

  def defunctionalizePFormula(phi : PFormula, funMap : Map[String, Expr => Expr]) : PFormula =
  {
    PFormula(phi.conjuncts.map((e : Expr) => defunctionalizeExpr(e, funMap)))
  }

  def defunctionalizeExpr(e : Expr, funMap : Map[String, Expr => Expr]) : Expr =
  {
    e
  }
}

