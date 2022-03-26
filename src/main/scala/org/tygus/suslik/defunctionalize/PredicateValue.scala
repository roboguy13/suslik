package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic.Heaplet

import scala.collection.immutable.SortedSet

sealed abstract class PredicateValue(abstr: PredicateAbstraction) {
  val params: Seq[Ident] = abstr.params
  val fvNames: Seq[Ident] = params.diff(params.map(Var(_))).toSeq

  // protected def assertNoFreeVars() = {
  //   val freeVars = abstr.vars.diff(abstr.args.map(Var(_)).toSet)

  //   if (!freeVars.isEmpty) {
  //     throw new Exception("Free variables in predicate abstraction (closures not yet supported)")
  //   }
  // }
}

case class SPredicateValue(abstr: SpatialPredicateAbstraction)
  extends PredicateValue(abstr) {

  def apply(args: Seq[Expr]): List[Heaplet] = {
    val st = (abstr.params, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    // assertNoFreeVars()

    abstr.body.subst(st.toMap).chunks
  }
}

case class PPredicateValue(abstr: PurePredicateAbstraction)
  extends PredicateValue(abstr) {

  def apply(args: Seq[Expr]): SortedSet[Expr] = {
    val st = (abstr.params, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    // assertNoFreeVars()

    abstr.body.subst(st.toMap).conjuncts.iterator.to[SortedSet]
  }
}

