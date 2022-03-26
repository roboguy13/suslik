package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._


object PredicateAbstractionUtils {
  def collectPredValues(args: Seq[Expr]): Seq[PredicateValue] = {
    args.collect {
      case x: PredicateAbstraction => toPredValue(x)
    }
  }

  def toPredValue(e: PredicateAbstraction): PredicateValue = {
    e match {
      case x: PurePredicateAbstraction => PPredicateValue(x)
      case x: SpatialPredicateAbstraction => SPredicateValue(x)
    }
  }

  def withoutPredAbstractions(args: Seq[Expr]): Seq[Expr] = {
    args.filter {
      case _: PurePredicateAbstraction => false
      case _: SpatialPredicateAbstraction => false
      case _ => true
    }
  }

  def withoutPredAbstractions(params: Formals, args: Seq[Expr]): Seq[Expr] = {
    (params.toSeq, args).zipped.filter((param, _) =>
        param match {
          case (_, PredType) => false
          case _ => true
        }
      )._2
  }
}

