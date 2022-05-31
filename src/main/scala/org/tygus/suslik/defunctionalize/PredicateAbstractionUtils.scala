package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.InductivePredicate
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
          case (_, AnyType) => true
          case (_, PredType) => false
          case _ => true
        }
      )._2
  }

  def getPredBaseName(p: InductivePredicate): Ident =
    stripDollarSuffix(p.name)

  def stripDollarSuffix(n: Ident): Ident =
    n.takeWhile(c => c != '$')

  // // Extend a PredicateEnv with a defunctionalized version of a predicate that
  // // is already in it based on the fresh name given (which consists of the
  // // original name, mangled with a unique ID)
  // def extendPredEnv(predEnv: PredicateEnv, n: Ident): PredicateEnv = {
  //   val origN = stripDollarSuffix(n)
  //   predEnv.get(origN) match {
  //     case None => throw new Exception(s"extendPredEnv: Name ${origN} does not exist in predEnv")
  //     case Some(p) =>
  //       predEnv + (n -> p.copy(name = n))
  //   }
  // }
  //   
}

