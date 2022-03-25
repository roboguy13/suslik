package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._

import scala.collection.mutable.Stack
import scala.collection.mutable.ListBuffer
import scala.collection.immutable.SortedSet

  // This abstracts over the traversal pattern used by both the part of
  // defunctionalization that traverses the inductive predicate as well
  // as the part that traverses expressions which use the inductive predicate and
  // might contain abstractions.
abstract class Defunctionalizer[A <: HasAssertions[A]] {

  def defunctionalize(): A = {
    setup().visitAssertions(asn => defunctionalizeAssertion(asn))
  }

  protected def setup(): A

  protected def defunctionalizeExpr(e: Expr): SortedSet[Expr]
  protected def defunctionalizeHeaplet(h: Heaplet): Seq[Heaplet]

  private def defunctionalizeAssertion(asn: Assertion): Assertion = {
    Assertion(defunctionalizePFormula(asn.phi), defunctionalizeSFormula(asn.sigma))
  }

  private def defunctionalizePFormula(phi: PFormula): PFormula = {
    PFormula(phi.conjuncts.flatMap((e : Expr) => defunctionalizeExpr(e)))
  }

  private def defunctionalizeSFormula(sigma: SFormula): SFormula = {
    SFormula(sigma.chunks.flatMap((chunk: Heaplet) => defunctionalizeHeaplet(chunk)))
  }
}

  // NOTE:
  //   - In the list of functions: Ensure that no free variables exist in the
  //   result of applications of the function, other than what is passed in as an
  //   argument.
  //   This requirement is to avoid variable capture.
  //
  //   - 'newName' should be a fresh name w.r.t. the names of the other
  //   inductive predicates
class DefunctionalizeInductive (newName: Ident, pred: InductivePredicate, fs: Seq[PredicateValue])
  extends Defunctionalizer[InductivePredicate] {

  val funMap : Map[String, PredicateValue] = pred.params.filter(
    {
      case (_, PredType) => true
      case _ => false
    }).map(_._1).zip(fs).map({
      case (Var(n), f) => (n, f)
    }).toMap

  def setup(): InductivePredicate = {
    val newParams = pred.params.filter(
      {
        case (_, PredType) => false
        case _ => true
      })
    InductivePredicate(newName, newParams, pred.clauses)
  }

  // Spatial part
  protected def defunctionalizeHeaplet(chunk: Heaplet): Seq[Heaplet] = {
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
  protected def defunctionalizeExpr(e: Expr): SortedSet[Expr] = {
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
  protected def assertNoFreeVars() = {
    val freeVars = abstr.vars.diff(abstr.args.map(Var(_)).toSet)

    if (!freeVars.isEmpty) {
      throw new Exception("Free variables in predicate abstraction (closures not yet supported)")
    }
  }
}

case class SPredicateValue(abstr: SpatialPredicateAbstraction) extends PredicateValue(abstr) {
  def apply(args: Seq[Expr]): List[Heaplet] = {
    val st = (abstr.args, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    assertNoFreeVars()

    abstr.body.subst(st.toMap).chunks
  }
}

case class PPredicateValue(abstr: PurePredicateAbstraction) extends PredicateValue(abstr) {
  def apply(args: Seq[Expr]): SortedSet[Expr] = {
    val st = (abstr.args, args).zipped map((x: Ident, y: Expr) => (Var(x) , y))

    assertNoFreeVars()

    abstr.body.subst(st.toMap).conjuncts.iterator.to[SortedSet]
  }
}
// Defunctionalization on the side of the predicate abstractions
class DefunctionalizeGoalContainer(goal: GoalContainer, gen: FreshIdentGen, predEnv: PredicateEnv) {
  def defunctionalize(): (GoalContainer, List[InductivePredicate]) = {

    val defun = new DefunctionalizeFunSpec(goal.spec, gen, predEnv)

    val newSpec = defun.defunctionalize()

    (GoalContainer(newSpec, goal.body), defun.getGeneratedPreds)
  }

}

class DefunctionalizeFunSpec(fun: FunSpec, gen: FreshIdentGen, predEnv: PredicateEnv)
  extends Defunctionalizer[FunSpec] {
  private val generatedPreds = new ListBuffer[InductivePredicate]()

  def getGeneratedPreds(): List[InductivePredicate] = generatedPreds.result()

  protected def setup(): FunSpec = fun

  protected def defunctionalizeHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](heaplet match {
      case SApp(predIdent, args, tag, card) => {
        val predValues = collectPredValues(args)

        if (predValues.isEmpty) {
          heaplet
        } else {
          val newArgs = withoutPredAbstractions(args)

          val newPredName = gen.genFresh(predIdent)

          val pred = predEnv.get(predIdent) match {
              case None => // TODO: Improve error message
                throw new Exception(s"Cannot find predicate ${predIdent}")

              case Some(p) => p
            }

          val defunctionalizer = new DefunctionalizeInductive(newPredName, pred, predValues)

          // TODO: Ensure there are no free variables remaining in any of the 'predValues'
          generatedPreds += defunctionalizer.defunctionalize()
          SApp(newPredName, newArgs, tag, card)
        }
      }

      case _ => heaplet
    })
  }

  protected def defunctionalizeExpr(e: Expr): SortedSet[Expr] = SortedSet[Expr](e)

  private def collectPredValues(args: Seq[Expr]): Seq[PredicateValue] = {
    args.collect {
      case x: PurePredicateAbstraction => PPredicateValue(x)
      case x: SpatialPredicateAbstraction => SPredicateValue(x)
    }
  }

  private def withoutPredAbstractions(args: Seq[Expr]): Seq[Expr] = {
    args.filter {
      case _: PurePredicateAbstraction => false
      case _: SpatialPredicateAbstraction => false
      case _ => true
    }
  }
}


class FreshIdentGen() {
  val existingIdents: ListBuffer[Ident] = ListBuffer[Ident]()

  def genFresh(baseIdent: Ident): Ident = genFreshWith(baseIdent, 0)

  def genFreshWith(baseIdent: Ident, n: Int): Ident = {
    val newName = baseIdent + "$" + n.toString

    if (existingIdents.contains(newName)) {
      genFreshWith(baseIdent, n + 1)
    } else {
      existingIdents += newName
      newName
    }
  }
}

