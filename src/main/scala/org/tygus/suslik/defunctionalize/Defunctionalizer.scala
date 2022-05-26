package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._
import org.tygus.suslik.LanguageUtils.cardinalityPrefix

import org.tygus.suslik.defunctionalize._

import scala.collection.mutable.ListBuffer
import scala.collection.immutable.SortedSet


  // TODO: Consider avoiding constructing this twice (once in
  // DefunctionalizeInductive and once in LambdaLiftInductive). On the other hand, this is
  // very unlikely to be a significant source of inefficiency.
class PredicateValueMap(pred: InductivePredicate, fs: Seq[PredicateValue]) {
  private val funMap : Map[String, PredicateValue] = pred.params.filter(
    {
      case (_, PredType) => true
      case _ => false
    }).map(_._1).zip(fs).map({
      case (Var(n), f) => (n, f)
    }).toMap


   def get(key: String): Option[PredicateValue] = funMap.get(key)
   def iterator: Iterator[(String, PredicateValue)] = funMap.iterator
}

  // NOTE:
  //   - In the list of functions: Ensure that no free variables exist in the
  //   result of applications of the function, other than what is passed in as an
  //   argument.
  //   This requirement is to avoid variable capture.
  //
  //   - 'newName' should be a fresh name w.r.t. the names of the other
  //   inductive predicates
case class DefunctionalizeInductive(newName: Ident, gen: FreshIdentGen, pred: InductivePredicate, fs: Seq[PredicateValue], spList: SpecializationList)
  extends TransformAssertions[InductivePredicate] {

  import PredicateAbstractionUtils._

  val funSpecElimAbs = new FunSpecEliminateAbstractions(gen, spList)

  val funMap = new PredicateValueMap(pred, fs)

  def setup(): InductivePredicate = {
    val newParams = pred.params.filter(
      {
        case (_, PredType) => false
        case _ => true
      })
    InductivePredicate(newName, newParams, pred.clauses)
  }

  override protected def finish(x: InductivePredicate): InductivePredicate = {
    val InductivePredicate(name, params, clauses0) = x

    val cards: Set[Var] = clauses0.flatMap(_.asn.vars).filter(_.name.startsWith(cardinalityPrefix)).toSet

    val clauses = clauses0.map(cl => cl.visitAssertions(e => transformExpr(e), h => transformHeaplet(h)))

    // val clauses = clauses0.map (cl => {
    //         cl.visitAssertions(a => {
    //             val cardMap: Map[Var, Expr] = cards.map(card => card -> Var(gen.withCurrentUniq(card.name))).toMap
    //             Assertion(a.phi.subst(cardMap), a.sigma.subst(cardMap))
    //             // cards.map(card => {
    //             //   val newCard = Var(gen.withCurrentUniq(card.name))
    //             //   Assertion(a.phi.subst(card, newCard), a.sigma.subst(card, newCard))
    //             // })
    //           })
    //       }
    //     )

    InductivePredicate(name, params, clauses)
  }

  // Spatial part
  protected def transformHeaplet(chunk: Heaplet): Seq[Heaplet] = {
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
              throw new Exception("Pure predicate used as a spatial predicate: " + predIdent)
          }
        }

      case _ => Seq(chunk)
    }
  }


  // Pure part
  protected def transformExpr(e: Expr): Expr = {
    e match {
      case PApp(predIdent, args) =>
        funMap get predIdent match {
          case None =>
            PApp(predIdent, args.map(e => transformExpr(e)))
            // throw new Exception(s"Invalid pure predicate application: ${e}")
          case Some(SPredicateValue(_)) =>
            throw new Exception(s"Spatial predicate used as a pure predicate: ${predIdent}")
          case Some(p @ PPredicateValue(_)) => p.apply(args)
        }
      case BinaryExpr(op, left, right) => BinaryExpr(op, transformExpr(left), transformExpr(right))
      case UnaryExpr(op, arg) => UnaryExpr(op, transformExpr(arg))
      case _ => e
    }
  }
}

// Defunctionalization on the side of the predicate abstractions

// case class DefunctionalizeGoalContainer(goal: GoalContainer, gen: FreshIdentGen, predEnv: PredicateEnv) {
//   def transform(): (GoalContainer, List[InductivePredicate]) = {
//
//     val defun = new DefunctionalizeFunSpec(goal.spec, gen, predEnv, spList)
//
//     val newSpec = defun.transform()
//
//     (GoalContainer(newSpec, goal.body), defun.getGeneratedPreds)
//   }
//
// }
//
case class DefunctionalizeFunSpec(fun: FunSpec, gen: FreshIdentGen, predEnv: PredicateEnv, spList: SpecializationList)
  extends TransformAssertions[FunSpec] {

  import PredicateAbstractionUtils._

  private val generatedPreds = new ListBuffer[InductivePredicate]()

  def getGeneratedPreds(): List[InductivePredicate] = generatedPreds.result()

  protected def setup(): FunSpec = fun

  protected def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
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

          val defunctionalizer = new DefunctionalizeInductive(newPredName, gen, pred, predValues, spList)

          // TODO: Ensure there are no free variables remaining in any of the 'predValues'
          generatedPreds += defunctionalizer.transform()
          SApp(newPredName, newArgs, tag, card)
        }
      }

      case _ => heaplet
    })
  }

  protected def transformExpr(e: Expr): Expr = e
}

// | This keeps track of the specializations we've already done
class SpecializationList() {
  private var sps: ListBuffer[Specialization] = ListBuffer[Specialization]()

  def insertSpecialization(s: Specialization) {
    sps += s
  }

  def lookupSpecialization(name: Ident, fromExpr: Expr): Option[Expr] =
    sps.collectFirst(Function.unlift(_.getSubstFor(name, fromExpr)))
}

private class Specialization(name: Ident, fromExpr: Expr, toExpr: Expr) {
  def getSubstFor(theName: Ident, theFromExpr: Expr): Option[Expr] =
    if (name == theName && theFromExpr == fromExpr) {
      Some(toExpr)
    } else {
      None
    }
}

// TODO: Calculate newName from origName and occurrence
class FreeVar(val occurrence: Int, val origName: Ident, val newName: Ident) {
}

