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
case class DefunctionalizeInductive(newName: Ident, gen: FreshIdentGen, pred: InductivePredicate, fs: Seq[PredicateValue], spList: SpecializationList, predEnv: PredicateEnv)
  extends TransformAssertionsH[InductivePredicate] {

  import PredicateAbstractionUtils._

  private val elimAbs = new AppEliminateAbstractions(gen, spList)

  private val funMap = new PredicateValueMap(pred, fs)
  private val generatedPreds = new ListBuffer[InductivePredicate]()

  def getGeneratedPreds: List[InductivePredicate] =
    generatedPreds.toList

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

    val clauses = clauses0.map(cl => cl.visitAssertions(e => transformExpr(e), h => transformHeaplet(h)))
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

          val app = SApp(newName, withoutPredAbstractions(pred.params, args), tag, card)
          Seq(app)
          // val (newApp, newPreds) = elimAbs.transform(app, predEnv)
          //
          // generatedPreds ++= newPreds
          //
          // Seq(newApp)

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
case class Defunctionalize[S, A <: HasAssertions[S]](fun: A, gen: FreshIdentGen, predEnv: PredicateEnv, spList: SpecializationList)
  extends TransformAssertions[S, A] {

  import PredicateAbstractionUtils._

  private val generatedPreds = new ListBuffer[InductivePredicate]()

  def getGeneratedPreds(): List[InductivePredicate] = generatedPreds.result()

  protected def setup(): A = fun

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
                throw new Exception(s"Defunctionalize: Cannot find predicate ${predIdent}")

              case Some(p) => p
            }

          val defunctionalizer = new DefunctionalizeInductive(newPredName, gen, pred, predValues, spList, predEnv)

          // TODO: Ensure there are no free variables remaining in any of the 'predValues'
          generatedPreds += defunctionalizer.transform()
          generatedPreds ++= defunctionalizer.getGeneratedPreds
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
  private var sps: ListBuffer[ExistSpecialization] = ListBuffer[ExistSpecialization]()

  def insertSpecialization(s: ExistSpecialization) {
    sps += s
  }

  def lookupSpecialization[A <: App](name: Ident, fromApp: A): Option[A] =
    ???
    // sps.collectFirst(Function.unlift(_.sp.getSubstFor[A](name, fromApp)))
}

private class ExistSpecialization(val sp: Specialization[T] forSome {type T <: App})

private class Specialization[T <: App](name: Ident, fromApp: T, toApp: T) {
  def getSubstFor[S <: App](theName: Ident, theFromApp: S)(implicit evidence: S =:= T): Option[T] =
    if (name == theName && theFromApp == fromApp) {
      Some(toApp)
    } else {
      None
    }
}

// TODO: Calculate newName from origName and occurrence
class FreeVar(val occurrence: Int, val origName: Ident, val newName: Ident) {
}

