package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.AnyType
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._

import scala.collection.mutable.ListBuffer
import scala.collection.immutable.SortedSet

abstract class LambdaLift[S, A <: HasAssertions[S]] extends TransformAssertions[S, A] {
  // protected val freeVars: Seq[FreeVar]
}

abstract class LambdaLiftH[A <: HasAssertions[A]] extends LambdaLift[A, A] {
}


// The side of lambda lifting that handles inductive predicate definitions.
// In particular, update the parameters to include the "closure arguments."
// Do this for recursive calls and for applications of predicate abstraction
// arguments.
class LambdaLiftInductive(pred: InductivePredicate, freeVarMap: Map[Var, Expr], fs: Seq[PredicateValue])
  extends LambdaLiftH[InductivePredicate] {

  private val funMap = new PredicateValueMap(pred, fs)
  private val gen = new FreshIdentGen("%")
  private val additionalParams: Formals = freeVarMap.toList.map{ case (origVar, Var(newVar)) => (new Var(newVar), AnyType) }
  private val specList = new SpecializationLists()

  // private val predParamMap: Map[Var, PredicateAbstraction]
  //   = pred.params.filter(x => x._2 == PredType).map(_._1).zip(fs.map(_.abstr)).toMap

  // private val abstractionMap: Map[Ident, PredicateValue]

  protected def setup(): InductivePredicate = {
    InductivePredicate(pred.name, pred.params ++ additionalParams, pred.clauses)
  }

  protected def transformExpr(e: Expr): Expr = {
      if (freeVarMap.isEmpty) {
        e
      } else {
        e match {
            case PApp(predIdent, args) => {
              funMap get predIdent match {
                case Some(PPredicateValue(_)) =>
                  // This is an application of a "lambda" parameter
                  PApp(predIdent, updateArgs(args.toSeq).toList)

                case None => e

                case Some(SPredicateValue(_)) =>
                  throw new Exception("LambdaLiftInductive: Spatial predicate used as a pure predicate: " + predIdent)
              }
            }

            case BinaryExpr(op, left, right) => {
              BinaryExpr(op, transformExpr(left), transformExpr(right))
            }

            case _ => e
      }
    }
  }

  protected def transformHeaplet(h: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](
      if (freeVarMap.isEmpty) {
        h
      } else {
        h match {
          case SApp(predIdent, args, tag, card) => {
            if (predIdent == pred.name) {
              // Recursive call

              SApp(predIdent, updateArgs(args), tag, card)
            } else {
              funMap get predIdent match {
                case Some(sp @ SPredicateValue(_)) =>
                  // This is an application of a "lambda" parameter
                  SApp(predIdent, updateArgs(args), tag, card)

                case Some(p @ PPredicateValue(_)) =>
                  SApp(predIdent, updateArgs(args), tag, card)
                  // TODO: Should this give an error?
                  // throw new Exception("LambdaLiftInductive: Pure predicate used as a spatial predicate: " + predIdent + " = " + p)

                case None => h
              }
            }
          }

          case _ => h
        }
      }
    )
  }


  // Include the "closure arguments"
  private def updateArgs(args: Seq[Expr]): Seq[Expr] = {
    args ++ additionalParams.map(_._1)
  }

}

class LambdaLiftGoalContainer(goal: GoalContainer) {
  def transform(): (GoalContainer, Map[Var, Expr]) = {
    val lambdaLiftFunSpec = new LambdaLiftHasAssns[FunSpec, FunSpec](goal.spec)

    val newSpec = lambdaLiftFunSpec.transform()

    (new GoalContainer(newSpec, goal.body), lambdaLiftFunSpec.freeVarMap)
  }
}

class LambdaLiftHasAssns[S, A <: HasAssertions[S]](fun: A) extends LambdaLift[S, A] {
  import PredicateAbstractionUtils._

  private val collectFVs = new CollectFreeVars[S, A]()
  val freeVarMap: Map[Var, Expr] = collectFVs.getFreeVarMap(fun)

  protected def setup(): A = fun

  protected def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](heaplet match {
      case SApp(predIdent, args, tag, card) => {
        val predValues = collectPredValues(args)

        if (predValues.isEmpty) {
          heaplet
        } else {
          SApp(predIdent, updateCallArgs(args.map(updatePredicateArg)), tag, card)
        }
      }

      case _ => heaplet
    })
  }

  // TODO: Is this correct?
  protected def transformExpr(e: Expr): Expr = e

  // Update the body of the predicate abstracts to refer to the closure argument
  // names rather than the original names of the variables being closed over
  private def updatePredicateArg(e: Expr): Expr = {
    e match {
      case pa: PredicateAbstraction =>
        pa.subst(freeVarMap)

      case _ => e
    }
  }

  // Include the "closure arguments"
  private def updateCallArgs(args: Seq[Expr]): Seq[Expr] = {
    args ++ freeVarMap.toSeq.map((x : (Var, Expr)) => x match { case (oldVar, newVar) => oldVar })
  }

  private class CollectFreeVars[S, A <: HasAssertions[S]] {
    private val freeVarSet: scala.collection.mutable.Set[Var] = scala.collection.mutable.Set[Var]()

    private val gen = new FreshIdentGen("%")

    def getFreeVarMap(x: A): Map[Var, Expr] = {
      freeVarSet.clear()

      x.visitAssertions(visitE, visitH)

      freeVarSet.map((origV: Var) => {
        val newName = gen.genFresh(origV.name)
        (origV, Var(newName))
      }).toMap
    }

    private def visitH(h: Heaplet): Seq[Heaplet] = {
      freeVarSet ++= collectFreeVars(h)
      Seq[Heaplet](h)
    }

    private def visitE(e: Expr): Expr = {
      freeVarSet ++= collectFreeVars(e)
      e
    }

    private def collectFreeVars[T <: HasExpressions[T]](x: T): scala.collection.immutable.Set[Var] =
      x.collect(_.isInstanceOf[PredicateAbstraction]).flatMap((x: PredicateAbstraction) => x.vars).toSet
  }
}

