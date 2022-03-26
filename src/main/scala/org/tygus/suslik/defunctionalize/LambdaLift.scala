package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.AnyType
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._

import scala.collection.immutable.SortedSet

abstract class LambdaLift[A <: HasAssertions[A]] extends TransformAssertions[A] {
  // protected val freeVars: Seq[FreeVar]
}


// The side of lambda lifting that handles inductive predicate definitions.
// In particular, update the parameters to include the "closure arguments."
// Do this for recursive calls and for applications of predicate abstraction
// arguments.
class LambdaLiftInductive(pred: InductivePredicate, freeVarMap: Map[Var, Expr], fs: Seq[PredicateValue])
  extends LambdaLift[InductivePredicate] {

  private val funMap = new PredicateValueMap(pred, fs)

  private val gen = new FreshIdentGen("%")

  private val additionalParams: Formals = freeVarMap.toList.map{ case (origVar, Var(newVar)) => (new Var(newVar), AnyType) }

  protected def setup(): InductivePredicate = {
    InductivePredicate(pred.name, pred.params ++ additionalParams, pred.clauses)
  }

  protected def transformExpr(e: Expr): SortedSet[Expr] = {
    SortedSet[Expr](e match {
        case PApp(predIdent, args) => {
          funMap get predIdent match {
            case Some(PPredicateValue(_)) =>
              // This is an application of a "lambda" parameter
              PApp(predIdent, updateArgs(args.toSeq).toList)

            case None =>
              throw new Exception(s"Invalid pure predicate application: ${e}")

            case Some(SPredicateValue(_)) =>
              throw new Exception("Spatial predicate used as a pure predicate: " + predIdent)
          }
        }

        case _ => e
      }
    )
  }

  protected def transformHeaplet(h: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](h match {
        case SApp(predIdent, args, tag, card) => {
          if (predIdent == pred.name) {
            // Recursive call

            SApp(predIdent, updateArgs(args), tag, card)
          } else {
            funMap get predIdent match {
              case Some(sp @ SPredicateValue(_)) =>
                // This is an application of a "lambda" parameter
                SApp(predIdent, updateArgs(args), tag, card)

              case Some(PPredicateValue(_)) =>
                throw new Exception("Pure predicate used as a spatial predicate: " + predIdent)

              case None => h
            }
          }
        }

        case _ => h
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
    val lambdaLiftFunSpec = new LambdaLiftFunSpec(goal.spec)

    val newSpec = lambdaLiftFunSpec.transform()

    (new GoalContainer(newSpec, goal.body), lambdaLiftFunSpec.freeVarMap)
  }
}

class LambdaLiftFunSpec(fun: FunSpec) extends LambdaLift[FunSpec] {
  import PredicateAbstractionUtils._

  private val collectFVs = new CollectFreeVars[FunSpec]()
  val freeVarMap: Map[Var, Expr] = collectFVs.getFreeVarMap(fun)

  protected def setup(): FunSpec = fun

  protected def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](heaplet match {
      case SApp(predIdent, args, tag, card) => {
        val predValues = collectPredValues(args)

        if (predValues.isEmpty) {
          heaplet
        } else {
          // SApp(predIdent, updateCallArgs(args.map(updatePredicateArg)), tag, card)
          SApp(predIdent, updateCallArgs(args), tag, card)
        }
      }

      case _ => heaplet
    })
  }

  protected def transformExpr(e: Expr): SortedSet[Expr] = SortedSet[Expr](e)

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

  private class CollectFreeVars[A <: HasAssertions[A]] {
    private val freeVarSet: scala.collection.mutable.Set[Var] = scala.collection.mutable.Set[Var]()

    private val gen = new FreshIdentGen("%")

    // private val freeVarNames: Set[Ident] = Set[Ident]()

    // private val freeVars: Seq[FreeVar] = Seq[FreeVar]()

    def getFreeVarMap(x: A): Map[Var, Expr] = {
      freeVarSet.map((origV: Var) => {
        val newName = gen.genFresh(origV.name)
        (origV, Var(newName))
      }).toMap
    }

    def visit(asn: Assertion): Assertion = {
      freeVarSet ++= asn.sigma.collect(_.isInstanceOf[PredicateAbstraction]).flatMap((x: PredicateAbstraction) => x.vars).toSet
      asn
    }

    // protected def setup(): A = ???
    // protected def transformExpr(e: Expr): SortedSet[Expressions.Expr] = ???
    // protected def transformHeaplet(h: Heaplet): Seq[Heaplet] = ???

    // private val freeVars: Seq[FreeVar] = freeVarNames.zip(0 to freeVarNames.size-1).map {
    //     case (n, i) => new FreeVar(i, n, gen.genFresh(n))
    // }.toSeq

    // val freeVarMap: Map[Var, Expr] = freeVars.map((x: FreeVar) => (Var(x.origName), Var(x.newName))).toMap

  }
}

// TODO: Calculate newName from origName and occurrence
class FreeVar(val occurrence: Int, val origName: Ident, val newName: Ident) {
}

