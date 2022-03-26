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
  protected val additionalParams: Formals

  // Include the "closure arguments"
  protected def updateArgs(args: Seq[Expr]): Seq[Expr] = {
     args ++ additionalParams.map(_._1)
  }
}

// The side of lambda lifting that handles inductive predicate definitions.
// In particular, update the parameters to include the "closure arguments."
// Do this for recursive calls and for applications of predicate abstraction
// arguments.
class LambdaLiftInductive(pred: InductivePredicate, fs: Seq[PredicateValue])
  extends LambdaLift[InductivePredicate] {

  private val funMap = new PredicateValueMap(pred, fs)

  private val gen = new FreshIdentGen("%")

  private val freeVarNames: Set[Ident] = fs.flatMap(_.fvNames).toSet

  private val freeVars = freeVarNames.zip(0 to freeVarNames.size-1).map {
      case (n, i) => new FreeVar(i, n, gen.genFresh(n))
  }

  protected val additionalParams = freeVars.map((x: FreeVar) => (new Var(x.newName), AnyType)).toList

  protected def setup(): InductivePredicate = {
    InductivePredicate(pred.name, pred.params ++ additionalParams, pred.clauses)
  }

  protected def transformExpr(e: Expr): SortedSet[Expr] = {
    SortedSet[Expr](e match {
        case PApp(predIdent, args) => {
          funMap get predIdent match {
            case Some(SPredicateValue(_)) =>
              // This is an application of a "lambda" parameter
              PApp(predIdent, updateArgs(args.toSeq).toList)

            case None =>
              throw new Exception(s"Invalid pure predicate application: ${e}")

            case Some(PPredicateValue(_)) =>
              throw new Exception("Pure predicate used as a spatial predicate: " + predIdent)
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
}

class LambdaLiftFunSpec(fun: FunSpec, theAdditionalParams: Formals) extends LambdaLift[FunSpec] {
  import PredicateAbstractionUtils._

  protected val additionalParams = theAdditionalParams

  protected def setup(): FunSpec = fun

  protected def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](heaplet match {
      case SApp(predIdent, args, tag, card) => {
        val predValues = collectPredValues(args)

        if (predValues.isEmpty) {
          heaplet
        } else {
          heaplet
        }
      }

      case _ => heaplet
    })
  }

  protected def transformExpr(e: Expr): SortedSet[Expr] = SortedSet[Expr](e)
}

class FreeVar(val occurrence: Int, val origName: Ident, val newName: Ident) {
}

