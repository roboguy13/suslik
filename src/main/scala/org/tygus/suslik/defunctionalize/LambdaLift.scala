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

// The side of lambda lifting that handles inductive predicate definitions.
// In particular, update the parameters to include the "closure arguments."
// Do this for recursive calls and for applications of predicate abstraction
// arguments.
class LambdaLiftInductive(pred: InductivePredicate, fs: Seq[PredicateValue])
  extends TransformAssertions[InductivePredicate] {

  private val funMap = new PredicateValueMap(pred, fs)

  private val gen = new FreshIdentGen("%")

  private val freeVarNames: Set[Ident] = fs.flatMap(_.fvNames).toSet

  private val freeVars = freeVarNames.zip(0 to freeVarNames.size-1).map {
      case (n, i) => new FreeVar(i, n, gen.genFresh(n))
  }

  val additionalParams: Formals = freeVars.map((x: FreeVar) => (new Var(x.newName), AnyType)).toList

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

class LambdaLiftFunSpec(fun: FunSpec, additionalParams: Formals) extends TransformAssertions[FunSpec] {
  protected def setup(): FunSpec = fun

  protected def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet]() // TODO: Implement
  }

  protected def transformExpr(e: Expr): SortedSet[Expr] = SortedSet[Expr](e)
}

class FreeVar(val occurrence: Int, val origName: Ident, val newName: Ident) {
}

