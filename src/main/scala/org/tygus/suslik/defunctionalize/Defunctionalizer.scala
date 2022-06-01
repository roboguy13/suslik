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
case class DefunctionalizeInductive(newName: Ident, pred: InductivePredicate, fs: Seq[PredicateValue], spList: SpecializationLists, predEnv: PredicateEnv)
  extends TransformAssertionsH[InductivePredicate] {

  import PredicateAbstractionUtils._


  private val funMap = new PredicateValueMap(pred, fs)
  private val generatedPreds = new ListBuffer[InductivePredicate]()

  private val predParamMap: Map[Var, PredicateAbstraction]
    = pred.params.filter(_._2 == PredType).map(_._1).zip(fs.map(_.abstr)).toMap

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

  private def substPredParamsIn(e: Expr): Expr =
    e.subst(predParamMap)

  // Spatial part
  protected def transformHeaplet(chunk: Heaplet): Seq[Heaplet] = {
    chunk match {
      case app@SApp(predIdent, args, tag, card) =>
        if (PredFreshNameGen.eqModUniq(predIdent, pred.name)) {
          // Recursive call

          // NOTE: We do not currently support changing predicate abstractions
          // in recursive calls

          val newApp = SApp(newName, withoutPredAbstractions(pred.params, args), tag, card)
          Seq(newApp)
          // val (newApp, newPreds) = elimAbs.transform(app, predEnv)
          //
          // generatedPreds ++= newPreds
          //
          // Seq(newApp)

        } else {
          funMap get predIdent match {
            case None => //Seq(chunk)
              val predBaseName = getPredBaseName(pred)

              spList.lookupSpatial(predBaseName, app) match {
                case Some(r) => r
                case None =>
                  val elimAbs = new AppEliminateAbstractions(spList, new PredicateApplication(pred.copy(name = predBaseName), fs))
                  val (lambdaLifted0, freeVarMap) = elimAbs.lambdaLiftSApp(app, predEnv)
                  val lambdaLifted =
                    SApp(lambdaLifted0.pred
                        ,lambdaLifted0.args.map(substPredParamsIn(_))
                        ,lambdaLifted0.tag
                        ,lambdaLifted0.card
                        )

                  // if (lambdaLifted.args.exists{ case SpatialPredicateAbstraction(_, _) | PurePredicateAbstraction(_, _) => true ; case _ => false }) {

                    // val lambdaLifted: SApp = lambdaLifted0.chunks.head.asInstanceOf[SApp]

                    spList.insertSpatial(predBaseName, app, Seq[Heaplet](new SApp(getNewName(predIdent).name, lambdaLifted.args, tag, card)))

                    println(s"+++ ${predBaseName}: inserting ${(predBaseName, app, Seq[Heaplet](new SApp(getNewName(predIdent).name, lambdaLifted.args, tag, card)))}")
                    println(s"*** ${predBaseName}: transforming ${lambdaLifted}")
                    println("")
                    val (xs, newPreds) = elimAbs.transformSApp(lambdaLifted, freeVarMap, predEnv)
                    println(s"*** newPreds = ${newPreds}")
                    generatedPreds ++= newPreds
                    println(s"====> xs = ${xs}")

                    Seq(xs.copy(args = withoutPredAbstractions(xs.args.map(substPredParamsIn(_)))))

                    // substPredParamsIn(xs) match {
                    //   case SApp(xsName, xsArgs, _, _) =>
                    //     Seq(SApp(xsName, withoutPredAbstractions(xsArgs), tag, card))
                    // }
                    // Seq(xs)
                  // } else {
                  //   Seq(chunk)
                  // }
              }
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

  private def getNewName(n: Ident): Var = PredFreshNameGen.withCurrentUniq(n)

  // private def getNewAppArgs(app: App): Seq[Expr] = withoutPredAbstractions(app.args)
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
case class Defunctionalize[S, A <: HasAssertions[S]](fun: A, predEnv: PredicateEnv, spList: SpecializationLists)
  extends TransformAssertions[S, A] {

  import PredicateAbstractionUtils._

  private val generatedPreds = new ListBuffer[InductivePredicate]()

  def getGeneratedPreds(): List[InductivePredicate] =
    {
      println(s"generated: ${generatedPreds.result()}")
      generatedPreds.result()
    }

  protected def setup(): A = fun

  protected def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] = {
    Seq[Heaplet](heaplet match {
      case SApp(predIdent, args, tag, card) => {
        val predValues = collectPredValues(args)

        if (predValues.isEmpty) {
          heaplet
        } else {
          val newArgs = withoutPredAbstractions(args)

          val newPredName = PredFreshNameGen.genFresh(predIdent)

          val pred = predEnv.get(PredFreshNameGen.removeUniq(predIdent)) match {
              case None => // TODO: Improve error message
                throw new Exception(s"Defunctionalize: Cannot find predicate ${predIdent}")

              case Some(p) => p.copy(args = withoutPredAbstractions(p.args))
            }

          val defunctionalizer = new DefunctionalizeInductive(newPredName.name, pred, predValues, spList, predEnv)

          // TODO: Ensure there are no free variables remaining in any of the 'predValues'
          generatedPreds += defunctionalizer.transform()
          generatedPreds ++= defunctionalizer.getGeneratedPreds
          SApp(newPredName.name, newArgs, tag, card)
        }
      }

      case _ => heaplet
    })
  }

  // TODO: Finish this
  protected def transformExpr(e: Expr): Expr = e
}

// | This keeps track of the specializations we've already done
class SpecializationLists() {
  private val spatialSps : SpecializationList[SApp, Seq[Heaplet]] = new SpecializationList()
  private val pureSps    : SpecializationList[PApp, Expr] = new SpecializationList()

  def insertSpatial(name: Ident, fromApp: SApp, toApp: Seq[Heaplet]) =
    spatialSps.insertSpecialization(new Specialization(name, fromApp, toApp))

  def insertPure(name: Ident, fromApp: PApp, toApp: Expr) =
    pureSps.insertSpecialization(new Specialization(name, fromApp, toApp))

  def lookupSpatial(name: Ident, fromApp: SApp): Option[Seq[Heaplet]] = {
    println(s"&&& Looking up ${(name, fromApp)}")
    println(s"  ^--> length = ${spatialSps.length}")
    val r = spatialSps.lookupSpecialization(name, fromApp)
    r match {
      case None => println("  ^--> not found")
      case Some(_) => println("  ^--> found")
    }
    r
  }

  def lookupPure(name: Ident, fromApp: PApp): Option[Expr] =
    pureSps.lookupSpecialization(name, fromApp)

  // def lookup(name: Ident, fromApp: App) =
  //   fromApp match {
  //     case WrappedPApp(x) => {
  //       // implicit val evidence: fromApp.R =:= Expr = ???
  //       lookupPure(name, x)
  //     }
  //     case WrappedSApp(x) => lookupSpatial(name, x)
  //   }

  private class SpecializationList[Src, Tgt]() {
    private val sps: ListBuffer[Specialization[Src, Tgt]] = ListBuffer[Specialization[Src, Tgt]]()

    def length: Int = sps.length

    def insertSpecialization(s: Specialization[Src, Tgt]) =
      sps += s

    def lookupSpecialization(name: Ident, fromApp: Src): Option[Tgt] =
      sps.collectFirst(Function.unlift(_.getSubstFor(name, fromApp)))
  }

  class Specialization[Src, Tgt](name: Ident, fromApp: Src, toApp: Tgt) {
    def getSubstFor(theName: Ident, theFromApp: Src): Option[Tgt] = {
      println(s"====== comparing ${name} with ${theName}")
      println(s"====== comparing ${theFromApp} with ${fromApp}")
      if (PredFreshNameGen.eqModUniq(name, theName) && theFromApp == fromApp) {
        Some(toApp)
      } else {
        None
      }
    }
  }
}


// TODO: Calculate newName from origName and occurrence
class FreeVar(val occurrence: Int, val origName: Ident, val newName: Ident) {
}

