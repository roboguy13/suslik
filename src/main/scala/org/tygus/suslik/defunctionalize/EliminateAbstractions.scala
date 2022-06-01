package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._

// Perform both lambda lifting and defunctionalization

class GoalContainerEliminateAbstractions {
  def transform(goal0: GoalContainer, predMap0: PredicateEnv): (GoalContainer, List[InductivePredicate]) = {
    val lambdaLiftGC = new LambdaLiftGoalContainer(goal0)

    val (goal, freeVarMap) = lambdaLiftGC.transform()

    val funSpecElimAbs = new EliminateAbstractions[FunSpec, FunSpec, FunSpec](new SpecializationLists())
    val (newFunSpec, newPreds) = funSpecElimAbs.transform(goal.spec, predMap0)

    (goal.copy(spec = newFunSpec), newPreds)
  }
}

class EliminateAbstractions[Base <: HasExpressions[Base], S <: HasExpressions[S] with HasAssertions[S], A <: HasAssertions[S] with HasExpressions[Base]]
  (spList: SpecializationLists, originOpt: Option[PredicateApplication] = None) {

  def lambdaLift(x0: A, predMap0: PredicateEnv): (S, Map[Var, Expr]) = {
    val lambdaLift = new LambdaLiftHasAssns[S, A](x0)

    val x1 = lambdaLift.transform()
    val freeVarMap = lambdaLift.freeVarMap
    (x1, freeVarMap)
  }

  def transform(x: A, predMap: PredicateEnv): (S, List[InductivePredicate]) = {
    val (lambdaLifted, freeVarMap) = lambdaLift(x, predMap)
    transformWithoutLambdaLift(lambdaLifted, freeVarMap, predMap, None)
  }


  def transformWithoutLambdaLift(x1: S, freeVarMap: Map[Var, Expr], predMap0: PredicateEnv, newName: Option[Ident]): (S, List[InductivePredicate]) = {

    val predVals = PredicateAbstractionUtils.collectPredValues(x1.collect(_ => true).toSeq)

    val predMap = predMap0.map{
      case (name: Ident, p: InductivePredicate) => {
        val lambdaLiftInductive = new LambdaLiftInductive(p, freeVarMap, predVals)

        (name, lambdaLiftInductive.transform())
      }
    }

    val x =
      originOpt match {
        case None => x1
        case Some(origin) => {
          val absMap: Map[Var, PredicateAbstraction]
            // = origin.pred.params.filter(x => x._2 == PredType).map(_._1).zip(origin.args.map(_.abstr)).toMap
            = origin.pred.params.filter(x => x._2 == PredType).map(_._1).zip(origin.absArgs.map(_.abstr)).toMap

          val instPredParams = new InstantiatePredParams[S, S](origin.pred, x1, absMap)
          instPredParams.transform()
        }
      }

    val defun = new Defunctionalize[S, S](x, predMap, spList, newName)

    val newX = defun.transform()
    (newX, defun.getGeneratedPreds())
  }
}

// Substitute the 'pred' values for the corresponding 'pred'-type formal parameters in applications
class InstantiatePredParams[S, A <: HasAssertions[S]](origin: InductivePredicate, x: A, absMap: Map[Var, PredicateAbstraction])
    extends TransformAssertions[S, A] {
  protected def setup(): A = x

  def transformHeaplet(heaplet: Heaplet): Seq[Heaplet] =
    Seq[Heaplet](heaplet match {
      case app@SApp(predIdent, args, tag, card) =>
        new WrappedSApp(app).substMap(absMap)
      case _ => heaplet
    })

  def transformExpr(e: Expr): Expr =
    e match {
      case app@PApp(_, _) =>
        new WrappedPApp(app).substMap(absMap)
      case _ => e
    }
}

class AppEliminateAbstractions(spList: SpecializationLists, origin: PredicateApplication) {

  def lambdaLiftSApp(x: SApp, predMap: PredicateEnv): (SApp, Map[Var, Expr]) = {
    val elimAbs = new EliminateAbstractions[Heaplet, SFormula, SApp](spList, Some(origin))
    val (r, freeVarMap) = elimAbs.lambdaLift(x, predMap)
    (r.chunks.head.asInstanceOf[SApp], freeVarMap)
  }

  def transformSApp(x: SApp, freeVarMap: Map[Var, Expr], predMap: PredicateEnv, newName: Option[Ident]): (SApp, List[InductivePredicate]) = {
    val elimAbs = new EliminateAbstractions[Heaplet, SFormula, SApp](spList, Some(origin))
    // spList.lookupSpatial(origin.pred.name, x) match {
    //   case None => {
        val (r, newMap) = elimAbs.transformWithoutLambdaLift(SFormula(List(x)), freeVarMap, predMap, newName)
        (r.chunks.head.asInstanceOf[SApp], newMap)
      // }
      // case Some(r) => (r.head.asInstanceOf[SApp], List())
    // }
  }

  // def transform[A <: App](origin: Ident, app: A, predMap: PredicateEnv):
  //     (app.R, List[InductivePredicate]) = {
  //   app match {
  //     case newApp@WrappedPApp(x) =>
  //       actualTransformOption[newApp.type](origin, app, predMap)(spList.lookupPure(origin, x))
  //       // (spList.lookupPure(origin, x), List())
  //     case newApp@WrappedSApp(x) =>
  //       actualTransformOption[newApp.type](origin, app, predMap)(spList.lookupSpatial(origin, x))
  //       // (spList.lookupSpatial(origin, x), List())
  //   }
  // }

  // def lambdaLiftSApp(x: SApp, predMap: PredicateEnv): (SApp, Map[Var, Expr]) =
  //   new EliminateAbstractions[SApp, SApp, SApp](freshIdentGen, spList, None).lambdaLift(x, predMap)
  //
  // def transformPApp(app: PApp, freeVarMap: Map[Var, Expr], predMap: PredicateEnv) =
  //   actualTransformOption(new WrappedPApp(app), freeVarMap, predMap)(spList.lookupPure(origin.pred.name, app))

  // def transformSApp(app: SApp, freeVarMap: Map[Var, Expr], predMap: PredicateEnv) =
  //   actualTransformOption(new WrappedSApp(app), freeVarMap, predMap)(spList.lookupSpatial(origin.pred.name, app).map(x => new SFormula(x.toList)))
  //
  // private def actualTransformOption[A <: App](app: A, freeVarMap: Map[Var, Expr], predMap: PredicateEnv)(opt: Option[app.R]): (app.R, List[InductivePredicate]) =
  //   opt match {
  //     case Some(x) => (x, List())
  //     case None => actualTransform(app, freeVarMap, predMap)
  //   }
  //
  // private def actualTransform[A <: App](app: A, freeVarMap: Map[Var, Expr], predMap: PredicateEnv):
  //     (app.R, List[InductivePredicate]) = {
  //   val (y, newPreds) = new EliminateAbstractions[app.Base, app.R, app.T](freshIdentGen, spList, Some(origin)).transformWithoutLambdaLift(app.unwrap, freeVarMap, predMap)
  //
  //   (y, newPreds)
  // }
}

class PredicateApplication(val pred: InductivePredicate, val absArgs: Seq[PredicateValue])

