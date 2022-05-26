package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Expressions.PredicateAbstraction
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._

// Perform both lambda lifting and defunctionalization

class GoalContainerEliminateAbstractions {
  def transform(goal0: GoalContainer, predMap0: PredicateEnv): (FreshIdentGen, (GoalContainer, List[InductivePredicate])) = {
    val lambdaLiftGC = new LambdaLiftGoalContainer(goal0)

    val (goal, freeVarMap) = lambdaLiftGC.transform()

    val freshIdentGen = new FreshIdentGen("$")

    val funSpecElimAbs = new FunSpecEliminateAbstractions(freshIdentGen, new SpecializationList())
    val (newFunSpec, newPreds) = funSpecElimAbs.transform(goal.spec, predMap0)

    (freshIdentGen, (goal.copy(spec = newFunSpec), newPreds))
  }
}

class FunSpecEliminateAbstractions(freshIdentGen: FreshIdentGen, spList: SpecializationList) {

  def transform(funSpec0: FunSpec, predMap0: PredicateEnv) : (FunSpec, List[InductivePredicate]) = {
    val lambdaLift = new LambdaLiftHasAssns(funSpec0)

    val funSpec = lambdaLift.transform()
    val freeVarMap = lambdaLift.freeVarMap

    val predVals = (PredicateAbstractionUtils.collectPredValues(funSpec.pre.collect(_ => true).toSeq)
                ++ PredicateAbstractionUtils.collectPredValues(funSpec.post.collect(_ => true).toSeq))

    val predMap = predMap0.map{
      case (name: Ident, p: InductivePredicate) => {
        val lambdaLiftInductive = new LambdaLiftInductive(p, freeVarMap, predVals)

        (name, lambdaLiftInductive.transform())
      }
    }

    val defun = new DefunctionalizeFunSpec(funSpec, freshIdentGen, predMap, spList)

    val newFunSpec = defun.transform()
    (newFunSpec, defun.getGeneratedPreds())

    // val lambdaLiftFunSpec: LambdaLiftFunSpec = new LambdaLiftFunSpec(funSpec0)

    // val funSpec = lambdaLiftFunSpec.transform()

    // // TODO: Finish implementing
    // // val defun = new DefunctionalizeFunSpec

    // // (funSpec, lambdaLiftFunSpec.freeVarMap)
    // funSpec
  }
}

class HasAssnsEliminateAbstractions[A <: HasAssertions[A] with HasExpressions[A]]
  (freshIdentGen: FreshIdentGen, spList: SpecializationList) {

  def transform(x: A, predMap0: PredicateEnv): (A, List[InductivePredicate]) = {
    val lambdaLift = new LambdaLiftHasAssns(x)

    val newX = lambdaLift.transform()
    val freeVarMap = lambdaLift.freeVarMap

    val predVals = PredicateAbstractionUtils.collectPredValues(x.collect(_ => true).toSeq)
    ???
  }
}

