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

    val predVals = (PredicateAbstractionUtils.collectPredValues(goal.spec.pre.collect(_ => true).toSeq)
                ++ PredicateAbstractionUtils.collectPredValues(goal.spec.post.collect(_ => true).toSeq))

    val predMap = predMap0.map{
      case (name: Ident, p: InductivePredicate) => {
        val lambdaLiftInductive = new LambdaLiftInductive(p, freeVarMap, predVals)

        (name, lambdaLiftInductive.transform())
      }
    }

    val freshIdentGen = new FreshIdentGen("$")

    val defun = new DefunctionalizeGoalContainer(goal, freshIdentGen, predMap)

    (freshIdentGen, defun.transform())
  }
}

class FunSpecEliminateAbstractions(freshIdentGen: FreshIdentGen) {

  def transform(funSpec0: FunSpec, predMap0: PredicateEnv) : (FunSpec, List[InductivePredicate]) = {
    val lambdaLift = new LambdaLiftFunSpec(funSpec0)

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

    val defun = new DefunctionalizeFunSpec(funSpec, freshIdentGen, predMap)

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

