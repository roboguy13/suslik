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

    val funSpecElimAbs = new EliminateAbstractions[FunSpec](freshIdentGen, new SpecializationList())
    val (newFunSpec, newPreds) = funSpecElimAbs.transform(goal.spec, predMap0)

    (freshIdentGen, (goal.copy(spec = newFunSpec), newPreds))
  }
}

class EliminateAbstractions[A <: HasAssertions[A] with HasExpressions[A]]
  (freshIdentGen: FreshIdentGen, spList: SpecializationList) {

  def transform(x0: A, predMap0: PredicateEnv): (A, List[InductivePredicate]) = {
    val lambdaLift = new LambdaLiftHasAssns(x0)

    val x = lambdaLift.transform()
    val freeVarMap = lambdaLift.freeVarMap

    val predVals = PredicateAbstractionUtils.collectPredValues(x.collect(_ => true).toSeq)

    val predMap = predMap0.map{
      case (name: Ident, p: InductivePredicate) => {
        val lambdaLiftInductive = new LambdaLiftInductive(p, freeVarMap, predVals)

        (name, lambdaLiftInductive.transform())
      }
    }

    val defun = new Defunctionalize(x, freshIdentGen, predMap, spList)

    val newX = defun.transform()
    (newX, defun.getGeneratedPreds())
  }
}

