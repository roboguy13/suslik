package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions.{Expr, Unknown, Var}
import org.tygus.suslik.language.Statements.Guarded
import org.tygus.suslik.language.{Expressions, IntType}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.FailRules.CheckPost
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Rules for branch abduction
  *
  * @author Nadia Polikarpova
  */

object BranchRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-branch"

  /**
    * Generates speculative conditionals, using an unknown predicate as the condition.
    * If then-branch generates a guarded statement, its guard replaces the unknown;
    * otherwise the unknown is instantiated to `true`.
    * The else branch is generated under the negation of the unknown,
    * and hence is vacuous unless the then-branch is guarded.
    */
  object Branch extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: String = "Branch"

    // Unknown predicate over all program variables of goal
    def unknownCond(goal: Goal): Unknown = Unknown("C", goal.programVars.toSet)

    // Among all unknowns in phi, find one with the smallest parameter set
    // that still includes all mustHaveVars
    def minimalUnknown(phi: PFormula, mustHaveVars: Set[Var]): Unknown =
      phi.unknowns.filter(u => mustHaveVars.subsetOf(u.params)).minBy(_.params.size)

    // Is goal the earliest branching point for guard cond?
    // Yes if there is no smaller unknown in goal that has all variables of cond
    def isBranchingPoint(goal: Goal, cond: Expr): Boolean =
      unknownCond(goal).sameVar(minimalUnknown(goal.pre.phi, cond.vars))

    // Once the guard of the then-branch has been determined,
    // substitute the unknown in the else-branch
    val elseGoalUpdater: GoalUpdater = sols => g => {
      assert(sols.size == 1) // single older sibling: then branch
      val knownCond = sols.head._1 match {
        case Guarded(cond, _) if isBranchingPoint(g, cond) => cond // then branch is guarded and branching point is here
        case _ => Expressions.eTrue // otherwise, treat as unguarded
      }
      g.copy(pre = g.pre.copy(phi = g.pre.phi.substUnknown(unknownCond(g), knownCond)))
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      if (!goal.env.config.branchAbduction) return List()
      val pre = goal.pre
      val unknown = unknownCond(goal)
      // If this goal already contains an unknown with the same program vars, the rule does not apply
      if (pre.phi.unknowns.exists(_.sameVar(unknown))) return List()
      // Otherwise: create two branches, adding unknown and its negation to precondition
      val thenGoal = goal.spawnChild(pre = Assertion(pre.phi && unknown, pre.sigma), childId = Some(0))
      val elseGoal = goal.spawnChild(pre = Assertion(pre.phi && unknown.not, pre.sigma), childId = Some(1))
      List(RuleResult(List(thenGoal, elseGoal), GuardedBranchProducer(thenGoal, unknown), this, goal).copy(updates =
        List(RuleResult.noUpdate, elseGoalUpdater)))
    }
  }

  /**
    * If post is invalid, finds a weakest predicate over program variables that makes it valid.
    * If abduction succeeds (i.e. minimal predicate is not `false`), generates the rest of the program and wraps it in a guarded statement.
    * If abduction fails (minimal predicate is `false`), acts as the failure rule CheckPost.
    */
  object AbduceBranch extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: String = "AbduceBranch"

    // def atomCandidates(goal: Goal): Seq[Expr] = //ZYTODO: add value?
    //   for {
    //     lhs <- goal.programVars.filter(goal.post.phi.vars.contains)
    //     rhs <- goal.programVars.filter(goal.post.phi.vars.contains)
    //     if lhs != rhs
    //     if goal.getType(lhs) == IntType && goal.getType(rhs) == IntType
    //   } yield lhs |<=| rhs

    def VarCondidates(goal: Goal): Seq[Var] = {
      for {
        tmpvar <- goal.programVars.filter(goal.post.phi.vars.contains)
        if goal.getType(tmpvar) == IntType
      } yield tmpvar
    }

    def BiVarCandidates(goal: Goal): Seq[Expr] = {
      val Varset = VarCondidates(goal)
      for{
        lhs <- Varset
        rhs <- Varset
        if lhs != rhs
      } yield lhs |<=| rhs
    }
    // def BiVarCandidates1(goal: Goal): Seq[Expr] = {
    //   val Varset = VarCondidates(goal)
    //   for{
    //     lhs <- 0 to Varset.length - 2
    //     rhs <- lhs to Varset.length - 1
    //     if Varset(lhs) != Varset(rhs)
    //   } yield Varset(lhs) |=| Varset(rhs)
    // }

    // def BiVarCandidates2(goal: Goal): Seq[Expr] = {
    //   val Varset = VarCondidates(goal)
    //   for{
    //     lhs <- 0 to Varset.length - 2
    //     rhs <- lhs to Varset.length - 1
    //     if Varset(lhs) != Varset(rhs)
    //   } yield Varset(lhs) |/=| Varset(rhs)
    // }

    // def BiVarCandidates3(goal: Goal): Seq[Expr] = {
    //   val Varset = VarCondidates(goal)
    //   for{
    //     lhs <- 0 to Varset.length - 2
    //     rhs <- lhs to Varset.length - 1
    //     if Varset(lhs) != Varset(rhs)
    //   } yield Varset(lhs) |<| Varset(rhs)
    // }
    // def BiVarCandidates4(goal: Goal): Seq[Expr] = {
    //   val Varset = VarCondidates(goal)
    //   for{
    //     rhs <- 0 to Varset.length - 2
    //     lhs <- rhs to Varset.length - 1
    //     if Varset(lhs) != Varset(rhs)
    //   } yield Varset(lhs) |<| Varset(rhs)
    // }
    
    def VarConstCandidates1(goal: Goal): Seq[Expr] = {
      for{
        lhs <- VarCondidates(goal)
        rhs <- goal.post.phi.intconstant //- Expressions.IntConst(0)
      } yield lhs |<| rhs
    }

    def VarConstCandidates2(goal: Goal): Seq[Expr] = {
      for{
        rhs <- VarCondidates(goal)
        lhs <- goal.post.phi.intconstant //- Expressions.IntConst(0)
      } yield lhs |<| rhs
    }

    def VarConstCandidates3(goal: Goal): Seq[Expr] = {
      for{
        lhs <- VarCondidates(goal)
        rhs <- goal.post.phi.intconstant //- Expressions.IntConst(0)
      } yield lhs |=| rhs
    }

    def VarConstCandidates4(goal: Goal): Seq[Expr] = {
      for{
        lhs <- VarCondidates(goal)
        rhs <- goal.post.phi.intconstant //- Expressions.IntConst(0)
      } yield lhs |/=| rhs
    }

    def condCandidates(goal: Goal): Seq[Expr] = {
      val atoms = BiVarCandidates(goal) ++ VarConstCandidates1(goal) ++ VarConstCandidates2(goal) ++ VarConstCandidates3(goal) ++ VarConstCandidates4(goal)
      // Toggle this to enable abduction of conjunctions
      // (without branch pruning, produces too many branches)
      //      atoms
      for {
        subset <- atoms.toSet.subsets.toSeq.sortBy(_.size)
        if subset.nonEmpty && subset.size <= goal.env.config.maxGuardConjuncts
      } yield PFormula(subset).toExpr
    }

    def guardedCandidates(goal: Goal): Seq[RuleResult] =
      for {
        cond <- condCandidates(goal)
        pre = goal.pre.phi
        if SMTSolving.valid((pre && cond) ==> goal.universalPost)
        if SMTSolving.sat((pre && cond).toExpr)
        unknown = Branch.minimalUnknown(goal.pre.phi, cond.vars)
        thenGoal = goal.spawnChild(goal.pre.copy(phi = goal.pre.phi.substUnknown(unknown, cond)))
      } yield {
        RuleResult(List(thenGoal), GuardedProducer(cond), this, thenGoal)
      }

    def apply(goal: Goal): Seq[RuleResult] = {
      val (uniPost, exPost) = goal.splitPost
      if (SMTSolving.valid(goal.pre.phi ==> uniPost))
        CheckPost.filterOutValidPost(goal, exPost, uniPost)
      else {
        val guarded = guardedCandidates(goal)
        if (guarded.isEmpty)
        // Abduction failed
          List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal)) // pre doesn't imply post: goal is unsolvable
        else { 
          guarded.take(1) // TODO: try several incomparable conditions, but filter out subsumed ones?
        }
      }
    }
  }

}

