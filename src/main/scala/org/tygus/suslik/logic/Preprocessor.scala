package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.language.Ident
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.defunctionalize.{DefunctionalizeInductive,DefunctionalizeGoalContainer,DefunctionalizeFunSpec,FreshIdentGen}
import org.tygus.suslik.defunctionalize.{PredicateValue,PPredicateValue,SPredicateValue}
import org.tygus.suslik.language.PredType

import scala.collection.immutable.Set
import scala.collection.mutable.ListBuffer

object Preprocessor extends SepLogicUtils {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def preprocessProgram(prog: Program, params: SynConfig): (Seq[FunSpec], PredicateEnv, FunctionEnv, Statement) = {
    val Program(preds0, funs0, goal0) = prog

    val gen = new FreshIdentGen()
    val predMap0 = preds0.map(ps => ps.name -> ps).toMap

    // [Cardinality] Instrument predicates with missing cardinality constraints
    // val newPreds = preds

    val preds = preds0.to[ListBuffer]

    val funs = funs0.map(fun => {
        val defunFunSpec = new DefunctionalizeFunSpec(fun, gen, predMap0)
        val newFun = defunFunSpec.defunctionalize()

        preds ++= defunFunSpec.getGeneratedPreds()
        newFun
      })

    val defun = new DefunctionalizeGoalContainer(goal0, gen, predMap0)

    val (goal, generatedPreds) = defun.defunctionalize()

    preds ++= generatedPreds

    val funMap = funs.map(fs => fs.name -> fs).toMap

    // Enable predicate instrumentation
    val newPreds = preds.filter(noAbstractArgs).map(p => p.copy(clauses = p.clauses.map(addCardConstraints)))
    val predMap = newPreds.map(ps => ps.name -> ps).toMap
    (List(goal.spec), predMap, funMap, goal.body)
  }

  private def noAbstractArgs(p: InductivePredicate) = {
    p.params.forall {
      case (_, PredType) => false
      case _ => true
    }
  }

  /**
    * Add a missing cardinality constraint to a predicate clause
    */
  private def addCardConstraints(clause: InductiveClause): InductiveClause = {
    val InductiveClause(sel, Assertion(phi, sigma)) = clause

    // All cardinality-related variables
    val cardVars = (for {
      SApp(_, _, _, card) <- sigma.chunks
      v <- card.vars
    } yield v).toSet

    val constrainedVars = sel.vars ++ phi.vars
    if (cardVars.subsetOf(constrainedVars)) return clause // No constraints to add

    // Otherwise, generate for the clause cardinality
    val (ptsCount, clauseCard) = heapCardinality(sigma)

    // Inequalities

    // All cardinalities are less than self-cardinality
    val ltCards = if (ptsCount > 0) {
      for (cv <- cardVars) yield BinaryExpr(OpLt, cv, selfCardVar)
    } else Set.empty

    // All cardinalities are non-negative
    // val posConstraints = for (cv <- cardVars) yield BinaryExpr(OpLeq, IntConst(0), cv)


    val newPhi = PFormula(phi.conjuncts ++ ltCards)

    InductiveClause(sel, Assertion(newPhi, sigma))
  }


  /**
    * [Cardinality] Obsolete: add precise cardinality
    */
  private def addPreciseCardConstraints(clause: InductiveClause): InductiveClause = {
    val InductiveClause(sel, Assertion(phi, sigma)) = clause

    // All cardinality-related variables
    val cardVars = (for {
      SApp(_, _, _, card) <- sigma.chunks
      v <- card.vars
    } yield v).toSet


    // Constant footprint
    if (cardVars.isEmpty) {
      val (_, clauseCard) = heapCardinality(sigma)
      val cardConstraint = BinaryExpr(OpEq, selfCardVar, clauseCard) // self_card = x
      val newPhi = PFormula(phi.conjuncts ++ Set(cardConstraint))
      return InductiveClause(sel, Assertion(newPhi, sigma))
    }

    val constrainedVars = sel.vars ++ phi.vars
    if (cardVars.subsetOf(constrainedVars)) return clause // No constraints to add

    // Otherwise, generate for the clause cardinality
    val (ptsCount, clauseCard) = heapCardinality(sigma)

    // Main equality
    val cardConstraint = BinaryExpr(OpEq, selfCardVar, clauseCard) // self_card = 2 + _alpha_xxx

    // To help the solver with strict inequalities - needed for trees
    val additionalConstraints: Set[Expr] =
      if (ptsCount == 0) Set.empty
      else for {
        v <- cardVars
      } yield BinaryExpr(OpLt, v, selfCardVar)


    val newPhi = PFormula(phi.conjuncts ++ Set(cardConstraint) ++ additionalConstraints)

    InductiveClause(sel, Assertion(newPhi, sigma))
  }


}
