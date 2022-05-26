package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.language.Ident
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.synthesis.SynConfig
// import org.tygus.suslik.defunctionalize.{DefunctionalizeInductive,DefunctionalizeGoalContainer,DefunctionalizeFunSpec,FreshIdentGen}
import org.tygus.suslik.defunctionalize.GoalContainerEliminateAbstractions
import org.tygus.suslik.defunctionalize.EliminateAbstractions
import org.tygus.suslik.defunctionalize.SpecializationList
import org.tygus.suslik.defunctionalize.{PredicateValue,PPredicateValue,SPredicateValue}
import org.tygus.suslik.language.PredType

import org.tygus.suslik.synonym.ExpandSynonyms

import scala.collection.immutable.Set
import scala.collection.mutable.ListBuffer

object Preprocessor extends SepLogicUtils {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def preprocessProgram(prog: Program, params: SynConfig): (Seq[FunSpec], PredicateEnv, FunctionEnv, Statement) = {
    val Program(predsWithSyns, syns, funsWithSyns, goalWithSyns) = prog

    for (s <- syns) {
      s.scopeCheck()
    }

    val synMap: Map[String, Synonym] = syns.map(s => s.name -> s).toMap

    val preds0 = predsWithSyns.map(expandSynonyms(synMap, _))
    val funs0 = funsWithSyns.map(expandSynonyms(synMap, _))
    val goal0 = expandSynonyms(synMap, goalWithSyns)

    val predMap0 = preds0.map(ps => ps.name -> ps).toMap

    // [Cardinality] Instrument predicates with missing cardinality constraints
    // val newPreds = preds

    val preds = preds0.to[ListBuffer]

    val goalElimAbs = new GoalContainerEliminateAbstractions()

    val (freshIdentGen, (goal, generatedPreds)) = goalElimAbs.transform(goal0, predMap0)

    val funSpecElimAbs = new EliminateAbstractions[FunSpec, FunSpec](freshIdentGen, new SpecializationList())

    val funs = funs0.map(f => {
        println(s"generating for ${f.pp}")
        val (newF, generated) = funSpecElimAbs.transform(f, predMap0)
        preds ++= generated
        newF
      }
    ) // TODO: Figure this out

    preds ++= generatedPreds

    val funMap = funs.map(fs => fs.name -> fs).toMap

    // Enable predicate instrumentation
    val newPreds = preds.filter(noAbstractArgs).map(p => p.copy(clauses = p.clauses.map(addCardConstraints)))
    val predMap = newPreds.map(ps => ps.name -> ps).toMap

    // println(s"newPreds: ${newPreds.map(_.pp)}")
    println(s"done preprocessing for ${goal.spec.pp}")
    println(s"preds = ${newPreds.map(_.pp)}")
    (List(goal.spec), predMap, funMap, goal.body)
  }

  private def expandSynonyms[A <: HasAssertions[A]](synonyms: Map[String, Synonym], x: A): A = {
    val tr = new ExpandSynonyms[A](synonyms, x)
    tr.transform()
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
