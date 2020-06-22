package org.tygus.suslik.synthesis

import java.io.PrintWriter

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.language.Statements.{Solution, _}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.report.{Log, ProofTrace}
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.synthesis.tactics.Tactic
import org.tygus.suslik.util.SynStats

import scala.Console._
import scala.annotation.tailrec

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

class Synthesis(tactic: Tactic, implicit val log: Log, implicit val trace: ProofTrace) extends SepLogicUtils {

  def synthesizeProc(funGoal: FunSpec, env: Environment, sketch: Statement): (List[Procedure], SynStats) = {
    implicit val config: SynConfig = env.config
    implicit val stats: SynStats = env.stats
    val FunSpec(name, tp, formals, pre, post, var_decl) = funGoal

    val goal = topLevelGoal(pre, post, formals, name, env, sketch, var_decl)
    log.print(List(("Initial specification:", Console.RESET), (s"${goal.pp}\n", Console.BLUE)))
    SMTSolving.init()
    memo.clear()
    try {
      synthesize(goal)(stats = stats) match {
        case Some((body, helpers)) =>
          printTree
          val main = Procedure(funGoal, body)
          (main :: helpers, stats)
        case None =>
          log.out.printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          (Nil, stats)
      }
    } catch {
      case SynTimeOutException(msg) =>
        log.out.printlnErr(msg)
        (Nil, stats)
    }
  }

  type Worklist = List[OrNode]

  protected def synthesize(goal: Goal)
                          (stats: SynStats): Option[Solution] = {
    // Initialize worklist: root or-node containing the top-level goal
    val root = OrNode(Vector(), goal, None, goal.allHeaplets)
    val worklist = List(root)
    processWorkList(worklist)(stats, goal.env.config)
  }

  @tailrec final def processWorkList(worklist: Worklist)
                                    (implicit
                                     stats: SynStats,
                                     config: SynConfig): Option[Solution] = {
    // Check for timeouts
    if (!config.interactive && stats.timedOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut} seconds.\n")
    }

    val sz = worklist.length
    log.print(List((s"Worklist ($sz): ${worklist.map(n => s"${n.pp()}[${n.cost}]").mkString(" ")}", Console.YELLOW)))
    log.print(List((s"Memo (${memo.size}) Suspended (${memo.suspendedSize})", Console.YELLOW)))
    stats.updateMaxWLSize(sz)

    if (worklist.isEmpty) None // No more goals to try: synthesis failed
    else {
      val (node, withRest) = selectNode(worklist) // Select next node to expand
      val goal = node.goal
      implicit val ctx = log.Context(goal)
      stats.addExpandedGoal(node)
      log.print(List((s"Expand: ${node.pp()}[${node.cost}]", Console.YELLOW)))
      if (config.printEnv) {
        log.print(List((s"${goal.env.pp}", Console.MAGENTA)))
      }
      log.print(List((s"${goal.pp}", Console.BLUE)))
      trace.add(node)

      // Lookup the node in the memo
      val res = memo.lookup(goal) match {
        case Some(Failed) => { // Same goal has failed before: record as failed
          log.print(List((s"Recalled FAIL", RED)))
          trace.add(node.id, Failed)
          Left(node.fail(withRest(Nil)))
        }
        case Some(Succeeded(sol)) => { // Same goal has succeeded before: return the same solution
          log.print(List((s"Recalled solution ${sol._1.pp}", RED)))
          trace.add(node.id, Succeeded(sol))
          node.succeed(sol, withRest(Nil))
        }
        case Some(Expanded) => { // Same goal has been expanded before: wait until it's fully explored
          log.print(List(("Suspend", RED)))
          memo.suspend(node)
          Left(withRest(List(node)))
        }
        case None => expandNode(node, withRest) // First time we see this goal: do expand
      }
      res match {
        case Left(newWorklist) => processWorkList(newWorklist)
        case Right(solution) => Some(solution)
      }
    }
  }

  // Given a worklist, return the next node to work on
  // and a strategy for combining its children with the rest of the list
  protected def selectNode(worklist: Worklist)(implicit config: SynConfig): (OrNode, Worklist => Worklist) =
    if (config.depthFirst)  // DFS? Pick the first one
      (worklist.head, _ ++ worklist.tail)
    else {  // Otherwise pick a minimum-cost node that is not suspended
      val best = worklist.minBy(n => (memo.isSuspended(n), n.cost))
      val idx = worklist.indexOf(best)
      (best, worklist.take(idx) ++ _ ++ worklist.drop(idx + 1))
    }

  // Expand node and return either a new worklist or the final solution
  protected def expandNode(node: OrNode, withRest: List[OrNode] => List[OrNode])(implicit stats: SynStats,
                                         config: SynConfig): Either[List[OrNode], Solution] = {
    val goal = node.goal
    memo.save(goal, Expanded)
    implicit val ctx = log.Context(goal)

    // Apply all possible rules to the current goal to get a list of alternative expansions,
    // each of which can have multiple open subgoals
    val rules = tactic.nextRules(node)
    val allExpansions = applyRules(rules)(node, stats, config, ctx)
    val expansions = tactic.filterExpansions(allExpansions)

    // Check if any of the expansions is a terminal
    expansions.find(_.subgoals.isEmpty) match {
      case Some(e) =>
        if (config.certTarget != null || config.printTree) {
          // [Certify]: Add a terminal node and its ancestors to the certification tree
          CertTree.addSuccessfulPath(node, e)
        }
        trace.add(e, node)
        node.succeed(e.producer(Nil), withRest(Nil))
      case None => { // no terminals: add all expansions to worklist
        // Create new nodes from the expansions
        val newNodes = for {
          (e, i) <- expansions.zipWithIndex
          andNode = AndNode(i +: node.id, e.producer, node, e.consume, e.rule)
          nSubs = e.subgoals.size; () = trace.add(andNode, nSubs)
          ((g, p), j) <- if (nSubs == 1) List(((e.subgoals.head, e.produces(goal).head), -1)) // this is here only for logging
          else e.subgoals.zip(e.produces(goal)).zipWithIndex
        } yield OrNode(j +: andNode.id, g, Some(andNode), p)

        // Suspend nodes with older and-siblings
        newNodes.foreach (n => {
          val idx = n.childIndex
          if (idx > 0) {
            val sib = newNodes.find(s => s.parent == n.parent && s.childIndex == idx - 1).get
            log.print(List((s"Suspending ${n.pp()} until ${sib.pp()} succeeds", RED)))
            memo.suspendSibling(n, sib) // always process the left and-goal first; unsuspend next once it succeeds
          }
        })

        if (newNodes.isEmpty) {
          // This is a dead-end: prune worklist and try something else
          log.print(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
          trace.add(node.id, Failed)
          Left(node.fail(withRest(Nil)))
        } else {
          stats.addGeneratedGoals(newNodes.size)
          Left(withRest(newNodes.toList))
        }
      }
    }
  }


  protected def applyRules(rules: List[SynthesisRule])(implicit node: OrNode,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ctx: log.Context): Seq[RuleResult] = {
    implicit val goal: Goal = node.goal
    rules match {
      case Nil => Vector() // No more rules to apply: done expanding the goal
      case r :: rs =>
        // Invoke the rule
        val children = r(goal)

        if (children.isEmpty) {
          // Rule not applicable: try other rules
          log.print(List((s"$r FAIL", RESET)), isFail = true)
          applyRules(rs)
        } else {
          // Rule applicable: try all possible sub-derivations
          val childFootprints = children.map(log.showChild(goal))
          log.print(List((s"$r (${children.size}): ${childFootprints.head}", RESET)))
          for {c <- childFootprints.tail}
            log.print(List((s" <|>  $c", CYAN)))

          if (r.isInstanceOf[InvertibleRule]) {
            // The rule is invertible: do not try other rules on this goal
            children
          } else {
            // Both this and other rules apply
            children ++ applyRules(rs)
          }
        }
    }
  }

  private def showFootprint(f: Footprint): String = s"$GREEN{${f.pre.pp}}$MAGENTA{${f.post.pp}}$RESET"
  private def showChild(goal: Goal)(c: RuleResult): String =
    c.subgoals.length match {
    case 0 => showFootprint(c.consume)
    case _ => s"${showFootprint(c.consume)} --> ${c.produces(goal).map(showFootprint).mkString(", ")}"
//    case 1 =>
//      s"${showFootprint(c.consume)} --> ${showFootprint(c.produces(goal).head)}"
//    case _ =>
//      s"${showFootprint(c.consume)} --> ${showFootprint(c.produces(goal).head)}, ..."
  }

  private def getIndent(implicit ind: Int): String = if (ind <= 0) "" else "|  " * ind

  protected def printLog(sc: List[(String, String)], isFail: Boolean = false)
                      (implicit config: SynConfig, ind: Int = 0): Unit = {
    if (config.printDerivations) {
      if (!isFail || config.printFailed) {
        for ((s, c) <- sc if s.trim.length > 0) {
          print(s"$RESET$getIndent")
          println(s"$c${s.replaceAll("\n", s"\n$RESET$getIndent$c")}")
        }
      }
      print(s"$RESET")
    }
  }

  protected def printTree(implicit config: SynConfig, ind: Int = 0): Unit = {
    if (config.printTree) {
      val tree = CertTree.pp()
      println()
      if (config.treeDest == null) println(tree) else {
        new PrintWriter(config.treeDest) { write(tree); close() }
        val msg = s"Successful derivations saved to ${config.treeDest.getCanonicalPath}"
        println(s"$MAGENTA$msg")
      }
    }
  }
}