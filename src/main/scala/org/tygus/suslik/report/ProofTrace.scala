package org.tygus.suslik.report

import java.io.{BufferedWriter, File, FileWriter}

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.Memoization
import org.tygus.suslik.synthesis.Memoization.GoalStatus
import org.tygus.suslik.synthesis.SearchTree.{AndNode, OrNode, SearchNode}
import org.tygus.suslik.synthesis.rules.Rules
import upickle.default.{macroRW, ReadWriter => RW}

import scala.annotation.tailrec

sealed abstract class ProofTrace {
  import ProofTrace._
  def add(node: OrNode) { }
  def add(node: AndNode, nChildren: Int) { }
  def add(node: SearchNode, status: GoalStatus, from: Option[String] = None) { }
  def add(result: Rules.RuleResult, parent: OrNode) { }
  def add(backlink: BackLink) { }
}

object ProofTrace {
  case class BackLink(bud: Goal, companion: Goal)

  var current: ProofTrace = ProofTraceNone  // oops, not thread-safe
}

object ProofTraceNone extends ProofTrace

class ProofTraceJson(val outputFile: File) extends ProofTrace {
  import ProofTrace._
  import ProofTraceJson._

  val writer = new BufferedWriter(new FileWriter(outputFile))

  def this(outputFilename: String) = this(new File(outputFilename))

  private def writeObject[T](t: T)(implicit w: upickle.default.Writer[T]): Unit = {
    writer.write(upickle.default.write(t))
    writer.write("\n\n")
    writer.flush()
  }

  override def add(node: OrNode): Unit =
    writeObject(NodeEntry(node.id, "OrNode", node.pp(), GoalEntry(node.goal), -1, node.cost))

  override def add(node: AndNode, nChildren: Int): Unit =
    writeObject(NodeEntry(node.id, "AndNode", node.pp(), null, nChildren, -1))

  override def add(node: SearchNode, status: GoalStatus, from: Option[String] = None): Unit = {
    val st = status match {
      case Memoization.Succeeded(_, _) => Succeeded
      case Memoization.Failed => Failed
      case _ => throw new RuntimeException(s"cannot serialize $status")
    }
    writeObject(StatusEntry(node.id, st.copy(from = from)))
  }

  override def add(result: Rules.RuleResult, parent: OrNode) {
    if (result.subgoals.isEmpty) {
      val resolution = AndNode(-1 +: parent.id, parent, result)
      val status = Memoization.Succeeded(null, null) // ignoring solution, sry
      add(resolution, 0)
      add(resolution, status)
      add(parent, status)
    }
  }

  override def add(backlink: BackLink) {
    writeObject(CyclicEntry(
      BackLinkEntry(backlink.bud.label.pp, backlink.companion.label.pp)))
  }
}


object ProofTraceJson {

  case class NodeEntry(id: Vector[Int], tag: String, pp: String, goal: GoalEntry,
                       nChildren: Int, cost: Int)
  object NodeEntry {
    implicit val rw: RW[NodeEntry] = macroRW
  }

  case class GoalEntry(id: String,
                       pre: String,
                       post: String,
                       sketch: String,
                       programVars: Seq[(String, String)],
                       existentials: Seq[(String, String)],
                       ghosts: Seq[(String, String)])
  object GoalEntry {
    implicit val rw: RW[GoalEntry] = macroRW

    def apply(goal: Goal): GoalEntry = GoalEntry(goal.label.pp,
      goal.pre.pp, goal.post.pp, goal.sketch.pp,
      vars(goal, goal.programVars), vars(goal, goal.existentials),
      vars(goal, goal.universalGhosts))

    private def vars(goal: Goal, vs: Iterable[Expressions.Var]) =
      vs.map(v => (goal.getType(v).pp, v.pp)).toSeq
  }

  case class GoalStatusEntry(tag: String, from: Option[String] = None)
  val Succeeded = new GoalStatusEntry("Succeeded")
  val Failed = new GoalStatusEntry("Failed")

  object GoalStatusEntry {
    implicit val readWriter: RW[GoalStatusEntry] = macroRW
  }

  case class StatusEntry(at: Vector[Int], status: GoalStatusEntry)
  object StatusEntry {
    implicit val rw: RW[StatusEntry] = macroRW
  }

  case class CyclicEntry(backlink: BackLinkEntry)
  object CyclicEntry {
    implicit val rw: RW[CyclicEntry] = macroRW
  }

  case class BackLinkEntry(bud: String, companion: String)
  object BackLinkEntry {
    implicit val rw: RW[BackLinkEntry] = macroRW
  }
}

// [Certify] Collects non-backtracked SearchTree nodes (and their ancestors), used to populate the CertTree
class ProofTraceCert extends ProofTrace {
  import scala.collection.mutable

  val derivations: mutable.HashMap[OrNode, Seq[(Boolean, AndNode)]] = mutable.HashMap.empty
  val subgoals: mutable.HashMap[AndNode, Seq[(Boolean, OrNode)]] = mutable.HashMap.empty
  val failed: mutable.Set[OrNode] = mutable.Set.empty
  val succeeded: mutable.Set[OrNode] = mutable.Set.empty
  val cachedGoals: mutable.HashMap[OrNode, OrNode] = mutable.HashMap.empty
  var root: OrNode = _


  def selfprint(curroot:OrNode, depth: Int): Unit = {
    if(depth == 0) return;
    Console.println(s"Trace:")
    derivations.get(curroot) match {
      case None => return;
      case Some(value1) => value1.foreach(x => {
        Console.println(s"${x._1.toString() + " " + x._2.pp()}")
        subgoals.get(x._2) match {
          case None => None
          case Some(value2) => value2.foreach(y => {
            Console.println(s"${y._1.toString() + " " + y._2.pp()}")
            selfprint(y._2, depth-1)
          })
        }
      }
      )
    }
    
    
  }
  override def add(node: OrNode): Unit = {
    node.parent match {
      case None => root = node
      case Some(an) =>
        subgoals.get(an) match {
          case None => subgoals(an) = Seq((false, node))
          case Some(ons) => subgoals(an) = ons :+ (false, node)
        }
    }
  }

  override def add(node: AndNode, nChildren: Int): Unit = {
    derivations.get(node.parent) match {
      case None => derivations(node.parent) = Seq((false, node))
      case Some(ans) => derivations(node.parent) = ans :+ (false, node)
    }
  }

  override def add(node: SearchNode, status: GoalStatus, from: Option[String] = None): Unit = (node, status) match {
    case (node: OrNode, Memoization.Succeeded(_, id)) =>
      succeeded.add(node)
      derivations.keys.find(_.id == id) match {
        case Some(succeededOr) => cachedGoals(node) = succeededOr
        case None => assert(false, s"Couldn't find cached OrNode with id $id")
      }
    case (node: OrNode, Memoization.Failed) =>
      failed.add(node)
    case _ =>
  }

  override def add(result: Rules.RuleResult, parent: OrNode): Unit = {
    if (result.subgoals.isEmpty) {
      val an = AndNode(-1 +: parent.id, parent, result)
      derivations.get(parent) match {
        case None => derivations(parent) = Seq((true, an))
        case Some(ans) => derivations(parent) = ans :+ (true, an)
      }
      succeeded.add(parent)
    }
  }

  @tailrec
  private def handleFail(node: OrNode, original: OrNode): Unit = node.parent match {
    case None =>
    case Some(an) =>
      derivations(an.parent) = derivations(an.parent).filterNot(_._2.id == an.id)
      if (!derivations(an.parent).exists(_._1)) {
        // This goal has no more viable candidate derivations, so can prune further up the tree
        handleFail(an.parent, original)
      }
  }

  @tailrec
  private def handleSuccess(node: OrNode): Unit = node.parent match {
    case None =>
    case Some(an) =>
      val newOns = updatePeerStatus(node, subgoals(an), newStatus = true)
      subgoals(an) = newOns
      if (newOns.forall(_._1)) {
        derivations(an.parent) = updatePeerStatus(an, derivations(an.parent), newStatus = true)
        handleSuccess(an.parent)
      }
  }

  def pruneFailed(): Unit = {
    for (s <- succeeded) {
      handleSuccess(s)
    }
    for (f <- failed) {
      handleFail(f, f)
    }
  }

  private def updatePeerStatus[T <: SearchNode](node: T, peers: Seq[(Boolean, T)], newStatus: Boolean): Seq[(Boolean, T)] =
    peers.map { case (status, n) => if (n.id == node.id) (newStatus, n) else (status, n )}

  def childAnds(node: OrNode): Seq[AndNode] = {
    derivations.getOrElse(node, Seq.empty).filter(_._1).map(_._2)
  }
  def childOrs(node: AndNode): Seq[OrNode] =
    subgoals.getOrElse(node, Seq.empty).filter(_._1).map(_._2)
}
