package org.tygus.suslik.compile

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Queue

// | This is essentially an ANF transformation
class CompileWith {
  def compileWith(goal: GoalContainer): GoalContainer = {
    goal.withClause match {
      case None => goal
      case Some(withClause) =>
        goal.copy(body = (goal.body :: compileWith(goal.spec.pre, goal.spec.post, withClause)).foldRight(Skip.asInstanceOf[Statement])((x, y) => SeqComp(x, y)))
    }
  }

  private def compileWith(pre: Assertion, post: Assertion, withClause: WithClause): List[Statement] = {
    val freeVars = pre.freeVars ++ post.freeVars

    // withClause.apps.map(x => Call(Var(x.fName), x.args, None))

    // val roseTree = makeRoseTreeRoot(new FreshVarGen(freeVars), withClause.apps.head)

    val (newApp, generated) = transformAndGenerate(new FreshVarGen(freeVars), withClause.apps.head)

    generated.map(((app, xs) => genCall(app, xs)).tupled) ++ List(Call(Var(newApp.fName), newApp.args, None))

    // RoseTree.breadthFirstTraversal(roseTree)
  }

  private def genCall(outVar: Var, app: PApp): Statement = {
    SeqComp(Malloc(outVar, AnyType, 1)
           ,Call(Var(app.fName), app.args, None)).asInstanceOf[Statement]
  }

  private def transformAndGenerate(gen: FreshVarGen, app: PApp): (PApp, List[(Var, PApp)]) = {
    val generated: ListBuffer[(Var, PApp)] = new ListBuffer()

    val newApp = app.copy(args = app.args.map {
        case appArg: PApp => {
            val newVar = gen.genVar

            // NOTE: This assumes that the "result" argument is always the first
            // argument.
            val (newAppArg, argGenerated) = transformAndGenerate(gen, appArg.copy(args = newVar :: appArg.args))

            generated ++= argGenerated
            generated += ((newVar, newAppArg))

            newVar
          }
        case x => x
      })

    (newApp, generated.result)
    // app.args.map(transformAndGenerate)
  }

/*
  private def makeRoseTreeRoot(gen: FreshVarGen, app: PApp): (PApp, List[RoseTree]) = {
    val varListBuffer: ListBuffer[Var] = ListBuffer()

    val newApp = app.copy(args = app.args.map {
        case _: PApp => {
          val newVar = gen.genVar
          varListBuffer += newVar
          newVar
        }
        case x => x
      })

    val appTypeArgs: List[PApp] = app.args.collect { case x: PApp => x }

    val varList: List[Var] = varListBuffer.result
    val varApps: List[(Var, PApp)] = varList.zip(appTypeArgs)

    val results: List[RoseTree] = varApps.map { case (v, appArg) => toRoseTree(gen, v, appArg): RoseTree }

    (app, results)
  }

  private def toRoseTree(gen: FreshVarGen, label: Var, app: PApp): RoseTree = {
    val (newApp, results) = makeRoseTreeRoot(gen, app)
    new RoseTree(newApp, label, results)
  }


  // private def reverseLevelOrder(t: RoseTree): List[Var * PApp] = {
  //   
  // }

  // | Invariant: app.args should not contain any 'PApp's
  private class RoseTree(val app: PApp, val label: Var, val children: List[RoseTree]) {
    private var reached: Boolean = false

    def reset(): Unit = {
      reached = false
      children.map(_.reset())
    }
  }

  private object RoseTree {
    def breadthFirstTraversal(t: RoseTree): List[(Var, PApp)] = {
      t.reached = true

      val pairs: ListBuffer[(Var, PApp)] = new ListBuffer()

      val queue: Queue[RoseTree] = new Queue()
      queue += t

      while (!queue.isEmpty) {
        val node = queue.dequeue

        pairs += ((node.label, node.app))

        for (child <- node.children) {
          if (!child.reached) {
            child.reached = true
            queue.enqueue(child)
          }
        }
      }

      pairs.result
    }
  }
*/

  private class FreshVarGen(usedVars: Set[Var]) {
    private var uniq: Int = 0
    private val ident: String = "inter"

    uniq = genUniq(0)

    private def genUniq(n: Int): Int =
      if (usedVars.contains(Var(ident ++ n.toString))) {
        genUniq(n + 1)
      } else {
        n
      }

    def genVar: Var = {
      val curr = Var(ident ++ uniq.toString)
      uniq = genUniq(uniq)
      curr
    }
  }

  // def compileWith(freeVars: Set[Var], gen: FreshVarGen, app: PApp): List[Statement] = ???
  //
  // // Convert to A-normal form
  // def compositionToSequence(gen: FreshVarGen, app: PApp): List[Statement] = {
  //   val seqs = app.args.map {
  //     case appArg: PApp => compositionToSequence(gen, appArg)
  //     case _ => List()
  //   }
  //
  //   ???
  //   // seqs ++ app.copy(args = app.args.map {
  //   //   case appArg: PApp => gen.genVar
  //   //   case x => x
  //   // })
  // }

}

