package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._

import scala.collection.mutable.ListBuffer

class FreshNameGen(mangleStr: String) {
  private var uniq: Int = 0

  def genFresh(baseString: String): Var = {
    val r = withCurrentUniq(removeUniq(baseString))
    uniq += 1
    r
  }

  def withCurrentUniq(baseString: String): Var = {
    // build(baseString, uniq)
    new Var(removeUniq(baseString) + mangleStr + uniq.toString)
  }

  def freshen(x: Var): Var =
    genFresh(removeUniq(x.name))

  def freshenWithCurrentUniq(x: Var): Var =
    withCurrentUniq(removeUniq(x.name))

  def removeUniq(str: String): String =
    str.takeWhile(c => c != '$' && c != '%')

  def eqModUniq(str1: String, str2: String): Boolean =
    removeUniq(str1) == removeUniq(str2)
}

object PredFreshNameGen extends FreshNameGen("$") {
}

object LambdaLiftNameGen extends FreshNameGen("%") {
}

// class FreshIdentGen[A <: UniqueName](build: (Ident, Int) => A) {
//   private var uniq: Int = 0
//
//   def genFresh(baseIdent: Ident): A = {
//     val r = withCurrentUniq(baseIdent)
//     uniq += 1
//     r
//   }
//
//   def withCurrentUniq(baseIdent: Ident): A = {
//     build(baseIdent, uniq)
//     // baseIdent + mangleStr + uniq.toString
//   }
//
//   def freshen(x: A): A =
//     genFresh(x.getBase)
//
//   def freshenWithCurrentUniq(x: A): A =
//     withCurrentUniq(x.getBase)
// }
//
