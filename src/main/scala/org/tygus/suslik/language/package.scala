package org.tygus.suslik

/**
  * @author Ilya Sergey
  */

package object language {

  type Ident = String

  // sealed class Name {
  //   def asString: String
  // }
  //
  // case class SimpleName(str: String) extends Name {
  //   def asString = str
  // }
  //
  // class UniqueName(base: String, uniq: Int, mangleStr: String) extends Name {
  //   def getBase: String = base
  //
  //   def asString: String = base + mangleStr + uniq.toString
  //
  //   // def freshen(gen: FreshIdentGen[A]): A = gen.freshen(this)
  // }
  //
  // // object UniqueName {
  // //   private var uniq: Int = 0
  // //
  // //   def genFresh
  // //
  // //   def withCurrentUniq[A <: UniqueName](build: (Ident, Int) => A, base: Ident): A =
  // //     build(base, uniq)
  // // }
  //
  // case class PredName(base: String, uniq: Int) extends UniqueName(base, uniq, "$")
  // object PredName { }
  //
  // case class LambdaLiftName(base: String, uniq: Int) extends UniqueName(base, uniq, "%")
  // object LambdaLift { }


}
