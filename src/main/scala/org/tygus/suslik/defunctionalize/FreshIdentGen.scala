package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._

import scala.collection.mutable.ListBuffer

class FreshIdentGen(mangleStr: String) {
  val existingIdents: ListBuffer[Ident] = ListBuffer[Ident]()

  private var uniq: Int = 0

  def genFresh(baseIdent: Ident): Ident = {
    uniq += 1
    withCurrentUniq(baseIdent)
  }

  // def genFreshWith(baseIdent: Ident, n: Int): Ident = {
  //   val newName = baseIdent + mangleStr + n.toString

  //   if (existingIdents.contains(newName)) {
  //     genFreshWith(baseIdent, n + 1)
  //   } else {
  //     existingIdents += newName
  //     newName
  //   }
  // }

  def withCurrentUniq(baseIdent: Ident): Ident = {
    baseIdent + mangleStr + uniq.toString
  }

  // def getBaseName(baseIdent: Ident): Ident = {
  //   baseIdent.takeWhile(c => c != mangleStr)
  // }
}

