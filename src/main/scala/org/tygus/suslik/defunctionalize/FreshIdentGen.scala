package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._

import scala.collection.mutable.ListBuffer

class FreshIdentGen(mangleStr: String) {
  val existingIdents: ListBuffer[Ident] = ListBuffer[Ident]()

  def genFresh(baseIdent: Ident): Ident = genFreshWith(baseIdent, 0)

  def genFreshWith(baseIdent: Ident, n: Int): Ident = {
    val newName = baseIdent + mangleStr + n.toString

    if (existingIdents.contains(newName)) {
      genFreshWith(baseIdent, n + 1)
    } else {
      existingIdents += newName
      newName
    }
  }
}

