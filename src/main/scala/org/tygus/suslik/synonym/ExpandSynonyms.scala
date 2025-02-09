package org.tygus.suslik.synonym

import org.tygus.suslik.language._
import org.tygus.suslik.defunctionalize.TransformAssertionsH
import org.tygus.suslik.logic.HasAssertions
import org.tygus.suslik.logic.InductivePredicate

import org.tygus.suslik.logic.PFormula._
import org.tygus.suslik.logic.SFormula._
import org.tygus.suslik.logic.Heaplet
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._

import org.tygus.suslik.language.Expressions._

import scala.collection.immutable.SortedSet

class ExpandSynonyms[A <: HasAssertions[A]](synonyms: Map[String, Synonym], orig: A) extends TransformAssertionsH[A] {
  protected def setup(): A = orig

  protected def transformExpr(e: Expr): Expr = e

  protected def transformHeaplet(h: Heaplet): Seq[Heaplet] = {
    h match {
      case SApp(predIdent, args, tag, card) => {
        synonyms get predIdent match {
          case Some(syn) => {
            val r = syn.expand(args)
            println(s"Expanding ${predIdent} to ${r.pp}...")
            r.chunks
          }
          case None => Seq[Heaplet](h)
            // Seq[Heaplet](SApp(predIdent, args.map(new ExpandSynonyms[Expr](synonyms, _).transform()), tag, card))
        }
      }
      case _ => Seq[Heaplet](h)
    }
  }
}

