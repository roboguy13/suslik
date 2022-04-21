package org.tygus.suslik.defunctionalize

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.{PFormula,SFormula}
import org.tygus.suslik.logic.Specifications._

import scala.collection.immutable.SortedSet

  // This abstracts over the traversal pattern used by both the part of
  // defunctionalization that traverses the inductive predicate as well
  // as the part that traverses expressions which use the inductive predicate and
  // might contain abstractions.
abstract class TransformAssertions[A <: HasAssertions[A]] {

  def transform(): A = {
    finish(setup().visitAssertions(asn => transformAssertion(asn)))
  }

  protected def setup(): A

  protected def finish(x: A): A = x

  protected def transformExpr(e: Expr): SortedSet[Expr]
  protected def transformHeaplet(h: Heaplet): Seq[Heaplet]

  private def transformAssertion(asn: Assertion): Assertion = {
    Assertion(transformPFormula(asn.phi), transformSFormula(asn.sigma))
  }

  private def transformPFormula(phi: PFormula): PFormula = {
    PFormula(phi.conjuncts.flatMap((e : Expr) => transformExpr(e)))
  }

  private def transformSFormula(sigma: SFormula): SFormula = {
    SFormula(sigma.chunks.flatMap((chunk: Heaplet) => transformHeaplet(chunk)))
  }
}
