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
abstract class TransformAssertions[S, A <: HasAssertions[S]] {

  def transform(): S = {
    finish(setup().visitAssertions(expr => transformExpr(expr), h => transformHeaplet(h)))
  }

  protected def setup(): A

  protected def finish(x: S): S = x

  protected def transformExpr(e: Expr): Expr
  protected def transformHeaplet(h: Heaplet): Seq[Heaplet]

  // private def transformAssertion(asn: Assertion): Assertion = {
  //   Assertion(transformPFormula(asn.phi), transformSFormula(asn.sigma))
  // }
  //
}

abstract class TransformAssertionsH[A <: HasAssertions[A]] extends TransformAssertions[A, A] {
}
