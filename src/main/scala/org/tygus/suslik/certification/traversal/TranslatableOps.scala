package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

object TranslatableOps {
  implicit class Translatable[S <: SourceStep](step: S) {
    def translate[D <: DestStep, C <: ClientContext[D]](clientContext: C)(implicit translator: Translator[S, D, C]): Translator.Result[D,C] = {
      translator.translate(step, clientContext)
    }
  }
}
