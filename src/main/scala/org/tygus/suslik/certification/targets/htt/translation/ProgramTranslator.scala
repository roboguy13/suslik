package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.program.Statements.{CFree, CGuarded, CIf, CSkip, CStatement, Noop}
import org.tygus.suslik.certification.targets.htt.translation.TranslatableOps.Translatable
import org.tygus.suslik.certification.traversal.Evaluator.Deferreds
import org.tygus.suslik.certification.traversal.Translator
import org.tygus.suslik.certification.traversal.Translator.Result

import scala.collection.immutable.Queue

object ProgramTranslator extends Translator[SuslikProofStep, CStatement, ProgramContext] {
  private val noDeferreds: Deferreds[CStatement, ProgramContext] = Queue.empty

  override def translate(value: SuslikProofStep, ctx: ProgramContext): Translator.Result[CStatement, ProgramContext] = {
    val meta = (noDeferreds, ctx)
    value match {
      case SuslikProofStep.Open(_, _, _, selectors) =>
        val stmt = CIf(selectors.map(_.translate))
        val metas = selectors.map(_ => meta)
        Result(List(stmt), metas)
      case SuslikProofStep.Branch(cond, _) =>
        val stmt = CGuarded(cond.translate)
        Result(List(stmt), List(meta, meta))
      case _:SuslikProofStep.EmpRule | _:SuslikProofStep.Inconsistency =>
        Result(List(CSkip), Nil)
      case _ =>
        val stmts = value match {
          case SuslikProofStep.Write(stmt) => List(stmt.translate)
          case SuslikProofStep.Read(_, _, stmt) => List(stmt.translate)
          case SuslikProofStep.Malloc(_, _, stmt) => List(stmt.translate)
          case SuslikProofStep.Free(stmt, sz) =>
            val v = stmt.v.translate
            (0 until sz).map(i => CFree(v, i)).toList
          case SuslikProofStep.Call(_, stmt) => List(stmt.translate)
          case _ => List(Noop)
        }
        Result(stmts, List(meta))
    }
  }
}
