package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.util.SynStats
import org.tygus.suslik.language.Statements

class InteractiveSynthesis(config: SynConfig, stats: SynStats) extends PhasedSynthesis(config) {

  override def filterExpansions(allExpansions: Seq[Rules.RuleResult]): Seq[Rules.RuleResult] = {
    // Interactive mode: ask user to pick an expansion
    for(i <- allExpansions.indices){
      println(s"choices:${i}\n ${allExpansions(i).rule.toString()}")
      for (j <- allExpansions(i).subgoals){
        println(s"${j.pp}")
      }
    }
    val choice = if (allExpansions.length == 1) 0 else readInt
    if (0 < choice && choice <= allExpansions.size) {
      val res = allExpansions(choice - 1)
      stats.addExpansionChoice(choice)
      List(res)
    } else allExpansions
  }

}
