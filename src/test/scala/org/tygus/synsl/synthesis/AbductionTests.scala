package org.tygus.synsl.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.synsl.synthesis.instances.PhasedSynthesis

/**
  * @author Ilya Sergey
  */

class AbductionTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
      synthesizeFromSpec(testName, in, out)
    }

  describe("SL-based synthesizer with abductor for hypothesis preconditions") {
    runAllTestsFromDir("abduct")
  }

}