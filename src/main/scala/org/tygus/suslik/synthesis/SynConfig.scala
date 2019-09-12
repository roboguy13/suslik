package org.tygus.suslik.synthesis

import org.tygus.suslik.language.PrettyPrinting

/**
  * @author Ilya Sergey
  */

case class SynConfig(
                      // Synthesis params
                      maxOpenDepth: Int         = 1,
                      maxCloseDepth: Int        = 1,
                      auxAbduction: Boolean     = false,
                      branchAbduction: Boolean  = false,
                      phased: Boolean           = true,
                      invert: Boolean           = true,
                      fail: Boolean             = true,
                      commute: Boolean          = false,
                      depthFirst: Boolean       = true,
                      // Timeout and logging
                      printStats: Boolean       = true,
                      printDerivations: Boolean = false,
                      printFailed: Boolean      = false,
                      printTags: Boolean        = false,
                      printEnv: Boolean         = false,
                      assertSuccess: Boolean    = false,
                      logToFile: Boolean        = true,
                      memoization: Boolean      = true,
                      prioImm: Boolean          = false,
                      imm: Boolean              = true,
                      timeOut: Long             = 120000,
                      // Global state
                      startTime: Long           = 0
                    ) extends PrettyPrinting {

  override def pp: String =
    ( (if (maxOpenDepth == defaultConfig.maxOpenDepth) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == defaultConfig.maxCloseDepth) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (auxAbduction == defaultConfig.auxAbduction) Nil else List(s"auxAbduction = $auxAbduction")) ++
      (if (branchAbduction == defaultConfig.branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (phased == defaultConfig.phased) Nil else List(s"phased = $phased")) ++
      (if (invert == defaultConfig.invert) Nil else List(s"invert = $invert")) ++
      (if (fail == defaultConfig.fail) Nil else List(s"fail = $fail")) ++
      (if (commute == defaultConfig.commute) Nil else List(s"commute = $commute"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)


