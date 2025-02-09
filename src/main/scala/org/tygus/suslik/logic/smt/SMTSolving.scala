package org.tygus.suslik.logic.smt

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, QuantifiedTerm, TypedTerm, VarTerm}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.report.LazyTiming

import scala.util.Success

/**
  * @author Ilya Sergey
  */

object SMTSolving extends Core
  with IntegerArithmetics
  with QuantifiedTerm
  with Resources
  with Commands
  with PureLogicUtils
  with ArrayExBool
  with ArrayExOperators
  with LazyTiming {

  val defaultSolver = "Z3" // choices: "Z3", "Z3 <= 4.7.x", "CVC4"

  def solverName = if (defaultSolver == "Z3" || defaultSolver == "Z3 <= 4.7.x")
    "Z3" else "CVC4"

  override val watchName = "SMTSolving"

  implicit private var solverObject: SMTSolver = null

  {
    disableLogging()

    // create solver and assert axioms
    // TODO: destroy solver when we're done
    solverObject = new SMTSolver(solverName, new SMTInit())
    for (cmd <- prelude) {
      solverObject.eval(Raw(cmd))
    }

    // Warm-up the SMT solver on start-up to avoid future delays
    for (i <- 1 to 5; j <- 1 to 2; k <- 1 to 3) {
      checkSat(convertBoolExpr(BinaryExpr(OpLeq, IntConst(i), BinaryExpr(OpPlus, IntConst(j), IntConst(k)))))
    }
  }

  /** Communication with the solver  */

  trait SetTerm
  trait IntervalTerm

  type SMTBoolTerm = TypedTerm[BoolTerm, Term]
  type SMTIntTerm = TypedTerm[IntTerm, Term]
  type SMTSetTerm = TypedTerm[SetTerm, Term]
  type SMTIntervalTerm = TypedTerm[IntervalTerm, Term]

  def setSort: Sort = SortId(SymbolId(SSymbol("SetInt")))

  def emptySetSymbol = SimpleQId(SymbolId(SSymbol("empty")))

  // def iteSymbol = IfThenElseTerm

  def setInsertSymbol = SimpleQId(SymbolId(SSymbol("insert")))

  def setUnionSymbol = SimpleQId(SymbolId(SSymbol("union")))

  def setDiffSymbol = SimpleQId(SymbolId(SSymbol("difference")))

  def setMemberSymbol = SimpleQId(SymbolId(SSymbol("member")))

  def setSubsetSymbol = SimpleQId(SymbolId(SSymbol("subset")))

  def setIntersectSymbol = SimpleQId(SymbolId(SSymbol("intersect")))

  def emptySetTerm: Term = QIdTerm(emptySetSymbol)

  def intervalSort: Sort = SortId(SymbolId(SSymbol("Interval")))

  def intervalConstructorSymbol = SimpleQId(SymbolId(SSymbol("interval")))

  def intervalInsertSymbol = SimpleQId(SymbolId(SSymbol("iinsert")))

  def intervalUnionSymbol = SimpleQId(SymbolId(SSymbol("iunion")))

  def intervalMemberSymbol = SimpleQId(SymbolId(SSymbol("imember")))

  def intervalSubsetSymbol = SimpleQId(SymbolId(SSymbol("isubset")))

  def intervalEqSymbol = SimpleQId(SymbolId(SSymbol("ieq")))

  def intervalLowerSymbol = SimpleQId(SymbolId(SSymbol("lower")))

  def intervalUpperSymbol = SimpleQId(SymbolId(SSymbol("upper")))

  def intervalPrelude: List[String] = List(
    "(define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))",
    "(define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))",
    "(define-fun iempty ((s Interval)) Bool (> (lower s) (upper s)))",
    "(define-fun ieq ((s1 Interval) (s2 Interval)) Bool (or (and (iempty s1) (iempty s2)) (and (= (lower s1) (lower s2)) (= (upper s1) (upper s2)))))",
    "(define-fun imember ((x Int) (s Interval)) Bool (and (<= (lower s) x) (<= x (upper s))))",
    "(define-fun isubset ((s1 Interval) (s2 Interval)) Bool (or (iempty s1) (and (<= (lower s2) (lower s1)) (<= (upper s1) (upper s2)))))",
    "(define-fun iinsert ((x Int) (s Interval)) Interval (ite (iempty s) (interval x x) (interval (min x (lower s)) (max x (upper s)))))",
    "(define-fun iunion ((s1 Interval) (s2 Interval)) Interval (ite (iempty s1) s2 (iinsert (lower s1) (iinsert (upper s1) s2))))",
  )

  // Commands to be executed before solving starts
  def prelude = if (defaultSolver == "CVC4") {
    List(
      "(set-logic ALL_SUPPORTED)",
      "(define-sort SetInt () (Set Int))",
      "(define-fun empty () SetInt (as emptyset (Set Int)))",
      "(declare-datatypes ((Interval 0)) (((interval (lower Int) (upper Int)))))"
    ) ++ intervalPrelude
  } else if (defaultSolver == "Z3") {
    List(
      "(define-sort SetInt () (Array Int Bool))",
      "(define-fun empty () SetInt ((as const SetInt) false))",
      "(define-fun member ((x Int) (s SetInt)) Bool (select s x))",
      "(define-fun insert ((x Int) (s SetInt)) SetInt (store s x true))",
      "(define-fun intersect ((s1 SetInt) (s2 SetInt)) SetInt (intersection s1 s2))",
      "(define-fun subset ((s1 SetInt) (s2 SetInt)) Bool (= s1 (intersect s1 s2)))",
      "(declare-fun andNot (Bool Bool) Bool)",
      "(assert (forall ((b1 Bool) (b2 Bool)) (= (andNot b1 b2) (and b1 (not b2)))))",
      "(define-fun difference ((s1 SetInt) (s2 SetInt)) SetInt ((_ map andNot) s1 s2))",
      "(declare-datatypes () ((Interval (interval (lower Int) (upper Int)))))"
    ) ++ intervalPrelude
  } else if (defaultSolver == "Z3 <= 4.7.x") {
    // In Z3 4.7.x and below, difference is built in and intersection is called intersect
    List(
      "(define-sort SetInt () (Array Int Bool))",
      "(define-fun empty () SetInt ((as const SetInt) false))",
      "(define-fun member ((x Int) (s SetInt)) Bool (select s x))",
      "(define-fun insert ((x Int) (s SetInt)) SetInt (store s x true))",
      "(declare-datatypes () ((Interval (interval (lower Int) (upper Int)))))"
    ) ++ intervalPrelude
  } else throw SolverUnsupportedExpr(defaultSolver)

  private def checkSat(term: SMTBoolTerm): Boolean =
    this.synchronized {
      timed {
        push(1)
        val res = isSat(term)
        pop(1)
        res != Success(UnSat()) // Unknown counts as SAT
      }
    }

  /** Translating expression into SMT  */

  case class SMTUnsupportedExpr(e: Expr)
    extends Exception(s"Cannot convert expression ${e.pp} to an equivalent SMT representation.")

  case class SolverUnsupportedExpr(solver: String)
    extends Exception(s"Unsupported solver: $solver.")

  private def convertSetExpr(e: Expr): SMTSetTerm = e match {
    case Var(name) => new VarTerm[SetTerm](name, setSort)
    case SetLiteral(elems) => {
      val emptyTerm = new TypedTerm[SetTerm, Term](Set.empty, emptySetTerm)
      makeSetInsert(emptyTerm, elems)
    }
    // Special case for unions with a literal
    case BinaryExpr(OpUnion, SetLiteral(elems1), SetLiteral(elems2)) => {
      val emptyTerm = new TypedTerm[SetTerm, Term](Set.empty, emptySetTerm)
      makeSetInsert(emptyTerm, elems1 ++ elems2)
    }
    case BinaryExpr(OpUnion, left, SetLiteral(elems)) => {
      val l = convertSetExpr(left)
      makeSetInsert(l, elems)
    }
    case BinaryExpr(OpUnion, SetLiteral(elems), right) => {
      val r = convertSetExpr(right)
      makeSetInsert(r, elems)
    }
    case BinaryExpr(OpUnion, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setUnionSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpDiff, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setDiffSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpIntersect, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setIntersectSymbol, List(l.termDef, r.termDef)))
    }
    case IfThenElse(cond, left, right) => {
      val c = convertBoolExpr(cond)
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      c.ite(l, r)
      // new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(iteSymbol, List(l.termDef, r.termDef)))
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def makeSetInsert(setTerm: SMTSetTerm, elems: List[Expr]): SMTSetTerm = {
    if (elems.isEmpty) {
      setTerm
    } else {
      val eTerms: List[SMTIntTerm] = elems.map(convertIntExpr)
      if (defaultSolver == "CVC4") {
        new TypedTerm[SetTerm, Term](setTerm.typeDefs ++ eTerms.flatMap(_.typeDefs).toSet,
          QIdAndTermsTerm(setInsertSymbol, (eTerms :+ setTerm).map(_.termDef)))
      } else if (defaultSolver == "Z3" || defaultSolver == "Z3 <= 4.7.x") {
        def makeInsertOne(setTerm: SMTSetTerm, eTerm: SMTIntTerm): SMTSetTerm =
          new TypedTerm[SetTerm, Term](setTerm.typeDefs ++ eTerm.typeDefs,
            QIdAndTermsTerm(setInsertSymbol, List(eTerm.termDef, setTerm.termDef)))

        eTerms.foldLeft(setTerm)(makeInsertOne)
      } else throw SolverUnsupportedExpr(defaultSolver)
    }
  }

  private def convertIntervalExpr(e: Expr): SMTIntervalTerm = e match {
    case Var(name) => new VarTerm[IntervalTerm](name, intervalSort)
    case BinaryExpr(OpRange, l, u) => {
      val lTerm = convertIntExpr(l)
      val uTerm = convertIntExpr(u)
      new TypedTerm[IntervalTerm, Term](lTerm.typeDefs ++ uTerm.typeDefs,
        QIdAndTermsTerm(intervalConstructorSymbol, List(lTerm.termDef, uTerm.termDef)))
    }
    // Special case for unions with a literal
    case BinaryExpr(OpIntervalUnion, BinaryExpr(OpRange, l, u), e) if l == u => {
      val lTerm = convertIntExpr(l)
      val eTerm = convertIntervalExpr(e)
      new TypedTerm[IntervalTerm, Term](lTerm.typeDefs ++ eTerm.typeDefs,
        QIdAndTermsTerm(intervalInsertSymbol, List(lTerm.termDef, eTerm.termDef)))
    }
    case BinaryExpr(OpIntervalUnion, e, r@BinaryExpr(OpRange, l, u)) if l == u =>
      convertIntervalExpr(BinaryExpr(OpIntervalUnion, r, e))
    case BinaryExpr(OpIntervalUnion, left, right) => {
      val lTerm = convertIntervalExpr(left)
      val rTerm = convertIntervalExpr(right)
      new TypedTerm[IntervalTerm, Term](lTerm.typeDefs ++ rTerm.typeDefs,
        QIdAndTermsTerm(intervalUnionSymbol, List(lTerm.termDef, rTerm.termDef)))
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def convertBoolExpr(e: Expr): SMTBoolTerm = e match {
    case Var(name) => Bools(name)
    case BoolConst(true) => True()
    case BoolConst(false) => False()
    case UnaryExpr(OpNot, e1) => !convertBoolExpr(e1)
    case BinaryExpr(OpAnd, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l & r
    }
    case BinaryExpr(OpOr, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l | r
    }
    case BinaryExpr(OpEq, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l === r
    }
    case BinaryExpr(OpBoolEq, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l === r
    }
    case BinaryExpr(OpLeq, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l <= r
    }
    case BinaryExpr(OpLt, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l < r
    }
    case BinaryExpr(OpIn, left, right) => {
      val l = convertIntExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(setMemberSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpSetEq, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      l === r
    }
    case BinaryExpr(OpSubset, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(setSubsetSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpIntervalIn, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntervalExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(intervalMemberSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpIntervalEq, left, right) => {
      val l = convertIntervalExpr(left)
      val r = convertIntervalExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(intervalEqSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpSubinterval, left, right) => {
      val l = convertIntervalExpr(left)
      val r = convertIntervalExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(intervalSubsetSymbol, List(l.termDef, r.termDef)))
    }
    case Unknown(_, _, _) => True() // Treat unknown predicates as true
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def convertIntExpr(e: Expr): SMTIntTerm = e match {
    case Var(name) => Ints(name)
    case IntConst(c) => Ints(c)
    case LocConst(c) => Ints(c)
    case UnaryExpr(OpLower, e) => {
      val s = convertIntervalExpr(e)
      new TypedTerm[IntTerm, Term](s.typeDefs, QIdAndTermsTerm(intervalLowerSymbol, List(s.termDef)))
    }
    case UnaryExpr(OpUpper, e) => {
      val s = convertIntervalExpr(e)
      new TypedTerm[IntTerm, Term](s.typeDefs, QIdAndTermsTerm(intervalUpperSymbol, List(s.termDef)))
    }
    case BinaryExpr(op, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      op match {
        case OpPlus => l + r
        case OpMinus => l - r
        case OpMultiply => l * r
        case OpMod => l % r
        case _ => throw SMTUnsupportedExpr(e)
      }
    }
    case IfThenElse(cond, left, right) => {
      val c = convertBoolExpr(cond)
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      c.ite(l, r)
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  /** Caching */

  private val cache = collection.mutable.Map[Expr, Boolean]()

  def cacheSize: Int = cache.size

  // Call this before synthesizing a new function
  def init(): Unit = {
    // Warm up solver
    cache.clear()
  }

  /** External interface */

  // Check if phi is satisfiable; all vars are implicitly existentially quantified
  def sat(phi: Expr): Boolean = {
    cache.getOrElseUpdate(phi, checkSat(convertBoolExpr(phi)))
  }

  // Check if phi is valid; all vars are implicitly universally quantified
  def valid(phi: Expr): Boolean = {
    !sat(phi.not)
  }

}
