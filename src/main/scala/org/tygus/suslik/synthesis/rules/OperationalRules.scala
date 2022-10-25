package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{Statements, _}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.{ExtractHelper, PrependProducer, StmtProducer, SubstVarProducer}
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Operational rules emit statement that operate of flat parts of the heap.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object OperationalRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-operational"

  import Statements._

  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; x.f -> l' * P} ; {ψ ; x.f -> l' * Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  object WriteRule extends SynthesisRule with GeneratesCode with InvertibleRule {

    override def toString: Ident = "Write"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }
      def notConst: Heaplet => Boolean = {
        case PointsTo(_,_,_) => true
        case TempPointsTo(_,_,_) => true
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && !sameRhs(hl)(hr) && noGhosts(hr) && notConst(hl)

      findMatchingHeaplets(_ => true, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@PointsTo(x@Var(_), offset, e1), hr@PointsTo(_, _, e2))) =>
          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl@TempPointsTo(x@Var(_), offset, e1), hr@PointsTo(_, _, e2))) =>
          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }

  }


  /*
  TempWrite rule: create a new write from where it's possible

  Γ ; {φ ; x.f ~> l' * P} ; {ψ ; Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [Tempwrite]
  Γ ; {φ ; x.f ->/~> l * P} ; {ψ ; x.f ~> l' * Q} ---> *x.f := l' ; S

  Γ ; {φ ; P} ; {ψ ; Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [Finalwrite]
  Γ ; {φ ; x.f ~> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  // object TempWriteRule extends SynthesisRule with GeneratesCode with InvertibleRule {

  //   override def toString: Ident = "TempWrite"

  //   def apply(goal: Goal): Seq[RuleResult] = {
  //     val pre = goal.pre
  //     val post = goal.post

  //     // Heaplets have no ghosts
  //     def noGhosts: Heaplet => Boolean = {
  //       case PointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
  //       case TempPointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
  //       case _ => false
  //     }
  //     def notConst: Heaplet => Boolean = {
  //       case PointsTo(_,_,_) => true
  //       case TempPointsTo(_,_,_) => true
  //       case _ => false
  //     }

  //     // When do two heaplets match
  //     def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs_Temp(hl)(hr) && noGhosts(hr) && notConst(hl) //&& !sameRhs(hl)(hr) zytodo: avoid unnecessary write

  //     findMatchingHeaplets(_ => true, isMatch, goal.pre.sigma, goal.post.sigma) match {
  //       case None => Nil
  //       case Some((hl@PointsTo(x@Var(_), offset, e1), hr@TempPointsTo(_, _, e2))) =>
  //         val newPre = Assertion(pre.phi, (goal.pre.sigma - hl) ** hr)
  //         val newPost = Assertion(post.phi, goal.post.sigma - hr)
  //         val subGoal = goal.spawnChild(newPre, newPost)
  //         val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)
  //         List(RuleResult(List(subGoal), kont, this, goal))
  //       case Some((hl@TempPointsTo(x@Var(_), offset, e1), hr@TempPointsTo(_, _, e2))) =>
  //         val newPre = Assertion(pre.phi, (goal.pre.sigma - hl) ** hr)
  //         val newPost = Assertion(post.phi, goal.post.sigma - hr)
  //         val subGoal = goal.spawnChild(newPre, newPost)
  //         val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)
  //         List(RuleResult(List(subGoal), kont, this, goal))
  //       case Some((hl@TempPointsTo(x@Var(_), offset, e1), hr@PointsTo(_, _, e2))) => //FinalWrite
  //         val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
  //         val newPost = Assertion(post.phi, goal.post.sigma - hr)
  //         val subGoal = goal.spawnChild(newPre, newPost)
  //         val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)
  //         List(RuleResult(List(subGoal), kont, this, goal))
  //       case Some((hl, hr)) =>
  //         ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
  //         Nil
  //     }
  //   }

  // }

  object FuncCall extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "FuncCall"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts zytodo: check
      def noGhosts: Heaplet => Boolean = {
        case FuncApp(_, init :+ last) => !goal.isGhost(last.asInstanceOf[Var]) && init.forall(e => e.vars.forall(v => !(goal.isGhost(v) || goal.unAllocedTemp(v) || goal.pre.sigma.chunks.contains(TempPointsTo(v, 0, LocConst(666))))))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = callable(hl)(hr) && noGhosts(hr)

      findMatchingHeaplets(_ => true, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@PointsTo(_,_,_), hr@FuncApp(f,args))) =>
          val newPre = Assertion(pre.phi, goal.pre.sigma)
          val newPost = Assertion(post.phi, (goal.post.sigma - hr) ** hl)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Func_Call(f,args)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl@FuncApp(_,_), hr@FuncApp(f,args))) =>
          val newPre = Assertion(pre.phi, goal.pre.sigma)
          val newPost = Assertion(post.phi, (goal.post.sigma - hr) ** hl)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Func_Call(f,args)) >> ExtractHelper(goal)

          List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl@TempPointsTo(l, o, v), hr@FuncApp(f,args))) =>
          val pts = PointsTo(l, o, v)
          val newPre = Assertion(pre.phi, (goal.pre.sigma - hl) ** pts)
          val newPost = Assertion(post.phi, (goal.post.sigma - hr) ** pts)
          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Func_Call(f,args)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        // case Some((hl@SApp(_,_,_,_), hr@FuncApp(f,args))) =>
        //   val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
        //   val newPost = Assertion(post.phi, goal.post.sigma - hr)
        //   val subGoal = goal.spawnChild(newPre, newPost)
        //   val kont: StmtProducer = PrependProducer(Func_Call(f,args)) >> ExtractHelper(goal)

        //   List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }

  }

  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{φ ; x -> A * P} ; [y/A]{ψ ; Q} ---> S
      ---------------------------------------------------------------- [read]
             Γ ; {φ ; x.f -> A * P} ; {ψ ; Q} ---> let y := *x.f ; S
  */
  object ReadRule extends SynthesisRule with GeneratesCode with InvertibleRule {

    override def toString: Ident = "Read"

    def apply(goal: Goal): Seq[RuleResult] = {
      val phi = goal.pre.phi
      val sigma = goal.pre.sigma

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e) =>
           !goal.isGhost(x) && e.vars.intersect(goal.ghosts).nonEmpty
        case ConstPointsTo(x@Var(_), _, e) =>
           !goal.isGhost(x) && e.vars.intersect(goal.ghosts).nonEmpty
        case _ => false
      }

      findHeaplet(isGhostPoints, goal.pre.sigma) match {
        case None => Nil
        case Some(pts@PointsTo(x@Var(_), offset, e)) =>
          val y = freshVar(goal.vars, e.pp)
          val tpy = e.getType(goal.gamma).get
          val newPhi = phi && (y |=| e)
          val newSigma = (sigma - pts) ** PointsTo(x, offset, y)
          val subGoal = goal.spawnChild(pre = Assertion(newPhi, newSigma),
                                        gamma = goal.gamma + (y -> tpy),
                                        programVars = y :: goal.programVars)
          val kont: StmtProducer = e match {
            case a:Var => SubstVarProducer(a, y) >> PrependProducer(Load(y, tpy, x, offset)) >> ExtractHelper(goal)
            case _ => PrependProducer(Load(y, tpy, x, offset)) >> ExtractHelper(goal)
          }
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some(pts@ConstPointsTo(x@Var(_), offset, e)) =>
          val y = freshVar(goal.vars, e.pp)
          val tpy = e.getType(goal.gamma).get
          val newPhi = phi && (y |=| e)
          val newSigma = (sigma - pts) ** ConstPointsTo(x, offset, y)
          val subGoal = goal.spawnChild(pre = Assertion(newPhi, newSigma),
                                        gamma = goal.gamma + (y -> tpy),
                                        programVars = y :: goal.programVars)
          val kont: StmtProducer = e match {
            case a:Var => SubstVarProducer(a, y) >> PrependProducer(Load(y, tpy, x, offset)) >> ExtractHelper(goal)
            case _ => PrependProducer(Load(y, tpy, x, offset)) >> ExtractHelper(goal)
          }
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some(h) =>
          ruleAssert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }

  object AllocTemp extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString(): String = "AllocTemp"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post
      val temp = findTemp(goal.post.sigma)
      findTemp(goal.post.sigma) match {
        case None => Nil
        case Some((hl1@TempVar(loc,0), hl2@FuncApp(name, lst))) =>
          var varname = freshVar(goal.vars, loc.pp)
          val tp = LocType

          val temppt = TempPointsTo(varname,0,LocConst(666))
          val newPre = Assertion(pre.phi, mkSFormula(pre.sigma.chunks ++ List(temppt)))
          val newPost = Assertion(post.phi, (post.sigma - TempVar(loc, 0)) ** TempVar(loc, 1))

          val subGoal = goal.spawnChild(newPre,
                                        newPost.subst(Var(loc.pp), varname),
                                        gamma = goal.gamma + (varname -> tp),
                                        programVars = varname :: goal.programVars)
          val kont: StmtProducer = SubstVarProducer(Var(loc.pp),varname) >> PrependProducer(Malloc(varname, tp, 1)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl1@TempVar(loc,0), hl2@SApp(name, lst, tag, card))) =>
          // var (varname1,varname2) = fresh2Var(goal.vars, loc.pp)
          // val tp = LocType

          // // val temppt2 = TempPointsTo(varname2,0,LocConst(666))
          // val temppt1 = PointsTo(varname1,0,varname2)
          // val newPre = Assertion(pre.phi, mkSFormula(pre.sigma.chunks ++ List(temppt1)))
          // val newPost = Assertion(post.phi, (((post.sigma - TempVar(loc, 0) - hl2) ** TempVar(loc, 2)) ** temppt1) ** hl2.subst(Var(loc.pp), varname1))

          // val subGoal = goal.spawnChild(newPre,
          //                               newPost.subst(Var(loc.pp), varname1),
          //                               gamma = goal.gamma + (varname1 -> tp) + (varname2 -> tp),
          //                               programVars = varname1 ::(varname2 :: goal.programVars))
          // val kont: StmtProducer = SubstVarProducer(Var(loc.pp),varname1) >> PrependProducer(Malloc(varname1, tp, 1)) >> PrependProducer(Malloc(varname2, tp, 1)) >> PrependProducer(Store(varname1, 0, varname2)) >> ExtractHelper(goal)
          // List(RuleResult(List(subGoal), kont, this, goal))
          var varname = freshVar(goal.vars, loc.pp)
          val tp = LocType

          val temppt = PointsTo(varname,0,LocConst(666))
          val newPre = Assertion(pre.phi, mkSFormula(pre.sigma.chunks ++ List(temppt)))
          val newPost = Assertion(post.phi, (post.sigma - TempVar(loc, 0)) ** TempVar(loc, 1))

          val subGoal = goal.spawnChild(newPre,
                                        newPost.subst(Var(loc.pp), varname),
                                        gamma = goal.gamma + (varname -> tp),
                                        programVars = varname :: goal.programVars)
          val kont: StmtProducer = SubstVarProducer(Var(loc.pp),varname) >> PrependProducer(Malloc(varname, tp, 1)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some((hl, hr)) => 
          ruleAssert(false, s"AllocTemp Error")
          Nil
      }
    }
  }

  /*
  Alloc rule: allocate memory for an existential block

           X ∈ GV(post) / GV (pre)        y, Ai fresh
         Γ ; {φ ; y -> (A0 .. An) * P} ; {ψ ; [y/X]Q} ---> S
     -------------------------------------------------------------- [alloc]
     Γ ; {φ ; P} ; {ψ ; block(X, n) * Q} ---> let y = malloc(n); S
  */
  object AllocRule extends SynthesisRule with GeneratesCode {
    override def toString: Ident = "Alloc"

    val MallocInitVal = 666

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      def isExistBlock: Heaplet => Boolean = {
        case Block(x@Var(_), _) => goal.isExistential(x)
        case _ => false
      }

      findBlockAndChunks(isExistBlock, _ => true, goal.post.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {

      val pre = goal.pre
      val post = goal.post

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((Block(x@Var(_), sz), pts)) =>
          val y = freshVar(goal.vars, x.name)
          val tpy = LocType

          val freshChunks = for {
            off <- 0 until sz
          } yield PointsTo(y, off, IntConst(MallocInitVal))
          val freshBlock = Block(x, sz).subst(x, y)
          val newPre = Assertion(pre.phi, mkSFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))

          val subGoal = goal.spawnChild(newPre,
                                        post.subst(x, y),
                                        gamma = goal.gamma + (y -> tpy),
                                        programVars = y :: goal.programVars)
          val kont: StmtProducer = SubstVarProducer(x, y) >> PrependProducer(Malloc(y, tpy, sz)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case _ => Nil
      }
    }

  }


  object FreeTemp extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "FreeTemp"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))

      findBlockAndChunks(noGhosts, _ => true, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post

      findTempforFree(goal.post.sigma) match {
        case None => Nil
        case Some(t@TempVar(x@Var(_), 1)) =>
          val y = freshVar(goal.vars, x.pp)
          val newPost = Assertion(post.phi, post.sigma - t)

          val subGoal = goal.spawnChild(post = newPost)
          val kont: StmtProducer = PrependProducer(Free(x)) >> PrependProducer(TypeFree(y)) >> PrependProducer(Load(y, LocType, x, 0)) >> ExtractHelper(goal)

          List(RuleResult(List(subGoal), kont, this, goal))
        // case Some(t@TempVar(x@Var(_), 2)) =>
        //   val newPost = Assertion(post.phi, post.sigma - t)

        //   val subGoal = goal.spawnChild(post = newPost)
        //   val kont: StmtProducer = PrependProducer(Free(x)) >> PrependProducer(TypeFree(x)) >> ExtractHelper(goal)

        //   List(RuleResult(List(subGoal), kont, this, goal))
        case Some(_) => Nil
      }
    }

  }
  

  /*
  Free rule: free a non-ghost block from the pre-state

                     Γ ; {φ ; P} ; {ψ ; Q} ---> S     GV(li) = Ø
   ------------------------------------------------------------------------ [free]
   Γ ; {φ ; block(x, n) * x -> (l1 .. ln) * P} ; { ψ ; Q } ---> free(x); S
*/
  object FreeRule extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Free"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))

      findBlockAndChunks(noGhosts, _ => true, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), _), pts)) =>
          val toRemove = mkSFormula(pts.toList) ** h
          val newPre = Assertion(pre.phi, pre.sigma - toRemove)

          val subGoal = goal.spawnChild(newPre)
          val kont: StmtProducer = PrependProducer(Free(x)) >> ExtractHelper(goal)

          List(RuleResult(List(subGoal), kont, this, goal))
        case Some(_) => Nil
      }
    }

  }

}