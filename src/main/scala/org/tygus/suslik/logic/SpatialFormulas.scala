package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.synthesis.SynthesisException
import scalaz.std.boolean

/**
  * Separation logic fragment
  */
sealed abstract class Heaplet extends PrettyPrinting with HasExpressions[Heaplet] with Ordered[Heaplet] with SepLogicUtils {

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    def collector(acc: Set[R])(h: Heaplet): Set[R] = h match {
      case PointsTo(v, offset, value) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case TempPointsTo(v, offset, value) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case ConstPointsTo(v, offset, value) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case Block(v, _) =>
        if (p(v)) acc + v.asInstanceOf[R] else acc
      case TempVar(_,_) => acc
      case SApp(_, args, _, card) =>
        args.foldLeft(acc)((a, e) => a ++ e.collect(p)) ++
          // [Cardinality] add the cardinality variable
          card.collect(p)
      case FuncApp(_, args, _) => 
        args.foldLeft(acc)((a, e) => a ++ e.collect(p))
      // case TempFuncApp(_, args) => 
      //   args.foldLeft(acc)((a, e) => a ++ e.collect(p))

    }

    collector(Set.empty)(this)
  }

  // Unify with that modulo theories:
  // produce pairs of expressions that must be equal for the this and that to be the same heaplet
  def unify(that: Heaplet): Option[ExprSubst]

  def compare(that: Heaplet): Int = this.pp.compare(that.pp)

  def resolve(gamma: Gamma, env: Environment): Option[Gamma]

  def getTag: Option[PTag] = None

  def setTag(t: PTag): Heaplet = this

  def eqModTags(other: Heaplet): Boolean = {
    this match {
      case ConstPointsTo(loc, offset, value) => ((this.setTag(PTag()) == other.setTag(PTag())) || (PointsTo(loc, offset, value).setTag(PTag()) == other.setTag(PTag())))
      case _ => this.setTag(PTag()) == other.setTag(PTag())
    }
  }

  // If this is a predicate instance, assume that from is too and copy its tag
  def copyTag(from: Heaplet): Heaplet = this match {
    case SApp(pred, args, _, card) => SApp(pred, args, from.asInstanceOf[SApp].tag, card)
    case _ => this
  }

  // Size of the heaplet (in AST nodes)
  def size: Int = this match {
    case PointsTo(loc, _, value) => 1 + loc.size + value.size
    case TempPointsTo(loc, _, value) => 1 + loc.size + value.size
    case ConstPointsTo(loc, _, value) => 1 + loc.size + value.size
    case TempVar(_, _) => 0
    case Block(loc, _) => 1 + loc.size
    case SApp(_, args, _, _) => args.map(_.size).sum
    case FuncApp(_, args, _) => args.map(_.size).sum
    // case TempFuncApp(_, args) => args.map(_.size).sum
  }

  def cost: Int = this match {
    case SApp(_, _, PTag(c, u), _) => 2 + 2*(c + u)
    case _ => 1
  }

}


/**
  * var + offset :-> value
  */
case class PointsTo(loc: Expr, offset: Int = 0, value: Expr) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma))

  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    s"$head :-> ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = loc.subst(sigma) match {
    case BinaryExpr(OpPlus, l, IntConst(off)) => PointsTo(l, offset + off, value.subst (sigma))
    case _ => PointsTo (loc.subst (sigma), offset, value.subst (sigma) )
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(LocType))
    } yield gamma2
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  // This only unifies the rhs of the points-to, because lhss are unified by a separate rule
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case PointsTo(l, o, v) if l == loc && o == offset => Some(Map(value -> v))
    case _ => None
  }
}

/**
  * var + offset :~> value
  */
case class TempPointsTo(loc: Expr, offset: Int = 0, value: Expr) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma))

  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    s"$head :~> ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = loc.subst(sigma) match {
    case BinaryExpr(OpPlus, l, IntConst(off)) => TempPointsTo(l, offset + off, value.subst (sigma))
    case _ => TempPointsTo (loc.subst (sigma), offset, value.subst (sigma) )
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(LocType))
    } yield gamma2
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  // This only unifies the rhs of the points-to, because lhss are unified by a separate rule
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case TempPointsTo(l, o, v) if l == loc && o == offset => Some(Map(value -> v))
    case _ => None
  }
}

/**
  * var + offset :=> value
  */
case class ConstPointsTo(loc: Expr, offset: Int = 0, value: Expr) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma))

  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    s"$head :=> ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = loc.subst(sigma) match {
    case BinaryExpr(OpPlus, l, IntConst(off)) => ConstPointsTo(l, offset + off, value.subst (sigma))
    case _ => ConstPointsTo (loc.subst (sigma), offset, value.subst (sigma) )
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(LocType))
    } yield gamma2
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  // This only unifies the rhs of the points-to, because lhss are unified by a separate rule
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case ConstPointsTo(l, o, v) if l == loc && o == offset => Some(Map(value -> v))
    case _ => None
  }
}

/**
  * block(var, size)
  */
case class Block(loc: Expr, sz: Int) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(loc = loc.resolveOverloading(gamma))

  override def pp: Ident = {
    s"[${loc.pp}, $sz]"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    Block(loc.subst(sigma), sz)
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = loc.resolve(gamma, Some(LocType))

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case Block(l, s) if sz == s => Some(Map(loc -> l))
    case _ => None
  }
}

/**
  * tempvar x
  */
case class TempVar(name: Expr, alloced: Int) extends Heaplet {
  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(name = name.resolveOverloading(gamma))

  override def pp: Ident = s"Tempvar (${name.pp}, $alloced)"

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    TempVar(name.subst(sigma),alloced)
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = Some(gamma)

  override def compare(that: Heaplet): Int = super.compare(that)
  
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case TempVar(n, _)  => Some(Map(name -> n))
    case _ => None
  }
}

/**
  * func(f(args..))
  */
case class FuncApp(fname: Ident, args: Seq[Expr], offset: Int = 0) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(args = args.map(_.resolveOverloading(gamma)))

  override def pp: Ident = {
    s"[Func, $fname(${args.map(_.pp)}), + $offset]"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    val newArgs = args.map(_.subst(sigma))
    this.copy(args = newArgs)
  }

  //todo: type checking
  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = Some(gamma)

  override def compare(that: Heaplet) = super.compare(that)

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case FuncApp(n, a, o) if (n == fname && o == offset) => Some(args.zip(a).toMap)
    case _ => None
  }
}


case class PTag(calls: Int = 0, unrolls: Int = 0) extends PrettyPrinting {
  override def pp: String = this match {
    case PTag(0, 0) => "" // Default tag
    case _ => s"[$calls,$unrolls]"
  }
}

/**
  *
  * @card is a cardinality of a current call.
  *
  *       Predicate application
  */
case class SApp(pred: Ident, args: Seq[Expr], tag: PTag, card: Expr) extends Heaplet with HasAssertions[SFormula] {

  def visitAssertions(f: Expr => Expr, g: Heaplet => Seq[Heaplet]): SFormula =
    SFormula(g(this).to[List])

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(args = args.map(_.resolveOverloading(gamma)))

  override def pp: String = {
    def ppCard(e: Expr) = s"<${e.pp}>"

    s"$pred(${args.map(_.pp).mkString(", ")})${ppCard(card)}${tag.pp}"
  }


  override def compare(that: Heaplet): Int = that match {
    case SApp(pred1, args1, tag, card) =>
      val c1 = this.pred.compareTo(pred1)
      val c2 = this.args.toString.compareTo(args1.toString)
      if (c1 != 0) return c1
      if (c2 != 0) return c2
      0
    case _ => super.compare(that)
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    val newArgs = args.map(_.subst(sigma))
    // [Cardinality] adjust cardinality
    val newCard = card.subst(sigma)
    this.copy(args = newArgs, card = newCard)
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains pred)) {
      throw SynthesisException(s"predicate $pred is undefined")
    }

    val gamma1 = card.resolve(gamma, Some(CardType))
    val formals = env.predicates(pred).params

    if (formals.length == args.length) {
      (formals, args).zipped.foldLeft[Option[Gamma]](gamma1) { case (go, (formal, actual)) => go match {
        case None => None
        case Some(g) => actual.resolve(g, Some(formal._2))
      }
      }
    } else None
  }

  override def freeVars: Set[Var] = args.flatMap(_.freeVars).toSet

  override def getTag: Option[PTag] = Some(tag)

  override def setTag(t: PTag): Heaplet = this.copy(tag = t)

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case SApp(p, as, _, c) if pred == p => Some((card :: args.toList).zip(c :: as.toList).toMap)
    case _ => None
  }
}


case class SFormula(chunks: List[Heaplet]) extends PrettyPrinting with HasExpressions[SFormula] with HasAssertions[SFormula] {

  def visitAssertions(f: Expr => Expr, g: Heaplet => Seq[Heaplet]): SFormula =
    SFormula(chunks.flatMap(g))

  def resolveOverloading(gamma: Gamma): SFormula = {
    this.copy(chunks = chunks.map(_.resolveOverloading(gamma)))
  }

  override def pp: Ident = if (chunks.isEmpty) "emp" else {
    def pt(l: List[Heaplet]) = l.map(_.pp).sortBy(x => x)
    List(temps, helper_funcs, tptss, cptss ,ptss, apps, blocks).flatMap(pt).mkString(" ** ")
  }

  def blocks: List[Block] = for (b@Block(_, _) <- chunks) yield b

  def apps: List[SApp] = for (b@SApp(_, _, _, _) <- chunks) yield b

  def ptss: List[PointsTo] = for (b@PointsTo(_, _, _) <- chunks) yield b

  def cptss: List[ConstPointsTo] = for (b@ConstPointsTo(_, _, _) <- chunks) yield b

  def tptss: List[TempPointsTo] = for (b@TempPointsTo(_, _, _) <- chunks) yield b

  def helper_funcs :List[FuncApp] = for (b@FuncApp(_,_,_) <- chunks) yield b

  def temps: List[TempVar] = for (b@TempVar(_,_) <- chunks) yield b

  def tempvars: List[Var] = for (b@TempVar(loc, 0) <- chunks) yield loc.asInstanceOf[Var]

  // def temp_helper_funcs :List[TempFuncApp] = for (b@TempFuncApp(_,_) <- chunks) yield b

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)))

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collect(p))
  }

  def setSAppTags(t: PTag): SFormula = SFormula(chunks.map(h => h.setTag(t)))

  def callTags: List[Int] = chunks.flatMap(_.getTag).map(_.calls)

  def isEmp: Boolean = chunks.isEmpty

  def block_size (expr: Expr) = blocks find { case Block(loc,_) if loc == expr => true case _ => false } map (v => v.sz)

  // Add h to chunks (multiset semantics)
  def **(h: Heaplet): SFormula = SFormula(h :: chunks)

  // Add all chunks from other (multiset semantics)
  def **(other: SFormula): SFormula = SFormula(chunks ++ other.chunks)

  // Remove h from this formula (multiset semantics)
  def -(h: Heaplet): SFormula = SFormula(chunks.diff(List(h)))

  // Remove all chunks present in other (multiset semantics)
  def -(other: SFormula): SFormula = SFormula(chunks.diff(other.chunks))

  // Add chunks from other (set semantics)
  def +(other: SFormula): SFormula = SFormula((chunks ++ other.chunks).distinct)

  def disjoint(other: SFormula): Boolean = chunks.intersect(other.chunks).isEmpty

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    chunks.foldLeft[Option[Map[Var, SSLType]]](Some(gamma))((go, h) => go match {
      case None => None
      case Some(g) => h.resolve(g, env)
    })
  }

  def replace(what: SFormula, replacement: SFormula): SFormula = {
    (this - what) ** replacement
  }

  lazy val profile: SProfile = {
    val appProfile = apps.groupBy(_.pred).mapValues(_.length)
    val blockProfile = blocks.groupBy(_.sz).mapValues(_.length)
    val tempptsProfile = List.concat(ptss, cptss.map(_ match {case ConstPointsTo(a,b,c) => PointsTo(a,b,c)}), tptss.map(_ match {case TempPointsTo(a,b,c) => PointsTo(a,b,c)}), helper_funcs.map(_ match {case FuncApp(_,init :+ last, o) => PointsTo(last,o,IntConst(0))})).groupBy(_.offset).mapValues(_.length)
    if(tempptsProfile.contains(0)){
      val zeronum = tempptsProfile(0)
      val ptsProfile = tempptsProfile - (0) + (0 -> (zeronum-tempvars.size))
      SProfile(appProfile, blockProfile, ptsProfile)
    }
    else
      SProfile(appProfile, blockProfile, tempptsProfile)
  }
  lazy val tempprofile: SProfile = {
    val appProfile = apps.groupBy(_.pred).mapValues(_.length)
    val blockProfile = blocks.groupBy(_.sz).mapValues(_.length)
    val ptsProfile = List.concat(ptss, cptss.map(_ match {case ConstPointsTo(a,b,c) => PointsTo(a,b,c)}), tptss.map(_ match {case TempPointsTo(a,b,c) => PointsTo(a,b,c)}), helper_funcs.map(_ match {case FuncApp(_,init :+ last, o) => PointsTo(last,o,IntConst(0))})).groupBy(_.offset).mapValues(_.length)
    SProfile(appProfile, blockProfile, ptsProfile)
  }

  override def freeVars: Set[Var] = chunks.flatMap(_.freeVars).toSet


  // Size of the formula (in AST nodes)
  def size: Int = chunks.map(_.size).sum

  def cost: Int = chunks.map(_.cost).sum

  //  def cost: Int = chunks.foldLeft(0)((m, c) => m.max(c.cost))
}

/**
  * Profile of a spatial formula (contains properties that cannot be changed by unification)
  * @param apps how maybe applications there are of each predicate?
  * @param blocks how many blocks there are of each size?
  * @param ptss how many points-to chunks there are with each offset?
  */
case class SProfile(apps: Map[Ident, Int], blocks: Map[Int, Int], ptss: Map[Int, Int])


