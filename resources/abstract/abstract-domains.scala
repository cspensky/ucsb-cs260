package cs260.imp.abstracted.domains

import cs260.imp.syntax._

//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals( x2n:Map[Var, ℤ] ) {
  def apply( x:Var ): ℤ =
    x2n(x)

  def +( xv:(Var, ℤ) ): Locals = {
    assert( x2n contains xv._1 )
    Locals( x2n + xv )
  }
}

//——————————————————————————————————————————————————————————————————————————————
// ℤ (abstract integer values)

sealed abstract class AInt {
  def +( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS)
    case   (POS, NEG) ⇒ Set(POS, NEG, ZERO)
    case  (POS, ZERO) ⇒ Set(POS)
    case   (NEG, POS) ⇒ Set(POS, NEG, ZERO)
    case   (NEG, NEG) ⇒ Set(NEG)
    case  (NEG, ZERO) ⇒ Set(NEG)
    case  (ZERO, POS) ⇒ Set(POS)
    case  (ZERO, NEG) ⇒ Set(NEG)
    case (ZERO, ZERO) ⇒ Set(ZERO)
  }

  def −( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS, NEG, ZERO)
    case   (POS, NEG) ⇒ Set(POS)
    case  (POS, ZERO) ⇒ Set(POS)
    case   (NEG, POS) ⇒ Set(NEG)
    case   (NEG, NEG) ⇒ Set(POS, NEG, ZERO)
    case  (NEG, ZERO) ⇒ Set(NEG)
    case  (ZERO, POS) ⇒ Set(NEG)
    case  (ZERO, NEG) ⇒ Set(POS)
    case (ZERO, ZERO) ⇒ Set(ZERO)
  }

  def ×( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS)
    case   (POS, NEG) ⇒ Set(NEG)
    case  (POS, ZERO) ⇒ Set(ZERO)
    case   (NEG, POS) ⇒ Set(NEG)
    case   (NEG, NEG) ⇒ Set(POS)
    case  (NEG, ZERO) ⇒ Set(ZERO)
    case  (ZERO, POS) ⇒ Set(ZERO)
    case  (ZERO, NEG) ⇒ Set(ZERO)
    case (ZERO, ZERO) ⇒ Set(ZERO)
  }

  def ÷( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS)
    case   (POS, NEG) ⇒ Set(NEG)
    case  (POS, ZERO) ⇒ Set()
    case   (NEG, POS) ⇒ Set(NEG)
    case   (NEG, NEG) ⇒ Set(POS)
    case  (NEG, ZERO) ⇒ Set()
    case  (ZERO, POS) ⇒ Set(ZERO)
    case  (ZERO, NEG) ⇒ Set(ZERO)
    case (ZERO, ZERO) ⇒ Set()
  }

  def <( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS, ZERO)
    case   (POS, NEG) ⇒ Set(ZERO)
    case  (POS, ZERO) ⇒ Set(ZERO)
    case   (NEG, POS) ⇒ Set(POS)
    case   (NEG, NEG) ⇒ Set(POS, ZERO)
    case  (NEG, ZERO) ⇒ Set(POS)
    case  (ZERO, POS) ⇒ Set(POS)
    case  (ZERO, NEG) ⇒ Set(ZERO)
    case (ZERO, ZERO) ⇒ Set(ZERO)
  }

  def ≤( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS, ZERO)
    case   (POS, NEG) ⇒ Set(ZERO)
    case  (POS, ZERO) ⇒ Set(ZERO)
    case   (NEG, POS) ⇒ Set(POS)
    case   (NEG, NEG) ⇒ Set(POS, ZERO)
    case  (NEG, ZERO) ⇒ Set(POS)
    case  (ZERO, POS) ⇒ Set(POS)
    case  (ZERO, NEG) ⇒ Set(ZERO)
    case (ZERO, ZERO) ⇒ Set(POS)
  }

  def ≈( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS, ZERO)
    case   (POS, NEG) ⇒ Set(ZERO)
    case  (POS, ZERO) ⇒ Set(ZERO)
    case   (NEG, POS) ⇒ Set(ZERO)
    case   (NEG, NEG) ⇒ Set(POS, ZERO)
    case  (NEG, ZERO) ⇒ Set(ZERO)
    case  (ZERO, POS) ⇒ Set(ZERO)
    case  (ZERO, NEG) ⇒ Set(ZERO)
    case (ZERO, ZERO) ⇒ Set(POS)
  }

  def ≠( a:AInt ): Set[AInt] = (this, a) match {
    case   (POS, POS) ⇒ Set(POS, ZERO)
    case   (POS, NEG) ⇒ Set(POS)
    case  (POS, ZERO) ⇒ Set(POS)
    case   (NEG, POS) ⇒ Set(POS)
    case   (NEG, NEG) ⇒ Set(POS, ZERO)
    case  (NEG, ZERO) ⇒ Set(POS)
    case  (ZERO, POS) ⇒ Set(POS)
    case  (ZERO, NEG) ⇒ Set(POS)
    case (ZERO, ZERO) ⇒ Set(ZERO)
  }
}

case object POS extends AInt
case object NEG extends AInt
case object ZERO extends AInt

case class ℤ( vs: Set[AInt] ) {
  def +( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x + y).flatten )

  def −( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x − y).flatten )

  def ×( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x × y).flatten )

  def ÷( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x ÷ y).flatten )

  def <( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x < y).flatten )

  def ≤( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x ≤ y).flatten )

  def ≈( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x ≈ y).flatten )

  def ≠( z:ℤ ) =
    ℤ( (for ( x ← vs ; y ← z.vs ) yield x ≠ y).flatten )

  override def toString =
    "{ " + vs.mkString(", ") + " }"
}

object ℤ {
  def α( ns: Set[BigInt] ): ℤ =
    ℤ( ns map (n ⇒ if (n < 0) NEG else if (n == 0) ZERO else POS) )

  def α( n: BigInt ): ℤ =
    α(Set(n))
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
case class StmtK( s:Stmt ) extends Kont
case class WhileK( e:Exp, ss:Seq[Stmt] ) extends Kont
