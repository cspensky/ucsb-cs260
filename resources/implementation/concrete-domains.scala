package cs260.lwnn.concrete.domains

import cs260.lwnn.syntax._

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
// ℤ (integer values)

case class ℤ( n:BigInt ) {
  def +( z:ℤ ) =
    ℤ( n + z.n )

  def −( z:ℤ ) =
    ℤ( n - z.n )

  def ×( z:ℤ ) =
    ℤ( n * z.n )

  def ÷( z:ℤ ) =
    ℤ( n / z.n )

  def <( z:ℤ ) =
    ℤ( if (n < z.n) 1 else 0 )

  def ≤( z:ℤ ) =
    ℤ( if (n <= z.n) 1 else 0 )

  def ≈( z:ℤ ) =
    ℤ( if (n == z.n) 1 else 0 )

  def ≠( z:ℤ ) =
    ℤ( if (n != z.n) 1 else 0 )

  override def toString =
    n.toString
}

object ℤ {
  def apply( n:Int ): ℤ = ℤ( BigInt(n) )
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
case class StmtK( s:Stmt ) extends Kont
case class WhileK( e:Exp, ss:Seq[Stmt] ) extends Kont
