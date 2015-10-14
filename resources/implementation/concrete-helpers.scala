package cs260.lwnn.concrete.helpers

import cs260.lwnn.syntax._
import cs260.lwnn.concrete.domains._
import cs260.lwnn.concrete.interpreter.State

object Helpers {

  // section 2.3.2
  def initstate( p:Program ): State = {
    val ρ = Locals( (p.xs map ( (_ → ℤ(0)) ) ).toMap )
    val κs = toSK(p.ss)
    State(None, ρ, κs)
  }


  // section 2.3.3
  def toSK( ss:Seq[Stmt] ): Seq[Kont] =
    ss map ( StmtK(_) )
}
