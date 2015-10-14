package cs260.imp.abstracted.helpers

import cs260.imp.syntax._
import cs260.imp.abstracted.domains._
import cs260.imp.abstracted.interpreter.State

object Helpers {

  // section 2.3.2
  def initstate( p:Program ): State = {
    val ρ = Locals( (p.xs map ( (_ → ℤ.α(0)) )).toMap )
    val κs = toSK(p.ss)
    State(None, ρ, κs)
  }


  // section 2.3.3
  def toSK( ss:Seq[Stmt] ): Seq[Kont] =
    ss map ( StmtK(_) )
}
