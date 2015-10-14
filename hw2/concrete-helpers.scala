package cs260.lwnn.concrete.helpers

import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.concrete.domains._
import cs260.lwnn.concrete.interpreter.State

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Helper functions

object Helpers {
  def initstate(p: Program): State = {
    val ClassDefs = None
//    val locals = Locals( (p.xs map ( (_ → ℤ(0)) )).toMap )
//    val kont_stack = toSK(p.ss)

//    State(ClassDefs, None, locals, heap, kont)
    println(ast)
  }
}
