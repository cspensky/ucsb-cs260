package cs260.lwnn.concrete.interpreter

import cs260.lwnn.syntax._
import cs260.lwnn.concrete.domains._
import cs260.lwnn.concrete.helpers.Helpers._

import scala.io._
import scala.util._

//——————————————————————————————————————————————————————————————————————————————
// Concrete interpreter entry point

object Concrete {
  def main( args:Array[String] ) {
    val ast = Examples.example1
    var curr_ς = initstate(ast)

    while ( !curr_ς.fin ) curr_ς = curr_ς.next
  }
}

//——————————————————————————————————————————————————————————————————————————————
// State, transition rules, and η

case class State( so:Option[Stmt], ρ:Locals, κs:Seq[Kont] ) {

  // is this a final state (i.e., the program has terminated)?
  def fin: Boolean =
    so.isEmpty && κs.isEmpty

  // we define η here so that we have access to ρ without needing to
  // pass it in as a parameter.
  def η( e:Exp ): ℤ =
    e match {
      // we deal with nondeterministic choice by randomly selecting a
      // number from the given set.
      case Nums(ns) ⇒
        ℤ( Random.shuffle(ns.toList).head )

      case x:Var ⇒
        ρ(x)

      case Binop(op, e1, e2) ⇒
        op match {
          case ⌜+⌝ ⇒ η(e1) + η(e2)
          case ⌜−⌝ ⇒ η(e1) − η(e2)
          case ⌜×⌝ ⇒ η(e1) × η(e2)
          case ⌜÷⌝ ⇒ η(e1) ÷ η(e2)
          case ⌜<⌝ ⇒ η(e1) < η(e2)
          case ⌜≤⌝ ⇒ η(e1) ≤ η(e2)
          case ⌜≈⌝ ⇒ η(e1) ≈ η(e2)
          case ⌜≠⌝ ⇒ η(e1) ≠ η(e2)
        }
    }
 

  // the state transition relation. technically this should return a
  // set of states to account for nondeterministic choice, but we'll
  // just compute a single path through the computation tree instead
  // of the entire tree.
  def next: State =
     so match {
      case Some(s) ⇒
        s match {
          // rule 1
          case Assign(x, e) ⇒
            State(None, ρ + (x → η(e)), κs)

          // rules 2,3
          case If(e, ss1, ss2) ⇒
            η(e) match {
              case ℤ(n) if n != 0 ⇒ State(None, ρ, toSK(ss1) ++ κs)
              case _ ⇒ State(None, ρ, toSK(ss2) ++ κs)
            }

          // rules 4,5
          case While(e, ss) ⇒
            η(e) match {
              case ℤ(n) if n != 0 ⇒
                State(None, ρ, (toSK(ss) :+ WhileK(e, ss)) ++ κs)
              case _ ⇒ State(None, ρ, κs)
            }

          // not in formal semantics
          case Print(e) ⇒
            println(s.id + ": " + η(e))
            State(None, ρ, κs)
        }

      case None ⇒
        κs.head match {
          // rule 6
          case StmtK(s1) ⇒
            State(Some(s1), ρ, κs.tail)

          // rules 7,8
          case wk @ WhileK(e, ss) ⇒
            η(e) match {
              case ℤ(n) if n != 0 ⇒ State(None, ρ, (toSK(ss) :+ wk) ++ κs.tail)
              case _ ⇒ State(None, ρ, κs.tail)
            }
        }
    }
}
