package cs260.imp.abstracted.interpreter

/*
 WARNING: this code compiles successfully, but has not been thoroughly
          tested for correctness
*/

import cs260.imp.syntax._
import cs260.imp.abstracted.domains._
import cs260.imp.abstracted.helpers.Helpers._

import scala.io._
import scala.util._

//——————————————————————————————————————————————————————————————————————————————
// Abstract interpreter entry point

object Abstract {
  def main( args:Array[String] ) {
    val ast = Examples.example1

    // worklist of states to be processed
    var work = Set[State]( initstate(ast) )

    // remember set of states we've encountered
    var memo = Set[State]()

    // worklist algorithm to compute fixpoint
    while ( work.nonEmpty ) {
      work = work.flatMap( _.next ).flatMap( ς ⇒
        if ( ς.fin )
          // if this is a final state, we don't need to do
          // anything
          None

        else if ( ς.so.isEmpty )
          // we'll skip memoizing intermediate states (i.e.,
          // states with no statement) just to save space; go
          // ahead and put such states on the worklist
          Some(ς)

        else if ( !memo(ς) ) {
          // if the state does have a statement, and we have not
          // seen it before, memoize it and put it on the worklist
          memo = memo + ς
          Some(ς)
        }

        else
          // the state does have a statement, but we've seen it
          // before so we don't need to process it again
          None
      )
    }
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
      case Nums(ns) ⇒
        ℤ.α(ns)

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
 
  // the state transition relation. it returns a set of states to
  // account for nondeterministic choice.
  def next: Set[State] =
    so match {
      case Some(s) ⇒
        s match {
          // rule 1
          case Assign(x, e) ⇒
            η(e) match {
              case z if z.vs.nonEmpty ⇒
                Set( copy(so = None, ρ = ρ + (x → z)) )
              case _ ⇒ Set()
            }

          // rules 2,3
          case If(e, ss1, ss2) ⇒
            η(e) match {
              case z if z.vs.nonEmpty ⇒
                z.vs flatMap (_ match {
                  case POS | NEG ⇒ Some( copy(so = None, κs = toSK(ss1) ++ κs) )
                  case ZERO ⇒ Some( copy(so = None, κs = toSK(ss2) ++ κs) )
                })
              case _ ⇒ Set()
            }

          // rules 4,5
          case While(e, ss) ⇒
            η(e) match {
              case z if z.vs.nonEmpty ⇒
                z.vs flatMap (_ match {
                  case POS | NEG ⇒ Some( copy(so = None, κs = (toSK(ss) :+ WhileK(e, ss)) ++ κs) )
                  case ZERO ⇒ Some( copy(so = None) )
                })
              case _ ⇒ Set()
            }

          // not in formal semantics
          case Print(e) ⇒
            Set( copy(so = None) )
        }

      case None ⇒
        κs.head match {
          // rule 6
          case StmtK(s1) ⇒
            Set( copy(so = Some(s1), κs = κs.tail) )

          // rules 7,8
          case WhileK(e, ss) ⇒
            η(e) match {
              case z if z.vs.nonEmpty ⇒
                z.vs flatMap (_ match {
                  case POS | NEG ⇒ Some( copy(so = None, κs = toSK(ss) ++ κs) )
                  case ZERO ⇒ Some( copy(so = None, κs = κs.tail) )
                })
              case _ ⇒ Set()
            }
        }
    }
}
