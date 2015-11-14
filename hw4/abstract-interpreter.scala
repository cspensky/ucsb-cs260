import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.abstracted.domains._
import cs260.lwnn.abstracted.helpers.Helpers._

import scala.util._
import scala.collection.mutable.{ Set ⇒ MSet, Map ⇒ MMap }

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Abstract interpreter entry point

object Abstract {
  import cs260.lwnn.abstracted.interpreter.State

  val DEBUG = false

  def main( args:Array[String] ) {
    Parse.getAST( scala.io.Source.fromFile(args(0)).mkString ) match {
      // parsing error: program is not well-formed
      case Left(err) ⇒ println(err)

      // successfully parsed: program is well-formed
      case Right((classTable, ast:Program)) ⇒
        try {
          // throws Illtyped exception if program is not well-typed
          Typechecker.typecheck(ast, classTable)

          // program is well-formed and well-typed; ready to compute
          // fixpoint for collecting semantics
          //
          // NOTE: this version computes the MOP result, i.e., there
          //       is no widening.

          // worklist
          var work = Set[State]( initstate(ast) )

          // remember set
          val memo = MSet[State]()

          // compute fixpoint
          while ( work.nonEmpty ) {
            work = work.flatMap( _.next ).flatMap( ς ⇒
              if ( ς.fin ) {
                // if this is a final state, we don't need to do
                // anything
                if (DEBUG) println("final state " + ς)
                None
              } else if ( ς.so.isEmpty && !ς.κs.head.isInstanceOf[FinK] ) {
                // we'll skip memoizing intermediate states (i.e.,
                // states with no statement) just to save space; go
                // ahead and put such states on the worklist
                if (DEBUG) println("new state FinK " + ς)
                Some(ς)
              } else if ( !memo(ς) ) {
                // if the state does have a statement, and we have not
                // seen it before, memoize it and put it on the
                // worklist
                if (DEBUG) println("new state " + ς)
                memo += ς
                Some(ς)

              }
              else {
                // the state does have a statement, but we've seen it
                // before so we don't need to process it again
                None
              }
            )
          }

          // output abstract values for Print statements: for each
          // Print, join all values for the printed expresion together
          // and output the result. Do this in ascending order of the
          // Print statements' node ids.
          val out = MMap[Int, Value]()
          memo foreach {
            case ς @ State(Some(print @ Print(e)), _, _, _) ⇒
              out get print.id match {
                case None ⇒
                  out(print.id) = ς.η(e)

                case Some(v) ⇒
                  out(print.id) = ς.η(e) ⊔ v
              }

            case _ ⇒ ()
          }
          out.toSeq.sortBy(_._1).foreach {
            case (id, v) ⇒ println(id + ": " + v)
          }
        }
        catch {
          // program is not well-typed
          case i:Illtyped ⇒ println(s"TypeError: ${i.msg}")
        }

      case _ ⇒
        sys.error("undefined behavior")
    }
  }
}

package cs260.lwnn.abstracted.interpreter {

//——————————————————————————————————————————————————————————————————————————————
// State, transition rules, and η
//
// Note: Any undefined behavior of the program (i.e., that would
// result in a sys.error in the concrete semantics) should result in
// next returning an empty set of States in the abstract version. This
// includes if η returns a ⊥ value.

case class State(/* θ is a global now */ so: Option[Stmt], ρ: Locals, σ: Heap, κs: Seq[Kont]) {
  val DEBUG = false

  // is this a final state (i.e., the program has terminated)?
  def fin: Boolean =
    so.isEmpty && κs.isEmpty

  // we define η here so that we have access to ρ and σ without
  // needing to pass them in as parameters.
  def η(e: Exp): Value =
    e match {
      // we deal with nondeterministic choice by randomly selecting a
      // number from the given set.
      case Nums(ns) =>
        if (DEBUG) println("Num "+ns+" "+ℤ.α(ns))
        ℤ.α(ns)

      case Bools(bs) =>
        if (DEBUG) println("Bool "+bs+" "+Bool.α(bs))
        Bool.α(bs)

      case Strs(ss) =>
        if (DEBUG) println("Str "+ss+" "+Str.α(ss))
        Str.α(ss)

      case Nulls() =>
        if (DEBUG) println("Null ")
        new Reference(Set.empty[Address], true)

      case x: Var ⇒
        if (DEBUG) println("Var "+x+" "+ρ(x))
        ρ(x)

      case Access(e, x) =>
        if (DEBUG) println("Access "+e+" "+x)

        val exp_val = η(e)

        if (DEBUG) println("Exp: "+exp_val)

        exp_val match {
          case ref: Reference =>
            // Call our special lookup function
            lookup(ref.as, x, σ)
          case _ =>
            sys.error("undefined behavior")
        }

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
          case ⌜∧⌝ ⇒ η(e1) ∧ η(e2)
          case ⌜∨⌝ ⇒ η(e1) ∨ η(e2)
        }

      case _ =>
        sys.error("Got bad expression. (undefined behavior)")
    }

  // the state transition relation.
  def next: Set[State] =
    so match {
      // Cases with statements (Rules 1-8)
      case Some(s) =>
        s match {
          // Rule 1
          case Assign(x, e) =>
            if (DEBUG) println("Assign " + x + " = " + e + " (" + η(e) +")")

            // Always just assign the value
            Set(State(None, ρ + (x -> η(e)), σ, κs))

          // Rule 2
          case Update(e1: Exp, x: Var, e2) =>
            if (DEBUG) println("Update " + e1 + "." + x + " = " + e2)

            val ref:Reference = η(e1).asInstanceOf[Reference]
            val new_heap = update(σ, ref.as, x, η(e2))

            Set(State(None, ρ, new_heap, κs))

          // Rule 3
          case Call(x, e, mn, args) =>
            if (DEBUG) println("Call " + x + "." + e + " " + mn + " " + args + "=>" + args.map(η(_)))

            val ref:Reference = η(e).asInstanceOf[Reference]
            val rtn:Set[(Locals, Heap, Seq[Kont])] = call(x, ref.as, σ, mn, args.map(η(_)), ρ,κs )


            var states = Set.empty[State]

            for (s <- rtn) {
              states += State(None, s._1, s._2, s._3)
            }

            // Return our set of states
            states


          // Rule 4
          case New(x, cn, args) =>
            if (DEBUG) println("New " + x + " " + cn + " " + args)

            // Call our constructor
            val con = construct(x, cn, args.map(η(_)), ρ, σ, κs)

            Set(State(None,con._1,con._2,con._3))

          // Rule 5 and 6
          case If(e, tb, fb) =>
            if (DEBUG) println("If " + e)
            // Evaluate our expression
            val exp_val = η(e)

            if (DEBUG) println("Exp: "+exp_val)

            var states = Set.empty[State]
            exp_val match {
              case b:Bool =>

                if (b contains true) {
                  states += State(None, ρ, σ, toSK(tb) ++ κs)
                }
                if (b contains false) {
                  states += State(None, ρ, σ, toSK(fb) ++ κs)
                }

              case _ =>
                sys.error("undefined behavior. (Got a non-boolean value back from if)")
            }

            // Return our possible states
            states


          // Rule 7 and 8
          case While(e, body) =>
            if (DEBUG) println("While " + e)
            // Evaluate our expression
            val exp_val = η(e)

            if (DEBUG) println("Exp "+exp_val)

            // Figure out the possible continuations
            var states = Set.empty[State]
            exp_val match {
              case b:Bool =>
                if (b contains true) {
                  states += State(None, ρ, σ, toSK(body) ++ Seq(WhileK(e, body)) ++ κs)
                }
                if (b contains false) {
                  states += State(None, ρ, σ, κs)
                }
              case _ =>
                sys.error("undefined behavior. (")
            }

            // Return our possible states
            states


          case Print(e) =>
            if (DEBUG) println(e + ": " + η(e))
//            else println(η(e))
            Set(State(None, ρ, σ, κs))
        }

      case None =>
        κs.head match {
          // Rule 9
          case FinK(addr:Address) =>
            if (DEBUG) println("FinK "+addr)

            // get our retK from the heap
            val kont_set = σ.getKont(addr)

            var states = Set.empty[State]
            for (kont <- kont_set) {
              kont.head match {
                case RetK(x, e, ret_locals) =>
                  if (DEBUG) println("retK " + x + " " + e + " " + ret_locals)

                  // Evaulate our expression
                  val exp_val = η(e)
                  if (DEBUG) println("retK " + x + " = " + exp_val)

                  // Return our state
                  states += State(None, ret_locals + (x -> exp_val), σ, kont.tail)
                case _ =>
                  sys.error("undefined behavior. (No ret on Kont after FinK)")
              }
            }
            states

          case RetK(x, e, ret_locals) =>
            if (DEBUG) println("retK " + x + " " + e + " " + ret_locals)

            sys.error("We should never get here... (RetK without FinK)")

          // Rule 10
          case StmtK(stmnt: Stmt) =>
            if (DEBUG) println("StmtK " + stmnt)

            return Set(State(Option(stmnt), ρ, σ, κs.tail))

          // Rule 11 and 12
          case WhileK(e, ss) =>
            if (DEBUG) println("WhileK " + e + " " + ss)
            // Evaluate our expression
            val exp_val = η(e)

            if (DEBUG) println("Exp: "+exp_val)
            exp_val match {
              case b: Bool =>
                var states = Set.empty[State]
                // do a function call
                if (b contains true) {
                  states += State(None, ρ, σ, toSK(ss) ++ κs)
                }
                if (b contains false) {
                  states += State(None, ρ, σ, κs.tail)
                }
                states
              case _ =>
                sys.error("undefined behavior")
            }

          case _ =>
            sys.error("undefined behavior.  Bad stack")
        }

      case _ =>
        sys.error("undefined behavior.  Bad stack")
    }
}

}
