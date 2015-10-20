import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.concrete.domains._
import cs260.lwnn.concrete.helpers.Helpers._
import scala.util._

import TypeAliases._



//——————————————————————————————————————————————————————————————————————————————
// Concrete interpreter entry point

object Concrete {
  var DEBUG = false
  def main( args:Array[String] ) {
    // read program from file given as command-line argument and try to parse it
    Parse.getAST( scala.io.Source.fromFile(args(0)).mkString ) match {
      // parsing error: program is not well-formed
      case Left(err) ⇒ println(err)

      // successfully parsed: program is well-formed
      case Right((classTable, ast:Program)) ⇒
        try {
          // throws Illtyped exception if program is not well-typed
          Typechecker.typecheck(ast, classTable)

          // program is well-formed and well-typed; ready to interpret
          var curr_ς = initstate(ast)

          if (DEBUG) println("θ = "+ θ.class_map)

          while ( !curr_ς.fin ) {
            if (DEBUG)
              println(curr_ς)
            curr_ς = curr_ς.next
          }
        }
        catch {
          // program is not well-typed
          case i:Illtyped ⇒ println("TypeError: ${i.msg}")
        }

      case _ ⇒
        sys.error("undefined behavior")
    }
  }
}

package cs260.lwnn.concrete.interpreter {

//——————————————————————————————————————————————————————————————————————————————
// State, transition rules, and η
//
// Note: Any undefined behavior of the program (i.e., anything not
// explicitly covered in the formal semantics) should result in a
// system error like so: sys.error("undefined behavior")

case class State(/* θ is a global now */ so: Option[Stmt], ρ: Locals, heap: Heap, κs: Seq[Kont]) {
  var DEBUG = false
  // is this a final state (i.e., the program has terminated)?
  def fin: Boolean =
    so.isEmpty && κs.isEmpty

  // we define η here so that we have access to ρ and σ without
  // needing to pass them in as parameters.
  def η(e: Exp): Value =
  // ...
    e match {
      // we deal with nondeterministic choice by randomly selecting a
      // number from the given set.
      case Nums(ns) =>
        new ℤ(Random.shuffle(ns.toList).head)

      case Bools(bs) =>
        new Bool(Random.shuffle(bs.toList).head)

      case Strs(ss) =>
        new Str(Random.shuffle(ss.toList).head)

      case Nulls() =>
        Null

      case x: Var ⇒
        ρ(x)

      case Access(e, x) =>
        val exp_val = η(e)
        exp_val match {
          case addr:Address =>
            heap(addr.asInstanceOf[Address]).locals(x)
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
    def next: State =
      so match {
          // Cases with statements (Rules 1-8)
        case Some(s) =>
          s match {
            // Rule 1
            case Assign(x, e) =>
              if (DEBUG) println("Assign "+x+" = "+e)
              State(None, ρ + (x -> η(e)), heap, κs)

            // Rule 2
            case Update(e1:Exp, x:Var, e2)  =>
              if (DEBUG) println("Update "+e1+"."+x+" = "+e2)
              // Resolve our address
              val exp_val = η(e1)
              exp_val match {
                case addr:Address =>
                  val obj = heap(addr)
                  val new_obj = Object(obj.cn, obj.locals + (x -> η(e2)) )
                  State(None, ρ, heap + (addr -> new_obj), κs)
                case _ =>
                  sys.error("undefined behavior")

              }

            // Rule 3
            case Call(x, e, mn, args) =>
              if (DEBUG) println("Call "+x+"."+e+" "+mn+" "+args)
              // Evaluate our expression
              val exp_val = η(e)
              exp_val match {
                case addr:Address =>
                  // do a function call
                  call(x, addr, heap, mn, args.map(η(_)), ρ, κs)
                case _ =>
                  sys.error("undefined behavior")

              }


            // Rule 4
            case New(x, cn, args) =>
              if (DEBUG) println("New "+x+" "+cn+" "+args)
              construct(x, cn, args.map(η(_)), ρ, heap, κs)

            // Rule 5 and 6
            case If(e, tb, fb) =>
              if (DEBUG) println("If "+e)
              // Evaluate our expression
              val exp_val = η(e)

              if (DEBUG) println(exp_val)
              exp_val match {
                case Bool(v) =>
                  // do a function call
                  v match {
                    case true =>
                      State(None, ρ, heap, toSK(tb) ++  κs)
                    case false =>
                      State(None, ρ, heap, toSK(fb) ++  κs)
                  }
                case _ =>
                  sys.error("undefined behavior. (Got a non-boolean value bzck from if)")
              }


            // Rule 7 and 8
            case While(e, body) =>
              if (DEBUG) println("While "+e)
              // Evaluate our expression
              val exp_val = η(e)
              exp_val match {
                case Bool(v) =>
                  // do a function call
                  v match {
                    case true =>
                      State(None, ρ, heap, toSK(body) ++ Seq(WhileK(e, body)) ++ κs)
                    case false =>
                      State(None, ρ, heap, κs)
                  }
                case _ =>
                  sys.error("undefined behavior")
              }

            case Print(e) =>
              println(e+": "+η(e))
              State(None, ρ, heap, κs)
          }

        case None =>
          κs.head match {
            // Rule 9
            case retK(x, e, ret_locals) =>
              if (DEBUG) println("retK "+x+" "+e+" "+ret_locals)
              // Evaluate our expression

              val exp_val = η(e)
              if (DEBUG) println("retK "+x+" = "+exp_val)
              State(None, ret_locals + (x -> exp_val), heap, κs.tail)

            // Rule 10
            case StmtK(stmnt:Stmt) =>
              if (DEBUG) println("StmtK "+stmnt)
              State(Option(stmnt), ρ, heap, κs.tail)

            // Rule 11 and 12
            case WhileK(e, ss) =>
              if (DEBUG) println("WhileK "+e+" "+ss)
              // Evaluate our expression
              val exp_val = η(e)
              exp_val match {
                case Bool(v) =>
                  // do a function call
                  v match {
                    case true =>
                      State(None, ρ, heap, toSK(ss) ++ κs)
                    case false =>
                      State(None, ρ, heap, κs.tail)
                  }
                case _ =>
                  sys.error("undefined behavior")
              }
          }
      }
}

}