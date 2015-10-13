import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.concrete.domains._
import cs260.lwnn.concrete.helpers.Helpers._
import scala.util._

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Concrete interpreter entry point

object Concrete {
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
          while ( !curr_ς.fin ) curr_ς = curr_ς.next
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

package cs260.lwnn.concrete.interpreter {

//——————————————————————————————————————————————————————————————————————————————
// State, transition rules, and η
//
// Note: Any undefined behavior of the program (i.e., anything not
// explicitly covered in the formal semantics) should result in a
// system error like so: sys.error("undefined behavior")

case class State( /* ... */ ) {
  // is this a final state (i.e., the program has terminated)?
  def fin: Boolean =
    // ...

  // we define η here so that we have access to ρ and σ without
  // needing to pass them in as parameters.
  def η( e:Exp ): Value =
    // ...

  // the state transition relation.
  def next: State =
    // ...
}
