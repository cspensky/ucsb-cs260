package cs260.imp.syntax

//——————————————————————————————————————————————————————————————————————————————
// AST base class, Program

sealed abstract class AST {
  val id = AST.id() // unique node identifier
}

object AST {
  // create unique node identifiers
  var genID = 0
  def id(): Int = { genID += 1; genID-1 }
}

case class Program( xs:Seq[Var], ss:Seq[Stmt] ) extends AST

//——————————————————————————————————————————————————————————————————————————————
// Stmt
//
// We include a Print statement not in the semantics, which prints out
// the value of an expression; this is used to help debug the
// interpreters by inspecting the values they compute.

sealed abstract class Stmt extends AST
case class Assign( x:Var, e:Exp ) extends Stmt
case class If( e:Exp, ss1:Seq[Stmt], ss2:Seq[Stmt] ) extends Stmt
case class While( e:Exp, ss:Seq[Stmt] ) extends Stmt
case class Print( e:Exp ) extends Stmt

//——————————————————————————————————————————————————————————————————————————————
// Exp, BinaryOp

sealed abstract class Exp extends AST
case class Nums( ns:Set[BigInt] ) extends Exp
case class Var( name:String ) extends Exp
case class Binop( op:BinaryOp, e1:Exp, e2:Exp ) extends Exp

sealed abstract class BinaryOp
case object ⌜+⌝ extends BinaryOp
case object ⌜−⌝ extends BinaryOp
case object ⌜×⌝ extends BinaryOp
case object ⌜÷⌝ extends BinaryOp
case object ⌜<⌝ extends BinaryOp
case object ⌜≤⌝ extends BinaryOp
case object ⌜≈⌝ extends BinaryOp
case object ⌜≠⌝ extends BinaryOp

//——————————————————————————————————————————————————————————————————————————————
// example programs

object Examples {
  val example1 = Program(
    Seq(Var("a"), Var("b"), Var("c")),
    Seq(
      Assign(Var("a"), Nums(Set(1))),
      Assign(Var("b"), Nums(Set(1))),
      While(
        Binop(⌜≠⌝, Var("a"), Nums(Set(0))),
        Seq(
          Assign(Var("b"), Binop(⌜×⌝, Var("b"), Binop(⌜+⌝, Var("a"), Nums(Set(1))))),
          Assign(Var("a"), Binop(⌜−⌝, Var("a"), Nums(Set(1))))
        )
      ),
      Assign(Var("c"), Binop(⌜+⌝, Var("a"), Var("b"))),
      Print(Var("c"))
    )
  )

  val example2 = Program(
    Seq(Var("x"), Var("y"), Var("ret")),
    Seq(
      Assign(Var("x"), Nums(Set(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10))),
      Assign(Var("y"), Nums(Set(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10))),
      If(
        Binop(⌜≤⌝, Var("y"), Var("x")),
        Seq(
          While(
            Binop(⌜≤⌝, Var("y"), Var("x")),
            Seq(
              Assign(Var("y"), Binop(⌜+⌝, Var("x"), Nums(Set(1))))
            )
          )
        ),
        Seq(
          Assign(Var("y"), Binop(⌜−⌝, Var("x"), Nums(Set(1))))
        )
      ),
      Assign(Var("ret"), Var("y")), 
      Print(Var("ret"))
    )
  )
}
