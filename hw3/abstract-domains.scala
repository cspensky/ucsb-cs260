package cs260.lwnn.abstracted.domains

import cs260.lwnn.syntax._
import cs260.lwnn.util._

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// ClassDefs
//
// the class definitions are invariant, so we can factor them out into
// one global version rather than having one per state as in the
// formal semantics

case object θ {
  type FieldMap = Map[Var, Type]
  type MethodMap = Map[MethodName, Method]

  // ... (same as for the concrete semantics)
}


//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals( /* ... */ ) {
  // ...
}

//——————————————————————————————————————————————————————————————————————————————
// Heap
//
// NOTE: in this version, we always weakly update the heap. for
// convenience, a Heap maintains two maps, one for objects and one for
// continuation stacks. In other words, there will be a map for
// Address to Object and also a Map for Address to sets of
// continuation stacks. Thus, there will be two different methods for
// accessing the heap (one for accessing objects, one for accessing
// continuation stacks) and two different methods for updating the
// heap (ditto).

case class Heap( /* ... */ ) {
  // ...
}

//——————————————————————————————————————————————————————————————————————————————
// Value
//
// NOTE: the type system disallows many operations on disparate value
// types (including ⊔), but we need to define them in the
// implementation anyway or the compiler will complain. We'll just
// have them return a ⊥ value.

sealed abstract class Value {
  def is_⊥ : Boolean
  def ⊔( v:Value ): Value
  def +( v:Value ): Value
  def −( v:Value ): Value
  def ×( v:Value ): Value
  def ÷( v:Value ): Value
  def <( v:Value ): Value
  def ≤( v:Value ): Value
  def ∧( v:Value ): Value
  def ∨( v:Value ): Value
  def ≈( v:Value ): Value
  def ≠( v:Value ): Value
}

// we'll use the {+,0,−} abstract domain with the following lattice:
// 
//      ⊤
//     /|\
//    − 0 +
//     \|/
//      ⊥
//
sealed abstract class ℤ extends Value


//
//  Top
//
class ℤ_top extends ℤ {

  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ = new ℤ_top()

  def +( v:Value ): ℤ = new ℤ_top()

  def −( v:Value ): ℤ = new ℤ_top()

  def ×( v:Value ): ℤ = new ℤ_top()

  def ÷( v:Value ): ℤ = new ℤ_top()

  def <( v:Value ): Bool = new Bool(Set(true, false))

  def ≤( v:Value): Bool = new Bool(Set(true))

  def ∧( v:Value ): ℤ = new ℤ_top()

  def ∨( v:Value ): ℤ = new ℤ_top()

  def ≈( v:Value ): Bool =
    v match {
      case ℤ_top => new Bool(Set(true))
      case _ => new Bool(Set(false))
    }

  def ≠( v:Value ): Bool =
    v match {
      case ℤ_top => new Bool(Set(false))
      case _ => new Bool(Set(true))
    }
}

//
//  POS +
//
class ℤ_pos extends ℤ {
  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_top()
      case ℤ_zero => new ℤ_top()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def +( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_zero => new ℤ_pos()
      case ℤ_neg => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
      case ℤ_top => new ℤ_top()
    }

  def −( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_top()
      case ℤ_neg => new ℤ_pos()
      case ℤ_zero => new ℤ_pos()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ×( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ÷( v:Value ): ℤ =
    v match {
        // Could be 1/3 => 0 in integer division (Assume we always round up)
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => sys.error("undefined behavior. (Divide by 0)")
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def <( v:Value ): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true, false)) // Who knows
      case ℤ_neg => new Bool(Set(false))
      case ℤ_zero => new Bool(Set(false))
      case ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
    }

  def ≤( v:Value): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true, false)) // Who knows
      case ℤ_neg => new Bool(Set(false))
      case ℤ_zero => new Bool(Set(false))
      case ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
    }

  def ∧( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_pos()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ∨( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => new ℤ_pos()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ≈( v:Value ): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true))
      case _ => new Bool(Set(false))
    }

  def ≠( v:Value ): Bool =
    v match {
      case ℤ_pos => new Bool(Set(false))
      case _ => new Bool(Set(true))
    }
}

//
//  NEG -
//
class ℤ_neg extends ℤ {
  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_top()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => new ℤ_top()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def +( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_top()
      case ℤ_zero => new ℤ_neg()
      case ℤ_neg => new ℤ_neg()
      case ℤ_bot => new ℤ_bot()
      case ℤ_top => new ℤ_top()
    }

  def −( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_neg()
      case ℤ_neg => new ℤ_top()
      case ℤ_zero => new ℤ_neg()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ×( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_neg()
      case ℤ_neg => new ℤ_pos()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ÷( v:Value ): ℤ =
    v match {
      // Could be 1/3 => 0 in integer division (Assume we always round up)
      case ℤ_pos => new ℤ_neg()
      case ℤ_neg => new ℤ_pos()
      case ℤ_zero => sys.error("undefined behavior. (Divide by 0)")
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def <( v:Value ): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true)) // Who knows
      case ℤ_neg => new Bool(Set(true, false))
      case ℤ_zero => new Bool(Set(true))
      case ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
    }

  def ≤( v:Value): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true)) // Who knows
      case ℤ_neg => new Bool(Set(true,false))
      case ℤ_zero => new Bool(Set(true))
      case ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
    }

  def ∧( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ∨( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_neg()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => new ℤ_neg()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ≈( v:Value ): Bool =
    v match {
      case ℤ_neg => new Bool(Set(true))
      case _ => new Bool(Set(false))
    }

  def ≠( v:Value ): Bool =
    v match {
      case ℤ_top => new Bool(Set(false))
      case _ => new Bool(Set(true))
    }
}

//
//  ZERO 0
//
class ℤ_zero extends ℤ {
  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_top()
      case ℤ_neg => new ℤ_top()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def +( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_zero => new ℤ_zero()
      case ℤ_neg => new ℤ_neg()
      case ℤ_bot => new ℤ_bot()
      case ℤ_top => new ℤ_top()
    }

  def −( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_neg()
      case ℤ_neg => new ℤ_pos()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ×( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_zero()
      case ℤ_neg => new ℤ_zero()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ÷( v:Value ): ℤ =
    v match {
      // Could be 1/3 => 0 in integer division (Assume we always round up)
      case ℤ_pos => new ℤ_zero()
      case ℤ_neg => new ℤ_zero()
      case ℤ_zero => sys.error("undefined behavior. (Divide by 0)")
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def <( v:Value ): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true)) // Who knows
      case ℤ_neg => new Bool(Set(false))
      case ℤ_zero => new Bool(Set(false))
      case ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
    }

  def ≤( v:Value): Bool =
    v match {
      case ℤ_pos => new Bool(Set(true)) // Who knows
      case ℤ_neg => new Bool(Set(false))
      case ℤ_zero => new Bool(Set(true))
      case ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
    }

  def ∧( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_zero()
      case ℤ_neg => new ℤ_zero()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ∨( v:Value ): ℤ =
    v match {
      case ℤ_pos => new ℤ_pos()
      case ℤ_neg => new ℤ_neg()
      case ℤ_zero => new ℤ_zero()
      case ℤ_top => new ℤ_top()
      case ℤ_bot => new ℤ_bot()
    }

  def ≈( v:Value ): Bool =
    v match {
      case ℤ_zero => new Bool(Set(true))
      case _ => new Bool(Set(false))
    }

  def ≠( v:Value ): Bool =
    v match {
      case ℤ_zero => new Bool(Set(false))
      case _ => new Bool(Set(true))
    }
}

//
//  BOTTOM _|_
//
class ℤ_bot extends ℤ {

  def is_⊥ : Boolean = true

  def ⊔( v:Value ): ℤ = new ℤ_bot()

  def +( v:Value ): ℤ = new ℤ_bot()

  def −( v:Value ): ℤ = new ℤ_bot()

  def ×( v:Value ): ℤ = new ℤ_bot()

  def ÷( v:Value ): ℤ = new ℤ_bot()

  def <( v:Value ): Bool = new Bool(Set(true, false))

  def ≤( v:Value): Bool = new Bool(Set(true, false))

  def ∧( v:Value ): ℤ = new ℤ_bot()

  def ∨( v:Value ): ℤ = new ℤ_bot()

  def ≈( v:Value ): Bool =
    v match {
      case ℤ_bot => new Bool(Set(true))
      case _ => new Bool(Set(false))
    }

  def ≠( v:Value ): Bool =
    v match {
      case ℤ_bot => new Bool(Set(false))
      case _ => new Bool(Set(true))
    }
}

object ℤ {
  val ⊤ = Long.MaxValue
  val ⊥ = Long.MinValue

  def α( ns:Set[BigInt] ): ℤ =

    // Empty set?
    if (ns.isEmpty)
      new ℤ_bot()
    else {
      // Map everything to Z
      ns.map(x => if (x.equals(BigInt(0))) 0
      else if (x < 0) -1
      else if (x > 0) 1)

      // More than one element left?
      if (ns.size > 1)
        new ℤ_top()

      // They must all be the same, what are they?
      ns.head match {
        case 1 =>
          new ℤ_pos()
        case -1 =>
          new ℤ_neg()
        case 0 =>
          new ℤ_zero()
      }
    }
}

// we'll use the (𝒫({true, false}), ⊆) abstract domain.
class Bool( bs:Set[Boolean] ) extends Value {

  def is_⊥ : Boolean =
    bs match {
      case ⊥ => true
      case _ => false
    }

  def ⊔( v:Bool ): Bool =
  v match {
    case ⊥ => ⊥
    case ⊤ => ⊤
    case _ => new Bool(v.bs ++ bs)
  }
  def +( v:Value ): Bool = sys.error("undefined behavior. (Adding bools)")

  def −( v:Value ): Bool = sys.error("undefined behavior. (- bools)")

  def ×( v:Value ): Bool = sys.error("undefined behavior. (x bools)")

  def ÷( v:Value ): Bool = sys.error("undefined behavior. (/ bools)")

  def <( v:Value ): Bool = sys.error("undefined behavior. (< bools)")

  def ≤( v:Value): Bool = sys.error("undefined behavior. (<= bools)")

  def ∧( v:Value ): Bool =
    v match {
      case x:Bool => new Bool(x.bs & bs)
      case _ => sys.error("undefined behavior. (Type Mismatch)")
    }

  def ∨( v:Value ): Bool =
    v match {
      case x:Bool => new Bool(x.bs ++ bs)
      case _ => sys.error("undefined behavior. (Type Mismatch)")
    }

  def ≈( v:Value ): Bool =
    v match {
      case x:Bool => new Bool(Set(x.bs == bs))
      case _ => sys.error("undefined behavior. (Type Mismatch)")
    }

  def ≠( v:Value ): Bool =
    v match {
      case x:Bool => new Bool(Set(x.bs != bs))
      case _ => sys.error("undefined behavior. (Type Mismatch)")
    }

  override def toString = {
    if (bs.isEmpty) "⊥"
    else if (bs.size == 1) bs.head.toString
    else "{true, false}"
  }
}

object Bool {
  val ⊤ = Set[Boolean](true,false)
  val ⊥ = Set[Boolean]()
  val True = Set[Boolean](true)
  val False = Set[Boolean](false)

  def α( bs:Set[Boolean] ): Bool =
    bs match {
      case ⊤ => Bool(⊤)
      case ⊥ => Bool(⊥)
      case True => Bool(True)
      case False => Bool(False)

    }
}

// for strings we'll use the {⊥,⊤} domain s.t. ⊥ means no string and ⊤
// means any string, so the ordering is ⊥ ⊑ ⊤.
sealed abstract class Str extends Value
class Str_unset extends Str {
  def is_⊥ : Boolean = true
  def ⊔( v:Value ): Value =
    v match {
      case x:Str_set => new Str_set()
      case x:Str_unset => new Str_unset()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def +( v:Value ): Value =
    v match {
      case x:Str_set => new Str_set()
      case x:Str_unset => new Str_unset()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def −( v:Value ): Value = sys.error("undefined behavior. (- Str)")
  def ×( v:Value ): Value = sys.error("undefined behavior. (* Str)")
  def ÷( v:Value ): Value = sys.error("undefined behavior. (/ Str)")
  def <( v:Value ): Value = sys.error("undefined behavior. (< Str)")
  def ≤( v:Value ): Value = sys.error("undefined behavior. (<= Str)")
  def ∧( v:Value ): Value = sys.error("undefined behavior. (^ Str)")
  def ∨( v:Value ): Value = sys.error("undefined behavior. (V Str)")
  def ≈( v:Value ): Bool =
    v match {
      case x:Str_set => new Bool(Set(false))
      case x:Str_unset => new Bool(Set(true))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≠( v:Value ): Value =
    v match {
      case x: Str_set => new Bool(Set(true))
      case x: Str_unset => new Bool(Set(false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }
}

class Str_set extends Str {
  def is_⊥ : Boolean = true
  def ⊔( v:Value ): Value =
    v match {
      case x:Str_set => new Str_set()
      case x:Str_unset =>  new Str_set()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def +( v:Value ): Value =
    v match {
      case x:Str_set =>  new Str_set()
      case x:Str_unset =>  new Str_set()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def −( v:Value ): Value = sys.error("undefined behavior. (- Str)")
  def ×( v:Value ): Value = sys.error("undefined behavior. (* Str)")
  def ÷( v:Value ): Value = sys.error("undefined behavior. (/ Str)")
  def <( v:Value ): Value = sys.error("undefined behavior. (< Str)")
  def ≤( v:Value ): Value = sys.error("undefined behavior. (<= Str)")
  def ∧( v:Value ): Value = sys.error("undefined behavior. (^ Str)")
  def ∨( v:Value ): Value = sys.error("undefined behavior. (V Str)")
  def ≈( v:Value ): Bool =
    v match {
      case x:Str_set => new Bool(Set(true,false))
      case x:Str_unset => new Bool(Set(false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≠( v:Value ): Bool =
    v match {
      case x: Str_set => new Bool(Set(true,false))
      case x: Str_unset => new Bool(Set(true))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }
}


object Str {
  val ⊤ = true
  val ⊥ = false

  def α( strs:Set[String] ): Str =
    if (strs.isEmpty)
      new Str_unset()
    else
      new Str_set()
}

// for convenience we'll keep a set of addresses and separately a
// boolean indicating whether the reference could also be Null.
case class Reference( as:Set[Address], nil:Boolean = false ) extends Value {
  // ...

  override def toString =
    if ( as.isEmpty && nil ) "null"
    else if ( as.size == 1 && !nil ) as.head.toString
    else {
      val addrs = as map ( _.toString )
      val strs = if ( nil ) addrs + "null" else addrs
      "{" + strs.mkString(",") + "}"
    }
}

object Reference {
  val ⊥ = // ...
  val Null = // ...

  def apply( a:Address ): Reference =
    // ...
}

// abstract addresses will be the AST node id of the left-hand side
// variable of the New statement that allocates the address.
case class Address( loc:Int ) {
  override def toString =
    "addr" + loc
}

//——————————————————————————————————————————————————————————————————————————————
// Object

case class Object( cn:ClassName, flds:Map[Var, Value] ) {
  def ⊔( o:Object ): Object = {
    // ...
  }

  def apply( x:Var ): Value =
    flds(x)

  def +( xv:(Var, Value) ): Object =
    Object( cn, flds + xv )
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
case class StmtK( s:Stmt ) extends Kont
case class WhileK( e:Exp, ss:Seq[Stmt] ) extends Kont
case class RetK( x:Var, e:Exp, ρ:Locals ) extends Kont
case class FinK( a:Address ) extends Kont
