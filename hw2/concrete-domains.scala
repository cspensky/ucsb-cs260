package cs260.lwnn.concrete.domains

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

  // ...
}


//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals( /* ... */ ) {
  // ...
}

//——————————————————————————————————————————————————————————————————————————————
// Heap

case class Heap( /* ... */ ) {
  // ...
}

//——————————————————————————————————————————————————————————————————————————————
// Value

sealed abstract class Value {
  def +( v:Value ): Value = sys.error("undefined behavior")
  def −( v:Value ): Value = sys.error("undefined behavior")
  def ×( v:Value ): Value = sys.error("undefined behavior")
  def ÷( v:Value ): Value = sys.error("undefined behavior")
  def <( v:Value ): Value = sys.error("undefined behavior")
  def ≤( v:Value ): Value = sys.error("undefined behavior")
  def ∧( v:Value ): Value = sys.error("undefined behavior")
  def ∨( v:Value ): Value = sys.error("undefined behavior")
  def ≈( v:Value ): Value = sys.error("undefined behavior")
  def ≠( v:Value ): Value = sys.error("undefined behavior")
}

case class ℤ( /* ... */ ) extends Value {
  // ...

  override def toString =
    n.toString
}

case class Bool( /* ... */ ) extends Value {
  // ...

  override def toString =
    b.toString
}

case class Str( /* ... */ ) extends Value {
  // ...

  override def toString =
    str
}

sealed abstract class Reference extends Value

case class Address( /* ... */ ) extends Reference {
  // ...

  override def toString =
    "addr" + loc
}

object Address {
  // generate fresh addresses on demand
  var genLoc = 0
  def apply(): Address = { genLoc += 1; Address(genLoc-1) }
}

case object Null extends Reference {
  // ...

  override def toString =
    "null"
}

//——————————————————————————————————————————————————————————————————————————————
// Object

case class Object( /* ... */ ) {
  // ...
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
// ...
