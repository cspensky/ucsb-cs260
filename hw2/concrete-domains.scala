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

  var class_map = Map[Str, (FieldMap, MethodMap)]

  def apply( className:Str): (FieldMap, MethodMap) =
    class_map(className)

  def +(name:Str, FieldMap, MethodMap): θ = {

  }

}


//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals( var_to_value:Map[Var, Value] ) {
  // Store our locals which map Variable to Values

  def apply( x:Var ): Value =
    var_to_value(x)

  def +( new_var_value:(Var, Value) ): Locals = {
    // We can only assign new values, but shouldn't be adding new vars
    assert( var_to_value contains new_var_value._1)
    Locals( var_to_value + new_var_value )

  }
}

//——————————————————————————————————————————————————————————————————————————————
// Heap

case class Heap( address_to_obj:Map[Address, Object] ) {
  // Map map addresses to objects

  def apply( addr:Address ): Object =
    address_to_obj(addr)

  def +( new_heap_obj:(Address,Object) ): Heap = {
    // Each address can only be used once
    assert(! (address_to_obj contains new_heap_obj._1) )
    Heap( address_to_obj + new_heap_obj)
  }
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
  def ≈( v:Value ): Bool =
    Bool( this == v )
  def ≠( v:Value ): Bool =
    Bool( this != v )
}

case class ℤ( n:BigInt ) extends Value {
  // Operations for integers
  def +( z:ℤ ) =
    ℤ( n + z.n )

  def −( z:ℤ ) =
    ℤ( n - z.n )

  def ×( z:ℤ ) =
    ℤ( n * z.n )

  def ÷( z:ℤ ) =
    ℤ( n / z.n )

  def <( z:ℤ ) =
    ℤ( if (n < z.n) 1 else 0 )

  def ≤( z:ℤ ) =
    ℤ( if (n <= z.n) 1 else 0 )

//  def ≈( z:ℤ ) =
//    ℤ( if (n == z.n) 1 else 0 )
//
//  def ≠( z:ℤ ) =
//    ℤ( if (n != z.n) 1 else 0 )

  override def toString =
    n.toString
}

case class Bool( b:Boolean ) extends Value {
  def ∧( b2:Bool ) =
    Bool( b && b2.b )

  def ∨( b2:Bool ) =
    Bool( b || b2.b )

  override def toString =
    b.toString
}

case class Str( str:String ) extends Value {
  def +( s:Str ) =
    Str( str + s.str )

  def <( s:Str ) =
    Bool( str < s.str )

  def ≤( s:Str ) =
    Bool( str <= s.str)

  override def toString =
    str
}

sealed abstract class Reference extends Value

case class Address( addr:BigInt ) extends Reference {

//  def +(n2:BigInt): Address = {
//    Address( n + n2.n )
//  }

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
