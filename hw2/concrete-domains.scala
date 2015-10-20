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

  var class_map = Map.empty[ClassName, (FieldMap, MethodMap)]

  def apply( cn:ClassName ): (FieldMap, MethodMap) = {
    class_map(cn)
  }

  def init( prog:Program): Unit = {
    class_map = class_map + ("TopClass" -> (Map().asInstanceOf[FieldMap], Map().asInstanceOf[MethodMap]) )
    class_map = prog.classes.foldLeft(Map.empty[ClassName, (FieldMap, MethodMap)]) { (m, c:Class) =>
      m + (c.cn ->
        (
          c.fields.foldLeft(Map.empty[Var, Type]) { (m:FieldMap, f:Decl) => m + (f.x -> f.τ)},
          c.methods.foldLeft(Map.empty[MethodName, Method]) { (m:MethodMap, mm:Method) => m + (mm.mn -> mm)}
          )
        )
    }
  }

  def getFirstClassName(): ClassName = {
    class_map.head._1
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
//    assert(! (address_to_obj contains new_heap_obj._1) )
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
  override def +( z:Value ) =
    ℤ( n + z.asInstanceOf[ℤ].n )

  override def −( z:Value ) =
    ℤ( n - z.asInstanceOf[ℤ].n )

  override def ×( z:Value ) =
    ℤ( n * z.asInstanceOf[ℤ].n )

  override def ÷( z:Value ) =
    if (z.asInstanceOf[ℤ].n == 0)
      ℤ( n / z.asInstanceOf[ℤ].n )
    else
      sys.error("undefined behavior. (Divide by 0)")

  override def <( z:Value ) =
    Bool( if (n < z.asInstanceOf[ℤ].n) true else false )

  override def ≤( z:Value ): Value =
    Bool( if (n <= z.asInstanceOf[ℤ].n) true else false )

//  def ≈( z:Value ) =
//    ℤ( if (n == z.asInstanceOf[ℤ].n) 1 else 0 )
//
//  def ≠( z:Value ) =
//    ℤ( if (n != z.asInstanceOf[ℤ].n) 1 else 0 )

  override def toString =
    n.toString
}

case class Bool( b:Boolean ) extends Value {
  override def ∧( b2:Value ) =
    Bool( b && b2.asInstanceOf[Bool].b )

  override def ∨( b2:Value ) =
    Bool( b || b2.asInstanceOf[Bool].b )

  override def toString =
    b.toString
}

case class Str( str:String ) extends Value {
  override def +( s:Value ) =
    Str( str + s.asInstanceOf[Str].str )

  override def <( s:Value ) =
    Bool( str < s.asInstanceOf[Str].str )

  override def ≤( s:Value ) =
    Bool( str <= s.asInstanceOf[Str].str)

  override def toString =
    str
}

sealed abstract class Reference extends Value

case class Address( loc:BigInt ) extends Reference {

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

case class Object( cn:ClassName, locals:Locals ) {
  // ...
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
case class StmtK( s:Stmt ) extends Kont
case class WhileK( e:Exp, ss:Seq[Stmt] ) extends Kont
case class retK(v:Var, e:Exp, locals:Locals) extends Kont
