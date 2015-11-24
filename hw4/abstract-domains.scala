package cs260.lwnn.abstracted.domains

import cs260.lwnn.syntax._
import cs260.lwnn.util._

import TypeAliases._

import scala.collection.immutable.{SortedSet, ListMap}

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
  var first_class = "TopClass"

  def apply( cn:ClassName ): (FieldMap, MethodMap) = {
    class_map(cn)
  }

  def init( prog:Program): Unit = {
    first_class = prog.classes.head.cn
    class_map = prog.classes.foldLeft(Map("TopClass" ->
      (Map().asInstanceOf[FieldMap], Map().asInstanceOf[MethodMap]) )) { (m, c:Class) =>
      m + (c.cn ->
        (
          m(c.supercn)._1 ++
            c.fields.foldLeft(Map.empty[Var, Type]) { (m:FieldMap, f:Decl) => m + (f.x -> f.τ)},
          m(c.supercn)._2 ++
            c.methods.foldLeft(Map.empty[MethodName, Method]) { (m:MethodMap, mm:Method) => m + (mm.mn -> mm)}
          )
        )
    }
  }

  def getFirstClassName(): ClassName = {
    first_class
  }

}


//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals( var_to_value:ListMap[Var, Value] ) {
  // Store our locals which map Variable to Values

  def apply( x:Var ): Value =
    var_to_value(x)

  def +( new_var_value:(Var, Value) ): Locals = {
    // We can only assign new values, but shouldn't be adding new vars
    assert( var_to_value contains new_var_value._1)
    Locals( var_to_value + new_var_value )

  }

  def ⊔( l:Locals): Locals = {

    val mergedValues = var_to_value ++ l.var_to_value.map {
      case (var_name, value) => if (var_to_value contains var_name) {
        var_name -> (value ⊔ var_to_value(var_name))
      } else {
        var_name -> value
      }
    }
    Locals(mergedValues)
  }
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

case class Heap( address_to_obj:Map[Address, Object] ,
                 address_to_kont:Map[Address, Set[Seq[Kont]]]) {
  // Map map addresses to objects

  def ⊔( h:Heap): Heap = {
    val mergedObjs = address_to_obj ++ h.address_to_obj.map {
      case (addr, obj: Object) => if (address_to_obj contains addr) {
        addr -> (obj ⊔ address_to_obj(addr))
      } else {
        addr -> obj
      }
    }

    val mergedKonts = address_to_kont ++ h.address_to_kont.map {
      case (addr, konts) => if (address_to_kont contains addr) {
        addr -> (konts ++ address_to_kont(addr))
      } else {
        addr -> konts
      }
    }
    Heap(mergedObjs, mergedKonts)
  }


  def getObj( addr:Address ): Object =
    address_to_obj(addr)

  def addObj( new_heap_obj:(Address,Object) ): Heap = {
    new Heap( address_to_obj + new_heap_obj, address_to_kont)
  }

  // Map addresses to Konts

  def getKont( addr:Address ): Set[Seq[Kont]] =
    address_to_kont(addr)

  def addKont( new_heap_obj:(Address, Seq[Kont] )): Heap = {
    if (address_to_kont contains new_heap_obj._1) {
      Heap(address_to_obj, address_to_kont + (new_heap_obj._1 -> (
        address_to_kont(new_heap_obj._1) + new_heap_obj._2)
        )
      )
    } else {
      Heap(address_to_obj,
        address_to_kont + (new_heap_obj._1 -> Set(new_heap_obj._2))
      )

    }
  }
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
case class ℤ_top extends ℤ {

  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case a:ℤ_bot => new ℤ_bot()
      case _ => new ℤ_top()
    }

  def +( v:Value ): ℤ = v match {
    case a:ℤ_bot => new ℤ_bot()
    case  _ => new ℤ_top()
  }

  def −( v:Value ): ℤ = v match {
    case a:ℤ_bot => new ℤ_bot()
    case  _ => new ℤ_top()
  }

  def ×( v:Value ): ℤ = v match {
    case a:ℤ_pos => new ℤ_top()
    case a:ℤ_zero => new ℤ_zero()
    case a:ℤ_neg =>new ℤ_top()
    case a:ℤ_bot => new ℤ_bot()
    case a:ℤ_top => new ℤ_top()
    case _ => sys.error("undefined behavior. (Type mismatch)")
  }

  def ÷( v:Value ): ℤ = v match {
    case a:ℤ_bot => new ℤ_bot()
    case a:ℤ_zero => new ℤ_bot() // Anything divided by zero is undefined.
    case _ => new ℤ_top()
  }

  def <( v:Value ): Bool = new Bool(Set(true, false))

  def ≤( v:Value): Bool = new Bool(Set(true,false))

  def ∧( v:Value ): ℤ = v match {
    case a:ℤ_bot => new ℤ_bot()
    case _ => new ℤ_top()
  }

  def ∨( v:Value ): ℤ = v match {
    case a:ℤ_bot => new ℤ_bot()
    case _ => new ℤ_top()
  }

  def ≈( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true,false))
      case a:ℤ_zero => new Bool(Set(true,false))
      case a:ℤ_neg => new Bool(Set(true,false))
      case a:ℤ_bot => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≠( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true,false))
      case a:ℤ_zero => new Bool(Set(true,false))
      case a:ℤ_neg => new Bool(Set(true,false))
      case a:ℤ_bot => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  override def toString = "ℤ_⊤"
}

//
//  BOTTOM _|_
//
case class ℤ_bot extends ℤ {

  def is_⊥ : Boolean = true

  def ⊔( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => a
      case a:ℤ_neg => a
      case a:ℤ_zero => a
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => this
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

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
      case a:ℤ_bot => new Bool(Set(true))
      case _ => new Bool(Set(false))
    }

  def ≠( v:Value ): Bool =
    v match {
      case a:ℤ_bot => new Bool(Set(false))
      case _ => new Bool(Set(true))
    }

  override def toString = "ℤ_⊥"
}

//
//  POS +
//
case class ℤ_pos extends ℤ {
  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_top()
      case a:ℤ_zero => new ℤ_top()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => this
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def +( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_zero => new ℤ_pos()
      case a:ℤ_neg => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case a:ℤ_top => new ℤ_top()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def −( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_top()
      case a:ℤ_neg => new ℤ_pos()
      case a:ℤ_zero => new ℤ_pos()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ×( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ÷( v:Value ): ℤ =
    v match {
        // Could be 1/3 => 0 in integer division (Assume we always round up)
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_bot() //sys.error("undefined behavior. (Divide by 0)")
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def <( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true, false)) // Who knows
      case a:ℤ_neg => new Bool(Set(false))
      case a:ℤ_zero => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case a:ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≤( v:Value): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true, false)) // Who knows
      case a:ℤ_neg => new Bool(Set(false))
      case a:ℤ_zero => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case a:ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ∧( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_pos()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ∨( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_pos()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≈( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true,false))
      case a:ℤ_zero => new Bool(Set(false))
      case a:ℤ_neg => new Bool(Set(false))
      case a:ℤ_bot => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≠( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true,false))
      case a:ℤ_zero => new Bool(Set(true))
      case a:ℤ_neg => new Bool(Set(true))
      case a:ℤ_bot => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  override def toString = "ℤ_+"
}

//
//  NEG -
//
case class ℤ_neg extends ℤ {
  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_top()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_top()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => this
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def +( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_top()
      case a:ℤ_zero => new ℤ_neg()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_bot => new ℤ_bot()
      case a:ℤ_top => new ℤ_top()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def −( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_neg()
      case a:ℤ_neg => new ℤ_top()
      case a:ℤ_zero => new ℤ_neg()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ×( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_neg()
      case a:ℤ_neg => new ℤ_pos()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ÷( v:Value ): ℤ =
    v match {
      // Could be 1/3 => 0 in integer division (Assume we always round up)
      case a:ℤ_pos => new ℤ_neg()
      case a:ℤ_neg => new ℤ_pos()
      case a:ℤ_zero => new ℤ_bot() //sys.error("undefined behavior. (Divide by 0)")
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def <( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true)) // Who knows
      case a:ℤ_neg => new Bool(Set(true, false))
      case a:ℤ_zero => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case a:ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≤( v:Value): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true)) // Who knows
      case a:ℤ_neg => new Bool(Set(true,false))
      case a:ℤ_zero => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case a:ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ∧( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ∨( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_neg()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_neg()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≈( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(false))
      case a:ℤ_zero => new Bool(Set(false))
      case a:ℤ_neg => new Bool(Set(true,false))
      case a:ℤ_bot => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≠( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true))
      case a:ℤ_zero => new Bool(Set(true))
      case a:ℤ_neg => new Bool(Set(true,false))
      case a:ℤ_bot => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  override def toString = "ℤ_-"
}

//
//  ZERO 0
//
case class ℤ_zero extends ℤ {
  def is_⊥ : Boolean = false

  def ⊔( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_top()
      case a:ℤ_neg => new ℤ_top()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => this
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def +( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_bot => new ℤ_bot()
      case a:ℤ_top => new ℤ_top()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def −( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_neg()
      case a:ℤ_neg => new ℤ_pos()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ×( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_zero()
      case a:ℤ_neg => new ℤ_zero()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_zero()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ÷( v:Value ): ℤ =
    v match {
      // Could be 1/3 => 0 in integer division (Assume we always round up)
      case a:ℤ_pos => new ℤ_zero()
      case a:ℤ_neg => new ℤ_zero()
      case a:ℤ_zero => new ℤ_bot() //sys.error("undefined behavior. (Divide by 0)")
      case a:ℤ_top => new ℤ_zero()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def <( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true)) // Who knows
      case a:ℤ_neg => new Bool(Set(false))
      case a:ℤ_zero => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case a:ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≤( v:Value): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true)) // Who knows
      case a:ℤ_neg => new Bool(Set(false))
      case a:ℤ_zero => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false)) // Doesn't make sense
      case a:ℤ_bot => new Bool(Set(true,false)) // Doesn't make sense
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ∧( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_zero()
      case a:ℤ_neg => new ℤ_zero()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ∨( v:Value ): ℤ =
    v match {
      case a:ℤ_pos => new ℤ_pos()
      case a:ℤ_neg => new ℤ_neg()
      case a:ℤ_zero => new ℤ_zero()
      case a:ℤ_top => new ℤ_top()
      case a:ℤ_bot => new ℤ_bot()
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≈( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(false))
      case a:ℤ_zero => new Bool(Set(true))
      case a:ℤ_neg => new Bool(Set(false))
      case a:ℤ_bot => new Bool(Set(false))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  def ≠( v:Value ): Bool =
    v match {
      case a:ℤ_pos => new Bool(Set(true))
      case a:ℤ_zero => new Bool(Set(false))
      case a:ℤ_neg => new Bool(Set(true))
      case a:ℤ_bot => new Bool(Set(true))
      case a:ℤ_top => new Bool(Set(true,false))
      case _ => sys.error("undefined behavior. (Type mismatch)")
    }

  override def toString = "ℤ_0"
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
      val signs = ns.map(x =>
        if (x.equals(BigInt(0))) 0
        else if (x < 0) -1
        else 1):Set[Int]

      // More than one element left?
      if (signs.size > 1) {
        new ℤ_top()
      } else {
        // They must all be the same, what are they?
        signs.head match {
          case 1 =>
            new ℤ_pos()
          case -1 =>
            new ℤ_neg()
          case 0 =>
            new ℤ_zero()
        }
      }
    }
}

// we'll use the (𝒫({true, false}), ⊆) abstract domain.
case class Bool( bs:Set[Boolean] ) extends Value {

//  def unapply(bs:Set[Boolean]) = Some(bs)

  def is_⊥ : Boolean =
    bs match {
      case Bool.⊥ => true
      case _ => false
    }

  def contains( b:Boolean ): Boolean = bs contains b

  def ⊔( v:Value ): Bool = {
    v match {
      case b:Bool => if (b.is_⊥)
          new Bool(Bool.⊥)
        else
          new Bool(bs ++ b.bs)
      case _ => sys.error("undefined behavior. (Type Mismatch)")
    }
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
      case ⊤ => new Bool(⊤)
      case ⊥ => new Bool(⊥)
      case True => new Bool(True)
      case False => new Bool(False)

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

  override def toString = "Str_⊥"
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

  override def toString = "Str_⊤"
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
  def is_⊥ : Boolean = as.isEmpty
  def ⊔( v:Value ): Value =
    v match {
      case x:Reference =>
        new Reference(x.as ++ as, nil || x.nil)
      case _ => sys.error("undefined behavior. (Type mismatch +)")
    }
  def +( v:Value ): Value = sys.error("undefined behavior. (+ on Ref)")
  def −( v:Value ): Value = sys.error("undefined behavior. (- on Ref)")
  def ×( v:Value ): Value = sys.error("undefined behavior. (x on Ref)")
  def ÷( v:Value ): Value = sys.error("undefined behavior. (/ on Ref)")
  def <( v:Value ): Value =
    v match {
      case x:Reference =>
        var rtn = Set.empty[Boolean]
        for (e <- as) {
          for (e2 <- x.as) {
            if (e2.loc >= e.loc) rtn += false
            else rtn += true
          }
        }
        new Bool(rtn)
      case _ => sys.error("undefined behavior. (Type mismatch +)")
    }
  def ≤( v:Value ): Value =
    v match {
      case x:Reference =>
        var rtn = Set.empty[Boolean]
        for (e <- as) {
          for (e2 <- x.as) {
            if (e2.loc > e.loc) rtn += false
            else rtn += true
          }
        }
        new Bool(rtn)
      case _ => sys.error("undefined behavior. (Type mismatch +)")
    }
  def ∧( v:Value ): Value = sys.error("undefined behavior (^ for Reference)")
  def ∨( v:Value ): Value = sys.error("undefined behavior (V for Reference)")
  def ≈( v:Value ): Bool =
    v match {
      case x:Reference =>
        var rtn = Set.empty[Boolean]

        // Item in one that isn't in the other?
        if (as.size != x.as.size) {
          rtn += false
        }

        // Both null?
        if (nil == true && nil == x.nil) {
          rtn += true
        }

        for (e <- as) {
          for (e2 <- x.as) {
            if (e2.loc != e.loc) rtn += false
            if (e2.loc == e.loc) rtn += true
          }
        }

        new Bool(rtn)
      case _ => sys.error("undefined behavior. (Type mismatch +)")
    }
  def ≠( v:Value ): Bool =
    v match {
      case x:Reference =>
        var rtn = Set.empty[Boolean]

        // Item in one that isn't in the other?
        if (as.size != x.as.size) {
          rtn += true
        }

        // Both null?
        if ((as.isEmpty && x.as.isEmpty) && (nil == true && nil == x.nil)) {
          rtn += false
        }


        for (e <- as) {
          for (e2 <- x.as) {
            if (e2.loc == e.loc) rtn += false
            if (e2.loc != e.loc) rtn += true
          }
        }
        new Bool(rtn)
      case _ => sys.error("undefined behavior. (Type mismatch +)")
    }

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
  val ⊥ = Nil
  val Null = new Reference(Set.empty[Address], true)

  def apply( a:Address ): Reference = {
    // ...

    new Reference(Set(a), false)
  }
}

// abstract addresses will be the AST node id of the left-hand side
// variable of the New statement that allocates the address.
case class Address( loc:Int ) {
  override def toString =
    "addr" + loc
}

//——————————————————————————————————————————————————————————————————————————————
// Object

case class Object( cn:ClassName, flds:ListMap[Var, Value] ) {
  def ⊔( o:Object ): Object = {
    if (o.cn != cn) sys.error("undefined behavior. (union of different objects)")

    Object(cn, o.flds ++ flds)
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
