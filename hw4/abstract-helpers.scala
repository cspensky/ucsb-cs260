package cs260.lwnn.abstracted.helpers

import cs260.lwnn.abstracted.domains.Address
import cs260.lwnn.abstracted.domains.Heap
import cs260.lwnn.abstracted.domains.Kont
import cs260.lwnn.abstracted.domains.Locals
import cs260.lwnn.abstracted.domains.θ
import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.abstracted.domains._
import cs260.lwnn.abstracted.interpreter.State

import TypeAliases._

import scala.collection.immutable.ListMap

//——————————————————————————————————————————————————————————————————————————————
// Helper functions

object Helpers {
  // section 2.3.2; doesn't take θ because we've factored it out into a global.
  def call(x: Var, as: Set[Address], σ: Heap, mn: MethodName, vs: Seq[Value], ρ: Locals, κs: Seq[Kont]): Set[(Locals, Heap, Seq[Kont])] = {

    var rtn_sets = Set.empty[(Locals, Heap, Seq[Kont])]
    for (a <- as) {
      val cn = σ.getObj(a).cn
      val methods = θ(cn)._2
      val ak = Address(methods(mn).id)

      // Define our locals for this address
      val new_locals = methods(mn).params.zipWithIndex.foldLeft(ListMap.empty[Var, Value]) {
        (m, e) =>
          // Ignore self, which is always first
          if (0 < e._2 && e._2 <= vs.length)
            m + (e._1.x -> vs(e._2 - 1))
          else
            m + (e._1.x -> defaultvalue(e._1.τ))
      } + (Var("self") -> Reference(a))

      // Update our heap
      val new_heap = σ.addKont(ak, Seq[Kont](RetK(x, methods(mn).rete, ρ)) ++ κs)

      // New continuation stack
      val new_kont = toSK(methods(mn).body) ++ Seq(FinK(ak))

      // Append to our set of returned states
      rtn_sets = rtn_sets + ( (Locals(new_locals),
        new_heap,
        new_kont))
    }

    // Return a set of possible new values
    rtn_sets
  }

  // section 2.3.3; doesn't take θ because we've factored it out into a global.
  def construct(x: Var, cn: ClassName, vs: Seq[Value], ρ: Locals, σ: Heap, κs: Seq[Kont]): (Locals, Heap, Seq[Kont]) = {
    // Set our address according to our heap model
    val a = new Address(x.id)


    // Define our fields with default values
    val flds = θ(cn)._1.foldLeft(ListMap.empty[Var, Value]) {
      (m, kv) =>
        m+ (kv._1 -> defaultvalue(kv._2))
    }

    // Create our new object
    val obj = Object(cn, flds )

    // Get our list of methods
    val methods = θ(cn)._2

    // Define our new locals
    val new_locals = methods(cn).params.zipWithIndex.foldLeft(ListMap.empty[Var, Value]) {
      (m, e) =>
        // Ignore self, which is always first
        if (0 < e._2 && e._2 <= vs.length)
          m + (e._1.x -> vs(e._2 - 1))
        else
          m + (e._1.x -> defaultvalue(e._1.τ))
    } + (Var("self") -> Reference(a))

    // Update our heap (obj)
    var new_heap = σ.addObj(a, obj)

    // Get our method address
    val ak = new Address(methods(cn).id)

    // Update our heap (kont)
    new_heap = new_heap.addKont(ak, Seq[Kont](RetK(x, methods(cn).rete, ρ)) ++ κs)

    val new_kont = toSK(methods(cn).body) ++ Seq(FinK(ak))

    (Locals(new_locals), new_heap, new_kont)
  }

  // section 2.3.4
  def defaultvalue( τ:Type ): Value =
    τ match {
      case IntT => new ℤ_zero()
      case BoolT => new Bool(Set(false))
      case StrT => new Str_unset()
      case _ => new Reference(Set(),true)
    }

  // section 2.3.5
  def initstate( p:Program ): (Int, State) = {
    // Initialize our class map
    θ.init(p)

    // Get our classname and address
    val cn = θ.getFirstClassName()
    val addr = new Address(0)

    val flds = θ(cn)._1.foldLeft(ListMap.empty[Var, Value]) {
      (m, kv) => m + (kv._1 -> defaultvalue(kv._2))
    }

    // Get our initial object
    val obj = Object(cn, flds)

    // Update our heap (1 object, 0 kont)
    val heap = Heap(Map(addr -> obj), Map())

    // Extract our methods and fields
    val methods = θ(cn)._2

    // Kontinuation stack
    val kont = toSK(methods(cn).body)

    // Define our locals
    val locals =  methods(cn).params.foldLeft(ListMap.empty[Var,Value]) { (m, d: Decl) =>
      m + (d.x -> defaultvalue(d.τ))
    } + (Var("self") -> Reference(addr))

    (0, State(None,Locals(locals),heap, kont))
  }

  // section 2.3.6
  def lookup( as:Set[Address], x:Var, σ:Heap ): Value = {

    if (as.isEmpty)
      return Reference.Null
    // Resolve all of our values
    as.map( σ.getObj(_).flds(x) ).reduceLeft[Value] { (acc, n) =>
      acc ⊔ n
    }

  }

  // section 2.3.7
  def toSK( ss:Seq[Stmt] ): Seq[Kont] =
    ss map ( StmtK(_) )

  // section 2.3.8
  def update( σ:Heap, as:Set[Address], x:Var, v:Value ): Heap = {
    // Is this a singleton?
    if (as.size == 1) {
      return σ.addObj(as.head, σ.getObj(as.head) + (x -> v))
    }

   // Get our new unioned value
    var new_val = v
    for (a <- as) {
      val obj = σ.getObj(a)
      new_val = new_val ⊔ obj(x)
    }

    // Updated all of the address locations
    var new_heap = σ
    for (a <- as) {
      val obj = σ.getObj(a)
      new_heap = new_heap.addObj(a, obj + (x -> new_val))
    }

    // Return aggregated heap
    new_heap
  }
}
