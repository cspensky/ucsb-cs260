package cs260.lwnn.concrete.helpers

import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.concrete.domains._
import cs260.lwnn.concrete.interpreter.State

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Helper functions



object Helpers {
  def get_default(t:Type): Value = {
    t match {
      case IntT => ℤ(0)
      case BoolT => Bool(false)
      case StrT => Str("")
      case _ => Null
    }
  }

  def initstate(p: Program): State = {
    // Initialize our class map
    θ.init(p)

    println("θ = "+ θ.class_map)
    // Get our classname and address
    val cn = θ.getFirstClassName()
    val addr = Address()
    // Define our fields
    val flds = θ(cn)._1.foldLeft(Map.empty[Var, Value]) { (m, kv) => m+ (kv._1 -> get_default(kv._2)) }
    // Get our initial object
    val obj = Object(cn, Locals(flds))

    // Update our heap
    val heap = Heap(Map(addr -> obj))

    // Extract our methods and fields
    val methods = θ(cn)._2

    // Kontinuation stack
    val kont = toSK(methods(cn).body)

    // Define our locals
    val locals =  methods(cn).params.foldLeft(Map.empty[Var,Value]) { (m, d: Decl) =>
      m + (d.x -> get_default(d.τ))
    } + (Var("self") -> addr)


    State(None,Locals(locals),heap, kont)
  }


  def call(x:Var, addr:Address, heap:Heap, mn:MethodName, values:Seq[Value], locals:Locals, kont:Seq[Kont] ): State = {
    val cn = heap(addr).cn

    val methods = θ(cn)._2

    val method_flds = methods(mn).params.foldLeft(Map.empty[Var, Value]) { (m, decl) => m + (decl.x -> get_default(decl.τ)) }

    val new_kont = toSK(methods(mn).body) ++ Seq(retK(x, methods(mn).rete, locals))

    println(method_flds)
    // Update our new locals to fill in any passed parameters, and keep existing defaults otherwise
    val new_locals = method_flds.zipWithIndex.foldLeft(Map.empty[Var,Value]) {
      (m,e) =>
        println(e, values)
        // Ignore self, which is always first
        if (0 < e._2 && e._2 <= values.length)
          m + (e._1._1 -> values(e._2 -1))
        else
          m + e._1
    } + (Var("self") -> addr)

    State(None, Locals(new_locals), heap, new_kont ++ kont)


  }

  def construct(x:Var, cn:ClassName, values:Seq[Value], locals:Locals, heap:Heap, kont:Seq[Kont] ): State = {
    val addr = Address()

    val flds = θ(cn)._1.foldLeft(Map.empty[Var, Value]) { (m, kv) => m+ (kv._1 -> get_default(kv._2)) }

    val obj = Object(cn, Locals(flds))

    val new_heap = heap + (addr -> obj)

    // Extract our methods and fields
    val methods = θ(cn)._2

    // Update our kontinuation stack with all of the statements and our return
    val new_kont = toSK(methods(cn).body) :+ retK(x, Var("self"), locals)

    val method_flds = methods(cn).params.foldLeft(Map.empty[Var, Value]) { (m, decl) => m + (decl.x -> get_default(decl.τ)) }

    // Update our new locals to fill in any passed parameters, and keep existing defaults otherwise
    val new_locals = method_flds.zipWithIndex.foldLeft(Map.empty[Var,Value]) {
      (m,e) =>
        // Ignore self, which is always first
        if (0 < e._2 && e._2 <= values.length)
          m + (e._1._1 -> values(e._2 -1))
        else
          m + e._1
    } + (Var("self") -> addr)

    State(None,Locals(new_locals),new_heap,new_kont.asInstanceOf[Seq[Kont]] ++ kont)
  }

  def toSK( ss:Seq[Stmt] ): Seq[Kont] =
    ss map ( StmtK(_) )

}
