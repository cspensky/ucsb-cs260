import cs260.lwnn.syntax._
import cs260.lwnn.util._

import scala.util._
import scala.collection.mutable.{ Set ⇒ MSet, Map ⇒ MMap }
import scala.collection.mutable.MutableList
import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Analysis entry point

object Andersen {
  // flag set by command-line argument: should we use cycle elimination?
  var CE = false
  var DEBUG = false

  def main( args:Array[String] ) {
    Parse.getAST( scala.io.Source.fromFile(args(0)).mkString ) match {
      // parsing error: program is not well-formed
      case Left(err) ⇒ println(err)

      // successfully parsed: program is well-formed
      case Right((classTable, ast:Program)) ⇒
        try {
          // throws Illtyped exception if program is not well-typed
          Typechecker.typecheck(ast, classTable)

          // program is well-formed and well-typed; ready to analyze.
          // first check whether we should use cycle elimination
          if (args.size > 1 && args(1) == "--ce") {
            CE = true
            sys.error("Cycle Elimination not implemented due to time and sanity contraints -- :-(")
          }

          // create and solve the constraint graph
          createGraph(ast)
          solveGraph()

          // print out solution. rather than print everything, which
          // can be overwhelming, instead we'll just print out the
          // points-to sets of the top-level variables.
          //
          // NOTE: if cycle elimination is enabled, then the following
          // needs to be modified accordingly. we want to get exactly
          // the same output whether we use cycle elimination or not.
          //
          val soln:MMap[String, String] = MMap()
          Graph.varToNode foreach {
            case ((m, x), n) ⇒
              val name = m.mn + "_" + x.name
              val ptsto = n.ptsto.toSeq.sortBy(_.id).mkString(", ")
              soln(name) = ptsto
          }
          soln.toSeq.sortBy(_._1).foreach {
            case (name, ptsto) ⇒ println(name + " → " + ptsto)
          }
        }
        catch {
          // program is not well-typed
          case i:Illtyped ⇒ println(s"TypeError: ${i.msg}")
        }

      case _ ⇒
        sys.error("undefined behavior")
    }
  }

  // create the constraint graph from the program's AST. this will:
  //
  // 1. create all TopNodes and ObjNodes (thus, after createGraph is
  // done no new nodes will ever be created). TopNodes correspond to
  // program variables; ObjNodes correspond to objects (with one
  // ObjNode per static allocation site, i.e., New statement, and also
  // one per object field).
  //
  // 2. fill in the appropriate TopNode ptsto sets using the ObjNodes
  // created for the program's New statements.
  //
  // 3. fill in the appropriate TopNode subsetof edges using the copy
  // assignments (e.g., 'x := y') and the determinate method calls
  // (including New statements, which are constructor calls and are
  // always determinate).
  //
  // 4. fill in the appropriate TopNode indirect constraint sets using
  // the remaining assignments and indeterminate method calls.
  //
  // see the comments below for definitions of determinate and
  // indeterminate calls.
  //
  // NOTE: we only care about variables and object fields that have a
  // reference type, i.e., null or some class. any other
  // variables/fields should be ignored.
  //
  // NOTE: we only care about assignments, method calls, and
  // returns. we assume that all assignments, calls, and returns are
  // of the following forms:
  //
  //      x := y
  //      x := y.z
  //    x.y := z
  //      x := new Foo(y, z, null)
  //      x := y.foo(null, z)
  //      x := null
  //    return x
  //    return x.y
  //    return null
  //
  // in particular, there is at most one field access in any statement
  // and no call arguments contain field accesses (the null call
  // arguments are there as an example just to remind you to handle
  // this special case). if the program contains an assignment, call,
  // or return that doesn't meet this requirement, your analysis
  // should call 'sys.error("malformed program")'.
  //
  // NOTE: a method call is _determinate_ if we can figure out which
  // method is being called without any analysis. consider the call 'x
  // := y.foo()'. this call is determinate if (1) foo's type is some
  // class X; and (2) no class that directly or transitively inherits
  // from X overrides method foo. in this case we know that there is
  // only one possible method that this call can go to, and we can go
  // ahead and update the constraint graph appropriately. otherwise
  // the call is _indeterminate_; indeterminate calls will be stored
  // in CallCon indirect constraints, attached to the receiver
  // object's node (in this example, the TopNode for y), and processed
  // dynamically.
  //
  // NOTE: when handling method calls (determinate ones here, but the
  // same note applies for the indeterminate ones handled
  // dynamically), be sure to remember the implicit 'self'
  // parameter. A method's 'self' parameter should be updated so that
  // its points-to set contains the ObjNode used to call that
  // method. For example, for 'x := y.foo()' suppose that y points to
  // an ObjNode o of class X, and X has a particular method foo. then
  // we will generate the appropriate assignments between the call
  // arguments and foo's parameters and between x and foo's return
  // statement. in addition, foo has an implicit parameter 'self', and
  // self's points-to set should be updated to contain o.
  //
  // NOTE: another thing to remember about method calls is that there
  // can be more parameters than arguments. Any extra parameters
  // should have their points-to sets updated to contain Null.
  //
  // First let's generate a class Map to easily lookup methods
  var classMap = MMap[ClassName, Class]()
  var methodMap = MMap[(ClassName,MethodName), Method]()

  def createGraph( ast:Program ) = {


    // Loop over all of our classes
    for (cls <- ast.classes) {
      classMap += (cls.cn -> cls)
      // Loop over every method in the class
      for (method <- cls.methods) {
        methodMap += ((cls.cn,method.mn) -> method)
      }
    }

    // Loop over all of our classes
    for (cls <- ast.classes) {
      if (DEBUG) println("class " + cls.cn + " " + cls.fields)

      // Loop over every method in the class (Just generating TopNodes)
      for (method <- cls.methods) {

        if (DEBUG) println(" method " + method.mn)
        for (param <- method.params) {

          // Create a TopNode for every variable
          if (DEBUG) println("  param " + param.x)
          Graph.varToNode += ((method, param.x) -> new TopNode())

          // Special case for main, since it is never explicitly initialized
          if (cls.cn == "Main" && method.mn == "Main" && param.x.name == "self") {
            Graph.varToNode(method, param.x).ptsto += Graph.allocNode(cls, 1)
          }
        }
      }
    }

    // Loop over all of our classes
    for (cls <- ast.classes) {

      // Loop over every method (This time evaluating the bodies)
      for (method <- cls.methods) {

        // Check out every statement in the body
        for (stmt <- method.body) {

          // Handle each statement properly
          stmt match {

            // Is it an assignment?
            case Assign(x: Var, e: Exp) =>
              if (DEBUG) println("   Assign " + x + ":=" + e)

              e match {
                case v@Var(name:String) =>
                  Graph.varToNode(method, v).subsetof += Graph.varToNode(method, x)

                // Are we updating a field in the variable v1?
                case Access(v1:Var, v2:Var) =>

                  // Get our graph node
                  val graphNode = Graph.varToNode(method, v1)
                  // Check all the objects for this field name
                  for (obj <- graphNode.ptsto) {
                    if (obj.isInstanceOf[ObjNode]) {
                      for (fld <- obj.asInstanceOf[ObjNode].fields.keys) {

                        // If we have this field, update its subsetof set
                        if (fld == v2) {
                          // Update our constraint v1.v2 subseteq x


                          obj.asInstanceOf[ObjNode].subsetof += Graph.varToNode(method, x)

                          graphNode.cons += LhsCon(graphNode, fld, Graph.varToNode(method, x))
                        }
                      }
                    }
                  }

                // Null entry?
                case Nulls() =>
                  if (DEBUG) println("   Assign " + x + ":=" + Nulls())
                  Graph.varToNode(method, x).ptsto += Null

                case _ => sys.error("malformed program")
              }


            // New Object?
            case New( x:Var, cn:ClassName, args:Seq[Exp] ) =>
              if (DEBUG) println("   New " + x + ":=" + cn +"("+args+")")

              val objClass = classMap(cn)
              val objNode = Graph.allocNode(objClass,stmt.id)

              Graph.varToNode(method, x).ptsto += objNode

              val selfMethod = methodMap(cn,cn)
              val selfVar = selfMethod.params(0).x

              Graph.varToNode(selfMethod, selfVar).ptsto += objNode

            // Updating a field?
            case Update( e1:Exp, x:Var, e2:Exp ) =>
              if (DEBUG) println("   Update " + e1 + "." + x + ":=" + e2)

              // Update our constraint


              if (e1.isInstanceOf[Var] && e2.isInstanceOf[Var]) {
                val v1 = e1.asInstanceOf[Var]
                val v2 = e2.asInstanceOf[Var]

                // Get our graph node
                val graphNode = Graph.varToNode(method, v1)
                val graphNode2 = Graph.varToNode(method, v2)


                // Check all the objects for this field name
                for (obj <- graphNode.ptsto) {
                  if (obj.isInstanceOf[ObjNode]) {
                    for (fld <- obj.asInstanceOf[ObjNode].fields.keys) {

                      // If we have this field, update its subsetof set
                      if (fld == x) {
                        Graph.varToNode(method, v2).subsetof += obj.asInstanceOf[ObjNode].fields(fld)
                      }
                    }
                  }
                }

                // Update our constraint e2 subseteq eq.x
                graphNode.cons += RhsCon(graphNode2, graphNode, x)

              } else {
                sys.error("malformed program")
              }

            // Calling a method?
            case Call( x:Var, e:Exp, mn:MethodName, args:Seq[Exp] ) =>
              if (DEBUG) println("   Call " + x + ":=" + e + "."+ mn + "("+args+")")
              // All methods in this version of the language just return self


              if (e.isInstanceOf[Var]) {
                val v = e.asInstanceOf[Var]
                val xNode = Graph.varToNode(method,x)
                val vNode = Graph.varToNode(method,v)
                val selfVar = method.params(0).x


                for (obj <- vNode.ptsto) {
                  if (obj.isInstanceOf[ObjNode]) {
                    val method2 = methodMap(obj.asInstanceOf[ObjNode].cn,mn)

                    // What is our return value?
                    method2.rete match {
                      case a@Access(v1: Var, v2: Var) =>
                        if (DEBUG) println("    Rete = "+a)
                        // Get our graph node
                        val graphNode = Graph.varToNode(method2, v1)
                        graphNode.cons += LhsCon(graphNode, v2, Graph.varToNode(method, x))
                        if (obj.asInstanceOf[ObjNode].fields.contains(v2)) {
                          obj.asInstanceOf[ObjNode].fields(v2).subsetof += Graph.varToNode(method, x)
                        }
//                        Graph.varToNode(method, x).ptsto += obj.asInstanceOf[ObjNode].fields(v2)
                      case v_ret@Var(_) =>
                        if (DEBUG) println("    Rete = "+v_ret)
                        Graph.varToNode(method2,v_ret).subsetof += Graph.varToNode(method,x)
                      case Nulls() =>
                        Graph.varToNode(method, x).ptsto += Null
                      case _ =>
                        sys.error("not handling "+ method2.rete)
                    }

                    // Update the parameters
                    var idx = 0
                    for (param <- method2.params) {

                      // if they were and argument, set them appropriately
                      // Update self
                      if (idx == 0) {
                        Graph.varToNode(method2,param.x).ptsto ++= Graph.varToNode(method,selfVar).ptsto

                      // Other args
                      } else if (idx < args.length+1) {
                        // using +1 since 0 is self and is implicit
                        val arg_e = args(idx-1)

                        // Pts to and subset relationship
                        if (arg_e.isInstanceOf[Var]) {
                          Graph.varToNode(method2, param.x).ptsto ++= Graph.varToNode(method, arg_e.asInstanceOf[Var]).ptsto
                          Graph.varToNode(method, arg_e.asInstanceOf[Var]).subsetof +=  Graph.varToNode(method2, param.x)
                        }

                      // All other params are Null
                      } else {
                        Graph.varToNode(method2, param.x).ptsto += Null
                      }

                      idx += 1
                    }
                  }
                }

                // Add our constraint for solving later
                var topArgs = Seq[TopNode]()
                for (a <- args) {
                  if (a.isInstanceOf[Var]) {
                    topArgs ++= Seq(Graph.varToNode(method,a.asInstanceOf[Var]))
                  }
                }
                xNode.cons += CallCon(xNode, vNode, mn, topArgs)


              } else {
                sys.error("malformed program")
              }

            case _ => println("Oops, we aren't handling this stmt: "+stmt)
          }
        }
      }
    }

  }

  // use the worklist algorithm to propagate ptsto sets and add new
  // edges until the constraint graph converges to its final version.
  //
  // if the CE flag is true, then solveGraph should use Lazy Cycle
  // Detection as described in class: immediately after propagating
  // ptsto information across an edge from node n to node m, check
  // whether n and m have identical points-to sets. if they do, then
  // trigger cycle elimination by calling cycleElim(n).
  //
  def solveGraph() {

    if (DEBUG) println("Solving Graph...")

    // initialize the worklist to contain all TopNodes
    //
    var worklist = List[Node]()
    for (mn_var <- Graph.varToNode.keys) {
      worklist ++= List(Graph.varToNode(mn_var))
    }

    // while the worklist is not empty:

    while (!worklist.isEmpty) {
      //   n := worklist.pop()
      val node = worklist.head
      worklist = worklist.drop(1)

      if (DEBUG) println("Worklist size: "+worklist.size)

      // Handle ObjNodes
      if (node.isInstanceOf[ObjNode]) {
        if (DEBUG) println("ObjNode")
        val n = node.asInstanceOf[ObjNode]
        // Update ptsto
        //   for each dst in n.subsetof do {
        //     propagate n.ptsto to dst.ptsto
        //     if dst.ptsto changed, add dst to worklist
        //     // if CE is true, check whether cycle elimination should be triggered
        //   }
        for (dst <- n.subsetof) {
          if (dst.isInstanceOf[ObjNode]) {
            if (DEBUG) println("and ObjNode")
            val dest = dst.asInstanceOf[ObjNode]
            val tmp = dest.ptsto.size
            dest.ptsto ++= n.ptsto
            if (dest.ptsto.size != tmp) {
              worklist ++= List(dest)
            }
          } else if (dst.isInstanceOf[TopNode]) {
            if (DEBUG) println("and TopNode")
            val dest = dst.asInstanceOf[TopNode]
            val tmp = dest.ptsto.size
            dest.ptsto ++= n.ptsto
            if (dest.ptsto.size!= tmp) {
              worklist ++= List(dest)
            }
          }
        }
      // Handle TopNodes
      } else if (node.isInstanceOf[TopNode]) {
        if (DEBUG) println("TopNode")
        val n = node.asInstanceOf[TopNode]
        // Update ptsto
        //   for each dst in n.subsetof do {
        //     propagate n.ptsto to dst.ptsto
        //     if dst.ptsto changed, add dst to worklist
        //     // if CE is true, check whether cycle elimination should be triggered
        //   }
        for (dst <- n.subsetof) {
          if (dst.isInstanceOf[ObjNode]) {
            if (DEBUG) println("and ObjNode")
            val dest = dst.asInstanceOf[ObjNode]
            val tmp = dest.ptsto.size
            dest.ptsto ++= n.ptsto
            if (dest.ptsto.size!= tmp) {
              worklist ++= List(dest)
            }
          } else if (dst.isInstanceOf[TopNode]) {
            if (DEBUG) println("and TopNode")
            val dest = dst.asInstanceOf[TopNode]
            val tmp = dest.ptsto.size
            dest.ptsto ++= n.ptsto
            if (dest.ptsto.size != tmp) {
              worklist ++= List(dest)
            }
          }
        }


        // Update Constraints
        for (con <- n.cons) {
          con match {
            case RhsCon(src, _, fld) =>
              if (DEBUG) println("RhsCon")
              //   for each RhsCon(src, _, fld) in n.cons {
              //     for each p in n.ptsto {
              //       update src.subsetof to include p.fields(fld)
              //       if src.subsetof changed, add src to worklist
              //     }
              //   }
              val tmp = src.subsetof.size
              for (obj <- n.ptsto) {
                if (obj.isInstanceOf[ObjNode]) {
                  for (f <- obj.asInstanceOf[ObjNode].fields.keys) {

                    // If we have this field, update its subsetof set
                    if (f == fld) {
                      src.subsetof += obj.asInstanceOf[ObjNode].fields(f)
                    }
                  }
                }
              }
              if (src.subsetof.size != tmp) {
                worklist ++= List(src)
              }


            case LhsCon(_, fld, dst) =>
              if (DEBUG) println("LhsCon")
              //   for each LhsCon(_, fld, dst) in n.cons {
              //     for each p in n.ptsto {
              //       update p.fields(fld).subsetof to include dst
              //       if p.fields(fld).subsetof changed, add p.fields(fld) to worklist
              //     }
              //   }
              for (obj <- n.ptsto) {
                if (obj.isInstanceOf[ObjNode]) {
                  for (f <- obj.asInstanceOf[ObjNode].fields.keys) {
                    if (DEBUG) println(f)
                    // If we have this field, update its subsetof set
                    if (f == fld) {
                      val tmp = obj.asInstanceOf[ObjNode].fields(fld).subsetof.size
                       obj.asInstanceOf[ObjNode].fields(fld).subsetof += dst
                      if (obj.asInstanceOf[ObjNode].fields(fld).subsetof.size != tmp) {
                        worklist ++= List(obj.asInstanceOf[ObjNode].fields(fld))
                      }
                    }
                  }
                }
              }

            case CallCon(lhs, _, mn, args) =>
              if (DEBUG) println("CallCon")
              //     for each p in n.ptsto {
              //       let getMethod(p.class, mn) = m @ Method(_, params, _, _, rete)
              //       let paramsN = params map ( getNode(m, _) )
              //       let reteN = getNode(m, rete)
              //       let selfN = getNode(m, Var("self"))
              //       update selfN.ptsto to include p
              //       if selfN.ptsto changed, add selfN to worklist
              //       update reteN.subsetof to include rhs
              //       if reteN.subsetOf changed, add reteN to worklist
              //       for each arg in args {
              //         let prm be the corresponding member of paramsN
              //         update arg.subsetof to include prm
              //         if arg.subsetof changed, add arg to worklist
              //       }
              //       for each prm in params that did not have a corresponding arg {
              //         update prm.ptsto to include Null
              //         if prm.ptsto changed, add prm to worklist
              //       }
              //     }
              //   }
              for (obj <- n.ptsto) {
                if (obj.isInstanceOf[ObjNode] && methodMap.contains((obj.asInstanceOf[ObjNode].cn, mn))) {
                  val method2 = methodMap(obj.asInstanceOf[ObjNode].cn, mn)

                  // Update the parameters
                  var idx = 0
                  for (param <- method2.params) {

                    val paramNode = Graph.varToNode(method2, param.x)
                    // if they were and argument, set them appropriately
                    // Update self
                    if (idx == 0) {
                      val tmp = paramNode.ptsto.size
                      paramNode.ptsto += obj

                      if (paramNode.ptsto.size != tmp) {
                        worklist ++= List(paramNode)
                      }
                    } else if (idx < args.length + 1) {
                      // using +1 since 0 is self and is implicit
                      val arg = args(idx - 1)
                      val tmp = arg.subsetof.size

                      // Put this in our graph creation
                      arg.subsetof += Graph.varToNode(method2, param.x)
                      if (arg.subsetof.size != tmp) {
                        worklist ++= List(arg)
                      }
                    } else {
                      val tmp = Graph.varToNode(method2, param.x).subsetof.size
                      Graph.varToNode(method2, param.x).ptsto += Null
                      if (Graph.varToNode(method2, param.x).subsetof.size != tmp) {
                        worklist ++= List(Graph.varToNode(method2, param.x))
                      }
                    }

                    idx += 1
                  }


                }
              }

          } // end match con

        } // enn contraints loop
      } else {
        sys.error("Weird node type on worklist!")
      }
    }

  }

  // this is called from solveGraph() to detect and merge cycles in
  // the constraint graph involving the given node n. it should only
  // be used if the 'CE' flag is set to true by a command-line
  // argument.
  //
  // NOTE: you will need to modify the definitions of the graph nodes
  // to enable node merging using the union-find data structure.
  //
  // NOTE: cycle elimination is simple in principle, but can be tricky
  // in execution. when merging nodes, you need to remember to
  // transfer all the appropriate information from the constituent
  // nodes to the new set representative. when processing nodes, you
  // need to be very careful that you're always dealing with the set
  // representative and not a node that has been merged away. remember
  // that cycle elimination can happen at any time, and just because
  // something used to be a set representative before doesn't mean
  // that it still is now.
  //
  // NOTE: you can choose whether to define a new kind of node to use
  // as set representatives, or to allow TopNodes and ObjNodes to
  // stand as set representatives; either way will work. consider,
  // though, that TopNodes and ObjNodes can be in the same cycle
  // together, and in this case a set representative needs to act like
  // a TopNode _and_ an ObjNode.
  //
  def cycleElim( n:Node ) {
    // ...
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Indirect constraints (initial and direct constraints are
// represented directly in the constraint graph via the ptsto and
// subsetof sets in the graph nodes)

sealed abstract class Constraint

// field access on the left: src.fld ⊆ dst
case class LhsCon( src:TopNode, fld:Var, dst:TopNode ) extends Constraint

// field access on the right: src ⊆ dst.fld
case class RhsCon( src:TopNode, dst:TopNode, fld:Var ) extends Constraint

// indeterminate method call: lhs := rhs.method(args)
case class CallCon( lhs:TopNode, rhs:TopNode, mn:MethodName, args:Seq[TopNode] ) extends Constraint

//——————————————————————————————————————————————————————————————————————————————
// Constraint graph

// constraint graph nodes
sealed abstract class Node

object Node {
  type Ptsto = MSet[RefNode] // points-to sets
  type Edges = MSet[Node]    // edge sets
}
import Node._

// nodes for top-level variables
case class TopNode(
  ptsto:Ptsto = MSet(),        // points-to set
  subsetof:Edges = MSet(),     // graph edges
  cons:MutableList[Constraint] = MutableList(), // indirect constraints for this node
  myid:Int = Graph.getUniqueID
) extends Node {
  override def equals(other: Any) = other match {
    case that: TopNode =>
      this.ptsto == that.ptsto && this.subsetof == that.subsetof
    case _ => false
  }
  override def hashCode = myid
}

// ref nodes are for things that can belong to points-to sets. this
// includes objects and Null.
sealed abstract class RefNode( val id:Int ) extends Node

// nodes for abstract objects
case class ObjNode(
  ptsto:Ptsto = MSet(),           // points-to set
  subsetof:Edges = MSet(),        // graph edges
  cn:ClassName,                   // this object's class
  site:Int,                       // this object's allocation site (AST node id)
  fields:Map[Var,ObjNode] = Map(), // this object's fields (that are references)
  myid:Int = Graph.getUniqueID
) extends RefNode(site) {
  override def toString = id.toString
  override def hashCode = myid
}

// the Null node. this will only show up inside points-to sets; there
// cannot be edges to or from Null.
case object Null extends RefNode(0) {
  override def toString = "null"
}

object Graph {
  var uniqueID = 0
  def getUniqueID: Int = {
    uniqueID += 1
    uniqueID
  }

  // we need to remember our mapping from variables to TopNodes in
  // order to consistently map the same variable to the same TopNode
  // across all constraints. in order to disambiguate multiple
  // variables with the same name in different methods, we'll actually
  // map from (method, variable) pairs to TopNodes.
  val varToNode = MMap[(Method,Var), TopNode]()

  // return the TopNode corresponding to the given method and
  // variable. use the mapping in varToNode if it exists; otherwise
  // create one and use that.
  def getNode( m:Method, x:Var ): TopNode = {
    TopNode()
  }
    // ...

  // for each object allocation site (i.e., New, as in 'x := new
  // Foo(...)'), we need to take the allocated class and AST node id
  // and create a new ObjNode. this is used to initialize the
  // points-to set of the TopNode corresponding to the variable on the
  // left-hand side of the New.
  //
  // NOTE: each ObjNode contains a map 'fields' containing those class
  // fields that are references; each such field maps to another
  // ObjNode standing for that object's field. the 'site' of these
  // field ObjNodes should be the same as their parent ObjNode, their
  // 'fields' should be empty, and their ptsto sets should be
  // initialized to contain Null.
  //
  // NOTE: the 'allocation site' is the AST node id of the New
  // statement itself. if AST node 'stmt' is 'x := new Foo(...)', then
  // the allocation site is stmt.id.
  //
  def allocNode( cls:Class, id:Int ): ObjNode = {
    var fields = Map[Var, ObjNode]()
    for (f <- cls.fields) {
      if (f.τ.isInstanceOf[ClassT]) {
        fields += (f.x -> new ObjNode(MSet(Null), MSet(), cls.cn, id))
      }
    }
    new ObjNode(MSet(),MSet(), cls.cn, id, fields)
  }
    // ...
}
