
package org

import parma_polyhedra_library._

object GenGlobalInvFischer extends ZoneGraph {

  def makeProcess(i: Int) = {
    //the clock of process
    val x = new Variable(0)    
    val le_x = new Linear_Expression_Variable(x)
    val l0: Location = "idle_" + i
    val l1: Location = "req_" + i
    val l2: Location = "wait_" + i 
    val l3: Location = "CS_" + i 
    val locs = Set(l0, l1, l2, l3)
    val clks = Map(x -> ("x"+i))
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_3 = new Coefficient(3)
    val le_3 = new Linear_Expression_Coefficient(coeff_3)
    val coeff_2 = new Coefficient(2)
    val le_2 = new Linear_Expression_Coefficient(coeff_2)    

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val inv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
   // inv.add_constraint(new Constraint(le_x, Relation_Symbol.LESS_OR_EQUAL, le_5))
    inv.add_constraint(new Constraint(le_x, Relation_Symbol.LESS_OR_EQUAL, le_2))
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(inv)), (l2 -> new NNC_Polyhedron(trueInv)), (l3 -> new NNC_Polyhedron(trueInv)))

    val g2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val g3 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    //g2.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_THAN, le_2))
    g2.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_OR_EQUAL, le_2))
    g3.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_OR_EQUAL, le_2))
    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)

    val r1: Reset = Set((x, 0))
    val r4: Reset = Set((x, 0))
    val r2: Reset = Set()
    val r3: Reset = Set()

    val t1: Transition = (l0, "try"+i, new NNC_Polyhedron(trueGuard), r1, l1)
    
    val t2: Transition = (l1, "set"+i, new NNC_Polyhedron(trueGuard), r4, l2)

    val t3: Transition = (l2,("enter"+i), g2, r2, l3)
    val t4: Transition = (l3,("retry"+i), g3, r3, l0)
    val trans = Set(t1, t2, t3, t4)	
    val process = (("process"+i), l0, locs, trans, clks, invM)
    process	
  }

  def makeController(nprocs : Int) = {
    val indices = List.range(0, nprocs)
    val indices1 = List.range(0, nprocs+1) 
    //val zs = List.range(0, nprocs+1).map{i => new Variable(i)}
    //val le_zs = List.range(0, nprocs+1).map{i => new Linear_Expression_Variable(zs(i)) }
    //val xs = List.range(nprocs+1, nprocs*2).map{i => new Variable(i)}
    //val le_xs = indices.map{i => new Linear_Expression_Variable(xs(i)) }

    val locsL = indices1.map{i => "s" + i}
    //val clks = ( zs.map{ z => (z -> "xeq" + i) } ::: xs.map{ z => (z -> "xs" + i) }).toMap
    val clks = Map[Clock, String]()	
    val dim = 0

    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)

    //true invariants have univ polygones
    val invM: InvMap = locsL.map{ l => (l -> new NNC_Polyhedron(trueInv)) }.toMap

    val emptyr : Reset = Set()
    val selfloops = for(i <- indices1) yield (locsL(i), "eq" + i , new NNC_Polyhedron(trueGuard), emptyr, locsL(i))
    val selfSETloops = for(i <- indices1.tail) yield (locsL(i), "setc" + i , new NNC_Polyhedron(trueGuard), emptyr, locsL(i))
    val loopsFrom0 = for(i <- indices1.tail) yield (locsL(0), "setc" + i , new NNC_Polyhedron(trueGuard), emptyr, locsL(i))
    val loopsij = for(i <- indices1.tail; j <- indices1.tail) yield (locsL(i), "setc" + j, new NNC_Polyhedron(trueGuard), emptyr, locsL(j))
	
    val controller: TA = ("Controller", locsL(0), locsL.toSet, (loopsFrom0 ::: loopsij ::: selfloops ::: selfSETloops).toSet, clks, invM)

    controller	
  }

  def LinkRetryEq(nprocs: Int) = for(i <- List.range(0, nprocs+1).tail ; j <- List.range(0, nprocs+1).tail ; if (j!=i))  yield  List("retry"+i, "eq"+j)

  def genIM(nprocs: Int) = { 
    val ims1 = List.range(1,nprocs+1).flatMap{i => List(List("eq0", "try"+i), List("eq"+i, "enter"+i))} 
    val ims2 = LinkRetryEq(nprocs) 
    val ims3 = List.range(1,nprocs+1).map{i => List("setc" + i, "set"+i)}
    if (!ims2.isEmpty) (ims1 ::: ims2) ::: ims3 
    else ims1 ::: ims3
  }


// safety property: two processes cannot be at the critical state in the same time
  def genSafe(nprocs: Int) = { 
      val conds = for(i <-  List.range(1, nprocs+1) ; j <-  List.range(1, nprocs+1)) 
		 yield ("Implies(And(CS_"+i +", CS_" +j + ")," + i + " == " + j +")")
      //conds
	//i guess you want to return the and of all conds, and not a list of strings, isn't it ? 	
      if (conds.length > 1) "And(" + conds.reduceLeft(_+","+_) + ")" else conds.mkString
  }
  

  def main(args: Array[String]) {
    val nprocs = args(0).toInt

    if (args.length > 1) 
      reachLim = args(1).toInt    

    if (args.length > 2) 
      DEBUG_LEVEL = args(2).toInt

    val runPy = true //if (args.length > 3) true else false

    Parma_Polyhedra_Library.initialize_library()   

    val im = genIM(nprocs)
    //println("Im = " + im)
    val ims = im.map{_.toSet}.toSet
    //println("II=" + genII(system, ims))
    val indices = List.range(0, nprocs+1).tail

    val systemH = getTAH(makeController(nprocs))(ims) +: indices.map{i => getTAH(makeProcess(i))(ims)}
    (0 to nprocs).foreach{i => toDot(systemH(i))}
    //(0 to nprocs-1).foreach{i => println(toString(systemH(i)))}
    //println(genTCZ3(systemH, ims.map{_.toList}.toList, "", "defaultZ3Fischer.py"))
    //see that the values for deltap aren't set
    //println(genTCZ3(systemH, ims.map{_.toList}.toList, Map(), genSafe(nprocs), "defaultZ3Fischer.py")
    val notSafe = "Not(" + genSafe(nprocs) + ")"	
    //println(genTCZ3(systemH, im, Map(), notSafe, "defaultZ3.py"))

    val z3Txt = genTCZ3(systemH, im, Map(), notSafe, "defaultZ3.py", defaultII="True")

    if (runPy) {
      val z3FilePath = "fischer30-09-" + nprocs + ".py"
      write2File(z3FilePath, z3Txt)
      val res = runZ3(z3FilePath)
      println("res = " + res)
    }
    else println(z3Txt)

    Parma_Polyhedra_Library.finalize_library()

  }
}


/*
 Dis = And(
 * Not(And(C1, is_up, -z >= -1)),
 * Not(C3, is_down),
 * Not(C2, in_0),
 * Not(near_0),
 * And(Not(And(coming_down, -y >= -2)), Not(going_up)), Not(C0, far_0))

Dis = And(
* Not(And(C1, is_up, -z >= -1)),
* Not(C3, is_down),
* Not(C2, in_0),
* And(Not(And(coming_down, -y >= -2)), Not(going_up)), Not(C0, far_0))

*/

