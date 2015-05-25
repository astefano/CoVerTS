package org

import parma_polyhedra_library._

object GenGlobalInvTGC extends ZoneGraph {

  def makeTrain(i: Int) = {
    //the clock of train
    val x = new Variable(0)    
    val le_x = new Linear_Expression_Variable(x)
    val l0: Location = "far_" + i
    val l1: Location = "near_" + i
    val l2: Location = "in_" + i 
    val locs = Set(l0, l1, l2)
    val clks = Map(x -> ("x"+i))
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_3 = new Coefficient(3)
    val le_3 = new Linear_Expression_Coefficient(coeff_3)
    val coeff_5 = new Coefficient(5)
    val le_5 = new Linear_Expression_Coefficient(coeff_5)    

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val inv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv.add_constraint(new Constraint(le_x, Relation_Symbol.LESS_OR_EQUAL, le_5))
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(inv)), (l2 -> new NNC_Polyhedron(inv)))

    val g2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    //g2.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_THAN, le_2))
    g2.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_OR_EQUAL, le_3))

    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val r1: Reset = Set((x, 0))
    val r2: Reset = Set()
    val r3: Reset = Set()
    val t1: Transition = (l0, "at"+i, new NNC_Polyhedron(trueGuard), r1, l1)
    //val t2: Transition = (l1, (eps+i), g2, r2, l2)
    val t2: Transition = (l1, eps, g2, r2, l2)
    val t3: Transition = (l2,("et"+i), new NNC_Polyhedron(trueGuard), r3, l0)
    val trans = Set(t1, t2, t3)	
    val train = (("Train"+i), l0, locs, trans, clks, invM)
    train	
  }

  def makeController = {
    val z = new Variable(0)    
    val le_z = new Linear_Expression_Variable(z)

    val l0: Location = "C0"
    val l1: Location = "C1"
    val l2: Location = "C2"
    val l3: Location = "C3"
    val locs = Set(l0, l1, l2, l3)

    val clks = Map(z -> "z")
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_1 = new Coefficient(1)
    val le_1 = new Linear_Expression_Coefficient(coeff_1)
//    val coeff_5 = new Coefficient(5)
//    val le_5 = new Linear_Expression_Coefficient(coeff_5)

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val inv1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv1.add_constraint(new Constraint(le_z, Relation_Symbol.LESS_OR_EQUAL, le_1))
    val inv3 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv3.add_constraint(new Constraint(le_z, Relation_Symbol.LESS_OR_EQUAL, le_1))
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(inv1)), (l2 -> new NNC_Polyhedron(trueInv)), (l3 -> new   NNC_Polyhedron(inv3)))

//cheating! to compute delta_p ...
//    val inv2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
//    inv2.add_constraint(new Constraint(le_z, Relation_Symbol.LESS_OR_EQUAL, le_5))
//    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(inv1)), (l2 -> new NNC_Polyhedron(inv2)), (l3 -> new   NNC_Polyhedron(inv3)))

    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val g2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g2.add_constraint(new Constraint(le_z, Relation_Symbol.EQUAL, le_1))

    val r1: Reset = Set((z, 0))
    val r2: Reset = Set()
    val r3: Reset = Set((z, 0))
    val r4: Reset = Set()

    val t1: Transition = (l0, "ac", new NNC_Polyhedron(trueGuard), r1, l1)
    val t2: Transition = (l1, "lc", g2, r2, l2)
    val t3: Transition = (l2, "ec", new NNC_Polyhedron(trueGuard), r3, l3)
    val t4: Transition = (l3, "rc", new NNC_Polyhedron(trueGuard), r4, l0)
    val trans = Set(t1, t2, t3, t4)	

    val controller = ("Controller", l0, locs, trans, clks, invM)
    controller	
  }

  def makeGate = {
    //the clocks of gate
    val y = new Variable(0)    
    val le_y = new Linear_Expression_Variable(y)

    val l0: Location = "is_up"
    val l1: Location = "coming_down"
    val l2: Location = "is_down"
    val l3: Location = "going_up"
    val locs = Set(l0, l1, l2, l3)
    val clks = Map(y -> "y")
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_1 = new Coefficient(1)
    val le_1 = new Linear_Expression_Coefficient(coeff_1)
    val coeff_2 = new Coefficient(2)
    val le_2 = new Linear_Expression_Coefficient(coeff_2)

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val inv1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv1.add_constraint(new Constraint(le_y, Relation_Symbol.LESS_OR_EQUAL, le_1))
    val inv3 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv3.add_constraint(new Constraint(le_y, Relation_Symbol.LESS_OR_EQUAL, le_2))
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(inv1)), (l2 -> new NNC_Polyhedron(trueInv)), (l3 -> new NNC_Polyhedron(inv3)))

    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val g4 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g4.add_constraint(new Constraint(le_y, Relation_Symbol.GREATER_OR_EQUAL, le_1))

    val r1: Reset = Set((y, 0))
    val r3: Reset = Set((y, 0))

    val epsg = eps//+"g"
    val t1: Transition = (l0, "lg", new NNC_Polyhedron(trueGuard), r1, l1)
    val t2: Transition = (l1, epsg, new NNC_Polyhedron(trueGuard), Set(), l2)
    val t3: Transition = (l2, "rg", new NNC_Polyhedron(trueGuard), r3, l3)
    val t4: Transition = (l3, epsg, g4, Set(), l0)
    val trans = Set(t1, t2, t3, t4)	

    val gate = ("Gate", l0, locs, trans, clks, invM)
    gate
  }

  def genIM(n: Int) = List.range(0,n).flatMap{i => List(List("ac", "at"+i), List("ec", "et"+i), List("lc", "lg"), List("rc", "rg"))}:+List(eps)

  //safety prop: in -> isdown 
  def genSafe2(n: Int) = {
    if (n == 1) "Not(Implies(in_0, is_down))"
   else {
      val indices = List.range(0, n)
      val s1 = "Not(" + indices.foldLeft("And(")((r, c) => r + "Implies(in_" + c + ", is_down), ").dropRight(2) + "))"
      val s2 = indices.foldLeft("")((r, c) => r + ", Implies(near_" + c + ", And(" + (indices.toSet - c).foldLeft("")(_+ ", far_" +_).drop(2)+ "))").drop(2)
      "And(" + s1 + ", " + s2 + ")"
    }
  }

  def genSafe2Int(n: Int) = {
    if (n == 1) "Not(Implies(in_0 == 1, is_down == 1))"
   else {
      val indices = List.range(0, n)
      val s1 = "Not(" + indices.foldLeft("And(")((r, c) => r + "Implies(in_" + c + " == 1, is_down == 1), ").dropRight(2) + "))"
      val s2 = indices.foldLeft("")((r, c) => r + ", Implies(near_" + c + " == 1, And(" + (indices.toSet - c).foldLeft("")(_+ ", far_" +_ + " == 1").drop(2)+ "))").drop(2)
      "And(" + s1 + ", " + s2 + ")"
    }
  }


  def main(args: Array[String]) {
    ISLOCINT = true //if (args(0).toInt == 1) true else false
    val vs = 1
    val n = args(1-vs).toInt
    val trainIndices = List.range(0, n)
    //val n = 2

    if (args.length > 1) 
      DEBUG_LEVEL = args(1).toInt

    Parma_Polyhedra_Library.initialize_library()   

    val im = genIM(n)
    val ims = im.map{_.toSet}.toSet
    //println("II=" + genII(system, ims))
    //println(genTCZ3(system, im, dis, "defaultZ3TGC.py"))
    val imWithEps = ims// + Set(eps + "g") ++ trainIndices.map{i => Set(eps+i)}.toSet

    val controller = makeController    

    val systemH = getTAH(controller)(imWithEps) +: getTAH(makeGate)(imWithEps) +: trainIndices.map{i => getTAH(makeTrain(i))(imWithEps)}
    (0 to n+1).foreach{i => println(toString(systemH(i)))}
    //println(genTCZ3(systemH, imWithEps.map{_.toList}.toList, "", "defaultZ3TGC.py"))
    //see that the values for deltap aren't set
    val rd = computeDelta(makeController, "dummyClk")
    val deltas = rd._2
    println("#deltas = " + deltas)   
    val ndeltas = deltas.map{el => if (el._1 == "ac") ("ac" -> 5) else el}
    println("#deltas = " + ndeltas)   
//    println(genTCZ3(systemH, imWithEps.map{_.toList}.toList, Map(), genSafe2(n), "defaultZ3TGC.py"))
    val strengthen = ""
    val fars = trainIndices.map{i => "far_"+i}.reduceLeft(_+"+"+_)
    val ii = if (ISLOCINT) "And(" + fars + " + C2 + C1 == " + n + ", " + fars + "- C3 - C0 +1 == " + n + ", " + "C2 + C3 + going_up + is_up == 1, is_down + coming_down == C2 + C3)" else ""
    val safe = if (ISLOCINT) genSafe2Int(n) else genSafe2(n)
    val z3Txt = genTCZ3(systemH, imWithEps.map{_.toList}.toList, ndeltas, safe, "defaultZ3TGC.py", strengthen, ii, true)

    val z3FilePath = "tgc1503-" + n + ".py"
    write2File(z3FilePath, z3Txt)
    val res = runZ3(z3FilePath)
    println("res = " + res)

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

