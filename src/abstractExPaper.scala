package org

import parma_polyhedra_library._

object GenGlobalInvAbstractExPaper extends ZoneGraph {

  def makeWorker(i: Int, beta: Int) = {
    //the clock of a rode
    val y = new Variable(0)    
    val le_y = new Linear_Expression_Variable(y)
    val l1: Location = "l" + (2*i + 1)
    val l2: Location = "l" + (2*i + 2)
    val locs = Set(l1, l2)
    val clks = Map(y -> ("y"+i))
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_ct = new Coefficient(beta)
    val le_ct = new Linear_Expression_Coefficient(coeff_ct)

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val invM: InvMap = Map((l1 -> new NNC_Polyhedron(trueInv)), (l2 -> new NNC_Polyhedron(trueInv)))

    val g1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g1.add_constraint(new Constraint(le_y, Relation_Symbol.GREATER_OR_EQUAL, le_ct))
    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val r1: Reset = Set()
    val r2: Reset = Set((y, 0))
    val t1: Transition = (l1, ("b"+i), g1, r1, l2)
    val t2: Transition = (l2,("d"+i), new NNC_Polyhedron(trueGuard), r2, l1)
    val trans = Set(t1, t2)	
    val worker = (("Worker"+i), l1, locs, trans, clks, invM)
    worker	
  }

  def makeController(alpha: Int, beta: Int) = {
    //the clocks of a controller
    val x = new Variable(0)    
    val le_x = new Linear_Expression_Variable(x)

    debug("x = " + x + " le_x " + le_x + " le_x.arg = " + le_x.argument)

    val l0: Location = "lc0"
    val l1: Location = "lc1"
    val l2: Location = "lc2"
    val locs = Set(l0, l1, l2)
    val clks = Map(x -> "x")
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_alpha = new Coefficient(alpha)
    val coeff_beta = new Coefficient(beta)
    val le_beta = new Linear_Expression_Coefficient(coeff_beta)
    val le_alpha = new Linear_Expression_Coefficient(coeff_alpha)

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val inv0 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
//    inv0.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_OR_EQUAL, le_beta))
    val inv1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv1.add_constraint(new Constraint(le_x, Relation_Symbol.LESS_OR_EQUAL, le_alpha))
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(inv0)), (l1 -> new NNC_Polyhedron(inv1)), (l2 -> new NNC_Polyhedron(trueInv)))

    val g1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g1.add_constraint(new Constraint(le_x, Relation_Symbol.GREATER_OR_EQUAL, le_beta))
    val g2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g2.add_constraint(new Constraint(le_x, Relation_Symbol.EQUAL, le_alpha))
    val g3 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)

    val r: Reset = Set((x, 0))

    val t1: Transition = (l0, eps, g1, r, l1)
    val t2: Transition = (l1, "a", g2, r, l2)
    val t3: Transition = (l2, "c", g3, r, l1)
    val trans = Set(t1, t2, t3)	

    val controller = ("Controller", l0, locs, trans, clks, invM)
      controller	
  }

  //TC stands for TempControl
  def genTCIM(n: Int) = List.range(0,n).flatMap{i => List(List("a", "b"+i), List("c", "d"+i))}:+List(eps)

  def main(args: Array[String]) {
    ISLOCINT = if (args(0).toInt == 1) true else false
    val n = args(1).toInt
//    val beta = args(1).toInt
//    val alpha = n * beta
    val alpha = args(2).toInt
    val beta = n * alpha
//    val beta = alpha / 2
    val checkSafe = args(3).toInt
    if (args.length > 4) 
      DEBUG_LEVEL = args(4).toInt

    //val n = 2
    Parma_Polyhedra_Library.initialize_library()   

    val im = genTCIM(n)
    val ims = im.map{_.toSet}.toSet
    val imWithEps = ims + Set(eps)
    val indices = List.range(0, n)
    val ctroller = makeController(alpha, beta)
    val systemH = getTAH(ctroller)(imWithEps) +: indices.map{i => getTAH(makeWorker(i, beta))(imWithEps)}
    //(0 to n).foreach{i => println(toString(system(i)) + "\n" + toString(systemH(i)))}

    val globalIni = "And(" + locProp("lc1") + ", " + indices.map{i => locProp("l" + (2*i+1))}.reduceLeft(_+", "+_) + ")"

    val ii = "lc0 + lc1 + " + indices.map{i => "l" + (2*i+2)}.reduceLeft(_+" + "+_) + " == 1"
    //println(genTCZ3(system, genTCIM(n), genDIS(im, system), "defaultZ3TC.py"))
    
    //println(genTCZ3(systemH, genTCIM(n), Map(("h", 1350), ("c", 1350)), "", "defaultZ3TC.py", strengthen, ii))

    //println(genTCZ3(systemH, genTCIM(n), Map(("h", 1350), ("c", 1350)), "", "defaultZ3TC.py", "", ii))

    val ctroller1 = makeController(alpha, beta)
    val rd = computeDelta(ctroller1, "dummyClk")
    val deltas = rd._2
    //println("deltas = " + deltas)
    val safe = "Or(" + List.range(0, n).map{i => "Implies(And(lc1 == 1, l" + (2*i+1) + " == 1), x - y" + i + " <= " + (alpha-beta)+ ")"}.reduceLeft(_+","+_) + ")"
    val negSafe = "Not(" + safe + ")"
    if (checkSafe == 1) println(genTCZ3(systemH, genTCIM(n), deltas, negSafe, "defaultZ3TC.py", "", ii))
    else println(genTCZ3(systemH, genTCIM(n), deltas, "", "defaultZ3TC.py", "", ii, true))

    Parma_Polyhedra_Library.finalize_library()

  }
}

