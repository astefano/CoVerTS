package org

import parma_polyhedra_library._

object GenGlobalInvTempControl extends ZoneGraph {

  def makeRode(i: Int, ct: Int) = {
    //the clock of a rode
    val t = new Variable(0)    
    val le_t = new Linear_Expression_Variable(t)
    val l0: Location = "l" + 3*i
    val l1: Location = "l" + (3*i + 1)
    val l2: Location = "l" + (3*i + 2)
    val locs = Set(l0, l1, l2)
    val clks = Map(t -> ("t"+i))
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_ct = new Coefficient(ct)
    val le_ct = new Linear_Expression_Coefficient(coeff_ct)

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(trueInv)), (l2 -> new NNC_Polyhedron(trueInv)))

    val g2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g2.add_constraint(new Constraint(le_t, Relation_Symbol.GREATER_OR_EQUAL, le_ct))
    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val r1: Reset = Set((t, ct))
    val r2: Reset = Set()
    val r3: Reset = Set((t, 0))
    val t1: Transition = (l0, eps, new NNC_Polyhedron(trueGuard), r1, l1)
    val t2: Transition = (l1, ("c"+i), g2, r2, l2)
    val t3: Transition = (l2,("r"+i), new NNC_Polyhedron(trueGuard), r3, l1)
    val trans = Set(t1, t2, t3)	
    val rode = (("Rode"+i), l0, locs, trans, clks, invM)
    rode	
  }

  def makeController(ct: Int) = {
    //the clocks of a controller
    val t = new Variable(0)    
    val le_t = new Linear_Expression_Variable(t)

    debug("t = " + t + " le_t " + le_t + " le_t.arg = " + le_t.argument)

    val l0: Location = "lc0"
    val l1: Location = "lc1"
    val l2: Location = "lc2"
    val locs = Set(l0, l1, l2)
    val clks = Map(t -> "t")
    val dim = clks.size

    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    val coeff_dec = new Coefficient(450)
    val le_dec = new Linear_Expression_Coefficient(coeff_dec)
    val coeff_ct = new Coefficient(ct)
    val le_ct = new Linear_Expression_Coefficient(coeff_ct)
    val coeff_lim_temp = new Coefficient(900)
    val le_lim_temp = new Linear_Expression_Coefficient(coeff_lim_temp)

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val inv1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv1.add_constraint(new Constraint(le_t, Relation_Symbol.LESS_OR_EQUAL, le_lim_temp))
    val inv2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    inv2.add_constraint(new Constraint(le_t, Relation_Symbol.LESS_OR_EQUAL, le_dec))
    val invM: InvMap = Map((l0 -> new NNC_Polyhedron(trueInv)), (l1 -> new NNC_Polyhedron(inv1)), (l2 -> new NNC_Polyhedron(inv2)))

    val g1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    //g1.add_constraint(new Constraint(le_t, Relation_Symbol.LESS_OR_EQUAL, le_ct))
    val g2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g2.add_constraint(new Constraint(le_t, Relation_Symbol.EQUAL, le_lim_temp))
    val g3 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    g3.add_constraint(new Constraint(le_t, Relation_Symbol.EQUAL, le_dec))

    val r: Reset = Set((t, 0))

    val t1: Transition = (l0, eps, g1, r, l1)
    val t2: Transition = (l1, "c", g2, r, l2)
    val t3: Transition = (l2, "h", g3, r, l1)
    val trans = Set(t1, t2, t3)	

    val controller = ("Controller", l0, locs, trans, clks, invM)
      controller	
  }

  //TC stands for TempControl
  def genTCIM(n: Int) = List.range(0,n).flatMap{i => List(List("c", "c"+i), List("h", "r"+i))}

  //DIS for TempControl. This should be gen automatically and moved to graphZone
  def genDis(n: Int, ct: Int, limI: Int, limS: Int) = {
    val disc = "Not(And(lc1, t < " + limS + ")), Not(And(lc2, t > "+ limI + "))"
    val c1 = "Not(And(lc1, t == " + limS +"))"
    val c2 = "Not(And(lc2, t == " + limI + "))"
    val indices = List.range(0, n)
    val res1 = indices.tail.foldLeft("Or(" + c1 + ", Not(And(l1, t0 >= " + ct + ")))")((r,c) => r + ", Or(" + c1 + ", Not(And(l" + (3*c+1) + ", t" + c + " >= "+ ct + ")))")
    val res2 = indices.tail.foldLeft("Or(" + c2 + ", Not(l2))")((r,c) => r + ", Or(" + c2 + ", Not(l" + (3*c + 2) + "))")
    ("And(" + disc + ", " + res1 + ", " + res2 + ", Not(lc0))")
  }

  def main(args: Array[String]) {
    ISLOCINT = if (args(0).toInt == 1) true else false
    val n = args(1).toInt
    val p = if (args.length < 3) 900 else args(2).toInt
    val ct = n * p

    //val ct = args(1).toInt * 900
    //    if (args.length > 2) 
    //      DEBUG_LEVEL = args(2).toInt

    if (args.length > 2) 
      DEBUG_LEVEL = args(2).toInt

    Parma_Polyhedra_Library.initialize_library()   

    val im = genTCIM(n)
    val ims = im.map{_.toSet}.toSet
    val imWithEps = ims + Set(eps)
    val indices = List.range(0, n)
    val ctroller = makeController(ct)
    val systemH = getTAH(ctroller)(imWithEps) +: indices.map{i => getTAH(makeRode(i, ct))(imWithEps)}
    //(0 to n).foreach{i => println(toString(system(i)) + "\n" + toString(systemH(i)))}

    val globalIni = "And(" + locProp("lc1") + ", " + indices.map{i => locProp("l" + (3*i+1))}.reduceLeft(_+", "+_) + ")"

/*
    def ordEqs(a: String) = indices.tail.map{i => hName + a + i + " - " + hName + a + (i-1) + " >= " + 1350}.reduceLeft(_+", "+_)

    val strengthen1 = globalIni + ", " + ordEqs("r")

    val strengthen = ordEqs("r")

    //println(genTCZ3(system, genTCIM(n), genDIS(im, system), "defaultZ3TC.py"))
    
    //println(genTCZ3(systemH, genTCIM(n), Map(("h", 1350), ("c", 1350)), "", "defaultZ3TC.py", strengthen, ii))
*/
    //println(genTCZ3(systemH, genTCIM(n), Map(("h", 1350), ("c", 1350)), "", "defaultZ3TC.py", "", ii))

    val ii = if (ISLOCINT) ("lc0 + lc1 + " + indices.map{i => "l" + (3*i+2)}.reduceLeft(_+" + "+_) + " == 1") else ""

    val ctroller1 = makeController(ct)
    val rd = computeDelta(ctroller1, "dummyClk")
    val deltas = rd._2
    println("#deltas = " + deltas)

    //println("#computeK = " + computeK(ctroller1))

    val z3Txt = genTCZ3(systemH, genTCIM(n), deltas, "", "defaultZ3TC.py", "", ii, true)

    val z3FilePath = "tc1503-" + n + "-" + ct + ".py"
    write2File(z3FilePath, z3Txt)
    val res = runZ3(z3FilePath)
    println("res = " + res)

    Parma_Polyhedra_Library.finalize_library()

  }
}

