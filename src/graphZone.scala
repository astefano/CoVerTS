package org

import scala.math.BigInt._
import parma_polyhedra_library._

import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException
import scala.util.control.Exception._

import scala.sys.process._

import scala.sys

case class ZoneGraph() {
//  val HISTCN = "histComp"
//  val HISTCLOC = "hcl"

  //constant to use in the name of the loc vector
  val LOCS = "l"

  //true if the locs are mapped into 0, 1 and false if the locs are bools (in Z3)
  var ISLOCINT = false 
  //var ISLOCINT = true
  
  val ISSEP = true//false

  //find a nice char to sep the ports in h_alpha (|, *, etc won't be ok for z3 python)
  val HSEP = ""

  var DEBUG_LEVEL = 0

  def debug(s: String, m: Int = 0) = if (DEBUG_LEVEL > m) println("#" + s)
  
  implicit val wd = System.getProperty("user.dir") + "/"

  try {
    //println("Debug: java.library.path= " + System.getProperty("java.library.path"))
    //System.load("/net/aconcagua/local/astefano/tools/lib/ppl/libppl_java.so")
    System.load(wd + "lib/libppl_java.so")
    //println(Parma_Polyhedra_Library.version())
  }
  catch {
    case e: UnsatisfiedLinkError =>
      println("Unable to load the library")
    println(e.getMessage())
    System.exit(-1)
  }

  val eps = "eps"
  //default name to be appended to history clocks
  val hName = "h"

  type Name = String
  type Location = String
  type Clock = Variable
  type Invariant = NNC_Polyhedron
  type Act = String
  type Guard = NNC_Polyhedron
  type Reset = Set[(Variable, Int)]  
  type Transition = (Location, Act, Guard, Reset, Location)
  type Zone = NNC_Polyhedron  
  type SymbolicState = (Location, Zone)    
  type InvMap = Map[Location, Invariant]
  type ClkMap = Map[Clock, String]

  //type TA = (Name, Location, Set[Location], Set[Transition], Map[Clock, String], InvMap)
  type TA = (Name, Location, Set[Location], Set[Transition], ClkMap, InvMap)
  type System = List[TA]

  type InteractionModel = Set[Set[String]]
  type InteractionModelExt = Set[(Set[String], Guard, Reset)]

  def getLoc(s: SymbolicState) = s._1
  def getZone(s: SymbolicState) = s._2
  
  def getIMfromExt(imext: InteractionModelExt) = imext.map{el => el._1}

  def mkIMClk(name: Set[String]) = hName + name.reduceLeft(_+ HSEP +_)

  //def mkHReset(hc: String) = Set((hc, ))

  //def mkIMH(im: InteractionModel) = im.map{alpha => (alpha, true, mkHReset(mkIMClk(alpha)))}

  /** getters from TA */
  def getName(ta: TA) = ta._1
  def getIni(ta: TA) = ta._2
  def getLocs(ta: TA) = ta._3
  def getTrans(ta: TA) = ta._4
  def getClkMap(ta: TA) = ta._5
  def getInvMap(ta: TA) = ta._6

  /** we fix the alph of a comp to be the set of acts appearing in the trans.*/
  def getAlph(ta: TA) = getTrans(ta).map{trans => getAct(trans)}

  /** getters from Transition */
  def getSource(t: Transition) = t._1
  def getAct(t: Transition) = t._2
  def getGuard(t: Transition) = t._3
  def getReset(t: Transition) = t._4
  def getSink(t: Transition) = t._5 
 
  def mkTrans(source: Location, p: Act, g : Guard, r: Reset, sink : Location) = (source, p, g, r, sink)

  def toString(t: Transition)(implicit clksM: Map[Clock, String] = Map()) : String = "(" + getSource(t) + ", " + getAct(t) + ", " + 
  //zone2String(getGuard(t),clksM) + ", " + reset2StrM(getReset(t))(clksM) + ", " + getSink(t) + ")"
  getGuard(t).toString + ", " + reset2StrM(getReset(t))(clksM) + ", " + getSink(t) + ")"

  //def toString(t: Transition) : String = "(" + getSource(t) + ", " + getAct(t) + ", " + getGuard(t).toString + ", " + getReset(t).map{el => (clksM(el._1), el._2)} + ", " + getSink(t) + ")"

  //def toString(r: Reset) : String = r.reduceLeft{(r, c) => r + ", (" + c._1.id + ", " + c._2 + ")"}
  def reset2Str(r: Reset) : String = r.map{el => "(" + el._1.id + ", " + el._2 + ")"}.toString

  def reset2StrM(r: Reset)(implicit clksM: Map[Clock, String] = Map()) = if (r.isEmpty) "" else r.map{el => (clksM.getOrElse(el._1, el._1.id) + "=" + el._2)}.reduceLeft(_+","+_)

  def toString(ta: TA) : String = {
    val clksM = getClkMap(ta)
    //getName(ta) + " = (" + getIni(ta) + ", " + getLocs(ta) + ", " + getTrans(ta).reduceLeft{(r,c) => r + "," + toString(c)(clksM)} + ", " + getInvMap(ta)
    getName(ta) + " = (" + getIni(ta) + ", " + getLocs(ta) + ",\n" + 
    getTrans(ta).map{t => toString(t)(clksM)}.reduceLeft(_+"\n"+_) + ",\n" + 
    getClkMap(ta).map{_._2} + ",\n" + 
    getInvMap(ta) + ")"
  }

  def toString(invsM: InvMap) : String = invsM.foldLeft("")((r,c) => r + "I(" + c._1 + ") = " + c._2 + " of dim " + c._2.space_dimension + ", ") 

  //def toString(clksM: ClkMap) : String = clksM.foldLeft("")((r,c) => r + c._1.id + " -> " + c._2) 

//  def ta2Str(ta: TA) : String = getName(ta) + " = (" + getIni(ta) + ", " + getLocs(ta) + ", " + getTrans(ta).map{t => toString(t)}.toString + ", " + getInvMap(ta)

  def getTransFromAct(ta: TA, a: String) = getTrans(ta).filter{ t => getAct(t) == a }

  /** internal acts are singletons in IM */
//  def getTAH(ta: TA)(implicit im: Set[Set[String]] = Set()) = {
  def getTAH(ta: TA)(implicit im: InteractionModel = Set()) = {
    var curClksMap = getClkMap(ta)
    var temp = Map[String, Clock]()
    val n = curClksMap.size
    val trans = getTrans(ta)
    val intActs = im.filter{alpha => alpha.size == 1}.map{_.toList.head}
    val extActs = trans.map{t => getAct(t)}.filter{a => !intActs(a)}.toList
    val indices = List.range(0, extActs.length)
    val ndim = extActs.length
    indices foreach {
      i => 
	//curClksMap += (hName + extActs(i) -> new Variable(n + i))
	val nclk = new Variable(n + i)
	val nclkName = hName + extActs(i)
	curClksMap += ( nclk -> nclkName)
        temp += (nclkName -> nclk)
    }

    val ntrans = trans.map{
      t => 
	val p = getAct(t)
	val hclkName = hName + p
	val ng = new NNC_Polyhedron(getGuard(t))	
	ng.add_space_dimensions_and_embed(ndim)
      if(!intActs(p)) {
	val nt = (getSource(t), p, ng, getReset(t) + ((temp(hclkName), 0)), getSink(t)) 
	//debug("for nt = " + toString(nt) + " the guard has dim = " + ng.space_dimension)
	nt      
      }
      //for internal (singletons) actions don't forget to redim the guard!!!
      else (getSource(t), p, ng, getReset(t), getSink(t)) 
    }

    val ninvsM = getInvMap(ta)
    ninvsM foreach {
      el => 
	//val z = NNC_Polyhedron(el._2)
	//z.add_space_dimensions_and_embed(ndim)
	el._2.add_space_dimensions_and_embed(ndim)
	//(el._1, z)
    }
    //debug("ninvsM = " + toString(ninvsM))
    (getName(ta) + hName, getIni(ta), getLocs(ta), ntrans, curClksMap, ninvsM)
  }

  def addDummyClk(ta: TA, clk: String) = {
    var curClksMap = getClkMap(ta)
    var temp = Map[String, Clock]()
    val n = curClksMap.size
    val nclk = new Variable(n)
    val nclkName = clk
    curClksMap += ( nclk -> nclkName)
    val trans = getTrans(ta)
    val ntrans = trans.map{
      t => 
	val p = getAct(t)
	val ng = new NNC_Polyhedron(getGuard(t))	
	ng.add_space_dimensions_and_embed(1)
       (getSource(t), p, ng, getReset(t), getSink(t)) 
    }
    val ninvsM = getInvMap(ta)
    ninvsM foreach {
      el => 
	el._2.add_space_dimensions_and_embed(1)
    }
    (getName(ta), getIni(ta), getLocs(ta), ntrans, curClksMap, ninvsM)
  }

/*
  def compose(taL: List[TA], im: Set[Set[String]]) = {
    val l0 = taL.map{ta => getIni(ta)}.mkString
  }
*/

  /** we want zone[r]
    * for an affine function \phi = (x_k'= <a,x>+b)) with "a" a vector and "b" \in R, the affine image of P is {\phi(v) | v \in P}
    * where \phi(v) is v where we change vk to \sum a_i*x_i + b,
    * so \phi(v) = (v0, .., vk = \sum a_i*x_i + b, .., v(n-1))
    * in PPL, the effective call is: P.affine_image(xk, \sum a_i*x_i + b, den)
    * where den normalises \sum a_i*x_i + b, i.e., the new value of xk will be (\sum a_i*x_i + b)/den.
    * A reset in TA is expressed as an affine transf, i.e., resetting a clock xk boils down to updating its value to 0, i.e., a = (0..0) and b = 0
    * so in PPL, we call P.affine_image(xk, 0, 1)
    */
//  def reset(zone: NNC_Polyhedron, toReset: List[Variable]) = {
  def reset(zone: NNC_Polyhedron, toReset: Reset) = {
    toReset foreach { 
    cV =>
      val clkname = cV._1
      val clkval = cV._2
      val coeff = new Coefficient(clkval)
      val le = new Linear_Expression_Coefficient(coeff)
      zone.affine_image(clkname, le, new Coefficient(1))
    }
    debug("after reset: " + zone)
    new NNC_Polyhedron(zone)
  }

  /** [r]zone*/
  def resetBck(zone: NNC_Polyhedron, toReset: Reset) = {
    val zoneCopy = new NNC_Polyhedron(zone)
    val vars = getVarsFromPolyhedron(zone)
    debug("before resetBck: " + zone + " with vars = " + vars.map{_.id})
    toReset foreach { 
    cV =>
      val clkname = cV._1
      val clkval = cV._2
      debug("resetback clk = " + clkname  + " with id " + clkname.id + " to val = " + clkval)
      val coeff = new Coefficient(clkval)
      val le = new Linear_Expression_Coefficient(coeff)
      zoneCopy.affine_preimage(clkname, le, new Coefficient(1))
    }
    debug("after resetBck: " + zoneCopy)
    //new NNC_Polyhedron(zone)
    zoneCopy
  }

//  def getVarsFromLinearExp(e: Linear_Expression): Set[Int] = e match {
  def getVarsFromLinearExp(e: Linear_Expression): Set[Variable] = e match {
    case lv: Linear_Expression_Variable => Set(lv.argument)//.id)
    case ls: Linear_Expression_Sum => getVarsFromLinearExp(ls.left_hand_side) ++ getVarsFromLinearExp(ls.right_hand_side)
    case ld: Linear_Expression_Difference => getVarsFromLinearExp(ld.left_hand_side) ++ getVarsFromLinearExp(ld.right_hand_side)
    case lt: Linear_Expression_Times => getVarsFromLinearExp(lt.linear_expression)
    case lm: Linear_Expression_Unary_Minus => getVarsFromLinearExp(lm.argument)
    case _ => Set()
  }

  def getVarsFromPolyhedron(p: Polyhedron) = {
    import collection.JavaConverters._
    val constraints = p.constraints.asScala
    val nc = constraints.size    
    val indices = List.range(0, nc)
    //val lr_sides = (for(i <- indices) yield Set(constraints(i).left_hand_side, constraints(i).right_hand_side)).toSet.flatten
    val lr_sides = (for(c <- constraints) yield Set(c.left_hand_side, c.right_hand_side)).toSet.flatten
    //println("lr = " + lr_sides)
    lr_sides.map{e => getVarsFromLinearExp(e)}.flatten
  }

  def getCtFromLinearExp(e: Linear_Expression) : Set[Int] = e match {
    case lcoeff: Linear_Expression_Coefficient => Set(lcoeff.argument.getBigInteger.intValue)
    case ls: Linear_Expression_Sum => getCtFromLinearExp(ls.left_hand_side) ++ getCtFromLinearExp(ls.right_hand_side)
    case ld: Linear_Expression_Difference => getCtFromLinearExp(ld.left_hand_side) ++ getCtFromLinearExp(ld.right_hand_side)
    case lt: Linear_Expression_Times => Set(lt.coefficient.getBigInteger.intValue) ++ getCtFromLinearExp(lt.linear_expression)
    case lm: Linear_Expression_Unary_Minus => getCtFromLinearExp(lm.argument)
    case _ => Set()
  }

  def getCtFromZone(z: Zone) = {
    import collection.JavaConverters._
    val constraints = z.constraints.asScala
    val nc = constraints.size    
    val lr_sides = (for(c <- constraints) yield Set(c.left_hand_side, c.right_hand_side)).toSet.flatten
    //println("lr = " + lr_sides)
    lr_sides.map{e => getCtFromLinearExp(e)}.flatten
  }

  /** @return true if e is a pos value
    */ 
  def isPosCt(e: Linear_Expression) = e match {
    case lcoeff: Linear_Expression_Coefficient => lcoeff.argument.getBigInteger.intValue >= 0 
    case _ => false
  }

  /** @return true if e is a pos value
    */ 
  def getVal(e: Linear_Expression) = e match {
    case lcoeff: Linear_Expression_Coefficient => lcoeff.argument.getBigInteger.intValue 
    case _ => Long.MinValue
  }

  def negOp(op: Relation_Symbol) = op match {
    case Relation_Symbol.LESS_THAN => Relation_Symbol.GREATER_OR_EQUAL
    case Relation_Symbol.LESS_OR_EQUAL => Relation_Symbol.GREATER_THAN
    case Relation_Symbol.GREATER_THAN => Relation_Symbol.LESS_OR_EQUAL
    case Relation_Symbol.GREATER_OR_EQUAL => Relation_Symbol.LESS_THAN
  }

  /** @return the opposite op: for <=, >= etc... */
  def oppositeOp(op: Relation_Symbol) = op match {
    case Relation_Symbol.LESS_THAN => Relation_Symbol.GREATER_THAN
    case Relation_Symbol.LESS_OR_EQUAL => Relation_Symbol.GREATER_OR_EQUAL
    case Relation_Symbol.GREATER_THAN => Relation_Symbol.LESS_THAN
    case Relation_Symbol.GREATER_OR_EQUAL => Relation_Symbol.LESS_OR_EQUAL
    case Relation_Symbol.EQUAL => Relation_Symbol.EQUAL
  }

  def negPolyhedron(p: Polyhedron) = {
    import collection.JavaConverters._
    val constraints = p.constraints.asScala
    val nc = constraints.size    
    val np = new NNC_Polyhedron(p.space_dimension, Degenerate_Element.UNIVERSE)
    constraints foreach {
      c => 
	np.add_constraint(new Constraint(c.left_hand_side, negOp(c.kind), c.right_hand_side))
    }
    np
  }

  /*
   * flashFwd Zone = {v + \delta | \delta \in \mathbb{R}, v \in Zone} owise said, v \in flashFwd Zone iff \exists \delta s.t. v - \delta \in Zone
   * P.time_elapse(Q) = {p + qt | t >= 0, p \in P, q \in Q}
   * so for Q the polyhedron consisting of 1 point (1,1,..,1), i.e., /\ x_i == 1 with x_i being the clocks in the TA, flashFwd Zone = Zone.time_elapse(Q)
   */
  def flashFwd(zone: Zone) = {
    val clocks = getVarsFromPolyhedron(zone).map{_.id}
    //println("clocks = " + clocks)
    val Q = new NNC_Polyhedron(clocks.size, Degenerate_Element.UNIVERSE)
    val le_1 = new Linear_Expression_Coefficient(new Coefficient(1))
    clocks foreach {
      x => 
	Q.add_constraint(new Constraint(new Linear_Expression_Variable(new Variable(x)), Relation_Symbol.EQUAL, le_1))
    }
    //val czone = new NNC_Polyhedron(zone)
    zone.time_elapse_assign(Q)
    new NNC_Polyhedron(zone)
    //czone
 }

  /*
   * flashBwd Zone = {v - \delta | \delta \in \mathbb{R}, v \in Zone} owise said, v \in flashFwd Zone iff \exists \delta s.t. v + \delta \in Zone
   * for Q the polyhedron consisting of 1 point (-1,-1,..,-1), i.e., /\ x_i == -1 with x_i being the clocks in the TA, flashBwd Zone = Zone.time_elapse(Q)
   */
  def flashBwd(zone: Zone, clocks: Set[Variable]) = {
    //val clocks = getVarsFromPolyhedron(zone).map{_.id}
    val Q = new NNC_Polyhedron(clocks.size, Degenerate_Element.UNIVERSE)
    val le_Minus1 = new Linear_Expression_Coefficient(new Coefficient(-1))
    clocks foreach {
      x => 
	//println("clock x = " + x)
	//Q.add_constraint(new Constraint(new Linear_Expression_Variable(new Variable(x)), Relation_Symbol.EQUAL, le_1))
      Q.add_constraint(new Constraint(new Linear_Expression_Variable(x), Relation_Symbol.EQUAL, le_Minus1))
    }
    val czone = new NNC_Polyhedron(zone)
    czone.time_elapse_assign(Q)    
    debug("in zone " + zone + " clocks = " + clocks.map{_.id} + " Q = " + Q + " czone = " + czone)
    czone
 }

//  def timeS(zone: NNC_Polyhedron, curr_invP: NNC_Polyhedron) = {
//  def timeS(zone: Zone, curr_invP: Invariant) = {
  def timeS(ss: SymbolicState, inv: InvMap) = {
    val loc = ss._1
    val zone = new NNC_Polyhedron(ss._2)
    val curr_invP = inv(loc)
    val flashFwdzone = flashFwd(zone)
    debug("after time_elapse: " + zone)
    zone.intersection_assign(curr_invP)
    debug("after intersection with cinv " + curr_invP + " : " + zone)
    (loc, new NNC_Polyhedron(zone))
  }

//  def discS(zone: NNC_Polyhedron, next_invP: NNC_Polyhedron, guardP: NNC_Polyhedron, toReset: List[Linear_Expression_Variable]) = {
//  def discS(zone: Zone, next_inv: Invariant, guard: Guard, toReset: Reset) = {
  def discS(ss: SymbolicState,t: Transition, inv: InvMap) = {    
    val guard = getGuard(t)
    val toReset = getReset(t)
    val curr_loc = ss._1
    val next_loc = getSink(t)
    val curr_inv = inv(curr_loc)
    val next_inv = inv(next_loc)
    val zone = new NNC_Polyhedron(ss._2)    
    debug("discS: t = " + toString(t) + " g.dim = " + guard.space_dimension + " zone = " + zone + " zone.dim = " + zone.space_dimension )
    zone.intersection_assign(guard)
    debug("after intersection with guard " + guard + " : " + zone)
    val nzone = reset(zone, toReset)
    //debug("before intersection with ninv " + next_inv + " ninv.dim = " + next_inv.space_dimension + " : " + nzone + " nzone.dim = " + nzone.space_dimension )
    nzone.intersection_assign(next_inv)
    debug("after intersection with ninv " + next_inv + " : " + nzone)
    (next_loc, new NNC_Polyhedron(nzone))
  }

//  def succ(zone: NNC_Polyhedron, curr_invP: NNC_Polyhedron, next_invP: NNC_Polyhedron, guardP: NNC_Polyhedron, toReset: List[Linear_Expression_Variable]) = {
//  def succ(zone: NNC_Polyhedron, curr_invP: NNC_Polyhedron, next_invP: NNC_Polyhedron, guardP: NNC_Polyhedron, toReset: List[Variable]) = {
  def succ(ss: SymbolicState,t: Transition, inv: InvMap) = {    
    val ns = timeS(discS(ss, t, inv), inv)
    val nloc = ns._1
    val nzone = new NNC_Polyhedron(ns._2)
    nzone.topological_closure_assign() 
    debug("after closure: " + nzone) 
    (nloc, new NNC_Polyhedron(nzone))
  }

  def succWithAct(ss: SymbolicState,t: Transition, inv: InvMap) = {    
    val ns = timeS(discS(ss, t, inv), inv)
    val nloc = ns._1
    val nzone = new NNC_Polyhedron(ns._2)
    nzone.topological_closure_assign() 
    debug("after closure: " + nzone) 
    ((nloc, new NNC_Polyhedron(nzone)), getAct(t))
  }

  def allSucc(ss: SymbolicState, lt: Set[Transition], inv: InvMap) = lt.filter(t => getSource(t) == ss._1).map(t => succ(ss, t, inv))

  def allSuccPairsWithActs(ss: SymbolicState, lt: Set[Transition], inv: InvMap) = lt.filter(t => getSource(t) == ss._1).map(t => succWithAct(ss, t, inv))

  //all clocks are equal and >= 0
  def init(clocks: Set[Clock]) = {
    val coeff_0 = new Coefficient(0)
    val le_0 = new Linear_Expression_Coefficient(coeff_0)
    // Constraint declarations
    val constraints = new Constraint_System()
    clocks foreach {
      ci => 
	val leci = new Linear_Expression_Variable(ci)
      //add that all clocks are >= 0
      val c = new Constraint(leci, Relation_Symbol.GREATER_OR_EQUAL, le_0)
      constraints.add(c)
      (clocks - ci) foreach {
	cj => 
	  val lecj = new Linear_Expression_Variable(cj)
	  val c = new Constraint(leci, Relation_Symbol.EQUAL, lecj)
	constraints.add(c)
      }
    }
    val ph = new NNC_Polyhedron(constraints)
    ph
  }

  import scala.collection.mutable.Stack

  def getMaxClkVal(ta: TA) = {
    val trans = getTrans(ta)
    val zonesInGuards = trans.map{t => getGuard(t)}.toSet
    val zonesInInvs = getInvMap(ta).map{_._2}.toSet
    val allZones = zonesInInvs ++ zonesInGuards
    val ctInResets = trans.map{t => getReset(t).map{_._2}}.flatten
    val ctInZones = allZones.map{z => getCtFromZone(z)}.flatten
    //println("getMaxClkVal: ctinzones = " + ctInZones)
    //println("getMaxClkVal: ctinresets = " + ctInResets)
    val m1 = if (!ctInZones.isEmpty) ctInZones.map{math.abs(_)}.max else 0
    val m2 = if (!ctInResets.isEmpty) ctInResets.map{math.abs(_)}.max else 0
    List(m1, m2).max
  }
  
  implicit var reachLim = 500

  def reach(ta: TA)(implicit clockCeiling: Map[Clock, Int] = Map[Clock, Int]()) = {
    debug("/***** reach for " + toString(ta) + " ********/\n")    
    val l0 = getIni(ta)
    val invl0 = getInvMap(ta)(l0)
    val trans = getTrans(ta)
    val clkM = getClkMap(ta)
    val clocks = clkM.keySet
    val m = getMaxClkVal(ta)
    val k = if (!clockCeiling.isEmpty) clockCeiling.map{el => (el._1.id->el._2)} else clocks.map{clk => (clk.id -> m)}.toMap
    //println("clkM = " + clkM + " clocks = " + clocks + " k = " + k)
    val inv = getInvMap(ta)
    val tovisit = new Stack[SymbolicState] 
    val initZ = init(clocks)
    initZ.intersection_assign(invl0)
    //tovisit.push((l0, initZ))
    //normalised init
    val ninitZ = normZone(initZ, k)
    tovisit.push((l0, ninitZ))   
    var visited : Set[SymbolicState] = Set()
    var i = 0
    while(tovisit!=Nil && i < reachLim) {
      i += 1
      val s = tovisit.pop
      if (!(visited contains s)) {	
	val nz = new NNC_Polyhedron(getZone(s))
	debug("adding s = " + makeStateProp(s, clkM) + " to visited = " + visited.map{s => makeStateProp(s, clkM)})//, 1)
	visited = visited + ((getLoc(s), nz))
	val succs =  allSucc(s, trans, inv)
	debug("succs = " + succs.map{s => makeStateProp(s, clkM)})//, 1)
	succs foreach { 
	  s => 
	    //val ns = (s._1, s._2)
	    val nZ = normZone(s._2, k)
	    //debug("NORM: z = " + zone2String(s._2, clkM) + " normalised z = " + zone2String(nZ, clkM), -1)
	    val ns = (getLoc(s), nZ)
	    tovisit.push(ns)
	}
      }
    }    
    debug("#stopped at i = " + i,-1)
    visited
  }

  def reachActs(ta: TA)(implicit clockCeiling: Map[Clock, Int] = Map[Clock, Int]()) = {
    debug("/***** reach for " + toString(ta) + " ********/\n")    
    val l0 = getIni(ta)
    val invl0 = getInvMap(ta)(l0)
    val trans = getTrans(ta)
    val clkM = getClkMap(ta)
    val clocks = clkM.keySet
    val m = getMaxClkVal(ta)
    val k = if (!clockCeiling.isEmpty) clockCeiling.map{el => (el._1.id->el._2)} else clocks.map{clk => (clk.id -> m)}.toMap
    //println("clkM = " + clkM + " clocks = " + clocks + " k = " + k)
    val inv = getInvMap(ta)
    val tovisit = new Stack[SymbolicState] 
    val initZ = init(clocks)
    initZ.intersection_assign(invl0)
    //tovisit.push((l0, initZ))
    //normalised init
    val ninitZ = normZone(initZ, k)
    tovisit.push((l0, ninitZ))   
    var visited : Set[SymbolicState] = Set()
    var res : Set[(SymbolicState, Act, SymbolicState)] = Set()
    var i = 0
    while(tovisit!=Nil && i < reachLim) {
      i += 1
      val s = tovisit.pop
      if (!(visited contains s)) {	
	val nz = new NNC_Polyhedron(getZone(s))
	debug("adding s = " + makeStateProp(s, clkM) + " to visited = " + visited.map{s => makeStateProp(s, clkM)})//, 1)
	visited = visited + ((getLoc(s), nz))
	val succsWithActs =  allSuccPairsWithActs(s, trans, inv)
	succsWithActs foreach { 
	  sa => 
	    val cs = sa._1
	    val a = sa._2
	    //val ns = (s._1, s._2)
	    val nZ = normZone(cs._2, k)
	    //debug("NORM: z = " + zone2String(s._2, clkM) + " normalised z = " + zone2String(nZ, clkM), -1)
	    val ns = (getLoc(cs), nZ)
	    tovisit.push(ns)
	    res += ((s, a, ns))
	}
      }
    }    
    debug("#stopped at i = " + i,-1)
    res
    //visited
  }

  def project(z: Zone, x: Linear_Expression_Variable) = {
    import collection.JavaConverters._
    val constraints = z.constraints.asScala
    val ncs = new Constraint_System()
    constraints.foreach{
      c => 
	if (c.left_hand_side == x || c.right_hand_side == x) ncs.add(c)
    }
    ncs
  }
  
 def msol(z: Zone, linhclk: Linear_Expression_Variable) = {
   //debug("finding min for " + z.constraints)
   println("finding min for " + z.constraints)
   val pr = new MIP_Problem(z.space_dimension, z.constraints, linhclk, Optimization_Mode.MINIMIZATION)
   val nDp = pr.optimizing_point()
   val nDpV = getCtFromLinearExp(nDp.linear_expression).head
   debug("computeDelta: nDp = " + nDp + " ndp.linexp = " + nDpV)
   nDpV
 }

  val maxOcc = Int.MaxValue

  /** i have a pr with strict ineqs */
  def matTE(ta: TA) = {
    val hclk = "te"
    val ta1 = addDummyClk(ta, hclk)
    //debug("computeDelta: ta " + toString(ta))    
    val clkM = getClkMap(ta1)
    val clocks = clkM.keySet
    val m = getMaxClkVal(ta1)
    val k = clocks.map{clk => (clk.id -> m)}.toMap
    //debug("matTE: clocks = " + clkM)
    val varhclk = clkM.filter{e => e._2 == hclk}.head._1
    val linhclk = new Linear_Expression_Variable(varhclk)

    val reachA = reachActs(ta1)
    val states = reachA.map{_._1}.toList
    val acts = getAlph(ta).toList.sorted
    val nacts = acts.length
    val ns = states.length
    //the max of act appearances in reach
    val maxApp = acts.map{a => reachA.filter(_._3 == a).size}.max
    //tm(i,j,k,p) = the min time to do p actions acts[k] from states[i] to states[j]
    val tm = Array.fill(ns,ns,nacts, maxApp)(maxOcc)
    var res = Map[(Location, Act, Location, Int), Int]()
    val sindices = List.range(0, ns)
    val aindices = List.range(0, nacts)
    val pindices = List.range(0, maxApp-1)
    reachA foreach {
      el => 
	val source = el._1
	val a = el._2
	val sink = el._3
	val nz = normZone(getZone(sink), k)
	tm(states.indexOf(source))(states.indexOf(sink))(acts.indexOf(a))(1) =  msol(nz, linhclk)
    }
    for(i<- sindices; j <- sindices; k <- aindices; pi <- pindices) {
      val tmaux = for(l <- sindices; m <- aindices) yield tm(i)(l)(m)(pi) + tm(l)(j)(k)(1)
      tm(i)(j)(k)(pi+1) = tmaux.toList.min
    }
    for(i<- sindices; j <- sindices; k <- aindices; pi <- pindices) {
      val v = tm(i)(j)(k)(pi)
      if (v < maxOcc) res += ((getLoc(states(i)), acts(k), getLoc(states(j)), pi) -> v)
    }
    res
  }

  /** @return the minimum time elapse from the ini loc until p occurences of a
    */ 
  def occ(ta: TA, n: Int, a: Act) = {
    val res = matTE(ta) 
    val ini = getIni(ta)
    res.filter{p => p._1._1 == ini && p._1._2 == a && p._1._4 == n}.map{_._2}.min
  }

  /**@return a map associating to each act a its ka as in Remark 3, Verimag report
    */ 
  def computeK(ta: TA) = {
    val acts = getAlph(ta)
    val res = matTE(ta) 
    val ini = getIni(ta)
    var ks = Map[Act, Int]()
    acts foreach {
      a => 
	val tea = res.filter{p => p._1._1 == ini && p._1._2 == a}.map{p => (p._1._4 -> p._2)}
	val maxAppa = res.keySet.map{_._4}.toList.max
	var mina = tea(1)
	List.range(1,maxAppa-1) foreach {
	  i => 
	    val nv = tea(i+1) - tea(i)
	    if (nv < mina) mina = nv
	}
      ks += (a -> mina)
    }
    ks
  }

  def computeDelta(ta0: TA, hclk: String)(implicit clockCeiling: Map[Clock, Int] = Map[Clock, Int]()) = {
    val ta = addDummyClk(ta0, hclk)
    debug("computeDelta: ta " + toString(ta))    
    val l0 = getIni(ta)
    val trans = getTrans(ta)
    //val deltas = trans.map{t => (getAct(t) -> new NNC_Polyhedron(1, Degenerate_Element.UNIVERSE))}.toMap
    val clkM = getClkMap(ta)
    val clocks = clkM.keySet
    debug("computeDelta: clocks = " + clkM)
    val varhclk = clkM.filter{e => e._2 == hclk}.head._1
    val linhclk = new Linear_Expression_Variable(varhclk)
    val m = getMaxClkVal(ta)
    debug("computeDelta: m = " + m)
    var deltas = trans.filter{t => getAct(t) != eps}.map{t => (getAct(t) -> m*trans.size)}.toMap
    val k = if (!clockCeiling.isEmpty) clockCeiling.map{el => (el._1.id->el._2)} else clocks.map{clk => (clk.id -> m)}.toMap
    //println("clkM = " + clkM + " clocks = " + clocks + " k = " + k)
    val inv = getInvMap(ta)
    val tovisit = new Stack[SymbolicState] 
    val initZ = init(clocks)
    //normalised init
    val ninitZ = normZone(initZ, k)
    tovisit.push((l0, ninitZ))
    var visited : Set[SymbolicState] = Set()
    var i = 0
    while(tovisit!=Nil && i < reachLim) {
      i += 1
      val s = tovisit.pop
      if (!(visited contains s)) {	
	val nz = new NNC_Polyhedron(s._2)
	debug("computeDelta: adding s = " + makeStateProp(s, clkM) + " to visited = " + visited.map{s => makeStateProp(s, clkM)})//, 1)
	visited = visited + ((s._1, nz))
	val succs = trans.filter(t => getSource(t) == s._1).map(t => (getAct(t), succ(s, t, inv)))
	debug("computeDelta: succs = " + succs.map{s => makeStateProp(s._2, clkM)})//, 1)
	succs foreach { 
	  sp => 
	    val p = sp._1
	    val s = sp._2
	    val nZ = normZone(s._2, k)
	    //val projH = project(nZ, linhclk)//clksM(hclk))
	    //debug("computeDelta: projH = " + projH)

	    if (p != eps) {
	      val oldDp = deltas(p)
	      
	      //val pr = new MIP_Problem(1, projH, linhclk, Optimization_Mode.MINIMIZATION)
	      debug("Solving pr = " + zone2String(s._2, clkM))
	      val pr = new MIP_Problem(s._2.space_dimension, s._2.constraints, linhclk, Optimization_Mode.MINIMIZATION)
	      val nDp = pr.optimizing_point()
	      val nDpV = getCtFromLinearExp(nDp.linear_expression).head
	      debug("computeDelta: nDp = " + nDp + " ndp.linexp = " + nDpV)
	      if (oldDp > nDpV) deltas = deltas.updated(p, nDpV) 
	    }
	    //debug("NORM: z = " + zone2String(s._2, clkM) + " normalised z = " + zone2String(nZ, clkM), -1)
	    val ns = (s._1, nZ)
	    tovisit.push(ns)
	}
      }
    }    
    //debug("stopped at i = " + i,-1)
    (visited, deltas)
  }

  //65 is 'A'; 48 is '0'
  def getVarNameFromId(id: Long) = {
    val letter = ((id % 26) + 65).toChar.toString
    val q = (id / 26)
    val index = if (q > 0) (q + 48).toChar else ""
    letter + index
  }

  def zone2String(zone: NNC_Polyhedron, clksMap: Map[Variable, String]) = {
    //vars should be of the form (0, 1, 2...)
    //val vars = getVarsFromPolyhedron(zone).toList.map{_.id} 
    val vars0 = getVarsFromPolyhedron(zone).toList
    val vars = vars0.map{_.id}.distinct
    val nmap = clksMap.map{el => (el._1.id -> el._2)}    
    
    //val lettersM = vars.map{i => ((i + 65).toChar -> i)}.toMap
    val lettersM = vars.map{i => (getVarNameFromId(i) -> i)}.toMap
    val letters = lettersM.keySet.toList.sortBy(-_.size)
    //zoneS.toString has default A, B, C... notation for vars; so i replace them with the names i keep in the clksMap
    var zoneS = zone.toString
    debug("zone = " + zone + "\nvars = " + vars + "\nnmap = " + nmap + "\nlettersM = " + lettersM + "\nletters = " + letters)
    if (zoneS == "true") zoneS
    else {
      letters foreach {l => zoneS = zoneS.replace(l.toString, nmap(lettersM(l)))}
      //replace " = " with " == " for Z3
      val res = zoneS.replace(" = ", " == ")      
      //debug("zone = " + zone + " clksMap = " + clksMap.map(el => (el._1.id, el._2)) + " transf. zone = " + res)
      res
    }
  }

  def locProp(l: Location) = if (!ISLOCINT) l else {
    //maybe l is a global loc, i.e., a string l1, l2, ...
    val locs = l.split(",")
    if (locs.length <= 0) l + " == 1" else (locs.reduceLeft(_  + " == 1, " + _) + " == 1")
  }

  def makeStateProp(s: SymbolicState, clksMap: Map[Variable, String]) = {
    val zoneS = zone2String(s._2, clksMap)
    val locP = locProp(s._1)
    "And("  + (if (zoneS == "true") locP else locP + ", " + zoneS) + ")"
  }

  /** map a pair (l, Set(z1, ..., zk)) into And(locProp(l), Or(zone2string(z1), ..., zone2string(zk)))*/
  def makeMultipleProp(l: Location, zones: Set[Zone], clksMap: Map[Variable, String]) = {
    val zonesStr0 = zones.map{z => zone2String(z, clksMap)}.filter(_!="true").map{x => "And(" + x +")"}    
    val zonesStr = if (zonesStr0.isEmpty) "" else if (zonesStr0.size==1) zonesStr0.head else "Or(" + zonesStr0.reduceLeft(_+", "+_) + ")"
    val locP = locProp(l)
    if (zonesStr == "") locP else "And(" + locP + ", " + zonesStr + ")"
  }

  //def post(ta: TA) = "Or(" + reach(ta).foldLeft("")((r, c) => r + ", " + makeStateProp(c, getClkMap(ta))).drop(1) + ")"  
  def post(ta: TA) = {
    val clks = getClkMap(ta)
    val rs = reach(ta).groupBy(_._1).map{x => (x._1, x._2.map{_._2})}
    if (rs.isEmpty) "false"
    else if (rs.size == 1) makeMultipleProp(rs.head._1, rs.head._2, clks)
    else "Or(" + rs.foldLeft("")((r,c) => r + ", " + makeMultipleProp(c._1, c._2, clks)).drop(1) + ")"
  }

  /** Gen Eqs from IM */

  //the name of the history clock
  val hcname = "h"
  //default prefix to be used in the names of the local invs
  val INV = "Inv"

  def getEqsC(im: InteractionModel) = {
    val imClks = im.map{alpha => (alpha, mkIMClk(alpha))}.toMap
    val ports = im.flatten.filter{_!= eps}
    "And(" + ports.map{
      p => 
	val cp = (hcname + p) + " == "
	val imp = im.filter{alpha => alpha(p)}
	//for each alpha containing p
	if (imp.size > 1) {
	  "Or(" + imp.map{
	    alpha => 
	      //  /\_beta alpha <= beta 
	      val alphaClkMins = (imp - alpha).map{beta => imClks(alpha) + " <= " + imClks(beta)}
	      val alphaClkMinConj = if (alphaClkMins.size > 1) "And(" + alphaClkMins.reduceLeft(_+", "+_) + ")" else alphaClkMins.head
	    "And(" + cp + imClks(alpha) + ", " + alphaClkMinConj + ")"
	  }.reduceLeft(_+", "+_) + ")"
	}
      else cp + imClks(imp.head)
    }.reduceLeft(_+", "+_) + ")"    
  }

  def getSepP(im: InteractionModel, p: String, deltap: Int, isSym: Boolean = false) = {
    val imp = im.filter{alpha => alpha(p)}
    //println("getSepP p = " + p + " imp = " + imp + " dp = " + deltap)
    if (imp.size > 1) {
      val impClks = imp.map{alpha => mkIMClk(alpha)}.toList    
      val indices = List.range(0, impClks.length)
      //val absdiffs = for(halpha <- impClks; hbeta <- impClks; if (halpha != hbeta)) yield "Or(" + halpha + " - " + hbeta + " >= " + deltap + ", " + hbeta + " - " + halpha  + " >= " + deltap + ")"
      if (!isSym) {
	val absdiffs = for(i <- indices; j <-indices.drop(i+1); val halpha = impClks(i); val hbeta = impClks(j)) yield "Or(" + halpha + " - " + hbeta + " >= " + deltap + ", " + hbeta + " - " + halpha  + " >= " + deltap + ")"
	if (absdiffs.size > 1) "And(" + absdiffs.reduceLeft(_+", "+_) + ")" else absdiffs.head
      }
      else {
	//if symm then it's enough to constr: /\_i h_a_i - h_a_{i+1} >= dp
	val indicesWithoutLast = List.range(0, impClks.length - 1)
	val absdiffs = (for(i <- indicesWithoutLast; val halpha = impClks(i); val hbeta = impClks(i+1)) yield (halpha + " - " + hbeta + " >= " + deltap))
	//val absdiffs = absdiffs0 :+ (impClks.last + " - " + impClks.head + " >= " + deltap)
	if (absdiffs.size > 1) "And(" + absdiffs.reduceLeft(_+", "+_) + ")" else absdiffs.head
      
      }
    }
    else ""
  }  

  def getSep(im: InteractionModel, portdeltas: Map[String, Int], isSym: Boolean = false) = {
    val ports = im.flatten.filter{_!=eps}
    val res = ports.map{p => getSepP(im, p, portdeltas.getOrElse(p, 0),isSym)}.filter{_ != ""}
    if (res.isEmpty) "True"
    else "And(" + res.reduceLeft(_+", "+_) + ")"
  }

  def eqInteraction(alpha: List[String]) = {
    val indices = List.range(0, alpha.length)
    val eqs0 = for(i <- indices; j <- indices.dropWhile(_<=i)) yield hcname + alpha(i) + " == " + hcname + alpha(j)
    val eqs = eqs0.toList
    if (eqs == List()) "" 
    else if (eqs.length == 1) eqs(0)
    else eqs.tail.foldLeft("And(" + eqs(0))((r, c) => r + ", " + c) + ")"
  }

  def leqInteraction(alpha: List[String], im: List[List[String]]) = {
    //the name of the history clock
    val a = alpha.head
    val portsIM = im.flatten.distinct
    val ineqs = for(p <- portsIM) yield hcname + a + " <= " + hcname + p
    if (ineqs.length > 1) 
      ineqs.tail.foldLeft("And(" + ineqs(0))((r, c) => r + ", " + c) + ")"
    else ineqs.mkString
  }

  /** returns \gamma \ominus \alpha as on the slides. 
    */ 
  def imdiff(alpha: List[String], im: List[List[String]]) = im.map{el => (el.toSet -- alpha.toSet).toList}.filter{el => el.length >= 1}

  /** returns \eqs(\gamma) as on the slides. the impl is precisely the rec def, so the resulting formulae may be huge.
    * you might want to use `getEqsSimpl` instead.
    */ 
  def getEqs(im: List[List[String]]) : String = {
    //println("im = " + im)
    if (im == List()) ""
    else if (im.length <= 1) eqInteraction(im.head) 
    else {
      //val c = im.head
      //val h = "And(" + eqInteraction(c) + ", " + leqInteraction(c, imdiff(c, im)) + ", " + getEqs(imdiff(c, im)) + ")"
      val res = for { 
	  alpha <- im; 	
	  val eqAlpha = eqInteraction(alpha); 
	  val leq = leqInteraction(alpha, imdiff(alpha, im));
	  val rem = getEqs(imdiff(alpha, im).filter{_.length > 1})
	  } yield "And(" + (eqAlpha + (if (leq != "") (", " + leq) else "") + (if (rem != "") (", " + rem) else "")) + ")"
      "Or(" + res.tail.foldLeft(res(0))((r,c) => r + ", " + c) + ")"
    }
  }

  /** returns \eqs(\gamma) as on the slides. it makes use of disjointness, s.t. the resulting formulae are minimal in size.
    */ 
  def getEqsSimpl(im: List[List[String]]) : String = {
    //println("#im = " + im)
    if (im == List()) ""
    else if (im.length <= 1 && im.head != eps) eqInteraction(im.head) 
    else {   
      val alpha = im.head
      val (p1, p2) = im.tail.partition(alphai => (alphai.toSet intersect alpha.toSet) == Set())
      if (p1 != List()) {
	val p1Eqs = getEqsSimpl(p1)
	val p2Eqs = getEqsSimpl(alpha +: p2)
	if (p1Eqs != "") {
	  if (p2Eqs != "")
	    "And(" + p1Eqs + ", " + p2Eqs + ")"
	  else p1Eqs
	}
	else p2Eqs
      }
      else {
	val res = for { 
	  alpha <- im; 	
	  val eqAlpha = eqInteraction(alpha); 
	  val leq = leqInteraction(alpha, imdiff(alpha, im));
	  val rem = getEqsSimpl(imdiff(alpha, im).filter{_.length > 1});
	  val all = List(eqAlpha, leq, rem).filter(_!="");
	  if (all != List())
	} //yield "And(" + (if (eqAlpha != "") + (if (leq != "") (", " + leq) else "") + (if (rem != "") (", " + rem) else "")) + ")"
	yield "And(" + all.reduceLeft(_+ ", " +_) + ")"
	"Or(" + res.tail.foldLeft(res(0))((r,c) => r + ", " + c) + ")"
      }
    }
  }


  /** Gen strings repr Z3 formulae */
  def genDeclLocsTA(ta: TA) = {
    val locs = getLocs(ta).toList
    val names = locs.tail.foldLeft(locs(0))((r, c) => r + ", " + c)
    val body = locs.tail.foldLeft(locs(0))((r, c) => r + " " + c)
    val typeLocs = if (ISLOCINT) "Ints" else "Bools"
    (names + " = " + typeLocs + "('" + body + "')")
  }

  def genDeclLocsSystem(s: System) = s.tail.foldLeft(genDeclLocsTA(s(0)))((r,c) => r + "\n" + genDeclLocsTA(c))

  def genDeclClksTA(ta: TA) = {
    val clks = getClkMap(ta).map{_._2}.toList
    val names = clks.tail.foldLeft(clks(0))((r, c) => r + ", " + c)
    val body = clks.tail.foldLeft(clks(0))((r, c) => r + " " + c)
    (names + " = Ints('" + body + "')")    
  }

  def genDeclClksSystem(s: System) = s.tail.foldLeft(genDeclClksTA(s(0)))((r,c) => r + "\n" + genDeclClksTA(c))

  def genAt2LocsTA(ta: TA) = {
    val locs = getLocs(ta).toList
    if (locs.length < 0) "False"    
    else if (locs.length == 2) "And(" + locs(0) + ", " + locs(1) + ")"
    else {
	val indices = List.range(0, locs.length)
	val pairs = for(i <- indices; j <- indices.dropWhile(_<=i)) yield "And(" + locs(i) + ", " + locs(j) + ")"
	"Or(" + pairs.tail.foldLeft(pairs(0))((r, c) => r + ", " + c) + ")"
     }
  }

  def genNotAt2LocsTA(ta: TA) = {
    if (ISLOCINT) {
      val locs = getLocs(ta).toList
      val sum = locs.reduceLeft(_+ "+" +_) + " == 1"
      val bigger0  = locs.reduceLeft(_+ " >= 0, "+_) + " >= 0"
      "And(" + bigger0 + ", " + sum + ")"
    }
    else "Not(" + genAt2LocsTA(ta) + ")"
  }

  def genAt2LocsSystem(s: System) = "Or(" + s.tail.foldLeft(genAt2LocsTA(s(0)))((r,c) => r + "," + genAt2LocsTA(c)) + ")"

  def genLocalInvTA(ta: TA) = "And(" + post(ta) + ", " + genNotAt2LocsTA(ta) + ")"

  //def genLocalInvs(s: System) = s.tail.foldLeft(INV + getName(s(0)) + " = " + post(s(0)))((r, c) => r + "\n" + (INV + getName(c) + " = " + post(c)))

  /** en(a,t) = at(l) \wedge ( (flashback(g) \wedge inv(l)) \ (flashback(flashback(g)\I)) ) , where t = (l, a, g, r, l')  */
  def enTrans0(t: Transition, I: Invariant, clksM: Map[Clock, String]) = {
    val clks = clksM.keySet
    val g = new NNC_Polyhedron(getGuard(t))
    val flashBwdG = flashBwd(g, clks)
    debug("for g = " + g + " flasback(g) = " + flashBwdG)
    val loc = getSource(t)
    val aux1 = new NNC_Polyhedron(flashBwdG)
    // flashback(g)\I
    aux1.difference_assign(I)
    debug("for I = " + I + " flashback(g) - I = " + aux1)
    val aux2 = new NNC_Polyhedron(aux1)
    //(flashback(flashback(g)\I)) )
    val rightDiff = flashBwd(aux2, clks)
    debug("for I = " + I + " flashback(flashback(g) - I) = " + rightDiff)
    val copyI = new NNC_Polyhedron(I)
    // (flashback(g) \wedge inv(l))
    copyI.intersection_assign(flashBwdG)
    debug("for I = " + I + " flashback(g) wedge I = " + copyI)
    val diff = new NNC_Polyhedron(copyI)
    diff.difference_assign(rightDiff)
    debug("for g = " + g + " and I = " + I + " flashback(g) wedge inv(l) - flashback(g) wedge inv(l) = " + diff)
    val ss = (loc, diff)
    makeStateProp(ss, clksM)
  }

  /** en(a,t) = at(l) \wedge ( (flashback(g) \wedge inv(l')) where t = (l, a, g, r, l')  */
  //def enTrans(t: Transition, I: Invariant, In: Invariant, clksM: Map[Clock, String]) = {
  def enTrans(t: Transition, In: Invariant, clksM: Map[Clock, String]) = {
    val clks = clksM.keySet    
    val guard = new NNC_Polyhedron(getGuard(t))    
    val toReset = getReset(t)
    val resetIn = resetBck(In, toReset)
    val gIn = new NNC_Polyhedron(guard)
    gIn.intersection_assign(resetIn)
    debug("enTrans : clksM = " + clksM.map{e => (e._1.id, e._2)})
    //G.concatenate_assign(flashBwd(GI, clks))
    val flashbgIn = flashBwd(gIn, clks)
    debug("enTrans: guard = " + guard + ", In = " + In + ", resetIn = " + resetIn + "\n gIn = " + gIn + ", flashback(g wedge [r]In) = " + flashbgIn)
    val ss = (getSource(t), flashbgIn)
    makeStateProp(ss, clksM)
  }

  def enActTrans(a: String, t: Transition, ta: TA) = {
    require (getAct(t) == a, println("[Err in enActTrans]: transition " + t + " is not labelled with act " + a + "."))  
    val clksM = getClkMap(ta)
    val clks = clksM.keySet
    val g = new NNC_Polyhedron(getGuard(t))
    val flashBwdG = flashBwd(g, clks)
    debug("for g = " + g + " flasback(g) = " + flashBwdG)
    val loc = getSource(t)
    val I = getInvMap(ta)(loc)
    val aux1 = new NNC_Polyhedron(flashBwdG)
    // flashback(g)\I
    aux1.difference_assign(I)
    debug("for I = " + I + " flashback(g) - I = " + aux1)
    val aux2 = new NNC_Polyhedron(aux1)
    //(flashback(flashback(g)\I)) )
    val rightDiff = flashBwd(aux2, clks)
    debug("for I = " + I + " flashback(flashback(g) - I) = " + rightDiff)
    val copyI = new NNC_Polyhedron(I)
    // (flashback(g) \wedge inv(l))
    copyI.intersection_assign(flashBwdG)
    debug("for I = " + I + " flashback(g) wedge I = " + copyI)
    val diff = new NNC_Polyhedron(copyI)
    diff.difference_assign(rightDiff)
    debug("for g = " + g + " and I = " + I + " flashback(g) wedge inv(l) - flashback(g) wedge inv(l) = " + diff)
    val ss = (loc, diff)
    makeStateProp(ss, clksM)
  }

  def enAct(a: String, system: System) = {
    val tasWithA = system.filter{ta => (getTrans(ta).filter{t => getAct(t) == a}).size > 0}
    require(a == eps || (a != eps && tasWithA.length == 1), println("[Err in enAct]: expected only 1 TA to have act " + a + " but found " + tasWithA.length + " instead.")) 
    val enCs = tasWithA.map{
      ta => 
	val transWithA = getTrans(ta).filter{t => getAct(t) == a}
      val res = transWithA.map{t => enActTrans(a, t, ta)}.toList
      if (res.length == 1) res.head
      else "Or(" + res.tail.foldLeft(res.head)((r, c) => r + " ," + c) + ")"
    }
    "And(" + enCs.reduceLeft(_+", "+_) + ")"
  }

  def renameLinExp(e: Linear_Expression, clksM: Map[Clock, String], revClksGM: Map[String, Clock]) : Linear_Expression = e match {   
    case lv: Linear_Expression_Variable => {
//      debug("lv = " + lv + " lv.arg = " + lv.argument + " lv.id = " + lv.argument.id + " revClksGM = " + revClksGM.map{x => (x._1, x._2.id)} + " clksM = " + clksM.map{x => (x._2, x._1.id)} + " clksM = " + clksM)
      val clkId = lv.argument.id
      //new Linear_Expression_Variable(revClksGM(clksM(lv.argument)))
      new Linear_Expression_Variable(revClksGM(clksM.filter(c => c._1.id == clkId).head._2))
    }
    case ls: Linear_Expression_Sum => new Linear_Expression_Sum(renameLinExp(ls.left_hand_side, clksM, revClksGM), renameLinExp(ls.right_hand_side, clksM, revClksGM))
    case ld: Linear_Expression_Difference => new Linear_Expression_Difference(renameLinExp(ld.left_hand_side, clksM, revClksGM), renameLinExp(ld.right_hand_side, clksM, revClksGM))
    case lt: Linear_Expression_Times => new Linear_Expression_Times(lt.coefficient, renameLinExp(lt.linear_expression, clksM, revClksGM))
    case lm: Linear_Expression_Unary_Minus => new Linear_Expression_Unary_Minus(renameLinExp(lm.argument, clksM, revClksGM)) 
    case lcoeff: Linear_Expression_Coefficient => lcoeff
  }

  def renameConstraint(c: Constraint, clksM: Map[Clock, String], revClksGM: Map[String, Clock]) = {
    val nc = new Constraint(renameLinExp(c.left_hand_side, clksM, revClksGM), c.kind, renameLinExp(c.right_hand_side, clksM, revClksGM))
    debug("c = " + c + " revClksGM = " + revClksGM.map{x => (x._1, x._2.id)} + " renamed c = " + nc)
    nc
  }

  /** @return the zone where we renamed the clocks in clksM wrt clocks in clksGM
    * It calls renameLinExp for the left, right sides of each constraint.
    */
  def renameZone(z: Zone, clksM: Map[Clock, String], clksGM: Map[Clock, String]) = {
    val revClksGM = clksGM.map{e => (e._2 -> e._1)}
    import collection.JavaConverters._
    val constraints = z.constraints.asScala
    val nc = constraints.size    
    //val nz = new NNC_Polyhedron(z.space_dimension, Degenerate_Element.UNIVERSE)
    val nz = new NNC_Polyhedron(clksGM.size, Degenerate_Element.UNIVERSE)
    constraints foreach {
      c => 
	nz.add_constraint(renameConstraint(c, clksM, revClksGM))
    }
    nz      
  }

  /** @return the resets where we renamed the clocks in clksM wrt clocks in clksGM
    */
  def renameReset(toReset: Reset, clksM: Map[Clock, String], clksGM: Map[Clock, String]) = {
    val revClksGM = clksGM.map{e => (e._2 -> e._1)}
    toReset.map{r => (revClksGM(clksM(r._1)), r._2)}
  }


  /** @return the normalised zone as in the tutorial of Uppaal:
    * for op \in {<=, <} remove each x op m and x - y op m for m > k(x)
    * for op \in {>=, >} transf each x op m and x - y op m into x > k(x), resp. x - y > k(x) for m > k(x)
    * where k is a clock ceiling
    */
  def normZone(z: Zone, k: Map[Long, Int]) = {
    import collection.JavaConverters._
    val constraints = z.constraints.asScala
    val nc = constraints.size    
    //val nz = new NNC_Polyhedron(z.space_dimension, Degenerate_Element.UNIVERSE)
    val nz = new NNC_Polyhedron(k.size, Degenerate_Element.UNIVERSE)
    constraints foreach {
      c => 
	var lhs = c.left_hand_side
	var op = c.kind
	var rhs = c.right_hand_side
	var rhsVal = getVal(rhs)	  
	if (rhsVal < 0) {
	  op = oppositeOp(op)
	  lhs = lhs.unary_minus
	  rhsVal = 0 - rhsVal	  
	}
	//take any clock in the lhs; check if it's correct to pick any, i.e., if lhs=(x - y) and i pick y is it fine?? 
        val x = getVarsFromLinearExp(lhs).toList.head.id
	//println("k = " + k +  " x = " + x)

/*
 //code before 23.04 
	if (op == Relation_Symbol.EQUAL || rhsVal <= k(x))
	  nz.add_constraint(c)
	  //nz.add_constraint(new Constraint(lhs, op, rhs))
	//for op \in {>=, >} transf each x op m and x - y op m into x op k(x), resp. x - y op k(x) for m > k(x)
	else if ((op == Relation_Symbol.GREATER_THAN || op == Relation_Symbol.GREATER_OR_EQUAL) && rhsVal > k(x)) 
	  nz.add_constraint(new Constraint(lhs, op, new Linear_Expression_Coefficient(new Coefficient(k(x)))))
	else println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!normZone: shouldn't be here! c = " + c)
    }
 */ 

	if (rhsVal <= k(x))
	  nz.add_constraint(c)
	else {
	  //for op \in {==, >=, >} transf each x op m and x - y op m into x > k(x), resp. x - y > k(x) for m > k(x)
	  //we include also == because left == m \equiv left >= m and left <= m; we are in the case m > k(x), so, in this case, we have:
	  //rm left <= m and add left >= k(x)
	    nz.add_constraint(new Constraint(lhs, Relation_Symbol.GREATER_THAN, new Linear_Expression_Coefficient(new Coefficient(k(x)))))
	}
    }
   nz      
  }

  /** @return a pair of "global inv" and "global trans" from a list of "local trans", i.e.,
    * the global trans is the result of transforming (t1, ..., tk) into (gsource, ga, gg, gr, gsink) where
    *  gsource = (source(t1), ..., source(tk)), gg = intersection of guard(ti) etc
    * and the global inv is the conj of all invs for the locs in gsink
    */
  //def makeGlobalTrans(tl: List[Transition], invM: InvMap, clksMs: List[Map[Clock, String]], clksGM: Map[Clock, String]) = {
  //def makeGlobalTrans(tl: List[Transition], invM: InvMap, clksMs: List[Map[Clock, String]], clksGM: Map[String, Clock]) = {
  def makeGlobalTrans(tlWithOwner: List[(Int, Transition)], invM: InvMap, clksMs: List[Map[Clock, String]], clksGM: Map[Clock, String]) = {
    val tl = tlWithOwner.map{_._2}
    val owner = tlWithOwner.map{_._1}
    require (tl.length > 0, println("[Err in makeGlobalTrans]: the arg is empty"))
    if (tl.length == 1) {
      val gt = tl.head 
      //val gI = invM(getSource(tl.head))
      val gI = invM(getSink(tl.head))
      debug("makeGobalTrans of tl = " + tl.map{toString(_)} + " returns gt = " + toString(gt) + " gI = " + gI)
      (gt, gI)
    }
    else {     
      val indices = List.range(0, tl.length)
      val gsourceL = tl.map{t => getSource(t)}
      val gsinkL = tl.map{t => getSink(t)}
      //val gIL = indices.map{i => new NNC_Polyhedron(renameZone(invM(gsourceL(i)), clksMs(owner(i)), clksGM))}
      val gIL = indices.map{i => new NNC_Polyhedron(renameZone(invM(gsinkL(i)), clksMs(owner(i)), clksGM))}
      val gI = gIL.head
      gIL.foreach{i => gI.intersection_assign(i)}
      val gsource = gsourceL.tail.foldLeft(gsourceL.head)((r, c) => r + ", " + c)
      val gsink = gsinkL.tail.foldLeft(gsinkL.head)((r, c) => r + ", " + c)
      val gaL = tl.map{t => getAct(t)}
      val ga = gaL.tail.foldLeft(gaL.head)((r, c) => r + " | " + c)
      val ggL = indices.map{i => new NNC_Polyhedron(renameZone(getGuard(tl(i)), clksMs(owner(i)), clksGM))}
      val gg = ggL.head
      //don't forget that the res of intersection will be in gg
      ggL.foreach{g => gg.intersection_assign(g)}
      val grL = indices.map{i => renameReset(getReset(tl(i)), clksMs(owner(i)), clksGM)}
      //correct gr !!!    
      val gr = grL.tail.foldLeft(grL.head)((r, c) => r ++ c)
      val gt : Transition = (gsource, ga, gg, gr, gsink)
      debug("makeGobalTrans of tl = " + tl.map{toString(_)} + " returns gt = " + toString(gt) + " gI = " + gI)
      (gt, gI)
    }
  }

  def makeGlobalClkMap(clksMs: List[Map[Clock, String]]) = {
    var clksGM = Map[Clock, String]()
    //var clksGM = Map[String, Clock]()
    var i = 0
    clksMs foreach {
      clksM => 
	clksM foreach {
	  cm => 
	    val clk = new Variable(i)
	  clksGM += (clk -> cm._2)
	  //clksGM += (cm._2, clk)
	  i += 1
	}
    }
    clksGM
  }

  /** @return DIS(\alpha) = \neg EN(\alpha); EN(\alpha) = \wedge_{a \in \alpha} en(a), so DIS(\alpha) = \vee_{a \in \alpha} \neg(en(a)) */
  def genDISInteraction(alpha: List[String], system: System) = {
    debug("clksMs = " + system.map{ta => getClkMap(ta).map(el => (el._1.id, el._2))})
    //debug("invsMs = " + system.map{ta => getInvMap(ta).foldLeft("")(_+"\n"+_)})
    val indices = List.range(0, alpha.length)
    //participating TA choices: for each a in alpha return the TAs (together with a and index i) which have a in their alph
    val pTaCs0 = indices.map{i => (i, alpha(i), system.dropWhile(ta => !getAlph(ta)(alpha(i))))}
    //use the index i to get the list of owners, i.e., to which comp. does the participating port in alpha belong to
    val owners = pTaCs0.map{el => el._1}
    debug("owners = " + owners)
    //remove the index i, it's no longer needed
    val pTaCs = pTaCs0.map{el => (el._2, el._3)}
    //require that any act in an alpha appears in a TA alph
    require(pTaCs.foldLeft(0)(_+_._2.length) >= alpha.length, println("There exists an act in " + alpha + " which doesn't appear in any TA alph"))
    //assuming all alphs are disjoint, there should be a unique TA for each a; so it's fine to take the head
    //pTaA is the list of TAs zipped with the acts from alpha which are in their alphs
    val pTaA = pTaCs.map{el => (el._2.head, el._1)}.toList
    //the clock and inv maps of the tas involved 
    val clksMs = indices.map{i => getClkMap(pTaA(i)._1)}
    val clksMG = makeGlobalClkMap(clksMs)
    val invMs = indices.map{i => getInvMap(pTaA(i)._1)}.reduceLeft(_++_)
    //tCs represents the list of trans labelled a for each a in alpha
    val tCs = indices.map{i => getTransFromAct(pTaA(i)._1, pTaA(i)._2).toList}
    //cp is the cartesian prod of transitions in tCs 
    val cp = cpLTrans(tCs)
    debug("for alpha = " + alpha + " cp = " + cp.map{tl => tl.map{toString(_)}})    
    // construct "global transitions" corr. to each tuple in tCs
    val tIGs = cp.map{tl => makeGlobalTrans(owners.zip(tl), invMs, clksMs, clksMG)}	
    //val disGT = tIGs.map{gt => "Not(" + enTrans0(gt._1, gt._2, clksMG) + ")"}  
    //for the last trans we don't have invariant, so we take true
    //val disGT = List.range(0, tIGs.length-1).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, tIGs(i+1)._2, clksMG) + ")"} :+ ("Not(" + enTrans(tIGs.last._1, tIGs.last._2, new NNC_Polyhedron(clksMG.size, Degenerate_Element.UNIVERSE), clksMG) + ")")
    //val disGT = List.range(0, tIGs.length).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, clksMG) + ")"} 
    val disGT = List.range(0, tIGs.length).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, clksMG) + ")"} 
    if (disGT.length == 1)  disGT.head
    else "And(" + disGT.tail.foldLeft(disGT.head)((r,c) => r + ", " + c) + ")"  
  }

  //eps trans happen by themselves; they're global by themselves
  def genDISEps(system: System) = {
    val dis = system.map{
      ta =>
	val clksM = getClkMap(ta)
	val invsM = getInvMap(ta)
	val epsTrans = getTrans(ta).filter(t => getAct(t) == eps)
	epsTrans.map{t => "Not(" + enTrans(t, invsM(getSink(t)), clksM) + ")"}.toList
    }.flatten
    if (dis.length == 1)  dis.head
    else "And(" + dis.tail.foldLeft(dis.head)((r,c) => r + ", " + c) + ")"  
  }

  /** generate DIS(\gamma) = \neg EN(\gamma); EN(\gamma) = \vee_{\alpha \in \gamma} en(\alpha), so DIS(\alpha) = \wedge_{\alpha \in \gamma} DIS(\alpha). */
  def genDIS(im: List[List[String]], system: System) = {
    val disAlphas = im.map{alpha => if (alpha.length == 1 && alpha.head == eps) genDISEps(system) else genDISInteraction(alpha, system)}
    if (disAlphas.length == 0) ""
    else if (disAlphas.length == 1) disAlphas.head
    else "And(" + disAlphas.tail.foldLeft(disAlphas.head)((r,c) => r + ", " + c) + ")"  
  }


/* For the reference, this impl. is wrt old def of TA enabled; see notebook */

  /** en(a,t) = at(l) \wedge g \wedge inv(l), where t = (l, a, g, r, l')  */
  def enActTransOld(a: String, t: Transition, ta: TA) = {
    require (getAct(t) == a, println("[Err in enActTrans]: transition " + t + " is not labelled with act " + a + "."))  
    val nzone = new NNC_Polyhedron(getGuard(t))
    val loc = getSource(t)
    nzone.add_constraints(getInvMap(ta)(loc).constraints)
    val ss = (loc, nzone)
    makeStateProp(ss, getClkMap(ta))
  }

  def enActOld(a: String, system: System) = {
    val tasWithA = system.filter{ta => (getTrans(ta).filter{t => getAct(t) == a}).size > 0}
    require(a == eps || (a != eps && tasWithA.length == 1), println("[Err in enActOld]: expected only 1 TA to have act " + a + " but found " + tasWithA.length + " instead.")) 
    val enCs = tasWithA.map{
      ta => 
	val transWithA = getTrans(ta).filter{t => getAct(t) == a}
      val res = transWithA.map{t => enActTransOld(a, t, ta)}.toList
      if (res.length == 1) res.head
      else "Or(" + res.tail.foldLeft(res.head)((r, c) => r + " ," + c) + ")"
    }
    "And(" + enCs.reduceLeft(_+", "+_) + ")"
  }
  
  /** for any loc l with inv diff from True we construct the prop l /\ inv* with inv* being inv where we replace op= by strict op.
    * Intuitively, for instance for inv t <= val, this prop says it's not ok to be at a loc and t > val (the case for t == val is taken care of
    * in genDISInteraction).
    */
  def delayLoc(l: Location, inv: NNC_Polyhedron, clksMap: Map[Clock, String]) = {
    debug("inv = " + inv.toString)
    makeStateProp((l, inv), clksMap).replace("==", "<").replace(">=", ">").replace("<=", "<")
    //"And(" + l + ", " + inv.toString.replace("==", "<") + ")"
  }

  /** for any loc l with inv diff from True we construct the prop not(l /\ strict(inv)) to express deadlock states wrt time
    */
  def deadLoc(l: Location, inv: NNC_Polyhedron, clksMap: Map[Clock, String]) = {
    val strictInv = zone2String(inv, clksMap).replace("<=", "<").replace(">=", ">")
    "Not(And(" + l + ", " + strictInv + "))"
  }

  def genDISInvs(system: System) = {
    val locsWithInv = system.map{ta => 
      val invM = getInvMap(ta)
      getLocs(ta).filter{l => invM(l).toString != "true"}.map{l => (l, invM(l), getClkMap(ta))}
			}.flatten
    //val disInvs = locsWithInv.map{lp => "Not(" + delayLoc(lp._1, lp._2, lp._3) + ")"}
    val disInvs = locsWithInv.map{lp => deadLoc(lp._1, lp._2, lp._3)}
    disInvs
  }

  def genDISInteractionOld(alpha: List[String], system: System) = {
    val disacts = alpha.map{ai => "Not(" + enActOld(ai, system) + ")"}
    if (disacts.length == 1)  disacts.head
    else "Or(" + disacts.tail.foldLeft(disacts.head)((r,c) => r + ", " + c) + ")"  
  }

  /** generate DIS(\gamma) = \wedge_alpha DIS(alpha) \wedge \wedge_l delayDIS(l) */
  def genDISOld(im: List[List[String]], system: System) = {
    val disAlphas = im.map{alpha => genDISInteractionOld(alpha, system)}
    val disFromInvs = genDISInvs(system)
    val allDis = disAlphas ::: disFromInvs
    if (allDis.length == 0) ""
    else if (allDis.length == 1) allDis.head
    else "And(" + allDis.tail.foldLeft(allDis.head)((r,c) => r + ", " + c) + ")"  
  }

  import scala.io.Source._

  def genDeclHistoryIM(im: List[List[String]]) = {
    val clks = im.map{alpha => mkIMClk(alpha.toSet)}
    val names = clks.tail.foldLeft(clks(0))((r, c) => r + ", " + c)
    val body = clks.tail.foldLeft(clks(0))((r, c) => r + " " + c)
    (names + " = Ints('" + body + "')")    
  }

  def genTCZ3(s: System, im: List[List[String]], portDelays: Map[String, Int], dis0: String="", defaultZ3FileName: String = "defaultZ3.py", strengthen: String = "", defaultII: String = "", isSym: Boolean = false) = {
    val disIn = if (dis0 == "") genDIS(im, s) else dis0
    val disOld = if (dis0 == "") genDISOld(im, s) else dis0
    val n = s.length
    val indices = List.range(0, n)
    val ims = im.map{alpha => alpha.toSet}.toSet
    val declLocs = genDeclLocsSystem(s)
    val declClks = genDeclClksSystem(s) 
    val declHistoryIM = genDeclHistoryIM(im.filter{_!=List(eps)})
    val invsNames = s.map{ta => INV + getName(ta)}
    val localInvs = indices.tail.foldLeft(invsNames(0) + " = " + genLocalInvTA(s(0)))((r, c) => r + "\n" + invsNames(c) + " = " + genLocalInvTA(s(c)))
    val sourceII = if (ISLOCINT) "" else ("sourceII = " + genII(s, ims))
    val II = if (defaultII == "" && sourceII == "") "" else ("II = " + (if (ISLOCINT || defaultII != "") defaultII else "getII(sourceII)") + " \n")
    //val eqs = "Eqs = " + getEqs(im)
    val eqsSimpl = "EqsS = " + getEqsSimpl(im)
    val eqsC = "EqsC = " + getEqsC(ims)
    val sep = "Sep = " + getSep(ims, portDelays, isSym)
    val gih =  "Gih = " + "And(" + (indices.tail.foldLeft(invsNames(0))((r, c) => r + ", " + invsNames(c))) + ", EqsS, II" + (if (strengthen != "") (", " + strengthen) else "") + ")"
    val gihExt =  "GihExt = " + "And(" + (indices.tail.foldLeft(invsNames(0))((r, c) => r + ", " + invsNames(c))) + ", EqsS, EqsC, Sep, II" + (if (strengthen != "") (", " + strengthen) else "") + ")"
    val dis = "Dis = " + disIn
    val disOldEl = "DisOld = " + disOld
    val dead = "dead = And(Gih, Dis)" 
    val deadExt = "deadExt = And(GihExt, Dis)" 
    val deadOld = "deadOld = And(Gih, DisOld)" 
    val goal = "solve(dead)"    

    val fileName = wd + "resources/" + defaultZ3FileName
    //val in: Input = Resource.fromFile(fileName)
    //val defaultZ3 = in.slurpString(Codec.UTF8)
    val source = scala.io.Source.fromFile(fileName)
    val defaultZ3 = source.mkString
    source.close()
    //val defaultZ3 = io.Source.fromInputStream(getClass.getResourceAsStream(wd + "/resources/defaultZ3.py")).mkString
    val z3File = (defaultZ3 + "\n" +       
    declLocs + "\n" + 
    declClks + "\n" +
    declHistoryIM  + "\n" +
    localInvs + "\n" + 
    sourceII  + "\n" + 
    II + "\n" + 
    "#print \"II = \", II\n"   +
    //eqs +  "\n" +
    eqsSimpl +  "\n" +
    "#print simplify(Eqs) \n" +
    "#print \"EqsS = \", simplify(EqsS) \n" +
    "#print \"Solving Not(Eqs == EqsS):\", solve(Not(Eqs == EqsS)) \n" +		  
    dis + "\n" + 
    "#print \"Dis =\", Dis\n" + 		  
    //disOldEl + "\n" + 
    "#print \"DisOld =\", DisOld\n" + 		  
    "#print \"Solving Not(Dis == DisOld):\", solve(Not(Dis == DisOld)) \n" +		  
    gih + "\n" + 
    dead + "\n" + 
    (if (ISSEP) eqsC + "\n" + sep + "\n" + gihExt + "\n" + deadExt + "\n" + "print \"Solving deadExt:\" \n" + "getCEX(deadExt)\n" else "") + 
    "#m100 = getAllModels(And(II, Not(at2Locs)), 100)\n" + 
    "#print \"Uppaal query for II= \", getUppaalQueryFromTempControlII(m100)\n" + 
    "print \"Solving dead:\" \n" + 
    "getCEX(dead)\n" 
    //deadOld + "\n" + 
    //"print \"Solving deadOld:\" \n" + 
    //"getCEX(deadOld)\n"
    )
    z3File
  }

  def genTCZ3Old(s: System, im: List[List[String]], dis0: String="", defaultZ3FileName: String = "defaultZ3.py", strengthen: String = "") = {
    val disIn = if (dis0 == "") genDIS(im, s) else dis0
    val disOld = if (dis0 == "") genDISOld(im, s) else dis0
    val ims = im.map{_.toSet}.toSet
    val n = s.length
    val indices = List.range(0, n)
    //val eqs = "Eqs = " + getEqs(im)
    val eqsSimpl = "EqsS = " + getEqsSimpl(im)
    val declLocs = genDeclLocsSystem(s)
    val declClks = genDeclClksSystem(s)
    val invsNames = s.map{ta => INV + getName(ta)}
    val localInvs = indices.tail.foldLeft(invsNames(0) + " = " + genLocalInvTA(s(0)))((r, c) => r + "\n" + invsNames(c) + " = " + genLocalInvTA(s(c)))
    val at2Locs = "at2Locs = " + genAt2LocsSystem(s)
    //val ims = im.map{alpha => alpha.toSet}.toSet
    val sourceII = "sourceII = " + genII(s, ims)
    val gih =  "Gih = " + "And(" + (indices.tail.foldLeft(invsNames(0))((r, c) => r + ", " + invsNames(c))) + ", EqsS, Not(at2Locs), II" + (if (strengthen != "") (", " + strengthen) else "") + ")"
    val dis = "Dis = " + disIn
    val disOldEl = "DisOld = " + disOld
    val dead = "dead = And(Gih, Dis)" 
    val deadOld = "deadOld = And(Gih, DisOld)" 
    val goal = "solve(dead)"    

    val fileName = wd + "resources/" + defaultZ3FileName
    //val in: Input = Resource.fromFile(fileName)
    //val defaultZ3 = in.slurpString(Codec.UTF8)
    val source = scala.io.Source.fromFile(fileName)
    val defaultZ3 = source.mkString
    source.close()
    //val defaultZ3 = io.Source.fromInputStream(getClass.getResourceAsStream(wd + "/resources/defaultZ3.py")).mkString
    val z3File = (defaultZ3 + "\n" +       
    declLocs + "\n" + 
    declClks + "\n" + 
    localInvs + "\n" + 
    at2Locs + "\n" + 
    sourceII + "\n" + 
    "II = getII(sourceII) \n" +   
    "#print \"II = \", II\n"   +
    //eqs +  "\n" +
    eqsSimpl +  "\n" +
    "#print simplify(Eqs) \n" +
    "\nprint \"EqsS = \", simplify(EqsS) \n" +
    "#print \"Solving Not(Eqs == EqsS):\", solve(Not(Eqs == EqsS)) \n" +		  
    dis + "\n" + 
    "#print \"Dis =\", Dis\n" + 		  
    disOldEl + "\n" + 
    "#print \"DisOld =\", DisOld\n" + 		  
    "#print \"Solving Not(Dis == DisOld):\", solve(Not(Dis == DisOld)) \n" +		  
    gih + "\n" + 
    dead + "\n" + 
    "#m100 = getAllModels(And(II, Not(at2Locs)), 100)\n" + 
    "#print \"Uppaal query for II= \", getUppaalQueryFromTempControlII(m100)\n" + 
    "print \"Solving dead:\" \n" + 
    "getCEX(dead)\n" + 
    deadOld + "\n" + 
    "print \"Solving deadOld:\" \n" + 
    "getCEX(deadOld)\n"
    )
    z3File
  }

  def cpLTrans(l : List[List[Transition]]) : List[List[Transition]] = l match {
    case Nil => List(List())
    case xl :: r => for (rl <- cpLTrans(r); x <- xl) yield x +: rl 
  }    

/** Interaction Invariant */
  
  /** @return a list of lists ??? of transitions
    */   
  def companionTrans(i: Int, t: Transition, system: System, im: Set[Set[String]]) = {
    val indices = List.range(0, system.length)
    val a = getAct(t)
    val res = (for(alpha <- im; val remalpha = (alpha - a); if (alpha.contains(a))) yield cpLTrans(indices.map{i => getTrans(system(i)).filter(t => remalpha.contains(getAct(t))).toList}.filter(_!=List()))).toList.flatten
    //debug("companionTrans: trans = " + toString(t) + " im = " + im + " res = " + res.map{lt => lt.map{toString(_)}})
    res
  }

  /** @return a list of sets of transitions with the indices of the comp to which they belong
    */ 
  def ldot(beh: TA, i: Int, source: Location, system: System, im: Set[Set[String]]) = getTrans(beh).filter(t => getSource(t) == source).map{t => companionTrans(i, t, system, im)}.flatten

  def dotl(beh: TA, i: Int, sink: Location, system: System, im: Set[Set[String]]) = getTrans(beh).filter(t => getSink(t) == sink).map{t => companionTrans(i, t, system, im)}.flatten 

  def genDisj(tl: List[Transition]) = if (tl.length == 0) "" 
				      else if(tl.length == 1) getSink(tl(0)) 
				      else "Or(" + tl.tail.foldLeft(getSink(tl(0)))((r,c) => r + ", " + getSink(c)) + ")"

  def genImplicOld(i: Int, l: Location, system: System, im: Set[Set[String]]) = {
    val beh = system(i)
    val ldotRes = ldot(beh, i, l, system, im).toList
    //debug("i = " + i + " l = " + l + " ldot = " + ldotRes.map{lt => lt.map{toString(_)}} + " beh.trans = " + getTrans(beh).map{toString(_)})
    if (ldotRes != List()) {
      val right_hand_side = if (ldotRes.length == 1) genDisj(ldotRes(0)) else "And(" + ldotRes.tail.foldLeft(genDisj(ldotRes.head))((r,c) => r  + "," + genDisj(c)) + ")"
      "Implies(" + l + ", " + right_hand_side + ")"
    }
    else ""    
  }

  /**impl def 16 pg 54, Hung thesis:
    * flash{l^\gamma} is the set of tuples of trans involved in some interaction of \gamma in which a trans t_i from l can participate.
    */ 
  def fwdInteractionSet0(i: Int, l: Location, system: System, im: Set[Set[String]]) = {
    val indices = List.range(0, system.length)
    val alphs = indices.map{i => getAlph(system(i))}
    im foreach {
      alpha => 
	//alpha is {a_1, ..., a_k} (representing a_1 | a_2 | .. | a_k)
	//find out to which component each a_i belongs to (we assume the alphabets of comps are disjoint)
	val participatingIndices = indices.filter{i => (alphs(i) & alpha) != Set()}
        //for each participating index get the trans with a label in alpha
	val participatingTrans = participatingIndices.map{i => getTrans(system(i)).filter{t => (alpha(getAct(t)))}.toList}
        //make the cp of the participating transitions
	val cpTrans = cpLTrans(participatingTrans)
	//filter those tuples which contain a trans with source l
	cpTrans.filter{tl => tl.exists(t => getSource(t) == l)}
    }
  }

  /**impl def 16 pg 54, Hung thesis:
    * flash{l^\gamma} is the set of tuples (we impl it as a list of lists)
    * of trans involved in some interaction of \gamma in which a trans t_i from l can participate.
    * We can make it more efficient if we first filter the trans starting from l in C_i and filtering im s.t. we only consider
    * the interactions involving the acts in the filtered trans
    */ 
  def fwdInteractionSet(i: Int, l: Location, system: System, im: Set[Set[String]]) = {
    val transi = getTrans(system(i)).filter{t => getSource(t) == l}
    val participatingActs = transi.map{t => getAct(t)}.toSet
    val participatingInteractions = im.filter{alpha => (alpha & participatingActs).size == 1}
    val indices = List.range(0, system.length)
    val alphs = indices.map{i => getAlph(system(i))}
    var res = List[List[Transition]]()
    participatingInteractions foreach {
      alpha => 
	//alpha is {a_1, ..., a_k} (representing a_1 | a_2 | .. | a_k)
	//find out to which component each a_i belongs to (we assume the alphabets of comps are disjoint)
	val participatingIndices = indices.filter{i => (alphs(i) & alpha) != Set()}
        //for each participating index get the trans with a label in alpha
	val participatingTrans = participatingIndices.map{
	  j => 
	    if (i == j) transi.filter{t => ( alpha(getAct(t)) ) }.toList
	    else getTrans(system(j)).filter{t => (alpha(getAct(t)))}.toList
	}
        //make the cp of the participating transitions
	res = res ::: cpLTrans(participatingTrans)
    }
    res
  }

  def genImplic(i: Int, l: Location, system: System, im: Set[Set[String]]) = {
    val beh = system(i)
    val fwdIL = fwdInteractionSet(i, l, system, im)
    if (fwdIL != List()) {
      val right_hand_side = if (fwdIL.length == 1) genDisj(fwdIL(0)) else "And(" + fwdIL.tail.foldLeft(genDisj(fwdIL.head))((r,c) => r  + "," + genDisj(c)) + ")"
      "Implies(" + l + ", " + right_hand_side + ")"
    }
    else ""    
  }

  def genII(system: System, im: Set[Set[String]]) = {
    val indices = List.range(0, system.length)
    val allLocs = indices.flatMap{i => getLocs(system(i)).map{l => (i, l)}}
    val implics = allLocs.map{l => genImplic(l._1, l._2, system, im)}.filter(_!="")
    if (implics.length == 0) ""
    else if (allLocs.length == 1) implics(0)
    else "And(" + implics.tail.foldLeft(implics(0))((r,c) => r + ", " + c) + ")"
  }

  def toDot(ta: TA) : String = { 
    val pathGraphsTxt = wd + "/graphs/"
    val pathGraphs = Path(pathGraphsTxt)

    val taName = getName(ta)

    if (!pathGraphs.exists) pathGraphs.createDirectory(failIfExists=false)
    val dotfile = pathGraphsTxt + taName + ".dot"
    val pngfile = pathGraphsTxt + taName + ".png"
    
    val clksM = getClkMap(ta)
    val invsM = getInvMap(ta)
    val tl = getTrans(ta)
    val aux = tl map { 
      t => 
	val l1 = getSource(t)
	val invl1 = zone2String(invsM(l1), clksM)
	val l2 = getSink(t)
	val invl2 = zone2String(invsM(l2), clksM)
	val guard = zone2String(getGuard(t),clksM)
	val reset = reset2StrM(getReset(t))(clksM)
	(l1 + "-> " + l2 + " [label=\"" + invl1 + ", " + getAct(t) + "," + guard + "," + reset + "\"]; \n")
    }
    val body = aux.foldLeft("")(_+_) 
    val dotcontent = "digraph " + taName + " {" + body + "}" 
    val path = Path(dotfile)
    path.createFile(failIfExists=false) 
    val file: FileOps = path 
    file.write(dotcontent)
    
    val cmd = "dot -Tpng " + dotfile + " -o " + pngfile
    val pd = Process(cmd)
    pd.!	
    dotcontent
  }

 def write2File(filePath: String, fileTxt: String) = { 
    val path = Path (filePath)
    path.createFile(failIfExists=false)
    val file: FileOps = Path (filePath)		   
    // By default the file write will replace
    // an existing file with the new data
    file.write (fileTxt)
    //content
  }

  def runZ3(filePath: String) = { 
    val cmd = ("time python " + filePath) 
      
    val out = new StringBuilder
    val err = new StringBuilder

    val logger = ProcessLogger(
      (o: String) => out.append(o),
      (e: String) => err.append(e))
    
    cmd ! logger
    debug("runZ3: cmd = " + cmd + "\n\n", 2)

    val all = out.toString + err.toString 

    (out.toString, err.toString)
  }

  def runImitator(filePath: String) = { 
    val cmd = ("/local/astefano/tools/imitator/./IMITATOR64 " + filePath + " -mode reachability -with-dot -with-log") 
      
    val out = new StringBuilder
    val err = new StringBuilder

    val logger = ProcessLogger(
      (o: String) => out.append(o),
      (e: String) => err.append(e))
    
    cmd ! logger
    debug("runImitator: cmd = " + cmd + "\n\n", 2)

    val all = out.toString + err.toString 

    (out.toString, err.toString)
  }


}
