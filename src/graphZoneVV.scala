package org

import scala.math.BigInt._
import parma_polyhedra_library._

import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException
import scala.util.control.Exception._

import scala.sys.process._

import scala.sys

//for XML
import com.codecommit.antixml._
//import com.codecommit.antixml.ZipperMergeStrategy._
//import XML._

import scala.util.matching.Regex

case class ZoneGraphVV() extends genEF {
//  val HISTCN = "histComp"
//  val HISTCLOC = "hcl"

  //set the working dir
  implicit val wd = System.getProperty("user.dir") + "/"

  //constant to use in the name of the loc vector
  val LOCS = "l"

  //true if the locs are mapped into 0, 1 and false if the locs are bools (in Z3)
  var ISLOCINT = false //true

  val ISSEP = true//false

  //find a nice char to sep the ports in h_alpha (|, *, etc won't be ok for z3 python)
  val HSEP = ""

  var DEBUG_LEVEL = 0

  def debug(s: String, m: Int = 0) = if (DEBUG_LEVEL > m) println(s)

/**/  
  try {
    println("Debug: java.library.path= " + System.getProperty("java.library.path"))
    //System.load("/net/aconcagua/local/astefano/tools/lib/ppl/libppl_java.so")
    System.load(wd + "lib/libppl_java.so")
    println(Parma_Polyhedra_Library.version())
  }
  catch {
    case e: UnsatisfiedLinkError =>
      println("Unable to load the library")
    println(e.getMessage())
    System.exit(-1)
  }
/**/

  val eps = "eps"
  //default name to be appended to history clocks
  val hName = "h"

  type Name = String
  type Location = String
  type Clock = Variable
  //type Param = Variable
  type Invariant = NNC_Polyhedron
  type Act = String
  type Guard = NNC_Polyhedron
  //for gv : GuardV, any (vn, op, vv) \in gv is to be interpreted as vn op vv with vn a var name, op \in {>=, <=, ==} and vv a value
  type GuardVElem = (String, String, Int)
  type GuardV = Set[GuardVElem]

  def getVN(gv: GuardVElem) = gv._1
  def getOp(gv: GuardVElem) = gv._2
  def getVV(gv: GuardVElem) = gv._3

  type Reset = Set[(Variable, Int)]  
  //in UpdV the last boolean is for this: if true, then just assign, else upd, i.e., +=
  type UpdV = Set[(String, Int, Boolean)]
  def mkUpd(p: (String, Int)) = (p._1, p._2, false) 
  def mkUpdB(p: (String, Int)) = (p._1, p._2, true) 
  type Transition = (Location, Act, Guard, GuardV, Reset, UpdV, Location)
  type InvMap = Map[Location, Invariant]
  type ClkMap = Map[Clock, String]
  type Params = Set[String]
  //valuation of vars
  type VarsV = Map[String, Int]
  val VarsV = Map[String, Int]()
  val emptyVV : VarsV = VarsV.empty
  //type TA = (Name, Location, Set[Location], Set[Transition], Map[Clock, String], InvMap)
  type TA = (Name, Location, Set[Location], Set[Transition], ClkMap, InvMap, VarsV)

  type PTA = (Name, Location, Set[Location], Set[Transition], ClkMap, InvMap, VarsV, Params)

  type TAS = List[TA]

  type Interaction = Set[Act]
  //type InteractionModel = Set[Set[String]]
  type InteractionModel = Set[Set[Act]]
  type InteractionModelExt = Set[(Set[String], Guard, Reset)]

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
  def getVars(ta: TA) = ta._7

/** getters from TA */
  def getName(ta: PTA) = ta._1
  def getIni(ta: PTA) = ta._2
  def getLocs(ta: PTA) = ta._3
  def getTrans(ta: PTA) = ta._4
  def getClkMap(ta: PTA) = ta._5
  def getInvMap(ta: PTA) = ta._6
  def getVars(ta: PTA) = ta._7
  def getParams(ta: PTA) = ta._8

  /** we fix the alph of a comp to be the set of acts appearing in the trans.*/
  def getAlph(ta: TA) = getTrans(ta).map{trans => getAct(trans)}
  def getAlph(ta: PTA) = getTrans(ta).map{trans => getAct(trans)}

  def getGlobalAlph(tal: List[TA]) = tal.flatMap{ta => getAlph(ta)}.toSet

  /** getters from Transition */
  def getSource(t: Transition) = t._1
  def getAct(t: Transition) = t._2
  def getGuard(t: Transition) = t._3
  def getGuardV(t: Transition) = t._4
  def getReset(t: Transition) = t._5
  def getUpd(t: Transition) = t._6
  def getSink(t: Transition) = t._7

  def mkTrans(source: Location, p: Act, g : Guard, gv : GuardV = Set(), r: Reset, upd : UpdV = Set(), sink : Location) = (source, p, g, gv, r, upd, sink)

  type Zone = NNC_Polyhedron  
  //the valuation of vars vars
  type SymbolicState = (Location, Zone, VarsV)    

  val noneSS: SymbolicState = ("nonreach", new NNC_Polyhedron(0, Degenerate_Element.UNIVERSE), emptyVV)

  def getLoc(s: SymbolicState) = s._1
  def getZone(s: SymbolicState) = s._2
  def getVV(s: SymbolicState) = s._3

  def getBfromGVElem(vv: VarsV, c: GuardVElem) : Boolean = getOp(c) match {
      case ">=" => (vv(getVN(c)) >= getVV(c))
      case ">" => (vv(getVN(c)) > getVV(c))
      case "<=" => (vv(getVN(c)) <= getVV(c))
      case "<" => (vv(getVN(c)) < getVV(c))
      case "==" => (vv(getVN(c)) == getVV(c))
  }

  def toString(t: Transition)(implicit clksM: Map[Clock, String] = Map()) : String = "(" + getSource(t) + ", " + getAct(t) + ", " + 
  //zone2String(getGuard(t),clksM) + ", " + reset2StrM(getReset(t))(clksM) + ", " + getSink(t) + ")"
  zone2String(getGuard(t), clksM) + ", " + reset2StrM(getReset(t))(clksM) + ", " + getSink(t) + ")"

  //def toString(t: Transition) : String = "(" + getSource(t) + ", " + getAct(t) + ", " + getGuard(t).toString + ", " + getReset(t).map{el => (clksM(el._1), el._2)} + ", " + getSink(t) + ")"

  //def toString(r: Reset) : String = r.reduceLeft{(r, c) => r + ", (" + c._1.id + ", " + c._2 + ")"}
  def reset2Str(r: Reset) : String = r.map{el => "(" + el._1.id + ", " + el._2 + ")"}.toString

  def reset2StrM(r: Reset)(implicit clksM: Map[Clock, String] = Map()) = if (r.isEmpty) "" else r.map{el => (clksM.getOrElse(el._1, -10) + "=" + el._2)}.reduceLeft(_+","+_)

  def upd2Str(u: UpdV) = if (u.isEmpty) "" else u.map{u => u._1 + "+=" + u._2}.reduceLeft(_+"," +_)

  def toString(ta: TA) : String = {
    val clksM = getClkMap(ta)
    //getName(ta) + " = (" + getIni(ta) + ", " + getLocs(ta) + ", " + getTrans(ta).reduceLeft{(r,c) => r + "," + toString(c)(clksM)} + ", " + getInvMap(ta)
    getName(ta) + " = (" + getIni(ta) + ", " + getLocs(ta) + ",\n" + 
    getTrans(ta).map{t => toString(t)(clksM)}.reduceLeft(_+"\n"+_) + ",\n" + 
    getClkMap(ta).map{_._2} + ",\n" + 
    getInvMap(ta) + ")"
  }

  def toString(pta: PTA): String = toString(getTA(pta)) + " and params = " + getParams(pta)

  def toString(invsM: InvMap) : String = invsM.foldLeft("")((r,c) => r + "I(" + c._1 + ") = " + c._2 + " of dim " + c._2.space_dimension + ", ") 

  //def toString(clksM: ClkMap) : String = clksM.foldLeft("")((r,c) => r + c._1.id + " -> " + c._2) 

//  def ta2Str(ta: TA) : String = getName(ta) + " = (" + getIni(ta) + ", " + getLocs(ta) + ", " + getTrans(ta).map{t => toString(t)}.toString + ", " + getInvMap(ta)

  def getTransFromAct(ta: TA, a: String) = getTrans(ta).filter{ t => getAct(t) == a }

  def mkHClk(a: String) = hName + a

  /** internal acts are singletons in IM */
//  def getTAH(ta: TA)(implicit im: Set[Set[String]] = Set()) = {
  def getTAH(ta: TA)(implicit im: InteractionModel = Set()) = {
    var curClksMap = getClkMap(ta)
    var temp = Map[String, Clock]()
    val n = curClksMap.size
    val trans = getTrans(ta)
    val intActs = if (!im.isEmpty) im.filter{alpha => alpha.size == 1}.map{_.toList.head} else Set[Act]()
    val extActs = trans.map{t => getAct(t)}.filter{a => !intActs(a)}.toList
    val indices = List.range(0, extActs.length)
    val ndim = extActs.length
    indices foreach {
      i => 
	//curClksMap += (hName + extActs(i) -> new Variable(n + i))
	val nclk = new Variable(n + i)
	val nclkName = mkHClk(extActs(i))
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
	val nt = (getSource(t), p, ng, getGuardV(t), getReset(t) + ((temp(hclkName), 0)), getUpd(t), getSink(t)) 
	//debug("for nt = " + toString(nt) + " the guard has dim = " + ng.space_dimension)
	nt      
      }
      //for internal (singletons) actions don't forget to redim the guard!!!
      else (getSource(t), p, ng, getGuardV(t), getReset(t), getUpd(t), getSink(t)) 
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
    (getName(ta) + hName, getIni(ta), getLocs(ta), ntrans, curClksMap, ninvsM, getVars(ta))
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
       (getSource(t), p, ng, getGuardV(t), getReset(t), getUpd(t), getSink(t)) 
    }
    val ninvsM = getInvMap(ta)
    ninvsM foreach {
      el => 
	el._2.add_space_dimensions_and_embed(1)
    }
    (getName(ta), getIni(ta), getLocs(ta), ntrans, curClksMap, ninvsM, getVars(ta))
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
  def resetBck(zone: NNC_Polyhedron, toReset: Reset)(implicit clksM: Map[Clock, String] = Map()) = {
    val zoneCopy = new NNC_Polyhedron(zone)
    val vars = getVarsFromPolyhedron(zone)
    debug("before resetBck: " + zone2String(zone, clksM) + " with vars = " + vars.map{_.id})
    toReset foreach { 
    cV =>
      val clkname = cV._1
      val clkval = cV._2
      debug("resetback clk = " + clksM(clkname)  + " with id " + clkname.id + " to val = " + clkval)
      val coeff = new Coefficient(clkval)
      val le = new Linear_Expression_Coefficient(coeff)
      zoneCopy.affine_preimage(clkname, le, new Coefficient(1))
    }
    debug("after resetBck: " + zone2String(zoneCopy, clksM))
    //new NNC_Polyhedron(zone)
    zoneCopy
  }

  def upd(vv: Map[String, Int], toUpd: UpdV) : Map[String, Int] = {
    val keys = vv.keySet
    val updM :  Map[String, (Int, Boolean)] = toUpd.map{x => (x._1 -> (x._2, x._3))}.toMap
    val nvv = keys.map{k => 
      val v = updM.getOrElse(k, (0, false)) 
      val nv = if (v._2 == true) v._1 else (v._1 + vv(k))
      k -> nv
   }.toMap
    debug("after upd: " + nvv)
    nvv
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

  def startsWithNeg(e: Linear_Expression) = e.toString.trim.startsWith("-")

  /** @return true if e is a pos value
    */ 
  def getVal(e: Linear_Expression) = e match {
    case lcoeff: Linear_Expression_Coefficient => lcoeff.argument.getBigInteger.intValue 
    case _ => Int.MinValue
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

  def op2Str(op: Relation_Symbol) = op match {
    case Relation_Symbol.LESS_THAN => "<"
    case Relation_Symbol.LESS_OR_EQUAL => "<="
    case Relation_Symbol.GREATER_THAN => ">"
    case Relation_Symbol.GREATER_OR_EQUAL => ">="
    case Relation_Symbol.EQUAL => "=="
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
    val loc = getLoc(ss)
    val zone = new NNC_Polyhedron(getZone(ss))
    val curr_invP = inv(loc)
    if (!zone.is_empty()) {
      val flashFwdzone = flashFwd(zone)
      debug("after time_elapse: " + zone)
      zone.intersection_assign(curr_invP)
      debug("after intersection with cinv " + curr_invP + " : " + zone)
      val vv = getVV(ss)
      debug("timeS: vv = " + vv)
      (loc, new NNC_Polyhedron(zone), vv)
    }
    else noneSS
  }

//  def discS(zone: NNC_Polyhedron, next_invP: NNC_Polyhedron, guardP: NNC_Polyhedron, toReset: List[Linear_Expression_Variable]) = {
//  def discS(zone: Zone, next_inv: Invariant, guard: Guard, toReset: Reset) = {
  def discS(ss: SymbolicState, t: Transition, inv: InvMap) = {    
    val guard = getGuard(t)
    val toReset = getReset(t)
    val curr_loc = getLoc(ss)
    val next_loc = getSink(t)
    val curr_inv = inv(curr_loc)
    val next_inv = inv(next_loc)
    val zone = new NNC_Polyhedron(getZone(ss))
    debug("discS: t = " + toString(t) + " g.dim = " + guard.space_dimension + " zone = " + zone + " zone.dim = " + zone.space_dimension )
    zone.intersection_assign(guard)
    debug("after intersection with guard " + guard + " : " + zone)
    val nzone = reset(zone, toReset)
    //debug("before intersection with ninv " + next_inv + " ninv.dim = " + next_inv.space_dimension + " : " + nzone + " nzone.dim = " + nzone.space_dimension )
    nzone.intersection_assign(next_inv)
    debug("after intersection with ninv " + next_inv + " : " + nzone)
    val vv = getVV(ss)
    val gv = getGuardV(t)
    val gvB = gv.foldLeft(true)((r, c) => r && getBfromGVElem(vv, c))
    if (gvB) {
      val vvU = upd(vv, getUpd(t))
      (next_loc, new NNC_Polyhedron(nzone), vvU)
    }
    else noneSS
  }

//  def succ(zone: NNC_Polyhedron, curr_invP: NNC_Polyhedron, next_invP: NNC_Polyhedron, guardP: NNC_Polyhedron, toReset: List[Linear_Expression_Variable]) = {
//  def succ(zone: NNC_Polyhedron, curr_invP: NNC_Polyhedron, next_invP: NNC_Polyhedron, guardP: NNC_Polyhedron, toReset: List[Variable]) = {
  def succ(ss: SymbolicState,t: Transition, inv: InvMap) = {   
    val ds = discS(ss, t, inv)
    if (ds != noneSS) {
      //debug("succ: ds = " + ds)
      //val ns = timeS(ds.asInstanceOf[SymbolicState], inv)
      val ns = timeS(ds.asInstanceOf[SymbolicState], inv)
      if (ns != noneSS) {
	val nloc = getLoc(ns)
	val nzone = new NNC_Polyhedron(getZone(ns))
	nzone.topological_closure_assign() 
	debug("after closure: " + nzone) 
	(nloc, new NNC_Polyhedron(nzone), getVV(ns))
      }
      else noneSS
    }
    else noneSS
  }

  def allSucc(ss: SymbolicState, lt: Set[Transition], inv: InvMap) = lt.filter(t => getSource(t) == getLoc(ss)).map(t => succ(ss, t, inv)).filter{_!=noneSS}

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

  //initially all vars are 0
  def initV0(vars: Set[String]) = if (vars.size > 0) vars.map(v => (v -> 0)).toMap else Map[String,Int]().empty

  def initV(varsv: VarsV) = varsv

  //import scala.collection.mutable._

  import scala.collection.mutable.Stack
  import scala.collection.mutable.Queue

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

  implicit val reachLim = 90

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
    //val tovisit = new Stack[SymbolicState] 
    val tovisit = new Queue[SymbolicState] 
    val initZ = init(clocks)
    initZ.intersection_assign(invl0)
    val vars = getVars(ta)
    val iniV = initV(vars)
    //tovisit.push((l0, initZ))
    //normalised init
    val ninitZ = normZone(initZ, k)
    var s : SymbolicState = (l0, ninitZ, iniV)
    //tovisit.push(s)   
    tovisit.enqueue(s)
    var visited : Set[SymbolicState] = Set()
    var i = 0
    while(tovisit!=Nil && i < reachLim) {
      i += 1
      //val s = tovisit.pop
      val s =  tovisit.dequeue
      if (!(visited contains s)) {	
	val nz = new NNC_Polyhedron(getZone(s))
	debug("adding s = " + mkStateProp(s, clkM) + " to visited = " + visited.map{s => mkStateProp(s, clkM)})//, 1)
	visited = visited + ((getLoc(s), nz, getVV(s)))
	val succs =  allSucc(s, trans, inv)
	debug("succs = " + succs.map{s => mkStateProp(s, clkM)})//, 1)
	succs foreach { 
	  s => 
	    //val ns = (s._1, s._2)
	    val nZ = normZone(s._2, k)
	    //add to tovisit only if the new zone isn't false
	    if (zone2String(nZ, clkM) != "false") {
	      //debug("NORM: z = " + zone2String(s._2, clkM) + " normalised z = " + zone2String(nZ, clkM), -1)
	      val ns = (getLoc(s), nZ, getVV(s))
	      //tovisit.push(ns)
	      tovisit.enqueue(ns)
	    }
	}
      }
    }    
    //debug("stopped at i = " + i,-1)
    visited
  }

  def reachApprox(ta: TA)(implicit clockCeiling: Map[Clock, Int] = Map[Clock, Int]()) = {
    debug("/***** approxreach for " + toString(ta) + " ********/\n")    
    val l0 = getIni(ta)
    val invl0 = getInvMap(ta)(l0)
    val trans = getTrans(ta)
    val clkM = getClkMap(ta)
    val clocks = clkM.keySet
    val m = getMaxClkVal(ta)
    val k = if (!clockCeiling.isEmpty) clockCeiling.map{el => (el._1.id->el._2)} else clocks.map{clk => (clk.id -> m)}.toMap
    //println("clkM = " + clkM + " clocks = " + clocks + " k = " + k)
    val inv = getInvMap(ta)
    val vars = getVars(ta)
    val iniV = initV(vars)
    val tovisit = new Stack[SymbolicState] 
    val initZ = init(clocks)
    initZ.intersection_assign(invl0)
    //tovisit.push((l0, initZ))
    //normalised init
    val ninitZ = normZone(initZ, k)
    tovisit.push((l0, ninitZ, iniV))   
    var visited = scala.collection.mutable.Map[Location, Zone]().empty
    var i = 0
    while(tovisit!=Nil && i < reachLim) {
      i += 1
      if (i > 1) debug("at " + i + ":\nvisited =\n" +  visited.map{x => x._1 + ", " + zone2String(x._2, clkM)}.reduceLeft(_+"\n"+_) + "\ntovisit =\n" + tovisit.map{x => x._1 + ", " + zone2String(x._2, clkM) + ", " + x._3}.reduceLeft(_+"\n"+_))
      val s = tovisit.pop
      val nloc = getLoc(s)
      val visitedLocs = visited.keySet
      val nzone = getZone(s)
      val empty = new NNC_Polyhedron(clocks.size, Degenerate_Element.EMPTY)
      val currzone = visited.getOrElseUpdate(nloc, new NNC_Polyhedron(empty))
      //if ((currzone==nzone) || ((currzone!=nzone) && !(currzone.contains(nzone)))) {	
      if (!currzone.contains(nzone)) {	
	val nz = new NNC_Polyhedron(currzone)
	debug("visited s = " + mkStateProp(s, clkM))
	//nz.add_constraints(nzone.constraints)
	nz.poly_hull_assign(nzone)
	//nz.minimize()
	visited(nloc) = nz
	val succs =  allSucc((nloc, nz, getVV(s)), trans, inv)
	succs foreach { 
	  s => 
	    //val ns = (s._1, s._2)
	    val l = getLoc(s)
	    val z = getZone(s)
	    val nz = normZone(z, k)
	    val ns = (l, nz, getVV(s))
	    tovisit.push(ns)
	}
      }      
    }    
    debug("stopped at i = " + i,-1)
    visited
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
    val vars = getVars(ta)
    tovisit.push((l0, ninitZ, initV(vars)))
    var visited : Set[SymbolicState] = Set()
    var i = 0
    while(tovisit!=Nil && i < reachLim) {
      i += 1
      val s = tovisit.pop
      if (!(visited contains s)) {	
	val nz = new NNC_Polyhedron(getZone(s))
	val vv = getVV(s)
	val l = getLoc(s)
	debug("computeDelta: adding s = " + mkStateProp(s, clkM) + " to visited = " + visited.map{s => mkStateProp(s, clkM)})//, 1)
	visited = visited + ((l, nz, vv))
	val succs = trans.filter(t => getSource(t) == s._1).map(t => (getAct(t), succ(s, t, inv)))
	debug("computeDelta: succs = " + succs.map{s => mkStateProp(s._2, clkM)})//, 1)
	succs foreach { 
	  sp => 
	    val p = sp._1
	    val s = sp._2
	    val nZ = normZone(getZone(s), k)
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
	    val ns = (s._1, nZ, getVV(s))
	    tovisit.push(ns)
	}
      }
    }    
    //debug("stopped at i = " + i,-1)
    (visited, deltas)
  }

  var debugt = 1

  def zone2String(zone: NNC_Polyhedron, clksMap: Map[Variable, String], isZ3: Boolean = true) = {    
    //debug("zone2String: zone = " + zone + " clksm = " + clksMap)
    //vars should be of the form (0, 1, 2...)
    if (!clksMap.isEmpty) {
      val varsM = getVarsFromPolyhedron(zone).toList.map{v => (v -> v.id)}.toSeq.sortWith(_._1.toString.length > _._1.toString.length)
      val nmap = clksMap.map{el => (el._1.id -> el._2)}    
      var zoneS = if (isZ3) zone.toString else mkEFZone(zone)
      //var zoneS = zone.toString
      if (zoneS == "true") {
	if (isZ3) zoneS else ""
      }
      else {
	//letters foreach {l => zoneS = zoneS.replace(l.toString, nmap(lettersM(l)))}
	varsM foreach {
	  vz => 
	    val vstr = vz._1
	    val vid = vz._2	  
	    zoneS = zoneS.replace(vstr.toString, nmap(vid))
	    if (debugt < 20 && (zoneS.contains("gamma41") || zoneS.contains("alpha41") || zoneS.contains("eta41"))) {
	      println("vstr = " + vstr + "\nzone = " + zone + "\nzoneS = " + zoneS)
	      debugt += 1
	    }
	}
	debug("zone = " + zone + " nmap = " + nmap + "\n zoneS = " + zoneS)

	//replace " = " with " == " for Z3
	val res = zoneS.replace(" = ", " == ")      
	//debug("zone = " + zone + " clksMap = " + clksMap.map(el => (el._1.id, el._2)) + " transf. zone = " + res)
	if (isZ3)
	  res
	else 
	  res.split(",").foldLeft("")((r, c) => r + " && " + mkIneq(c)).drop(4)
      }
    }
    else {
      println("zone2String: clksm is empty; return zone.toString")
      zone.toString
    }
  }

  def locProp(l: Location, isZ3: Boolean = true) = {
    if (isZ3) {
      if (!ISLOCINT) 
	l 
      else {
	//maybe l is a global loc, i.e., a string l1, l2, ...
	val locs = l.split(",")
	if (locs.length <= 0) l + " == 1" else (locs.reduceLeft(_  + " == 1, " + _) + " == 1")
      }
    }
    else
      l.split(",").reduce((r,c) => r + " && " + c)
  }

  def vars2String(vm: Map[String, Int]) = if (vm.size > 0) vm.map{x => x._1 + " == " + x._2}.reduceLeft(_+","+_) else ""

  def mkStateProp(s: SymbolicState, clksMap: Map[Variable, String], isZ3: Boolean = true) = {
    val locP = locProp(getLoc(s), isZ3)
    val zoneS = zone2String(getZone(s), clksMap, isZ3)
    val varsV = vars2String(getVV(s))
    if (isZ3)
      "And("  + locP + (if (zoneS == "true") "" else ", " + zoneS) + (if (varsV != "") ", " + varsV else "") + ")"
    else 
      locP + (if (zoneS == "true") "" else " && " + zoneS)
  }

  def mkGVElemProp(elem: GuardVElem, isZ3: Boolean = true) : String = {
    val l = getVN(elem)
    val r = getVV(elem)
    val op = getOp(elem)
    val res =  l + op + r
    if (isZ3)
      res
    else  {
      //for efsmt no neg signs!
      if (!l.trim.startsWith("-") && r >= 0)
	  mkIneq(res)
       else {
	 val nl = if (l.trim.startsWith("-")) l.trim.drop(1) else l
	 if (r >= 0) {
	   /*
	    * -l <= r \equiv 0 <= l + r
	    * -l >= r \equiv 0 >= l + r 
	   */
	   "0 " + op + " " + nl + " + " + r
	 }
	 else {
	   val nr = (0-r)
	   if (l.trim.startsWith("-")) {	   
	   /*
	    * -l <= -r \equiv l >= r \equiv r <= l
	    * -l >= -r \equiv l =< r \equiv r >= l 
	   */
	   nr + op + nl
	   }
	   else nl + " + " + nr + " " + op + " 0 "
	 }
       }
    }
  }

  def mkGVProp(gv: GuardV, isZ3: Boolean = true) : String = {
    if (isZ3) 
      if (gv.isEmpty) "" else if (gv.size == 1) mkGVElemProp(gv.head) else "And(" + gv.map{mkGVElemProp(_)}.reduceLeft(_ + ", " + _)
    else
      if (gv.isEmpty) "" else if (gv.size == 1) mkGVElemProp(gv.head, isZ3) else gv.map{mkGVElemProp(_, isZ3)}.reduceLeft(_ + " && " + _)

  }

  def post(ta: TA) = "Or(" + reach(ta).foldLeft("")((r, c) => r + ", " + mkStateProp(c, getClkMap(ta))).drop(1) + ")"  

/*
  def mkUppaalPropNoHist(loc: Location, z: Zone, taName: String, clks: ClkMap)  = {
    taName + "." + loc + " and " + 
  }
*/

  def mkUppaalPropFromLinExp(e: Linear_Expression, taName: String, clks: ClkMap) = {
    def aux(e: Linear_Expression): (String, Boolean) = e match {   
      case lv: Linear_Expression_Variable => ((if (taName != "") (taName + ".") else "") + clks.filter(c => c._1.id==lv.argument.id).head._2, false)
      case ls: Linear_Expression_Sum => {
	val (l, isNegL) = aux(ls.left_hand_side)
	val (r, isNegR) = aux(ls.right_hand_side)
	if (isNegL) (r + " - " + l, false) 
	else if (isNegR) (l + " - " + r, false) 
	else (l + " + " + r, false)
      }
      case ld: Linear_Expression_Difference => {
	val l = aux(ld.left_hand_side)._1 
	val r = aux(ld.right_hand_side)._1
	(l + " - " + r, false)
      }
      case lt: Linear_Expression_Times => {
	//println("lt = " + lt)
	val res = aux(lt.linear_expression)._1
	if (lt.coefficient.toString == "1") (res, false) else (res, true)
      }
      case lm: Linear_Expression_Unary_Minus => {
	//println("lm = " + lm + " lm.arg = " + lm.argument)
	val (v, isNeg) = aux(lm.argument)
	if (isNeg) (v, false) else (v, true)
      } 
      case lcoeff: Linear_Expression_Coefficient => {
	//println("lcoeff = " + lcoeff)
	val v = lcoeff.toString
	if (v.startsWith("-")) (v, true) 
	else (v, false) 
      }
    }
    aux(e)
  }

  def mkUppaalFromConstraint(c: Constraint, taName: String, clksM: ClkMap) = {
    val l = c.left_hand_side
    val r = c.right_hand_side
    val op = c.kind
    val (nl, isNegL) = mkUppaalPropFromLinExp(l, taName, clksM) 
    val nop = if (!isNegL) op else oppositeOp(op)
    //println("isneg = " + isNegL + " r = " + r)
    val (nr0, isNegR) =  if (!isNegL) mkUppaalPropFromLinExp(r, taName, clksM) else mkUppaalPropFromLinExp(r.unary_minus, taName, clksM)
    //println("isneg = " + isNegL + " r = " + r)
    //if !isNegR  nr0 is -x so we drop the first char
    val nr = if (!isNegR && isNegL) nr0.drop(1) else nr0 
    val nc = nl + op2Str(nop) + nr
    //println("c = " + c + " nc = " + nc)
    nc
  }

  def mkUppaalPropFromPoly(p: Polyhedron, clks: ClkMap)(implicit taName: String="")  = {
    //println("p = " + p)
    import collection.JavaConverters._
    val constraints = p.constraints.asScala
    val nc = constraints.size    
    val res = if (constraints.isEmpty) "" else constraints.map{mkUppaalFromConstraint(_, taName, clks)}.reduceLeft(_+" and "+_) 
    //println("resp = " + res)
    res
  }

  def mkUppaalProp(loc: Location, z: Zone, taName: String, clks: ClkMap)  =  {
    val uppaalZone = mkUppaalPropFromPoly(z, clks)(taName)
    if (uppaalZone == "") "(" + taName + "." + loc + ")"
    else "(" + taName + "." + loc + " and " + uppaalZone + ")"
  }

  def mkUppaalPropMulti(loc: Location, zs: Set[Zone], taName: String, clks: ClkMap)  = {
    if (zs.size == 1) mkUppaalProp(loc, zs.head, taName, clks)
    else "(" + taName + "." + loc + " and (" + zs.map{z => "(" + mkUppaalPropFromPoly(z, clks)(taName) + ")"}.filter{_!=""}.reduceLeft(_ + " or " + _) + "))"
  }

  def getUppaalInvQuery(ta: TA) = {
    //val reachS = reachApprox(ta)
    val reachS = reach(ta).groupBy(_._1).map{x => (x._1, x._2.map{_._2})}
    //println("reachs = " + reachS)
    val taName = getName(ta)
    val clks = getClkMap(ta)
    val reachLocs = reachS.keys
    if (reachS.isEmpty) "false"
    else if (reachLocs.size == 1) "A[] (" + mkUppaalPropMulti(reachLocs.head, reachS(reachLocs.head), taName, clks) + ")"
//    else "A[] " + reachS.foldLeft("")((r,c) => r + " or " + mkUppaalProp(c._1, c._2, taName, clks)).drop(1) + ")"
    else "A[] (" + reachS.map{c => "(" + mkUppaalPropMulti(c._1, c._2, taName, clks) + ")"}.reduceLeft(_+ " or " +_) + ")"
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

  def eqInteraction(alpha: List[String], isZ3: Boolean = true) = {
    val indices = List.range(0, alpha.length)
    val bl = if (isZ3) "" else "["
    val br = if (isZ3) "" else "]"
    val eqs0 = for(i <- indices; j <- indices.dropWhile(_<=i)) yield bl + hcname + alpha(i) + " == " + hcname + alpha(j) + br
    val eqs = eqs0.toList
    if (eqs == List()) "" 
    else if (eqs.length == 1) eqs(0)
    else if (isZ3)
      eqs.tail.foldLeft("And(" + eqs(0))((r, c) => r + ", " + c) + ")"
    else
      eqs.tail.foldLeft(eqs(0))((r, c) => r + " && " + c)
  }

  def leqInteraction(alpha: List[String], im: List[List[String]], isZ3: Boolean = true) = {
    //the name of the history clock
    val a = alpha.head
    val portsIM = im.flatten.distinct
    val bl = if (isZ3) "" else "["
    val br = if (isZ3) "" else "]"
    val ineqs = for(p <- portsIM) yield bl + hcname + a + " <= " + hcname + p + br
    if (ineqs.length > 1) 
      if (isZ3)
	ineqs.tail.foldLeft("And(" + ineqs(0))((r, c) => r + ", " + c) + ")"
      else
	ineqs.tail.foldLeft(ineqs(0))((r, c) => r + " && " + c) 
    else ineqs.mkString
  }

  /** returns \gamma \ominus \alpha as on the slides. 
    */ 
  def imdiff(alpha: List[String], im: List[List[String]]) = im.map{el => (el.toSet -- alpha.toSet).toList}.filter{el => el.length >= 1}

  /** returns \eqs(\gamma) as on the slides. the impl is precisely the rec def, so the resulting formulae may be huge.
    * you might want to use `getEqsSimpl` instead.
    */ 
  def getEqs(im: List[List[String]], isZ3: Boolean = true) : String = {
    //println("im = " + im)
    if (im == List()) ""
    else if (im.length <= 1) eqInteraction(im.head, isZ3) 
    else {
      //val c = im.head
      //val h = "And(" + eqInteraction(c) + ", " + leqInteraction(c, imdiff(c, im)) + ", " + getEqs(imdiff(c, im)) + ")"
      val res = for { 
	  alpha <- im; 	
	  val eqAlpha = eqInteraction(alpha); 
	  val leq = leqInteraction(alpha, imdiff(alpha, im), isZ3);
	  val rem = getEqs(imdiff(alpha, im).filter{_.length > 1}, isZ3)
	  } yield "And(" + (eqAlpha + (if (leq != "") (", " + leq) else "") + (if (rem != "") (", " + rem) else "")) + ")"
      "Or(" + res.tail.foldLeft(res(0))((r,c) => r + ", " + c) + ")"
    }
  }

  /** returns \eqs(\gamma) as on the slides. it makes use of disjointness, s.t. the resulting formulae are minimal in size.
    */ 
  def getEqsSimpl(im: List[List[String]], isZ3: Boolean = true) : String = {
    //println("#im = " + im)
    if (im == List()) ""
    else if (im.length <= 1 && im.head != eps) eqInteraction(im.head, isZ3) 
    else {   
      val alpha = im.head
      val (p1, p2) = im.tail.partition(alphai => (alphai.toSet intersect alpha.toSet) == Set())
      if (p1 != List()) {
	val p1Eqs = getEqsSimpl(p1, isZ3)
	val p2Eqs = getEqsSimpl(alpha +: p2, isZ3)
	if (p1Eqs != "") {
	  if (p2Eqs != "")
	    if (isZ3)
	      "And(" + p1Eqs + ", " + p2Eqs + ")"
	    else
	      p1Eqs + " && " + p2Eqs 
	  else p1Eqs
	}
	else p2Eqs
      }
      else {
	if (isZ3) {
	val res = for { 
	  alpha <- im; 	
	  val eqAlpha = eqInteraction(alpha, isZ3); 
	  val leq = leqInteraction(alpha, imdiff(alpha, im), isZ3);
	  val rem = getEqsSimpl(imdiff(alpha, im).filter{_.length > 1}, isZ3);
	  val all = List(eqAlpha, leq, rem).filter(_!="");
	  if (all != List())
	} //yield "And(" + (if (eqAlpha != "") + (if (leq != "") (", " + leq) else "") + (if (rem != "") (", " + rem) else "")) + ")"
	yield "And(" + all.reduceLeft(_+ ", " +_) + ")"
	"Or(" + res.tail.foldLeft(res(0))((r,c) => r + ", " + c) + ")"
	}
	else {
	val res = for { 
	  alpha <- im; 	
	  val eqAlpha = eqInteraction(alpha, isZ3); 
	  val leq = leqInteraction(alpha, imdiff(alpha, im), isZ3);
	  val rem = getEqsSimpl(imdiff(alpha, im).filter{_.length > 1}, isZ3);
	  val all = List(eqAlpha, leq, rem).filter(_!="");
	  if (all != List())
	} //yield "And(" + (if (eqAlpha != "") + (if (leq != "") (", " + leq) else "") + (if (rem != "") (", " + rem) else "")) + ")"
		  yield all.reduceLeft(_+ " && " +_) 
	"(" + res.tail.foldLeft(res(0))((r,c) => r + " || " + c) + ")"
	}
      }
    }
  }


  /** Gen strings repr Z3 formulae */
  def genDeclLocsTA(ta: TA) = {
    val locs = getLocs(ta).toList
    if (locs.isEmpty) ""
    else if (locs.length == 1) {
      val loc = locs.head 
      val typeLoc = if (ISLOCINT) "Int" else "Bool"
      (loc + " = " + typeLoc + "('" + loc + "')")
    }
    else {
      val names = locs.reduceLeft(_+", "+_) //locs.tail.foldLeft(locs(0))((r, c) => r + ", " + c)
      val body =  locs.reduceLeft(_+" "+_) //locs.tail.foldLeft(locs(0))((r, c) => r + " " + c)
      val typeLocs = if (ISLOCINT) "Ints" else "Bools"
      (names + " = " + typeLocs + "('" + body + "')")
    }
  }

  def genDeclLocsSystem(s: TAS) = s.tail.foldLeft(genDeclLocsTA(s(0)))((r,c) => r + "\n" + genDeclLocsTA(c))

  def genDeclVarsTA(ta: TA) = {
    val vars = getVars(ta).keySet
    if (vars.isEmpty) "" 
    else {
      val names = vars.reduceLeft(_+","+_)//vars.tail.foldLeft(vars.head)((r, c) => r + ", " + c)
      val body = vars.reduceLeft(_+" "+_)//vars.tail.foldLeft(vars(0))((r, c) => r + " " + c)
      val typeVars = if (vars.size > 1) "Ints" else "Int"
      (names + " = " + typeVars + "('" + body + "')")
    }
  }

  def genDeclVarsSystem(s: TAS) = s.tail.foldLeft(genDeclVarsTA(s(0)))((r,c) => r + "\n" + genDeclVarsTA(c))

  def genDeclClksTA(ta: TA) = {
    val clks = getClkMap(ta).map{_._2}.toList
    val names = clks.tail.foldLeft(clks(0))((r, c) => r + ", " + c)
    val body = clks.tail.foldLeft(clks(0))((r, c) => r + " " + c)
    val typeClks = if (clks.size > 1) "Ints" else "Int"
    (names + " = " + typeClks + "('" + body + "')")    
  }

  def genDeclClksSystem(s: TAS) = s.tail.foldLeft(genDeclClksTA(s(0)))((r,c) => r + "\n" + genDeclClksTA(c))

  def genAt2LocsTA(ta: TA) = {
    val locs = getLocs(ta).toList    
    if (locs.length < 2) "False"    
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

  def genAt2LocsSystem(s: TAS) = "Or(" + s.tail.foldLeft(genAt2LocsTA(s(0)))((r,c) => r + "," + genAt2LocsTA(c)) + ")"

  def genLocalInvTA(ta: TA) = "And(" + post(ta) + ", " + genNotAt2LocsTA(ta) + ")"

  //def genLocalInvs(s: System) = s.tail.foldLeft(INV + getName(s(0)) + " = " + post(s(0)))((r, c) => r + "\n" + (INV + getName(c) + " = " + post(c)))

  /** en(a,t) = at(l) \wedge gv \wedge ( (flashback(g) \wedge inv(l)) \ (flashback(flashback(g)\I)) ) , where t = (l, a, g, gv, r, upd, l')  */
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
    //TODO: check if fixed
    val ss = (loc, diff, emptyVV)
    val gv = getGuardV(t)
    val gvProp = mkGVProp(gv)
    val stateProp = mkStateProp(ss, clksM)
    if (gvProp != "") "And(" + stateProp + "," + gvProp + ")" else stateProp
  }

  /** en(a,t) = at(l) \wedge ( (flashback(g) \wedge inv(l')) where t = (l, a, g, r, l')  */
  //def enTrans(t: Transition, I: Invariant, In: Invariant, clksM: Map[Clock, String]) = {
  def enTrans(triple: (Invariant, Transition, Invariant), clksM: Map[Clock, String], isZ3: Boolean = true) = {
    val (invsource, t, invsink) = triple
    val clks = clksM.keySet    
    val guard = new NNC_Polyhedron(getGuard(t))    
    val toReset = getReset(t)
    val resetIn = resetBck(invsink, toReset)(clksM)
    val gIn = new NNC_Polyhedron(guard)
    gIn.intersection_assign(invsource)
    gIn.intersection_assign(resetIn)
    debug("enTrans : clksM = " + clksM.map{e => (e._1.id, e._2)})
    //G.concatenate_assign(flashBwd(GI, clks))
    val flashbgIn = flashBwd(gIn, clks)
    debug("enTrans: guard = " + zone2String(guard,clksM) + 
	  ", invsource = " + zone2String(invsource,clksM) + 
	  ", invsink = " + zone2String(invsink,clksM) + 
	  ", resetIn = " + resetIn + "\n gIn = " + gIn + 
	  ", flashback(g wedge [r]In) = " + flashbgIn)
    //TODO: check if fixed
    val ss = (getSource(t), flashbgIn, emptyVV)
    val gv = getGuardV(t)
    val gvProp = mkGVProp(gv, isZ3)
    val stateProp = mkStateProp(ss, clksM, isZ3)
    if (isZ3)
      if (gvProp != "") "And(" + stateProp + "," + gvProp + ")" else stateProp
    else
      if (gvProp != "") stateProp + " && " + gvProp else stateProp
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
    val varsM = getVars(ta)
    //TODO: check if fixed
    val ss = (loc, diff, emptyVV)
    val gv = getGuardV(t)
    val gvProp = mkGVProp(gv)
    val stateProp = mkStateProp(ss, clksM)
    if (gvProp != "") "And(" + stateProp + "," + gvProp + ")" else stateProp
  }

  def enAct(a: String, tas: TAS) = {
    val tasWithA = tas.filter{ta => (getTrans(ta).filter{t => getAct(t) == a}).size > 0}
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
    //debug("c = " + c + " revClksGM = " + revClksGM.map{x => (x._1, x._2.id)} + " renamed c = " + nc)
    nc
  }

  /** @return the zone where we renamed the clocks in clksM wrt clocks in clksGM
    * It calls renameLinExp for the left, right sides of each constraint.
    */
  def renameZone(z: Zone, clksM: Map[Clock, String], clksGM: Map[Clock, String]) = {
    //debug("renameZone: z = " + zone2String(z, clksM))
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
    //debug("renameZone: nz = " + zone2String(nz, clksGM))
    nz      
  }

  /** @return the resets where we renamed the clocks in clksM wrt clocks in clksGM
    */
  def renameReset(toReset: Reset, clksM: Map[Clock, String], clksGM: Map[Clock, String]) = {
    val revClksGM = clksGM.map{e => (e._2 -> e._1)}
    //println("renameReset: toreset = " + toReset + "\nclksM = " + clksM + "\nclksGM = "  + clksGM + "\nrevClksGM = " + revClksGM)
    //println("rr: " + clksM.keys)
    //if (toReset.size > 0) println("rrrr: " + clksM(toReset.toList(0)._1))
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

 def mkEFZone(z: Zone) = {
    import collection.JavaConverters._
    val constraints = z.constraints.asScala
    val nc = constraints.size    
    var s = ""
    constraints foreach {
      c => 
	var lhs = c.left_hand_side
        var lstr = lhs.toString
	var op = c.kind
	var rhs = c.right_hand_side
	var rhsVal = getVal(rhs)	  
	if (rhsVal < 0) {       	 
	  if (startsWithNeg(lhs)) {
	    op = oppositeOp(op)
	    lhs = lhs.unary_minus
	    lstr = lhs.toString
	    rhsVal = 0 - rhsVal	  
	  }
	  // a + b op -ct = a + b + ct op 0
	  else {
	    rhsVal = 0
	    lstr = lstr + " + " + rhsVal
	  }
	}
	else 
	  if (startsWithNeg(lhs)) {
	    lstr = lhs.unary_minus.toString
	  }
	if (lstr.startsWith("-")) println("\t\t\t\t lhsa = " + lstr + " in c = " + c)
	s += lstr + " " + op2Str(op) + " " + rhsVal + ", "
    }
   s.dropRight(2).trim
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
      val gI = invM(getSource(tl.head))
      val gINext = invM(getSink(tl.head))
      debug("makeGobalTrans of tl = " + tl.map{toString(_)(clksGM)} + " returns gt = " + toString(gt)(clksGM) + " gI = " + zone2String(gI,clksGM)  + " gINext = " + zone2String(gINext,clksGM))
      (gI, gt, gINext)
    }
    else {     
      val indices = List.range(0, tl.length)
      val gsourceL = tl.map{t => getSource(t)}
      val gsinkL = tl.map{t => getSink(t)}
      //val gIL = indices.map{i => new NNC_Polyhedron(renameZone(invM(gsourceL(i)), clksMs(owner(i)), clksGM))}
      val gIL = indices.map{i => new NNC_Polyhedron(renameZone(invM(gsourceL(i)), clksMs(owner(i)), clksGM))}
      val gINextL = indices.map{i => new NNC_Polyhedron(renameZone(invM(gsinkL(i)), clksMs(owner(i)), clksGM))}

      val gI = gIL.head
      val gINext = gINextL.head
      gINextL.foreach{i => gINext.intersection_assign(i)}
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
      val ggv = tl.flatMap{t => getGuardV(t)}.toSet
      val gupd = tl.flatMap{t => getUpd(t)}.toSet
      val gt : Transition = (gsource, ga, gg, ggv, gr, gupd, gsink)
      debug("makeGobalTrans of tl = " + tl.map{toString(_)(clksGM)} + " returns gt = " + toString(gt)(clksGM) + " gI = " + zone2String(gI,clksGM)  + " gINext = " + zone2String(gINext,clksGM))
      (gI, gt, gINext)
    }
  }

  def mkGT(tlWithOwner: List[(Int, Transition)], invM: InvMap, clksMs: List[Map[Clock, String]], clksGM: Map[Clock, String], globalLoc: List[(Location,Int)]) = {    
    val tl = tlWithOwner.map{_._2}
    val owner = tlWithOwner.map{_._1}
    require (tl.length > 0 && globalLoc.length > 0, println("[Err in makeGlobalTrans]: the tl or global loc is empty"))
    //won't work if clocks are shared in diff components (see the renaming in makeGlobalTrans)
    val gIL = globalLoc.map{li => new NNC_Polyhedron(renameZone(invM(li._1), clksMs(li._2), clksGM))}
    val gInv = gIL(0)
    gIL.foreach{inv => gInv.intersection_assign(inv)}
    if (tl.length == 1) {
      val gt = tl.head 
      val gINext = invM(getSink(tl.head))
      debug("makeGobalTrans of tl = " + tl.map{toString(_)(clksGM)} + " returns gt = " + toString(gt)(clksGM) + " gI = " + zone2String(gInv,clksGM)  + " gINext = " + zone2String(gINext,clksGM))
      (gInv, gt, gINext)
    }
    else {     
      val indices = List.range(0, tl.length)
      val gsinkL = tl.map{t => getSink(t)}
      val gINextL = indices.map{i => new NNC_Polyhedron(renameZone(invM(gsinkL(i)), clksMs(owner(i)), clksGM))}
      val gINext = gINextL.head
      gINextL.foreach{i => gINext.intersection_assign(i)}
      val gsource = globalLoc.tail.foldLeft(globalLoc.head._1)((r, c) => r + ", " + c._1)
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
      val ggv = tl.flatMap{t => getGuardV(t)}.toSet
      val gupd = tl.flatMap{t => getUpd(t)}.toSet
      val gt : Transition = (gsource, ga, gg, ggv, gr, gupd, gsink)
      debug("makeGobalTrans of tl = " + tl.map{toString(_)(clksGM)} + " returns gt = " + toString(gt)(clksGM) + " gI = " + zone2String(gInv,clksGM)  + " gINext = " + zone2String(gINext,clksGM))
      (gInv, gt, gINext)
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
  def genDISInteraction(alpha: List[String], system: TAS) = {
    val clksML = system.map{getClkMap(_)}
    val clksMAll = clksML.reduce((r, c) => r ++ c)
    debug("clksMs = " + clksMAll)
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
    debug("for alpha = " + alpha + " cp = " + cp.map{tl => tl.map{toString(_)(clksMG)}})    
    // construct "global transitions" corr. to each tuple in tCs
    val tIGs = cp.map{tl => makeGlobalTrans(owners.zip(tl), invMs, clksMs, clksMG)}	
    debug("genDisInteraction tIGs = " + tIGs.map{gt => toString(gt._2)(clksMG)})
    //val disGT = tIGs.map{gt => "Not(" + enTrans0(gt._1, gt._2, clksMG) + ")"}  
    //for the last trans we don't have invariant, so we take true
    //val disGT = List.range(0, tIGs.length-1).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, tIGs(i+1)._2, clksMG) + ")"} :+ ("Not(" + enTrans(tIGs.last._1, tIGs.last._2, new NNC_Polyhedron(clksMG.size, Degenerate_Element.UNIVERSE), clksMG) + ")")
    //val disGT = List.range(0, tIGs.length).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, clksMG) + ")"} 
    val disGT = List.range(0, tIGs.length).map{i => "Not(" + enTrans(tIGs(i), clksMG) + ")"} 
    if (disGT.length == 1)  disGT.head
    else "And(" + disGT.tail.foldLeft(disGT.head)((r,c) => r + ", " + c) + ")"  
  }

  def genDISIAG(alpha: List[String], system: TAS, globalLoc: List[(Location,Int)], isZ3: Boolean = true) = {
    val clksML = system.map{getClkMap(_)}
    val clksMAll = clksML.reduce((r, c) => r ++ c)
    debug("clksMs = " + clksMAll)
    //debug("invsMs = " + system.map{ta => getInvMap(ta).foldLeft("")(_+"\n"+_)})
    val indices = List.range(0, alpha.length)
    //participating TA choices: for each a in alpha return the TAs (together with a and index i) which have a in their alph
    val pTaCs0 = List.range(0, system.length).filter{i => (alpha.toSet & getAlph(system(i))) != Set()}.map{i => (i, (alpha.toSet & getAlph(system(i))).toList(0), system(i))}
    //val pTaCs0 = indices.map{i => (i, alpha(i), system.dropWhile(ta => !getAlph(ta)(alpha(i))))}
    //use the index i to get the list of owners, i.e., to which comp. does the participating port in alpha belong to
    val owners = pTaCs0.map{el => el._1}
    debug("owners = " + owners)
    //remove the index i, it's no longer needed
    val pTaCs = pTaCs0.map{el => (el._2, el._3)}
    //require that any act in an alpha appears in a TA alph
    require(pTaCs.length >= alpha.length, println("There exists an act in " + alpha + " which doesn't appear in any TA alph"))
    //assuming all alphs are disjoint, there should be a unique TA for each a; so it's fine to take the head
    //pTaA is the list of TAs zipped with the acts from alpha which are in their alphs
    val pTaA = pTaCs.map{el => (el._2, el._1)}.toList    
    val clksMG = makeGlobalClkMap(clksML)
    val invG = system.map{ta => getInvMap(ta)}.reduceLeft(_++_)
    //tCs represents the list of trans labelled a for each a in alpha
    val tCs = indices.map{i => getTransFromAct(pTaA(i)._1, pTaA(i)._2).toList}
    //cp is the cartesian prod of transitions in tCs 
    val cp = cpLTrans(tCs)
    debug("for alpha = " + alpha + " cp = " + cp.map{tl => tl.map{toString(_)(clksMG)}})    
    // construct "global transitions" corr. to each tuple in tCs
    val tIGs = cp.map{tl => mkGT(owners.zip(tl), invG, clksML, clksMG, globalLoc)}	
    debug("genDisInteraction tIGs = " + tIGs.map{gt => toString(gt._2)(clksMG)})
    //val disGT = tIGs.map{gt => "Not(" + enTrans0(gt._1, gt._2, clksMG) + ")"}  
    //for the last trans we don't have invariant, so we take true
    //val disGT = List.range(0, tIGs.length-1).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, tIGs(i+1)._2, clksMG) + ")"} :+ ("Not(" + enTrans(tIGs.last._1, tIGs.last._2, new NNC_Polyhedron(clksMG.size, Degenerate_Element.UNIVERSE), clksMG) + ")")
    //val disGT = List.range(0, tIGs.length).map{i => "Not(" + enTrans(tIGs(i)._1, tIGs(i)._2, clksMG) + ")"} 
    if (isZ3) {
      val disGT = List.range(0, tIGs.length).map{i => "Not(" + enTrans(tIGs(i), clksMG) + ")"} 
      if (disGT.length == 1)  disGT.head
      else "And(" + disGT.tail.foldLeft(disGT.head)((r,c) => r + ", " + c) + ")"  
    }
    else {
      val disGT = List.range(0, tIGs.length).map{i => enTrans(tIGs(i), clksMG, isZ3)} 
      if (disGT.length == 1)  disGT.head
      else disGT.reduce((r,c) => r + " || " + c) 
    }      
  }


  //eps trans happen by themselves; they're global by themselves
  def genDISEps(system: TAS) = {
    val dis = system.map{
      ta =>
	val clksM = getClkMap(ta)
	val invsM = getInvMap(ta)
	val epsTrans = getTrans(ta).filter(t => getAct(t) == eps)
	epsTrans.map{t => "Not(" + enTrans((invsM(getSource(t)), t, invsM(getSink(t))), clksM) + ")"}.toList
    }.flatten
    if (dis.length == 1)  dis.head
    else "And(" + dis.tail.foldLeft(dis.head)((r,c) => r + ", " + c) + ")"  
  }

  /** generate DIS(\gamma) = \neg EN(\gamma); EN(\gamma) = \vee_{\alpha \in \gamma} en(\alpha), so DIS(\alpha) = \wedge_{\alpha \in \gamma} DIS(\alpha). */
  def genDIS(im: List[List[String]], system: TAS) = {
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
    val ss = (loc, nzone, emptyVV)
    mkStateProp(ss, getClkMap(ta))
  }

  def enActOld(a: String, system: TAS) = {
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
    debug("delayLoc inv = " + inv.toString)
    val ninv = mkStateProp((l, inv, emptyVV), clksMap).replace("==", "<").replace(">=", ">").replace("<=", "<")
    debug("delayLoc ninv = " + ninv)
    ninv
    //"And(" + l + ", " + inv.toString.replace("==", "<") + ")"
  }

  /** for any loc l with inv diff from True we construct the prop not(l /\ strict(inv)) to express deadlock states wrt time
    */
  def deadLoc(l: Location, inv: NNC_Polyhedron, clksMap: Map[Clock, String]) = {
    val strictInv = zone2String(inv, clksMap).replace("<=", "<").replace(">=", ">")
    val res = "Not(And(" + l + ", " + strictInv + "))"
    debug("deadLoc res = " + res)
    res
  }

  def delayDis(ta: TA) = {
    val invM = getInvMap(ta)
    //println("invM = " + invM)				 
    val locsWithInv = getLocs(ta).filter{l => invM(l).toString != "true"}.map{l => (l, invM(l), getClkMap(ta))}
    val res = if (locsWithInv.isEmpty) "" else "And(" + locsWithInv.map{lp => deadLoc(lp._1, lp._2, lp._3)}.reduceLeft(_ + ", " + _) + ")"    
    debug("delayDis res = " + res)
    res
  }

  /**@return \/_ta delayDis(ta)
    */ 
  def genDISInvs(system: TAS) = {
    val delayDisL = system.map{ta => delayDis(ta)}.filter(_!="")
    if (delayDisL.isEmpty) "" else "Or(" + delayDisL.reduceLeft(_ + ", " + _) + ")"
  }

  def genDISInteractionOld(alpha: List[String], system: TAS) = {
    val disacts = alpha.map{ai => "Not(" + enActOld(ai, system) + ")"}
    if (disacts.length == 1)  disacts.head
    //else "Or(" + disacts.tail.foldLeft(disacts.head)((r,c) => r + ", " + c) + ")"  
    else "Or(" + disacts.reduceLeft(_ + ", " + _) + ")"
  }

  /** generate DIS(\gamma) = \wedge_alpha DIS(alpha) \wedge \wedge_l delayDIS(l) */
  def genDISOld(im: List[List[String]], system: TAS) = {
    val disAlphas = "And(" + im.map{alpha => genDISInteractionOld(alpha, system)}.reduceLeft(_ + ", " + _) + ")"
    
    val disDelays = genDISInvs(system)

    if (disDelays == "") disAlphas else "And(" + disAlphas + ", " + disDelays + ")"
  }

  import scala.io.Source._

  def genDeclHistoryIM(im: List[List[String]]) = {
    val clks = im.map{alpha => mkIMClk(alpha.toSet)}
    val names = clks.tail.foldLeft(clks(0))((r, c) => r + ", " + c)
    val body = clks.tail.foldLeft(clks(0))((r, c) => r + " " + c)
    (names + " = Ints('" + body + "')")    
  }

  def genTCZ3(s: TAS, im0: List[List[String]], portDelays: Map[String, Int], dis0: String="", defaultZ3FileName: String = "defaultZ3.py", strengthen: String = "", defaultII: String = "", isSym: Boolean = false) = {
    val galph = s.flatMap{ta => getAlph(ta)}.toSet
    //filter out any port which isn't in a ta in s
    val im = im0.map{alpha => alpha.filter(p => galph(p))}.filter(im => !im.isEmpty)
    println("im = " + im)
    val disIn = if (dis0 == "") genDIS(im, s) else dis0
    val disOld = if (dis0 == "") genDISOld(im, s) else dis0
    val n = s.length
    val indices = List.range(0, n)
    val ims = im.map{alpha => alpha.toSet}.toSet
    val declLocs = genDeclLocsSystem(s)
    val declClks = genDeclClksSystem(s) 
    val declVars = genDeclVarsSystem(s)
    val declHistoryIM = genDeclHistoryIM(im.filter{_!=List(eps)})
    val invsNames = s.map{ta => INV + getName(ta)}
    val localInvs = indices.tail.foldLeft(invsNames(0) + " = " + genLocalInvTA(s(0)))((r, c) => r + "\n" + invsNames(c) + " = " + genLocalInvTA(s(c)))
    val sourceII = "sourceII = " + genII(s, ims)
    val II = "II = " + (if (ISLOCINT) defaultII else "getII(sourceII)") + " \n"
    val eqs = "Eqs = " + getEqs(im)
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
    declVars + "\n" +
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

  def genTCZ3Old(s: TAS, im: List[List[String]], dis0: String="", defaultZ3FileName: String = "defaultZ3.py", strengthen: String = "") = {
    val disIn = if (dis0 == "") genDIS(im, s) else dis0
    val disOld = if (dis0 == "") genDISOld(im, s) else dis0
    val ims = im.map{_.toSet}.toSet
    val n = s.length
    val indices = List.range(0, n)
    //val eqs = "Eqs = " + getEqs(im)
    val eqsSimpl = "EqsS = " + getEqsSimpl(im)
    val declLocs = genDeclLocsSystem(s)
    val declClks = genDeclClksSystem(s)
    val declVars = genDeclVarsSystem(s)
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
    declVars + "\n" + 
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
  def companionTrans(i: Int, t: Transition, system: TAS, im: Set[Set[String]]) = {
    val indices = List.range(0, system.length)
    val a = getAct(t)
    val res = (for(alpha <- im; val remalpha = (alpha - a); if (alpha.contains(a))) yield cpLTrans(indices.map{i => getTrans(system(i)).filter(t => remalpha.contains(getAct(t))).toList}.filter(_!=List()))).toList.flatten
    //debug("companionTrans: trans = " + toString(t) + " im = " + im + " res = " + res.map{lt => lt.map{toString(_)}})
    res
  }

  /** @return a list of sets of transitions with the indices of the comp to which they belong
    */ 
  def ldot(beh: TA, i: Int, source: Location, system: TAS, im: Set[Set[String]]) = getTrans(beh).filter(t => getSource(t) == source).map{t => companionTrans(i, t, system, im)}.flatten

  def dotl(beh: TA, i: Int, sink: Location, system: TAS, im: Set[Set[String]]) = getTrans(beh).filter(t => getSink(t) == sink).map{t => companionTrans(i, t, system, im)}.flatten 

  def genDisj(tl: List[Transition]) = if (tl.length == 0) "" 
				      else if(tl.length == 1) getSink(tl(0)) 
				      else "Or(" + tl.tail.foldLeft(getSink(tl(0)))((r,c) => r + ", " + getSink(c)) + ")"

  def genImplicOld(i: Int, l: Location, system: TAS, im: Set[Set[String]]) = {
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
  def fwdInteractionSet0(i: Int, l: Location, system: TAS, im: Set[Set[String]]) = {
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
  def fwdInteractionSet(i: Int, l: Location, system: TAS, im: Set[Set[String]]) = {
    val transi = getTrans(system(i)).filter{t => getSource(t) == l}
    //println("transi = " + transi)
    val participatingActs = transi.map{t => getAct(t)}.toSet
    val participatingInteractions = im.filter{alpha => (alpha & participatingActs).size == 1}
    //println("pit = " + participatingInteractions)
    val indices = List.range(0, system.length)
    val alphs = indices.map{i => getAlph(system(i))}
    var res = List[List[Transition]]()
    participatingInteractions foreach {
      alpha => 
	//println("alpha = " + alpha)
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

  def genImplic(i: Int, l: Location, system: TAS, im: Set[Set[String]]) = {
    val beh = system(i)
    val fwdIL = fwdInteractionSet(i, l, system, im)
    if (fwdIL != List()) {
      val right_hand_side = if (fwdIL.length == 1) genDisj(fwdIL(0)) else "And(" + fwdIL.tail.foldLeft(genDisj(fwdIL.head))((r,c) => r  + "," + genDisj(c)) + ")"
      "Implies(" + l + ", " + right_hand_side + ")"
    }
    else ""    
  }

  def genII(system: TAS, im: Set[Set[String]]) = {
    val indices = List.range(0, system.length)
    val allLocs = indices.flatMap{i => getLocs(system(i)).map{l => (i, l)}}
    println("locs = " + allLocs)
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
	val g = zone2String(getGuard(t),clksM)
	val gv = mkGVProp(getGuardV(t))
	val reset = reset2StrM(getReset(t))(clksM)
        val upd = upd2Str(getUpd(t))
	(l1 + "-> " + l2 + " [label=\"" + invl1 + ", " + getAct(t) + "," + g + "," + reset + ","+ gv + ", " + upd + "\"]; \n")
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

  def addIntActs(alphG: Set[Act], im: InteractionModel) = im ++ (alphG -- im.flatten).map{Set(_)}

  //well formed tas
  def wfTA(ta: TA) = {
    val trans = getTrans(ta)
    val ls = trans.flatMap{t => Set(getSource(t), getSink(t))} 
    require(ls == getLocs(ta), println("The set of sources and sinks " + ls + " is diff. from the set of locs."))
  }

  def sanityChecks(tal: List[TA], im: InteractionModel) = {
    val alphG = tal.flatMap{ta => getAlph(ta)}.toSet
    val actsIM = im.flatten
    require(alphG subsetOf actsIM, println("The global alph " + alphG.toList.sorted + " is diff. from the acts in IM " + actsIM.toList.sorted + "\ngalph - im = " + (alphG -- actsIM) + "\nim - galph = " + (actsIM -- alphG) ))
    val clksG = tal.flatMap{ta => getClkMap(ta).map{_._2}}.toSet
    val hclks = alphG.map{mkHClk(_)}
    val singletons = im.filter(_.size==1).flatten.map{mkHClk(_)}
    val diffClks = hclks -- clksG
    require(diffClks == singletons, println("There are acts without corr. hclk:\nhclks = " + hclks.toList.sorted + "\nclksG = " + clksG.toList.sorted + "\ndiff = " + diffClks + "\nsingletons = " + singletons)) 
    tal.foreach{wfTA(_)}
  }


  def writeTAXML(taXML: Elem, newTAFile: String) = { 
//  def writeTAXML(taXML: String, newTAFile: String) = { 
    val path = Path (newTAFile)
    path.createFile(failIfExists=false)
    val file: FileOps = Path (newTAFile)		   
    // By default the file write will replace
    // an existing file with the new data
    file.write (taXML.toString)
    //content
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

  def mkUppaalExpr(s: String) = s.replace(">=", "&gt;=").replace("<=", "&lt;=").replace("<", "&lt;").replace(">", "&gt;").replace(",", " and ")

  /** make all acts broadcasts */
  def genUppaalTA(ta: TA) = {
    val taName = getName(ta)
    val locsI = getLocs(ta).toList.zipWithIndex.toMap
    val clksM = getClkMap(ta)
    val clks = if (clksM.isEmpty) "" else clksM.map{_._2}.reduceLeft(_+", "+_)
    val trans = getTrans(ta)
    val invsM = getInvMap(ta) 
    val invs = invsM.map{el => (el._1 -> zone2String(el._2, clksM))}.toMap
    val vars = getVars(ta)
    val iniL = getIni(ta)
    val idIni = "id" + locsI(iniL)
    val acts = getAlph(ta).reduceLeft(_+", "+_)

    val locsL = locsI.map{
      li => 
	//val inv = mkUppaalExpr(invs(li._1))
	val inv =  mkUppaalExpr(mkUppaalPropFromPoly(invsM(li._1), clksM)(""))
	"<location id=\"id"+ li._2 + "\"><name>" + li._1 + "</name>" + 
	(if (inv != "true") ("<label kind=\"invariant\">" + inv + "</label>") else "") + 
	"</location>\n" 
    }.reduceLeft(_+"\n"+_)
    val  transList = trans.map{
      t => 
	val source = getSource(t)
	val sink = getSink(t)
	val g0 = getGuard(t)
	val g = mkUppaalExpr(mkUppaalPropFromPoly(g0, clksM)(""))
	//println("g = " + g)
	//val g1 = zone2String(g0, clksM)
	//val g = if (g1 == "true") "" else g1
	val gvS = getGuardV(t)
	val gv = if (gvS.isEmpty) "" else gvS.map{el => (el._1 + el._2 + el._3)}.reduceLeft(_+" and "+_)
	//val gt = if (g =="") mkUppaalExpr(gv) else if (gv =="") mkUppaalExpr(g) else mkUppaalExpr(g + " and " + gv)
	val gt = if (g =="") mkUppaalExpr(gv) else if (gv =="") g else g + " and " + mkUppaalExpr(gv)
	val r = getReset(t)
	val upd = getUpd(t)
	val at = if (r.isEmpty) "" 
		 else r.map{el => clksM(el._1) + " = " + el._2}.reduceLeft(_ + ", " +_) + 
		 (if (upd.isEmpty) "" else  ", " + upd.map{el =>  el._1 + (if (el._3) " = " else " += ") + el._2}.reduceLeft(_ + ", " + _))
	val a = getAct(t) + "!"
	"<transition>\n <source ref=\"id" + locsI(source) + "\"/>\n<target ref=\"id" + locsI(sink) + "\"/>\n" + 
	"<label kind=\"synchronisation\">" + a + "</label> \n" + 
	(if (at != "") "<label kind=\"assignment\">" + at + "</label> \n" else "") + 
	(if (gt != "") "<label kind=\"guard\">" + gt + "</label> \n" else "") + 
	"</transition> \n"  
    }.reduceLeft(_+"\n"+_)

    val broadcastDecl = "\nbroadcast chan " + acts + " ;\n"
 
    val varDecl = if (vars.isEmpty) "\n" else vars.map{vv => "int " + vv._1 + " = " + vv._2 + ";\n"}.reduceLeft(_+_) 			  

    val globalDeclTxt = broadcastDecl + varDecl

    val globalDecl = "<declaration>\n" + globalDeclTxt + "\n</declaration>"    
    val template = "<template>\n <name>" + taName + "</name>\n <declaration>\n clock " + clks + ";\n" + 
		    "</declaration>\n" + locsL + "\n <init ref=\"" + idIni + "\"/>\n" + transList + "\n</template>"  
    val syst = "<system>\n system " + taName + ";\n</system>"
    val nta = "<nta>\n" + globalDecl + "\n" + template + syst + "\n </nta>"
    val xml = XML fromString nta
    //val xml = header + nta
    //println("wd = " + wd)
    writeTAXML(xml, wd + "gen" + taName + ".xml")
  }

  /** make all acts broadcasts */
  def genUppaalTA2(ta: TA) = {
    val taName = getName(ta)
    val locsI = getLocs(ta).toList.zipWithIndex.toMap
    val clksM = getClkMap(ta)
    val clks = clksM.map{_._2}.reduceLeft(_+", "+_)
    val trans = getTrans(ta)
    val invsM = getInvMap(ta) 
    val invs = invsM.map{el => (el._1 -> zone2String(el._2, clksM))}.toMap
    val vars = getVars(ta)
    val iniL = getIni(ta)
    val idIni = "id" + locsI(iniL)
    val acts = getAlph(ta).reduceLeft(_+", "+_)

    val locsL = locsI.map{
      li => 
	//val inv = mkUppaalExpr(invs(li._1))
	val inv =  mkUppaalExpr(mkUppaalPropFromPoly(invsM(li._1), clksM)(""))
	"<location id=\"id"+ li._2 + "\"><name>" + li._1 + "</name>" + 
	(if (inv != "true") ("<label kind=\"invariant\">" + inv + "</label>") else "") + 
	"</location>" 
    }.reduceLeft(_+_)
    val  transList = trans.map{
      t => 
	val source = getSource(t)
	val sink = getSink(t)
	val g0 = getGuard(t)
	val g = mkUppaalExpr(mkUppaalPropFromPoly(g0, clksM)(""))
	//println("g = " + g)
	//val g1 = zone2String(g0, clksM)
	//val g = if (g1 == "true") "" else g1
	val gvS = getGuardV(t)
	val gv = if (gvS.isEmpty) "" else gvS.map{el => (el._1 + el._2 + el._3)}.reduceLeft(_+" and "+_)
	//val gt = if (g =="") mkUppaalExpr(gv) else if (gv =="") mkUppaalExpr(g) else mkUppaalExpr(g + " and " + gv)
	val gt = if (g =="") mkUppaalExpr(gv) else if (gv =="") g else g + " and " + mkUppaalExpr(gv)
	val r = getReset(t)
	val upd = getUpd(t)
	val at = if (r.isEmpty) "" 
		 else r.map{el => clksM(el._1) + " = " + el._2}.reduceLeft(_ + ", " +_) + 
		 (if (upd.isEmpty) "" else  ", " + upd.map{el =>  el._1 + (if (el._3) " = " else " += ") + el._2}.reduceLeft(_ + ", " + _))
	val a = getAct(t) + "!"
	"<transition><source ref=\"id" + locsI(source) + "\"/><target ref=\"id" + locsI(sink) + "\"/>" + 
	"<label kind=\"synchronisation\">" + a + "</label>" + 
	(if (at != "") "<label kind=\"assignment\">" + at + "</label>" else "") + 
	(if (gt != "") "<label kind=\"guard\">" + gt + "</label>" else "") + 
	"</transition>"  
    }.reduceLeft(_+_)

    val broadcastDecl = "broadcast chan " + acts + " ;"
 
    val varDecl = if (vars.isEmpty) "" else vars.map{vv => "int " + vv._1 + " = " + vv._2 + ";"}.reduceLeft(_+_) 			  

    val globalDeclTxt = broadcastDecl + varDecl

    val globalDecl = "<declaration>" + globalDeclTxt + "</declaration>"    
    val template = "<template><name>" + taName + "</name><declaration>clock " + clks + ";" + "</declaration>" + locsL + "<init ref=\"" + idIni + "\"/>" + transList + "</template>"  
    val syst = "<system>system " + taName + ";</system>"
    val nta = "<nta>" + globalDecl + template + syst + "</nta>"
    val xml = XML fromString nta
    //val xml = header + nta
    //println("wd = " + wd)
    writeTAXML(xml, wd + "gen" + taName + ".xml")
  }


  /* helper getter methods for parsing uppaal xml */

  def elem(name: String, children: Node*) = Elem(None, name, Attributes(), scala.collection.immutable.Map[String, String](), Group(children: _*))

  def anyElem = Selector[Elem]({case x:Elem => x})

  /** @return All the templates from the xml file (check if the root must be a node <nta>). 
   *
   */ 
  def getTemplates(ta: Elem) = ta \ 'template 

  def getTemplate(ta: Elem, name: String) = { 
    val templs = ta \ 'template 
    val res = templs filter (t => getTemplateName(t)==name)
    //debug("getTemplate: template names in ta = " + (templs.map(t => getTemplateName(t))).toList, 2)
    require (res.length > 0, println("Err: no template called " + name + " in " + ta + "."))
    // i assume names in xml are unique 
    res(0)  
  }

  def getTemplateNames(ta: Elem) = (ta \ 'template \ 'name \text) map (_.mkString) 

  def getTemplateName(templ: Elem) = (templ \ 'name \text).mkString  

  /** @return All the transitions from a template.
   *
   */ 
  def getTransitions(templ: Elem) = (templ \ 'transition)

    def getSourceId(transition: Elem) = { 
      val source = (transition \ 'source)
	if (source.size > 0) source.head.attrs("ref") 
	else { 
	  println("Err: trans " + transition + " has no source. Return empty."); ""
	}
    }

  def getSinkId(transition: Elem) = { 
    val target = (transition \ 'target)
      if (target.size > 0) target.head.attrs("ref") 
      else { 
	println("Err: trans " + transition + " has no target. Return empty."); ""
      }
  }
  
  /** Each trans has at most 1 sync (so it's ok to take the head);
   * if it's an internal action its name is the empty string. 
   */
  def getUppaalAct(transition: Elem) = { 
    val res = ((transition \ 'label).filter(l => (l.attrs("kind") == "synchronisation")) \text)
      if (res.size>0) res.head.mkString else "" 
  }

  /** Each trans has at most 1 guard which can be a conjunction. 
   * @return The corresponding list (list, because we want to go through it).
   */ 
  def getUppaalGuard(transition: Elem) = { 
    val guards = ((transition \ 'label).filter(l => (l.attrs("kind") == "guard")) \text) 
      val res = if (guards.size>0) guards.head.split("and").map(_.trim.filter(_!=' ')).toList else List() 
    //println("getguard: res = " + res)
    res
  } 

  def getUppaalReset(transition: Elem) = {
    /* an assignment is a string like "", or "x = 0", or "x = 0, y = 1" for example
     */
    val resets = ((transition \ 'label).filter(l => (l.attrs("kind") == "assignment")) \text)
    if (!resets.isEmpty) resets.head.replace(scala.sys.props("line.separator"), "").filter(_!=' ').split(",").map{_.trim}.toList else List()
  }

  def getUppaalLocs(templ: Elem) = (templ \ 'location)

    /** There is only one invariant associated with a location
     * (i.e., one elem in the xml)
     * so it's ok to use head
     */
  def getUppaalInv(loc: Elem) = { 
      val res = ((loc \'label).filter(l => (l.attrs("kind") == "invariant")) \text)
	if (res.length>0) res.head.mkString else ""
    }

  def getLocId(loc: Elem) = loc.attrs("id")

  def getLocName(loc: Elem) = (loc \'name \text).mkString

  def getInitRef(templ: Elem) = {
    (templ \ 'init).head.asInstanceOf[Elem].attrs("ref")
  }

  def getSystem(ta: Elem) = ta \ 'system

  /** @return the name of the unique TA in the NTA;
   * the syntax is: <system>system A;</system> so we need to drop the first 7 chars and the last ; to obtain the names A
   */    
  def getSystemName(ta: Elem) : String = {      
    val systTxt = (ta \ 'system \text).mkString.trim
    //eliminate comments
    val commentPos = systTxt.lastIndexOf("system ")
    val name = systTxt.drop(7+commentPos).dropRight(1).trim 
    //println("getSystemName name = " + name)
    name
  }

  /** @clk decl from the local declarations inside a template*/
  def getUppaalClks(templ: Elem): List[String] = {
    val decls = (templ \'declaration \text).mkString.trim.split(Array(';', '\n'))
    val clkDecl = decls.filter(x => x.startsWith("clock")) 
    val clocks = clkDecl.map{el => el.drop("clock ".length).split(",")}.flatten.map(_.trim).distinct.toList
    clocks
  }

  def getGlobalDeclText(ta: Elem) = (ta \ 'declaration \text).mkString

  def getUppaalVars(ta: Elem) = {
    val gdecl = getGlobalDeclText(ta: Elem)
    //val lines = gdecl.split(";").map{_.trim}.filter{l => (l!="" && l!="\n" && (l.startsWith("int") || l.startsWith("bool")))}.toList
    val lines = gdecl.split(";").map{_.trim}.filter{l => l.startsWith("int")}.toList
    //println("lines = " + lines)
    val res = lines.flatMap{
      l =>
//	if (l.startsWith("int")) {
	  //decl like: int x, y = 2 or int x, y
	  val res = l.split("=").toList
	  val v = if (res.length == 1) 0 else res(1).trim.toInt
	  val vars = res(0).drop(3).trim.split(",").map{_.trim}
	  vars.map{vv => (vv -> v)}
//	}
/*
      else { //starts with bool 
	  //decl like: int x, y = 2 or int x, y
	  val res = l.split("=").toList
	  val v = if (res.length == 1) false else res(1)
	  val vars = res(0).drop(4).trim.split(",").map{_.trim}
	  vars.map{vv => (vv -> v)}
      }
*/
      }.toMap
    //println("res = " + res)
    res
  }

//  val ctReg = new Regex("""\s*[]""", "operand1", "op", "operand2")

  def mkOp(op: String) = op match {
    case ">=" => Relation_Symbol.GREATER_OR_EQUAL 
    case  "==" => Relation_Symbol.EQUAL
    case "<=" => Relation_Symbol.LESS_OR_EQUAL 
    case "<" => Relation_Symbol.LESS_THAN 
    case ">" => Relation_Symbol.GREATER_THAN 
  }

  def mkConstraint(ct0: String, clks: ClkMap, vars: Set[String]): Either[Constraint, GuardVElem] = {
    val ct1 = ct0.trim.filter(_!=' ')
    //clkname -> var
    val reversedclks = clks.map{_.swap}
    //println("ct1 = *" + ct1 + "*")
    val ops = List("<=", ">=", "<", ">", "==")
    val op = ops.dropWhile{o => !ct1.contains(o)}.head
    //after the split it should have 2 elems, a clk and a value
    val res = ct1.split(op)      
    val op1 = res(0)
    val op2 = res(1)
    if (vars(op1) || vars(op2)) {
      val resgV = if (vars(op1)) (op1, op, op2.toInt) else (op2, op, op1.toInt)
      Right(resgV)
    }
    else {
      val (clk, v) = if (reversedclks.keySet(op1) || vars(op1)) (op1, op2) else (op2, op1) 
      //println("clk = " + clk + " val = " + v)
      val le_clk = new Linear_Expression_Variable(reversedclks(clk))      
      if (reversedclks.keys.toSet contains v) {
	val le_val = new Linear_Expression_Variable(reversedclks(v))      
	val resct = new Constraint(le_clk, mkOp(op), le_val)
	//println("resct = " + resct)      
	Left(resct)
      }
      else {
	val le_val = new Linear_Expression_Coefficient(new Coefficient(v))
	val resct = new Constraint(le_clk, mkOp(op), le_val)
	Left(resct)
      }
      //println("resct = " + resct)      
    }
  }

  def mkZoneInv(invs0: String, dim: Int, clks: ClkMap, vars: Set[String]) = {
    val invs = invs0.trim.filter(_!=' ').split(" and ").toList.filter(_!="")
    if (invs.isEmpty) new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    else {
      //println("invs = " + invs + " dim = " + dim)
      val invP = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
      invs foreach {
	i => 
	  //println("invar = *" + i + "*")
	  val ct = mkConstraint(i, clks, vars) 
	//println("ct = " + ct)
	ct match {
	  case Left(x) => invP.add_constraint(x)      
	}
      }
      invP
    }
  }

  def mkZoneGuards(gl: List[String], dim: Int, clks: ClkMap, vars: Set[String]) = {
    val g = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    //println("g = " + g)
    var gv = Set[GuardVElem]()
    if (!gl.isEmpty) 
      gl foreach {
	gs0 =>
	  val gsf = gs0.trim.replace("\n", "").filter(_!=' ')
	  if (!gsf.isEmpty) {
	    mkConstraint(gsf, clks, vars) match {
	      case Left(x) => g.add_constraint(x)
	      case Right(x) => gv += x
	    }
	  }
      }
    (g, gv)    
  }

  def mkReset(rL: List[String], clks: ClkMap, vars: Set[String]) = {
    var r = Set[(Variable, Int)]()
    var updv = Set[(String, Int, Boolean)]()
    if (!rL.isEmpty) {
    val reversedClkM = clks.map{_.swap}      
      rL foreach {
	rs0 => 
	  val rsf = rs0.trim.replace("\n", "").filter(_!=' ')
	  if (!rsf.isEmpty) {
	    if (rsf.contains("+=")) {
	      //an assignment like z += v; it's a var
	      val res = rsf.split("\\+=").map{_.trim}
	      updv += ((res(0), res(1).toInt, false))
	    }
	    else {
	      val res = rsf.split("=").map{_.trim}
	      val varn = res(0)
	      val v = res(1).toInt
	      if (vars(varn)) updv += ((varn, v, true))
	      else r += ((reversedClkM(varn), v))
	    }
	  }
      }
    }
    (r, updv)
  }

  /** i assume taFile contains only one TA; it's name is in the system def.*/
  def loadTA(taFile: String) : TA = {
    val in:Input = Resource.fromFile(taFile)
    val stringFromIn = in.slurpString(Codec.UTF8)
    require (stringFromIn != "", println("Empty xml file. Perhaps the path " + taFile + " is wrong?"))
    val taXML = XML fromString stringFromIn 
    val name = getSystemName(taXML)
    val varsM = getUppaalVars(taXML)
    val vars = varsM.keySet
    //println("name = " + name)
    val templ = getTemplates(taXML).filter(templ => getTemplateName(templ) == name).head
    val locs = getUppaalLocs(templ)
    val locsn = locs.map{l => getLocName(l)}
    //println("locsn = " + locsn)
    val iniRef = getInitRef(templ)
    val ini = getLocName(locs.filter(l => getLocId(l) == iniRef).head)
    //println("ini = " + ini)
    val clks = getUppaalClks(templ)
    //println("clks = " + clks)
    val dim = clks.length
    val clkindices = List.range(0, dim)
    val clksM = clkindices.map{i => (new Variable(i), clks(i))}.toMap
    val invsM = locs.map{l => (getLocName(l) -> mkZoneInv(getUppaalInv(l), dim, clksM, vars))}.toMap
    val trans = getTransitions(templ)   
    val transS = trans.map{
      t => 
	//dropping !/? from uppaal
	val act = getUppaalAct(t).dropRight(1)
	val sourceId = getSourceId(t)
	val sourceN = getLocName(locs.filter(l => getLocId(l) == sourceId).head)
	val sinkId = getSinkId(t)
	val sinkN = getLocName(locs.filter(l => getLocId(l) == sinkId).head)
	val gL = getUppaalGuard(t)
	val rL = getUppaalReset(t)      
	//println("for t = " + t + " source = " + sourceN + " sink = " + sinkN + " g = " + gL + " r = " + rL + " act = " + act)
	val (glz, glv) = mkZoneGuards(gL, dim, clksM, vars)
	val (rl, updl) = mkReset(rL, clksM, vars)
	//mkTrans(source: Location, p: Act, g : Guard, gv : GuardV = Set(), r: Reset, upd : UpdV = Set(), sink : Location)
	//println("rl = " + rl + " upd = " + updl)
        mkTrans(source = sourceN, p = act, g = glz, gv = glv, r = rl, upd = updl, sink = sinkN)
    }.toSet
    //("new" + name, ini, locsn.toSet, transS, clksM, invsM, varsM)
    (name, ini, locsn.toSet, transS, clksM, invsM, varsM)
  }

  def loadTATest(taFile: String) = {
    val in:Input = Resource.fromFile(taFile)
    val stringFromIn = in.slurpString(Codec.UTF8)
    require (stringFromIn != "", println("Empty xml file. Perhaps the path " + taFile + " is wrong?"))
    val taXML = XML fromString stringFromIn 

    def transform(ta: Elem) : Elem = ta match {
      case Elem(x, y, attrs, z, children) => {
	Elem(x, y, attrs - "x" - "y", z, children.map{c => if (c.isInstanceOf[Elem]) transform(c.asInstanceOf[Elem]) else c})
      }
      case _ => Elem(None, "dummy", Attributes(), Map(), Group())
    }
    val nta = transform(taXML)
    //println("nta = " + nta)
    nta
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

  def getVarValImi(vv: Int) = if (vv != -1) " = " + vv else ""
  
  def mkPTAName(name: String) = "\nautomaton " + name + "\n"

  def andImi(l: List[String]) = l.reduce((r,c) => r + " & " + c) 

  def mkSyncImi(acts: String) = "\nsynclabs: " + acts + ";\n"

  def mkVarDeclImi(decl: String) = "var\n\t" + decl + "\n" 

  def mkTransImi(source: String, inv0: String, a: String, g0: String, r: String, sink: String) = {
    val inv = if (inv0.trim.equals("true")) "True" else inv0
    val g = if (g0.trim.equals("true") || g0.trim.equals("")) "True" else g0
    "\nloc " + source + ": while " + inv + " wait {}\n" +
	"\t\t when " + g + " sync " + a + " do {" + r + "} goto " + sink + ";\n"
  }

  def mkResetImi(r: Reset, clksM: ClkMap) =  if (r.isEmpty) "" else r.map{el => clksM(el._1) + "' = " + el._2}.reduceLeft(_ + ", " +_)

  def getImiIni(l: String, taName: String) = "loc[" + taName + "] = " + l

  def getImiIniClks(clks: List[String]) = clks.foldLeft("")((r,c) => r + " & " + c + " = 0")

  def mkImi(ta: PTA, path: String = "") = {
    val taName = getName(ta)
    val locsI = getLocs(ta).toList.zipWithIndex.toMap
    val clksM = getClkMap(ta)
    val trans = getTrans(ta)
    val invsM = getInvMap(ta) 
    val invs = invsM.map{el => (el._1 -> zone2String(el._2, clksM))}.toMap
    val vars = getVars(ta)
    val params = getParams(ta)
    val iniL = getIni(ta)
    val idIni = "id" + locsI(iniL)
    val acts = getAlph(ta).reduceLeft(_+", "+_)

    val  transList = trans.map{
      t => 
	val source = getSource(t)
	val sink = getSink(t)
	val g0 = getGuard(t)
	val g = mkUppaalExpr(mkUppaalPropFromPoly(g0, clksM)(""))
	//println("g = " + g)
	//val g1 = zone2String(g0, clksM)
	//val g = if (g1 == "true") "" else g1
	val gvS = getGuardV(t)
	val gv = if (gvS.isEmpty) "" else gvS.map{el => (el._1 + el._2 + el._3)}.reduceLeft(_+" and "+_)
	val gt = if (g =="") mkUppaalExpr(gv) else if (gv =="") g else g + " and " + mkUppaalExpr(gv)
	val r = getReset(t)
	val a = getAct(t) 
	mkTransImi(source, invs(source), a, gt.replace("&gt;=", " <= "), mkResetImi(r, clksM), sink)
    }.reduceLeft(_+_)
 
    val varDecl = if (vars.isEmpty) "" else vars.map{vv => vv._1 + getVarValImi(vv._2) + ","}.reduceLeft(_+_) + ": parameter;\n"
    val paramDecl = if (params.isEmpty) "" else params.reduceLeft(_+ ", " + _) + ": parameter;\n"
    val clks = (clksM.map{_._2}.toSet diff params).reduceLeft(_+", "+_)
    val clkDecl = "\t" + clks + ": clock;\n"
    val decl = paramDecl + varDecl + clkDecl
    val pta = mkVarDeclImi(decl) + 
	      mkPTAName(taName) + 
		mkSyncImi(acts) + 
		transList + 
	      "\nend\n\n" +
	      "\nvar init: region;\n" + 
	      "\ninit:= " + getImiIni(iniL, taName) + "\n" +
			    "\t\t" + getImiIniClks(clksM.map{_._2}.toList) + "\n;"
    write2File(path + taName + ".imi", pta)
  }

  def mkIM(imFile: String) : InteractionModel = {
    val file = Path(imFile)
    val lines = file.lines()
    var im : InteractionModel = Set[Set[Act]]()
    lines foreach {
      l =>
	val lt = l.trim
	if (lt != "\n" && lt != "") {
	  val interaction = l.split(" , ").map{_.trim}.toSet
	  im += interaction
	}
    }
    im
  }

  /** load a PTA from an imi file; i assume 1 PTA per file*/
  def loadImi(imiFile: String) : PTA = {
     val file = Path(imiFile)
     val lines = file.lines()
     var name = ""
     var locs = Set[Location]()
     var l0 = ""
     var trans = Set[Transition]()
     var params = Set[String]()//Map[Param, String]()   
     var vars = emptyVV
     var invS = Set[(Location, Invariant)]()
     var clksM = Map[Clock, String]()  
     var dim = 0
     var dimp = 0
     var sourceN = ""
     lines foreach {
       l =>
	 val lt = l.trim()
	 if (lt.startsWith("automaton "))	 
	   name = l.split("automaton")(1).trim
	 //line is of form: loc <loc_name>:
	 if (lt.startsWith("loc ")) {
	   val r1 = lt.drop(4).split(":")
	   sourceN = r1(0).trim
	   //println("source = " + sourceN)
	   val rest = r1(1)
	   locs += sourceN
	   var inv = lt.split("while")(1).split("wait")(0).trim()
	   val dimt = dim + dimp
	   //println("inv = " + inv + " dimt = " + dimt)
	   if (inv.equals("True")) 
	     inv = ""	   
	   invS += ((sourceN, mkZoneInv(inv, dimt, clksM, Set[String]())))
	 }
	 if (lt.startsWith("when")) {
	   val r2 = lt.split("goto")
	   val rest1 = r2(0)
	   //println("rest1 = " + rest1)
	   val rest2 = r2(1)
	   //println("rest2 = " + rest2)
	   val sinkN = rest2.replace(";","").trim()
	   //println("sinkN = " + sinkN)
	   val r3 = rest1.replace("{", "").replace("}","").split("do")	   
	   val rest3 = r3(0)
	   //println("rest3 = " + rest3)
	   val rest4 = r3(1)
	   //println("rest4 = " + rest4)
	   val reset = mkReset(rest4.replace("'","").split(",").toList, clksM, Set[String]())._1
	   val r4 = rest3.split("sync")
	   val rest5 = r4(0) 
	   //println("rest5 = " + rest5)
	   val act = r4(1)
	   //println("a = " + act)
	   val a = act.trim()
	   val r5 = rest5.split("when")
	   val gt = r5(1)
	   //println("g = " + gt)
	   var gs = gt.split("and").map(_.trim()).toList
	   //println("gs = " + gs)
	   if (!gs.isEmpty && gs(0).equals("True"))
	     gs = List()
	   val glz = mkZoneGuards(gs.toList, dim+dimp, clksM, Set[String]())._1
	   trans += mkTrans(source = sourceN, p = a, g = glz, r = reset, sink = sinkN)
	 }
	 else if (lt.contains(":")) {
	   if (lt.contains("parameter")) {
	     val paramsl = lt.split("parameter")(0).split(":")(0).split(",").map{_.trim}
	     params = paramsl.toSet
	     dimp = params.size
	     clksM = clksM ++ (0 to dimp-1).map{i => (new Variable(i), paramsl(i).trim)}.toMap
	     //println(clksM)
	   }
	   if (lt.contains("clock")) {
	     val clks = lt.split("clock")(0).split(":")(0).split(",")
	     //println(clks.toList)
	     dim = clks.length
	     clksM = clksM ++ (0 to dim-1).map{i => (new Variable(i + dimp), clks(i).trim)}.toMap
	     //println(clksM)
	   }
	   if (lt.contains("loc[")) {
	     l0 = lt.split("]")(1).split("=")(1).split("&")(0).trim()
	   }	     	     
	 }
     }
    (name, l0, locs, trans, clksM, invS.toMap, vars, params)
  }

  def getTA(ta: PTA) = {
    val taName = getName(ta)
    val locs = getLocs(ta)
    val clksM = getClkMap(ta)
    val trans = getTrans(ta)
    val invsM = getInvMap(ta) 
    val vars = getVars(ta)
    val iniL = getIni(ta)
    (taName, iniL, locs, trans, clksM, invsM, vars)
   }

  def getPTA(ta: TA, params: Params = Set[String]()) = {
    val taName = getName(ta)
    val locs = getLocs(ta)
    val clksM = getClkMap(ta)
    val trans = getTrans(ta)
    val invsM = getInvMap(ta) 
    val vars = getVars(ta)
    val iniL = getIni(ta)
    (taName, iniL, locs, trans, clksM, invsM, vars, params)    
   }

  def actsFromLoc(ta: TA, l: Location) = getTrans(ta).filter{t => getSource(t) == l}.map{t => getAct(t)}

  //return a set of pairs (gl, alpha), with gl a global loc and alpha an interaction from gl
  def getAbstractReachIA(system: TAS, im: InteractionModel) = {
    val n = system.length
    val indices = List.range(0, n)
    val l0 = system.map{ta => getIni(ta)}
    var visited = Set(l0)
    var abstractReach = Set[(List[Location], Interaction)]()
    val tovisit = new Stack[List[Location]]
    tovisit.push(l0)
    while(tovisit.length > 0) {
      val l = tovisit.pop
      val possibleActs = (indices flatMap (i => actsFromLoc(system(i), l(i)))).toSet
      im foreach {
	alpha => 
	  if (alpha subsetOf possibleActs) {
	    val nl : List[Location] = indices map {
	      i => 
		val li = getAlph(system(i)) & alpha
		if (li == Set()) l(i)
		else {
		  val ti = getTrans(system(i)).filter{t => (getSource(t) == l(i) && (alpha contains getAct(t)))}
		  //assume det; not true in general; \todo[correct]
		  if (ti != Set()) getSink(ti.toList(0))
		  else {
		    println("[getAbstractReach]: unexpected behaviour")
		    l(i)
		  }
		}
	    }
	    //val nt = mkGT()	    
	    if (!(visited(nl))) tovisit.push(nl)
	    abstractReach += ((l, alpha))
	  }
      }
      visited += l
    }
    //val absReachEF = abstractReach.foldLeft("")((r,c) => r + " || " + 
    //(abstractReach, en)
    abstractReach
  }

  def mkEFStateProp(l: List[String]) = l.reduce((r,c) => r + " && " + c)

  def genAbsReach_En(system: TAS, im: InteractionModel) = {
    val absReachWithIA = getAbstractReachIA(system, im)
    var absr = ""
    var en = ""
    absReachWithIA foreach {
      glIA =>
	val gl = glIA._1
	val alpha = glIA._2
	absr += " || " + mkEFStateProp(gl)
	//debug("genAbsReach_En: absr = " + absr + " alpha = " + alpha)
	en += " || " + genDISIAG(alpha.toList, system, gl.zipWithIndex, false) 	
	//debug("genAbsReach_En: en = " + en)
    }
    "\n\n%abstract reach\n Assumption(" + absr.drop(4) + ") \n\n" + 
    "Guarantee(" + en.drop(4) + ")\n\n"
  }    

}

