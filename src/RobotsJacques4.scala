package org

import parma_polyhedra_library._

object GenGlobalInvRobots4 extends ZoneGraphVV {

  def genIM = {
    val collab = List("collaborate", "close", "collaborate_r", "move_to_desk", "nochild_b", "nochild_c")
    val clean = List("lock", "underbed", "reached_desk", "nochild_b", "no_child_pict", "start_cleaning")
    // autonomic actions involved in priorities
    val stopCleaning = List("stop_cleaning", "unlock")
    val navigate = List("navigate")
    // model the analysis of the camera
    val testIn = List("test_in", "tkpict_in")  
    val testOut = List("test_out", "tkpict_out")  
    // child enter/exit
    val openDoorEnter = List("enter", "open")  
    val openDoorExit = List("exit", "open")  
    //child activity  
    val putObj = List("putobj", "putobj_r")
    val takeObj = List("tkobj", "tkobj_r")
    val childGetOnBed = List("bed", "geton")  
    val childSeat = List("seat", "seat_c")
    val childGetUpBed = List("in_room", "getup_b")
    val childGetUpChair = List("in_room", "getup_c")
    //stop ranger
    val childOnChair = List("stop_assist", "seated")
    val childOnBed = List("stop_assist", "child_b")

    List(collab, 
	 clean, 
	 stopCleaning, 
	 navigate, 
	 testIn, testOut, 
	 openDoorEnter, openDoorExit, 
	 putObj, takeObj, childGetOnBed, childSeat, childGetUpBed, childGetUpChair, 
	 childOnBed, childOnChair)
  }

  def genSafe = "Implies(cleaningS, outS)"

  def main(args: Array[String]) {
    if (args.length > 0) 
      DEBUG_LEVEL = args(0).toInt

    //println("test")

    Parma_Polyhedra_Library.initialize_library()   

    val systPath = wd + "examples/genCompsJacquesOK"
//    val systPath = wd + "examples/genCompsJacquesTraces"
    try {
      val compsdir = new java.io.File(systPath)    
      val system = compsdir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".xml")).toList.map{loadTA(_)} 

      val imNoSingles = genIM
      //println("Im = " + im)
      val imsNoSingles = imNoSingles.map{_.toSet}.toSet
      //println("II=" + genII(system, ims))   

      val ims = addIntActs(getGlobalAlph(system), imsNoSingles)
      val im = ims.map{_.toList}.toList

      val systemH = system.map{el => getTAH(el)(ims)}
      //systemH.foreach{ta => toDot(ta)}

/*
      systemH foreach {
	c => 
	  println("Uppaal query for " + getName(c) + " = " + getUppaalInvQuery(c))
	  genUppaalTA(c)
	  //val nta = loadTA(wd + "gen" + getName(c) + ".xml")
	  //genUppaalTA(nta)
      }
*/
      //println("Ims = " + ims)

      //sanityChecks(systemH, ims)

      val notSafe = "Not(" + genSafe + ")"	

      println("ha")
      
      val txt = genTCZ3(systemH, im, Map(), notSafe, "defaultZ3.py")

      println("ha2")

      write2File("genPys/robots17-04.py", txt)
      write2File("/home/lastefan/tools/z3/build/robots17-04.py", txt)


    } 
    catch {
      case e => println("e = " + e + ". Inexistent path " + systPath)
    }



/*
    systemH foreach {
      c => 
	println("Uppaal query for " + getName(c) + " = " + getUppaalInvQuery(c))
	genUppaalTA(c)
    }
*/
  
    Parma_Polyhedra_Library.finalize_library()

  }
}
