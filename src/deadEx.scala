package org

import parma_polyhedra_library._

object GenGlobalDeadEx extends ZoneGraphVV {

  def main(args: Array[String]) {
    ISLOCINT = if (args(0).toInt == 1) true else false

    Parma_Polyhedra_Library.initialize_library()   

    val systPath = wd + "examples/deadEx"
    try {
      val compsdir = new java.io.File(systPath)    
      val system = compsdir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".xml")).toList.map{loadTA(_)} 

      val im = List(List("a1","a2"), List("b1","b2"))
      val ims = Set(Set("a1","a2"), Set("b1","b2"))

      val systemH = system.map{el => getTAH(el)(ims)}
      systemH.foreach{ta => toDot(ta)}

      systemH foreach {
	c => 
	  println("Uppaal query for " + getName(c) + " = " + getUppaalInvQuery(c))
	  genUppaalTA(c)
	  //val nta = loadTA(wd + "gen" + getName(c) + ".xml")
	  //genUppaalTA(nta)
      }
    
      val txt = genTCZ3(systemH, im, Map())
      write2File("genPys/deadEx.py", txt)
      write2File("/home/lastefan/tools/z3/build/deadEx.py", txt)

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

