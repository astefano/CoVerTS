package org

import parma_polyhedra_library._

//for parsing
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator._

import scala.util.matching.Regex

//options parser
import scopt._

object PTA2EF extends ZoneGraphVV {

  def getBit(x: Int, i: Int) = if ((x & (1 << i)) != 0) 1 else 0

  def encodeLocs(ta: TA) = {
    val locs = getLocs(ta).toList.sorted
    val name = getName(ta)
    val defaultlocname = "l" + name
    val n = locs.length

    if (n == 2) {
      (Map((locs(0) -> ("!"+defaultlocname)), (locs(1) -> defaultlocname)), 
       Set(defaultlocname))
    }
    else {
      var nlocs = Set[String](defaultlocname+"0", defaultlocname+"1")
      val map2 = Map[Location, Location]((locs(0), "!"+defaultlocname+"0 && !" +defaultlocname+"1"), 
					 (locs(1), defaultlocname+"0 && !" +defaultlocname+"1"))
      val maplocs = List.range(2, n).map{
	i =>
	  var is = i
	var pos = 0
	var encode = ""
	while (is > 0) {
	  val bit = is & (1 << 0)
	  val neg = if (bit != 0) "" else "!"
	  encode +=  neg + defaultlocname + pos + " && "
	  nlocs += defaultlocname + pos
	  is = is >> 1
	  pos += 1
	}
	((locs(i) -> encode.dropRight(4).trim))
      } ++ map2

      (maplocs.toMap, nlocs)
    }
  }

  def main(args: Array[String]) {

    //runConfig(configFile)
    var badArgs = false

    var ptaDir = ""

    var imFile = ""

    var withHC = false

    val parser = new OptionParser("parse info: ") {
       opt("ip", "imitatorPath", "imitatorPath is the absolute path to imitator", { 
	 v: String => IMITATORPATH = v
       })
      
       opt("ptaDir", "ptaDir", "<ptaDir>", "ptaDir is the relative path to the dir with models", { 
	 v: String => 
	     require(!v.contains("ptaDir"), { 
	       println("Missing value for ptaDir. ")
	       badArgs = true
	     }) 
	 ptaDir = v})

       opt("imFile", "interactionModelFile", "<imFile>", "the relative path to the file with the interaction model", { 
	 v: String => 
	     require(!v.contains("imFile"), { 
	       println("Missing value for imFile. ")
	       badArgs = true
	     }) 
	 imFile = v})

       opt("hc", "historyClocks", "<hc>", "reach with history clocks", {
	 v: String => withHC = true	 
       })
    }

    require (parser.parse(args) && !badArgs, println("error while parsing arguments for TA."))  

    var outEF = ""

    var tas : TAS = List[TA]()

    var tasName = ""

    Parma_Polyhedra_Library.initialize_library()   

    val modelPath = wd + "Imitator/" + ptaDir 
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	file => 
	  var pta = loadImi(file)
	  var ta = getTA(pta)
	  val params = getParams(pta)
	  var nfile = file
	  if (withHC) {
	    ta = getTAH(ta)
	    pta = getPTA(ta, params)
	    val modelPathH = modelPath + "H/"
	    mkImi(pta, modelPathH)
	    nfile = modelPathH + getName(pta) + ".imi"	    
	  }
	val out = runImitator(nfile) 
	outEF += "\n" + imiDecl2EFDecl(nfile) + "\n\n" + states2CIEF(out)
	tas = tas:+ta
	tasName += getName(ta) + "_"
      }
    }  

    val im = mkIM(wd + imFile)
    //println("im = " + im)

    if (withHC) {
      val eqs = getEqsSimpl(im.map{_.toList}.toList, false)    
      outEF += "\nAssumption(" + eqs + ")\n"
    }

    outEF += genAbsReach_En(tas, im)

    tas foreach {
      ta => 
	val (m, nlocs) = encodeLocs(ta)
	val locs = m.keys.toList
	//replace decl Forall(p._1) 
	val forallOlddecl = locs.map{l => "Forall("+l.trim+")"}
	val forallNewdecl = nlocs.map{l => "Forall("+l.trim+")\n"}.mkString
	outEF = outEF.replace(forallOlddecl(0), forallNewdecl)
	forallOlddecl foreach {
	  d => 
	  outEF = outEF.replace(d, "")
	}
	m foreach {
	  p => 
	    outEF = outEF.replace("Forall(" + p._1 + ")", "").replace(p._1, p._2)
	}
    }
    

    import java.util.Calendar
    import java.text.SimpleDateFormat

    val today = Calendar.getInstance.getTime
    val curTimeFormat = new SimpleDateFormat("D_M_Y")

    val date = curTimeFormat.format(today)

    val efFile = tasName + "-outEF-" + date
    write2File(efFile, outEF)

    runEF(wd + efFile)

    Parma_Polyhedra_Library.finalize_library()

  }
}


