# CoVerTS
a prototype for the verification of state properties for timed systems

Requirements:
- Z3 (z3.codeplex.com) 
- optional, if you want to experiment with the source code yourself:
 * sbt (http://www.scala-sbt.org/) 
 * PPL (bugseng.com/products/ppl/‎), the platform dependent libppl_java.so, ppl_java.jar must be copied inside the "lib" folder)


=================================
How to test the existing apps:  
=================================

from the cmd line:

x$ java <app-name>.jar <args>

where <app-name> \in {tgc, fischer, tc} and <args> is the list of arguments:
1. for TGC: <n>, with <n> being the number of trains 
2. for Fischer: <n>, with <n> being the number of processes ...
3. for TC: <n> <isLinInv> <beta>, with <n> being the number of rodes, <isLinInv> is either 0 or 1 (1 is for using linear interaction invariants), <beta> is the constant in the rode component (this param is optional, by default it is n*900)

========================
How to impl new apps:  
========================

1. Implementation:
 - look at the files tgc.scala, tempcontrol.scala; your new app. should look similar:
  * implement your TAs (see makeTrain, you need to be familiar with PPL) or input it from an Uppaal file (see, for example src/Robots.scala)
  * define your IM (see genIM)
  * define your safety property to pass as the 3rd param to genTCZ3. Obs. that, by default, the 3rd param of genTCZ3 is implicitly DIS, automatically computed with genDIS.
- your main method should be identical to the main methods in the existing apps, with the only 2 exceptions of the def of the system and the call to genTCZ3 where you can ignore the last param.

(Obs.: the file graphZone.scala is generic, this shouldn't be modified.)
 
2. Compile & make a jar:
- make sure you're in the dir genGlobalInv
- make a jar with the main app, from the cmd line:
  .../genGlobalInv$ sbt one-jar
  you'll be prompted to give the nb of the main class. Choose the one corresponding to yours. The generated jar file has a default name genglobalinv-0.1-one-jar.jar and is to be found in the folder "target". 

3. Run: 
- from the cmd line:
  .../genGlobalInv$ java target/genglobalinv-0.1-one-jar.jar <args>
where <args> are the arguments of your main method, if any.
