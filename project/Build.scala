import com.github.retronym.SbtOneJar
import sbt._
import Keys._
import Scope.{GlobalScope, ThisScope}

object HelloBuild extends Build {

  val hwsettings: Seq[sbt.Project.Setting[_]] = Defaults.defaultSettings ++ Seq(
    organization := "hello",
    name         := "world",
    version      := "1.0-SNAPSHOT"
  )

//scalesxml 
//val scalesRepo = "Scales Repo" at "http://scala-scales.googlecode.com/svn/repo"
//val scalesXml = "scales" %% "scales-xml" % "0.2.1"

//antixml
val antiXML = "com.codecommit" %% "anti-xml" % "0.3"

  val hello = TaskKey[Unit]("hello", "Prints 'Hello World'")
  val sampleTask = TaskKey[Int]("sample-task")
  val stringTask = TaskKey[String]("string-task")

  val x = stringTask := System.getProperty("user.name")

  val y = sampleTask := {
    val sum = 1 + 2
    println("sum: " + sum)
    sum 
  }

  val helloTask = hello := {
    println("Hello World")
  }
  
  lazy val project = Project (
    "project",
    file ("."),
    settings = hwsettings ++ Seq(helloTask, x, y))
    .configs( FunTest )
    .settings( inConfig(FunTest)(Defaults.testTasks) : _*)

 lazy val FunTest = config("fun") extend(Test)

 def standardSettings = Seq(
    exportJars := true
  ) ++ Defaults.defaultSettings

  lazy val multi  = Project("multi", file("."), aggregate = Seq(alpha, beta))
  lazy val alpha = Project("alpha", file("alpha"), settings = standardSettings)
  lazy val beta = Project("beta",
    file("beta"),
    dependencies = Seq(alpha),
    settings = standardSettings ++ SbtOneJar.oneJarSettings
  )
}

  
