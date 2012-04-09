import AssemblyKeys._

name := "sav"

organization := "EPFL"

scalaVersion := "2.9.1"

libraryDependencies <+= scalaVersion("org.scala-lang" % "scala-compiler" % _ % "provided")

seq(assemblySettings: _*)

excludedJars in assembly <<= (fullClasspath in assembly) map { cp =>
  cp filter { _.data.getName.startsWith("scala-") }
}
