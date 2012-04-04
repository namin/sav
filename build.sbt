name := "sav"

organization := "EPFL"

scalaVersion := "2.9.1"

libraryDependencies <+= scalaVersion("org.scala-lang" % "scala-compiler" % _ % "provided")

