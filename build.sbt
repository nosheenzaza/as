name := "as"

version := "1.0"

scalaVersion := "2.10.2"

mainClass in (Compile, run) := Some("Main")

//scalacOptions += "-Xshow-phases"

libraryDependencies <+= scalaVersion("org.scala-lang" % "scala-compiler" % _ )