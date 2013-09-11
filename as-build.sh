#!/bin/sh

cd "/Users/nosheen/Google Drive/EclipseProjects/as/"
/Users/nosheen/Development/sbt/bin/sbt package
#/Users/nosheen/Development/sbt/bin/sbt run

#for quick testing
#wait
#cd "/Users/nosheen/Google Drive/EclipseProjects/as-tests"

/opt/local/share/scala/scala-2.10.2/bin/scalac -classpath \
"/Users/nosheen/Google Drive/EclipseProjects/as/target/scala-2.10/as_2.10-1.0.jar" \
-Xplugin:"/Users/nosheen/Google Drive/EclipseProjects/as/target/\
scala-2.10/as_2.10-1.0.jar"  \
"/Users/nosheen/Google Drive/EclipseProjects/as/src/main/scala/Main.scala"
