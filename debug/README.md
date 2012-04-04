`scalac-plugin-xml.jar` is a jar containing the `scala-plugin.xml`
file but not any classfiles. It is used to debug the compiler plugin
in Eclipse, as explained at the end of the tutorial on [Writing Scala
Compiler Plugins](http://www.scala-lang.org/node/140).

The steps are:

* create a launch configuration for `scala.tools.nsc.Main`
* pass `-Xplugin:debug/scalac-plugin-xml.jar` as argument
* add this project in the classpath of the launch configuration
