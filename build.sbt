sourceManaged in Compile := file("content")
enablePlugins(TutPlugin)
tutTargetDirectory := file("content")


libraryDependencies ++= Seq(
  "io.argonaut" %% "argonaut" % "6.2.2",
  "com.chuusai" %% "shapeless" % "2.3.3",
  "org.typelevel" %% "cats-core" % "1.4.0",
  "org.typelevel" %% "cats-free" % "1.4.0",
)
