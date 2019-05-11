sourceManaged in Compile := file("content")
enablePlugins(TutPlugin)
tutTargetDirectory := file("content")
addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.7")


scalacOptions ++= Seq("-Ypartial-unification")

lazy val http4sVersion = "0.20.0"


libraryDependencies ++= Seq(
  "io.argonaut" %% "argonaut" % "6.2.2",
  "com.chuusai" %% "shapeless" % "2.3.3",
  "org.typelevel" %% "cats-core" % "1.4.0",
  "org.typelevel" %% "cats-free" % "1.4.0",
  "io.frees" %% "iota-core"  % "0.3.10",
  "org.http4s" %% "http4s-dsl" % http4sVersion,
  "org.http4s" %% "http4s-blaze-server" % http4sVersion,
  "org.http4s" %% "http4s-circe" % http4sVersion
)
