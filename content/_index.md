+++
title = "GADTs in Scala"
outputs = ["Reveal"]
+++

## Compile Time Scaffolding in Scala

* Author: Travis Stevens
* Twitter: @OleTraveler
* Comments: https://bit.ly/2GOstV4

---

Quick Outline

* Goal is to build a compile time scaffolding library.
* GADT Basics
* Validation using GADT
* Shapeless - HList
* More Interchange formats (protobuff)
* Describing REST endpoints
* Documentation for Free (as in Beer)
* Extending with Free Applicative

---
Detailed Outline

* What are GADTs?
  * Basics
  * Free (Applicative|Monad)
  * Interpreters 
  * Important: Interpret, then compute
  * Simple Extraction Example
  * Performance
* Validation Using GADT
  * Accumulating Errors
  * Validating Data Before Instantiation
  * Validation using GADT
* Using HList instead of Tuples
  * Split
  * Conversion to case classes.
* Interchange formats
  * JSON - Argonaut, Circe, LiftJson
  * BJSON
  * Protobuf
* Describing Rest Endpoints
* Creating Documentation
  * Swagger
* CRUD - Final Steps
  * Database Interpreters
  * React Interpreters
* DEMO
  * This is not a framework
* Your Domain Specific Types
  * Free Applicative - BYOGADT
  * Interpreters
  

---

ADT - Algebraic Data Type

```scala
sealed abstract class ValueOp
case object StringData extends ValueOp
case object LongData extends ValueOp
case class OptionalData(t1: ValueOp) extends ValueOp
case class TupleData(t1: ValueOp, t2: ValueOp) extends ValueOp
```

---

GADT - _Generalized_ Algebraic Data Type

```scala
sealed abstract class ValueOp[A]
case object StringData extends ValueOp[String]
case object LongData extends ValueOp[Long]
case class OptionalData[B](t1: ValueOp[B]) extends ValueOp[Option[B]]
case class TupleData[B,C](t1: ValueOp[B], t2: ValueOp[C]) extends ValueOp[(B,C)]
``` 


---

Data Structure Example 1

```scala
scala> TupleData( StringData, OptionalData(LongData) )
res0: TupleData[String,Option[Long]] = TupleData(StringData,OptionalData(LongData))
```

---

Data Structure Example 2
```scala
scala> TupleData( TupleData ( OptionalData ( TupleData( StringData, LongData )), OptionalData(LongData)), LongData )
res1: TupleData[(Option[(String, Long)], Option[Long]),Long] = TupleData(TupleData(OptionalData(TupleData(StringData,LongData)),OptionalData(LongData)),LongData)
```

---

Digression 1a: Free Monad - Describing Actions

```scala
sealed trait KVStoreA[A]
case class Put[T](key: String, value: T) extends KVStoreA[Unit]
case class Get[T](key: String) extends KVStoreA[Option[T]]
case class Delete(key: String) extends KVStoreA[Unit]

import cats.free.Free

type KVStore[A] = Free[KVStoreA, A]

import cats.free.Free.liftF
```
```scala
scala> liftF[KVStoreA, Unit](Put[String]("name", "King Gizzard"))
res2: cats.free.Free[KVStoreA,Unit] = Free(...)
```
---

Digression 1b: Free Applicative - Describing Data

```scala
sealed abstract class ValidationOp[A]
case class Size(size: Int) extends ValidationOp[Boolean]
case object HasNumber extends ValidationOp[Boolean]

import cats.free.FreeApplicative
import cats.free.FreeApplicative.lift
type Validation[A] = FreeApplicative[ValidationOp, A]
```
```scala
scala> lift(Size(1))
res3: cats.free.FreeApplicative.FA[ValidationOp,Boolean] = FreeApplicative(...)
```

---

#### Free Monad
* Continuations - not our goal

---

#### Free Applicative
* Describe Data
* Interpreters convert GADTs
* Interpreters consume the entire data structure
* Wrapping and Unwrapping is complex

---

How far will GADTs take us?

---

#### Interchange Formats are Key Value Pairs.

```scala
sealed abstract class ValueOp[A]
case class StringData(key: String)  extends ValueOp[String]
case class LongData(key: String)  extends ValueOp[Long]
case class OptionalData[B](t1: ValueOp[B]) extends ValueOp[Option[B]]
case class TupleData[B,C](t1: ValueOp[B], t2: ValueOp[C]) extends ValueOp[(B,C)]
```

```scala
scala> val example = 
     |   TupleData( 
     |     TupleData( 
     |       OptionalData ( TupleData( StringData("name"), LongData("age"))), 
     |       OptionalData( LongData("experienceInYears"))), 
     |     LongData("numberOfKudos")
     |     )
example: TupleData[(Option[(String, Long)], Option[Long]),Long] = TupleData(TupleData(OptionalData(TupleData(StringData(name),LongData(age))),OptionalData(LongData(experienceInYears))),LongData(numberOfKudos))
``` 

---

```scala
object DocInterpreter {

 def createDoc[A](op: ValueOp[A]): String = {
   op match {
     case StringData(key) => s"${key}:String"
     case LongData(key) => s"${key}:Long"
     case OptionalData(b) => s"Optional( ${createDoc(b)} )"
     case TupleData(b,c) => s"Tuple( ${createDoc(b)}, ${createDoc(c)})"
   }
 } 
}
```

```scala
scala> DocInterpreter.createDoc(example)
res0: String = Tuple( Tuple( Optional( Tuple( name:String, age:Long) ), Optional( experienceInYears:Long )), numberOfKudos:Long)
```



