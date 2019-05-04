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
  * It's use in Free Applicative (but let's not go there)
  * Interpreters 
  * Note: Interpret recursively, then compute
  * Simple Marshall/Unmarshall Example
  * Performance
* Validation Using GADT
  * Accumulating Errors
  * Validating Data Before Object Instantiation
  * Validation using GADT
* Using HList instead of Tuples
  * Split
  * Conversion to case classes.
* DSL
  * Making this usable
* Interchange formats
  * JSON - Argonaut, Circe, LiftJson
  * BJSON
  * Protobuf
* Describing Rest Endpoints
* Creating Documentation
  * Swagger (Wrapping OPP - other peoples projects)
* CRUD - Final Steps
  * Database GADT Interpreters
  * React GADT Interpreters
* DEMO
  * This is not a framework, it is a collection of functions
* Your Domain Specific Types
  * Free Applicative - BYOGADT
  * Modifications to Interpreters to acommodate Free Ap
  

---

* What is the Bones project?
  * Original Inent: JSON extraction with validation
  * Create _generated_ functions from a schema using GADT interpreters
  * Only difference between endpoints is a Schema
  * Encapsilate 3rd party libraries behind an Interpreter

---

ADT - Algebraic Data Type

```tut:silent
sealed abstract class ValueOp

case object StringData extends ValueOp

case object IntData extends ValueOp

case class OptionalData(optionalValue: ValueOp) extends ValueOp

case class TupleData(leftValue: ValueOp, rightValue: ValueOp) extends ValueOp
```

---

GADT - _Generalized_ Algebraic Data Type

```tut:silent:reset
sealed abstract class ValueOp[A]

case object StringData extends ValueOp[String]

case object IntData extends ValueOp[Int]

case class OptionalData[B](b: ValueOp[B]) extends ValueOp[Option[B]]

case class TupleData[B,C]( b: ValueOp[B], c: ValueOp[C]) extends ValueOp[(B,C)]
``` 


---

Data Structure Examples

```tut
TupleData( StringData, OptionalData(IntData) )
```

```tut
TupleData( StringData,
  TupleData(
    TupleData( IntData, IntData),
    OptionalData(IntData)
  )
)
```

---

#### Parsing JSON

```tut:silent:reset
sealed abstract class ValueOp[A]

case class StringData(key: String)  extends ValueOp[String]

case class IntData(key: String)  extends ValueOp[Int]

case class OptionalData[B](optionalValueOp: ValueOp[B]) extends ValueOp[Option[B]]

case class TupleData[B,C](leftValue: ValueOp[B], rightValue: ValueOp[C]) extends ValueOp[(B,C)]
```
---

#### Parsing JSON

```tut
val example = TupleData( StringData("name"),
                TupleData(
                  OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
                  OptionalData(IntData("height"))
              ))

``` 

---

#### First Interpreter: Print the type
```tut:silent

object DocInterpreter {

 def createDoc[A](op: ValueOp[A]): String = {
   op match {
     case TupleData(b,c) => s"${createDoc(b)} combined with ${createDoc(c)})"
     case OptionalData(b) => s"${createDoc(b)} which is optional"
     case StringData(key) => s"a String with key ${key}"
     case IntData(key) => s"an Int with key ${key}"
   }
 } 
}
```

```tut
DocInterpreter.createDoc(example)
```

---

#### Marshall Interpreter
```tut:silent
import argonaut._
object ArgonautMarshall {

  def marshall[A](op: ValueOp[A]): A => Json = {
    op match {
      case TupleData(l,r) => {
        val fLeft = marshall(l)
        val fRight = marshall(r)
        (tuple: A) => {
          combine( fLeft(tuple._1), fRight(tuple._2))
        }
      }

      case OptionalData(aValueOp) => {
        val fOptional = marshall(aValueOp)
        (opt: A) => {
          opt match {
            case None => Json.jEmptyObject
            case Some(a) => fOptional(a)
          }
        }
      }

      case StringData(key) => str => Json.obj( (key, Json.jString(str)) )

      case IntData(key) => l => Json.obj( (key, Json.jNumber(l)) )


    }

  }

  def combine(prefix: Json, postfix: Json): Json = {
    val values1 = prefix.obj.toList.flatMap(_.toList)
    val values2 = postfix.obj.toList.flatMap(_.toList)
    Json.obj(values1 ::: values2: _*)
  }

}

```

---

#### Usage
```tut:silent

val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))

val dryFalls = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
```

#### Create Function and Pass Data
```tut
val waterfallToJson = ArgonautMarshall.marshall(waterfallSchema)
val waterfallJson = waterfallToJson(dryFalls)

```

---

#### What is waterfallToJson?
```tut:silent
    val waterfallFLiteral
      : ((String, (Option[(Int, Int)], Option[Int]))) => argonaut.Json =
      (i1: (String, (Option[(Int, Int)], Option[Int]))) => {           // <-- function params
        ArgonautMarshall.combine(
          { (s: String) =>
            Json.obj(("name", Json.jString(s)))
          }.apply(i1._1), { (i2: (Option[(Int, Int)], Option[Int])) => // <-- function params
            {
              ArgonautMarshall.combine(
                {
                  (i3: Option[(Int, Int)]) =>                          // <-- function params
                    {
                      i3 match {
                        case None => Json.jEmptyObject
                        case Some(a) => { (i4: (Int, Int)) =>          // <-- function params
                          {
                            ArgonautMarshall.combine({ (i: Int) =>     // <-- function params
                              Json.obj(("lattitude", Json.jNumber(i)))
                            }.apply(i4._1), { (i: Int) =>              //<-- function params
                              Json.obj(("longitude", Json.jNumber(i)))
                            }.apply(i4._2))
                          }
                        }.apply(a)
                      }
                    }
                }.apply(i2._1), { (i: Option[Int]) =>                 //<-- function params
                  i match {
                    case None => Json.jNull
                    case Some(a) => { (i: Int) =>
                      Json.obj(("age", Json.jNumber(i)))
                    }.apply(a)
                  }
                }.apply(i2._2)
              )
            }
          }.apply(i1._2)
        )
      }
```

---

```tut
  waterfallFLiteral.apply(dryFalls)
```

---

#### Unmarshall Example

```tut:silent
import argonaut.Json.JsonAssoc
object ArgonautUnmarshall {
      def unmarshall[A](op: ValueOp[A]) : Json => Either[String, A] = {
        op match {
          case op: OptionalData[b] =>
            val valueB = unmarshall(op.optionalValueOp) // Json => Either[String,Option[A]]
            json => {
              valueB(json) match {
                case Left(_) => Right(None)
                case Right(x) => Right(Some(x))
              }
            }
          case TupleData(leftOp, rightOp) =>
            val leftF = unmarshall(leftOp)
            val rightF = unmarshall(rightOp)
            json => {
              val left = leftF(json)
              val right = rightF(json)
              combineTuple(left,right)
            }
          case StringData(key) => json =>
            findField(key, json).flatMap(_._2.string).toRight(s"String Not Found ${key}")
          case IntData(key) => json =>
            findField(key, json).flatMap(_._2.number).flatMap(_.toInt)
              .toRight(s"Int Not Found ${key}")
        }
      }

      def combineTuple[B,C](b: Either[String,B], c: Either[String,C]): Either[String, (B,C)] = {
        (b,c) match {
          case ( Left(bErr), Left(cError) ) => Left(s"${bErr}|${cError}" )
          case ( Left(bErr), _ ) => Left(bErr)
          case ( _ , Left(cErr) ) => Left(cErr)
          case ( Right(b), Right(c) ) => Right( (b,c) )
        }
      }

      def findField(key: String, json: Json) : Option[JsonAssoc] = {
        json.obj.flatMap(_.toList.find(_._1 == key))
      }

    }
```

---

#### full circle, JSON to Data
```tut
ArgonautUnmarshall.unmarshall(waterfallSchema)(waterfallJson)
```

---

#### 2 Steps: Interpret, Run
```scala
          case op: OptionalData[b] =>

            // This Code is evaluated before returning the function
            // and is therefor only executed once per schema begin interpreted
            val valueB = unmarshall(op.optionalValueOp)

            // This function is executed many times
            // whenever we are actually transforming data
            json => {
              valueB(json) match {
                case Left(_) => Right(None)
                case Right(x) => Right(Some(x))
              }
            }
```
---

#### Do Not Do This

```tut:silent
  def marshall[A](op: ValueOp[A]): A => Json = a => {
    op match {
      case StringData(key) => Json.obj( (key, Json.jString(a)) )

      case IntData(key) => Json.obj( (key, Json.jNumber(a)) )

      case OptionalData(aValueOp) => {
        val fOptional = marshall(aValueOp)
        a match {
          case None => Json.jNull
          case Some(a) => fOptional(a)
        }
      }

      case TupleData(l,r) => {
        val fLeft = marshall(l)
        val fRight = marshall(r)
        ArgonautMarshall.combine( fLeft(a._1), fRight(a._2))
      }
    }

  }


```

---

### new Features/improvements

* case clases
  * Hierarchical
```tut:silent
case class Location(countryIso: String, stateProvince: Option[String])
case class Person(name: String, age: Int, location: Option[Location])
```
  * Key should not be on the Primative data description, does not allow for hierarchical data.


---


### Shapeless HList - Quick Overview

It's Heterogenius List

```tut:silent
import shapeless.ops.hlist
import shapeless.ops.hlist.{Length, Prepend, Split}
import shapeless.{::, Generic, HList, HNil, Nat, Succ}
```


Will allow us to flatten the tuple.
```tut
val personTuple = ((("Eugene", 12), Some(12)), 5)
val personHlist = "Eugene" :: 12 :: Some(12) :: 5 :: HNil
```

---

Can arbitrarily split an HList
```tut
personHlist.head
val split = Split[String::Int::Option[Int]::Int::HNil, Nat._2]
split(personHlist)
```

---

Can prepend HList to HList
```tut
``` 

---
<details class="notes"><summary>N</summary>
<p>
Test
</p>
</details>

Magic conversion from HList to case classes and vise versa.
```tut:silent
  case class Location(latitude: Int, longitude: Int)
  case class Waterfall(name: String, location: Option[Location], height: Option[Int])

  val genLocation = Generic[Location]
  val genWaterfall = Generic[Waterfall]

  val dryFallsHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
  val dryFallsLocation: String :: Option[Location] :: Option[Int] :: HNil =
    dryFallsHList.head :: dryFallsHList.tail.head.map(genLocation.from) :: dryFallsHList.tail.tail.head :: dryFallsHList.tail.tail.tail
```
```tut
   val waterfall = genWaterfall.from(dryFallsLocation)
   val waterfallHlist = genWaterfall.to(waterfall)
```



---

#### Mirror HList

---



# Validation Using GADT

---

```tut:silent
trait ValidationOp[T] {
  def isValid: T => Boolean
  def defaultError(t: T): String
  def description: String
}

case class MaxLength(max: Int) extends ValidationOp[String] {
  val isValid: String => Boolean = _.length <= max

  override def defaultError(t: String): String = s"$t is greater than $max"

  override def description: String = s"maximum of $max"
}



```

---


#### Validation

[GV](https://dreampuf.github.io/GraphvizOnline/#%0Adigraph%20G%20%7B%0A%0A%20%20subgraph%20cluster_0%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Is%20String%22-%3E%20%22Max%2030%22%3B%0A%20%20%20%20%22Is%20String%22%20-%3E%20%22Alpha%20Only%22%3B%0A%20%20%20%20label%20%3D%20%22Cardholder%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_1%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Month%20Is%20Number%22%20-%3E%20%22Is%20between%201%20and%2012%22%3B%0A%20%20%20%20label%20%3D%20%22Exp%20Month%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_2%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Year%20Is%20Number%22%20-%3E%20%22Is%20After%202018%22%3B%0A%20%20%20%20label%20%3D%20%22Exp%20Year%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_3%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22CC%20Is%20Number%22%20-%3E%20%22Luhn%20Check%22%3B%0A%20%20%20%20%22CC%20Is%20Number%22%20-%3E%20%22Starts%20with%203%2C4%2C5%20or%207%22%3B%0A%20%20%20%20label%20%3D%20%22Card%20Number%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_4%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Is%20between%201%20and%2012%22%20-%3E%20%22Is%20After%20Today%22%3B%0A%20%20%20%20%22Is%20After%202018%22%20-%3E%20%22Is%20After%20Today%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_5%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Max%2030%22%20-%3E%20%22Credit%20Card%22%3B%0A%20%20%20%20%22Alpha%20Only%22%20-%3E%20%22Credit%20Card%22%3B%0A%20%20%20%20%22Is%20After%20Today%22%20-%3E%20%22Credit%20Card%22%3B%0A%20%20%20%20%22Luhn%20Check%22%20-%3E%20%22Credit%20Card%22%3B%0A%20%20%20%20%22Starts%20with%203%2C4%2C5%20or%207%22%20-%3E%20%22Credit%20Card%22%0A%20%20%20%20%0A%20%20%20%20%20%20%0A%20%20%7D%0A%20%20%0A%20%20%0A%20%20%0A%20%20%0A%20%20JSON%20-%3E%20%22Is%20String%22%3B%0A%20%20JSON%20-%3E%20%22Month%20Is%20Number%22%3B%0A%20%20JSON%20-%3E%20%22Year%20Is%20Number%22%3B%0A%20%20JSON%20-%3E%20%22CC%20Is%20Number%22%0A%0A%20%20JSON%20%5Bshape%3DMdiamond%5D%3B%0A%7D)

![alt text](/cc-validation.png "Logo Title Text 1")


---
Free Applicative - Describing Computations

```tut:silent:reset
import cats.free.FreeApplicative
import cats.free.FreeApplicative.lift

sealed abstract class ValueOp[A]
type Value[A] = FreeApplicative[ValueOp, A]

case object StringData extends ValueOp[String]
case object IntData extends ValueOp[Int]
case class Tuple[B,C](b: Value[B], c: Value[C]) extends ValueOp[(B,C)]
```

```tut:silent
```
```tut
lift(StringData)
```

---

```tut:silent
```

---

#### Free Applicative
* Describe Data
* Interpreters convert GADTs
* Interpreters consume the entire data structure
* Wrapping and Unwrapping is complex

---

How far will GADTs take us?



