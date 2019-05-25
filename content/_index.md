+++
title = "GADTs in Scala"
outputs = ["Reveal"]
+++

## Compile Time Scaffolding in Scala w/ GADTs

* Author: Travis Stevens
* Twitter: @OleTraveler
* Slides: https://oletraveler.github.io/bones-presentation/  
   * or https://bit.ly/2J9O5i1

---

## Talk  Outline

* GADT Basics
* GADTs w/ HList
* Validation
* Describing REST endpoints
* Demo
* \<Ctrl-D\>

---

## Objectives

  * Learn about GADTs and Interpreters
    * Utilize this pattern in your application
  * Learn about the Bones project -- I am looking for feedback

---

## What are GADTs

Generalized Algebraic Data Types

* Aliases
  * Guarded Recursive Data Type
  * First-class Phantom Type
  * Fixed-point types (Generalization of Recursion)  
* Data Structure
   * Algebra
* Interpreter
   * Transforming the Data Structure into another Data Structure 

---

Algebra

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 

<details class="notes"><summary>?</summary>
<p>
* phantom type.
* For Optional data we wrap the type from the Value in Option
* For tuple, combine 2 types into the duple.
* Limit our domain to just Ints and String (and combinations of them)
</p>
</details>



---

Algebra

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 

Usage

```scala
val x: KvpValue[(Int,Int)] = TupleData(IntData, IntData)
```

---

Algebra

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 

Usage

```scala
val x: KvpValue[Option[(Int,Int)]] =
  OptionalData(
    TupleData(IntData, IntData)
  )
```

---

Algebra

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 

Usage

```scala
val x: KvpValue[(Option[(Int,Int)], Option[Int])] =
  TupleData(
    OptionalData(
      TupleData(IntData, IntData)
    ),
    OptionalData(IntData)
  )
```

---

Algebra

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 

Usage

```scala
val x: KvpValue[(String,(Option[(Int,Int)], Option[Int]))] =
    TupleData( StringData,
      TupleData(
        OptionalData(
          TupleData( 
            IntData, IntData
          ),
        ),
        OptionalData(IntData)
      )
    )
```

---

Algebra

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 

Compiler keeps track fo the type

```scala
scala> val x =
     |     TupleData( StringData,
     |       TupleData(
     |         OptionalData(
     |           TupleData( 
     |             IntData, IntData
     |           ),
     |         ),
     |         OptionalData(IntData)
     |       )
     |     )
x: TupleData[String,(Option[(Int, Int)], Option[Int])] = TupleData(StringData,TupleData(OptionalData(TupleData(IntData,IntData)),OptionalData(IntData)))
```

---

Example: Parsing Key Value Pairs

---

Example: Parsing Key Value Pairs

```scala
sealed abstract class KvpValue[A]

case class StringData(key: String)  extends KvpValue[String]

case class IntData(key: String)  extends KvpValue[Int]

case class OptionalData[B](optional: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C](e1: KvpValue[B], e2: KvpValue[C]) extends KvpValue[(B,C)]
```

---
Building our Schema

```scala
scala> val waterfallSchema = 
     |   TupleData( StringData("name"),
     |     TupleData(
     |       OptionalData( 
     |         TupleData( 
     |           IntData("latitude"), IntData("longitude"))),
     |       OptionalData(IntData("height"))
     |     )
     |   )
waterfallSchema: TupleData[String,(Option[(Int, Int)], Option[Int])] = TupleData(StringData(name),TupleData(OptionalData(TupleData(IntData(latitude),IntData(longitude))),OptionalData(IntData(height))))
``` 

---
Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

First Interpreter: Description of the Schema

```scala
object DocInterpreter {

 def createDoc[A](kvp: KvpValue[A]): String = {
   kvp match {
     case TupleData(e1,e2) => s"(${createDoc(e1)} combined with ${createDoc(e2)})"
     case OptionalData(optB) => s"(${createDoc(optB)} which is optional)"
     case StringData(key) => s"a String with key ${key}"
     case IntData(key) => s"an Int with key ${key}"
   }
 } 
}
```

---
Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

First Interpreter: Description of the Schema

```scala
object DocInterpreter {

 def createDoc[A](kvp: KvpValue[A]): String = {
   kvp match {
     case TupleData(e1,e2) => s"(${createDoc(e1)} combined with ${createDoc(e2)})"
     case OptionalData(optB) => s"(${createDoc(optB)} which is optional)"
     case StringData(key) => s"a String with key ${key}"
     case IntData(key) => s"an Int with key ${key}"
   }
 } 
}
```

```scala
scala> DocInterpreter.createDoc(waterfallSchema)
res0: String = (a String with key name combined with (((an Int with key latitude combined with an Int with key longitude) which is optional) combined with (an Int with key height which is optional)))
```

<details class="notes"><summary>?</summary>
<p>
* TupleData and OptionalData unwrap the members and recursively call createDoc and then add some metadata
* String and Int data print the key and type.
</p>
</details>

---
Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

Generate JSON: Marshall Interpreter
```scala
import argonaut._
object ArgonautMarshall {

  def marshallF[A](kvp: KvpValue[A]): A => Json = {
    kvp match {
      case t: TupleData[e1,e2] => {
        val e1F: e1 => Json = marshallF(t.e1)
        val e2F: e2 => Json = marshallF(t.e2)
        (tuple: A) => {
          combine( e1F(tuple._1), e2F(tuple._2))
        }
      }
    }
  }

  def combine(prefix: Json, postfix: Json): Json = ???

}

```

* Note use of type variable

--- 
Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

Generate Marshall Interpreter
```scala
import argonaut._
object ArgonautMarshall {

  def marshallF[A](kvp: KvpValue[A]): A => Json = {
    kvp match {
      case o: OptionalData[b] => {
        val bF: b => Json = marshallF(o.optional)
        (opt: A) => {
          opt match {
            case None => Json.jEmptyObject
            case Some(a) => bF(a)
          }
        }
      }    
      
//    case t: TupleData[l,r] => ???

    }
  }
}
```

---
Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

Generate Marshall Interpreter

```scala
import argonaut._
object ArgonautMarshall {

  def marshall[A](kvp: KvpValue[A]): A => Json = {
    kvp match {
      case StringData(key) => str => Json.obj( (key, Json.jString(str)) )

       case IntData(key) => l => Json.obj( (key, Json.jNumber(l)) )
     
//     case o: OptionalData[b] => ???

//     case t: TupleData[l,r] => ???

    }
  }   
}
   
```




---

Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

Create Function
```scala
scala> val waterfallToJson = ArgonautMarshall.marshallF(waterfallSchema)
waterfallToJson: ((String, (Option[(Int, Int)], Option[Int]))) => argonaut.Json = ArgonautMarshall$$$Lambda$21242/1882021955@64fe81e6
```

---

Our Schema

```scala
val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))
```

Create Function
```scala
scala> val waterfallToJson = ArgonautMarshall.marshallF(waterfallSchema)
waterfallToJson: ((String, (Option[(Int, Int)], Option[Int]))) => argonaut.Json = ArgonautMarshall$$$Lambda$21242/1882021955@7e309df6
```

Pass Data
```scala
scala> val dryFalls = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
dryFalls: (String, (Some[(Int, Int)], Some[Int])) = (Dry Falls,(Some((35,-83)),Some(80)))

scala> val waterfallJson = waterfallToJson(dryFalls)
waterfallJson: argonaut.Json = {"name":"Dry Falls","latitude":35,"longitude":-83,"height":80}
```



---

## Schema
![data-structure-base](data-structure-base.png)

---

## Runtime Function
![data-structure](data-structure.png)

---

## Runtime Function
![result](result.png)

---

Unmarshall Example

```scala
object ArgonautUnmarshall {
  def unmarshallF[A](kvp: KvpValue[A]) : Json => Either[String, A] = {
    kvp match {
      case t: TupleData[e1,e2] =>
        val e1F: Json => Either[String,e1] = unmarshallF(t.e1)   // recurse b type
        val e2F: Json => Either[String,e2] = unmarshallF(t.e2)   // recurse c type
        json => {
          val e1Result: Either[String,e1] = e1F(json)  
          val e2Result: Either[String,e2] = e2F(json)
          combineTuple(e1Result,e2Result)
        }
    }
  }

  def combineTuple[B,C](b: Either[String,B], c: Either[String,C]): Either[String, (B,C)] = ???

}
```

---

Unmarshall Example
```scala
object ArgonautUnmarshall {
  def unmarshallF[A](kvp: KvpValue[A]) : Json => Either[String, A] = {
    kvp match {
      case op: OptionalData[b] =>
        val valueB: Json => Either[String,b] = unmarshallF(op.optional) // recurse
        json => {
          valueB(json) match {
            case Left(_) => Right(None)
            case Right(x) => Right(Some(x))
          }
        }
//    case t: TupleData[l,r] => ???        
    }
  }
}
```


---

Unmarshall Example
```scala
object ArgonautUnmarshall {
  def unmarshall[A](kvp: KvpValue[A]) : Json => Either[String, A] = {
    kvp match {
      case StringData(key) => json =>
        findField(key, json).flatMap(_._2.string).toRight(s"String Not Found ${key}")
      case IntData(key) => json =>
        findField(key, json).flatMap(_._2.number).flatMap(_.toInt)
          .toRight(s"Int Not Found ${key}")
//    case t: TupleData[b,c] => ???
//    case op: OptionalData[b] => ???
    }
  }

  def findField(key: String, json: Json) : Option[JsonAssoc] = {
    json.obj.flatMap(_.toList.find(_._1 == key))
  }

}
```




<details class="notes"><summary>?</summary>
 <p>
* 
* Either is required in case the input Json doesn't conform to our specification.
* For the marshall example, we didn't need Either because the compile enforsed the our type conformed to the schema.
</p> 
</details>

---

JSON to Data (full circle)
```scala
scala> waterfallJson
res1: argonaut.Json = {"name":"Dry Falls","latitude":35,"longitude":-83,"height":80}

scala> ArgonautUnmarshall.unmarshallF(waterfallSchema)(waterfallJson)
res2: Either[String,(String, (Option[(Int, Int)], Option[Int]))] = Right((Dry Falls,(Some((35,-83)),Some(80))))
```

---

2 Steps: Interpret, Run
```scala
          case op: OptionalData[b] =>

            // This Code is evaluated before returning the function
            // and is therefor only executed once per schema begin interpreted
            val valueB = unmarshallF(op.optionalKvpValue)

            // This function is executed many times,
            // one for each data transformation
            json => {
              valueB(json) match {
                case Left(_) => Right(None)
                case Right(x) => Right(Some(x))
              }
            }
```

---

## Recap

* As the data structure grows, the type is maintained
* Interpreters are recursive, but may result in non-recursive data structure
* Created both Documentation and Runtime Interpreter for GADT

![data-structure](waterfalls/discovery-falls.jpg)
 

---

## Improvements to our implementation

* Current implementation does not allow for hierarchical data
* Tuples are clunky (and limited to 22 values)
* We want Hierarchical case classes

```scala
case class Location(latitude: Int, longitude: Int)
case class Waterfall(name: String, location: Option[Location], height: Option[Int])
```

---

## Shapeless HList - Quick Overview




Example Heterogeneous List
```scala
scala> val waterfallTuple = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
waterfallTuple: (String, (Some[(Int, Int)], Some[Int])) = (Dry Falls,(Some((35,-83)),Some(80)))

scala> val waterfallHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
waterfallHList: String :: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: Some(80) :: HNil
```

---

Arbitrarily split an HList
```scala
val waterfallHlist = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
val split = Split[String::Option[Int::Int::HNil]::Option[Int]::HNil, Nat._2]
```

---

Arbitrarily split an HList
```scala
val waterfallHlist = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
val split = Split[String::Option[Int::Int::HNil]::Option[Int]::HNil, Nat._2]
```
```scala
scala> split(waterfallHlist)
res0: split.Out = (Dry Falls :: Some(35 :: -83 :: HNil) :: HNil,Some(80) :: HNil)
```

---

Concatenate HLists of arbitrary sizes
```scala
val prefix = "Dry Falls" :: Some( 35 :: -83 :: HNil) :: HNil
val suffix = Some(80) :: HNil
```

```scala
scala> prefix ::: suffix
res1: String :: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: Some(80) :: HNil
``` 

---

Concatenate HLists of arbitrary sizes
```scala
val prefix = "Dry Falls" :: Some( 35 :: -83 :: HNil) :: HNil
val suffix = Some(80) :: HNil
```

```scala
scala> prefix ::: suffix
res2: String :: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: Some(80) :: HNil
``` 

---

Conversion HList to/from Case Classes

```scala
  case class Location(latitude: Int, longitude: Int)
  case class Waterfall(name: String, location: Option[Location], height: Option[Int])

  val genLocation = Generic[Location]
  val genWaterfall = Generic[Waterfall]
```  
```scala
scala>     genWaterfall.to _
res3: Waterfall => genWaterfall.Repr = $$Lambda$21323/1567139798@425c4895

scala>     genWaterfall.from _
res4: genWaterfall.Repr => Waterfall = $$Lambda$21324/1122702221@4b126d74
```

---

Conversion HList to/from Case Classes

```scala
  case class Location(latitude: Int, longitude: Int)
  case class Waterfall(name: String, location: Option[Location], height: Option[Int])

  val genLocation = Generic[Location]
  val genWaterfall = Generic[Waterfall]
```

```scala
  val dryFallsHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
  val dryFallsLocation: String :: Option[Location] :: Option[Int] :: HNil = dryFallsHList.head :: dryFallsHList.tail.head.map(genLocation.from) :: dryFallsHList.tail.tail.head :: dryFallsHList.tail.tail.tail
```

```scala
scala>    val waterfall = genWaterfall.from(dryFallsLocation)
waterfall: Waterfall = Waterfall(Dry Falls,Some(Location(35,-83)),Some(80))

scala>    val waterfallHlist = genWaterfall.to(waterfall)
waterfallHlist: genWaterfall.Repr = Dry Falls :: Some(Location(35,-83)) :: Some(80) :: HNil
```

---

## Refactor KvpValue

* Two Algebras 
  * `KvpHList[H<:HList,N<:Nat]`
     * Groups 0 or more key value pairs (Json Object)
     * Mirrors HList functionality for prepend/concat
     * Guarantee that head of non nil list will have a key/value class
         * `KeyValueDefinition(key: String, kvp: KvpValue)`
     * Type Parameter will track the Type
  * `KvpValue[A]`
     * Remove key from Primitives
     * Remove TupleData type
     * Add a type representing the conversion from KvpHList to a case class
     * Interpreter result is case class, not HList
  * Two interpreters which recursively call each other for hierarchical data


---

Refactored KvpValue

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]]

case class KvpConvertData[H<:HList, N<:Nat, A](kvpHList: KvpHList[H,N], fha: H => A, fah: A => H) extends KvpValue[A]
```

---

Key/Value class
```scala
case class KeyValueDefinition[A](key: String, kvpValue: KvpValue[A])
```

---

KvpHList
```scala
sealed abstract class KvpHList[H <: HList, N <: Nat]
```

---

KvpHList
```scala
sealed abstract class KvpHList[H <: HList, N <: Nat]

object KvpNil extends KvpHList[HNil, Nat._0]
```

---

KvpHList
```scala
sealed abstract class KvpHList[H <: HList, N <: Nat]

object KvpNil extends KvpHList[HNil, Nat._0]

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H]
(
  keyValueDefinition: KeyValueDefinition[A],
  tail: KvpHList[H, N],
  isHCons: IsHCons.Aux[OUT, A, H]
) extends KvpHList[OUT, Succ[N]]
```

---

KvpHList
```scala
sealed abstract class KvpHList[H <: HList, N <: Nat]

object KvpNil extends KvpHList[HNil, Nat._0]

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H]
(
  keyValueDefinition: KeyValueDefinition[A],
  tail: KvpHList[H, N],
  isHCons: IsHCons.Aux[OUT, A, H]
) extends KvpHList[OUT, Succ[N]]

case class KvpHListHead[HH <: HList, HN <:Nat, HT<:HList, NT <:Nat, HO<:HList, NO<:Nat](
  head: KvpHList[HH, HN],
  tail: KvpHList[HT, NT],
  prepend: Prepend.Aux[HH, HT, HO],
  split: Split.Aux[HO, HN, HH, HT], // analogous: Split.Aux[prepend.OUT,HL,H,T] with lpLength: Length.Aux[H,HL],
) extends KvpHList[HO, NO]
```

---

## Bizarre HList Triangle
* KvpValue can contain KvpHList
* Head of KvpHList is a KeyValueDefinition
* Value in KeyValueDefinition is a KvpValue

---

KvpHList Cons and Concat
```scala
    // Enforce head must be a KvpSingleValueHead
    def ::[B](v: KeyValueDefinition[B])(implicit isHCons: IsHCons.Aux[B::HO, B, HO]):
      KvpSingleValueHead[A :: HO, Succ[HN]] = ???

    def :::[HO <: HList, NO <: Nat, HP <: HList, NP <: Nat](prefix: KvpHList[HP, NP])(
      implicit prepend: Prepend.Aux[HP, HH, HO],
      lengthP: Length.Aux[HP, NP],
      length: Length.Aux[HO, NO],
      split: Split.Aux[HO, NP, HP, HH]
    ): KvpHListHead[HP, NP, HH, HP, HO, NO] = ???

```



---

Interpreter - Mutual Recursion
```scala
object ArgonautMarshall {
   type Key = String
   def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = ???
   def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = ???
}
```


---

Waterfall Example
```scala
case class Location(lat: Int, long: Int)
case class Waterfall(name: String, location: Option[Location], height: Option[Int])

val locationHlistSchema =
  KeyValueDefinition("latitude", IntData) ::
  KeyValueDefinition("longitude", IntData) ::
  KvpNil

val genericLocation = Generic[Location]
val locationSchema = KvpConvertData(locationHlistSchema, genericLocation.from, genericLocation.to)

val waterfallHlistSchema =
  KeyValueDefinition("name", StringData) ::
  KeyValueDefinition("location", OptionalData(locationSchema)) ::
  KeyValueDefinition("height", OptionalData(IntData)) ::
  KvpNil

val genericWaterfall = Generic[Waterfall]
```




```scala
scala>   val waterfallSchema = KvpConvertData(waterfallHlistSchema, genericWaterfall.from, genericWaterfall.to)
waterfallSchema: slides.HListSlides.KvpConvertData[slides.HListSlides.genericWaterfall.Repr,shapeless.Succ[shapeless.Succ[shapeless.Succ[shapeless.Nat._0]]],slides.HListSlides.Waterfall] = KvpConvertData(KvpSingleValueHead(KeyValueDefinition(name,StringData),KvpSingleValueHead(KeyValueDefinition(location,OptionalData(KvpConvertData(KvpSingleValueHead(KeyValueDefinition(latitude,IntData),KvpSingleValueHead(KeyValueDefinition(longitude,IntData),slides.HListSlides$KvpNil$@4c420ae0,shapeless.ops.hlist$IsHCons$$anon$156@1edc29ed),shapeless.ops.hlist$IsHCons$$anon$156@531112e),slides.HListSlides$$$Lambda$21350/779881388@857e28f,slides.HListSlides$$$Lambda$21351/21936550@549eec6f))),KvpSingleValueHead(KeyValueDefinition(height,OptionalData(IntData)),slides.HListSlides...
```

---

#### Validation

---

![waterfall](waterfall-validation.png "Logo Title Text 1")

  * Short Circuit
     * Converting Data Types
     * Combining Data Types (hierarchical data)
  * Accumulate
     * At each KVP Value
     * Each parallel input   

[GV](https://dreampuf.github.io/GraphvizOnline/#%0Adigraph%20G%20%7B%0A%0A%20%20subgraph%20cluster_0%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Is%20String%22-%3E%20%22Max%2030%22%3B%0A%20%20%20%20%22Is%20String%22%20-%3E%20%22Words%20Only%22%3B%0A%20%20%20%20label%20%3D%20%22Name%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_1%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Lat%20Is%20Number%22%20-%3E%20%22Lat%3A%20-90..90%22%3B%0A%20%20%20%20label%20%3D%20%22Latitude%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_2%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Lon%20Is%20Number%22%20-%3E%20%22Lon%3A%20-90..90%22%3B%0A%20%20%20%20label%20%3D%20%22Longitude%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_3%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Height%20Is%20Number%22%20-%3E%20%22Greater%20than%200%22%3B%0A%20%20%20%20%22Height%20Is%20Number%22%20-%3E%20%22Less%20than%203%2C212%20ft%22%3B%0A%20%20%20%20label%20%3D%20%22Card%20Number%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_4%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Lat%3A%20-90..90%22%20-%3E%20%22Is%20in%20WNC%22%3B%0A%20%20%20%20%22Lon%3A%20-90..90%22%20-%3E%20%22Is%20in%20WNC%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_5%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Max%2030%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Words%20Only%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Is%20in%20WNC%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Greater%20than%200%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Less%20than%203%2C212%20ft%22%20-%3E%20%22Waterfall%22%0A%20%20%7D%0A%20%20%0A%20%20%0A%20%20%0A%20%20%0A%20%20JSON%20-%3E%20%22Is%20String%22%3B%0A%20%20JSON%20-%3E%20%22Lat%20Is%20Number%22%3B%0A%20%20JSON%20-%3E%20%22Lon%20Is%20Number%22%3B%0A%20%20JSON%20-%3E%20%22Height%20Is%20Number%22%3B%0A%0A%20%20JSON%20%5Bshape%3DMdiamond%5D%3B%0A%7D)


---

Validation Using a GADT state of mind 
```scala
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

#### Validation Interpreter

```scala
def isValid[A](op: ValidationOp[A]): A => Either[String, A] = {
  a => if (op.isValid(a)) Right(a) else Left(op.defaultError(a))
}
def doc[A](op: ValidationOp[A]): String = {
  op.description
}
```

---
#### Accumulate errors in Primitive Types


```scala
case class StringData(validationOps: ValidationOp[String]) extends KvpValue[String]

def unmarshall[A](kvpValue: KvpValue[A]): (Key, Json) => Either[NonEmptyList[String],A] = {
kvpValue match {
  case StringData(validations) =>
    (key, json) =>
      for {
        jsonString <- json.field(key).toRight(NonEmptyList.one(s"Field with key $key not found."))
        str <- jsonString.string.toRight(NonEmptyList.one(s"Field with key $key is not a String"))
        validStr <- applicativeCombine(validations.map(validationOp => isValid(validationOp).apply(str)))
      } yield validStr
  }
}

```

---

#### Accumulate results, Short Circuit Product Type

```scala
  case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H]
  (
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N],
    isHCons: IsHCons.Aux[OUT, A, H],
    validationOps: List[ValidationOp[OUT]]
  ) extends KvpHList[OUT, Succ[N]]


  def accumulate[A,B,C](e1: Either[NonEmptyList[String],A], e2: Either[NonEmptyList[String],B])(f: (A,B) => C)
    : Either[NonEmptyList[String],C] = ???

  // Doesn't quite compile.
  def unmarshallHList[H<:HList, N<:Nat](kvpValue: KvpHList[H,N]): Json => Either[NonEmptyList[String],H] = {
    kvpValue match {
      case kvp: KvpSingleValueHead[a,h,n,o] =>
        val kvpF = unmarshallF(kvp.fieldDefinition.op)
        val tailF = unmarshallHList(kvp.tail)
        (json) =>
          for {
            jsonString <- json.obj.toRight(NonEmptyList.one(s"JSON is not an object"))
            hlist <- accumulate(kvpF(kvp.fieldDefinition.key,json), tailF(json))((t1: a,t2: h) => {
              (t1 :: t2)
            })
            validStr <- applicativeTraverse(kvp.validationOps.map(validationOp => isValid(validationOp).apply(hlist)))
          } yield validStr
    }
  }
```

---

#### Describing REST endpoints

   * Input
   * Output
   * Error
   
---

CRUD Algebra
```scala
case class Create[I,E,O](in: KvpValue[I], err: KvpValue[E], out: KvpValue[O]) 
case class Read[E,O](err: KvpValue[E], out: KvpValue[O])
case class Update[I,E,O](in: KvpValue[I], err: KvpValue[E], out: KvpValue[O])
case class Delete[E,O](err: KvpValue[E], out: KvpValue[O])
case class Search[E,O](err: KvpValue[E], out: KvpValue[O])
```

---

Business Logic
```scala
def createF[I,E,O]: I => Either[E,O] = ???
def readF[ID,E,O]: ID => Either[E,O] = ???
def updateF[ID,I,E,O]: (ID,I) => Either[E,O] = ???
def delete[ID,E,O]: ID => Either[E,O] = ???
def findAll[O]: () => Stream[O] = ???
def search[SP,E,O]: SP => Either[E,Stream[O]] = ???
```

---

# Interpreter

  * Take care of the Plumbing
     * Encoding Routes
     * What to use as an ID
     * Roles
     * Extract data for a search
       * parameters
       * page limits and sizing
     
---





```scala

  type Key = String
  case class Create[I,E,O](in: KvpValue[I], err: KvpValue[E], out: KvpValue[O])
  def marshallF[A](op: KvpValue[A]): A => Array[Byte] = ???
  def unmarshallF[A](op: KvpValue[A]): Array[Byte] => Either[String,A] = ???

  def post[CI, CE, CO](c: Create[CI,CE,CO],
                       path: String): (CI => IO[Either[CE, CO]]) => HttpRoutes[IO] = { createF =>

    val inF: Array[Byte] => Either[String,CI] = unmarshallF(c.in)
    val outF: CO => Array[Byte] = marshallF(c.out)
    val errF: CE => Array[Byte] = marshallF(c.err)


    HttpRoutes.of[IO] {
      case req@Method.POST -> Root / path => {
        val result: EitherT[IO, IO[Response[IO]], IO[Response[IO]]] = for {
          body <- EitherT[IO, IO[Response[IO]], Array[Byte]] {
            req.as[Array[Byte]].map(Right(_))
          }
          in <- EitherT.fromEither[IO] {
            inF(body).left.map(x => BadRequest())                  // <---- input conversion to CI
          }
          out <- EitherT[IO, IO[Response[IO]], CO] {
            createF(in)                                            // <---- business logic
              .map(_.left.map(ce => {
              val out = errF(ce)                                   // <----- error case output conversion from CE
              InternalServerError(out,
                Header("Content-Type", "text/json"))
            }))
          }
        } yield {
          Ok(outF(out), Header("Content-Type", "text/json"))        // <----- output conversion from CO
        }
        result.value.flatMap(_.merge)
      }
    }
  }

```


---

## Collection of interpreters

  * Circe, Argonaut, LiftJson, Bson, Protobuff
     * marshall and unmarshall
  * Documentation
     * Swagger Doc & Protofiles
  * DB
     * Basic ORM, DB Schema Gen
  * ReactJS
     * Create ES2018 React Components
  * Http
     * Http4s HttpRoutes
     * Unfiltered ResponseFunction
  * Scalacheck Generators   
  * BYOI
     
----

# DEMO

----

#### <Ctrl-D>

  * Extend functionality using coproduct
  * Relationship to Free Applicative
  * Encapsulation

    





