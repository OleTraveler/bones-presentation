+++
title = "GADTs in Scala"
outputs = ["Reveal"]
+++

## Compile Time Scaffolding in Scala w/ GADTs

* Author: Travis Stevens
* Twitter: @OleTraveler
* Slides: https://oletraveler.github.io/bones-presentation/  (https://bit.ly/2J9O5i1)

---

#### Talk  Outline

* GADT Basics
* HList
* Validation using GADT
* Describing REST endpoints
* Demo
* Protobuf and Other Interpreters
* Final Thoughts

---

#### Objectives

  * Learn about GADTs and Interpreters
    * Utilize this pattern in your application
  * Learn about the Bones project -- I am looking for feedback

---

#### Generalized Algebraic Datatype Definition

  * Few Names
     * GADT
     * Guarded Recursive Data Type
     * First-class Phantom Types
     
---     
     
#### Generalized Algebraic Datatype Definition     
  * Data Structure
     * Algebra
  * Interpreter
     * Transforming the Data Structure into another Data Structure 

---

<details class="notes"><summary>?</summary>
<p>
* phantom type.
* For Optional data we wrap the type from the Value in Option
* For tuple, combine 2 types into the duple.
* Limit our domain to just Ints and String (and combinations of them)
</p>
</details>

GADT - _Generalized_ Algebraic Data Type

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 


---

<details class="notes"><summary>?</summary>
<p>
* Note type type of the end result..
</p>
</details>


Data Structure Examples

```scala
scala> TupleData( StringData,
     |   TupleData(
     |     OptionalData(
     |       TupleData( 
     |         IntData, IntData
     |       ),
     |     ),
     |     OptionalData(IntData)
     |   )
     | )
res0: TupleData[String,(Option[(Int, Int)], Option[Int])] = TupleData(StringData,TupleData(OptionalData(TupleData(IntData,IntData)),OptionalData(IntData)))
```

---

#### Parsing JSON

<details class="notes"><summary>?</summary>
<p>
* Added key to the primitives for demonstration.
</p>
</details>

```scala
sealed abstract class KvpValue[A]

case class StringData(key: String)  extends KvpValue[String]

case class IntData(key: String)  extends KvpValue[Int]

case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C](leftValue: KvpValue[B], rightValue: KvpValue[C]) extends KvpValue[(B,C)]
```
---

<details class="notes"><summary>?</summary>
<p>
* 
</p>
</details>
#### Building our Schema

```scala
scala> val example = 
     |   TupleData( StringData("name"),
     |     TupleData(
     |       OptionalData( 
     |         TupleData( 
     |           IntData("latitude"), IntData("longitude"))),
     |       OptionalData(IntData("height"))
     |     )
     |   )
example: TupleData[String,(Option[(Int, Int)], Option[Int])] = TupleData(StringData(name),TupleData(OptionalData(TupleData(IntData(latitude),IntData(longitude))),OptionalData(IntData(height))))
``` 

---

<details class="notes"><summary>?</summary>
<p>
* TupleData and OptionalData unwrap the members and recursively call createDoc and then add some metadata
* String and Int data print the key and type.
</p>
</details>

#### First Interpreter: Print the type
```scala

object DocInterpreter {

 def createDoc[A](op: KvpValue[A]): String = {
   op match {
     case TupleData(b,c) => s"${createDoc(b)} combined with ${createDoc(c)})"
     case OptionalData(b) => s"${createDoc(b)} which is optional"
     case StringData(key) => s"a String with key ${key}"
     case IntData(key) => s"an Int with key ${key}"
   }
 } 
}
```

```scala
scala> DocInterpreter.createDoc(example)
res0: String = a String with key name combined with an Int with key latitude combined with an Int with key longitude) which is optional combined with an Int with key height which is optional))
```

---

<details class="notes"><summary>?</summary>
<p>
* Tuple data 
  * During interpretation is recursively calling marshall to get the A => Json function of it's members.
  * For runtime, it will execute those functions and combine the result.
* Option data
  * Is recursively calling marshall during interpretation.
  * For runtime, checks the option, for None => return empty object, 
   for some unwrap the item from the some and call the function corresponding to that value.
* Int and String primitives 
  * don't do anything for interpretation step execpt return function
  * create an object with the value passed as the value and the key as the json name
</p>
</details>

#### Marshall Interpreter
```scala
import argonaut._
object ArgonautMarshall {

  def marshall[A](op: KvpValue[A]): A => Json = {
    op match {
      case TupleData(l,r) => {
        val fLeft = marshall(l)
        val fRight = marshall(r)
        (tuple: A) => {
          combine( fLeft(tuple._1), fRight(tuple._2))
        }
      }

      case OptionalData(aKvpValue) => {
        val fOptional = marshall(aKvpValue)
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
```scala

val waterfallSchema = 
  TupleData( StringData("name"),
    TupleData(
      OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
      OptionalData(IntData("height"))
  ))

val dryFalls = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
```

#### Create Function and Pass Data
```scala
scala> val waterfallToJson = ArgonautMarshall.marshall(waterfallSchema)
waterfallToJson: ((String, (Option[(Int, Int)], Option[Int]))) => argonaut.Json = ArgonautMarshall$$$Lambda$12717/1772851426@51c780b3

scala> val waterfallJson = waterfallToJson(dryFalls)
waterfallJson: argonaut.Json = {"name":"Dry Falls","latitude":35,"longitude":-83,"height":80}
```

---

<details class="notes"><summary>?</summary>
<p>
</p>
</details>

#### What is waterfallToJson?
```scala
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

Output
```scala
scala>   waterfallFLiteral.apply(dryFalls)
res1: argonaut.Json = {"name":"Dry Falls","lattitude":35,"longitude":-83,"age":80}
```

---


<details class="notes"><summary>?</summary>
 <p>
* 
* Either is required in case the input Json doesn't conform to our specification.
* For the marshall example, we didn't need Either because the compile enforsed the our type conformed to the schema.
</p> 
</details>

#### Unmarshall Example

```scala
import argonaut.Json.JsonAssoc
object ArgonautUnmarshall {
      def unmarshall[A](op: KvpValue[A]) : Json => Either[String, A] = {
        op match {
          case TupleData(leftOp, rightOp) =>
            val leftF = unmarshall(leftOp)             // recurse left type
            val rightF = unmarshall(rightOp)           // recurse right type
            json => {
              val left = leftF(json)  
              val right = rightF(json)
              combineTuple(left,right)
            }
          case op: OptionalData[b] =>
            val valueB = unmarshall(op.optionalKvpValue) // recurse member type
            json => {
              valueB(json) match {
                case Left(_) => Right(None)
                case Right(x) => Right(Some(x))
              }
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
```scala
scala> ArgonautUnmarshall.unmarshall(waterfallSchema)(waterfallJson)
res2: Either[String,(String, (Option[(Int, Int)], Option[Int]))] = Right((Dry Falls,(Some((35,-83)),Some(80))))
```

---

#### 2 Steps: Interpret, Run
```scala
          case op: OptionalData[b] =>

            // This Code is evaluated before returning the function
            // and is therefor only executed once per schema begin interpreted
            val valueB = unmarshall(op.optionalKvpValue)

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

#### Do Not Do This

<details><summary>?</summary>
<p>
By moving the input type a up in the code, we skip the interpreter step and 
the match would happen at runtime.
</p>
</details>

```scala
  def marshall[A](op: KvpValue[A]): A => Json = a => {
    op match {
      case StringData(key) => Json.obj( (key, Json.jString(a)) )

      case IntData(key) => Json.obj( (key, Json.jNumber(a)) )

      case OptionalData(aKvpValue) => {
        val fOptional = marshall(aKvpValue)
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

#### Final notes on GADTs

---

<details class="notes"><summary>?</summary>
* Shapeless will replace tuples and gives us case classes for free
* During our refactor to HList, we will address the key issue.
</details>

### Improvements to our algebra

* Key on the primitive doesn't allow for hierarchical data
* Tuples are clunky
* Hierarchical case classes
```scala
case class Location(latitude: Int, longitude: Int)
case class Waterfall(name: String, location: Option[Location], height: Option[Int])
```


---

<details class="notes"><summary>?</summary>
<p>

</p>
</details>

### Shapeless HList - Quick Overview

The heterogeneous list

```scala
import shapeless.ops.hlist.{IsHCons, Length, Prepend, Split}
import shapeless.{::, Generic, HList, HNil, Nat, Succ}
```


removes nesting
```scala
scala> val waterfallTuple = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
waterfallTuple: (String, (Some[(Int, Int)], Some[Int])) = (Dry Falls,(Some((35,-83)),Some(80)))

scala> val waterfallHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
waterfallHList: String :: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: Some(80) :: HNil
```

---

Can arbitrarily split an HList
```scala
scala> val waterfallHlist = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
waterfallHlist: String :: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: Some(80) :: HNil

scala> waterfallHlist.head
res0: String = Dry Falls

scala> waterfallHlist.tail
res1: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Some(35 :: -83 :: HNil) :: Some(80) :: HNil

scala> val split = Split[String::Option[Int::Int::HNil]::Option[Int]::HNil, Nat._2]
split: shapeless.ops.hlist.Split[String :: Option[Int :: Int :: shapeless.HNil] :: Option[Int] :: shapeless.HNil,shapeless.Succ[shapeless.Succ[shapeless._0]]]{type Prefix = String :: Option[Int :: Int :: shapeless.HNil] :: shapeless.HNil; type Suffix = Option[Int] :: shapeless.HNil} = shapeless.ops.hlist$Split$$anon$78@6e93523f

scala> split(waterfallHlist)
res2: split.Out = (Dry Falls :: Some(35 :: -83 :: HNil) :: HNil,Some(80) :: HNil)
```

---

Can prepend HLists of arbitrary size
```scala
scala> val prefix = "Dry Falls" :: Some( 35 :: -83 :: HNil) :: HNil
prefix: String :: Some[Int :: Int :: shapeless.HNil] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: HNil

scala> val suffix = Some(80) :: HNil
suffix: Some[Int] :: shapeless.HNil = Some(80) :: HNil

scala> prefix ::: suffix
res3: String :: Some[Int :: Int :: shapeless.HNil] :: Some[Int] :: shapeless.HNil = Dry Falls :: Some(35 :: -83 :: HNil) :: Some(80) :: HNil
``` 

---

Magic conversion to/from case classes
```scala
  case class Location(latitude: Int, longitude: Int)
  case class Waterfall(name: String, location: Option[Location], height: Option[Int])

  val genLocation = Generic[Location]
  val genWaterfall = Generic[Waterfall]

  val dryFallsHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
  val dryFallsLocation: String :: Option[Location] :: Option[Int] :: HNil =
    dryFallsHList.head :: dryFallsHList.tail.head.map(genLocation.from) :: dryFallsHList.tail.tail.head :: dryFallsHList.tail.tail.tail
```

```scala
scala>    val waterfall = genWaterfall.from(dryFallsLocation)
waterfall: Waterfall = Waterfall(Dry Falls,Some(Location(35,-83)),Some(80))

scala>    val waterfallHlist = genWaterfall.to(waterfall)
waterfallHlist: genWaterfall.Repr = Dry Falls :: Some(Location(35,-83)) :: Some(80) :: HNil
```

---

#### Refactor KvpValue

<details class="notes"><summary>?</summary>
<p>
* removed key from StringData and IntData
* Removed TupleData
</p>
</details>

* Split GADT into two algebras
  * KvpValue
  * KvpHList
     * Head of list will have a key/value class: `case class KeyValueDefinition[A](key: String, op: KvpValue[A])`
     * Mirrors HList functionality for prepend
* Add a KvpConvertData to the KvpValue algebra
  * Used to signify conversion to/from HList
  * Bubble up the case class as the type.
* Two interpreters which recursively call each other for hierarchical data


---


#### Refactored KvpValue

```scala
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]]

case class KvpHListData[H <: HList, N<:Nat](kvpHList: KvpHList[H, N]) extends KvpValue[H]

case class KvpConvertData[H<:HList, N<:Nat, A](kvpHList: KvpHList[H,N], fha: H => A, fah: A => H) extends KvpValue[A]
```

```scala
case class KeyValueDefinition[A](key: String, op: KvpValue[A])
```

---

#### New KvpHList

```scala
sealed abstract class KvpHList[H <: HList, N <: Nat] {
  def ::[A](v: KeyValueDefinition[A])(implicit iCons: IsHCons.Aux[A::H, A, H]): KvpSingleValueHead[A, H, N, A :: H]
}

object KvpNil extends KvpHList[HNil, Nat._0] {
def ::[A](v: KeyValueDefinition[A])(implicit isHCons: IsHCons.Aux[A::HNil, A, HNil]): KvpSingleValueHead[A, HNil, Nat._0, A :: HNil] =
  KvpSingleValueHead[A, HNil, Nat._0, A :: HNil](v, KvpNil, isHCons)
}

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H]
(
  fieldDefinition: KeyValueDefinition[A],
  tail: KvpHList[H, N],
  isHCons: IsHCons.Aux[OUT, A, H]
) extends KvpHList[OUT, Succ[N]] {
def ::[A](v: KeyValueDefinition[A])(implicit isHCons: IsHCons.Aux[A::OUT, A, OUT])
  : KvpSingleValueHead[A, OUT, Succ[N], A :: OUT] =
     KvpSingleValueHead[A, OUT, Succ[N], A :: OUT](v, this, isHCons)
}

case class KvpHListHead[HH <: HList, HN <:Nat, HT<:HList, NT <:Nat, HO<:HList, NO<:Nat](
  head: KvpHList[HH, HN],
  tail: KvpHList[HT, NT],
  prepend: Prepend.Aux[HH, HT, HO],
  split: Split.Aux[HO, HN, HH, HT], // analogous: Split.Aux[prepend.OUT,HL,H,T] with lpLength: Length.Aux[H,HL],
) extends KvpHList[HO, NO] {
def ::[A](v: KeyValueDefinition[A])(implicit isHCons: IsHCons.Aux[A::HO, A, HO]):
  KvpSingleValueHead[A, HO, NO, A :: HO] =
  KvpSingleValueHead[A, HO, NO, A :: HO](v, this, isHCons)
}
```


---

### Two different GADT
```scala
object ArgonautMarshall {
   type Key = String
   def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = ???
   def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = ???
}
```


---

#### Waterfall Example

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
waterfallSchema: slides.HListSlides.KvpConvertData[slides.HListSlides.genericWaterfall.Repr,shapeless.Succ[shapeless.Succ[shapeless.Succ[shapeless.Nat._0]]],slides.HListSlides.Waterfall] = KvpConvertData(KvpSingleValueHead(KeyValueDefinition(name,StringData),KvpSingleValueHead(KeyValueDefinition(location,OptionalData(KvpConvertData(KvpSingleValueHead(KeyValueDefinition(latitude,IntData),KvpSingleValueHead(KeyValueDefinition(longitude,IntData),slides.HListSlides$KvpNil$@6b02143f,shapeless.ops.hlist$IsHCons$$anon$156@49c3c2ef),shapeless.ops.hlist$IsHCons$$anon$156@4579ce08),slides.HListSlides$$$Lambda$12808/1280023826@9f90f6a,slides.HListSlides$$$Lambda$12809/1953960451@72215186))),KvpSingleValueHead(KeyValueDefinition(height,OptionalData(IntData)),slides.HListSl...
```


---
#### Final Thoughts on KvpHList
  * There is a DSL to clean up usage
  
---


## Validation

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

# Validation Rules

---

# Validation Using GADT

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
        val kvpF = unmarshall(kvp.fieldDefinition.op)
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

### Final Thoughts on Validation



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
     * What to use as an ID
     * Roles
     * Extract data for a search
     * Encoding Routes
     
---





```scala

  type Key = String
  case class Create[I,E,O](in: KvpValue[I], err: KvpValue[E], out: KvpValue[O])
  def marshall[A](op: KvpValue[A]): A => Array[Byte] = ???
  def unmarshall[A](op: KvpValue[A]): Array[Byte] => Either[String,A] = ???

  def post[CI, CE, CO](c: Create[CI,CE,CO],
                       path: String): (CI => IO[Either[CE, CO]]) => HttpRoutes[IO] = { createF =>

    val inF = unmarshall(c.in)
    val outF = marshall(c.out)
    val errF = marshall(c.err)


    HttpRoutes.of[IO] {
      case req@Method.POST -> Root / path => {
        val result: EitherT[IO, IO[Response[IO]], IO[Response[IO]]] = for {
          body <- EitherT[IO, IO[Response[IO]], Array[Byte]] {
            req.as[Array[Byte]].map(Right(_))
          }
          in <- EitherT.fromEither[IO] {
            inF(body).left.map(x => BadRequest())       // <---- input conversion to CI
          }
          out <- EitherT[IO, IO[Response[IO]], CO] {
            createF(in)                                           // <---- business logic
              .map(_.left.map(ce => {
              val out = errF(ce)                    // <----- error case output conversion from CE
              InternalServerError(out,
                Header("Content-Type", "text/json"))
            }))
          }
        } yield {
          Ok(outF(out), Header("Content-Type", "text/json")) // <----- output conversion from CO
        }
        result.value.flatMap(_.merge)
      }
    }
  }

```


---

#### Collection of interpreters

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
  * BYOI
     
----

# DEMO


----


#### Protobuf


  * Byte Array & Mutable Pointer
  * Protobuf File


----


#### Final Thoughts

  * Extend functionality using coproduct
  * Relationship to Free Applicative
  * Encapsulation

    





