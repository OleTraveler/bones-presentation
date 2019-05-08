+++
title = "GADTs in Scala"
outputs = ["Reveal"]
+++

## Compile Time Scaffolding in Scala

* Author: Travis Stevens
* Twitter: @OleTraveler
* Slides: https://oletraveler.github.io/bones-presentation/

---

#### Talk  Outline

* GADT Basics
* HList
* Validation using GADT
* Protouf
* Describing REST endpoints
* Demo
* Final Thoughts

---

#### Objectives

  * Learn about the Bones project -- I am looking for feedback.
  * Learn about GADTs and Interpreters
    * Utilize this pattern in your application.
  * 

---

<details class="notes"><summary>?</summary>
<p>
* ADT aka Sum Type aka Subtyping
* Note sealed!
</p>
</details>

ADT - Algebraic Data Type

```tut:silent
sealed abstract class KvpValue

case object StringData extends KvpValue

case object IntData extends KvpValue

case class OptionalData(optionalValue: KvpValue) extends KvpValue

case class TupleData(leftValue: KvpValue, rightValue: KvpValue) extends KvpValue
```

---

<details class="notes"><summary>?</summary>
<p>
* Add a phantom type.
* For Optional data we wrap the type from the Value in Option
* For tuple, combine 2 types into the duple.
* Limit our domain to just Ints and String (and combinations of them)
</p>
</details>

GADT - _Generalized_ Algebraic Data Type

```tut:silent:reset
sealed abstract class KvpValue[A]

case object StringData extends KvpValue[String]

case object IntData extends KvpValue[Int]

case class OptionalData[B](b: KvpValue[B]) extends KvpValue[Option[B]]

case class TupleData[B,C]( b: KvpValue[B], c: KvpValue[C]) extends KvpValue[(B,C)]
``` 


---

<details class="notes"><summary>?</summary>
<p>
* Note that the outer GADT keeps track of the entire type.
</p>
</details>


Data Structure Examples

```tut
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

#### Parsing JSON

<details class="notes"><summary>?</summary>
<p>
* Added key to the primitives for demonstration.
</p>
</details>

```tut:silent:reset
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

```tut
val example = TupleData( StringData("name"),
                TupleData(
                  OptionalData( TupleData( IntData("latitude"), IntData("longitude") )),
                  OptionalData(IntData("height"))
              ))

``` 

---

<details class="notes"><summary>?</summary>
<p>
* TupleData and OptionalData unwrap the members and recursively call createDoc and then add some metadata
* String and Int data print the key and type.
</p>
</details>

#### First Interpreter: Print the type
```tut:silent

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

```tut
DocInterpreter.createDoc(example)
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
```tut:silent
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

<details class="notes"><summary>?</summary>
<p>
</p>
</details>

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

Output
```tut
  waterfallFLiteral.apply(dryFalls)
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

```tut:silent
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
```tut
ArgonautUnmarshall.unmarshall(waterfallSchema)(waterfallJson)
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

```tut:silent
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

### new Features/improvements

* Key on the pimitive doesn't allow for hierarchical data
* Tuples are clunky
* Hierarchical case classes
```tut:silent
case class Location(latitude: Int, longitude: Int)
case class Waterfall(name: String, location: Option[Location], height: Option[Int])
```


---

<details class="notes"><summary>?</summary>
<p>

</p>
</details>

### Shapeless HList - Quick Overview

The heterogenius list

```tut:silent:reset
import shapeless.ops.hlist.{IsHCons, Length, Prepend, Split}
import shapeless.{::, Generic, HList, HNil, Nat, Succ}
```


will allow us to flatten the tuple.
```tut
val waterfallTuple = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
val waterfallHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
```

---

Can arbitrarily split an HList
```tut
val waterfallHlist = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
waterfallHlist.head
waterfallHlist.tail
val split = Split[String::Option[Int::Int::HNil]::Option[Int]::HNil, Nat._2]
split(waterfallHlist)
```

---

Can prepend HLists of arbitrary size
```tut
val prefix = "Dry Falls" :: Some( 35 :: -83 :: HNil) :: HNil
val suffix = Some(80) :: HNil
prefix ::: suffix
``` 

---

Magic conversion to/from case classes
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

```tut:invisible
import slides.HListSlides._
```

```tut
  val waterfallSchema = KvpConvertData(waterfallHlistSchema, genericWaterfall.from, genericWaterfall.to)


```


---



#### Final Thoughts on KvpHList
  * There is a DSL to clean up usage

---

# Validation

[GV](https://dreampuf.github.io/GraphvizOnline/#%0Adigraph%20G%20%7B%0A%0A%20%20subgraph%20cluster_0%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Is%20String%22-%3E%20%22Max%2030%22%3B%0A%20%20%20%20%22Is%20String%22%20-%3E%20%22Words%20Only%22%3B%0A%20%20%20%20label%20%3D%20%22Name%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_1%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Lat%20Is%20Number%22%20-%3E%20%22Lat%3A%20-90..90%22%3B%0A%20%20%20%20label%20%3D%20%22Latitude%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_2%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Lon%20Is%20Number%22%20-%3E%20%22Lon%3A%20-90..90%22%3B%0A%20%20%20%20label%20%3D%20%22Longitude%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_3%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Height%20Is%20Number%22%20-%3E%20%22Greater%20than%200%22%3B%0A%20%20%20%20%22Height%20Is%20Number%22%20-%3E%20%22Less%20than%203%2C212%20ft%22%3B%0A%20%20%20%20label%20%3D%20%22Card%20Number%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_4%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Lat%3A%20-90..90%22%20-%3E%20%22Is%20in%20WNC%22%3B%0A%20%20%20%20%22Lon%3A%20-90..90%22%20-%3E%20%22Is%20in%20WNC%22%3B%0A%20%20%7D%0A%20%20%0A%20%20subgraph%20cluster_5%20%7B%0A%20%20%20%20style%3Dfilled%3B%0A%20%20%20%20color%3Dlightgrey%3B%0A%20%20%20%20node%20%5Bstyle%3Dfilled%2Ccolor%3Dwhite%5D%3B%0A%20%20%20%20%22Max%2030%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Words%20Only%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Is%20in%20WNC%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Greater%20than%200%22%20-%3E%20%22Waterfall%22%3B%0A%20%20%20%20%22Less%20than%203%2C212%20ft%22%20-%3E%20%22Waterfall%22%0A%20%20%7D%0A%20%20%0A%20%20%0A%20%20%0A%20%20%0A%20%20JSON%20-%3E%20%22Is%20String%22%3B%0A%20%20JSON%20-%3E%20%22Lat%20Is%20Number%22%3B%0A%20%20JSON%20-%3E%20%22Lon%20Is%20Number%22%3B%0A%20%20JSON%20-%3E%20%22Height%20Is%20Number%22%3B%0A%0A%20%20JSON%20%5Bshape%3DMdiamond%5D%3B%0A%7D)

![waterfall](/waterfall-validation.png "Logo Title Text 1")

---

# Validation Rules
  * Short Circuit
     * Changing datatypes
     * Combining datatypes (hierarchical data)
  * Accumulate
     * At each KVP Value
     * Each input until combining   

---

# Validation Using GADT

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





