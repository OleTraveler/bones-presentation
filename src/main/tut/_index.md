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
import shapeless.ops.hlist.{Length, Prepend, Split}
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
val waterfallHlist = "Eugene" :: 12 :: Some(12) :: 5 :: HNil
waterfallHlist.head
waterfallHlist.tail
val split = Split[String::Int::Option[Int]::Int::HNil, Nat._2]
split(waterfallHlist)
```

---

Can prepend HList to HList
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

#### HList

  * types to use in a schema 
  * values to feed a functions
  * Mirror HList as a GADT
  * Split GADT base trait
    * KvpValue
    * KvpHList

---

#### Refactor KvpValue

<details class="notes"><summary>?</summary>
<p>
* removed key from StringData and IntData
* Removed TupleData
</p>
</details>

```tut:silent
sealed abstract class KvpValue[A]

case object StringData  extends KvpValue[String]

case object IntData  extends KvpValue[Int]

case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]]
```


---

<details class="notes"><summary>?</summary>
<p>
Need N <: Nat for prepend HList which will not be demonstrated.
</p>
</details>

#### Base Trait and HNil

```scala
sealed abstract class KvpHList[H <: HList, N <: Nat]
object KvpNil extends KvpHList[HNil, Nat._0]
```

---

### Prepend a Value


<details class="notes"><summary>?</summary>
<p>
* KvpSingleValueHead is a recursive type.
</p>
</details>


```tut:silent
case class KeyValueDefinition[A](key: String, op: KvpValue[A])
```

Define KvpSingleValueHead
```scala
sealed abstract class KvpHList[H <: HList, N <: Nat]

object KvpNil extends KvpHList[HNil, Nat._0]

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H](
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N]
) extends KvpHList[OUT, Succ[N]]
```

---

<details><summary>?</summary>
<p>
* Most dense slide.
* :: is short for "Prepend On Value"
* <: Lower bound
* H :: HNil prepend a the type level.
</p>
</details>
#### Implement :: for KvpNil
```tut:silent
sealed abstract class KvpHList[H <: HList, N <: Nat] 

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H](
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N]
) extends KvpHList[OUT, Succ[N]] 


object KvpNil extends KvpHList[HNil, Nat._0] {
  def ::[A](v: KeyValueDefinition[A]) : KvpSingleValueHead[A, HNil, Nat._0, A :: HNil] =
      KvpSingleValueHead[A, HNil, Nat._0, A :: HNil](v, KvpNil)
}
```

---

#### Implement :: for KvpSingleValueHead
```tut:silent
sealed abstract class KvpHList[H <: HList, N <: Nat] 

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H](
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N]
) extends KvpHList[OUT, Succ[N]] {
  def ::[A](v: KeyValueDefinition[A])
    : KvpSingleValueHead[A, OUT, Succ[N], A :: OUT] =
    KvpSingleValueHead[A, OUT, Succ[N], A :: OUT](v, this)  
}

object KvpNil extends KvpHList[HNil, Nat._0]

```

---

```tut:silent
sealed abstract class KvpHList[H <: HList, N <: Nat]

case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H](
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N]
) extends KvpHList[OUT, Succ[N]] {
  def ::[A](v: KeyValueDefinition[A])
    : KvpSingleValueHead[A, OUT, Succ[N], A :: OUT] =
    KvpSingleValueHead[A, OUT, Succ[N], A :: OUT](v, this)
}
object KvpNil extends KvpHList[HNil, Nat._0] {
  def ::[A](v: KeyValueDefinition[A]) : KvpSingleValueHead[A, HNil, Nat._0, A :: HNil] =
      KvpSingleValueHead[A, HNil, Nat._0, A :: HNil](v, KvpNil)
}

```

---

#### Nested JSON
```tut:silent
case class KvpHListData[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]) extends KvpValue[H]
````

---
```tut:invisible
   import argonaut.Json
    def combine(prefix: Json, postfix: Json): Json = {
      val values1 = prefix.obj.toList.flatMap(_.toList)
      val values2 = postfix.obj.toList.flatMap(_.toList)
      Json.obj(values1 ::: values2: _*)
    }
   type Key = String
```

### Two different GADT
```tut:silent
object ArgonautMarshall {
   type Key = String
   def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = ???
   def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = ???
}
```

---

```tut:invisible
def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = ???
```

#### Kvp HList
```tut:silent
    def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = {
      kvpHList match {
        case KvpNil => (nil: H) => Json.jEmptyObject
          
        case KvpSingleValueHead(fieldDefinition, tail) => {
          val kvpValueF = marshallKvpValue(fieldDefinition.op)
          val kvpHListF = marshallKvpHList(tail)
          (h: H) => {
            val head = h.head
            val tail = h.tail
            val headResult = kvpValueF(fieldDefinition.key, head)
            val tailResult = kvpHListF(tail)
            combine(headResult, tailResult)
          }
        }
      }
    }
```


---

#### Kvp Value
```tut:silent
    def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = {
      op match {
        case StringData =>
          (key: Key, str: String) => Json.obj((key, Json.jString(str)))
        case IntData =>
          (key: Key, i: Int) => Json.obj((key, Json.jNumber(i)))
        case OptionalData(aValueOp) => {
          val fOptional = marshallKvpValue(aValueOp)
          (key: String, opt: A) =>
          {
            opt match {
              case None    => Json.jNull
              case Some(a) => fOptional(key, a)
            }
          }
        }
        case op: KvpHListData[h,n] => {
          val kvpHListF = marshallKvpHList(op.kvpHList)
          (key: String, hList: A) => {
            val kvpHListValue: Json = kvpHListF(hList.asInstanceOf[h])
            Json.obj( (key, kvpHListValue) )
          }
        }
      }

    }
```

---

### Usage

```tut:invisible
  object ArgonautMarshall {

    def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = {
      kvpHList match {
        case KvpNil => (nil: H) => Json.jEmptyObject

        case KvpSingleValueHead(fieldDefinition, tail) => {
          val kvpValueF = marshallKvpValue(fieldDefinition.op)
          val kvpHListF = marshallKvpHList(tail)
          (h: H) => {
            val head = h.head
            val tail = h.tail
            val headResult = kvpValueF(fieldDefinition.key, head)
            val tailResult = kvpHListF(tail)
            combine(headResult, tailResult)
          }
        }
      }
    }

    def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = {
      op match {
        case StringData =>
          (key: Key, str: String) => Json.obj((key, Json.jString(str)))
        case IntData =>
          (key: Key, i: Int) => Json.obj((key, Json.jNumber(i)))
        case OptionalData(aValueOp) => {
          val fOptional = marshallKvpValue(aValueOp)
          (key: String, opt: A) =>
          {
            opt match {
              case None    => Json.jNull
              case Some(a) => fOptional(key, a)
            }
          }
        }
        case op: KvpHListData[h,n] => {
          val kvpHListF = marshallKvpHList(op.kvpHList)
          (key: String, hList: A) => {
            val kvpHListValue: Json = kvpHListF(hList.asInstanceOf[h])
            Json.obj( (key, kvpHListValue) )
          }
        }
      }

    }

    def combine(prefix: Json, postfix: Json): Json = {
      val values1 = prefix.obj.toList.flatMap(_.toList)
      val values2 = postfix.obj.toList.flatMap(_.toList)
      Json.obj(values1 ::: values2: _*)
    }

  }
```

```tut:silent
val locationSchema = 
   KeyValueDefinition("latitude", IntData) :: KeyValueDefinition("longitude", IntData) :: KvpNil

val waterfallSchema = KeyValueDefinition("name", StringData) :: KeyValueDefinition("location", OptionalData(KvpHListData(locationSchema))) :: KeyValueDefinition("height", OptionalData(IntData)) :: KvpNil

val toJsonF = ArgonautMarshall.marshallKvpHList(waterfallSchema)

val dryFallsHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
toJsonF(dryFallsHList)

```

---
<details class="notes"><summary>?</summary>
<p>
fha and fah are derived from Generic[A]
</p>
</details>
#### fha and fah are derived from Generic[A]
```tut:silent
case class KvpConvertData[H<:HList, N<:Nat, A](kvpHList: KvpHList[H,N], fha: H => A, fah: A => H) extends KvpValue[A]
```
---

#### KvpHListHead
Allows us to define *:::*
```tut:silent
  case class KvpHListHead[HH <: HList, HN <:Nat, HT<:HList, NT <:Nat, HO<:HList, NO<:Nat](
    head: KvpHList[HH, HN],
    tail: KvpHList[HT, NT],
    prepend: Prepend.Aux[HH, HT, HO],
    split: Split.Aux[HO, HN, HH, HT], // analogous: Split.Aux[prepend.OUT,HL,H,T] with lpLength: Length.Aux[H,HL],
  ) extends KvpHList[HO, NO] {
    def ::[A](v: KeyValueDefinition[A]) = ???
  }
```

---



#### Final Thoughts on KvpHList
  * Unmarshall implementation
  * There is a DSL to clean up usage

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

sealed abstract class KvpValue[A]
type Value[A] = FreeApplicative[KvpValue, A]

case object StringData extends KvpValue[String]
case object IntData extends KvpValue[Int]
case class Tuple[B,C](b: Value[B], c: Value[C]) extends KvpValue[(B,C)]
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




