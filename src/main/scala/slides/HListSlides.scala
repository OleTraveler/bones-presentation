package slides

import argonaut.Json
import shapeless.ops.hlist.{IsHCons, Length, Prepend, Split}
import shapeless.{::, Generic, HList, HNil, Nat, Succ}

object HListSlides {

  sealed abstract class KvpValue[A]

  case object StringData extends KvpValue[String]

  case object IntData extends KvpValue[Int]

  case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]]

  case class KvpHListData[H <: HList, N<:Nat](kvpHList: KvpHList[H, N]) extends KvpValue[H]

  case class KvpConvertData[H<:HList, N<:Nat, A](kvpHList: KvpHList[H,N], fha: H => A, fah: A => H) extends KvpValue[A]


  case class KeyValueDefinition[A](key: String, op: KvpValue[A])

  sealed abstract class KvpHList[H <: HList, N <: Nat] {
//    def ::[A](v: KeyValueDefinition[A])(implicit iCons: IsHCons.Aux[A::H, A, H]): KvpSingleValueHead[A, H, N, A :: H]
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
      KvpHList[A :: HO, Succ[HN]] = ???

    def :::[HO <: HList, NO <: Nat, HP <: HList, NP <: Nat](kvp: KvpHList[HP, NP])(
      implicit prepend: Prepend.Aux[HP, HH, HO],
      lengthP: Length.Aux[HP, NP],
      length: Length.Aux[HO, NO],
      split: Split.Aux[HO, NP, HP, HH]
    ): KvpHList[HO, NO] = ???
  }





  type Key = String
  object ArgonautMarshall {

    def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = {
      kvpHList match {
        case KvpNil => (nil: H) => Json.jEmptyObject

        case kvp: KvpSingleValueHead[a,h,n,H] => {
          val kvpValueF = marshallKvpValue(kvp.fieldDefinition.op)
          val kvpHListF = marshallKvpHList(kvp.tail)
          (h: H) => {
            val head = h.head(kvp.isHCons)
            val tail = h.tail(kvp.isHCons)
            val headResult = kvpValueF(kvp.fieldDefinition.key, head)
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
  val waterfallSchema = KvpConvertData(waterfallHlistSchema, genericWaterfall.from, genericWaterfall.to)







}
