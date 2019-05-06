package slides

import argonaut.Json
import shapeless.ops.hlist.{Length, Prepend, Split}
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
    def ::[A](v: KeyValueDefinition[A]): KvpSingleValueHead[A, H, N, A :: H]
  }

  object KvpNil extends KvpHList[HNil, Nat._0] {
    def ::[A](v: KeyValueDefinition[A]): KvpSingleValueHead[A, HNil, Nat._0, A :: HNil] =
      KvpSingleValueHead[A, HNil, Nat._0, A :: HNil](v, KvpNil)
  }

  case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H]
  (
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N]
  ) extends KvpHList[OUT, Succ[N]] {
    def ::[A](v: KeyValueDefinition[A])
    : KvpSingleValueHead[A, OUT, Succ[N], A :: OUT] =
      KvpSingleValueHead[A, OUT, Succ[N], A :: OUT](v, this)
  }

  case class KvpHListHead[HH <: HList, HN <:Nat, HT<:HList, NT <:Nat, HO<:HList, NO<:Nat](
    head: KvpHList[HH, HN],
    tail: KvpHList[HT, NT],
    prepend: Prepend.Aux[HH, HT, HO],
    split: Split.Aux[HO, HN, HH, HT], // analogous: Split.Aux[prepend.OUT,HL,H,T] with lpLength: Length.Aux[H,HL],
  ) extends KvpHList[HO, NO] {
    def ::[A](v: KeyValueDefinition[A]) = ???
  }



  type Key = String
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


}
