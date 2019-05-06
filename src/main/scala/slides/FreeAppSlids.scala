package slides

import argonaut.Json
import cats.arrow.FunctionK
import shapeless.ops.hlist.{IsHCons, Length, Prepend, Split}
import shapeless.{::, Coproduct, HList, HNil, Nat, Succ}
import cats.data.Kleisli
import cats.free.FreeApplicative
import cats.free.FreeApplicative.lift
import cats.implicits._
import shapeless.ops.hlist.IsHCons.Aux

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global


class FreeAppSlids {

  sealed abstract class KvpValue[A] {
    def toFA: KvpValueFA[A]
  }

  case object StringData extends KvpValue[String] {
    val toFA: KvpValueFA[String] = lift(StringData)
  }

  case object IntData extends KvpValue[Int] {
    val toFA: KvpValueFA[Int] = lift(IntData)
  }

  case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]] {
    val toFA: KvpValueFA[Option[B]] = lift[KvpValue, Option[B]](this)
  }

  case class KvpHListData[H <: HList, N<:Nat](kvpHList: KvpHList[H, N]) extends KvpValue[H] {
    val toFA: KvpValueFA[H] = lift[KvpValue, H](this)
  }

  case class KvpConvertData[H<:HList, N<:Nat, A](kvpHList: KvpHList[H,N], fha: H => A, fah: A => H) extends KvpValue[A] {
    val toFA: KvpValueFA[A] = ???
  }

  type KvpValueFA[A] = FreeApplicative[KvpValue, A]

  sealed abstract class MyKvpValue[A]

  case object BooleanData extends MyKvpValue[Boolean] {
    val toFA: MyKvpValueFA[Boolean] = lift(BooleanData)
  }

  case object Markdown extends MyKvpValue[String] {
    val toFA: MyKvpValueFA[String] = lift(Markdown)
  }

  type MyKvpValueFA[A] = FreeApplicative[MyKvpValue,A]


  import cats.data.Tuple2K
  type MyKvpDomain[A] = Tuple2K[KvpValue, MyKvpValue, A]


  case class KeyValueDefinition[F[_],A](key: String, op: F[A])

  sealed abstract class KvpHList[H <: HList, N <: Nat] {
    def ::[F[_],A](v: KeyValueDefinition[F,A])(implicit vIsHCons: IsHCons.Aux[A :: H, A, H]): KvpSingleValueHead[F,A, H, N, A :: H]
  }

  object KvpNil extends KvpHList[HNil, Nat._0] {
    def ::[F[_],A](v: KeyValueDefinition[F,A])(implicit vIsHCons: IsHCons.Aux[A :: HNil, A, HNil]): KvpSingleValueHead[F,A, HNil, Nat._0, A :: HNil] =
      KvpSingleValueHead[F,A, HNil, Nat._0, A :: HNil](v, KvpNil, vIsHCons)
  }

  case class KvpSingleValueHead[F[_], A, H <: HList, N <: Nat, OUT <: A :: H]
  (
    fieldDefinition: KeyValueDefinition[F,A],
    kvpTail: KvpHList[H, N],
    isHCons: IsHCons.Aux[OUT, A, H]
  ) extends KvpHList[OUT, Succ[N]] {
    def ::[F[_],A](v: KeyValueDefinition[F,A])(implicit vIsHCons: IsHCons.Aux[A :: OUT, A, OUT])
    : KvpSingleValueHead[F, A, OUT, Succ[N], A :: OUT] =
      KvpSingleValueHead[F, A, OUT, Succ[N], A :: OUT](v, this, vIsHCons)
  }

  case class KvpHListHead[HH <: HList, HN <:Nat, HT<:HList, NT <:Nat, HO<:HList, NO<:Nat](
                                                                                           head: KvpHList[HH, HN],
                                                                                           tail: KvpHList[HT, NT],
                                                                                           prepend: Prepend.Aux[HH, HT, HO],
                                                                                           split: Split.Aux[HO, HN, HH, HT], // analogous: Split.Aux[prepend.OUT,HL,H,T] with lpLength: Length.Aux[H,HL],
                                                                                         ) extends KvpHList[HO, NO] {
    override def ::[F[_], A](v: KeyValueDefinition[F, A])(implicit vIsHCons: Aux[A :: HO, A, HO]): KvpSingleValueHead[F, A, HO, NO, A :: HO] = ???
  }



  type Key = String
  type MarshallJson[A] = (Key, A) => Json

  trait ArgonautMarshall[F[_]] {

    def marshallPrimitives: FunctionK[F, (Key, ?) => Json]

    def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = {
      kvpHList match {
        case KvpNil => (nil: H) => Json.jEmptyObject

        case kvp: KvpSingleValueHead[F,a,h,n,H] => {
          val kvpValueF = marshallPrimitives(kvp.fieldDefinition.op)
          val kvpHListF = marshallKvpHList(kvp.kvpTail)
          (hList: H) => {
            val head = hList.head(kvp.isHCons)
            val tail = hList.tail(kvp.isHCons)
            val headResult = kvpValueF(kvp.fieldDefinition.key, head)
            val tailResult = kvpHListF(tail)
            combine(headResult, tailResult)
          }
        }
      }
    }

    type MarshallJson[A] = (Key, A) => Json


    def combine(prefix: Json, postfix: Json): Json = {
      val values1 = prefix.obj.toList.flatMap(_.toList)
      val values2 = postfix.obj.toList.flatMap(_.toList)
      Json.obj(values1 ::: values2: _*)
    }

  }


  trait MarshallKvpValue[F[_]] extends FunctionK[KvpValueFA, (Key, ?) => Json]{

      def recurse[A](fa: F[A]): (Key, A) => Json

      def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json

      def apply[A](fa: KvpValue[A]): (Key, A) => Json =
        fa match {
          case StringData =>
            (key: Key, str: A) => Json.obj((key, Json.jString(str)))
          case IntData =>
            (key: Key, i: Int) => Json.obj((key, Json.jNumber(i)))
          case op: OptionalData[b] => {
            val fOptional: (Key, b) => Json = ??? //recurse(op.optionalKvpValue.toFA)
            (key: String, opt: A) =>
            {
              opt match {
                case None    => Json.jNull
                case Some(a) => fOptional(key, a.asInstanceOf[b])
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

}
