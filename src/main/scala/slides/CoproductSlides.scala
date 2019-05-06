//package slides
//
//import argonaut.Json
//import cats.free.FreeApplicative.lift
//import shapeless.{::, HList, HNil, Nat, Succ}
//import shapeless.ops.hlist.{Prepend, Split}
//import iota._
//import TList.{:: => TCONS}
//import TListK.{::: => TCONSK}
//
//class CoproductSlides {
//
//  sealed abstract class KvpValue[A]
//
//  case object StringData extends KvpValue[String]
//
//  case object IntData extends KvpValue[Int]
//
//  case class OptionalData[B](optionalKvpValue: KvpValue[B]) extends KvpValue[Option[B]]
//
//  case class KvpHListData[H <: HList, N<:Nat](kvpHList: KvpHList[H, N]) extends KvpValue[H]
//
//  case class KvpConvertData[H<:HList, N<:Nat, A](kvpHList: KvpHList[H,N], fha: H => A, fah: A => H) extends KvpValue[A]
//
//  sealed abstract class MyKvpValue[A]
//
//  case object BooleanData extends MyKvpValue[Boolean]
//
//  case object Markdown extends MyKvpValue[String]
//
//  type Bar[A] = CopK[KvpValue TCONSK MyKvpValue TCONSK TNilK, A]
//
//  case class KeyValueDefinition[F[_],A](key: String, op: F[A])
//
//  sealed abstract class KvpHList[H <: HList, N <: Nat] {
//    def ::[F[_],A](v: KeyValueDefinition[F,A]): KvpSingleValueHead[F, A, H, N, A :: H]
//  }
//
//  object KvpNil extends KvpHList[HNil, Nat._0] {
//    def ::[F[_],A](v: KeyValueDefinition[F,A]): KvpSingleValueHead[F, A, HNil, Nat._0, A :: HNil] =
//      KvpSingleValueHead[F, A, HNil, Nat._0, A :: HNil](v, KvpNil)
//  }
//
//  case class KvpSingleValueHead[F[_], A, H <: HList, N <: Nat, OUT <: A :: H]
//  (
//    fieldDefinition: KeyValueDefinition[F,A],
//    tail: KvpHList[H, N]
//  ) extends KvpHList[OUT, Succ[N]] {
//    def ::[F2[_], A](v: KeyValueDefinition[F2,A])
//    : KvpSingleValueHead[F2, A, OUT, Succ[N], A :: OUT] =
//      KvpSingleValueHead[F2, A, OUT, Succ[N], A :: OUT](v, this)
//  }
//
//  case class KvpHListHead[HH <: HList, HN <:Nat, HT<:HList, NT <:Nat, HO<:HList, NO<:Nat](
//                                                                                           head: KvpHList[HH, HN],
//                                                                                           tail: KvpHList[HT, NT],
//                                                                                           prepend: Prepend.Aux[HH, HT, HO],
//                                                                                           split: Split.Aux[HO, HN, HH, HT], // analogous: Split.Aux[prepend.OUT,HL,H,T] with lpLength: Length.Aux[H,HL],
//                                                                                         ) extends KvpHList[HO, NO] {
//    def ::[F[_],A](v: KeyValueDefinition[F,A]) = ???
//  }
//
//
//
//  type Key = String
//  object ArgonautMarshall {
//
//    def marshallKvpHList[H<:HList,N<:Nat](kvpHList: KvpHList[H,N]): H => Json = {
//      kvpHList match {
//        case KvpNil => (nil: H) => Json.jEmptyObject
//
//        case KvpSingleValueHead(fieldDefinition, tail) => {
//          val kvpValueF = marshallKvpValue(fieldDefinition.op)
//          val kvpHListF = marshallKvpHList(tail)
//          (h: H) => {
//            val head = h.head
//            val tail = h.tail
//            val headResult = kvpValueF(fieldDefinition.key, head)
//            val tailResult = kvpHListF(tail)
//            combine(headResult, tailResult)
//          }
//        }
//      }
//    }
//
//    def marshallKvpValue[A](op: KvpValue[A]): (Key, A) => Json = {
//      op match {
//        case StringData =>
//          (key: Key, str: String) => Json.obj((key, Json.jString(str)))
//        case IntData =>
//          (key: Key, i: Int) => Json.obj((key, Json.jNumber(i)))
//        case OptionalData(aValueOp) => {
//          val fOptional = marshallKvpValue(aValueOp)
//          (key: String, opt: A) =>
//          {
//            opt match {
//              case None    => Json.jNull
//              case Some(a) => fOptional(key, a)
//            }
//          }
//        }
//        case op: KvpHListData[h,n] => {
//          val kvpHListF = marshallKvpHList(op.kvpHList)
//          (key: String, hList: A) => {
//            val kvpHListValue: Json = kvpHListF(hList.asInstanceOf[h])
//            Json.obj( (key, kvpHListValue) )
//          }
//        }
//      }
//
//    }
//
//    def combine(prefix: Json, postfix: Json): Json = {
//      val values1 = prefix.obj.toList.flatMap(_.toList)
//      val values2 = postfix.obj.toList.flatMap(_.toList)
//      Json.obj(values1 ::: values2: _*)
//    }
//
//  }
//
//}
