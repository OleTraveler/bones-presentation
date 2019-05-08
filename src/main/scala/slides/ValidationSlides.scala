package slides

import argonaut.Json
import cats.data.NonEmptyList
import shapeless.ops.hlist.{IsHCons, Length, Prepend, Split}
import shapeless.{::, Generic, HList, HNil, Nat, Succ}

object ValidationSlides {

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

  def isValid[A](op: ValidationOp[A]): A => Either[String, A] = {
    a => if (op.isValid(a)) Right(a) else Left(op.defaultError(a))
  }
  def doc[A](op: ValidationOp[A]): String = {
    op.description
  }

  abstract class KvpValue[A]

  case class StringData(validationOps: List[ValidationOp[String]]) extends KvpValue[String]

  type Key = String
  def applicativeTraverse[A](list: List[Either[String, A]]): Either[NonEmptyList[String], A] = ???

  def unmarshall[A](kvpValue: KvpValue[A]): (Key, Json) => Either[NonEmptyList[String],A] = {
    kvpValue match {
      case StringData(validations) =>
        (key, json) =>
          for {
            jsonString <- json.field(key).toRight(NonEmptyList.one(s"Field with key $key not found."))
            str <- jsonString.string.toRight(NonEmptyList.one(s"Field with key $key is not a String"))
            validStr <- applicativeTraverse(validations.map(validationOp => isValid(validationOp).apply(str)))
          } yield validStr
    }
  }


  sealed abstract class KvpHList[H <: HList, N <: Nat]

  case class KeyValueDefinition[A](key: String, op: KvpValue[A])

  case class KvpSingleValueHead[A, H <: HList, N <: Nat, OUT <: A :: H]
  (
    fieldDefinition: KeyValueDefinition[A],
    tail: KvpHList[H, N],
    isHCons: IsHCons.Aux[OUT, A, H],
    validationOps: List[ValidationOp[OUT]]
  ) extends KvpHList[OUT, Succ[N]]


  def accumulate[A,B,C](e1: Either[NonEmptyList[String],A], e2: Either[NonEmptyList[String],B])(f: (A,B) => C)
    : Either[NonEmptyList[String],C] = ???

  def unmarshallHList[H<:HList, N<:Nat](kvpValue: KvpHList[H,N]): Json => Either[NonEmptyList[String],H] = {
    kvpValue match {
      case kvp: KvpSingleValueHead[a,h,n,o] =>
        val kvpF = unmarshall(kvp.fieldDefinition.op)
        val tailF = unmarshallHList(kvp.tail)
        (json) =>
          for {
            jsonString <- json.obj.toRight(NonEmptyList.one(s"JSON is not an object"))
            hlist <- accumulate(kvpF(kvp.fieldDefinition.key,json), tailF(json))((t1: a,t2: h) => {
              (t1 :: t2).asInstanceOf[o]
            })
            validStr <- applicativeTraverse(kvp.validationOps.map(validationOp => isValid(validationOp).apply(hlist)))
          } yield validStr.asInstanceOf[H]
    }
  }



}
