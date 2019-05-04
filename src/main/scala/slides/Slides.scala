package slides

import argonaut.Json.JsonAssoc
import shapeless.{Generic, HNil, ::}

object Slides extends App {

  sealed abstract class ValueOp[A]

  case class StringData(key: String) extends ValueOp[String]

  case class IntData(key: String) extends ValueOp[Int]

  case class OptionalData[B](optionalValueOp: ValueOp[B])
      extends ValueOp[Option[B]]

  case class TupleData[B, C](leftValue: ValueOp[B], rightValue: ValueOp[C])
      extends ValueOp[(B, C)]

  val example =
    TupleData(
      StringData("name"),
      TupleData(
        OptionalData(TupleData(IntData("latitude"), IntData("longitude"))),
        OptionalData(IntData("height"))
      ))

  object DocInterpreter {

    def createDoc[A](op: ValueOp[A]): String = {
      op match {
        case TupleData(b, c) =>
          s"${createDoc(b)} combined with ${createDoc(c)})"
        case OptionalData(b) => s"${createDoc(b)} which is optional"
        case StringData(key) => s"a String with key ${key}"
        case IntData(key)    => s"an Int with key ${key}"
      }
    }
  }

  DocInterpreter.createDoc(example)

  import argonaut._
  object ArgonautMarshall {

    def marshall[A](op: ValueOp[A]): A => Json = {
      op match {
        case StringData(key) =>
          (str: String) =>
            Json.obj((key, Json.jString(str)))

        case IntData(key) =>
          (i: Int) =>
            Json.obj((key, Json.jNumber(i)))

        case OptionalData(aValueOp) => {
          val fOptional = marshall(aValueOp)
          (opt: A) =>
            {
              opt match {
                case None    => Json.jNull
                case Some(a) => fOptional(a)
              }
            }
        }

        case TupleData(l, r) => {
          val fLeft = marshall(l)
          val fRight = marshall(r)
          (tuple: A) =>
            {
              val left = fLeft(tuple._1)
              val right = fRight(tuple._2)
              val combined = combine(left, right)
              combined
            }
        }
      }

    }

    val waterfallLiteral
      : ((String, (Option[(Int, Int)], Option[Int]))) => argonaut.Json =
      (i1: (String, (Option[(Int, Int)], Option[Int]))) => {
        combine(
          { (s: String) =>
            Json.obj(("name", Json.jString(s)))
          }.apply(i1._1), { (i2: (Option[(Int, Int)], Option[Int])) =>
            {
              combine(
                {
                  (i3: Option[(Int, Int)]) =>
                    {
                      i3 match {
                        case None => Json.jEmptyObject
                        case Some(a) => { (i4: (Int, Int)) =>
                          {
                            combine({ (i: Int) =>
                              Json.obj(("lattitude", Json.jNumber(i)))
                            }.apply(i4._1), { (i: Int) =>
                              Json.obj(("longitude", Json.jNumber(i)))
                            }.apply(i4._2))
                          }
                        }.apply(a)
                      }
                    }
                }.apply(i2._1), { (i: Option[Int]) =>
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

    val personFLiteral: (((Option[(String, Int)], Option[Int]), Int)) => Json =
      (i1: (((Option[(String, Int)], Option[Int]), Int))) => {
        combine(
          { (i2: (Option[(String, Int)], Option[Int])) =>
            {
              combine(
                {
                  (i3: Option[(String, Int)]) =>
                    {
                      i3 match {
                        case None => Json.jEmptyObject
                        case Some(a) => {
                          { (i4: (String, Int)) =>
                            {
                              combine(
                                { (s: String) =>
                                  Json.obj(("name", Json.jString(s)))
                                }.apply(i4._1), { (i: Int) =>
                                  Json.obj(("age", Json.jNumber(i)))
                                }.apply(i4._2)
                              )
                            }
                          }.apply(a)
                        }
                      }
                    }
                }.apply(i2._1), { (i5: Option[Int]) =>
                  {
                    i5 match {
                      case None => Json.jNull
                      case Some(a) => { (i: Int) =>
                        Json.obj(("experienceInYears", Json.jNumber(i)))
                      }.apply(a)
                    }
                  }
                }.apply(i2._2)
              )
            }
          }.apply(i1._1), { (i: Int) =>
            Json.obj(("numberOfKudos", Json.jNumber(i)))
          }.apply(i1._2)
        )
      }

    def combine(prefix: Json, postfix: Json): Json = {
      val values1 = prefix.obj.toList.flatMap(_.toList)
      val values2 = postfix.obj.toList.flatMap(_.toList)
      Json.obj(values1 ::: values2: _*)
    }

  }

  object ArgonautUnmarshall {
    def unmarshall[A](op: ValueOp[A]): Json => Either[String, A] = {
      op match {
        case StringData(key) =>
          json =>
            findField(key, json)
              .flatMap(_._2.string)
              .toRight(s"String Not Found ${key}")
        case IntData(key) =>
          json =>
            findField(key, json)
              .flatMap(_._2.number)
              .flatMap(_.toInt)
              .toRight(s"Int Not Found ${key}")
        case op: OptionalData[b] =>
          val valueB = unmarshall(op.optionalValueOp) // Json => Either[String,Option[A]]
          json =>
            {
              valueB(json) match {
                case Left(_)  => Right(None)
                case Right(x) => Right(Some(x))
              }
            }
        case TupleData(leftOp, rightOp) =>
          val leftF = unmarshall(leftOp)
          val rightF = unmarshall(rightOp)
          json =>
            {
              val left = leftF(json)
              val right = rightF(json)
              combineTuple(left, right)
            }
      }
    }

    def combineTuple[B, C](b: Either[String, B],
                           c: Either[String, C]): Either[String, (B, C)] = {
      (b, c) match {
        case (Left(bErr), Left(cError)) => Left(s"${bErr}|${cError}")
        case (Left(bErr), _)            => Left(bErr)
        case (_, Left(cErr))            => Left(cErr)
        case (Right(b), Right(c))       => Right((b, c))
      }
    }

    def findField(key: String, json: Json): Option[JsonAssoc] = {
      json.obj.flatMap(_.toList.find(_._1 == key))
    }

  }

  val dryFalls = ( "Dry Falls", ( Some( (35, -83) ), Some(80) ))
  val personF =
    ArgonautMarshall.marshall(example)
  val result = personF(dryFalls)

  val finalValue = ArgonautUnmarshall.unmarshall(example)(result)

  result
  finalValue
  ArgonautMarshall.waterfallLiteral(dryFalls)

  case class Location(latitude: Int, longitude: Int)
  case class Waterfall(name: String, location: Option[Location], height: Option[Int])

  val genLocation = Generic[Location]
  val genWaterfall = Generic[Waterfall]

  val dryFallsHList = "Dry Falls" :: Some( 35 :: -83 :: HNil ) :: Some(80) :: HNil
  val dryFallsLocation: String :: Option[Location] :: Option[Int] :: HNil =
    dryFallsHList.head ::
      dryFallsHList.tail.head.map(genLocation.from) ::
      dryFallsHList.tail.tail.head ::
      dryFallsHList.tail.tail.tail

  genWaterfall.from(dryFallsLocation)

}
