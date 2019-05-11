package slides

import argonaut.Json
import cats.data.{EitherT, NonEmptyList}
import cats.effect.{IO, Sync}
import org.http4s.{Header, HttpRoutes, Method, Response}
import cats.effect._
import cats.effect._
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import shapeless.{HList, Nat}
import slides.HListSlides.{KvpHList, KvpValue}

object Http4sSlides {


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

}
