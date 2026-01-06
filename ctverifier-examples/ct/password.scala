import stainless.annotation._
import stainless.collection._

@ctverify
def checkPassword(@secret correctPassword: List[Char], attemptPassword: List[Char]): Boolean =
  @public val passwordSize = correctPassword.size

  (correctPassword, attemptPassword) match
    case (Cons(correctChar, correctRest), Cons(attemptChar, attemptRest)) =>
      (correctChar == attemptChar) & checkPassword(correctRest, attemptRest)

    case (Nil(), Nil()) =>
      true

    case _ =>
      false

