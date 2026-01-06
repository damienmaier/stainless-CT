import stainless.annotation._
import stainless.collection._

@ctverify
def checkPassword(@secret correctPassword: List[Char], attemptPassword: List[Char]): Boolean =
  (correctPassword, attemptPassword) match
    case (Cons(correctChar, correctRest), Cons(attemptChar, attemptRest)) =>
      if correctChar == attemptChar then
        checkPassword(correctRest, attemptRest)
      else
        false

    case (Nil(), Nil()) =>
      true

    case _ =>
      false

