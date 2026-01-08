import stainless.annotation._
import stainless.collection._

@ctverify
def checkPassword(@secret password: List[Char], candidate: List[Char]): Boolean =
  (password, candidate) match
    case (Cons(x, xs), Cons(y, ys)) =>
      x == y && checkPassword(xs, ys)

    case (Nil(), Nil()) =>
      true

    case _ =>
      false

