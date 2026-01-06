import stainless.annotation._
import stainless.collection._

@ctverify
def lexigographicCompare(@secret a: List[BigInt], @secret b: List[BigInt]): Boolean =

    (a, b) match
    case (Nil(), Nil()) =>
      true

    case (Cons(x, xs), Cons(y, ys)) =>
      if x > y then
        true
      else if x < y then
        false
      else
        lexigographicCompare(xs, ys)

    case _ =>
      false
  

