import stainless.annotation._
import stainless.collection._

@ctverify
def lexigographicCompare(@secret a: List[BigInt], @secret b: List[BigInt], @secret gt: Boolean = false, @secret lt: Boolean = true): Boolean =

  @public val sizea = a.size
  @public val sizeb = b.size

  (a, b) match
    case (Nil(), Nil()) =>
      !lt

    case (Cons(x, xs), Cons(y, ys)) =>
      val undecided = (!gt) & (!lt)

      val xGt = x > y
      val xLt = x < y

      val nextGt = gt | (undecided & xGt)
      val nextLt = lt | (undecided & xLt)

      lexigographicCompare(xs, ys, nextGt, nextLt)

    case _ =>
      false
  

