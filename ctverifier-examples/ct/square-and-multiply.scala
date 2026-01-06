import stainless.annotation._
import stainless.collection._

@ctverify
def squareAndMultiply(base: BigInt, @secret exponentBits: List[BigInt], modulus: BigInt, @secret acc: BigInt = 1): BigInt =
    require(modulus > 0)
    @public val exponentSize = exponentBits.size
    exponentBits match
        case Nil() => acc
        case Cons(bit, rest) =>
            val squared = (acc * acc) % modulus
            val multiplied = squared * base % modulus
            val nextAcc = squared + (multiplied - squared) * bit
            squareAndMultiply(base, rest, modulus, nextAcc)
