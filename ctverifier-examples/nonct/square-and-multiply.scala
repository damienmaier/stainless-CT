import stainless.annotation._
import stainless.collection._

@ctverify
def squareAndMultiply(base: BigInt, @secret exponentBits: List[Boolean], modulus: BigInt, acc: BigInt = 1): BigInt =
    require(modulus > 0)
    exponentBits match
        case Nil() => acc
        case Cons(bit, rest) =>
            val squared = (acc * acc) % modulus
            val nextAcc =
                if bit then
                    squared * base
                else
                    squared
            squareAndMultiply(base, exponentBits, modulus, nextAcc)
