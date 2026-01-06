import stainless.annotation._
import stainless.collection._

@ctverify
def squareAndMultiply(base: BigInt, @secret exponentBits: List[BigInt], modulus: BigInt, @secret acc: BigInt = 1): BigInt =
    require(modulus > 0)
    exponentBits match
        case Nil() => acc
        case Cons(bit, rest) =>
            val squared = (acc * acc) % modulus
            val nextAcc =
                if bit == 1 then
                    (squared * base) % modulus
                else
                    squared
            squareAndMultiply(base, rest, modulus, nextAcc)
