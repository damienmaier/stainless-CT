import stainless.annotation._
import stainless.collection._

@ctverify
def foo(@secret password: List[Int], candidate: List[Int], i: BigInt = 0): Boolean =
  require(password.size == 5)
  require(candidate.size == 5)
  require(0 <= i && i <= 5)

  if i == 5 then true else
    (password(i) == candidate(i)) && foo(password, candidate, i+1)


