import stainless.annotation._
import stainless.collection._

@ctverify
def foo(@secret password: List[Int], candidate: List[Int], i: BigInt = 0): Boolean =
  require(password.size == 100)
  require(candidate.size == 100)
  require(0 <= i && i <= 100)

  if i == 100 then true else
    (password(i) == candidate(i)) & foo(password, candidate, i+1)


