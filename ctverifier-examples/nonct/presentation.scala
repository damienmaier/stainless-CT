import stainless.annotation._

@ctverify
def foo(public: Int, @secret secret: Int) =
  val a = public * 2
  val b = secret + 1

  val c = if a == 42 then b else 0

  if c > 10 then 
    1 
  else
    0
