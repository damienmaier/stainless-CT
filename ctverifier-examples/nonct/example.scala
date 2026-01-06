import stainless.annotation._
import stainless.collection._

@ctverify
def foo(@secret secret: Int, public: List[Char]): Boolean =

  val result = if public.contains('X') then secret else 1

  result match
    case 42 => true
    case _ => false
  

