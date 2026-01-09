# Stainless-CT

This is modified version of the Stainless verification framework, that enables automatic verification that a Scala function is constant time, i.e., that its execution path does not depend on secret data.

## Build

To build this project, clone the present repository with its submodules, then run
```
sbt Universal/stage
```

See the [Stainless installation instructions](https://epfl-lara.github.io/stainless/installation.html#build-from-source) for more information.

## Usage

Write the function to be analyzed in a Scala source file.
The function should have the `@ctverify` annotation, and each secret argument should have the `@secret` annotation.
Non annotated arguments are considered public.

Additionally, any variable declaration in the function body that has a `@public` annotation will be considered public.
This can be useful for instance to specify that the content of a list is secret, while allowing the execution path to depend on its size.

For example, write the following code in a file `example.scala`

```scala
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
```

In this function, the only conditional branching is the pattern matching statement.
The execution path after the pattern matching only depends on the size of the secret input `exponentBits`, not on its content.
As the size of `exponentBits` is made public via the annotated variable `exponentSize`, the execution path of this function does not depend on secret data, and thus the function is constant time.

Run:

```stainless example.scala```

to automatically verify that this function is constant time.

Various examples of constant time and non constant time functions are provied in the dirs `ctverifier-examples/ct` and `ctverifier-examples/nonct` of this repo.

### Feedback for non constant time functions

When provided with a non constant time function, Stainless automatically identifies the source code lines where a conditional branch depends on secret data, and gives a counterexample.

For example, consider the square and multiply implementation given in [`ctverifier-examples/nonct/square-and-multiply.scala`](ctverifier-examples/nonct/square-and-multiply.scala).
This function contains two CT violations : the pattern matching depends on the size of the secret input (in this function, the size of the secret input is not declared as public), and the if statement depends on the content of the secret input.

Running:

```
stainless ctverifier-examples/nonct/square-and-multiply.scala
```

gives:

```
[Warning ]  - Result for 'body assertion: The match case condition should not depend on the secret' VC for squareAndMultiply @7:5:
[Warning ] ctverifier-examples/nonct/square-and-multiply.scala:7:5:  => INVALID
               exponentBits match
               ^^^^^^^^^^^^^^^^^^...
[Warning ] Found counter-example:
[Warning ]   modulus: (BigInt, BigInt)                  -> (BigInt("1"), BigInt("1"))
[Warning ]   exponentBits: (List[BigInt], List[BigInt]) -> (Nil[BigInt](), Cons[BigInt](BigInt("3"), Nil[BigInt]()))
[Warning ]   base: (BigInt, BigInt)                     -> (BigInt("2"), BigInt("2"))


[Warning ]  - Result for 'body assertion: The if condition should not depend on the secret' VC for squareAndMultiply @12:17:
[Warning ] ctverifier-examples/nonct/square-and-multiply.scala:12:17:  => INVALID
                           if bit == 1 then
                           ^^^^^^^^^^^^^^^^...
[Warning ] Found counter-example:
[Warning ]   modulus: (BigInt, BigInt)                  -> (BigInt("39"), BigInt("39"))
[Warning ]   exponentBits: (List[BigInt], List[BigInt]) -> (Cons[BigInt](BigInt("1"), Nil[BigInt]()), Cons[BigInt](BigInt("3"), Nil[BigInt]()))
[Warning ]   base: (BigInt, BigInt)                     -> (BigInt("2"), BigInt("2"))
```

For the first CT violation, Stainless gives as counterexample two different secret inputs `exponentBits` of different sizes.

For the second CT violation, Stainless gives as counterexample two different secret inputs `exponentBits` with different content.

## Lockstep product program transformation

Internally, our implementation relies on a new phase in the Stainless pipeline, that translates the original function into a lockstep product function whose safety is equivalent to the CT security of the original function.

To see the effect of this transformation, use the flags `--debug=trees --debug-phases=Lockstep`.

For instance, running:

```
stainless --debug=trees --debug-phases=Lockstep ctverifier-examples/nonct/example.scala
```

Gives :

```scala
Symbols before Lockstep

[...]

@ctverify
@final
def foo((secret: Int) @secret, public: List[Char]): Boolean = {
  val result: Int = if (public.contains('X')) {
    secret
  } else {
    1
  }
  result match {
    case 42 =>
      true
    case _ =>
      false
  }
}

[...]

Running phase Lockstep

Symbols after Lockstep

[...]

@ctverify
@final
def foo(secret: (Int, Int), public: (List[Char], List[Char])): (Boolean, Boolean) = {
    require(public._1 == public._2)
    val result: (Int, Int) = {
        assert(public._1.contains('X') == public._2.contains('X'), "The if condition should not depend on the secret")
        if (public._1.contains('X')) {
            secret
        } else {
            (1, 1)
        }
    }
    assert(result._1 match {
        case 42 =>
            0
        case _ =>
            1
    } == result._2 match {
        case 42 =>
            0
        case _ =>
            1
    }, "The match case condition should not depend on the secret")
    result match {
        case (42, 42) =>
            (true, true)
        case (_, _) =>
            (false, false)
    }
}

```

## Stainless flags default values

As this version of Stainless focuses on verifying if functions are constant time, some other features of Stainless are disabled by default, but can be reenabled by passing the corresponding flags to the `stainless` command:
- --infer-measures
- --check-measures
- --strict-arithmetic

## Implementation

The modifications applied to Stainless in this project mostly consist of
- A new extraction phase implemented in `core/src/main/scala/stainless/extraction/ct/package.scala`
- The addition of this new phase in the pipeline in `core/src/main/scala/stainless/extraction/package.scala`

