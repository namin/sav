Course Project in Synthesis, Analysis and Verification in Scala
===============================================================
by Nada Amin

This project develops the [`sav`][SavPlugin] Scala compiler plugin,
which integrates the Scala compiler with the verifier built during the
[EPFL SAV 2012 course][sav12].

The [SAV verifier][lazabs] takes in the [CFG][cfg] representation of a
program, where each vertex represent a point in the program, and each
edge is labelled with one of an assumption, an assignment or a "havoc"
destroying all information about a variable, from which it [generates
a set of verification conditions][vcg]. This set of verification
conditions are then checked for validity with a theorem prover.

The `sav` plugin collects method and class definitions annotated with
[`@verify`][verifyAnnotation]. It generates a CFG for each method
definition to verify.

Features
--------

The plugin understands the following specially-handled statements:
`assume`, `assert`, `precondition`, `postcondition`. When verifying a
method definition, `precondition` is like `assume`, and
`postcondition` is like `assert`. `precondition` and `postcondition`
becomes part of the "contract" of a verified method. The contract is
used when a verified method is called from another to (1) assert that
the preconditions hold (2) exploit the postconditions as asssumptions.

`Int` parameters and local variables can appear in a checked boolean
clauses. In addition, if a class is annotated with `@verify`, its
`Int` fields can also appear in a checked boolean clause, and
furthermore, its immutable fields of an `@verify` class type are
recursively considered.

The plugin tries to be lenient in ignoring variables, statements and
expressions that it can guarantee to be irrelevant for the generation
of verification conditions. This leniency allows a broad subset of
Scala to be used in verified methods.

A `while` loop invariant is expressed as an `assert` statement
immediately preceding it.

It is possible to refer to "old" values of a field in a
`postcondition`. The pattern is to create `Int val`s at the beginning
of the verified method, where the right-hand side is wrapped in an
`old` library call, a no-op that the plugin uses as a signal. See the
last motivating example.

Motivating Examples
-------------------

- [`ex3`][ex3] is an introductory example, which is similar to those
  handled by the original course verifier.

- [`ex4`][ex4] is an advanced example, which cannot be handled by the
  original course verifier. In `test`, the verifier checks whether
  calls to `lock` and `unlock` alternate. The `queue` parameter is
  entirely ignored and is not needed for verification. For instance,
  the boolean clause of the `if` inside the `do`-`while`, `q.next !=
  None` is not registered in the CFG, as it's not a clause that the
  theorem prover can understand. [`ex4c`][ex4c] is the same program
  rewritten using an `@verify` class and a field.

- [`ex7`][ex7] motivates the `@verify` class feature.

Limitations
-----------

The verifier relies on the [Princess theorem prover][princess], which
only supports Presburger arithmetic. In particular, multiplications
between variables are not allowed. [`neg1`][neg1] shows an example
that cannot be handled because it is beyond Princess' powers.

`@verify` classes raises the issue of aliasing. The limitation that
non-`Int` fields must be immutable to be considered in checked boolean
clauses is there to contain the damage of aliasing. Aliasing is the
only known source of unsoundness, and the plugin deals with it by
generating warnings. The [`inv1`][inv1] and [`inv3`][inv3] examples
are invalid because of aliasing . In `inv1`, the `bar` method is
correct, except when the parameter `foo` is `this`. This aliasing
possibility generates a warning, but the method still successfully
verifies. Fortunately, the `evil` method which calls it in the
aliasing configuration correctly fails to verify (thanks to the
havocing of the arguments passed by reference). In `inv3`, the
`postcondition` in the `baz` method always fails because of
predictable aliasing -- warnings are issued, but, as of now, aliasing
is not explicitly handled so the method still successfully verifies.

Compiling and Testing
---------------------
`sbt assembly`, then `./run-tests`

[sav12]: http://lara.epfl.ch/w/sav12:top
[princess]: http://www.philipp.ruemmer.org/princess.shtml
[SavPlugin]: https://github.com/namin/sav/blob/master/src/main/scala/net/namin/sav/SavPlugin.scala
[lazabs]: https://github.com/namin/sav/blob/master/src/main/scala/lazabs
[cfg]: https://github.com/namin/sav/blob/master/src/main/scala/lazabs/cfg/CFG.scala
[vcg]: https://github.com/namin/sav/blob/master/src/main/scala/lazabs/vcg/VCG.scala
[verifyAnnotation]: https://github.com/namin/sav/blob/master/src/main/scala/net/namin/sav/annotation/verify.scala
[neg1]: https://github.com/namin/sav/blob/master/test/neg1.scala
[ex3]: https://github.com/namin/sav/blob/master/test/ex3.scala
[ex4]: https://github.com/namin/sav/blob/master/test/ex4.scala
[ex4c]: https://github.com/namin/sav/blob/master/test/ex4c.scala
[ex7]: https://github.com/namin/sav/blob/master/test/ex7.scala
[inv1]: https://github.com/namin/sav/blob/master/test/inv1.scala
[inv3]: https://github.com/namin/sav/blob/master/test/inv3.scala
