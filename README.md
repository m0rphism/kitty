# Kitty

An Agda Framework for programming language metatheory based on
extrinsic typing, intrinsic scoping and de Bruijn indices.

You write the syntax and typing relation, and the framework derives
definitions and lemmas of untyped substitution via reflection, and
provide you with an abstraction to prove type preservation of all
renaming and substitution operations of all variable sorts with a
single lemma.

We build on McBride's *kit* abstraction, which abstracts over
renamings and substitutions, and also abstract over the four
compositions between them and over type preservation of renamings and
substitutions. In the following, we use the term *map* to talk about
something, which can be either a renaming or a substitution.

## Dependencies

The framework requires the following dependencies to be installed:

-   [The Agda proof assistant](https://agda.readthedocs.io/en/latest/) in version >= 2.6.4
-   [The Agda standard library](https://github.com/agda/agda-stdlib) in version 2.0

## Comparison to the Simplified Version

We have submitted a paper about our framework to
[ITP'24](https://www.viam.science.tsu.ge/itp2024/). In the paper
we describe a simplified version of our framework, which can also be
found in the repository in
[src/Kitty/Examples/SystemF-Simple](src/Kitty/Examples/SystemF-Simple).

The full framework extends the simple framework as follows:

-   Additional map operations are provided, such as parallel
    compositions `_∥_`.

-   A reflection algorithm is provided to derive all definitions and
    lemmas about untyped maps.

-   We axiomatize the structure of maps, so you can choose
    whether you want to represent them as functions, vectors, or
    syntax trees.

-   We axiomatize the structure of type contexts, so you can choose
    whether you want to represent them as functions or vectors.

-   We extend the extensional equality for maps to an equivalence that
    can also compare renamings with substitutions. Intuitively, a
    renaming is equivalent to a substitution, iff they behave the same
    when applied to a term.

-   We don't rely on the functional extensionality axiom, and instead
    prove that our operations preserve map equivalence and provide a
    lemma that states that applying equivalent maps to a term yiels
    equal terms.

Those changes significantly increase the complexity of our framework,
so if you are interested in the internals of our framework, we
recommend to start looking at the simplified framework in
[src/Kitty/Examples/SystemF-Simple](src/Kitty/Examples/SystemF-Simple).

## Documentation

As the library is still changing a lot, we do not provide extensive
documentation, yet.

For now, we recommend to check out the examples and case studies in
[src/Kitty/Examples](src/Kitty/Examples) to get familiar with the framework.
