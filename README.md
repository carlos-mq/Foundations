# Foundations

A Lean4 formalization of some foundational mathematics in Lean, without the help of ``mathlib``. Only for educational purposes.

## Current Structure

- ``Finite.lean``: Here, we define basic structures including lists, binary trees, and natural numbers **N**.

- ``Structures.lean``: We define the basic algebraic structures that are particularly useful: semigroups, monoids, groups, abelian groups, posets, and totally ordered sets.

- ``Naturals.lean``: Ultimately, we prove that the natural numbers **N** form a commutative monoid under addition and a totally ordered set.

- ``Integers.lean``: We begin by defining the integers **Z** as a quotient type of **N** x **N**, and ultimately prove that they form an Abelian group under addition.

- ``Multiplication.lean``: [TO-DO] We begin by defining multiplication for natural numbers, extend it to integers, and ultimately prove that **Z** form a commutative ring.

## To-Do (Plans)

1. Creating multiplicative and additive copies of certain typeclasses, so that we are able to define the hierarchy ``Semiring -> Ring -> CommRing -> Field``.

2. Having defined this hierarchy, ultimately prove that **Z** is a commutative ring.

3. Define the rational numbers **Q** as an appropriate quotient over **Z** x **Z**; having done this, prove that **Q** forms a field.

After this, I may either do basic real analysis and topology:

4. Define the real numbers **R** as Cauchy sequences over **Q**. Prove **R** is a field, and its completeness.

5. Basic topology and basic topological properties of **R**.

Or instead, much more likely:

6. Define cyclic groups as quotients over **Z**, develop basic group theory, and from it develop some basic number theory.