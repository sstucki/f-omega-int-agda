f-omega-int-agda – Fω with interval kinds mechanized in Agda
=============================================================

A mechanized type safety proof for Fω extended with interval kinds.

The code in this repository contains an Agda mechanization of the type system Fω extended with *interval kinds* ("F omega int").  An interval kind `A..B` represents a type interval bounded by a pair of types `A`, `B`.  It is inhabited by all proper types `C : A..B` that are both supertypes of `A` and subtypes of `B`.  Interval kinds are flexible enough to express various features found in other type systems, such as

 * F-<:-style bounded polymorphism,
 * bounded type operators,
 * singleton kinds and first-class type definitions.

The mechanization includes a small-step operational call-by-value semantics, declarative and canonical presentations of typing and kinding, along with (syntactic) proofs of various meta-theoretic properties, such as

 * weak normalization of types (and kinds) via hereditary substitution,
 * subject reduction for types (w.r.t. full β-reduction),
 * type safety (progress & preservation) w.r.t. to the CBV semantics,
 * undecidability of subtyping.


The Agda mechanization
----------------------

The file `src/README.agda` contains a detailed overview of the formalization.

The theory has been mechanized in [Agda](https://github.com/agda/agda) and makes heavy use of the [Agda standard library](https://github.com/agda/agda-stdlib).  The code in this repository has been type-checked using Agda 2.6.1.3 and version 1.6 of the Agda standard library.  The latest versions of the Agda distribution and standard library, along with setup instructions, can be found at

 * https://github.com/agda/agda
 * https://github.com/agda/agda-stdlib

The easiest way to check all the code is to compile the `README.agda` file from the `src/` directory.  Run

    agda src/README.agda

in the console, or simply open the file using the [Agda Emacs mode](https://github.com/agda/agda#configuring-the-emacs-mode) and type `C-c C-l`.


License
-------

The source code is released under the MIT License.  See the `LICENSE` file for details.
