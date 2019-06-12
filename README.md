f-omega-int-agda -- Fω with interval kinds mechanized in Agda
=============================================================

A mechanized type safety proof for Fω extended with interval kinds.

The code in this repository contains an Agda mechanization of the type system Fω extended with *interval kinds* ("F omega int").  An interval kind `A..B` represents a type interval bounded by a pair of types `A`, `B`.  It is inhabited by all proper types `C : A..B` that are both supertypes of `A` and subtypes of `B`.  Interval kinds are flexible enough to express various features found in other type systems, such as

 * F-<:-style bounded polymorphism,
 * bounded type operators,
 * singleton kinds and first-class type definitions.

The mechanization includes a small-step operational call-by-value semantics, declarative and canonical presentations of typing and kinding, along with (syntactic) proofs of various meta-theoretic properties, such as

 * weak normalization of types (and kinds) via hereditary substitution,
 * subject reduction for types (w.r.t. full β-reduction),
 * type safety (progress & preservation) w.r.t. to the CBV semantics.

The metatheory of Fω with interval kinds is described in detail in my PhD thesis [Higher-Order Subtyping with Type Intervals](http://dx.doi.org/10.5075/epfl-thesis-8014).


The Agda mechanization
----------------------

The file `src/README.agda` contains a more detailed overview of the formalization.

The theory has been mechanized in [Agda](https://github.com/agda/agda) and makes heavy use of the [Agda standard library](https://github.com/agda/agda-stdlib).  The code in this repository has been type-checked using Agda 2.5.3 and version 0.14 of the Agda standard library.  The latest versions of the Agda distribution and standard library, along with setup instructions, can be found at

 * https://github.com/agda/agda
 * https://github.com/agda/agda-stdlib

The easiest way to check all the code is to compile the `README.agda` file from the `src/` directory.  Run

    agda src/README.agda -i src -i <path-to-Agda-standard-library>/src

in the console, or simply open the file using the [Agda Emacs mode](https://github.com/agda/agda#configuring-the-emacs-mode) and type `C-c C-l`.


Source code
-----------

The Agda sources are freely available on GitHub:

 * https://github.com/sstucki/f-omega-int-agda


License and copyright
---------------------

The source code is released under the MIT License.  See the `LICENSE` file for details.


------------------------------------------------------------------------
Sandro Stucki -- Copyright (c) 2017, 2018, 2019 EPFL
