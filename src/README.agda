------------------------------------------------------------------------
-- Fω with interval kinds
------------------------------------------------------------------------

-- Author: Sandro Stucki
-- Copyright (c) 2017-2020 EPFL

-- The code in this repository contains an Agda mechanization of the
-- type system Fω extended with interval kinds ("F omega int").  An
-- interval kind `A..B' represents a type interval bounded by a pair
-- of types `A', `B'.  It is inhabited by all proper types `C : A..B'
-- that are both supertypes of `A' and subtypes of `B'.  Interval
-- kinds are flexible enough to express various features found in
-- other type systems, such as
--
--  * F-<:-style bounded polymorphism,
--  * bounded type operators,
--  * singleton kinds and first-class type definitions.
--
-- The mechanization includes a small-step operational call-by-value
-- semantics, declarative and canonical presentations of typing and
-- kinding, along with (syntactic) proofs of various meta-theoretic
-- properties, such as
--
--  * weak normalization of types (and kinds) via hereditary substitution,
--  * subject reduction for types (w.r.t. full β-reduction),
--  * type safety (progress & preservation) w.r.t. to the CBV semantics.
--
-- For more details on Fω with interval kinds, see my PhD thesis
-- "Higher-Order Subtyping with Type Intervals", which is available at
--
--   http://dx.doi.org/10.5075/epfl-thesis-8014
--
-- The code makes heavy use of the Agda standard library, which is
-- freely available at
--
--   https://github.com/agda/agda-stdlib/
--
-- The code has been tested using Agda 2.6.1 and version 1.3 of
-- the Agda standard library.

module README where


------------------------------------------------------------------------
-- Modules related to Fω with interval kinds.

-- Syntax of (untyped) terms along with support for substitutions,
-- (untyped) hereditary substitutions and normalization.
open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization

-- Weak equaity of (untyped) terms up to kind ascriptions in
-- abstractions.
open import FOmegaInt.Syntax.WeakEquality

-- Variants of β-reduction/equivalence and properties thereof.
open import FOmegaInt.Reduction.Cbv
open import FOmegaInt.Reduction.Full

-- Typing, kinding, subtyping, etc. along with corresponding
-- substitution lemmas.
open import FOmegaInt.Typing

-- An alternate presentation of kinding and subtyping that is better
-- suited for proving funcionality and validity lemmas, along with a
-- proof that the two presentations are equivalent.
open import FOmegaInt.Kinding.Declarative
open import FOmegaInt.Kinding.Declarative.Validity
open import FOmegaInt.Kinding.Declarative.Equivalence

-- Soundness of normalization w.r.t. to declarative kinding.
open import FOmegaInt.Kinding.Declarative.Normalization

-- Simple kinding of types, (hereditary) substitution lemmas.
open import FOmegaInt.Kinding.Simple

-- Lemmas about η-expansion of simply kinded and normalization and
-- simultaneous simplification of declaratively kinded types.
open import FOmegaInt.Kinding.Simple.EtaExpansion
open import FOmegaInt.Kinding.Simple.Normalization

-- Canonical kinding of types along with (hereditary) substitution,
-- validity and inversion lemmas for canonical kinding and subtyping.
open import FOmegaInt.Kinding.Canonical
open import FOmegaInt.Kinding.Canonical.HereditarySubstitution
open import FOmegaInt.Kinding.Canonical.Validity
open import FOmegaInt.Kinding.Canonical.Inversion

-- Lifting of weak (untyped) kind and type equality to canonical kind
-- and type equality.
open import FOmegaInt.Kinding.Canonical.WeakEquality

-- Equivalence of canonical and declarative kinding.
open import FOmegaInt.Kinding.Canonical.Equivalence

-- Generation of typing and inversion of declarative subtyping in the
-- empty context.
open import FOmegaInt.Typing.Inversion

-- Type safety (preservation/subject reduction and progress).
open import FOmegaInt.Typing.Preservation
open import FOmegaInt.Typing.Progress

-- Encodings and properties of higher-order extremal types, interval
-- kinds and bounded quantifiers.
open import FOmegaInt.Typing.Encodings


------------------------------------------------------------------------
-- Modules containing generic functionality

-- Extra lemmas that are derivable in the substitution framework of
-- the Agda standard library, as well as support for binary (term)
-- relations lifted to substitutions, typed substitutions, and typed
-- relations lifted to substitutions.
open import Data.Fin.Substitution.Context
open import Data.Fin.Substitution.Context.Properties
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Relation
open import Data.Fin.Substitution.Typed
open import Data.Fin.Substitution.TypedRelation

-- Support for generic reduction relations.
open import Relation.Binary.Reduction

-- Relational reasoning for transitive relations.
open import Relation.Binary.TransReasoning
