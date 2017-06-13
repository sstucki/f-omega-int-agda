------------------------------------------------------------------------
-- Experiments with higher-order Dependent Object Types (h-DOT)
------------------------------------------------------------------------

-- Author: Sandro Stucki
-- Copyright (c) 2017 EPFL

-- The code in this directory contains an experimental (and partial)
-- Agda mechanization of a higher-order Dependent Object Types (h-DOT)
-- calculus and variants thereof.
--
-- The code makes heavy use of the Agda standard library, which is
-- freely available from
--
--   https://github.com/agda/agda-stdlib/


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
-- suited for proving parallel substitution and validity lemmas, along
-- with a proof that the two presentations are equivalent.
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

-- Inversion lemmas for the alternate declarative subtyping judgment
-- that hold in the empty context.
open import FOmegaInt.Kinding.Declarative.Inversion

-- Generation of typing and inversion of declarative subtyping in the
-- empty context.
open import FOmegaInt.Typing.Inversion

-- Type safety (preservation/subject reduction and progress).
open import FOmegaInt.Typing.Preservation
open import FOmegaInt.Typing.Progress


------------------------------------------------------------------------
-- Modules containing generic functionality

-- Extra lemmas that are derivable in the substitution framework of
-- the Agda standard library, as well as support for substitutions
-- lifted to binary (term) relations, typed substitutions, and typed
-- parallel substitutions.
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Relation
open import Data.Fin.Substitution.Typed
open import Data.Fin.Substitution.TypedParallel

-- Support for generic reduction relations.
open import Relation.Binary.Reduction

-- Relational reasoning for transitive relations.
open import Relation.Binary.TransReasoning
