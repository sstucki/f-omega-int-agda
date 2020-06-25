------------------------------------------------------------------------
-- Undecidability of subtyping in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Undecidable where

open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import FOmegaInt.Syntax
open import FOmegaInt.Typing as Declarative
open import FOmegaInt.Kinding.Canonical as Canonical
open import FOmegaInt.Kinding.Canonical.Equivalence
open import FOmegaInt.Undecidable.SK
open import FOmegaInt.Undecidable.Encoding
open import FOmegaInt.Undecidable.Decoding

open Syntax
open ContextConversions using (⌞_⌟Ctx)
open Canonical.Kinding  using (_⊢_<:_⇇_)
open Declarative.Typing using (_⊢_<:_∈_)
open Encoding
module T = TermCtx
module E = ElimCtx


------------------------------------------------------------------------
-- SK combinator term equality checking reduces to subtype checking in
-- Fω with interval kinds.
--
-- We do not proof undecidability of subtyping directly, but give a
-- reduction from undecidability of checking the equivalence of two SK
-- combinator terms, which is well-known to be undecidable.  In other
-- words, if we could check subtyping, we could also check the
-- equality of two SK combinator terms, which we cannot.
--
-- The following types characterize the decision procedures involved.

SKEqualityCheck : Set
SKEqualityCheck = (s t : SKTerm) → Dec (s ≡SK t)

CanoncialSubtypeCheck : Set
CanoncialSubtypeCheck = ∀ {n} (Γ : E.Ctx n) a b k → Dec (Γ ⊢ a <: b ⇇ k)

DeclarativeSubtypeCheck : Set
DeclarativeSubtypeCheck = ∀ {n} (Γ : T.Ctx n) a b k → Dec (Γ ⊢ a <: b ∈ k)

-- The reduction from SK equality checking to canoncial subtype checking.

module CanoncialReduction (check-<:⇇ : CanoncialSubtypeCheck) where

  canonicalEquivalence : ∀ s t → Γ-SK? ⊢ encode s <: encode t ⇇ ⌜*⌝ ⇔ s ≡SK t
  canonicalEquivalence s t = equivalence decode-<:⇇-encode <:⇇-encode

  check-≡SK : SKEqualityCheck
  check-≡SK s t =
    map (canonicalEquivalence s t) (check-<:⇇ Γ-SK? (encode s) (encode t) ⌜*⌝)

canonicalReduction : CanoncialSubtypeCheck → SKEqualityCheck
canonicalReduction = CanoncialReduction.check-≡SK

-- The reduction from SK equality checking to declarative subtype checking.

module DeclarativeReduction (check-<:∈ : DeclarativeSubtypeCheck) where

  declarativeEquivalence :
    ∀ s t → ⌞Γ-SK?⌟ ⊢ ⌞ encode s ⌟ <: ⌞ encode t ⌟ ∈ * ⇔ s ≡SK t
  declarativeEquivalence s t = equivalence
    (λ es<:et∈* → decode-<:⇇-encode
        (subst₂ (_ ⊢_<:_⇇ _) (nf-encode s) (nf-encode t) (complete-<: es<:et∈*)))
    (λ s≡t → sound-<:⇇ (<:⇇-encode s≡t))

  check-≡SK : SKEqualityCheck
  check-≡SK s t =
    map (declarativeEquivalence s t)
        (check-<:∈ ⌞Γ-SK?⌟ ⌞ encode s ⌟ ⌞ encode t ⌟ *)

declarativeReduction : DeclarativeSubtypeCheck → SKEqualityCheck
declarativeReduction = DeclarativeReduction.check-≡SK
