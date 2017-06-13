------------------------------------------------------------------------
-- Inversion of declarative subtyping in Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Declarative.Inversion where

open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import FOmegaInt.Syntax
open import FOmegaInt.Kinding.Declarative
open import FOmegaInt.Kinding.Declarative.Validity
open import FOmegaInt.Kinding.Declarative.Normalization
open import FOmegaInt.Kinding.Canonical.Equivalence
  using (sound-<:; sound-<∷; complete-<∷; complete-<:-⋯)
import FOmegaInt.Kinding.Canonical.Inversion as CanInv

open Syntax
open Substitution using (_[_]; weaken)
open TermCtx
open Kinding
open KindedSubstitution


------------------------------------------------------------------------
-- Inversion of subtyping (in the empty context).

-- NOTE.  The following two lemmas only hold in the empty context
-- because we can not invert instances of the interval projection
-- rules (<:-⟨| and (<:-|⟩) in arbitrary contexts.  This is because
-- instances of these rules can reflect arbitrary subtyping
-- assumptions into the subtyping relation.  Consider, e.g.
--
--     Γ, X :: ⊤..⊥ ctx    Γ(X) = ⊥..⊤
--     ------------------------------- (∈-var)
--     Γ, X :: ⊤..⊥ ⊢ X :: ⊤..⊥
--     -------------------------- (<:-⟨|, <:-|⟩)
--     Γ, X :: ⊤..⊥ ⊢ ⊤ <: X <: ⊥
--
-- Which allows us to prove that ⊤ <: ⊥ using (<:-trans) under the
-- assumption (X : ⊤..⊥).  On the other hand, it is impossible to give
-- a transitivity-free proof of ⊤ <: ⊥.  In general, it is therefore
-- impossible to invert subtyping statements in non-empty contexts,
-- i.e. one cannot prove lemmas like (<:-→-inv) or (<:-∀-inv) below
-- for arbitrary contexts.

<:-∀-inv : ∀ {k₁ k₂ : Kind Term 0} {a₁ a₂} → [] ⊢ Π k₁ a₁ <: Π k₂ a₂ ∈ * →
           [] ⊢ k₂ <∷ k₁ × kd k₂ ∷ [] ⊢ a₁ <: a₂ ∈ *
<:-∀-inv ∀k₁a₁<:∀k₂a₂∈* =
  let nf-∀k₁a₁<:nf-∀k₂a₂          = complete-<:-⋯ ∀k₁a₁<:∀k₂a₂∈*
      nf-k₂<∷nf-k₁ , nf-a₁<:nf-a₂ = CanInv.<:-∀-inv nf-∀k₁a₁<:nf-∀k₂a₂
      ∀k₁a₁∈* , ∀k₂a₂∈*           = <:-valid ∀k₁a₁<:∀k₂a₂∈*
      k₁≅nf-k₁∈* , a₁≃nf-a₁∈*     = Tp∈-∀-≃-⌞⌟-nf ∀k₁a₁∈*
      k₂≅nf-k₂∈* , a₂≃nf-a₂∈*     = Tp∈-∀-≃-⌞⌟-nf ∀k₂a₂∈*
      k₂<∷nf-k₂∈*                 = ≅⇒<∷ k₂≅nf-k₂∈*
      k₂-kd , _                   = ≅-valid k₂≅nf-k₂∈*
      k₂<∷k₁ = <∷-trans (<∷-trans k₂<∷nf-k₂∈* (sound-<∷ nf-k₂<∷nf-k₁))
                        (≅⇒<∷ (≅-sym k₁≅nf-k₁∈*))
  in k₂<∷k₁ ,
     <:-trans (<:-trans (⇓-<: k₂-kd k₂<∷k₁ (≃⇒<: a₁≃nf-a₁∈*))
                        (⇓-<: k₂-kd k₂<∷nf-k₂∈* (sound-<: nf-a₁<:nf-a₂)))
              (≃⇒<: (≃-sym a₂≃nf-a₂∈*))

<:-→-inv : ∀ {a₁ a₂ b₁ b₂ : Term 0} → [] ⊢ a₁ ⇒ b₁ <: a₂ ⇒ b₂ ∈ * →
           [] ⊢ a₂ <: a₁ ∈ * × [] ⊢ b₁ <: b₂ ∈ *
<:-→-inv a₁⇒b₁<:a₂⇒b₂∈* =
  let nf-a₁⇒b₁<:nf-a₂⇒b₂          = complete-<:-⋯ a₁⇒b₁<:a₂⇒b₂∈*
      nf-a₂<:nf-a₁ , nf-b₁<:nf-b₂ = CanInv.<:-→-inv nf-a₁⇒b₁<:nf-a₂⇒b₂
      a₁⇒b₁∈* , a₂⇒b₂∈*           = <:-valid a₁⇒b₁<:a₂⇒b₂∈*
      a₁≃nf-a₁∈* , b₁≃nf-b₁∈*     = Tp∈-→-≃-⌞⌟-nf a₁⇒b₁∈*
      a₂≃nf-a₂∈* , b₂≃nf-b₂∈*     = Tp∈-→-≃-⌞⌟-nf a₂⇒b₂∈*
  in <:-trans (<:-trans (≃⇒<: a₂≃nf-a₂∈*) (sound-<: nf-a₂<:nf-a₁))
              (≃⇒<: (≃-sym a₁≃nf-a₁∈*)) ,
     <:-trans (<:-trans (≃⇒<: b₁≃nf-b₁∈*) (sound-<: nf-b₁<:nf-b₂))
              (≃⇒<: (≃-sym b₂≃nf-b₂∈*))

-- Arrows are not canonical subtypes of universals and vice-versa.

⇒-≮:-Π : ∀ {a₁ b₁ : Term 0} {k₂ a₂} → ¬ [] ⊢ a₁ ⇒ b₁ <: Π k₂ a₂ ∈ *
⇒-≮:-Π a₁⇒b₁<:∀k₂a₂∈* = CanInv.⇒-≮:-Π (complete-<:-⋯ a₁⇒b₁<:∀k₂a₂∈*)

Π-≮:-⇒ : ∀ {k₁ a₁} {a₂ b₂ : Term 0} → ¬ [] ⊢ Π k₁ a₁ <: a₂ ⇒ b₂ ∈ *
Π-≮:-⇒ ∀k₁a₁<:a₂⇒b₂∈* = CanInv.Π-≮:-⇒ (complete-<:-⋯ ∀k₁a₁<:a₂⇒b₂∈*)
