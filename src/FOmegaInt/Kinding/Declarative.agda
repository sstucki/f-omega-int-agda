------------------------------------------------------------------------
-- Extended declarative kinding in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Kinding.Declarative where

open import Data.Context.WellFormed
open import Data.Fin using (Fin; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.Extra using (module SimpleExt)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Fin.Substitution.TypedRelation
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_; proj₁)
import Data.Vec as Vec
open import Function using (_∘_)
import Level
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax


------------------------------------------------------------------------
-- Extended declarative (sub)kinding, subtyping and equality.
--
-- This module contains variants of the declarative kinding and
-- subtyping judgments which differ slightly from those given in the
-- Typing module.  Some of the rules in this module have additional
-- premises which we call "validity conditions".  These validity
-- conditions are redundant in the sense that they follow (more or
-- less) directly from so-called "validity" properties of the
-- corresponding judgments.  For example, the kinding rule (∈-Π-e)
-- below concludes that `Γ ⊢ a · b ∈ k Kind[ b ]' and has, among
-- others, the validity condition `Γ ⊢ k Kind[ b ] kd' as one of its
-- premises.  But this is a direct consequence of "kinding validity"
-- which states that the kinds of well-kinded types are themselves
-- well-formed, i.e. that `Γ ⊢ k kd' whenever `Γ ⊢Tp a ∈ k' (see the
-- Kinding.Declarative.Validity module for the full set of validity
-- lemmas).  Since all the validity conditions follow from
-- corresponding validity lemmas, they are, in principle, redundant.
-- Indeed, this is why they do not appear in the kinding and subtyping
-- rules of the Typing module.  The reason for including the validity
-- conditions as premises in the rules below is that the proofs of
-- some lemmas (notably the validity lemmas themselves) are done by
-- induction on kinding and subtyping derivations and require the
-- proofs of these conditions to be proper sub-derivations of the
-- derivations on which the induction is performed.
--
-- To proof the validity lemmas for both variants of the kinding and
-- subtyping judgments, we use the following strategy:
--
--  1. prove the validity lemmas for the judgments containing the
--     additional validity conditions as premises,
--
--  2. prove that the two variants of the judgments are
--     equivalent, i.e.
--
--     a) the extended judgments are sound w.r.t to the original
--        judgments: we can drop the validity conditions without
--        affecting the conclusion of the derivations, and
--
--     b) the extended judgments are complete w.r.t. to the original
--        judgments: crucially, the additional validity conditions
--        follow from the *remaining premises* of the extended rules
--        via the validity lemmas proved in step 1,
--
--  3. prove that validity holds for the original judgments via the
--     equivalence: convert to the extended judgment (via
--     completeness), apply the lemma in question, convert the
--     conclusion back (via soundness).
--
--  See the Kinding.Declarative.Equivalence module for the full proof
--  of equivalence (point 2) and the `Tp∈-valid' lemma in the
--  Typing.Inversion module for an example of point 3.

module Kinding where
  open TermCtx
  open Syntax
  open Substitution using (_[_]; _Kind[_]; weaken)

  infix 4 _ctx _⊢_kd _⊢_wf
  infix 4 _⊢Tp_∈_ _⊢_∈_
  infix 4 _⊢_<:_∈_ _⊢_<∷_
  infix 4 _⊢_≃_∈_ _⊢_≅_ _⊢_≃⊎≡_∈_

  mutual

    -- Well-formed typing contexts.

    _ctx : ∀ {n} → Ctx n → Set
    _ctx = ContextFormation._wf _⊢_wf

    -- Well-formed type/kind ascriptions in typing contexts.

    data _⊢_wf {n} (Γ : Ctx n) : TermAsc n → Set where
      wf-kd : ∀ {a} → Γ ⊢ a kd    → Γ ⊢ (kd a) wf
      wf-tp : ∀ {a} → Γ ⊢Tp a ∈ * → Γ ⊢ (tp a) wf

    -- Well-formed kinds.

    data _⊢_kd {n} (Γ : Ctx n) : Kind Term n → Set where
      kd-⋯ : ∀ {a b} → Γ ⊢Tp a ∈ * → Γ ⊢Tp b ∈ * → Γ ⊢ a ⋯ b kd
      kd-Π : ∀ {j k} → Γ ⊢ j kd → kd j ∷ Γ ⊢ k kd → Γ ⊢ Π j k kd

    -- Kinding derivations.

    data _⊢Tp_∈_ {n} (Γ : Ctx n) : Term n → Kind Term n → Set where
      ∈-var : ∀ {k} x → Γ ctx → lookup Γ x ≡ kd k → Γ ⊢Tp var x ∈ k
      ∈-⊥-f : Γ ctx → Γ ⊢Tp ⊥ ∈ *
      ∈-⊤-f : Γ ctx → Γ ⊢Tp ⊤ ∈ *
      ∈-∀-f : ∀ {k a} → Γ ⊢ k kd → kd k ∷ Γ ⊢Tp a ∈ * → Γ ⊢Tp Π k a ∈ *
      ∈-→-f : ∀ {a b} → Γ ⊢Tp a ∈ * → Γ ⊢Tp b ∈ * → Γ ⊢Tp a ⇒ b ∈ *
      ∈-Π-i : ∀ {j a k} → Γ ⊢ j kd → kd j ∷ Γ ⊢Tp a ∈ k →
              -- Validity condition:
              kd j ∷ Γ ⊢ k kd →
              Γ ⊢Tp Λ j a ∈ Π j k
      ∈-Π-e : ∀ {a b j k} → Γ ⊢Tp a ∈ Π j k → Γ ⊢Tp b ∈ j →
              -- Validity conditions:
              kd j ∷ Γ ⊢ k kd → Γ ⊢ k Kind[ b ] kd →
              Γ ⊢Tp a · b ∈ k Kind[ b ]
      ∈-s-i : ∀ {a b c} → Γ ⊢Tp a ∈ b ⋯ c → Γ ⊢Tp a ∈ a ⋯ a
      ∈-⇑   : ∀ {a j k} → Γ ⊢Tp a ∈ j → Γ ⊢ j <∷ k → Γ ⊢Tp a ∈ k

    -- Subkinding derivations.

    data _⊢_<∷_ {n} (Γ : Ctx n) : Kind Term n → Kind Term n → Set where
      <∷-⋯ : ∀ {a₁ a₂ b₁ b₂} →
             Γ ⊢ a₂ <: a₁ ∈ * → Γ ⊢ b₁ <: b₂ ∈ * → Γ ⊢ a₁ ⋯ b₁ <∷ a₂ ⋯ b₂
      <∷-Π : ∀ {j₁ j₂ k₁ k₂} →
             Γ ⊢ j₂ <∷ j₁ → kd j₂ ∷ Γ ⊢ k₁ <∷ k₂ → Γ ⊢ Π j₁ k₁ kd →
             Γ ⊢ Π j₁ k₁ <∷ Π j₂ k₂

    -- Subtyping derivations.

    data _⊢_<:_∈_ {n} (Γ : Ctx n) : Term n → Term n → Kind Term n → Set where
      <:-refl  : ∀ {a k}     → Γ ⊢Tp a ∈ k → Γ ⊢ a <: a ∈ k
      <:-trans : ∀ {a b c k} → Γ ⊢ a <: b ∈ k → Γ ⊢ b <: c ∈ k → Γ ⊢ a <: c ∈ k
      <:-β₁    : ∀ {j a k b} → kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j →
                 -- Validity conditions:
                 Γ ⊢Tp a [ b ] ∈ k Kind[ b ] →
                 kd j ∷ Γ ⊢ k kd → Γ ⊢ k Kind[ b ] kd →
                 Γ ⊢ (Λ j a) · b <: a [ b ] ∈ k Kind[ b ]
      <:-β₂    : ∀ {j a k b} → kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j →
                 -- Validity conditions:
                 Γ ⊢Tp a [ b ] ∈ k Kind[ b ] →
                 kd j ∷ Γ ⊢ k kd → Γ ⊢ k Kind[ b ] kd →
                 Γ ⊢ a [ b ] <: (Λ j a) · b ∈ k Kind[ b ]
      <:-η₁    : ∀ {a j k} → Γ ⊢Tp a ∈ Π j k →
                 Γ ⊢ Λ j (weaken a · var zero) <: a ∈ Π j k
      <:-η₂    : ∀ {a j k} → Γ ⊢Tp a ∈ Π j k →
                 Γ ⊢ a <: Λ j (weaken a · var zero) ∈ Π j k
      <:-⊥     : ∀ {a b c} → Γ ⊢Tp a ∈ b ⋯ c → Γ ⊢ ⊥ <: a ∈ *
      <:-⊤     : ∀ {a b c} → Γ ⊢Tp a ∈ b ⋯ c → Γ ⊢ a <: ⊤ ∈ *
      <:-∀     : ∀ {k₁ k₂ a₁ a₂} →
                 Γ ⊢ k₂ <∷ k₁ → kd k₂ ∷ Γ ⊢ a₁ <: a₂ ∈ * → Γ ⊢Tp Π k₁ a₁ ∈ * →
                 Γ ⊢ Π k₁ a₁ <: Π k₂ a₂ ∈ *
      <:-→     : ∀ {a₁ a₂ b₁ b₂} → Γ ⊢ a₂ <: a₁ ∈ * → Γ ⊢ b₁ <: b₂ ∈ * →
                 Γ ⊢ a₁ ⇒ b₁ <: a₂ ⇒ b₂ ∈ *
      <:-λ     : ∀ {j₁ j₂ a₁ a₂ j k} → kd j ∷ Γ ⊢ a₁ <: a₂ ∈ k →
                 Γ ⊢Tp Λ j₁ a₁ ∈ Π j k → Γ ⊢Tp Λ j₂ a₂ ∈ Π j k →
                 Γ ⊢ Λ j₁ a₁ <: Λ j₂ a₂ ∈ Π j k
      <:-·     : ∀ {a₁ a₂ b₁ b₂ j k} → Γ ⊢ a₁ <: a₂ ∈ Π j k → Γ ⊢ b₁ ≃ b₂ ∈ j →
                 -- Validity conditions:
                 Γ ⊢Tp b₁ ∈ j → kd j ∷ Γ ⊢ k kd → Γ ⊢ k Kind[ b₁ ] kd →
                 Γ ⊢ a₁ · b₁ <: a₂ · b₂ ∈ k Kind[ b₁ ]
      <:-⟨|    : ∀ {a b c} → Γ ⊢Tp a ∈ b ⋯ c → Γ ⊢ b <: a ∈ *
      <:-|⟩    : ∀ {a b c} → Γ ⊢Tp a ∈ b ⋯ c → Γ ⊢ a <: c ∈ *
      <:-⋯-i   : ∀ {a b c d} → Γ ⊢ a <: b ∈ c ⋯ d → Γ ⊢ a <: b ∈ a ⋯ b
      <:-⇑     : ∀ {a b j k} → Γ ⊢ a <: b ∈ j → Γ ⊢ j <∷ k → Γ ⊢ a <: b ∈ k

    -- Type equality.

    data _⊢_≃_∈_ {n} (Γ : Ctx n) : Term n → Term n → Kind Term n → Set where
      <:-antisym : ∀ {a b k} → Γ ⊢ a <: b ∈ k → Γ ⊢ b <: a ∈ k → Γ ⊢ a ≃ b ∈ k

  -- Kind equality.

  data _⊢_≅_ {n} (Γ : Ctx n) : Kind Term n → Kind Term n → Set where
    <∷-antisym : ∀ {j k} → Γ ⊢ j <∷ k → Γ ⊢ k <∷ j → Γ ⊢ j ≅ k

  -- Combined kinding of types and term variable typing.

  data _⊢_∈_ {n} (Γ : Ctx n) : Term n → TermAsc n → Set where
    ∈-tp  : ∀ {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ a ∈ kd k
    ∈-var : ∀ x {a} → Γ ctx → lookup Γ x ≡ tp a → Γ ⊢ var x ∈ tp a

  -- Combined type equality and syntactic term variable equality (used
  -- for well-formed equality lifted to substitutions).

  data _⊢_≃⊎≡_∈_ {n} (Γ : Ctx n) : Term n → Term n → TermAsc n → Set where
    ≃-tp  : ∀ {a b k} → Γ ⊢ a ≃ b ∈ k           → Γ ⊢ a     ≃⊎≡ b     ∈ kd k
    ≃-var : ∀ x {a} → Γ ctx → lookup Γ x ≡ tp a → Γ ⊢ var x ≃⊎≡ var x ∈ tp a

  open PropEq using ([_])

  -- Derived variable rules.

  ∈-var′ : ∀ {n} {Γ : Ctx n} x → Γ ctx → Γ ⊢ var x ∈ lookup Γ x
  ∈-var′ {Γ = Γ} x Γ-ctx with lookup Γ x | inspect (lookup Γ) x
  ∈-var′ x Γ-ctx | kd k | [ Γ[x]≡kd-k ] = ∈-tp (∈-var x Γ-ctx Γ[x]≡kd-k)
  ∈-var′ x Γ-ctx | tp a | [ Γ[x]≡tp-a ] = ∈-var x Γ-ctx Γ[x]≡tp-a

  ≃⊎≡-var : ∀ {n} {Γ : Ctx n} x → Γ ctx → Γ ⊢ var x ≃⊎≡ var x ∈ lookup Γ x
  ≃⊎≡-var {Γ = Γ} x Γ-ctx with lookup Γ x | inspect (lookup Γ) x
  ≃⊎≡-var x Γ-ctx | kd k | [ Γ[x]≡kd-k ] =
    let x∈a = ∈-var x Γ-ctx Γ[x]≡kd-k
    in ≃-tp (<:-antisym (<:-refl x∈a) (<:-refl x∈a))
  ≃⊎≡-var x Γ-ctx | tp a | [ Γ[x]≡tp-a ] = ≃-var x Γ-ctx Γ[x]≡tp-a

  open ContextFormation _⊢_wf public
    hiding (_wf) renaming (_⊢_wfExt to _⊢_ext)


------------------------------------------------------------------------
-- Properties of typings

open Syntax
open TermCtx
open Kinding

-- An inversion lemma for _⊢_wf.

wf-kd-inv : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ kd k wf → Γ ⊢ k kd
wf-kd-inv (wf-kd k-kd) = k-kd

-- Subkinds have the same shape.

<∷-⌊⌋ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → ⌊ j ⌋ ≡ ⌊ k ⌋
<∷-⌊⌋ (<∷-⋯ _ _)             = refl
<∷-⌊⌋ (<∷-Π j₂<∷j₁ k₁<∷k₂ _) = cong₂ _⇒_ (sym (<∷-⌊⌋ j₂<∷j₁)) (<∷-⌊⌋ k₁<∷k₂)

-- Equal kinds have the same shape.

≅-⌊⌋ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → ⌊ j ⌋ ≡ ⌊ k ⌋
≅-⌊⌋ (<∷-antisym j<∷k k<∷j) = <∷-⌊⌋ j<∷k

-- Kind and type equality imply subkinding and subtyping, respectively.

≅⇒<∷ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ j <∷ k
≅⇒<∷ (<∷-antisym j<∷k k<∷j) = j<∷k

≃⇒<: : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ∈ k → Γ ⊢ a <: b ∈ k
≃⇒<: (<:-antisym a<:b b<:a) = a<:b

-- Reflexivity of subkinding.

<∷-refl : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ k <∷ k
<∷-refl (kd-⋯ a∈* b∈*)   = <∷-⋯ (<:-refl a∈*) (<:-refl b∈*)
<∷-refl (kd-Π j-kd k-kd) = <∷-Π (<∷-refl j-kd) (<∷-refl k-kd) (kd-Π j-kd k-kd)

-- Reflexivity of kind equality.

≅-refl : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ k ≅ k
≅-refl k-kd = <∷-antisym (<∷-refl k-kd) (<∷-refl k-kd)

-- Symmetry of kind equality.

≅-sym : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ k ≅ j
≅-sym (<∷-antisym j<∷k k<∷j) = <∷-antisym k<∷j j<∷k

-- An admissible kind equality rule for interval kinds.

≅-⋯ : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂} →
      Γ ⊢ a₁ ≃ a₂ ∈ * → Γ ⊢ b₁ ≃ b₂ ∈ * → Γ ⊢ a₁ ⋯ b₁ ≅ a₂ ⋯ b₂
≅-⋯ (<:-antisym a₁<:a₂ a₂<:a₁) (<:-antisym b₁<:b₂ b₂<:b₁) =
  <∷-antisym (<∷-⋯ a₂<:a₁ b₁<:b₂) (<∷-⋯ a₁<:a₂ b₂<:b₁)

-- Type equality is reflexive.

≃-refl : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ a ≃ a ∈ k
≃-refl a∈k = <:-antisym (<:-refl a∈k) (<:-refl a∈k)

-- Type equality is transitive.

≃-trans : ∀ {n} {Γ : Ctx n} {a b c k} →
          Γ ⊢ a ≃ b ∈ k → Γ ⊢ b ≃ c ∈ k → Γ ⊢ a ≃ c ∈ k
≃-trans (<:-antisym a<:b b<:a) (<:-antisym b<:c c<:b) =
  <:-antisym (<:-trans a<:b b<:c) (<:-trans c<:b b<:a)

-- Type equality is symmetric.

≃-sym : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ∈ k → Γ ⊢ b ≃ a ∈ k
≃-sym (<:-antisym a<:b b<:a) = <:-antisym b<:a a<:b

-- Reflexivity of the combined type and term variable equality.

≃⊎≡-refl : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ∈ b → Γ ⊢ a ≃⊎≡ a ∈ b
≃⊎≡-refl (∈-tp a∈k)                = ≃-tp (≃-refl a∈k)
≃⊎≡-refl (∈-var x Γ-ctx Γ[x]≡tp-a) = ≃-var x Γ-ctx Γ[x]≡tp-a

-- Types inhabiting interval kinds are proper Types.

Tp∈-⋯-* : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Tp a ∈ b ⋯ c → Γ ⊢Tp a ∈ *
Tp∈-⋯-* a∈b⋯c = ∈-⇑ (∈-s-i a∈b⋯c) (<∷-⋯ (<:-⊥ a∈b⋯c) (<:-⊤ a∈b⋯c))

-- Well-formedness of the * kind.

*-kd : ∀ {n} {Γ : Ctx n} → Γ ctx → Γ ⊢ * kd
*-kd Γ-ctx = kd-⋯ (∈-⊥-f Γ-ctx) (∈-⊤-f Γ-ctx)

module _ where
  open Substitution

  -- An admissible β-rule for type equality.

  ≃-β : ∀ {n} {Γ : Ctx n} {j a k b} → kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j →
        -- Validity conditions:
        Γ ⊢Tp a [ b ] ∈ k Kind[ b ] → kd j ∷ Γ ⊢ k kd → Γ ⊢ k Kind[ b ] kd →
        Γ ⊢ (Λ j a) · b ≃ a [ b ] ∈ k Kind[ b ]
  ≃-β a∈k b∈j a[b]∈k[b] k-kd k[b]-kd =
    <:-antisym (<:-β₁ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd)
               (<:-β₂ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd)

  -- An admissible η-rule for type equality.

  ≃-η : ∀ {n} {Γ : Ctx n} {a j k} →
        Γ ⊢Tp a ∈ Π j k → Γ ⊢ Λ j (weaken a · var zero) ≃ a ∈ Π j k
  ≃-η a∈Πjk = <:-antisym (<:-η₁ a∈Πjk) (<:-η₂ a∈Πjk)

-- An admissible congruence rule for type equality w.r.t. formation of
-- arrow types.

≃-→ : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂} →
      Γ ⊢ a₁ ≃ a₂ ∈ * → Γ ⊢ b₁ ≃ b₂ ∈ * → Γ ⊢ a₁ ⇒ b₁ ≃ a₂ ⇒ b₂ ∈ *
≃-→ (<:-antisym a₁<:a₂∈* a₂<:a₁∈*) (<:-antisym b₁<:b₂∈* b₂<:b₁∈*) =
  <:-antisym (<:-→ a₂<:a₁∈* b₁<:b₂∈*) (<:-→ a₁<:a₂∈* b₂<:b₁∈*)

-- An admissible congruence rule for type equality w.r.t. operator
-- abstraction.

≃-λ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂ j k} →
      kd j ∷ Γ ⊢ a₁ ≃ a₂ ∈ k → Γ ⊢Tp Λ j₁ a₁ ∈ Π j k → Γ ⊢Tp Λ j₂ a₂ ∈ Π j k →
      Γ ⊢ Λ j₁ a₁ ≃ Λ j₂ a₂ ∈ Π j k
≃-λ (<:-antisym a₁<:a₂∈k a₂<:a₁∈k) Λj₁a₁∈Πjk Λj₂a₂∈Πjk =
  <:-antisym (<:-λ a₁<:a₂∈k Λj₁a₁∈Πjk Λj₂a₂∈Πjk)
             (<:-λ a₂<:a₁∈k Λj₂a₂∈Πjk Λj₁a₁∈Πjk)

-- An admissible subsumption rule for type equality.

≃-⇑ : ∀ {n} {Γ : Ctx n} {a b j k} → Γ ⊢ a ≃ b ∈ j → Γ ⊢ j <∷ k → Γ ⊢ a ≃ b ∈ k
≃-⇑ (<:-antisym a<:b b<:a) j<∷k = <:-antisym (<:-⇑ a<:b j<∷k) (<:-⇑ b<:a j<∷k)

-- The contexts of all the above judgments are well-formed.

mutual

  kd-ctx : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ctx
  kd-ctx (kd-⋯ a∈* b∈*)    = Tp∈-ctx a∈*
  kd-ctx (kd-Π j-kd  k-kd) = kd-ctx j-kd

  Tp∈-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ctx
  Tp∈-ctx (∈-var x Γ-ctx Γ[x]≡kd-k) = Γ-ctx
  Tp∈-ctx (∈-⊥-f Γ-ctx)             = Γ-ctx
  Tp∈-ctx (∈-⊤-f Γ-ctx)             = Γ-ctx
  Tp∈-ctx (∈-∀-f k-kd a∈*)          = kd-ctx k-kd
  Tp∈-ctx (∈-→-f a∈* b∈*)           = Tp∈-ctx a∈*
  Tp∈-ctx (∈-Π-i j-kd a∈k k-kd)     = kd-ctx j-kd
  Tp∈-ctx (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) = Tp∈-ctx a∈Πjk
  Tp∈-ctx (∈-s-i a∈b⋯c)             = Tp∈-ctx a∈b⋯c
  Tp∈-ctx (∈-⇑ a∈j j<∷k)            = Tp∈-ctx a∈j

wf-ctx : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → Γ ctx
wf-ctx (wf-kd k-kd) = kd-ctx k-kd
wf-ctx (wf-tp a∈*)  = Tp∈-ctx a∈*

<:-ctx : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ∈ k → Γ ctx
<:-ctx (<:-refl a∈k)            = Tp∈-ctx a∈k
<:-ctx (<:-trans a<:b∈k b<:c∈k) = <:-ctx a<:b∈k
<:-ctx (<:-β₁ a∈j b∈k a[b]∈k[b] k-kd k[b]-kd) = Tp∈-ctx b∈k
<:-ctx (<:-β₂ a∈j b∈k a[b]∈k[b] k-kd k[b]-kd) = Tp∈-ctx b∈k
<:-ctx (<:-η₁ a∈Πjk) = Tp∈-ctx a∈Πjk
<:-ctx (<:-η₂ a∈Πjk) = Tp∈-ctx a∈Πjk
<:-ctx (<:-⊥ a∈b⋯c)  = Tp∈-ctx a∈b⋯c
<:-ctx (<:-⊤ a∈b⋯c)  = Tp∈-ctx a∈b⋯c
<:-ctx (<:-∀ k₂<∷k₁ a₁<:a₂ ∀k₁a₁∈*) = Tp∈-ctx ∀k₁a₁∈*
<:-ctx (<:-→ a₂<:a₁ b₁<:b₂)         = <:-ctx a₂<:a₁
<:-ctx (<:-λ a₂<:a₁∈Πjk Λa₁k₁∈Πjk Λa₂k₂∈Πjk)        = Tp∈-ctx Λa₁k₁∈Πjk
<:-ctx (<:-· a₂<:a₁∈Πjk b₂≃b₁∈j b₁∈j k-kd k[b₁]-kd) = <:-ctx a₂<:a₁∈Πjk
<:-ctx (<:-⟨| a∈b⋯c)      = Tp∈-ctx a∈b⋯c
<:-ctx (<:-|⟩ a∈b⋯c)      = Tp∈-ctx a∈b⋯c
<:-ctx (<:-⋯-i a<:b∈c⋯d)  = <:-ctx a<:b∈c⋯d
<:-ctx (<:-⇑ a<:b∈j j<∷k) = <:-ctx a<:b∈j

<∷-ctx : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ ctx
<∷-ctx (<∷-⋯ a₂<:a₁ b₁<:b₂)          = <:-ctx a₂<:a₁
<∷-ctx (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) = <∷-ctx j₂<∷j₁

≅-ctx : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ctx
≅-ctx (<∷-antisym j<∷k k<∷j) = <∷-ctx j<∷k

≃-ctx : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ∈ k → Γ ctx
≃-ctx (<:-antisym a<:b∈k b<:a∈k) = <:-ctx a<:b∈k

∈-ctx : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ∈ b → Γ ctx
∈-ctx (∈-tp a∈k)                = Tp∈-ctx a∈k
∈-ctx (∈-var x Γ-ctx Γ[x]≡tp-a) = Γ-ctx

≃⊎≡-ctx : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a ≃⊎≡ b ∈ c → Γ ctx
≃⊎≡-ctx (≃-tp a≃b∈k)              = ≃-ctx a≃b∈k
≃⊎≡-ctx (≃-var x Γ-ctx Γ[x]≡tp-a) = Γ-ctx


----------------------------------------------------------------------
-- Well-kinded/typed substitutions (i.e. substitution lemmas)

-- A shorthand for kindings and typings of Ts by kind or type
-- ascriptions.

TermAscTyping : (ℕ → Set) → Set₁
TermAscTyping T = Typing TermAsc T TermAsc Level.zero

-- Liftings from well-typed Ts to well-typed/kinded terms/types.

LiftTo-∈ : ∀ {T} → TermAscTyping T → Set₁
LiftTo-∈ _⊢T_∈_ = LiftTyped Substitution.termAscTermSubst _⊢_wf _⊢T_∈_ _⊢_∈_

-- Helper lemmas about untyped T-substitutions in raw terms and kinds.

record TypedSubstAppHelpers {T} (rawLift : Lift T Term) : Set where
  open Substitution using (weaken; _[_]; _Kind[_])
  module A = SubstApp rawLift
  module L = Lift     rawLift

  field

    -- Substitutions in kinds and types commute.

    Kind/-sub-↑ : ∀ {m n} k a (σ : Sub T m n) →
                  k Kind[ a ] A.Kind/ σ ≡ (k A.Kind/ σ L.↑) Kind[ a A./ σ ]

    /-sub-↑ : ∀ {m n} b a (σ : Sub T m n) →
              b [ a ] A./ σ ≡ (b A./ σ L.↑) [ a A./ σ ]

    -- Weakening of terms commutes with substitution in terms.

    weaken-/ : ∀ {m n} {σ : Sub T m n} a →
               weaken (a A./ σ) ≡ weaken a A./ σ L.↑

-- Application of generic well-formed T-substitutions to all the
-- judgments.

module TypedSubstApp {T : ℕ → Set} (_⊢T_∈_ : TermAscTyping T)
                     (liftTyped : LiftTo-∈ _⊢T_∈_)
                     (helpers : TypedSubstAppHelpers
                                  (LiftTyped.rawLift liftTyped))
                     where

  open LiftTyped liftTyped renaming (lookup to /∈-lookup)
  open TypedSubstAppHelpers helpers

  -- Lift well-kinded Ts to well-kinded types.

  liftTp : ∀ {n} {Γ : Ctx n} {a k kd-k} →
           kd-k ≡ kd k → Γ ⊢T a ∈ kd-k → Γ ⊢Tp L.lift a ∈ k
  liftTp refl a∈kd-k with ∈-lift a∈kd-k
  liftTp refl a∈kd-k | ∈-tp a∈k = a∈k

  mutual

    -- Substitutions preserve well-formedness of kinds and
    -- well-kindedness of types.

    kd-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k σ} →
           Γ ⊢ k kd → Δ ⊢/ σ ∈ Γ → Δ ⊢ k A.Kind/ σ kd
    kd-/ (kd-⋯ a∈* b∈*)   σ∈Γ = kd-⋯ (Tp∈-/ a∈* σ∈Γ) (Tp∈-/ b∈* σ∈Γ)
    kd-/ (kd-Π j-kd k-kd) σ∈Γ =
      kd-Π j/σ-kd (kd-/ k-kd (∈-↑ (wf-kd j/σ-kd) σ∈Γ))
      where j/σ-kd = kd-/ j-kd σ∈Γ

    Tp∈-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
            Γ ⊢Tp a ∈ k → Δ ⊢/ σ ∈ Γ → Δ ⊢Tp a A./ σ ∈ k A.Kind/ σ
    Tp∈-/ (∈-var x Γ-ctx Γ[x]≡kd-k) σ∈Γ =
      liftTp (cong (_/ _) Γ[x]≡kd-k) (/∈-lookup σ∈Γ x)
    Tp∈-/ (∈-⊥-f Γ-ctx)    σ∈Γ = ∈-⊥-f (/∈-wf σ∈Γ)
    Tp∈-/ (∈-⊤-f Γ-ctx)    σ∈Γ = ∈-⊤-f (/∈-wf σ∈Γ)
    Tp∈-/ (∈-∀-f k-kd a∈*) σ∈Γ =
      ∈-∀-f k/σ-kd (Tp∈-/ a∈* (∈-↑ (wf-kd k/σ-kd) σ∈Γ))
      where k/σ-kd = kd-/ k-kd σ∈Γ
    Tp∈-/ (∈-→-f a∈* b∈*)  σ∈Γ = ∈-→-f (Tp∈-/ a∈* σ∈Γ) (Tp∈-/ b∈* σ∈Γ)
    Tp∈-/ (∈-Π-i j-kd a∈k k-kd) σ∈Γ =
      ∈-Π-i j/σ-kd (Tp∈-/ a∈k σ↑∈j∷Γ) (kd-/ k-kd σ↑∈j∷Γ)
      where
        j/σ-kd = kd-/ j-kd σ∈Γ
        σ↑∈j∷Γ = ∈-↑ (wf-kd j/σ-kd) σ∈Γ
    Tp∈-/ (∈-Π-e {_} {b} {_} {k} a∈Πjk b∈j k-kd k[b]-kd) σ∈Γ =
      subst (_ ⊢Tp _ ∈_) (sym k[b]/σ≡k/σ[b/σ])
            (∈-Π-e (Tp∈-/ a∈Πjk σ∈Γ) (Tp∈-/ b∈j σ∈Γ)
                   (kd-/ k-kd (∈-↑ (kd-/-wf k-kd σ∈Γ) σ∈Γ))
                   (subst (_ ⊢_kd) k[b]/σ≡k/σ[b/σ] (kd-/ k[b]-kd σ∈Γ)))
      where k[b]/σ≡k/σ[b/σ] = Kind/-sub-↑ k b _
    Tp∈-/ (∈-s-i a∈b⋯c)  σ∈Γ = ∈-s-i (Tp∈-/ a∈b⋯c σ∈Γ)
    Tp∈-/ (∈-⇑ a∈j j<∷k) σ∈Γ = ∈-⇑ (Tp∈-/ a∈j σ∈Γ) (<∷-/ j<∷k σ∈Γ)

    -- Substitutions commute with subkinding, subtyping and type
    -- equality.

    <∷-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
           Γ ⊢ j <∷ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ j A.Kind/ σ <∷ k A.Kind/ σ
    <∷-/ (<∷-⋯ a₂<:a₁ b₁<:b₂) σ∈Γ = <∷-⋯ (<:-/ a₂<:a₁ σ∈Γ) (<:-/ b₁<:b₂ σ∈Γ)
    <∷-/ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) σ∈Γ =
      <∷-Π (<∷-/ j₂<∷j₁ σ∈Γ) (<∷-/ k₁<∷k₂ (∈-↑ (<∷-/-wf k₁<∷k₂ σ∈Γ) σ∈Γ))
           (kd-/ Πj₁k₁-kd σ∈Γ)

    <:-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b k σ} →
           Γ ⊢ a <: b ∈ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A./ σ <: b A./ σ ∈ k A.Kind/ σ
    <:-/ (<:-refl a∈k)            σ∈Γ = <:-refl (Tp∈-/ a∈k σ∈Γ)
    <:-/ (<:-trans a<:b∈k b<:c∈k) σ∈Γ =
      <:-trans (<:-/ a<:b∈k σ∈Γ) (<:-/ b<:c∈k σ∈Γ)
    <:-/ (<:-β₁ {j} {a} {k} {b} a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) σ∈Γ =
      subst₂ (_ ⊢ (Λ j a) · b A./ _ <:_∈_)
             (sym a[b]/σ≡a/σ[b/σ]) (sym k[b]/σ≡k/σ[b/σ])
             (<:-β₁ (Tp∈-/ a∈k σ↑∈j∷Γ) (Tp∈-/ b∈j σ∈Γ)
                    (subst₂ (_ ⊢Tp_∈_) a[b]/σ≡a/σ[b/σ] k[b]/σ≡k/σ[b/σ]
                            (Tp∈-/ a[b]∈k[b] σ∈Γ))
                    (kd-/ k-kd σ↑∈j∷Γ)
                    (subst (_ ⊢_kd) k[b]/σ≡k/σ[b/σ] (kd-/ k[b]-kd σ∈Γ)))
      where
        σ↑∈j∷Γ          = ∈-↑ (Tp∈-/-wf a∈k σ∈Γ) σ∈Γ
        k[b]/σ≡k/σ[b/σ] = Kind/-sub-↑ k b _
        a[b]/σ≡a/σ[b/σ] = /-sub-↑ a b _
    <:-/ (<:-β₂ {j} {a} {k} {b} a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) σ∈Γ =
      subst₂ (_ ⊢_<: (Λ j a) · b A./ _ ∈_)
             (sym a[b]/σ≡a/σ[b/σ]) (sym k[b]/σ≡k/σ[b/σ])
             (<:-β₂ (Tp∈-/ a∈k σ↑∈j∷Γ) (Tp∈-/ b∈j σ∈Γ)
                    (subst₂ (_ ⊢Tp_∈_) a[b]/σ≡a/σ[b/σ] k[b]/σ≡k/σ[b/σ]
                            (Tp∈-/ a[b]∈k[b] σ∈Γ))
                    (kd-/ k-kd σ↑∈j∷Γ)
                    (subst (_ ⊢_kd) k[b]/σ≡k/σ[b/σ] (kd-/ k[b]-kd σ∈Γ)))
      where
        σ↑∈j∷Γ          = ∈-↑ (Tp∈-/-wf a∈k σ∈Γ) σ∈Γ
        k[b]/σ≡k/σ[b/σ] = Kind/-sub-↑ k b _
        a[b]/σ≡a/σ[b/σ] = /-sub-↑ a b _
    <:-/ {Δ = Δ} {σ = σ} (<:-η₁ {a} {j} {k} a∈Πjk) σ∈Γ =
      subst (Δ ⊢_<: a A./ σ ∈ Π j k A.Kind/ σ)
            (cong (Λ _) (cong₂ _·_ (weaken-/ a) (sym (lift-var zero))))
            (<:-η₁ (Tp∈-/ a∈Πjk σ∈Γ))
    <:-/ {Δ = Δ} {σ = σ} (<:-η₂  {a} {j} {k} a∈Πjk) σ∈Γ =
      subst (Δ ⊢ a A./ σ <:_∈ Π j k A.Kind/ σ)
            (cong (Λ _) (cong₂ _·_ (weaken-/ a) (sym (lift-var zero))))
            (<:-η₂ (Tp∈-/ a∈Πjk σ∈Γ))
    <:-/ (<:-⊥ a∈b⋯c) σ∈Γ = <:-⊥ (Tp∈-/ a∈b⋯c σ∈Γ)
    <:-/ (<:-⊤ a∈b⋯c) σ∈Γ = <:-⊤ (Tp∈-/ a∈b⋯c σ∈Γ)
    <:-/ (<:-∀ k₂<∷k₁ a₁<:a₂∈* ∀j₁k₁∈*) σ∈Γ =
      <:-∀ (<∷-/ k₂<∷k₁ σ∈Γ) (<:-/ a₁<:a₂∈* (∈-↑ (<:-/-wf a₁<:a₂∈* σ∈Γ) σ∈Γ))
           (Tp∈-/ ∀j₁k₁∈* σ∈Γ)
    <:-/ (<:-→ a₂<:a₁∈* b₁<:b₂∈*) σ∈Γ =
      <:-→ (<:-/ a₂<:a₁∈* σ∈Γ) (<:-/ b₁<:b₂∈* σ∈Γ)
    <:-/ (<:-λ a₁<:a₂∈k Λj₁a₁∈Πjk Λj₂a₂∈Πjk) σ∈Γ =
      <:-λ (<:-/ a₁<:a₂∈k (∈-↑ (<:-/-wf a₁<:a₂∈k σ∈Γ) σ∈Γ))
           (Tp∈-/ Λj₁a₁∈Πjk σ∈Γ) (Tp∈-/ Λj₂a₂∈Πjk σ∈Γ)
    <:-/ (<:-· {k = k} a₁<:a₂∈Πjk b₁≃b₂∈j b₁∈j k-kd k[b₁]-kd) σ∈Γ =
      subst (_ ⊢ _ <: _ ∈_) (sym k[b₁]/σ≡k/σ[b₁/σ])
            (<:-· (<:-/ a₁<:a₂∈Πjk σ∈Γ) (≃-/ b₁≃b₂∈j σ∈Γ)
                  (Tp∈-/ b₁∈j σ∈Γ) (kd-/ k-kd (∈-↑ (kd-/-wf k-kd σ∈Γ) σ∈Γ))
                  (subst (_ ⊢_kd) k[b₁]/σ≡k/σ[b₁/σ] (kd-/ k[b₁]-kd σ∈Γ)))
      where k[b₁]/σ≡k/σ[b₁/σ] = Kind/-sub-↑ k _ _
    <:-/ (<:-⟨| a∈b⋯c)      σ∈Γ = <:-⟨| (Tp∈-/ a∈b⋯c σ∈Γ)
    <:-/ (<:-|⟩ a∈b⋯c)      σ∈Γ = <:-|⟩ (Tp∈-/ a∈b⋯c σ∈Γ)
    <:-/ (<:-⋯-i a<:b∈c⋯d)  σ∈Γ = <:-⋯-i (<:-/ a<:b∈c⋯d σ∈Γ)
    <:-/ (<:-⇑ a<:b∈j j<∷k) σ∈Γ = <:-⇑ (<:-/ a<:b∈j σ∈Γ) (<∷-/ j<∷k σ∈Γ)

    ≃-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b k σ} →
          Γ ⊢ a ≃ b ∈ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A./ σ ≃ b A./ σ ∈ k A.Kind/ σ
    ≃-/ (<:-antisym a<:b∈k b<:a∈k) σ∈Γ =
      <:-antisym (<:-/ a<:b∈k σ∈Γ) (<:-/ b<:a∈k σ∈Γ)

    -- Helpers (to satisfy the termination checker).

    kd-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
              kd j ∷ Γ ⊢ k kd → Δ ⊢/ σ ∈ Γ → Δ ⊢ kd (j A.Kind/ σ) wf
    kd-/-wf (kd-⋯ a∈* _)  σ∈Γ = Tp∈-/-wf a∈* σ∈Γ
    kd-/-wf (kd-Π j-kd _) σ∈Γ = kd-/-wf j-kd σ∈Γ

    Tp∈-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
               kd j ∷ Γ ⊢Tp a ∈ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ kd (j A.Kind/ σ) wf
    Tp∈-/-wf (∈-var x (wf-kd k-kd ∷ Γ-ctx) _) σ∈Γ = wf-kd (kd-/ k-kd σ∈Γ)
    Tp∈-/-wf (∈-⊥-f (wf-kd j-kd ∷ Γ-ctx)) σ∈Γ = wf-kd (kd-/ j-kd σ∈Γ)
    Tp∈-/-wf (∈-⊤-f (wf-kd j-kd ∷ Γ-ctx)) σ∈Γ = wf-kd (kd-/ j-kd σ∈Γ)
    Tp∈-/-wf (∈-∀-f k-kd _)      σ∈Γ = kd-/-wf k-kd σ∈Γ
    Tp∈-/-wf (∈-→-f a∈* _)       σ∈Γ = Tp∈-/-wf a∈* σ∈Γ
    Tp∈-/-wf (∈-Π-i j-kd _ _)    σ∈Γ = kd-/-wf j-kd σ∈Γ
    Tp∈-/-wf (∈-Π-e a∈Πjk _ _ _) σ∈Γ = Tp∈-/-wf a∈Πjk σ∈Γ
    Tp∈-/-wf (∈-s-i a∈b⋯c)       σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    Tp∈-/-wf (∈-⇑ a∈b _)         σ∈Γ = Tp∈-/-wf a∈b σ∈Γ

    <:-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j k σ} →
              kd j ∷ Γ ⊢ a <: b ∈ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ kd (j A.Kind/ σ) wf
    <:-/-wf (<:-refl a∈k)        σ∈Γ = Tp∈-/-wf a∈k σ∈Γ
    <:-/-wf (<:-trans a<:b _)    σ∈Γ = <:-/-wf a<:b σ∈Γ
    <:-/-wf (<:-β₁ _ b∈j _ _ _)  σ∈Γ = Tp∈-/-wf b∈j σ∈Γ
    <:-/-wf (<:-β₂ _ b∈j _ _ _)  σ∈Γ = Tp∈-/-wf b∈j σ∈Γ
    <:-/-wf (<:-η₁ a∈Πjk)        σ∈Γ = Tp∈-/-wf a∈Πjk σ∈Γ
    <:-/-wf (<:-η₂ a∈Πjk)        σ∈Γ = Tp∈-/-wf a∈Πjk σ∈Γ
    <:-/-wf (<:-⊥ a∈b⋯c)         σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    <:-/-wf (<:-⊤ a∈b⋯c)         σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    <:-/-wf (<:-∀ j₂<∷j₁ _ _)    σ∈Γ = <∷-/-wf j₂<∷j₁ σ∈Γ
    <:-/-wf (<:-→ a₂<:a₁∈* _)    σ∈Γ = <:-/-wf a₂<:a₁∈* σ∈Γ
    <:-/-wf (<:-λ _ Λj₁a₂∈Πjk _) σ∈Γ = Tp∈-/-wf Λj₁a₂∈Πjk σ∈Γ
    <:-/-wf (<:-· a₁<:a₂∈Πjk _ _ _ _) σ∈Γ = <:-/-wf a₁<:a₂∈Πjk σ∈Γ
    <:-/-wf (<:-⟨| a∈b⋯c)        σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    <:-/-wf (<:-|⟩ a∈b⋯c)        σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    <:-/-wf (<:-⋯-i a<:b∈c⋯d)    σ∈Γ = <:-/-wf a<:b∈c⋯d σ∈Γ
    <:-/-wf (<:-⇑ a<:b∈k _)      σ∈Γ = <:-/-wf a<:b∈k σ∈Γ

    <∷-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k l σ} →
              kd j ∷ Γ ⊢ k <∷ l → Δ ⊢/ σ ∈ Γ → Δ ⊢ kd (j A.Kind/ σ) wf
    <∷-/-wf (<∷-⋯ j₂<:j₁ _)   σ∈Γ = <:-/-wf j₂<:j₁ σ∈Γ
    <∷-/-wf (<∷-Π j₂<∷j₁ _ _) σ∈Γ = <∷-/-wf j₂<∷j₁ σ∈Γ

  -- Substitutions preserve well-formedness of ascriptions.

  wf-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a σ} →
         Γ ⊢ a wf → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A.TermAsc/ σ wf
  wf-/ (wf-kd k-kd) σ∈Γ = wf-kd (kd-/ k-kd σ∈Γ)
  wf-/ (wf-tp a∈b)  σ∈Γ = wf-tp (Tp∈-/ a∈b σ∈Γ)

  -- Substitutions commute with kind equality.

  ≅-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
        Γ ⊢ j ≅ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ j A.Kind/ σ ≅ k A.Kind/ σ
  ≅-/ (<∷-antisym j<∷k k<∷j) σ∈Γ = <∷-antisym (<∷-/ j<∷k σ∈Γ) (<∷-/ k<∷j σ∈Γ)

  -- Substitutions preserve well-kindedness and well-typedness.

  ∈-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
        Γ ⊢ a ∈ b → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A./ σ ∈ b A.TermAsc/ σ
  ∈-/ (∈-tp a∈b)                σ∈Γ = ∈-tp (Tp∈-/ a∈b σ∈Γ)
  ∈-/ (∈-var x Γ-ctx Γ[x]≡tp-a) σ∈Γ =
    subst (_ ⊢ _ ∈_) (cong (A._TermAsc/ _) Γ[x]≡tp-a)
          (∈-lift (/∈-lookup σ∈Γ x))

  -- Substitutions preserve type and syntactic term equality.

  ≃⊎≡-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b c σ} →
          Γ ⊢ a ≃⊎≡ b ∈ c → Δ ⊢/ σ ∈ Γ →
          Δ ⊢ a A./ σ ≃⊎≡ b A./ σ ∈ c A.TermAsc/ σ
  ≃⊎≡-/ (≃-tp a≃b∈k) σ∈Γ              = ≃-tp (≃-/ a≃b∈k σ∈Γ)
  ≃⊎≡-/ (≃-var x Γ-ctx Γ[x]≡tp-a) σ∈Γ =
    let x/σ∈tp-a/σ = subst (_ ⊢ _ ∈_) (cong (A._TermAsc/ _) Γ[x]≡tp-a)
                           (∈-lift (/∈-lookup σ∈Γ x))
    in ≃⊎≡-refl x/σ∈tp-a/σ

-- Well-kinded type substitutions.

module KindedSubstitution where
  open Substitution           using (simple; termSubst)
  open SimpleExt    simple    using (extension)
  open TermSubst    termSubst using (varLift; termLift)

  private
    module S  = Substitution
    module KL = TermLikeLemmas S.termLikeLemmasKind

  -- Helper lemmas about untyped renamings and substitutions in terms
  -- and kinds.

  varHelpers : TypedSubstAppHelpers varLift
  varHelpers = record
    { Kind/-sub-↑ = KL./-sub-↑
    ; /-sub-↑     = LiftSubLemmas./-sub-↑ S.varLiftSubLemmas
    ; weaken-/    = LiftAppLemmas.wk-commutes S.varLiftAppLemmas
    }

  termHelpers : TypedSubstAppHelpers termLift
  termHelpers = record
    { Kind/-sub-↑ = λ k _ _ → KL.sub-commutes k
    ; /-sub-↑     = λ a _ _ → S.sub-commutes a
    ; weaken-/    = S.weaken-/
    }

  -- Kinded type substitutions.

  typedTermSubst : TypedTermSubst TermAsc Term Level.zero TypedSubstAppHelpers
  typedTermSubst = record
    { _⊢_wf = _⊢_wf
    ; _⊢_∈_ = _⊢_∈_
    ; termLikeLemmas = S.termLikeLemmasTermAsc
    ; varHelpers     = varHelpers
    ; termHelpers    = termHelpers
    ; wf-wf    = wf-ctx
    ; ∈-wf     = ∈-ctx
    ; ∈-var    = ∈-var′
    ; typedApp = TypedSubstApp.∈-/
    }
  open TypedTermSubst typedTermSubst public
    hiding (_⊢_wf; _⊢_∈_; varHelpers; termHelpers; ∈-var; ∈-/Var; ∈-/)
    renaming (lookup to /∈-lookup)
  open TypedSubstApp _⊢Var_∈_ varLiftTyped varHelpers public using () renaming
    ( wf-/  to wf-/Var
    ; kd-/  to kd-/Var
    ; Tp∈-/ to Tp∈-/Var
    ; <∷-/  to <∷-/Var
    ; <:-/  to <:-/Var
    ; ∈-/   to ∈-/Var
    ; ≃⊎≡-/ to ≃⊎≡-/Var
    )
  open Substitution using (weaken; weakenKind; weakenTermAsc)

  -- Weakening preserves the various judgments.

  wf-weaken : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a wf → Γ ⊢ b wf →
              (a ∷ Γ) ⊢ weakenTermAsc b wf
  wf-weaken a-wf b-wf = wf-/Var b-wf (Var∈-wk a-wf)

  kd-weaken : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢ a wf → Γ ⊢ k kd →
              (a ∷ Γ) ⊢ weakenKind k kd
  kd-weaken a-wf k-kd = kd-/Var k-kd (Var∈-wk a-wf)

  Tp∈-weaken : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a wf → Γ ⊢Tp b ∈ k →
               (a ∷ Γ) ⊢Tp weaken b ∈ weakenKind k
  Tp∈-weaken a-wf b∈k = Tp∈-/Var b∈k (Var∈-wk a-wf)

  <∷-weaken : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢ a wf → Γ ⊢ j <∷ k →
              (a ∷ Γ) ⊢ weakenKind j <∷ weakenKind k
  <∷-weaken a-wf j<∷k = <∷-/Var j<∷k (Var∈-wk a-wf)

  <:-weaken : ∀ {n} {Γ : Ctx n} {a b c k} → Γ ⊢ a wf → Γ ⊢ b <: c ∈ k →
              (a ∷ Γ) ⊢ weaken b <: weaken c ∈ weakenKind k
  <:-weaken a-wf b<:c∈k = <:-/Var b<:c∈k (Var∈-wk a-wf)

  ∈-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b ∈ c →
             (a ∷ Γ) ⊢ weaken b ∈ weakenTermAsc c
  ∈-weaken a-wf b∈c = ∈-/Var b∈c (Var∈-wk a-wf)

  -- Weakening preserves type and syntactic term equality.

  ≃⊎≡-weaken : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a wf → Γ ⊢ b ≃⊎≡ c ∈ d →
               (a ∷ Γ) ⊢ weaken b ≃⊎≡ weaken c ∈ weakenTermAsc d
  ≃⊎≡-weaken a-wf b≃⊎≡c∈d = ≃⊎≡-/Var b≃⊎≡c∈d (Var∈-wk a-wf)

  open TypedSubstApp _⊢_∈_ termLiftTyped termHelpers public
  open Substitution using (_/_; _Kind/_; id; sub; _↑⋆_; _[_]; _Kind[_])

  -- Substitution of a single well-typed term or well-kinded type
  -- preserves the various judgments.

  kd-[] : ∀ {n} {Γ : Ctx n} {a b k} →
          b ∷ Γ ⊢ k kd → Γ ⊢ a ∈ b → Γ ⊢ k Kind[ a ] kd
  kd-[] k-kd a∈b = kd-/ k-kd (∈-sub a∈b)

  ≅-[] : ∀ {n} {Γ : Ctx n} {j k a b} →
         b ∷ Γ ⊢ j ≅ k → Γ ⊢ a ∈ b → Γ ⊢ j Kind[ a ] ≅ k Kind[ a ]
  ≅-[] j≅k a∈b = ≅-/ j≅k (∈-sub a∈b)

  Tp∈-[] : ∀ {n} {Γ : Ctx n} {a b k c} →
           c ∷ Γ ⊢Tp a ∈ k → Γ ⊢ b ∈ c → Γ ⊢Tp a [ b ] ∈ k Kind[ b ]
  Tp∈-[] a∈k b∈c = Tp∈-/ a∈k (∈-sub b∈c)

  -- Context narrowing.

  -- A typed substitution that narrows the kind of the first type
  -- variable.

  ∈-<∷-sub : ∀ {n} {Γ : Ctx n} {j k} →
             Γ ⊢ j kd → Γ ⊢ j <∷ k → kd j ∷ Γ ⊢/ id ∈ kd k ∷ Γ
  ∈-<∷-sub j-kd j<∷k =
    ∈-tsub (∈-tp (∈-⇑ (∈-var zero (j-wf ∷ Γ-ctx) refl) (<∷-weaken j-wf j<∷k)))
    where
      j-wf  = wf-kd j-kd
      Γ-ctx = kd-ctx j-kd

  -- Narrowing the kind of the first type variable preserves
  -- well-formedness of kinds.

  ⇓-kd : ∀ {n} {Γ : Ctx n} {j₁ j₂ k} →
         Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ k kd → kd j₁ ∷ Γ ⊢ k kd
  ⇓-kd j₁-kd j₁<∷j₂ k-kd =
    subst (_ ⊢_kd) (KL.id-vanishes _) (kd-/ k-kd (∈-<∷-sub j₁-kd j₁<∷j₂))

  -- Narrowing the kind of the first type variable preserves
  -- well-kindedness.

  ⇓-Tp∈ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a k} →
          Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢Tp a ∈ k → kd j₁ ∷ Γ ⊢Tp a ∈ k
  ⇓-Tp∈ j₁-kd j₁<∷j₂ a∈k =
    subst₂ (_ ⊢Tp_∈_) (S.id-vanishes _) (KL.id-vanishes _)
           (Tp∈-/ a∈k (∈-<∷-sub j₁-kd j₁<∷j₂))

  -- Narrowing the kind of the first type variable preserves
  -- subkinding and subtyping.

  ⇓-<∷ : ∀ {n} {Γ : Ctx n} {j₁ j₂ k₁ k₂} →
         Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ k₁ <∷ k₂ → kd j₁ ∷ Γ ⊢ k₁ <∷ k₂
  ⇓-<∷ j₁-kd j₁<∷j₂ k₁<∷k₂ =
    subst₂ (_ ⊢_<∷_) (KL.id-vanishes _) (KL.id-vanishes _)
           (<∷-/ k₁<∷k₂ (∈-<∷-sub j₁-kd j₁<∷j₂))

  ⇓-<: : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂ k} →
         Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ a₁ <: a₂ ∈ k →
         kd j₁ ∷ Γ ⊢ a₁ <: a₂ ∈ k
  ⇓-<: j₁-kd j₁<∷j₂ a₁<:a₂∈k =
    subst (_ ⊢ _ <: _ ∈_) (KL.id-vanishes _)
          (subst₂ (_ ⊢_<:_∈ _) (S.id-vanishes _) (S.id-vanishes _)
                  (<:-/ a₁<:a₂∈k (∈-<∷-sub j₁-kd j₁<∷j₂)))

-- Operations on well-formed contexts that require weakening of
-- well-formedness judgments.

module WfCtxOps where
  wfWeakenOps : WellFormedWeakenOps weakenOps
  wfWeakenOps = record { wf-weaken = KindedSubstitution.wf-weaken }

  open WellFormedWeakenOps wfWeakenOps public renaming (lookup to lookup-wf)

  -- Lookup the kind of a type variable in a well-formed context.

  lookup-kd : ∀ {m} {Γ : Ctx m} {k} x →
              Γ ctx → TermCtx.lookup Γ x ≡ kd k → Γ ⊢ k kd
  lookup-kd x Γ-ctx Γ[x]≡kd-k =
    wf-kd-inv (subst (_ ⊢_wf) Γ[x]≡kd-k (lookup-wf Γ-ctx x))

open KindedSubstitution
open WfCtxOps

-- Transitivity of subkinding.

<∷-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j <∷ k → Γ ⊢ k <∷ l → Γ ⊢ j <∷ l
<∷-trans (<∷-⋯ a₂<:a₁ b₁<:b₂) (<∷-⋯ a₃<:a₂ b₂<:b₃) =
  <∷-⋯ (<:-trans a₃<:a₂ a₂<:a₁) (<:-trans b₁<:b₂ b₂<:b₃)
<∷-trans (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) (<∷-Π j₃<∷j₂ k₂<∷k₃ Πj₂k₂-kd) =
  <∷-Π (<∷-trans j₃<∷j₂ j₂<∷j₁)
       (<∷-trans (⇓-<∷ (wf-kd-inv (wf-∷₁ (<∷-ctx k₂<∷k₃))) j₃<∷j₂ k₁<∷k₂)
                 k₂<∷k₃)
       Πj₁k₁-kd

-- Transitivity of kind equality.

≅-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j ≅ k → Γ ⊢ k ≅ l → Γ ⊢ j ≅ l
≅-trans (<∷-antisym k₁<∷k₂ k₂<∷k₁) (<∷-antisym k₂<∷k₃ k₃<∷k₂) =
  <∷-antisym (<∷-trans k₁<∷k₂ k₂<∷k₃) (<∷-trans k₃<∷k₂ k₂<∷k₁)


----------------------------------------------------------------------
-- Well-formed equality lifted to substitutions

module WfSubstitutionEquality where
  open Substitution        hiding (subst)
  open TermSubst termSubst using  (termLift)
  open ZipUnzipSimple simple simple
  open TypedSubstAppHelpers KindedSubstitution.termHelpers
  private
    module KL = TermLikeLemmas termLikeLemmasKind
    module AL = TermLikeLemmas termLikeLemmasTermAsc
    module S  = SimpleExt simple
    module Z  = SimpleExt zippedSimple

  -- Well-formed equal substitutions: pairs of substitutions that are
  -- point-wise equal.

  wfEqSub : TypedSubRel TermAsc Term Level.zero
  wfEqSub = record
    { typedRelation       = record { _⊢_wf = _⊢_wf ; _⊢_∼_∈_ = _⊢_≃⊎≡_∈_ }
    ; typeExtension       = TermCtx.weakenOps
    ; typeTermApplication = record { _/_ = λ a ρσ → a TermAsc/ (π₁ ρσ) }
    ; termSimple          = simple
    }
  open TypedSubRel wfEqSub public using ()
    renaming (_⊢/_∼_∈_ to _⊢/_≃_∈_)

  -- Simple substitutions of well-formed equal terms and types.

  wfEqWeakenOps : TypedRelWeakenOps wfEqSub
  wfEqWeakenOps = record
    { ∼∈-weaken  = ≃⊎≡-weaken
    ; ∼∈-wf      = ≃⊎≡-ctx
    ; /-wk       = /-wk-π₁
    ; /-weaken   = λ {m} {n} {στ} a → /-weaken-π₁ {m} {n} {στ} a
    ; weaken-/-∷ = AL.weaken-/-∷
    }
    where
      open ≡-Reasoning

      /-wk-π₁ : ∀ {n} {a : TermAsc n} → a TermAsc/ π₁ Z.wk ≡ weakenTermAsc a
      /-wk-π₁ {_} {a} = begin
        a TermAsc/ π₁ Z.wk   ≡⟨ cong ((a TermAsc/_) ∘ proj₁) (sym wk-unzip) ⟩
        a TermAsc/ wk        ≡⟨ AL./-wk ⟩
        weakenTermAsc a      ∎

      /-weaken-π₁ : ∀ {m n} {στ : Sub (Term ⊗ Term) m n} a →
                    a TermAsc/ π₁ (Vec.map Z.weaken στ) ≡
                      a TermAsc/ π₁ στ TermAsc/ π₁ Z.wk
      /-weaken-π₁ {_} {_} {στ} a = begin
          a TermAsc/ π₁ (Vec.map Z.weaken στ)
        ≡˘⟨ cong ((a TermAsc/_) ∘ proj₁) (map-weaken-unzip στ) ⟩
          a TermAsc/ Vec.map S.weaken (π₁ στ)
        ≡⟨ AL./-weaken a ⟩
          a TermAsc/ π₁ στ TermAsc/ S.wk
        ≡⟨ cong ((a TermAsc/ π₁ στ TermAsc/_) ∘ proj₁) wk-unzip ⟩
          a TermAsc/ π₁ στ TermAsc/ π₁ Z.wk
        ∎

  wfEqSimple : TypedRelSimple wfEqSub
  wfEqSimple = record
    { typedRelWeakenOps = wfEqWeakenOps
    ; ∼∈-var            = ≃⊎≡-var
    ; wf-wf             = wf-ctx
    ; id-vanishes       = id-vanishes-π₁
    }
    where
      open TypedRelWeakenOps wfEqWeakenOps
      open ≡-Reasoning

      id-vanishes-π₁ : ∀ {n} (a : TermAsc n) → a TermAsc/ π₁ Z.id ≡ a
      id-vanishes-π₁ a = begin
        a TermAsc/ π₁ Z.id   ≡⟨ cong ((a TermAsc/_) ∘ proj₁) (sym id-unzip) ⟩
        a TermAsc/ id        ≡⟨ AL.id-vanishes a ⟩
        a                    ∎

  open TypedRelSimple wfEqSimple public
    hiding (typedRelWeakenOps; ∼∈-var; ∼∈-weaken; ∼∈-wf; wf-wf)
    renaming (lookup to ≃-lookup)

  infixl 4  _⊢/_≃′_∈_

  -- An inversion lemma for the generic term/type equality.

  ≃⊎≡-kd-inv : ∀ {n} {Γ : Ctx n} {a b k kd-k} →
               kd-k ≡ kd k → Γ ⊢ a ≃⊎≡ b ∈ kd-k → Γ ⊢ a ≃ b ∈ k
  ≃⊎≡-kd-inv refl (≃-tp a≃b∈k) = a≃b∈k

  -- A 'judgment' that combines equality of a pair of substitutions σ
  -- and ρ with well-formedness of σ and ρ.
  --
  -- NOTE.  By using this combined equality and well-formedness
  -- judgment in the functionality lemmas below we effectively add
  -- extra premises (validity conditions) to the lemmas, thus
  -- weakening them.  We prove stronger versions later when we have
  -- established validity of all the judgments (which uses the weak
  -- version of the functionality lemmas).

  _⊢/_≃′_∈_ : ∀ {m n} → Ctx n → Sub Term m n → Sub Term m n → Ctx m → Set
  Δ ⊢/ σ ≃′ ρ ∈ Γ = Δ ⊢/ σ ∈ Γ × Δ ⊢/ ρ ∈ Γ × Δ ⊢/ σ ≃ ρ ∈ Γ × Δ ⊢/ ρ ≃ σ ∈ Γ

  -- Symmetry of the combined substitution equality judgment.

  ≃′-sym : ∀ {m n Δ Γ} {ρ σ : Sub Term m n} → Δ ⊢/ ρ ≃′ σ ∈ Γ → Δ ⊢/ σ ≃′ ρ ∈ Γ
  ≃′-sym (ρ∈Γ , σ∈Γ , ρ≃σ∈Γ , σ≃ρ∈Γ) = σ∈Γ , ρ∈Γ , σ≃ρ∈Γ , ρ≃σ∈Γ

  -- Lift a pair of equal substitutions over an additional type
  -- variable.

  ≃′-↑ : ∀ {m n Γ Δ} {ρ σ : Sub Term m n} {j k} →
         Δ ⊢ j kd → Δ ⊢ j ≅ k Kind/ ρ → Δ ⊢ j ≅ k Kind/ σ → Δ ⊢/ ρ ≃′ σ ∈ Γ →
         kd j ∷ Δ ⊢/ ρ ↑ ≃′ σ ↑ ∈ kd k ∷ Γ
  ≃′-↑ j-kd j≅k/ρ j≅k/σ (ρ∈Γ , σ∈Γ , ρ≃σ∈ , σ≃ρ∈) =
    ∈-/∷ (∈-tp z∈k/ρ) ρ∈Γ , ∈-/∷ (∈-tp z∈k/σ) σ∈Γ ,
    ∼∈-/∷ (≃-tp (≃-refl z∈k/ρ′)) ρ≃σ∈ , ∼∈-/∷ (≃-tp (≃-refl z∈k/σ′)) σ≃ρ∈
    where
      j-wf    = wf-kd j-kd
      j∷Δ-ctx = j-wf ∷ kd-ctx j-kd
      z∈k/ρ   = ∈-⇑ (∈-var zero j∷Δ-ctx refl) (<∷-weaken j-wf (≅⇒<∷ j≅k/ρ))
      z∈k/σ   = ∈-⇑ (∈-var zero j∷Δ-ctx refl) (<∷-weaken j-wf (≅⇒<∷ j≅k/σ))
      z∈k/ρ′  = subst (_ ⊢Tp _ ∈_)
                      (cong (weakenKind ∘ (_ Kind/_)) (sym (π₁-zip _ _))) z∈k/ρ
      z∈k/σ′  = subst (_ ⊢Tp _ ∈_)
                      (cong (weakenKind ∘ (_ Kind/_)) (sym (π₁-zip _ _))) z∈k/σ

  -- Functionality of substitution (weak versions).
  --
  -- NOTE.  The functionality lemmas proven below are stated in terms
  -- of the combined equality and well-formedness judgment defined
  -- above.  This effectively adds extra premises (validity
  -- conditions) to the lemmas, thus weakening them.  We prove
  -- stronger versions later when we have established validity of all
  -- the judgments (which uses the weak version of the functionality
  -- lemmas).

  mutual

    -- Equal substitutions map well-formed kinds to kind equations.

    kd-/≃ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k ρ σ} →
            Γ ⊢ k kd → Δ ⊢/ ρ ≃′ σ ∈ Γ → Δ ⊢ k Kind/ ρ ≅ k Kind/ σ
    kd-/≃ (kd-⋯ a∈* b∈*)   ρ≃σ∈Γ = ≅-⋯ (Tp∈-/≃ a∈* ρ≃σ∈Γ) (Tp∈-/≃ b∈* ρ≃σ∈Γ)
    kd-/≃ (kd-Π j-kd k-kd) ρ≃σ∈Γ =
      let ρ∈Γ , σ∈Γ , _ = ρ≃σ∈Γ
          j/ρ-kd  = kd-/ j-kd ρ∈Γ
          j/σ-kd  = kd-/ j-kd σ∈Γ
          j/ρ≅j/σ = kd-/≃ j-kd ρ≃σ∈Γ
          k/ρ≅k/σ = kd-/≃ k-kd
                          (≃′-↑ j/σ-kd (≅-sym j/ρ≅j/σ) (≅-refl j/σ-kd) ρ≃σ∈Γ)
          k/σ≅k/ρ = kd-/≃ k-kd
                          (≃′-↑ j/ρ-kd j/ρ≅j/σ (≅-refl j/ρ-kd) (≃′-sym ρ≃σ∈Γ))
          Πjk/ρ-kd = kd-/ (kd-Π j-kd k-kd) ρ∈Γ
          Πjk/σ-kd = kd-/ (kd-Π j-kd k-kd) σ∈Γ
      in <∷-antisym (<∷-Π (≅⇒<∷ (≅-sym j/ρ≅j/σ)) (≅⇒<∷ k/ρ≅k/σ) Πjk/ρ-kd)
                    (<∷-Π (≅⇒<∷ j/ρ≅j/σ) (≅⇒<∷ k/σ≅k/ρ) Πjk/σ-kd)

    -- Equal substitutions map well-kinded types to type equations.

    Tp∈-/≃ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k ρ σ} →
             Γ ⊢Tp a ∈ k → Δ ⊢/ ρ ≃′ σ ∈ Γ → Δ ⊢ a / ρ ≃ a / σ ∈ k Kind/ ρ
    Tp∈-/≃ {ρ = ρ} {σ} (∈-var x Γ-ctx Γ[x]≡kd-k) (_ , _ , ρ≃σ∈Γ , _) =
      (≃⊎≡-kd-inv (cong (_TermAsc/ ρ) Γ[x]≡kd-k)
                  (subst (_ ⊢ _ ≃⊎≡ _ ∈_)
                         (cong (_ TermAsc/_) (π₁-zip ρ σ))
                         (≃-lookup ρ≃σ∈Γ x)))
    Tp∈-/≃ (∈-⊥-f Γ-ctx) (ρ∈Γ , _) = ≃-refl (∈-⊥-f (/∈-wf ρ∈Γ))
    Tp∈-/≃ (∈-⊤-f Γ-ctx) (ρ∈Γ , _) = ≃-refl (∈-⊤-f (/∈-wf ρ∈Γ))
    Tp∈-/≃ (∈-∀-f k-kd a∈*) ρ≃σ∈Γ =
      let ρ∈Γ , σ∈Γ , _ = ρ≃σ∈Γ
          k/ρ-kd    = kd-/ k-kd ρ∈Γ
          k/σ-kd    = kd-/ k-kd σ∈Γ
          k/ρ≅k/σ   = kd-/≃ k-kd ρ≃σ∈Γ
          a/ρ≃a/σ∈* = Tp∈-/≃ a∈* (≃′-↑ k/σ-kd (≅-sym k/ρ≅k/σ)
                                       (≅-refl k/σ-kd) ρ≃σ∈Γ)
          a/σ≃a/ρ∈* = Tp∈-/≃ a∈* (≃′-↑ k/ρ-kd k/ρ≅k/σ
                                       (≅-refl k/ρ-kd) (≃′-sym ρ≃σ∈Γ))
          ∀ka/ρ∈*   = Tp∈-/ (∈-∀-f k-kd a∈*) ρ∈Γ
          ∀ka/σ∈*   = Tp∈-/ (∈-∀-f k-kd a∈*) σ∈Γ
      in <:-antisym (<:-∀ (≅⇒<∷ (≅-sym k/ρ≅k/σ)) (≃⇒<: a/ρ≃a/σ∈*) ∀ka/ρ∈*)
                    (<:-∀ (≅⇒<∷ k/ρ≅k/σ) (≃⇒<: a/σ≃a/ρ∈*) ∀ka/σ∈*)
    Tp∈-/≃ (∈-→-f a∈* b∈*) ρ≃σ∈Γ = ≃-→ (Tp∈-/≃ a∈* ρ≃σ∈Γ) (Tp∈-/≃ b∈* ρ≃σ∈Γ)
    Tp∈-/≃ (∈-Π-i j-kd a∈k k-kd) ρ≃σ∈Γ =
      let ρ∈Γ , σ∈Γ , _ = ρ≃σ∈Γ
          j/ρ-kd        = kd-/ j-kd ρ∈Γ
          j/σ-kd        = kd-/ j-kd σ∈Γ
          j/ρ≅j/σ       = kd-/≃ j-kd ρ≃σ∈Γ
          ρ↑∈j∷Γ        = ∈-↑ (wf-kd j/ρ-kd) ρ∈Γ
          σ↑∈j∷Γ        = ∈-↑ (wf-kd j/σ-kd) σ∈Γ
          ρ↑≃σ↑∈j∷Γ     = ≃′-↑ j/ρ-kd (≅-refl j/ρ-kd) j/ρ≅j/σ ρ≃σ∈Γ
          a/ρ∈k/ρ       = Tp∈-/ a∈k ρ↑∈j∷Γ
          a/σ∈k/σ       = Tp∈-/ a∈k σ↑∈j∷Γ
          a/ρ≃a/σ∈k/ρ   = Tp∈-/≃ a∈k ρ↑≃σ↑∈j∷Γ
          k/ρ-kd        = kd-/ k-kd ρ↑∈j∷Γ
          k/σ-kd        = kd-/ k-kd σ↑∈j∷Γ
          k/ρ≅k/σ       = kd-/≃ k-kd ρ↑≃σ↑∈j∷Γ
          Λja/ρ∈Πjk/ρ   = ∈-Π-i j/ρ-kd a/ρ∈k/ρ k/ρ-kd
          Πjk/σ<∷Πjk/ρ  = <∷-Π (≅⇒<∷ j/ρ≅j/σ) (≅⇒<∷ (≅-sym k/ρ≅k/σ))
                               (kd-Π j/σ-kd k/σ-kd)
          Λja/σ∈Πjk/ρ   = ∈-⇑ (∈-Π-i j/σ-kd a/σ∈k/σ k/σ-kd) Πjk/σ<∷Πjk/ρ
      in ≃-λ a/ρ≃a/σ∈k/ρ Λja/ρ∈Πjk/ρ Λja/σ∈Πjk/ρ
    Tp∈-/≃ (∈-Π-e {k = k} a∈Πjk b∈j k-kd k[b]-kd) ρ≃σ∈Γ =
      let k[b]/ρ≡k/ρ[b/ρ] = Kind/-sub-↑ k _ _
          k[b]/σ≡k/σ[b/σ] = Kind/-sub-↑ k _ _
          ρ∈Γ , σ∈Γ , _ = ρ≃σ∈Γ
          j-wf          = wf-∷₁ (kd-ctx k-kd)
          j-kd          = wf-kd-inv j-wf
          j/σ≅j/ρ       = kd-/≃-≅ k-kd (≃′-sym ρ≃σ∈Γ)
          j/σ-kd        = kd-/ j-kd σ∈Γ
          ρ↑≃σ↑∈j∷Γ     = ≃′-↑ j/σ-kd j/σ≅j/ρ (≅-refl j/σ-kd) ρ≃σ∈Γ
          ρ↑∈j∷Γ        = (∈-↑ (wf-/ j-wf ρ∈Γ) ρ∈Γ)
          a/ρ≃a/σ∈Πjk/ρ = Tp∈-/≃ a∈Πjk ρ≃σ∈Γ
          b/ρ≃b/σ∈j/ρ   = Tp∈-/≃ b∈j   ρ≃σ∈Γ
          k[b]/ρ≅k[b]/σ = kd-/≃ k[b]-kd ρ≃σ∈Γ
          k/ρ≅k/σ       = kd-/≃ k-kd ρ↑≃σ↑∈j∷Γ
          b/ρ∈j/ρ   = Tp∈-/ b∈j ρ∈Γ
          b/σ∈j/σ   = Tp∈-/ b∈j σ∈Γ
          b/σ∈j/ρ   = ∈-⇑ b/σ∈j/σ (≅⇒<∷ j/σ≅j/ρ)
          k/ρ-kd    = kd-/ k-kd ρ↑∈j∷Γ
          k/ρ[b/ρ]-kd = subst (_ ⊢_kd) k[b]/ρ≡k/ρ[b/ρ] (kd-/ k[b]-kd ρ∈Γ)
          k/ρ[b/σ]-kd = kd-[] k/ρ-kd (∈-tp b/σ∈j/ρ)
          k/ρ[b/σ]≅k[b]/σ = subst (_ ⊢ (k Kind/ _) Kind[ _ ] ≅_)
                                  (sym k[b]/σ≡k/σ[b/σ])
                                  (≅-[] k/ρ≅k/σ (∈-tp b/σ∈j/σ))
          k[b]/σ≅k/ρ[b/ρ] = subst (_ ⊢ _ ≅_) k[b]/ρ≡k/ρ[b/ρ]
                                  (≅-sym k[b]/ρ≅k[b]/σ)
          k/ρ[b/σ]≅k/ρ[b/ρ] = ≅-trans k/ρ[b/σ]≅k[b]/σ k[b]/σ≅k/ρ[b/ρ]
      in (subst (_ ⊢ _ ≃ _ ∈_) (sym k[b]/ρ≡k/ρ[b/ρ])
                (<:-antisym (<:-· (≃⇒<: a/ρ≃a/σ∈Πjk/ρ) b/ρ≃b/σ∈j/ρ b/ρ∈j/ρ
                                  k/ρ-kd k/ρ[b/ρ]-kd)
                            (<:-⇑ (<:-· (≃⇒<: (≃-sym a/ρ≃a/σ∈Πjk/ρ))
                                        (≃-sym b/ρ≃b/σ∈j/ρ) b/σ∈j/ρ k/ρ-kd
                                        k/ρ[b/σ]-kd)
                                  (≅⇒<∷ k/ρ[b/σ]≅k/ρ[b/ρ]))))
    Tp∈-/≃ (∈-s-i a∈b⋯d) ρ≃σ∈Γ =
      let ρ∈Γ , σ∈Γ , _    = ρ≃σ∈Γ
          a/ρ∈*            = Tp∈-⋯-* (Tp∈-/ a∈b⋯d ρ∈Γ)
          a/σ∈*            = Tp∈-⋯-* (Tp∈-/ a∈b⋯d σ∈Γ)
          a/ρ≃a/σ∈b/ρ⋯d/ρ  = Tp∈-/≃ a∈b⋯d ρ≃σ∈Γ
          a/ρ<:a/σ∈a/ρ⋯a/σ = <:-⋯-i (≃⇒<: a/ρ≃a/σ∈b/ρ⋯d/ρ)
          a/σ<:a/ρ∈a/σ⋯a/ρ = <:-⋯-i (≃⇒<: (≃-sym a/ρ≃a/σ∈b/ρ⋯d/ρ))
          a/ρ<:a/σ∈*       = <:-⇑ a/ρ<:a/σ∈a/ρ⋯a/σ
                                  (<∷-⋯ (<:-⊥ a/ρ∈*) (<:-⊤ a/σ∈*))
          a/σ<:a/ρ∈*       = <:-⇑ a/σ<:a/ρ∈a/σ⋯a/ρ
                                  (<∷-⋯ (<:-⊥ a/σ∈*) (<:-⊤ a/ρ∈*))
          a/ρ<:a/σ∈a/ρ⋯a/ρ = <:-⇑ a/ρ<:a/σ∈a/ρ⋯a/σ
                                  (<∷-⋯ (<:-refl a/ρ∈*) a/σ<:a/ρ∈*)
          a/σ<:a/ρ∈a/ρ⋯a/ρ = <:-⇑ a/σ<:a/ρ∈a/σ⋯a/ρ
                                  (<∷-⋯ a/ρ<:a/σ∈* (<:-refl a/ρ∈*))
      in <:-antisym a/ρ<:a/σ∈a/ρ⋯a/ρ a/σ<:a/ρ∈a/ρ⋯a/ρ
    Tp∈-/≃ (∈-⇑ a∈j j<∷k) ρ≃σ∈Γ =
      ≃-⇑ (Tp∈-/≃ a∈j ρ≃σ∈Γ) (<∷-/ j<∷k (proj₁ ρ≃σ∈Γ))

    -- Helpers (to satisfy the termination checker).

    kd-/≃-≅ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k ρ σ} →
              kd j ∷ Γ ⊢ k kd → Δ ⊢/ ρ ≃′ σ ∈ Γ → Δ ⊢ j Kind/ ρ ≅ j Kind/ σ
    kd-/≃-≅ (kd-⋯ a∈* _)  ρ≃σ∈Γ = Tp∈-/≃-≅ a∈* ρ≃σ∈Γ
    kd-/≃-≅ (kd-Π j-kd _) ρ≃σ∈Γ = kd-/≃-≅ j-kd ρ≃σ∈Γ

    Tp∈-/≃-≅ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k ρ σ} →
               kd j ∷ Γ ⊢Tp a ∈ k → Δ ⊢/ ρ ≃′ σ ∈ Γ → Δ ⊢ j Kind/ ρ ≅ j Kind/ σ
    Tp∈-/≃-≅ (∈-var x (wf-kd k-kd ∷ Γ-ctx) _) ρ≃σ∈Γ = kd-/≃ k-kd ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-⊥-f (wf-kd k-kd ∷ Γ-ctx))     ρ≃σ∈Γ = kd-/≃ k-kd ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-⊤-f (wf-kd k-kd ∷ Γ-ctx))     ρ≃σ∈Γ = kd-/≃ k-kd ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-∀-f k-kd _)                   ρ≃σ∈Γ = kd-/≃-≅ k-kd ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-→-f a∈* _)                    ρ≃σ∈Γ = Tp∈-/≃-≅ a∈* ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-Π-i j-kd _ _)                 ρ≃σ∈Γ = kd-/≃-≅ j-kd ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-Π-e a∈Πjk _ _ _)              ρ≃σ∈Γ = Tp∈-/≃-≅ a∈Πjk ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-s-i a∈b⋯c)                    ρ≃σ∈Γ = Tp∈-/≃-≅ a∈b⋯c ρ≃σ∈Γ
    Tp∈-/≃-≅ (∈-⇑ a∈k _)                      ρ≃σ∈Γ = Tp∈-/≃-≅ a∈k ρ≃σ∈Γ


  -- Functionality of single-variable substitutions.

  -- Equal single-variable substitutions map well-formed kinds to kind
  -- equations (weak version).

  kd-[≃′] : ∀ {n} {Γ : Ctx n} {a b j k} →
            kd j ∷ Γ ⊢ k kd → Γ ⊢Tp a ∈ j → Γ ⊢Tp b ∈ j → Γ ⊢ a ≃ b ∈ j →
            Γ ⊢ k Kind[ a ] ≅ k Kind[ b ]
  kd-[≃′] k-kd a∈j b∈j a≃b∈j =
    kd-/≃ k-kd (∈-sub (∈-tp a∈j) , ∈-sub (∈-tp b∈j) ,
                ∼∈-sub (≃-tp a≃b∈j) , ∼∈-sub (≃-tp (≃-sym (a≃b∈j))))

  -- Equal single-variable substitutions map well-kinded types to type
  -- equations (weak version).

  Tp∈-[≃′] : ∀ {n} {Γ : Ctx n} {a b c j k} →
             kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j → Γ ⊢Tp c ∈ j → Γ ⊢ b ≃ c ∈ j →
             Γ ⊢ a [ b ] ≃ a [ c ] ∈ k Kind[ b ]
  Tp∈-[≃′] a∈k b∈j c∈j b≃c∈j =
    Tp∈-/≃ a∈k (∈-sub (∈-tp b∈j) , ∈-sub (∈-tp c∈j) ,
                ∼∈-sub (≃-tp b≃c∈j) , ∼∈-sub (≃-tp (≃-sym (b≃c∈j))))
