------------------------------------------------------------------------
-- Typing and kinding of Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Typing where

open import Data.Context.WellFormed
open import Data.Fin using (Fin; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Level using () renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax


------------------------------------------------------------------------
-- Typing derivations.

module Typing where
  open TermCtx
  open Syntax
  open Substitution using (_[_]; _Kind[_]; weaken)

  infix 4 _ctx _⊢_kd _⊢_wf
  infix 4 _⊢Tp_∈_ _⊢Tm_∈_ _⊢_∈_
  infix 4 _⊢_<:_∈_ _⊢_<∷_ _⊢_≤_
  infix 4 _⊢_≃_∈_ _⊢_≅_ _⊢_≃_wf _≃_ctx
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
              Γ ⊢Tp Λ j a ∈ Π j k
      ∈-Π-e : ∀ {a b j k} → Γ ⊢Tp a ∈ Π j k → Γ ⊢Tp b ∈ j →
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
                 Γ ⊢ (Λ j a) · b <: a [ b ] ∈ k Kind[ b ]
      <:-β₂    : ∀ {j a k b} → kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j →
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

  -- Typing derivations.
  data _⊢Tm_∈_ {n} (Γ : Ctx n) : Term n → Term n → Set where
    ∈-var : ∀ {a} x → Γ ctx → lookup Γ x ≡ tp a → Γ ⊢Tm var x ∈ a
    ∈-∀-i : ∀ {k a b} → Γ ⊢ k kd → kd k ∷ Γ ⊢Tm a ∈ b →
            Γ ⊢Tm Λ k a ∈ Π k b
    ∈-→-i : ∀ {a b c} → Γ ⊢Tp a ∈ * → tp a ∷ Γ ⊢Tm b ∈ weaken c →
            -- FIXME: redundant validity condition (could be avoided
            -- by proving a context strengthening lemma for
            -- eliminating term variables in kindings).
            Γ ⊢Tp c ∈ * →
            Γ ⊢Tm ƛ a b ∈ a ⇒ c
    ∈-∀-e : ∀ {a b k c} → Γ ⊢Tm a ∈ Π k c → Γ ⊢Tp b ∈ k →
            Γ ⊢Tm a ⊡ b ∈ c [ b ]
    ∈-→-e : ∀ {a b c d} → Γ ⊢Tm a ∈ c ⇒ d → Γ ⊢Tm b ∈ c →
            Γ ⊢Tm a · b ∈ d
    ∈-⇑   : ∀ {a b c} → Γ ⊢Tm a ∈ b → Γ ⊢ b <: c ∈ * → Γ ⊢Tm a ∈ c

  -- Combined typing and kinding of terms and types.
  data _⊢_∈_ {n} (Γ : Ctx n) : Term n → TermAsc n → Set where
    ∈-tp : ∀ {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ a ∈ kd k
    ∈-tm : ∀ {a b} → Γ ⊢Tm a ∈ b → Γ ⊢ a ∈ tp b

  -- Combined subtyping and subkinding.
  data _⊢_≤_ {n} (Γ : Ctx n) : TermAsc n → TermAsc n → Set where
    ≤-<∷ : ∀ {j k} → Γ ⊢ j <∷ k     → Γ ⊢ kd j ≤ kd k
    ≤-<: : ∀ {a b} → Γ ⊢ a <: b ∈ * → Γ ⊢ tp a ≤ tp b

  mutual

    -- Combined kind and type equality, i.e. equality of well-formed
    -- ascriptions.
    data _⊢_≃_wf {n} (Γ : Ctx n) : TermAsc n → TermAsc n → Set where
      ≃wf-≅ : ∀ {j k} → Γ ⊢ j ≅ k     → Γ ⊢ kd j ≃ kd k wf
      ≃wf-≃ : ∀ {a b} → Γ ⊢ a ≃ b ∈ * → Γ ⊢ tp a ≃ tp b wf

    -- Equality of well-formed contexts.
    data _≃_ctx : ∀ {n} → Ctx n → Ctx n → Set where
      ≃-[] : [] ≃ [] ctx
      ≃-∷  : ∀ {n a b} {Γ Δ : Ctx n} →
             Γ ⊢ a ≃ b wf → Γ ≃ Δ ctx → a ∷ Γ ≃ b ∷ Δ ctx

  open PropEq using ([_])

  -- A derived variable rule.
  ∈-var′ : ∀ {n} {Γ : Ctx n} x → Γ ctx → Γ ⊢ var x ∈ lookup Γ x
  ∈-var′ {Γ = Γ} x Γ-ctx with lookup Γ x | inspect (lookup Γ) x
  ∈-var′ x Γ-ctx | kd k | [ Γ[x]≡kd-k ] = ∈-tp (∈-var x Γ-ctx Γ[x]≡kd-k)
  ∈-var′ x Γ-ctx | tp a | [ Γ[x]≡tp-a ] = ∈-tm (∈-var x Γ-ctx Γ[x]≡tp-a)

  -- A derived subsumption rule.
  ∈-⇑′ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a ∈ b → Γ ⊢ b ≤ c → Γ ⊢ a ∈ c
  ∈-⇑′ (∈-tp a∈b) (≤-<∷ b<∷c) = ∈-tp (∈-⇑ a∈b b<∷c)
  ∈-⇑′ (∈-tm a∈b) (≤-<: b<:c) = ∈-tm (∈-⇑ a∈b b<:c)

  open ContextFormation _⊢_wf public
    hiding (_wf) renaming (_⊢_wfExt to _⊢_ext)


------------------------------------------------------------------------
-- Properties of typings

open Syntax
open TermCtx
open Typing

-- Inversion lemmas for _⊢_wf.

wf-kd-inv : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ kd k wf → Γ ⊢ k kd
wf-kd-inv (wf-kd k-kd) = k-kd

wf-tp-inv : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ tp a wf → Γ ⊢Tp a ∈ *
wf-tp-inv (wf-tp a∈*) = a∈*

-- An inversion lemma for _⊢_≃_wf.
≃wf-kd-inv : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ kd j ≃ kd k wf → Γ ⊢ j ≅ k
≃wf-kd-inv (≃wf-≅ j≅k) = j≅k

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
        Γ ⊢ (Λ j a) · b ≃ a [ b ] ∈ k Kind[ b ]
  ≃-β a∈k b∈j = <:-antisym (<:-β₁ a∈k b∈j) (<:-β₂ a∈k b∈j)

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

-- NOTE.  There are more admissible rules one might want to prove
-- here, such as congruence lemmas for type and kind equality
-- w.r.t. the remaining type constructors (e.g. Π and _·_) or
-- transitivity of subkinding and kind equality.  But the proofs of
-- these lemmas require context narrowing and/or validity lemmas which
-- we have not yet established.  We will prove these lemmas once we
-- have established validity of the declarative judgments (see the
-- Typing.Validity module).


-- The contexts of all the above judgments are well-formed.

mutual

  kd-ctx : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ctx
  kd-ctx (kd-⋯ a∈* b∈*)    = Tp∈-ctx a∈*
  kd-ctx (kd-Π j-kd  k-kd) = kd-ctx j-kd

  Tp∈-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ctx
  Tp∈-ctx (∈-var x Γ-ctx Γ[x]≡kd-k) = Γ-ctx
  Tp∈-ctx (∈-⊥-f Γ-ctx)     = Γ-ctx
  Tp∈-ctx (∈-⊤-f Γ-ctx)     = Γ-ctx
  Tp∈-ctx (∈-∀-f k-kd a∈*)  = kd-ctx k-kd
  Tp∈-ctx (∈-→-f a∈* b∈*)   = Tp∈-ctx a∈*
  Tp∈-ctx (∈-Π-i j-kd a∈k)  = kd-ctx j-kd
  Tp∈-ctx (∈-Π-e a∈Πjk b∈j) = Tp∈-ctx a∈Πjk
  Tp∈-ctx (∈-s-i a∈b⋯c)     = Tp∈-ctx a∈b⋯c
  Tp∈-ctx (∈-⇑ a∈j j<∷k)    = Tp∈-ctx a∈j

wf-ctx : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → Γ ctx
wf-ctx (wf-kd k-kd) = kd-ctx k-kd
wf-ctx (wf-tp a∈*)  = Tp∈-ctx a∈*

<:-ctx : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ∈ k → Γ ctx
<:-ctx (<:-refl a∈k)            = Tp∈-ctx a∈k
<:-ctx (<:-trans a<:b∈k b<:c∈k) = <:-ctx a<:b∈k
<:-ctx (<:-β₁ a∈j b∈k) = Tp∈-ctx b∈k
<:-ctx (<:-β₂ a∈j b∈k) = Tp∈-ctx b∈k
<:-ctx (<:-η₁ a∈Πjk)   = Tp∈-ctx a∈Πjk
<:-ctx (<:-η₂ a∈Πjk)   = Tp∈-ctx a∈Πjk
<:-ctx (<:-⊥ a∈b⋯c)    = Tp∈-ctx a∈b⋯c
<:-ctx (<:-⊤ a∈b⋯c)    = Tp∈-ctx a∈b⋯c
<:-ctx (<:-∀ k₂<∷k₁ a₁<:a₂ ∀k₁a₁∈*) = Tp∈-ctx ∀k₁a₁∈*
<:-ctx (<:-→ a₂<:a₁ b₁<:b₂)         = <:-ctx a₂<:a₁
<:-ctx (<:-λ a₂<:a₁∈Πjk Λa₁k₁∈Πjk Λa₂k₂∈Πjk) = Tp∈-ctx Λa₁k₁∈Πjk
<:-ctx (<:-· a₂<:a₁∈Πjk b₂≃b₁∈j)             = <:-ctx a₂<:a₁∈Πjk
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

Tm∈-ctx : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢Tm a ∈ b → Γ ctx
Tm∈-ctx (∈-var x Γ-ctx Γ[x]≡tp-a) = Γ-ctx
Tm∈-ctx (∈-∀-i k-kd a∈b)    = kd-ctx k-kd
Tm∈-ctx (∈-→-i a∈* b∈c c∈*) = Tp∈-ctx a∈*
Tm∈-ctx (∈-∀-e a∈∀kc b∈k)   = Tm∈-ctx a∈∀kc
Tm∈-ctx (∈-→-e a∈c⇒d b∈c)   = Tm∈-ctx a∈c⇒d
Tm∈-ctx (∈-⇑ a∈b b<:c)      = Tm∈-ctx a∈b

∈-ctx : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ∈ b → Γ ctx
∈-ctx (∈-tp a∈k) = Tp∈-ctx a∈k
∈-ctx (∈-tm a∈b) = Tm∈-ctx a∈b


----------------------------------------------------------------------
-- Well-typed substitutions (i.e. substitution lemmas)

-- A shorthand for kindings and typings of Ts by kind or type
-- ascriptions.
TermAscTyping : (ℕ → Set) → Set₁
TermAscTyping T = Typing TermAsc T TermAsc lzero

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

-- Application of generic well-typed T-substitutions to all the judgments.

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

  -- Lift well-typed Ts to well-typed terms.
  liftTm : ∀ {n} {Γ : Ctx n} {a b tp-b} →
           tp-b ≡ tp b → Γ ⊢T a ∈ tp-b → Γ ⊢Tm L.lift a ∈ b
  liftTm refl a∈tp-b with ∈-lift a∈tp-b
  liftTm refl a∈tp-b | ∈-tm a∈b = a∈b

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
    Tp∈-/ (∈-Π-i j-kd a∈k) σ∈Γ =
      ∈-Π-i j/σ-kd (Tp∈-/ a∈k (∈-↑ (wf-kd j/σ-kd) σ∈Γ))
      where j/σ-kd = kd-/ j-kd σ∈Γ
    Tp∈-/ (∈-Π-e {_} {b} {_} {k} a∈Πjk b∈j) σ∈Γ =
      subst (_ ⊢Tp _ ∈_) (sym (Kind/-sub-↑ k b _))
            (∈-Π-e (Tp∈-/ a∈Πjk σ∈Γ) (Tp∈-/ b∈j σ∈Γ))
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
    <:-/ (<:-β₁ {j} {a} {k} {b} a∈k b∈j) σ∈Γ =
      subst₂ (_ ⊢ (Λ j a) · b A./ _ <:_∈_)
             (sym (/-sub-↑ a b _)) (sym (Kind/-sub-↑ k b _))
             (<:-β₁ (Tp∈-/ a∈k (∈-↑ (Tp∈-/-wf a∈k σ∈Γ) σ∈Γ)) (Tp∈-/ b∈j σ∈Γ))
    <:-/ (<:-β₂ {j} {a} {k} {b} a∈k b∈j) σ∈Γ =
      subst₂ (_ ⊢_<: (Λ j a) · b A./ _ ∈_)
             (sym (/-sub-↑ a b _)) (sym (Kind/-sub-↑ k b _))
             (<:-β₂ (Tp∈-/ a∈k (∈-↑ (Tp∈-/-wf a∈k σ∈Γ) σ∈Γ)) (Tp∈-/ b∈j σ∈Γ))
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
    <:-/ (<:-· {k = k} a₁<:a₂∈Πjk b₁≃b₂∈j) σ∈Γ =
      subst (_ ⊢ _ <: _ ∈_) (sym (Kind/-sub-↑ k _ _))
            (<:-· (<:-/ a₁<:a₂∈Πjk σ∈Γ) (≃-/ b₁≃b₂∈j σ∈Γ))
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
    Tp∈-/-wf (∈-Π-i j-kd _)      σ∈Γ = kd-/-wf j-kd σ∈Γ
    Tp∈-/-wf (∈-Π-e a∈Πjk _)     σ∈Γ = Tp∈-/-wf a∈Πjk σ∈Γ
    Tp∈-/-wf (∈-s-i a∈b⋯c)       σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    Tp∈-/-wf (∈-⇑ a∈b _)         σ∈Γ = Tp∈-/-wf a∈b σ∈Γ

    <:-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j k σ} →
              kd j ∷ Γ ⊢ a <: b ∈ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ kd (j A.Kind/ σ) wf
    <:-/-wf (<:-refl a∈k)        σ∈Γ = Tp∈-/-wf a∈k σ∈Γ
    <:-/-wf (<:-trans a<:b _)    σ∈Γ = <:-/-wf a<:b σ∈Γ
    <:-/-wf (<:-β₁ _ b∈j)        σ∈Γ = Tp∈-/-wf b∈j σ∈Γ
    <:-/-wf (<:-β₂ _ b∈j)        σ∈Γ = Tp∈-/-wf b∈j σ∈Γ
    <:-/-wf (<:-η₁ a∈Πjk)        σ∈Γ = Tp∈-/-wf a∈Πjk σ∈Γ
    <:-/-wf (<:-η₂ a∈Πjk)        σ∈Γ = Tp∈-/-wf a∈Πjk σ∈Γ
    <:-/-wf (<:-⊥ a∈b⋯c)         σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    <:-/-wf (<:-⊤ a∈b⋯c)         σ∈Γ = Tp∈-/-wf a∈b⋯c σ∈Γ
    <:-/-wf (<:-∀ j₂<∷j₁ _ _)    σ∈Γ = <∷-/-wf j₂<∷j₁ σ∈Γ
    <:-/-wf (<:-→ a₂<:a₁∈* _)    σ∈Γ = <:-/-wf a₂<:a₁∈* σ∈Γ
    <:-/-wf (<:-λ _ Λj₁a₂∈Πjk _) σ∈Γ = Tp∈-/-wf Λj₁a₂∈Πjk σ∈Γ
    <:-/-wf (<:-· a₁<:a₂∈Πjk _)  σ∈Γ = <:-/-wf a₁<:a₂∈Πjk σ∈Γ
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

  -- Substitutions preserve well-typedness of terms.
  Tm∈-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
          Γ ⊢Tm a ∈ b → Δ ⊢/ σ ∈ Γ → Δ ⊢Tm a A./ σ ∈ b A./ σ
  Tm∈-/ (∈-var x Γ-ctx Γ[x]=tp-k) σ∈Γ =
    liftTm (cong (_/ _) Γ[x]=tp-k) (/∈-lookup σ∈Γ x)
  Tm∈-/ (∈-∀-i k-kd a∈*)          σ∈Γ =
    ∈-∀-i k/σ-kd (Tm∈-/ a∈* (∈-↑ (wf-kd k/σ-kd) σ∈Γ))
    where k/σ-kd = kd-/ k-kd σ∈Γ
  Tm∈-/ (∈-→-i {c = c} a∈* b∈c c∈*) σ∈Γ =
    ∈-→-i a/σ∈* (subst (_ ⊢Tm _ ∈_) (sym (weaken-/ c) ) b/σ↑∈c)
          (Tp∈-/ c∈* σ∈Γ)
    where
      a/σ∈*  = Tp∈-/ a∈* σ∈Γ
      b/σ↑∈c = Tm∈-/ b∈c (∈-↑ (wf-tp a/σ∈*) σ∈Γ)
  Tm∈-/ (∈-∀-e {c = c} a∈∀kc b∈k) σ∈Γ =
    subst (_ ⊢Tm _ ∈_) (sym (/-sub-↑ c _ _))
          (∈-∀-e (Tm∈-/ a∈∀kc σ∈Γ) (Tp∈-/ b∈k σ∈Γ))
  Tm∈-/ (∈-→-e a∈c→d b∈c)         σ∈Γ = ∈-→-e (Tm∈-/ a∈c→d σ∈Γ) (Tm∈-/ b∈c σ∈Γ)
  Tm∈-/ (∈-⇑ a∈b b<:c)            σ∈Γ = ∈-⇑ (Tm∈-/ a∈b σ∈Γ) (<:-/ b<:c σ∈Γ)

  -- Substitutions preserve well-kindedness and well-typedness.
  ∈-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
        Γ ⊢ a ∈ b → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A./ σ ∈ b A.TermAsc/ σ
  ∈-/ (∈-tp a∈b) σ∈Γ = ∈-tp (Tp∈-/ a∈b σ∈Γ)
  ∈-/ (∈-tm a∈b) σ∈Γ = ∈-tm (Tm∈-/ a∈b σ∈Γ)

  -- Substitutions preserve subkinding and subtyping.
  ≤-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
        Γ ⊢ a ≤ b → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A.TermAsc/ σ ≤ b A.TermAsc/ σ
  ≤-/ (≤-<∷ a<∷b)   σ∈Γ = ≤-<∷ (<∷-/ a<∷b σ∈Γ)
  ≤-/ (≤-<: a<:b∈k) σ∈Γ = ≤-<: (<:-/ a<:b∈k σ∈Γ)

  -- Substitutions preserve equality of kind and type ascriptions.
  ≃wf-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
          Γ ⊢ a ≃ b wf → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A.TermAsc/ σ ≃ b A.TermAsc/ σ wf
  ≃wf-/ (≃wf-≅ j≅k) σ∈Γ = ≃wf-≅ (≅-/ j≅k σ∈Γ)
  ≃wf-/ (≃wf-≃ a≃b) σ∈Γ = ≃wf-≃ (≃-/ a≃b σ∈Γ)

-- Well-kinded/typed type and term substitutions.
module TypedSubstitution where
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

  -- Typed term substitutions.

  typedTermSubst : TypedTermSubst TermAsc Term lzero TypedSubstAppHelpers
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
    ; ≤-/   to ≤-/Var
    ; ≃wf-/ to ≃wf-/Var
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

  ≤-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b ≤ c →
             (a ∷ Γ) ⊢ weakenTermAsc b ≤ weakenTermAsc c
  ≤-weaken a-wf b≤c = ≤-/Var b≤c (Var∈-wk a-wf)

  ≃wf-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b ≃ c wf →
               (a ∷ Γ) ⊢ weakenTermAsc b ≃ weakenTermAsc c wf
  ≃wf-weaken a-wf b≃c = ≃wf-/Var b≃c (Var∈-wk a-wf)

  open TypedSubstApp _⊢_∈_ termLiftTyped termHelpers public
  open Substitution using (_/_; _Kind/_; id; sub; _↑⋆_; _[_]; _Kind[_])

  -- Substitution of a single well-typed term or well-kinded type
  -- preserves the various judgments.

  kd-[] : ∀ {n} {Γ : Ctx n} {a b k} →
          b ∷ Γ ⊢ k kd → Γ ⊢ a ∈ b → Γ ⊢ k Kind[ a ] kd
  kd-[] k-kd a∈b = kd-/ k-kd (∈-sub a∈b)

  Tp∈-[] : ∀ {n} {Γ : Ctx n} {a b k c} →
           c ∷ Γ ⊢Tp a ∈ k → Γ ⊢ b ∈ c → Γ ⊢Tp a [ b ] ∈ k Kind[ b ]
  Tp∈-[] a∈k b∈c = Tp∈-/ a∈k (∈-sub b∈c)

  Tm∈-[] : ∀ {n} {Γ : Ctx n} {a b c d} →
           d ∷ Γ ⊢Tm a ∈ c → Γ ⊢ b ∈ d → Γ ⊢Tm a [ b ] ∈ c [ b ]
  Tm∈-[] a∈c b∈d = Tm∈-/ a∈c (∈-sub b∈d)

  <:-[] : ∀ {n} {Γ : Ctx n} {a b c d k} →
          d ∷ Γ ⊢ a <: b ∈ k → Γ ⊢ c ∈ d → Γ ⊢ a [ c ] <: b [ c ] ∈ k Kind[ c ]
  <:-[] a<:b c∈d = <:-/ a<:b (∈-sub c∈d)

-- Operations on well-formed contexts that require weakening of
-- well-formedness judgments.

module WfCtxOps where
  wfWeakenOps : WellFormedWeakenOps weakenOps
  wfWeakenOps = record { wf-weaken = TypedSubstitution.wf-weaken }

  open WellFormedWeakenOps wfWeakenOps public renaming (lookup to lookup-wf)

  -- Lookup the kind of a type variable in a well-formed context.
  lookup-kd : ∀ {m} {Γ : Ctx m} {k} x →
              Γ ctx → TermCtx.lookup Γ x ≡ kd k → Γ ⊢ k kd
  lookup-kd x Γ-ctx Γ[x]≡kd-k =
    wf-kd-inv (subst (_ ⊢_wf) Γ[x]≡kd-k (lookup-wf Γ-ctx x))

  -- Lookup the type of a term variable in a well-formed context.
  lookup-tp : ∀ {m} {Γ : Ctx m} {a} x →
              Γ ctx → TermCtx.lookup Γ x ≡ tp a → Γ ⊢Tp a ∈ *
  lookup-tp x Γ-ctx Γ[x]≡tp-a =
    wf-tp-inv (subst (_ ⊢_wf) Γ[x]≡tp-a (lookup-wf Γ-ctx x))

open TypedSubstitution
open WfCtxOps


----------------------------------------------------------------------
-- Generation lemmas for kinding

-- A generation lemma for kinding of universals.
Tp∈-∀-inv : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢Tp Π j a ∈ k →
            Γ ⊢ j kd × kd j ∷ Γ ⊢Tp a ∈ *
Tp∈-∀-inv (∈-∀-f j-kd a∈*) = j-kd , a∈*
Tp∈-∀-inv (∈-s-i ∀ka∈b⋯c)  = Tp∈-∀-inv ∀ka∈b⋯c
Tp∈-∀-inv (∈-⇑ ∀ja∈k k<∷l) = Tp∈-∀-inv ∀ja∈k

-- A generation lemma for kinding of arrows.
Tp∈-→-inv : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ⇒ b ∈ k →
            Γ ⊢Tp a ∈ * × Γ ⊢Tp b ∈ *
Tp∈-→-inv (∈-→-f a∈* b∈*)  = a∈* , b∈*
Tp∈-→-inv (∈-s-i a⇒b∈c⋯d)  = Tp∈-→-inv a⇒b∈c⋯d
Tp∈-→-inv (∈-⇑ a⇒b∈j j<∷k) = Tp∈-→-inv a⇒b∈j
