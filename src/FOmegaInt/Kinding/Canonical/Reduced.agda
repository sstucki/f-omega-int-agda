------------------------------------------------------------------------
-- Reduced canonical kinding for the undecidability proof
------------------------------------------------------------------------

{-# OPTIONS --safe --exact-split --without-K #-}

module FOmegaInt.Kinding.Canonical.Reduced where

open import Data.Context.WellFormed
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec as Vec using ([]; _∷_)
open import Data.Vec.Properties as VecProps using (map-∘; map-cong)
open import Function using (_∘_)
open import Level using () renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution using (Kind/⟨★⟩-/)
import FOmegaInt.Kinding.Canonical as CanonicalKinding

module C where
  open CanonicalKinding public
  open Kinding          public


------------------------------------------------------------------------
-- Reduced canonical kinding derivations.

module Kinding where
  open ElimCtx
  open Syntax
  open Substitution using (_Kind′[_])

  infix 4 _⊢_wf _ctx _⊢_kd
  infix 4 _⊢Nf_⇉_ _⊢Ne_⇉_ _⊢Var_⇉_ _⊢_⇉∙_⇉_ _⊢Nf_⇇_
  infix 4 _⊢_<∷_ _⊢_∼_
  infix 4 _⊢_⇉∙_∼_⇉_

  mutual

    -- Formation of kinds, bindings, and contexts.
    --
    -- NOTE. The rule kd-Π only supports first-order operators.

    data _⊢_kd {n} (Γ : Ctx n) : Kind Elim n → Set where
      kd-⋯ : ∀ {a b}   → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢Nf b ⇉ b ⋯ b → Γ ⊢ a ⋯ b kd
      kd-Π : ∀ {a b k} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢Nf b ⇉ b ⋯ b →
             kd (a ⋯ b) ∷ Γ ⊢ k kd → Γ ⊢ Π (a ⋯ b) k kd

    data _⊢_wf {n} (Γ : Ctx n) : ElimAsc n → Set where
      wf-kd : ∀ {a} → Γ ⊢ a kd        → Γ ⊢ kd a wf
      wf-tp : ∀ {a} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢ tp a wf

    _ctx : ∀ {n} → Ctx n → Set
    Γ ctx = ContextFormation._wf _⊢_wf Γ

    -- Kind synthesis for variables, neutrals and βη-normal types.

    data _⊢Var_⇉_ {n} (Γ : Ctx n) : Fin n → Kind Elim n → Set where
      ⇉-var : ∀ {k} x → Γ ctx → lookup Γ x ≡ kd k → Γ ⊢Var x ⇉ k

    data _⊢Ne_⇉_ {n} (Γ : Ctx n) : Elim n → Kind Elim n → Set where
      ⇉-∙ : ∀ {x j k} {as : Spine n} → Γ ⊢Var x ⇉ j →
            Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢Ne var x ∙ as ⇉ k

    data _⊢Nf_⇉_ {n} (Γ : Ctx n) : Elim n → Kind Elim n → Set where
      ⇉-⊥-f : Γ ctx → Γ ⊢Nf ⊥∙ ⇉ ⊥∙ ⋯ ⊥∙
      ⇉-⊤-f : Γ ctx → Γ ⊢Nf ⊤∙ ⇉ ⊤∙ ⋯ ⊤∙
      ⇉-s-i : ∀ {a b c} → Γ ⊢Ne a ⇉ b ⋯ c → Γ ⊢Nf a ⇉ a ⋯ a

    -- Kind checking for η-long β-normal types.

    data _⊢Nf_⇇_ {n} (Γ : Ctx n) : Elim n → Kind Elim n → Set where
      ⇇-⇑  : ∀ {a j k} → Γ ⊢Nf a ⇉ j → Γ ⊢ j <∷ k → Γ ⊢Nf a ⇇ k

    -- Kind synthesis for spines.
    --
    -- Note the use of ordinary (instead of hereditary) substitution.

    data _⊢_⇉∙_⇉_ {n} (Γ : Ctx n)
      : Kind Elim n → Spine n → Kind Elim n → Set where
      ⇉-[] : ∀ {k} → Γ ⊢ k ⇉∙ [] ⇉ k
      ⇉-∷  : ∀ {a as b c j k} → Γ ⊢Nf a ⇇ b ⋯ c →
             Γ ⊢ j Kind′[ ⌞ a ⌟ ] ⇉∙ as ⇉ k → Γ ⊢ Π (b ⋯ c) j ⇉∙ a ∷ as ⇉ k

    -- Reduced canonical subkinding derivations.
    --
    -- NOTE. The rule <∷-Π only supports first-order operators.

    data _⊢_<∷_ {n} (Γ : Ctx n) : Kind Elim n → Kind Elim n → Set where
      <∷-⋯ : ∀ {a₁ a₂ b₁ b₂} →
             Γ ⊢ a₂ ∼ a₁ → Γ ⊢ b₁ ∼ b₂ → Γ ⊢ a₁ ⋯ b₁ <∷ a₂ ⋯ b₂
      <∷-Π : ∀ {a₁ a₂ b₁ b₂ k₁ k₂} → Γ ⊢ a₁ ∼ a₂ → Γ ⊢ b₂ ∼ b₁ →
             kd (a₂ ⋯ b₂) ∷ Γ ⊢ k₁ <∷ k₂ →
             Γ ⊢ Π (a₁ ⋯ b₁) k₁ <∷ Π (a₂ ⋯ b₂) k₂

    -- Canonical relatedness of proper types and spines.

    data _⊢_∼_ {n} (Γ : Ctx n) : Elim n → Elim n → Set where
      ∼-trans : ∀ {a b c} → Γ ⊢ a ∼ b → Γ ⊢ b ∼ c → Γ ⊢ a ∼ c
      ∼-⊥     : ∀ {a} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢ ⊥∙ ∼ a
      ∼-⊤     : ∀ {a} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢ a ∼ ⊤∙
      ∼-∙     : ∀ {x as₁ as₂ k b c} →
                Γ ⊢Var x ⇉ k → Γ ⊢ k ⇉∙ as₁ ∼ as₂ ⇉ b ⋯ c →
                Γ ⊢ var x ∙ as₁ ∼ var x ∙ as₂
      ∼-⟨|    : ∀ {a b c} → Γ ⊢Ne a ⇉ b ⋯ c → Γ ⊢ b ∼ a
      ∼-|⟩    : ∀ {a b c} → Γ ⊢Ne a ⇉ b ⋯ c → Γ ⊢ a ∼ c

    data _⊢_⇉∙_∼_⇉_ {n} (Γ : Ctx n)
      : Kind Elim n → Spine n → Spine n → Kind Elim n → Set where
      ∼-[] : ∀ {k} → Γ ⊢ k ⇉∙ [] ∼ [] ⇉ k
      ∼-∷  : ∀ {a as b bs c d j k} → Γ ⊢ c ∼ a → Γ ⊢ a ∼ d →
             Γ ⊢ a ∼ b → Γ ⊢ j Kind′[ ⌞ a ⌟ ] ⇉∙ as ∼ bs ⇉ k →
             Γ ⊢ Π (c ⋯ d) j ⇉∙ a ∷ as ∼ b ∷ bs ⇉ k

  -- Well-formed context extensions.
  open ContextFormation _⊢_wf public hiding (_wf; _⊢_wfExt)

  -- A wrapper for the kind checking judgment that also supports
  -- arbitrary variable bindings.

  infix 4 _⊢NfOrVar_∈_

  data _⊢NfOrVar_∈_ {n} (Γ : Ctx n) : Term n → ElimAsc n → Set where
    ∈-nf  : ∀ {a b c d e} → Γ ⊢Nf a ⇇ c ⋯ d → ⌞ a ⌟ ≡ b → kd (c ⋯ d) ≡ e →
            Γ ⊢NfOrVar b ∈ e
    ∈-var : ∀ x {a b} → Γ ctx → var x ≡ a → lookup Γ x ≡ b →
            Γ ⊢NfOrVar a ∈ b


------------------------------------------------------------------------
-- Simple properties of canonical kindings

open Syntax
open ElimCtx hiding (_++_)
open Kinding

-- An inversion lemma for interval subkinding.

<∷-⋯-inv : ∀ {n} {Γ : Ctx n} {k a₂ b₂} → Γ ⊢ k <∷ a₂ ⋯ b₂ →
           ∃ λ a₁ → ∃ λ b₁ → Γ ⊢ a₂ ∼ a₁ × Γ ⊢ b₁ ∼ b₂ × k ≡ a₁ ⋯ b₁
<∷-⋯-inv (<∷-⋯ a₂∼a₁ b₁∼b₂) = _ , _ , a₂∼a₁ , b₁∼b₂ , refl

-- An inversion lemma for _⊢_wf.

wf-kd-inv : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ kd k wf → Γ ⊢ k kd
wf-kd-inv (wf-kd k-kd) = k-kd

-- The synthesized kind of a normal proper type is exactly the singleton
-- containing that type.

Nf⇉-≡ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → k ≡ a ⋯ a
Nf⇉-≡ (⇉-⊥-f Γ-ctx)       = refl
Nf⇉-≡ (⇉-⊤-f Γ-ctx)       = refl
Nf⇉-≡ (⇉-s-i a∈b⋯c)       = refl

-- Derived singleton introduction rules where the premises are
-- well-kinded normal forms rather than neutrals.

Nf⇉-s-i : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → Γ ⊢Nf a ⇉ a ⋯ a
Nf⇉-s-i a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
Nf⇉-s-i a⇉a⋯a | refl = a⇉a⋯a

Nf⇇-s-i : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢Nf a ⇉ a ⋯ a
Nf⇇-s-i (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂∼b₁ c₁∼c₂)) = Nf⇉-s-i a⇉b₁⋯c₁

-- The synthesized kinds of neutrals kind-check.

Nf⇇-ne : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Ne a ⇉ b ⋯ c → Γ ⊢Nf a ⇇ b ⋯ c
Nf⇇-ne (⇉-∙ x∈k k⇉as⇉b⋯c) =
  ⇇-⇑ (⇉-s-i (⇉-∙ x∈k k⇉as⇉b⋯c))
      (<∷-⋯ (∼-⟨| (⇉-∙ x∈k k⇉as⇉b⋯c)) (∼-|⟩ (⇉-∙ x∈k k⇉as⇉b⋯c)))

-- The contexts of (most of) the above judgments are well-formed.
--
-- NOTE. The exceptions are again the spine judgments.  See the
-- comment on context validity in FOmegaInt.Kinding.Canonical for why
-- this doesn't matter.

Var⇉-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Var a ⇉ k → Γ ctx
Var⇉-ctx (⇉-var x Γ-ctx _) = Γ-ctx

Ne⇉-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Ne a ⇉ k → Γ ctx
Ne⇉-ctx (⇉-∙ x∈j j⇉as⇉k) = Var⇉-ctx x∈j

Nf⇉-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → Γ ctx
Nf⇉-ctx (⇉-⊥-f Γ-ctx) = Γ-ctx
Nf⇉-ctx (⇉-⊤-f Γ-ctx) = Γ-ctx
Nf⇉-ctx (⇉-s-i a∈b⋯c) = Ne⇉-ctx a∈b⋯c

Nf⇇-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇇ k → Γ ctx
Nf⇇-ctx (⇇-⇑ a⇉j j<∷k) = Nf⇉-ctx a⇉j

kd-ctx : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ctx
kd-ctx (kd-⋯ a⇉a⋯a b⇉b⋯b)      = Nf⇉-ctx a⇉a⋯a
kd-ctx (kd-Π a⇉a⋯a b⇉b⋯b k-kd) = Nf⇉-ctx a⇉a⋯a

∼-ctx : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ∼ b → Γ ctx
∼-ctx (∼-trans a∼b b∼c)   = ∼-ctx a∼b
∼-ctx (∼-⊥ a⇉a⋯a)           = Nf⇉-ctx a⇉a⋯a
∼-ctx (∼-⊤ a⇉a⋯a)           = Nf⇉-ctx a⇉a⋯a
∼-ctx (∼-∙ x∈j as∼bs)       = Var⇉-ctx x∈j
∼-ctx (∼-⟨| a∈b⋯c)          = Ne⇉-ctx a∈b⋯c
∼-ctx (∼-|⟩ a∈b⋯c)          = Ne⇉-ctx a∈b⋯c

<∷-ctx : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ ctx
<∷-ctx (<∷-⋯ a₂∼a₁ b₁∼b₂)        = ∼-ctx a₂∼a₁
<∷-ctx (<∷-Π a₁∼a₂ b₂∼b₁ k₁<∷k₂) = ∼-ctx a₁∼a₂

wf-ctx : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → Γ ctx
wf-ctx (wf-kd k-kd)  = kd-ctx k-kd
wf-ctx (wf-tp a⇉a⋯a) = Nf⇉-ctx a⇉a⋯a

NfOrVar∈-ctx : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢NfOrVar a ∈ b → Γ ctx
NfOrVar∈-ctx (∈-nf a⇇c⋯d _ _)    = Nf⇇-ctx a⇇c⋯d
NfOrVar∈-ctx (∈-var x Γ-ctx _ _) = Γ-ctx

-- Reflexivity of the various relations.

mutual

  <∷-refl : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ k <∷ k
  <∷-refl (kd-⋯ a⇉a⋯a b⇉b⋯b)      = <∷-⋯ (∼-refl a⇉a⋯a) (∼-refl b⇉b⋯b)
  <∷-refl (kd-Π a⇉a⋯a b⇉b⋯b k-kd) =
    <∷-Π (∼-refl a⇉a⋯a) (∼-refl b⇉b⋯b) (<∷-refl k-kd)

  ∼-refl : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢ a ∼ a
  ∼-refl (⇉-⊥-f Γ-ctx)            = ∼-⊥ (⇉-⊥-f Γ-ctx)
  ∼-refl (⇉-⊤-f Γ-ctx)            = ∼-⊤ (⇉-⊤-f Γ-ctx)
  ∼-refl (⇉-s-i (⇉-∙ x∈j j⇉as⇉k)) = ∼-∙ x∈j (∼Sp-refl j⇉as⇉k)

  ∼Sp-refl : ∀ {n} {Γ : Ctx n} {as j k} →
             Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢ j ⇉∙ as ∼ as ⇉ k
  ∼Sp-refl ⇉-[]                       = ∼-[]
  ∼Sp-refl (⇉-∷ (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂∼b₁ c₁∼c₂)) k[a]⇉as⇉l)
    with Nf⇉-≡ a⇉b₁⋯c₁
  ∼Sp-refl (⇉-∷ (⇇-⇑ a⇉a⋯a (<∷-⋯ b∼a a∼c)) k[a]⇉as⇉l) | refl =
    ∼-∷ b∼a a∼c (∼-refl a⇉a⋯a) (∼Sp-refl k[a]⇉as⇉l)

-- Admissible projection rules for canonically kinded proper types.

∼-⟨|-Nf⇉ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢ b ∼ a
∼-⟨|-Nf⇉ a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
∼-⟨|-Nf⇉ a⇉a⋯a | refl = ∼-refl a⇉a⋯a

∼-⟨|-Nf⇇ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢ b ∼ a
∼-⟨|-Nf⇇ (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂∼b₁ c₁∼c₂)) =
  ∼-trans b₂∼b₁ (∼-⟨|-Nf⇉ a⇉b₁⋯c₁)

∼-|⟩-Nf⇉ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢ a ∼ c
∼-|⟩-Nf⇉ a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
∼-|⟩-Nf⇉ a⇉a⋯a | refl = ∼-refl a⇉a⋯a

∼-|⟩-Nf⇇ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢ a ∼ c
∼-|⟩-Nf⇇ (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂∼b₁ c₁∼c₂)) =
  ∼-trans (∼-|⟩-Nf⇉ a⇉b₁⋯c₁) c₁∼c₂

-- Spines with interval-kinded heads are empty, and therefore have
-- interval-kinded tails.

Sp⇉-⋯ : ∀ {n} {Γ : Ctx n} {as b c k} →
        Γ ⊢ b ⋯ c ⇉∙ as ⇉ k → as ≡ [] × k ≡ b ⋯ c
Sp⇉-⋯ ⇉-[] = refl , refl

Sp∼-⋯ : ∀ {n} {Γ : Ctx n} {as bs c d k} →
        Γ ⊢ c ⋯ d ⇉∙ as ∼ bs ⇉ k → as ≡ [] × bs ≡ [] × k ≡ c ⋯ d
Sp∼-⋯ ∼-[] = refl , refl , refl


----------------------------------------------------------------------
-- Well-kinded/typed substitutions (i.e. substitution lemmas)

-- A shorthand for kindings and typings of Ts by kind or type
-- ascriptions.
ElimAscTyping : (ℕ → Set) → Set₁
ElimAscTyping T = Typing ElimAsc T ElimAsc Level.zero

-- Liftings from well-typed Ts to well-typed/kinded normal forms or
-- variables.
LiftTo-NfOrVar∈ : ∀ {T} → ElimAscTyping T → Set₁
LiftTo-NfOrVar∈ _⊢T_∈_ =
  LiftTyped Substitution.elimAscTermSubst _⊢_wf _⊢T_∈_ _⊢NfOrVar_∈_

-- A helper lemma about untyped T-substitutions in raw kinds.

record TypedSubstAppHelpers {T} (rawLift : Lift T Term) : Set where
  open Substitution using (_Kind′[_])
  module A = SubstApp rawLift
  module L = Lift     rawLift

  -- Substitutions in kinds and types commute.

  field Kind/-sub-↑ : ∀ {m n} k a (σ : Sub T m n) →
                      k Kind′[ ⌞ a ⌟ ] A.Kind′/ σ ≡
                        (k A.Kind′/ σ L.↑) Kind′[ ⌞ a A.Elim/ σ ⌟ ]

-- Application of generic well-typed T-substitutions to all the judgments.

module TypedSubstApp {T : ℕ → Set} (_⊢T_∈_ : ElimAscTyping T)
                     (liftTyped : LiftTo-NfOrVar∈ _⊢T_∈_)
                     (helpers : TypedSubstAppHelpers
                                  (LiftTyped.rawLift liftTyped))
                     where

  open LiftTyped liftTyped renaming (lookup to /∈-lookup) hiding (∈-var)
  open TypedSubstAppHelpers helpers

  -- Well-typed/kinded substitutions preserve all the judgments.

  mutual

    wf-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a σ} →
              Γ ⊢ a wf → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A.ElimAsc/ σ wf
    wf-/ (wf-kd k-kd)  σ∈Γ = wf-kd (kd-/ k-kd σ∈Γ)
    wf-/ (wf-tp a⇉a⋯a) σ∈Γ = wf-tp (Nf⇉-/ a⇉a⋯a σ∈Γ)

    kd-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k σ} →
              Γ ⊢ k kd → Δ ⊢/ σ ∈ Γ → Δ ⊢ k A.Kind′/ σ kd
    kd-/ (kd-⋯ a⇉a⋯a b⇉b⋯b) σ∈Γ =
      kd-⋯ (Nf⇉-/ a⇉a⋯a σ∈Γ) (Nf⇉-/ b⇉b⋯b σ∈Γ)
    kd-/ (kd-Π a⇉a⋯a b⇉b⋯b  k-kd) σ∈Γ =
      let a/σ⇉a/σ⋯a/σ = Nf⇉-/ a⇉a⋯a σ∈Γ
          b/σ⇉b/σ⋯b/σ = Nf⇉-/ b⇉b⋯b σ∈Γ
      in kd-Π a/σ⇉a/σ⋯a/σ b/σ⇉b/σ⋯b/σ
              (kd-/ k-kd (∈-↑ (wf-kd (kd-⋯ a/σ⇉a/σ⋯a/σ b/σ⇉b/σ⋯b/σ)) σ∈Γ))

    Ne⇉-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Ne a ⇉ k → Δ ⊢/ σ ∈ Γ →
               Δ ⊢Nf a A.Elim/ σ ⇇ k A.Kind′/ σ ⊎
               Δ ⊢Ne a A.Elim/ σ ⇉ k A.Kind′/ σ
    Ne⇉-/ (⇉-∙ (⇉-var x Γ-ctx Γ[x]≡j) j⇉as⇉k) σ∈Γ with ∈-lift (/∈-lookup σ∈Γ x)
    ... | ∈-nf {a} a⇇c⋯d ⌞a⌟≡σ[x] c⋯d≡Γ[x]/σ =
      let c⋯d≡j/σ = kd-inj (trans c⋯d≡Γ[x]/σ (cong (A._ElimAsc/ _) Γ[x]≡j))
          c⋯d⇉as/σ⇉k/σ = subst (_ ⊢_⇉∙ _ ⇉ _) (sym c⋯d≡j/σ) (Sp⇉-/ j⇉as⇉k σ∈Γ)
          as≡[] , k/σ≡c⋯d = Sp⇉-⋯ c⋯d⇉as/σ⇉k/σ
          a≡⌜σ[x]⌝ = trans (sym (⌜⌝∘⌞⌟-id a)) (cong ⌜_⌝ ⌞a⌟≡σ[x])
          ⌜σ[x]⌝∙∙as≡a = trans (cong₂ _∙∙_ (sym a≡⌜σ[x]⌝) as≡[]) (∙∙-[] _)
      in inj₁ (subst₂ (_ ⊢Nf_⇇_) (sym ⌜σ[x]⌝∙∙as≡a) (sym k/σ≡c⋯d) a⇇c⋯d)
    ... | ∈-var y Δ-ctx y≡σ[x] Δ[y]≡Γ[x]/σ =
      let Δ[y]≡j/σ = trans Δ[y]≡Γ[x]/σ (cong (A._ElimAsc/ _) Γ[x]≡j)
      in inj₂ (subst (_ ⊢Ne_⇉ _) (cong (_∙∙ _) (cong ⌜_⌝ y≡σ[x]))
                     (⇉-∙ (⇉-var y Δ-ctx Δ[y]≡j/σ) (Sp⇉-/ j⇉as⇉k σ∈Γ)))

    Nf⇉-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
            Γ ⊢Nf a ⇉ k → Δ ⊢/ σ ∈ Γ → Δ ⊢Nf a A.Elim/ σ ⇉ k A.Kind′/ σ
    Nf⇉-/ (⇉-⊥-f Γ-ctx) σ∈Γ = ⇉-⊥-f (/∈-wf σ∈Γ)
    Nf⇉-/ (⇉-⊤-f Γ-ctx) σ∈Γ = ⇉-⊤-f (/∈-wf σ∈Γ)
    Nf⇉-/ (⇉-s-i a∈b⋯c) σ∈Γ with Ne⇉-/ a∈b⋯c σ∈Γ
    ... | inj₁ a/σ⇇b/σ⋯c/σ = Nf⇇-s-i a/σ⇇b/σ⋯c/σ
    ... | inj₂ a/σ⇉b/σ⋯c/σ = ⇉-s-i a/σ⇉b/σ⋯c/σ

    Nf⇇-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Nf a ⇇ k → Δ ⊢/ σ ∈ Γ → Δ ⊢Nf a A.Elim/ σ ⇇ k A.Kind′/ σ
    Nf⇇-/ (⇇-⇑ a⇉j j<∷k) σ∈Γ = ⇇-⇑ (Nf⇉-/ a⇉j σ∈Γ) (<∷-/ j<∷k σ∈Γ)

    Sp⇉-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as j k σ} →
               Γ ⊢ j ⇉∙ as ⇉ k → Δ ⊢/ σ ∈ Γ →
               Δ ⊢ j A.Kind′/ σ ⇉∙ as A.// σ ⇉ k A.Kind′/ σ
    Sp⇉-/ ⇉-[]                                σ∈Γ = ⇉-[]
    Sp⇉-/ (⇉-∷ {a} {j = j} a⇇b⋯c j[a]⇉as⇉k) σ∈Γ =
      ⇉-∷ (Nf⇇-/ a⇇b⋯c σ∈Γ)
          (subst (_ ⊢_⇉∙ _ ⇉ _) (Kind/-sub-↑ j a _)
                 (Sp⇉-/ j[a]⇉as⇉k σ∈Γ))

    <∷-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
              Γ ⊢ j <∷ k → Δ ⊢/ σ ∈ Γ → Δ ⊢ j A.Kind′/ σ <∷ k A.Kind′/ σ
    <∷-/ (<∷-⋯ a₂∼a₁ b₁∼b₂) σ∈Γ =
      <∷-⋯ (∼-/ a₂∼a₁ σ∈Γ) (∼-/ b₁∼b₂ σ∈Γ)
    <∷-/ (<∷-Π a₁∼a₂ b₂∼b₁ k₁<∷k₂) σ∈Γ =
      <∷-Π (∼-/ a₁∼a₂ σ∈Γ) (∼-/ b₂∼b₁ σ∈Γ)
           (<∷-/ k₁<∷k₂ (∈-↑ (<∷-/-wf k₁<∷k₂ σ∈Γ) σ∈Γ))

    ∼-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
              Γ ⊢ a ∼ b → Δ ⊢/ σ ∈ Γ → Δ ⊢ a A.Elim/ σ ∼ b A.Elim/ σ
    ∼-/ (∼-trans a∼b b∼c) σ∈Γ =
      ∼-trans (∼-/ a∼b σ∈Γ) (∼-/ b∼c σ∈Γ)
    ∼-/ (∼-⊥ a⇉a⋯a) σ∈Γ = ∼-⊥ (Nf⇉-/ a⇉a⋯a σ∈Γ)
    ∼-/ (∼-⊤ a⇉a⋯a) σ∈Γ = ∼-⊤ (Nf⇉-/ a⇉a⋯a σ∈Γ)
    ∼-/ (∼-∙ (⇉-var x Γ-ctx Γ[x]≡j) j⇉as∼bs⇉k) σ∈Γ
      with ∈-lift (/∈-lookup σ∈Γ x)
    ... | ∈-nf {a} (⇇-⇑ a⇉c₁⋯d₁ (<∷-⋯ _ _)) ⌞a⌟≡σ[x] c⋯d≡Γ[x]/σ =
      let c⋯d≡j/σ = kd-inj (trans c⋯d≡Γ[x]/σ (cong (A._ElimAsc/ _) Γ[x]≡j))
          c⋯d⇉as/σ∼bs/σ⇉k/σ = subst (_ ⊢_⇉∙ _ ∼ _ ⇉ _) (sym c⋯d≡j/σ)
                                    (Sp∼-/ j⇉as∼bs⇉k σ∈Γ)
          as≡[] , bs≡[] , _ = Sp∼-⋯ c⋯d⇉as/σ∼bs/σ⇉k/σ
          a≡⌜σ[x]⌝ = trans (sym (⌜⌝∘⌞⌟-id a)) (cong ⌜_⌝ ⌞a⌟≡σ[x])
          ⌜σ[x]⌝∙∙as≡a = trans (cong₂ _∙∙_ (sym a≡⌜σ[x]⌝) as≡[]) (∙∙-[] _)
          ⌜σ[x]⌝∙∙bs≡a = trans (cong₂ _∙∙_ (sym a≡⌜σ[x]⌝) bs≡[]) (∙∙-[] _)
      in subst₂ (_ ⊢_∼_) (sym ⌜σ[x]⌝∙∙as≡a) (sym ⌜σ[x]⌝∙∙bs≡a)
                (∼-refl a⇉c₁⋯d₁)
    ... | ∈-var y Δ-ctx y≡σ[x] Δ[y]≡Γ[x]/σ =
      let Δ[y]≡j/σ = trans Δ[y]≡Γ[x]/σ (cong (A._ElimAsc/ _) Γ[x]≡j)
      in subst₂ (_ ⊢_∼_) (cong (_∙∙ _) (cong ⌜_⌝ y≡σ[x]))
                (cong (_∙∙ _) (cong ⌜_⌝ y≡σ[x]))
                (∼-∙ (⇉-var y Δ-ctx Δ[y]≡j/σ) (Sp∼-/ j⇉as∼bs⇉k σ∈Γ))
    ∼-/ (∼-⟨| a∈b⋯c) σ∈Γ with Ne⇉-/ a∈b⋯c σ∈Γ
    ... | inj₁ a⇇b⋯c = ∼-⟨|-Nf⇇ a⇇b⋯c
    ... | inj₂ a⇉b⋯c = ∼-⟨| a⇉b⋯c
    ∼-/ (∼-|⟩ a∈b⋯c) σ∈Γ with Ne⇉-/ a∈b⋯c σ∈Γ
    ... | inj₁ a⇇b⋯c = ∼-|⟩-Nf⇇ a⇇b⋯c
    ... | inj₂ a⇉b⋯c = ∼-|⟩ a⇉b⋯c

    Sp∼-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as bs j k σ} →
                Γ ⊢ j ⇉∙ as ∼ bs ⇉ k → Δ ⊢/ σ ∈ Γ →
                Δ ⊢ j A.Kind′/ σ ⇉∙ as A.// σ ∼ bs A.// σ ⇉ k A.Kind′/ σ
    Sp∼-/ ∼-[] σ∈Γ = ∼-[]
    Sp∼-/ (∼-∷ {a} {j = j} c∼a a∼d a∼b as∼bs) σ∈Γ =
      ∼-∷ (∼-/ c∼a σ∈Γ) (∼-/ a∼d σ∈Γ) (∼-/ a∼b σ∈Γ)
          (subst (_ ⊢_⇉∙ _ ∼ _ ⇉ _) (Kind/-sub-↑ j a _)
                 (Sp∼-/ as∼bs σ∈Γ))

    -- Helpers (to satisfy the termination checker).
    --
    -- These are simply (manual) expansions of the form
    --
    --   XX-/-wf x σ∈Γ  =  wf-/ (wf-∷₁ (XX-ctx x)) σ∈Γ
    --
    -- to ensure the above definitions remain structurally recursive
    -- in the various derivations.

    Nf⇉-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                  kd j ∷ Γ ⊢Nf a ⇉ k → Δ ⊢/ σ ∈ Γ →
                  Δ ⊢ kd (j A.Kind′/ σ) wf
    Nf⇉-/-wf (⇉-⊥-f (j-wf ∷ _)) σ∈Γ = wf-/ j-wf σ∈Γ
    Nf⇉-/-wf (⇉-⊤-f (j-wf ∷ _)) σ∈Γ = wf-/ j-wf σ∈Γ
    Nf⇉-/-wf (⇉-s-i a∈b⋯c)      σ∈Γ = Ne⇉-/-wf a∈b⋯c σ∈Γ

    Ne⇉-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                  kd j ∷ Γ ⊢Ne a ⇉ k → Δ ⊢/ σ ∈ Γ →
                  Δ ⊢ kd (j A.Kind′/ σ) wf
    Ne⇉-/-wf (⇉-∙ x∈k _) σ∈Γ = Var⇉-/-wf x∈k σ∈Γ

    Var⇉-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                   kd j ∷ Γ ⊢Var a ⇉ k → Δ ⊢/ σ ∈ Γ →
                   Δ ⊢ kd (j A.Kind′/ σ) wf
    Var⇉-/-wf (⇉-var x (j-wf ∷ _) _) σ∈Γ = wf-/ j-wf σ∈Γ

    <∷-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k l σ} →
                 kd j ∷ Γ ⊢ k <∷ l → Δ ⊢/ σ ∈ Γ → Δ ⊢ kd (j A.Kind′/ σ) wf
    <∷-/-wf (<∷-⋯ a₂∼a₁ _)   σ∈Γ = ∼-/-wf a₂∼a₁ σ∈Γ
    <∷-/-wf (<∷-Π a₁∼a₂ _ _) σ∈Γ = ∼-/-wf a₁∼a₂ σ∈Γ

    ∼-/-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j σ} →
                 kd j ∷ Γ ⊢ a ∼ b → Δ ⊢/ σ ∈ Γ →
                 Δ ⊢ kd (j A.Kind′/ σ) wf
    ∼-/-wf (∼-trans a∼b _)  σ∈Γ = ∼-/-wf a∼b σ∈Γ
    ∼-/-wf (∼-⊥ a⇉a⋯a)      σ∈Γ = Nf⇉-/-wf a⇉a⋯a σ∈Γ
    ∼-/-wf (∼-⊤ a⇉a⋯a)      σ∈Γ = Nf⇉-/-wf a⇉a⋯a σ∈Γ
    ∼-/-wf (∼-∙ x∈j _)      σ∈Γ = Var⇉-/-wf x∈j σ∈Γ
    ∼-/-wf (∼-⟨| a∈b⋯c)     σ∈Γ = Ne⇉-/-wf a∈b⋯c σ∈Γ
    ∼-/-wf (∼-|⟩ a∈b⋯c)     σ∈Γ = Ne⇉-/-wf a∈b⋯c σ∈Γ

  -- Renamings preserve wrapped variable typing

  NfOrVar∈-/ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
               Γ ⊢NfOrVar a ∈ b → Δ ⊢/ σ ∈ Γ →
               Δ ⊢NfOrVar a A./ σ ∈ b A.ElimAsc/ σ
  NfOrVar∈-/ (∈-nf {a} a⇇c⋯d refl refl) σ∈Γ =
    ∈-nf (Nf⇇-/ a⇇c⋯d σ∈Γ) (A.⌞⌟-/ a) refl
  NfOrVar∈-/ (∈-var x _ refl refl)  σ∈Γ = ∈-lift (/∈-lookup σ∈Γ x)

-- Well-kinded renamings and type substitutions.

module KindedSubstitution where
  open Substitution           using (simple; termSubst)
  open SimpleExt    simple    using (extension)
  open TermSubst    termSubst using (varLift; termLift)
  open ≡-Reasoning

  private
    module S  = Substitution
    module KL = TermLikeLemmas S.termLikeLemmasKind′

  -- Helper lemmas about untyped renamings and substitutions in terms
  -- and kinds.

  varHelpers : TypedSubstAppHelpers varLift
  varHelpers = record
    { Kind/-sub-↑ = λ k a ρ → begin
          (k Kind′[ ⌞ a ⌟ ]) Kind′/Var ρ
        ≡⟨ KL./-sub-↑ k ⌞ a ⌟ ρ ⟩
          (k Kind′/Var ρ VarSubst.↑) Kind′[ ⌞ a ⌟ /Var ρ ]
        ≡⟨ cong ((k Kind′/Var ρ VarSubst.↑) Kind′[_]) (sym (⌞⌟-/Var a)) ⟩
          (k Kind′/Var ρ VarSubst.↑) Kind′[ ⌞ a Elim/Var ρ ⌟ ]
        ∎
    }
    where open S

  termHelpers : TypedSubstAppHelpers termLift
  termHelpers = record
    { Kind/-sub-↑ = λ k a σ → begin
          (k Kind′[ ⌞ a ⌟ ]) Kind′/ σ
        ≡⟨ KL.sub-commutes k ⟩
          (k Kind′/ σ ↑) Kind′[ ⌞ a ⌟ / σ ]
        ≡⟨ cong ((k Kind′/ σ ↑) Kind′[_]) (sym (⌞⌟-/ a)) ⟩
          (k Kind′/ σ ↑) Kind′[ ⌞ a Elim/ σ ⌟ ]
        ∎
    }
    where open S

  -- Kinded type substitutions.

  typedTermSubst : TypedTermSubst ElimAsc Term Level.zero TypedSubstAppHelpers
  typedTermSubst = record
    { _⊢_wf = _⊢_wf
    ; _⊢_∈_ = _⊢NfOrVar_∈_
    ; termLikeLemmas = S.termLikeLemmasElimAsc
    ; varHelpers     = varHelpers
    ; termHelpers    = termHelpers
    ; wf-wf    = wf-ctx
    ; ∈-wf     = NfOrVar∈-ctx
    ; ∈-var    = λ x Γ-ctx → ∈-var x Γ-ctx refl refl
    ; typedApp = TypedSubstApp.NfOrVar∈-/
    }
  open TypedTermSubst typedTermSubst public
    hiding (_⊢_wf; _⊢_∈_; varHelpers; termHelpers; ∈-var; ∈-/Var; ∈-/)
    renaming (lookup to /∈-lookup)
  open TypedSubstApp _⊢Var_∈_ varLiftTyped varHelpers public using ()
    renaming (wf-/ to wf-/Var; ∼-/ to ∼-/Var)
  open Substitution using (weakenElim; weakenElimAsc)

  -- Weakening preserves the various judgments.

  wf-weaken : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a wf → Γ ⊢ b wf →
              (a ∷ Γ) ⊢ weakenElimAsc b wf
  wf-weaken a-wf b-wf = wf-/Var b-wf (Var∈-wk a-wf)

  ∼-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b ∼ c →
             (a ∷ Γ) ⊢ weakenElim b ∼ weakenElim c
  ∼-weaken a-wf b∼c∈k = ∼-/Var b∼c∈k (Var∈-wk a-wf)

  open TypedSubstApp _⊢NfOrVar_∈_ termLiftTyped termHelpers public
  open Substitution using (_Kind′/_; id; sub; _Kind′[_])

  -- Substitution of a single variable or normal form preserves the
  -- kinding judgments.

  kd-[] : ∀ {n} {Γ : Ctx n} {a b c k} →
          kd (b ⋯ c) ∷ Γ ⊢ k kd → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢ k Kind′[ ⌞ a ⌟ ] kd
  kd-[] k-kd a⇇b⋯c = kd-/ k-kd (∈-sub (∈-nf a⇇b⋯c refl refl))

  <∷-[] : ∀ {n} {Γ : Ctx n} {j k a b c} →
          kd (b ⋯ c) ∷ Γ ⊢ j <∷ k → Γ ⊢Nf a ⇇ b ⋯ c →
          Γ ⊢ j Kind′[ ⌞ a ⌟ ] <∷ k Kind′[ ⌞ a ⌟ ]
  <∷-[] j<∷k a⇇b⋯c = <∷-/ j<∷k (∈-sub (∈-nf a⇇b⋯c refl refl))

  -- A typed substitution that narrows the kind of the first type
  -- variable.

  ∈-<∷-sub : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂} →
             Γ ⊢ (a₁ ⋯ b₁) kd → Γ ⊢ a₂ ∼ a₁ → Γ ⊢ b₁ ∼ b₂ →
             kd (a₁ ⋯ b₁) ∷ Γ ⊢/ id ∈ kd (a₂ ⋯ b₂) ∷ Γ
  ∈-<∷-sub a₁⋯b₁-kd a₁∼a₂ b₂∼b₁ =
    ∈-tsub (∈-nf (⇇-⇑ (⇉-s-i x∈a₁⋯a₂) (<∷-⋯ x∼a₂ b₂∼x)) refl refl)
    where
      a₁⋯b₁-wf = wf-kd a₁⋯b₁-kd
      Γ-ctx    = kd-ctx a₁⋯b₁-kd
      x∈a₁⋯a₂  = ⇉-∙ (⇉-var zero (a₁⋯b₁-wf ∷ Γ-ctx) refl) ⇉-[]
      x∼a₂     = ∼-trans (∼-weaken a₁⋯b₁-wf a₁∼a₂) (∼-⟨| x∈a₁⋯a₂)
      b₂∼x     = ∼-trans (∼-|⟩ x∈a₁⋯a₂) (∼-weaken a₁⋯b₁-wf b₂∼b₁)

  -- Narrowing the kind of the first type variable preserves
  -- subkinding

  ⇓-<∷ : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ k₁ k₂} →
         Γ ⊢ (a₁ ⋯ b₁) kd → Γ ⊢ a₂ ∼ a₁ → Γ ⊢ b₁ ∼ b₂ →
         kd (a₂ ⋯ b₂) ∷ Γ ⊢ k₁ <∷ k₂ → kd (a₁ ⋯ b₁) ∷ Γ ⊢ k₁ <∷ k₂
  ⇓-<∷ a₁⋯b₁-kd a₂∼a₁ b₁∼b₂ k₁<∷k₂ =
    subst₂ (_ ⊢_<∷_) (KL.id-vanishes _) (KL.id-vanishes _)
           (<∷-/ k₁<∷k₂ (∈-<∷-sub a₁⋯b₁-kd a₂∼a₁ b₁∼b₂))

-- Operations on well-formed contexts that require weakening of
-- well-formedness judgments.

module WfCtxOps where
  wfWeakenOps : WellFormedWeakenOps weakenOps
  wfWeakenOps = record { wf-weaken = KindedSubstitution.wf-weaken }

  open WellFormedWeakenOps wfWeakenOps public renaming (lookup to lookup-wf)

  -- Lookup the kind of a type variable in a well-formed context.

  lookup-kd : ∀ {m} {Γ : Ctx m} {k} x →
              Γ ctx → ElimCtx.lookup Γ x ≡ kd k → Γ ⊢ k kd
  lookup-kd x Γ-ctx Γ[x]≡kd-k =
    wf-kd-inv (subst (_ ⊢_wf) Γ[x]≡kd-k (lookup-wf Γ-ctx x))

open KindedSubstitution
open WfCtxOps

-- A corollary of context narrowing: transitivity of subkinding is
-- admissible.

<∷-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j <∷ k → Γ ⊢ k <∷ l → Γ ⊢ j <∷ l
<∷-trans (<∷-⋯ a₂∼a₁ b₁∼b₂) (<∷-⋯ a₃∼a₂ b₂∼b₃) =
  <∷-⋯ (∼-trans a₃∼a₂ a₂∼a₁) (∼-trans b₁∼b₂ b₂∼b₃)
<∷-trans (<∷-Π a₁∼a₂ b₂∼b₁ k₁<∷k₂) (<∷-Π a₂∼a₃ b₃∼b₂ k₂<∷k₃) =
  let a₃⋯b₃-kd = wf-kd-inv (wf-∷₁ (<∷-ctx k₂<∷k₃))
  in <∷-Π (∼-trans a₁∼a₂ a₂∼a₃) (∼-trans b₃∼b₂ b₂∼b₁)
          (<∷-trans (⇓-<∷ a₃⋯b₃-kd a₂∼a₃ b₃∼b₂ k₁<∷k₂) k₂<∷k₃)

-- Another corollary: subsumption is admissible in kind checking.

Nf⇇-⇑ : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢Nf a ⇇ j → Γ ⊢ j <∷ k → Γ ⊢Nf a ⇇ k
Nf⇇-⇑ (⇇-⇑ a⇇j₁ j₁<∷j₂) j₂<∷j₃ = ⇇-⇑ a⇇j₁ (<∷-trans j₁<∷j₂ j₂<∷j₃)

-- We can push kind formation proofs through spine kindings.

kd-Sp⇉ : ∀ {n} {Γ : Ctx n} {j as k} →
         Γ ⊢ j kd → Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢ k kd
kd-Sp⇉ j-kd ⇉-[] = j-kd
kd-Sp⇉ (kd-Π b⇉b⋯b c⇉c⋯c j-kd) (⇉-∷ a⇇b⋯c j[a]⇉as⇉k) =
  kd-Sp⇉ (kd-[] j-kd a⇇b⋯c) j[a]⇉as⇉k

-- Kind-validity of neutrals

Var⇉-valid : ∀ {n} {Γ : Ctx n} {x k} → Γ ⊢Var x ⇉ k → Γ ⊢ k kd
Var⇉-valid (⇉-var x Γ-ctx Γ[x]≡k) = lookup-kd x Γ-ctx Γ[x]≡k

Ne⇉-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Ne a ⇉ k → Γ ⊢ k kd
Ne⇉-valid (⇉-∙ x⇉j j⇉as⇉k) = kd-Sp⇉ (Var⇉-valid x⇉j) j⇉as⇉k

-- Left-hand validity of related types and spines

mutual

  ∼-valid₁ : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ∼ b → Γ ⊢Nf a ⇉ a ⋯ a
  ∼-valid₁ (∼-trans a∼b _) = ∼-valid₁ a∼b
  ∼-valid₁ (∼-⊥ b⇉b⋯b) = ⇉-⊥-f (Nf⇉-ctx b⇉b⋯b)
  ∼-valid₁ (∼-⊤ a⇉a⋯a) = a⇉a⋯a
  ∼-valid₁ (∼-∙ x⇉j j⇉as⇉k) = ⇉-s-i (⇉-∙ x⇉j (∼Sp-valid₁ j⇉as⇉k))
  ∼-valid₁ (∼-⟨| a⇉b⋯c) with Ne⇉-valid a⇉b⋯c
  ... | kd-⋯ b⇉b⋯b _ = b⇉b⋯b
  ∼-valid₁ (∼-|⟩ a⇉b⋯c) = ⇉-s-i a⇉b⋯c

  ∼Sp-valid₁ : ∀ {n} {Γ : Ctx n} {j as bs k} →
               Γ ⊢ j ⇉∙ as ∼ bs ⇉ k → Γ ⊢ j ⇉∙ as ⇉ k
  ∼Sp-valid₁ ∼-[] = ⇉-[]
  ∼Sp-valid₁ (∼-∷ c∼a a∼d a∼b j[x]⇉as⇉k) =
    ⇉-∷ (⇇-⇑ (∼-valid₁ a∼b) (<∷-⋯ c∼a a∼d)) (∼Sp-valid₁ j[x]⇉as⇉k)

-- We can push subkinding proofs through spine kindings/relations.

<∷-Sp⇉ : ∀ {n} {Γ : Ctx n} {j₁ j₂ as k₂} →
         Γ ⊢ j₁ <∷ j₂ → Γ ⊢ j₂ ⇉∙ as ⇉ k₂ → ∃ λ k₁ →
         Γ ⊢ j₁ ⇉∙ as ⇉ k₁ × Γ ⊢ k₁ <∷ k₂
<∷-Sp⇉ j₁<∷j₂ ⇉-[] = _ , ⇉-[] , j₁<∷j₂
<∷-Sp⇉ (<∷-Π b₁∼b₂ c₂∼c₁ j₁<∷j₂) (⇉-∷ a⇇b₂⋯c₂ j₂[a]⇉as⇉k₂) =
  let k₁ , j₁[a]⇉as⇉k₁ , k₁<∷k₂ = <∷-Sp⇉ (<∷-[] j₁<∷j₂ a⇇b₂⋯c₂) j₂[a]⇉as⇉k₂
  in  k₁ , ⇉-∷ (Nf⇇-⇑ a⇇b₂⋯c₂ (<∷-⋯ b₁∼b₂ c₂∼c₁)) j₁[a]⇉as⇉k₁ , k₁<∷k₂

<∷-Sp∼ : ∀ {n} {Γ : Ctx n} {j₁ j₂ as bs k₂} →
         Γ ⊢ j₁ <∷ j₂ → Γ ⊢ j₂ ⇉∙ as ∼ bs ⇉ k₂ → ∃ λ k₁ →
         Γ ⊢ j₁ ⇉∙ as ∼ bs ⇉ k₁ × Γ ⊢ k₁ <∷ k₂
<∷-Sp∼ j₁<∷j₂ ∼-[] = _ , ∼-[] , j₁<∷j₂
<∷-Sp∼ (<∷-Π c₁∼c₂ d₂∼d₁ j₁<∷j₂)
       (∼-∷ c₂∼a a∼d₂ a∼b j₂[a]⇉as∼bs⇉k₂) =
  let a⇇c₂⋯d₂ = ⇇-⇑ (∼-valid₁ a∼b) (<∷-⋯ c₂∼a a∼d₂)
      k₁ , j₁[a]⇉as∼bs⇉k₁ , k₁<∷k₂ = <∷-Sp∼ (<∷-[] j₁<∷j₂ a⇇c₂⋯d₂)
                                            j₂[a]⇉as∼bs⇉k₂
  in  k₁ , ∼-∷ (∼-trans c₁∼c₂ c₂∼a) (∼-trans a∼d₂ d₂∼d₁) a∼b j₁[a]⇉as∼bs⇉k₁ ,
      k₁<∷k₂


------------------------------------------------------------------------
-- Squashing of terms

mutual

  squashElim : ∀ {n} → Elim n → Elim n
  squashElim (a ∙ as) = squashHead a ∙ squashSpine as

  squashHead : ∀ {n} → Head n → Head n
  squashHead (var x) = var x
  squashHead ⊥       = ⊥
  squashHead ⊤       = ⊤
  {-# CATCHALL #-}
  squashHead a       = ⊤   -- all other types are squashed into ⊤

  squashSpine : ∀ {n} → Spine n → Spine n
  squashSpine []       = []
  squashSpine (a ∷ as) = squashElim a ∷ squashSpine as

  squashKind : ∀ {n} → Kind Elim n → Kind Elim n
  squashKind (a ⋯ b) = squashElim a ⋯ squashElim b
  squashKind (Π j k) = Π (squashKind j) (squashKind k)

squashAsc : ∀ {n} → ElimAsc n → ElimAsc n
squashAsc (kd k) = kd (squashKind k)
squashAsc (tp a) = tp (squashElim a)

squashCtx : ∀ {n} → Ctx n → Ctx n
squashCtx []      = []
squashCtx (a ∷ Γ) = (squashAsc a) ∷ (squashCtx Γ)

squashTerm : ∀ {n} → Term n → Term n
squashTerm a = ⌞ squashElim ⌜ a ⌝ ⌟

squash-++ : ∀ {n} (as : Spine n) {bs} →
            squashSpine as ++ squashSpine bs ≡ squashSpine (as ++ bs)
squash-++ []       = refl
squash-++ (a ∷ as) = cong (_ ∷_) (squash-++ as)

squash-∙∙ : ∀ {n} (a : Elim n) {bs} →
            squashElim a ∙∙ squashSpine bs ≡ squashElim (a ∙∙ bs)
squash-∙∙ (a ∙ as) = cong (_ ∙_) (squash-++ as)

-- Squashing commutes with generic substitutions.

module SquashSubstAppLemmas {T : ℕ → Set} (l : Lift T Term)
       (squashSub : ∀ {m n} → Sub T m n → Sub T m n)
       (squash-↑  : ∀ {m n} (σ : Sub T m n) →
          Lift._↑ l (squashSub σ) ≡ squashSub (Lift._↑ l σ))
       (squash-lift-lookup : ∀ {m n} (σ : Sub T m n) x →
          ⌜ Lift.lift l (Vec.lookup (squashSub σ) x) ⌝ ≡
          squashElim ⌜ Lift.lift l (Vec.lookup σ x) ⌝)
       where

  open SubstApp l

  -- Squashing commutes with application of generic substitutions.

  mutual

    squashElim-/ : ∀ {m n} {σ : Sub T m n} a →
                   squashElim a Elim/ squashSub σ ≡ squashElim (a Elim/ σ)
    squashElim-/ (a ∙ as) =
      trans (cong₂ _∙∙_ (squashHead-/ a) (squashSpine-/ as)) (squash-∙∙ _)

    squashHead-/ : ∀ {m n} {σ : Sub T m n} a →
                   squashHead a Head/ squashSub σ ≡ squashElim (a Head/ σ)
    squashHead-/ (var x) = squash-lift-lookup _ x
    squashHead-/ ⊥       = refl
    squashHead-/ ⊤       = refl
    squashHead-/ (Π k a) = refl
    squashHead-/ (a ⇒ b) = refl
    squashHead-/ (Λ k a) = refl
    squashHead-/ (ƛ a b) = refl
    squashHead-/ (a ⊡ b) = refl

    squashSpine-/ : ∀ {m n} {σ : Sub T m n} as →
                    squashSpine as // squashSub σ ≡ squashSpine (as // σ)
    squashSpine-/ []       = refl
    squashSpine-/ (a ∷ as) =
      cong₂ _∷_ (squashElim-/ a) (squashSpine-/ as)

    squashKind-/ : ∀ {m n} {σ : Sub T m n} k →
                   squashKind k Kind′/ squashSub σ ≡ squashKind (k Kind′/ σ)
    squashKind-/ (a ⋯ b) = cong₂ _⋯_ (squashElim-/ a) (squashElim-/ b)
    squashKind-/ (Π j k) =
      cong₂ Π (squashKind-/ j)
            (trans (cong (_ Kind′/_) (squash-↑ _)) (squashKind-/ k))

  squashAsc-/ : ∀ {m n} {σ : Sub T m n} a →
                squashAsc a ElimAsc/ squashSub σ ≡ squashAsc (a ElimAsc/ σ)
  squashAsc-/ (kd k) = cong kd (squashKind-/ k)
  squashAsc-/ (tp a) = cong tp (squashElim-/ a)

  squashTerm-/ : ∀ {m n} {σ : Sub T m n} a →
                 squashTerm a / squashSub σ ≡ squashTerm (a / σ)
  squashTerm-/ {σ = σ} a = begin
    ⌞ squashElim ⌜ a ⌝ ⌟ / squashSub σ      ≡˘⟨ ⌞⌟-/ (squashElim ⌜ a ⌝) ⟩
    ⌞ squashElim ⌜ a ⌝ Elim/ squashSub σ ⌟  ≡⟨ cong ⌞_⌟ (squashElim-/ ⌜ a ⌝) ⟩
    ⌞ squashElim (⌜ a ⌝ Elim/ σ) ⌟   ≡˘⟨ cong (⌞_⌟ ∘ squashElim) (⌜⌝-/ a) ⟩
    ⌞ squashElim ⌜ a / σ ⌝ ⌟         ∎
    where open ≡-Reasoning

-- Squashing commutes with renamings and term substitutions.

module SquashSubstLemmas where
  open Substitution
    using (termSubst; _↑; id; sub; weaken; _Kind′/_; _Kind′[_])
  open TermSubst termSubst using (varLift; termLift)
  open ≡-Reasoning

  open SquashSubstAppLemmas varLift (λ x → x) (λ _ → refl) (λ _ _ → refl)
    public using () renaming
    ( squashAsc-/  to squashAsc-/Var
    ; squashTerm-/ to squashTerm-/Var
    )

  -- Squashing applied point-wise to term substitutions.

  squashSub : ∀ {m n} → Sub Term m n → Sub Term m n
  squashSub = Vec.map squashTerm

  -- Helper lemmas about squashed substitutions.

  squash-↑ : ∀ {m n} (σ : Sub Term m n) → (squashSub σ) ↑ ≡ squashSub (σ ↑)
  squash-↑ σ = cong (_ ∷_) (begin
    Vec.map weaken (Vec.map squashTerm σ)  ≡˘⟨ map-∘ weaken squashTerm σ ⟩
    Vec.map (weaken ∘ squashTerm) σ        ≡⟨ map-cong squashTerm-/Var σ ⟩
    Vec.map (squashTerm ∘ weaken) σ        ≡⟨ map-∘ squashTerm weaken σ  ⟩
    Vec.map squashTerm (Vec.map weaken σ)  ∎)

  squash-lookup : ∀ {m n} (σ : Sub Term m n) x →
    ⌜ Vec.lookup (squashSub σ) x ⌝ ≡ squashElim ⌜ Vec.lookup σ x ⌝
  squash-lookup σ x = begin
      ⌜ Vec.lookup (squashSub σ) x ⌝
    ≡⟨ cong ⌜_⌝ (VecProps.lookup-map x squashTerm σ) ⟩
      ⌜ squashTerm (Vec.lookup σ x) ⌝
    ≡⟨ ⌜⌝∘⌞⌟-id (squashElim ⌜ Vec.lookup σ x ⌝) ⟩
      squashElim ⌜ Vec.lookup σ x ⌝
    ∎
  open SquashSubstAppLemmas termLift squashSub squash-↑ squash-lookup public

  squash-id : ∀ {n} → squashSub (id {n}) ≡ id
  squash-id {zero}  = refl
  squash-id {suc n} = cong (var zero ∷_) (begin
    Vec.map squashTerm (Vec.map weaken id)  ≡˘⟨ map-∘ squashTerm weaken id ⟩
    Vec.map (squashTerm ∘ weaken) id        ≡˘⟨ map-cong squashTerm-/Var id ⟩
    Vec.map (weaken ∘ squashTerm) id        ≡⟨ map-∘ weaken squashTerm id ⟩
    Vec.map weaken (Vec.map squashTerm id)  ≡⟨ cong (Vec.map weaken) squash-id ⟩
    Vec.map weaken id                       ∎)

  squash-sub : ∀ {n} (a : Term n) → squashSub (sub a) ≡ sub (squashTerm a)
  squash-sub a = cong (squashTerm a ∷_) squash-id

  -- Squashing commutes with single-variable substitutions in kinds.

  squashKind-[] : ∀ {n} k (a : Elim n) →
                  squashKind (k Kind′[ ⌞ a ⌟ ]) ≡
                    squashKind k Kind′[ ⌞ squashElim a ⌟ ]
  squashKind-[] k a = begin
      squashKind (k Kind′[ ⌞ a ⌟ ])
    ≡˘⟨ squashKind-/ k ⟩
      squashKind k Kind′/ squashSub (sub ⌞ a ⌟)
    ≡⟨ cong (squashKind k Kind′/_) (squash-sub ⌞ a ⌟) ⟩
      squashKind k Kind′[ squashTerm ⌞ a ⌟ ]
    ≡⟨ cong ((squashKind k Kind′[_]) ∘ ⌞_⌟ ∘ squashElim) (⌜⌝∘⌞⌟-id a) ⟩
      squashKind k Kind′[ ⌞ squashElim a ⌟ ]
    ∎

open Substitution using (weakenElimAsc)
open SquashSubstLemmas

-- Context lookup and conversion to vector representation commute with
-- squashing

toVec-squashCtx : ∀ {n} (Γ : Ctx n) →
                  toVec (squashCtx Γ) ≡ Vec.map squashAsc (toVec Γ)
toVec-squashCtx []      = refl
toVec-squashCtx (a ∷ Γ) = cong₂ _∷_ (squashAsc-/Var a) (begin
    Vec.map weakenElimAsc (toVec (squashCtx Γ))
  ≡⟨ cong (Vec.map weakenElimAsc) (toVec-squashCtx Γ) ⟩
    Vec.map weakenElimAsc (Vec.map squashAsc (toVec Γ))
  ≡˘⟨ map-∘ weakenElimAsc squashAsc (toVec Γ) ⟩
    Vec.map (weakenElimAsc ∘ squashAsc) (toVec Γ)
  ≡⟨ map-cong squashAsc-/Var (toVec Γ) ⟩
    Vec.map (squashAsc ∘ weakenElimAsc) (toVec Γ)
  ≡⟨ map-∘ squashAsc weakenElimAsc (toVec Γ) ⟩
    Vec.map squashAsc (Vec.map weakenElimAsc (toVec Γ))
  ∎)
  where open ≡-Reasoning

lookup-squashCtx : ∀ {n} (Γ : Ctx n) x →
                   lookup (squashCtx Γ) x ≡ squashAsc (lookup Γ x)
lookup-squashCtx {n} Γ x = begin
    Vec.lookup (toVec (squashCtx Γ)) x
  ≡⟨ cong (λ Δ → Vec.lookup Δ x) (toVec-squashCtx Γ) ⟩
    Vec.lookup (Vec.map squashAsc (toVec Γ)) x
  ≡⟨ VecProps.lookup-map x squashAsc (toVec Γ) ⟩
    squashAsc (Vec.lookup (toVec Γ) x)
  ∎
  where open ≡-Reasoning


------------------------------------------------------------------------
-- Predicates characterizing first-order kinds, bindings and contexts.

data FOKind {n} : Kind Elim n → Set where
  fo-⋯ : ∀ {a b}   → FOKind (a ⋯ b)
  fo-Π : ∀ {a b k} → FOKind k → FOKind (Π (a ⋯ b) k)

data FOAsc {n} : ElimAsc n → Set where
  fo-kd : ∀ {k} → FOKind k → FOAsc (kd k)

open ContextFormation (λ {n} Γ → FOAsc {n}) public using () renaming
  ( _wf to FOCtx; [] to fo-[]; _∷_ to fo-∷
  ; WellFormedWeakenOps to FOWeakenOps)

<∷-FOKind₂ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → FOKind k
<∷-FOKind₂ (<∷-⋯ _ _)      = fo-⋯
<∷-FOKind₂ (<∷-Π _ _ j<∷k) = fo-Π (<∷-FOKind₂ j<∷k)

module FOSubstAppLemmas {T : ℕ → Set} (l : Lift T Term) where
  open SubstApp l

  FOKind-/ : ∀ {m n k} {σ : Sub T m n} → FOKind k → FOKind (k Kind′/ σ)
  FOKind-/ fo-⋯        = fo-⋯
  FOKind-/ (fo-Π k-fo) = fo-Π (FOKind-/ k-fo)

  FOAsc-/ : ∀ {m n a} {σ : Sub T m n} → FOAsc a → FOAsc (a ElimAsc/ σ)
  FOAsc-/ (fo-kd k-fo) = fo-kd (FOKind-/ k-fo)

module FOSubstLemmas where
  open Substitution using (termSubst)
  open TermSubst termSubst using (varLift; termLift)

  open FOSubstAppLemmas varLift public using ()
    renaming (FOKind-/ to FOKind-/Var; FOAsc-/ to FOAsc-/Var)
  open FOSubstAppLemmas termLift public

  FOAsc-weaken : ∀ {n} {a : ElimAsc n} → FOAsc a → FOAsc (weakenElimAsc a)
  FOAsc-weaken a-fo = FOAsc-/Var a-fo

open FOSubstLemmas

foWeakenOps : FOWeakenOps weakenOps
foWeakenOps = record { wf-weaken = λ _ → FOAsc-weaken }
open FOWeakenOps foWeakenOps public using () renaming (lookup to lookup-FOAsc)

lookup-FOKind : ∀ {m} {Γ : Ctx m} {k} x →
                FOCtx Γ → ElimCtx.lookup Γ x ≡ kd k → FOKind k
lookup-FOKind x Γ-fo Γ[x]≡kd-a with subst FOAsc Γ[x]≡kd-a (lookup-FOAsc Γ-fo x)
... | fo-kd k-fo = k-fo


------------------------------------------------------------------------
-- Reduction of canonical judgments to their reduced forms

open Substitution hiding (subst)

mutual

  reduce-ctx : ∀ {n} {Γ : Ctx n} → FOCtx (squashCtx Γ) →
               Γ C.ctx → squashCtx Γ ctx
  reduce-ctx fo-[] C.[]                        = []
  reduce-ctx (fo-∷ a-fo Γ-fo) (a-wf C.∷ Γ-ctx) =
    reduce-wf Γ-fo a-fo a-wf ∷ reduce-ctx Γ-fo Γ-ctx

  reduce-wf : ∀ {n} {Γ : Ctx n} {a} →
              FOCtx (squashCtx Γ) → FOAsc (squashAsc a) →
              Γ C.⊢ a wf → squashCtx Γ ⊢ squashAsc a wf
  reduce-wf Γ-fo (fo-kd k-fo) (C.wf-kd k-kd)  =
    wf-kd (reduce-kd Γ-fo k-fo k-kd)
  reduce-wf Γ-fo _ (C.wf-tp a⇉a⋯a) = wf-tp (reduce-Nf⇉ Γ-fo a⇉a⋯a)

  reduce-kd : ∀ {n} {Γ : Ctx n} {k} →
              FOCtx (squashCtx Γ) → FOKind (squashKind k) →
              Γ C.⊢ k kd → squashCtx Γ ⊢ squashKind k kd
  reduce-kd Γ-fo _ (C.kd-⋯ a⇉a⋯a b⇉b⋯b) =
    kd-⋯ (reduce-Nf⇉ Γ-fo a⇉a⋯a) (reduce-Nf⇉ Γ-fo b⇉b⋯b)
  reduce-kd Γ-fo (fo-Π k-fo) (C.kd-Π (C.kd-⋯ a⇉a⋯a b⇉b⋯b) k-kd) =
    kd-Π (reduce-Nf⇉ Γ-fo a⇉a⋯a) (reduce-Nf⇉ Γ-fo b⇉b⋯b)
         (reduce-kd (fo-∷ (fo-kd fo-⋯) Γ-fo) k-fo k-kd)
  reduce-kd Γ-fo () (C.kd-Π (C.kd-Π _ _) k-kd)

  reduce-Var∈ : ∀ {n} {Γ : Ctx n} {x k} → FOCtx (squashCtx Γ) →
                Γ C.⊢Var x ∈ k → ∃ λ j →
                squashCtx Γ ⊢Var x ⇉ j × squashCtx Γ ⊢ j <∷ squashKind k
  reduce-Var∈ {_} {Γ} Γ-fo (C.⇉-var x Γ-ctx Γ[x]≡kd-j₁) =
    let Γ-ctx′      = reduce-ctx Γ-fo Γ-ctx
        Γ[x]≡kd-j₁′ = trans (lookup-squashCtx Γ x) (cong squashAsc Γ[x]≡kd-j₁)
    in _ , ⇉-var x Γ-ctx′ Γ[x]≡kd-j₁′ ,
       <∷-refl (lookup-kd x Γ-ctx′ Γ[x]≡kd-j₁′)
  reduce-Var∈ Γ-fo (C.⇇-⇑ x∈k₁ k₁<∷k₂ _) =
    let j , x∈j , j<∷k₁ = reduce-Var∈ Γ-fo x∈k₁
    in  j , x∈j , <∷-trans j<∷k₁ (reduce-<∷ Γ-fo (<∷-FOKind₂ j<∷k₁) k₁<∷k₂)

  reduce-Ne∈ : ∀ {n} {Γ : Ctx n} {a b c} → FOCtx (squashCtx Γ) →
               Γ C.⊢Ne a ∈ (b ⋯ c) →
               squashCtx Γ ⊢Nf squashElim a ⇇ squashKind (b ⋯ c)
  reduce-Ne∈ {_} {Γ} Γ-fo (C.∈-∙ {as = as} x∈j₂ j₂⇉as⇉b₂⋯c₂) =
    let j₁ , x⇉j₁ , j₁<∷j₂ = reduce-Var∈ Γ-fo x∈j₂
        j₂-fo              = <∷-FOKind₂ j₁<∷j₂
        j₂⇉as⇉b₂⋯c₂′       = reduce-Sp⇉ Γ-fo j₂-fo j₂⇉as⇉b₂⋯c₂
        k₁ , j₁⇉as⇉k₁ , k₁<∷b₂⋯c₂        = <∷-Sp⇉ j₁<∷j₂ j₂⇉as⇉b₂⋯c₂′
        _ , _ , b₂∼b₁ , c₁∼c₂ , k₁≡b₁⋯c₁ = <∷-⋯-inv k₁<∷b₂⋯c₂
        j₁⇉as⇉b₁⋯c₁ = subst (squashCtx Γ ⊢ j₁ ⇉∙ squashSpine as ⇉_)
                            k₁≡b₁⋯c₁ j₁⇉as⇉k₁
    in Nf⇇-⇑ (Nf⇇-ne (⇉-∙ x⇉j₁ j₁⇉as⇉b₁⋯c₁)) (<∷-⋯ b₂∼b₁ c₁∼c₂)

  reduce-Nf⇉ : ∀ {n} {Γ : Ctx n} {a b c} → FOCtx (squashCtx Γ) →
               Γ C.⊢Nf a ⇉ b ⋯ c →
               squashCtx Γ ⊢Nf squashElim a ⇉ squashElim b ⋯ squashElim c
  reduce-Nf⇉ Γ-fo (C.⇉-⊥-f Γ-ctx)   = ⇉-⊥-f (reduce-ctx Γ-fo Γ-ctx)
  reduce-Nf⇉ Γ-fo (C.⇉-⊤-f Γ-ctx)   = ⇉-⊤-f (reduce-ctx Γ-fo Γ-ctx)
  reduce-Nf⇉ Γ-fo (C.⇉-∀-f k-kd _)  =
    ⇉-⊤-f (reduce-kd-ctx Γ-fo k-kd)
  reduce-Nf⇉ Γ-fo (C.⇉-→-f a⇉a⋯a _) =
    ⇉-⊤-f (Nf⇉-ctx (reduce-Nf⇉ Γ-fo a⇉a⋯a))
  reduce-Nf⇉ Γ-fo (C.⇉-s-i (C.∈-∙ x∈j j⇉as⇉b⋯c))
    with reduce-Ne∈ Γ-fo (C.∈-∙ x∈j j⇉as⇉b⋯c)
  ... | ⇇-⇑ (⇉-s-i x∙as∈b′⋯c′) (<∷-⋯ _ _) = ⇉-s-i x∙as∈b′⋯c′

  reduce-Nf⇇ : ∀ {n} {Γ : Ctx n} {a b c} → FOCtx (squashCtx Γ) →
               Γ C.⊢Nf a ⇇ b ⋯ c →
               squashCtx Γ ⊢Nf squashElim a ⇇ squashElim b ⋯ squashElim c
  reduce-Nf⇇ Γ-fo (C.⇇-⇑ a⇉b₁⋯c₁ (C.<∷-⋯ b₂<:b₁ c₁<:c₂)) =
    ⇇-⇑ (reduce-Nf⇉ Γ-fo a⇉b₁⋯c₁)
        (<∷-⋯ (reduce-<: Γ-fo b₂<:b₁) (reduce-<: Γ-fo c₁<:c₂))

  reduce-Sp⇉ : ∀ {n} {Γ : Ctx n} {j as k} →
               FOCtx (squashCtx Γ) → FOKind (squashKind j) →
               Γ C.⊢ j ⇉∙ as ⇉ k →
               squashCtx Γ ⊢ squashKind j ⇉∙ squashSpine as ⇉ squashKind k
  reduce-Sp⇉ Γ-fo _ C.⇉-[]                  = ⇉-[]
  reduce-Sp⇉ Γ-fo (fo-Π k-fo)
             (C.⇉-∷ {a} {as} {b ⋯ c} {k} a⇇b⋯c _ k[a∈★]⇉as⇉l) =
    let k[a∈★]≡k[a] = trans (cong squashKind (Kind/⟨★⟩-/ k))
                            (squashKind-[] k a)
        k[a∈★]-fo   = subst FOKind (sym k[a∈★]≡k[a])
                            (FOKind-/ {σ = sub ⌞ squashElim a ⌟} k-fo)
    in ⇉-∷ (reduce-Nf⇇ Γ-fo a⇇b⋯c)
           (subst (_ ⊢_⇉∙ _ ⇉ _) k[a∈★]≡k[a]
                  (reduce-Sp⇉ Γ-fo k[a∈★]-fo k[a∈★]⇉as⇉l))

  reduce-<∷ : ∀ {n} {Γ : Ctx n} {j k} →
              FOCtx (squashCtx Γ) → FOKind (squashKind j) →
              Γ C.⊢ j <∷ k → squashCtx Γ ⊢ squashKind j <∷ squashKind k
  reduce-<∷ Γ-fo a₁⋯a₂-fo (C.<∷-⋯ a₂<:a₁ b₁<:b₂) =
    <∷-⋯ (reduce-<: Γ-fo a₂<:a₁) (reduce-<: Γ-fo b₁<:b₂)
  reduce-<∷ Γ-fo (fo-Π k₁-fo) (C.<∷-Π (C.<∷-⋯ a₁<:a₂ b₂<:b₁) k₁<∷k₂ bb) =
    <∷-Π (reduce-<: Γ-fo a₁<:a₂) (reduce-<: Γ-fo b₂<:b₁)
         (reduce-<∷ (fo-∷ (fo-kd fo-⋯) Γ-fo) k₁-fo k₁<∷k₂)

  reduce-<: : ∀ {n} {Γ : Ctx n} {a b} → FOCtx (squashCtx Γ) →
              Γ C.⊢ a <: b → squashCtx Γ ⊢ squashElim a ∼ squashElim b
  reduce-<: Γ-fo (C.<:-trans a<:b b<:c) =
    ∼-trans (reduce-<: Γ-fo a<:b) (reduce-<: Γ-fo b<:c)
  reduce-<: Γ-fo (C.<:-⊥ b⇉b⋯b) = ∼-⊥ (reduce-Nf⇉ Γ-fo b⇉b⋯b)
  reduce-<: Γ-fo (C.<:-⊤ a⇉a⋯a) = ∼-⊤ (reduce-Nf⇉ Γ-fo a⇉a⋯a)
  reduce-<: Γ-fo (C.<:-∀ _ _ ∀ka⇉⋯) =
    ∼-⊤ (⇉-⊤-f (Nf⇉-ctx (reduce-Nf⇉ Γ-fo ∀ka⇉⋯)))
  reduce-<: Γ-fo (C.<:-→ a₂<:a₁ _) =
    ∼-⊤ (⇉-⊤-f (∼-ctx (reduce-<: Γ-fo a₂<:a₁)))
  reduce-<: {_} {Γ} Γ-fo (C.<:-∙ {as₁ = as} {bs} x∈j₂ j₂⇉as∼bs⇉c₂⋯d₂) =
    let j₁ , x⇉j₁ , j₁<∷j₂ = reduce-Var∈ Γ-fo x∈j₂
        j₂-fo              = <∷-FOKind₂ j₁<∷j₂
        j₂⇉as∼bs⇉c₂⋯d₂′    = reduce-Sp≃ Γ-fo j₂-fo j₂⇉as∼bs⇉c₂⋯d₂
        k₁ , j₁⇉as∼bs⇉k₁ , k₁<∷c₂⋯d₂ = <∷-Sp∼ j₁<∷j₂ j₂⇉as∼bs⇉c₂⋯d₂′
        _ , _ , _ , _ , k₁≡c₁⋯d₁     = <∷-⋯-inv k₁<∷c₂⋯d₂
        j₁⇉as∼bs⇉c₁⋯d₁ = subst (squashCtx Γ ⊢ j₁ ⇉∙ squashSpine as ∼
                                                    squashSpine bs ⇉_)
                               k₁≡c₁⋯d₁ j₁⇉as∼bs⇉k₁
    in ∼-∙ x⇉j₁ j₁⇉as∼bs⇉c₁⋯d₁
  reduce-<: Γ-fo (C.<:-⟨| b∈a⋯c) with reduce-Ne∈ Γ-fo b∈a⋯c
  ... | b⇇a⋯c = ∼-⟨|-Nf⇇ b⇇a⋯c
  reduce-<: Γ-fo (C.<:-|⟩ a∈c⋯b) with reduce-Ne∈ Γ-fo a∈c⋯b
  ... | a⇇c⋯b = ∼-|⟩-Nf⇇ a⇇c⋯b

  reduce-Sp≃ : ∀ {n} {Γ : Ctx n} {j as bs k} →
               FOCtx (squashCtx Γ) → FOKind (squashKind j) →
               Γ C.⊢ j ⇉∙ as ≃ bs ⇉ k →
               squashCtx Γ ⊢ squashKind j ⇉∙ squashSpine as ∼
                                             squashSpine bs ⇉ squashKind k
  reduce-Sp≃ Γ-fo _ C.≃-[] = ∼-[]
  reduce-Sp≃ Γ-fo (fo-Π k-fo)
             (C.≃-∷ {j = c ⋯ d}
                    (C.<:-antisym _
                      (C.<:-⇇ (C.⇇-⇑ a⇉c₁⋯d₁ (C.<∷-⋯ _ _)) _ a<:b) _)
                    k[a∈★]⇉as≃bs⇉l)
             with C.Nf⇉-≡ a⇉c₁⋯d₁
  reduce-Sp≃ Γ-fo (fo-Π k-fo)
             (C.≃-∷ {a} {as} {b} {bs} {c ⋯ d} {k}
                    (C.<:-antisym _
                      (C.<:-⇇ (C.⇇-⇑ a⇉a⋯a (C.<∷-⋯ c<:a a<:d)) _ a<:b) _)
                    k[a∈★]⇉as≃bs⇉l)
             | refl , refl =
    let k[a∈★]≡k[a] = trans (cong squashKind (Kind/⟨★⟩-/ k))
                            (squashKind-[] k a)
        k[a∈★]-fo   = subst FOKind (sym k[a∈★]≡k[a])
                            (FOKind-/ {σ = sub ⌞ squashElim a ⌟} k-fo)
    in ∼-∷ (reduce-<: Γ-fo c<:a) (reduce-<: Γ-fo a<:d)
           (reduce-<: Γ-fo a<:b)
           (subst (_ ⊢_⇉∙ _ ∼ _ ⇉ _) k[a∈★]≡k[a]
                  (reduce-Sp≃ Γ-fo k[a∈★]-fo k[a∈★]⇉as≃bs⇉l))

  -- A helper to satisfy the termination checker.

  reduce-kd-ctx : ∀ {n} {Γ : Ctx n} {k} →
                  FOCtx (squashCtx Γ) → Γ C.⊢ k kd → squashCtx Γ ctx
  reduce-kd-ctx Γ-fo (C.kd-⋯ a⇉a⋯a _) = Nf⇉-ctx (reduce-Nf⇉ Γ-fo a⇉a⋯a)
  reduce-kd-ctx Γ-fo (C.kd-Π j-kd _)  = reduce-kd-ctx Γ-fo j-kd
