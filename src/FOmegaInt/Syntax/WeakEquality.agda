------------------------------------------------------------------------
-- Untyped kind/type/term equality in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Syntax.WeakEquality where

open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Relation
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using ([]; _∷_; _++_)
open import Data.Vec as Vec using ([])
open import Relation.Binary using (IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality as P

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization


------------------------------------------------------------------------
-- Weak untyped kind/type/term equality.
--
-- A "weak" equality that identifies syntactically equal terms and
-- types in elimination form up to type/kind ascriptions in
-- abstractions (lambdas).
--
-- TODO: explain the point of weak equality.

open Syntax

infix 4 _≋_ _≈_ _≈Hd_ _≈Sp_ _≈Asc_ _≈Ctx_ _⟨≈⟩_ _≈?_

mutual

  data _≋_ {n} : Kind Elim n → Kind Elim n → Set where
    ≋-Π : ∀ {j₁ j₂ k₁ k₂} → j₁ ≋ j₂ → k₁ ≋ k₂ → Π j₁ k₁ ≋ Π j₂ k₂
    ≋-⋯ : ∀ {a₁ a₂ b₁ b₂} → a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ ⋯ b₁ ≋ a₂ ⋯ b₂

  data _≈_ {n} : Elim n → Elim n → Set where
    ≈-∙ : ∀ {a₁ a₂ bs₁ bs₂} → a₁ ≈Hd a₂ → bs₁ ≈Sp bs₂ → a₁ ∙ bs₁ ≈ a₂ ∙ bs₂

  data _≈Hd_ {n} : Head n → Head n → Set where
    ≈-var : ∀ x →                                           var x ≈Hd var x
    ≈-⊥   :                                                     ⊥ ≈Hd ⊥
    ≈-⊤   :                                                     ⊤ ≈Hd ⊤
    ≈-∀   : ∀ {k₁ k₂ a₁ a₂} → k₁ ≋ k₂         → a₁ ≈ a₂ → Π k₁ a₁ ≈Hd Π k₂ a₂
    ≈-→   : ∀ {a₁ a₂ b₁ b₂} → a₁ ≈ a₂         → b₁ ≈ b₂ → a₁ ⇒ b₁ ≈Hd a₂ ⇒ b₂
    ≈-Λ   : ∀ {k₁ k₂ a₁ a₂} → ⌊ k₁ ⌋ ≡ ⌊ k₂ ⌋ → a₁ ≈ a₂ → Λ k₁ a₁ ≈Hd Λ k₂ a₂
    ≈-λ   : ∀ {a₁ a₂ b₁ b₂}                   → b₁ ≈ b₂ → ƛ a₁ b₁ ≈Hd ƛ a₂ b₂
    ≈-⊡   : ∀ {a₁ a₂ b₁ b₂} → a₁ ≈ a₂         → b₁ ≈ b₂ → a₁ ⊡ b₁ ≈Hd a₂ ⊡ b₂

  data _≈Sp_ {n} : Spine n → Spine n → Set where
    ≈-[] :                                                   [] ≈Sp []
    ≈-∷  : ∀ {a₁ a₂ bs₁ bs₂} → a₁ ≈ a₂ → bs₁ ≈Sp bs₂ → a₁ ∷ bs₁ ≈Sp a₂ ∷ bs₂

data _≈Asc_ {n} : ElimAsc n → ElimAsc n → Set where
  ≈-kd : ∀ {k₁ k₂} → k₁ ≋ k₂ → kd k₁ ≈Asc kd k₂
  ≈-tp : ∀ {a₁ a₂} → a₁ ≈ a₂ → tp a₁ ≈Asc tp a₂

open ElimCtx hiding (_++_)

data _≈Ctx_ : ∀ {n} → Ctx n → Ctx n → Set where
  ≈-[] : [] ≈Ctx []
  ≈-∷  : ∀ {n a₁ a₂} {Γ₁ Γ₂ : Ctx n} →
         a₁ ≈Asc a₂ → Γ₁ ≈Ctx Γ₂ → a₁ ∷ Γ₁ ≈Ctx a₂ ∷ Γ₂

-- Weak equality of single-variable substations and results.

data _⟨≈⟩_ : ∀ {m n} → SVSub m n → SVSub m n → Set where
  ≈-sub : ∀ {n}   {a b : Elim n}    →  a ≈ b  → sub a ⟨≈⟩ sub b
  ≈-↑   : ∀ {m n} {σ τ : SVSub m n} → σ ⟨≈⟩ τ →   σ ↑ ⟨≈⟩ τ ↑

data _≈?_ {n} : SVRes n → SVRes n → Set where
  ≈-hit  : ∀ {a b : Elim n} → a ≈ b →  hit a ≈? hit b
  ≈-miss : ∀ (x : Fin n)            → miss x ≈? miss x

-- Shorthands.

≈-var∙ : ∀ {n} (x : Fin n) → var∙ x ≈ var∙ x
≈-var∙ x = ≈-∙ (≈-var x) ≈-[]

≈-⊥∙ : ∀ {n} → _≈_ {n = n} ⊥∙ ⊥∙
≈-⊥∙ = ≈-∙ (≈-⊥) ≈-[]

≈-⊤∙ : ∀ {n} → _≈_ {n = n} ⊤∙ ⊤∙
≈-⊤∙ = ≈-∙ (≈-⊤) ≈-[]

≈-∀∙ : ∀ {n} {k₁ k₂ : Kind Elim n} {a₁ a₂} →
       k₁ ≋ k₂ → a₁ ≈ a₂ → ∀∙ k₁ a₁ ≈ ∀∙ k₂ a₂
≈-∀∙ k₁≋k₂ a₁≈a₂ = ≈-∙ (≈-∀ k₁≋k₂ a₁≈a₂) ≈-[]

≈-⇒∙ : ∀ {n} {a₁ a₂ : Elim n} {b₁ b₂} →
       a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ ⇒∙ b₁ ≈ a₂ ⇒∙ b₂
≈-⇒∙ a₁≈a₂ b₁≈b₂ = ≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) ≈-[]

≈-Λ∙ : ∀ {n} {k₁ k₂ : Kind Elim n} {a₁ a₂} → ⌊ k₁ ⌋ ≡ ⌊ k₂ ⌋ → a₁ ≈ a₂ →
       Λ∙ k₁ a₁ ≈ Λ∙ k₂ a₂
≈-Λ∙ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂ = ≈-∙ (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) ≈-[]

≈-λ∙ : ∀ {n} {a₁ a₂ : Elim n} {b₁ b₂} → b₁ ≈ b₂ → ƛ∙ a₁ b₁ ≈ ƛ∙ a₂ b₂
≈-λ∙ a₁≈a₂ = ≈-∙ (≈-λ a₁≈a₂) ≈-[]

≈-⊡∙ : ∀ {n} {a₁ a₂ : Elim n} {b₁ b₂} →
       a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ ⊡ b₁ ∙ [] ≈ a₂ ⊡ b₂ ∙ []
≈-⊡∙ a₁≈a₂ b₁≈b₂ = ≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) ≈-[]


------------------------------------------------------------------------
-- Simple properties of weake equality.

-- Some simple congruence rules w.r.t. operations on spines and
-- eliminations.

≈-++ : ∀ {n} {as₁ as₂ : Spine n} {bs₁ bs₂} →
       as₁ ≈Sp as₂ → bs₁ ≈Sp bs₂ → as₁ ++ bs₁ ≈Sp as₂ ++ bs₂
≈-++ ≈-[]                bs₁≈bs₂ = bs₁≈bs₂
≈-++ (≈-∷ a₁≈a₂ as₁≈as₂) bs₁≈bs₂ = ≈-∷ a₁≈a₂ (≈-++ as₁≈as₂ bs₁≈bs₂)

≈-∙∙ : ∀ {n} {a₁ a₂ : Elim n} {bs₁ bs₂} →
       a₁ ≈ a₂ → bs₁ ≈Sp bs₂ → a₁ ∙∙ bs₁ ≈ a₂ ∙∙ bs₂
≈-∙∙ (≈-∙ a₁≈a₂ as₁≈as₂) bs₁≈bs₂ = ≈-∙ a₁≈a₂ (≈-++ as₁≈as₂ bs₁≈bs₂)

≈-⌜·⌝ : ∀ {n} {a₁ a₂ : Elim n} {b₁ b₂} →
        a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ ⌜·⌝ b₁ ≈ a₂ ⌜·⌝ b₂
≈-⌜·⌝ a₁≈a₂ b₁≈b₂ = ≈-∙∙ a₁≈a₂ (≈-∷ b₁≈b₂ ≈-[])

-- Weakly equal kinds simplify equally.
≋-⌊⌋ : ∀ {n} {k₁ k₂ : Kind Elim n} → k₁ ≋ k₂ → ⌊ k₁ ⌋ ≡ ⌊ k₂ ⌋
≋-⌊⌋ (≋-Π j₁≋j₂ k₁≋k₂) = cong₂ _⇒_ (≋-⌊⌋ j₁≋j₂) (≋-⌊⌋ k₁≋k₂)
≋-⌊⌋ (≋-⋯ a₁≈a₂ b₁≈b₂) = refl

module _ where
  open SimpleCtx          using (kd; ⌊_⌋Asc)
  open ContextConversions using (⌊_⌋Ctx)

  -- Weakly equal ascriptions and contexts simplify equally.

  ≈Asc-⌊⌋ : ∀ {n} {a₁ a₂ : ElimAsc n} → a₁ ≈Asc a₂ → ⌊ a₁ ⌋Asc ≡ ⌊ a₂ ⌋Asc
  ≈Asc-⌊⌋ (≈-kd k₁≋k₂) = cong kd (≋-⌊⌋ k₁≋k₂)
  ≈Asc-⌊⌋ (≈-tp a₁≈a₂) = refl

  ≈Ctx-⌊⌋ : ∀ {n} {Γ₁ Γ₂ : Ctx n} → Γ₁ ≈Ctx Γ₂ → ⌊ Γ₁ ⌋Ctx ≡ ⌊ Γ₂ ⌋Ctx
  ≈Ctx-⌊⌋ ≈-[]              = refl
  ≈Ctx-⌊⌋ (≈-∷ a₁≈a₂ Γ₁≈Γ₂) = cong₂ _∷_ (≈Asc-⌊⌋ a₁≈a₂) (≈Ctx-⌊⌋ Γ₁≈Γ₂)

-- Reflexivity of weak equality.

mutual

  ≋-refl : ∀ {n} (k : Kind Elim n) → k ≋ k
  ≋-refl (a ⋯ b) = ≋-⋯ (≈-refl a) (≈-refl b)
  ≋-refl (Π j k) = ≋-Π (≋-refl j) (≋-refl k)

  ≈-refl : ∀ {n} (a : Elim n) → a ≈ a
  ≈-refl (a ∙ as) = ≈-∙ (≈Hd-refl a) (≈Sp-refl as)

  ≈Hd-refl : ∀ {n} (a : Head n) → a ≈Hd a
  ≈Hd-refl (var x) = ≈-var x
  ≈Hd-refl ⊥       = ≈-⊥
  ≈Hd-refl ⊤       = ≈-⊤
  ≈Hd-refl (Π k a) = ≈-∀ (≋-refl k) (≈-refl a)
  ≈Hd-refl (a ⇒ b) = ≈-→ (≈-refl a) (≈-refl b)
  ≈Hd-refl (Λ k a) = ≈-Λ refl (≈-refl a)
  ≈Hd-refl (ƛ a b) = ≈-λ (≈-refl b)
  ≈Hd-refl (a ⊡ b) = ≈-⊡ (≈-refl a) (≈-refl b)

  ≈Sp-refl : ∀ {n} (as : Spine n) → as ≈Sp as
  ≈Sp-refl []       = ≈-[]
  ≈Sp-refl (a ∷ as) = ≈-∷ (≈-refl a) (≈Sp-refl as)

≈Asc-refl : ∀ {n} (a : ElimAsc n) → a ≈Asc a
≈Asc-refl (kd k) = ≈-kd (≋-refl k)
≈Asc-refl (tp a) = ≈-tp (≈-refl a)

≈Ctx-refl : ∀ {n} (Γ : Ctx n) → Γ ≈Ctx Γ
≈Ctx-refl []      = ≈-[]
≈Ctx-refl (a ∷ Γ) = ≈-∷ (≈Asc-refl a) (≈Ctx-refl Γ)


-- Transitivity of weak equality.

mutual

  ≋-trans : ∀ {n} {j k l : Kind Elim n} → j ≋ k → k ≋ l → j ≋ l
  ≋-trans (≋-Π j₁≋j₂ k₁≋k₂) (≋-Π j₂≋j₃ k₂≋k₃) =
    ≋-Π (≋-trans j₁≋j₂ j₂≋j₃) (≋-trans k₁≋k₂ k₂≋k₃)
  ≋-trans (≋-⋯ a₁≈a₂ b₁≈b₂) (≋-⋯ a₂≈a₃ b₂≈b₃) =
    ≋-⋯ (≈-trans a₁≈a₂ a₂≈a₃) (≈-trans b₁≈b₂ b₂≈b₃)

  ≈-trans : ∀ {n} {a b c : Elim n} → a ≈ b → b ≈ c → a ≈ c
  ≈-trans (≈-∙ a₁≈a₂ bs₁≈bs₂) (≈-∙ a₂≈a₃ bs₂≈bs₃) =
    ≈-∙ (≈Hd-trans a₁≈a₂ a₂≈a₃) (≈Sp-trans bs₁≈bs₂ bs₂≈bs₃)

  ≈Hd-trans : ∀ {n} {a b c : Head n} → a ≈Hd b → b ≈Hd c → a ≈Hd c
  ≈Hd-trans (≈-var x)         (≈-var .x)        = ≈-var x
  ≈Hd-trans ≈-⊥               ≈-⊥               = ≈-⊥
  ≈Hd-trans ≈-⊤               ≈-⊤               = ≈-⊤
  ≈Hd-trans (≈-∀ k₁≋k₂ a₁≈a₂) (≈-∀ k₂≋k₃ a₂≈a₃) =
    ≈-∀ (≋-trans k₁≋k₂ k₂≋k₃) (≈-trans a₁≈a₂ a₂≈a₃)
  ≈Hd-trans (≈-→ a₁≈a₂ b₁≈b₂) (≈-→ a₂≈a₃ b₂≈b₃) =
    ≈-→ (≈-trans a₁≈a₂ a₂≈a₃) (≈-trans b₁≈b₂ b₂≈b₃)
  ≈Hd-trans (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) (≈-Λ ⌊k₂⌋≡⌊k₃⌋ a₂≈a₃) =
    ≈-Λ (trans ⌊k₁⌋≡⌊k₂⌋ ⌊k₂⌋≡⌊k₃⌋) (≈-trans a₁≈a₂ a₂≈a₃)
  ≈Hd-trans (≈-λ a₁≈a₂)       (≈-λ a₂≈a₃)       = ≈-λ (≈-trans a₁≈a₂ a₂≈a₃)
  ≈Hd-trans (≈-⊡ a₁≈a₂ b₁≈b₂) (≈-⊡ a₂≈a₃ b₂≈b₃) =
    ≈-⊡ (≈-trans a₁≈a₂ a₂≈a₃) (≈-trans b₁≈b₂ b₂≈b₃)

  ≈Sp-trans : ∀ {n} {as bs cs : Spine n} → as ≈Sp bs → bs ≈Sp cs → as ≈Sp cs
  ≈Sp-trans ≈-[]                ≈-[]                = ≈-[]
  ≈Sp-trans (≈-∷ a₁≈a₂ bs₁≈bs₂) (≈-∷ a₂≈a₃ bs₂≈bs₃) =
    ≈-∷ (≈-trans a₁≈a₂ a₂≈a₃) (≈Sp-trans bs₁≈bs₂ bs₂≈bs₃)

≈Asc-trans : ∀ {n} {a b c : ElimAsc n} → a ≈Asc b → b ≈Asc c → a ≈Asc c
≈Asc-trans (≈-kd k₁≋k₂) (≈-kd k₂≋k₃) = ≈-kd (≋-trans k₁≋k₂ k₂≋k₃)
≈Asc-trans (≈-tp a₁≈a₂) (≈-tp a₂≈a₃) = ≈-tp (≈-trans a₁≈a₂ a₂≈a₃)

≈Ctx-trans : ∀ {n} {Γ Δ E : Ctx n} → Γ ≈Ctx Δ → Δ ≈Ctx E → Γ ≈Ctx E
≈Ctx-trans ≈-[]              ≈-[]                = ≈-[]
≈Ctx-trans (≈-∷ a₁≈a₂ Γ₁≈Γ₂) (≈-∷ a₂≈a₃ Γ₂≈Γ₃) =
  ≈-∷ (≈Asc-trans a₁≈a₂ a₂≈a₃) (≈Ctx-trans Γ₁≈Γ₂ Γ₂≈Γ₃)

-- Symmetry of weak equality.

mutual

  ≋-sym : ∀ {n} {j k : Kind Elim n} → j ≋ k → k ≋ j
  ≋-sym (≋-⋯ a₁≈a₂ b₁≈b₂) = ≋-⋯ (≈-sym a₁≈a₂) (≈-sym b₁≈b₂)
  ≋-sym (≋-Π j₁≋j₂ k₁≋k₂) = ≋-Π (≋-sym j₁≋j₂) (≋-sym k₁≋k₂)

  ≈-sym : ∀ {n} {a b : Elim n} → a ≈ b → b ≈ a
  ≈-sym (≈-∙ a≈b as≈bs) = ≈-∙ (≈Hd-sym a≈b) (≈Sp-sym as≈bs)

  ≈Hd-sym : ∀ {n} {a b : Head n} → a ≈Hd b → b ≈Hd a
  ≈Hd-sym (≈-var x)             = ≈-var x
  ≈Hd-sym ≈-⊥                   = ≈-⊥
  ≈Hd-sym ≈-⊤                   = ≈-⊤
  ≈Hd-sym (≈-∀ k₁≋k₂ a₁≈a₂)     = ≈-∀ (≋-sym k₁≋k₂) (≈-sym a₁≈a₂)
  ≈Hd-sym (≈-→ a₁≈a₂ b₁≈b₂)     = ≈-→ (≈-sym a₁≈a₂) (≈-sym b₁≈b₂)
  ≈Hd-sym (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) = ≈-Λ (sym ⌊k₁⌋≡⌊k₂⌋) (≈-sym a₁≈a₂)
  ≈Hd-sym (≈-λ a₁≈a₂)           = ≈-λ (≈-sym a₁≈a₂)
  ≈Hd-sym (≈-⊡ a₁≈a₂ b₁≈b₂)     = ≈-⊡ (≈-sym a₁≈a₂) (≈-sym b₁≈b₂)

  ≈Sp-sym : ∀ {n} {as bs : Spine n} → as ≈Sp bs → bs ≈Sp as
  ≈Sp-sym ≈-[]                = ≈-[]
  ≈Sp-sym (≈-∷ a₁≈a₂ as₁≈as₂) = ≈-∷ (≈-sym a₁≈a₂) (≈Sp-sym as₁≈as₂)

≈Asc-sym : ∀ {n} {a b : ElimAsc n} → a ≈Asc b → b ≈Asc a
≈Asc-sym (≈-kd j≋k) = ≈-kd (≋-sym j≋k)
≈Asc-sym (≈-tp a≈b) = ≈-tp (≈-sym a≈b)

≈Ctx-sym : ∀ {n} {Γ Δ : Ctx n} → Γ ≈Ctx Δ → Δ ≈Ctx Γ
≈Ctx-sym ≈-[]              = ≈-[]
≈Ctx-sym (≈-∷ a₁≈a₂ Γ₁≈Γ₂) = ≈-∷ (≈Asc-sym a₁≈a₂) (≈Ctx-sym Γ₁≈Γ₂)

-- Weak equality is an equivalence relation.

≋-isEquivalence : (n : ℕ) → IsEquivalence (_≋_ {n})
≋-isEquivalence n = record
  { refl  = λ {k} → ≋-refl k
  ; sym   = ≋-sym
  ; trans = ≋-trans
  }

≈-isEquivalence : (n : ℕ) → IsEquivalence (_≈_ {n})
≈-isEquivalence n = record
  { refl  = λ {k} → ≈-refl k
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

≈Hd-isEquivalence : (n : ℕ) → IsEquivalence (_≈Hd_ {n})
≈Hd-isEquivalence n = record
  { refl  = λ {k} → ≈Hd-refl k
  ; sym   = ≈Hd-sym
  ; trans = ≈Hd-trans
  }

≈Sp-isEquivalence : (n : ℕ) → IsEquivalence (_≈Sp_ {n})
≈Sp-isEquivalence n = record
  { refl  = λ {k} → ≈Sp-refl k
  ; sym   = ≈Sp-sym
  ; trans = ≈Sp-trans
  }

≈Asc-isEquivalence : (n : ℕ) → IsEquivalence (_≈Asc_ {n})
≈Asc-isEquivalence n = record
  { refl  = λ {k} → ≈Asc-refl k
  ; sym   = ≈Asc-sym
  ; trans = ≈Asc-trans
  }

≈Ctx-isEquivalence : (n : ℕ) → IsEquivalence (_≈Ctx_ {n})
≈Ctx-isEquivalence n = record
  { refl  = λ {k} → ≈Ctx-refl k
  ; sym   = ≈Ctx-sym
  ; trans = ≈Ctx-trans
  }

-- Kinds together with weak equality form a setoid.
≋-setoid : ℕ → Setoid _ _
≋-setoid n = record
  { Carrier       = Kind Elim n
  ; _≈_           = _≋_
  ; isEquivalence = ≋-isEquivalence n
  }

-- Types and terms together with weak equality form a setoid.

≈-setoid : ℕ → Setoid _ _
≈-setoid n = record
  { Carrier       = Elim n
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence n
  }

≈Hd-setoid : ℕ → Setoid _ _
≈Hd-setoid n = record
  { Carrier       = Head n
  ; _≈_           = _≈Hd_
  ; isEquivalence = ≈Hd-isEquivalence n
  }

≈Sp-setoid : ℕ → Setoid _ _
≈Sp-setoid n = record
  { Carrier       = Spine n
  ; _≈_           = _≈Sp_
  ; isEquivalence = ≈Sp-isEquivalence n
  }

≈Asc-setoid : ℕ → Setoid _ _
≈Asc-setoid n = record
  { Carrier       = ElimAsc n
  ; _≈_           = _≈Asc_
  ; isEquivalence = ≈Asc-isEquivalence n
  }

≈Ctx-setoid : ℕ → Setoid _ _
≈Ctx-setoid n = record
  { Carrier       = Ctx n
  ; _≈_           = _≈Ctx_
  ; isEquivalence = ≈Ctx-isEquivalence n
  }

-- Equational reasoning for weak equality.
module ≈-Reasoning {n : ℕ} where
  open SetoidReasoning (≈-setoid n) public
  module Kd = SetoidReasoning (≋-setoid n)
  module Hd = SetoidReasoning (≈Hd-setoid n)
  module Sp = SetoidReasoning (≈Sp-setoid n)
  module Asc = SetoidReasoning (≈Asc-setoid n)
  module Ctx = SetoidReasoning (≈Ctx-setoid n)


------------------------------------------------------------------------
-- Substitution lemmas for weak equality.

-- Renamings in weakly equal terms.
--
-- The substitution lemmas below establishe that renamings of
-- variables in kinds, heads, eliminations and spines preserve weak
-- equality:
--
--                                ≈
--                           a ------→ b
--                           |         |
--                       -/ρ |         | -/ρ
--                           ↓    ≈    ↓
--                          a/ρ ····→ b/ρ
--
-- where ρ is a renaming.
module Renaming where
  open Substitution
  module V = VarSubst

  mutual

    -- Renamings preserve weak equality.

    ≋-/Var : ∀ {m n k₁ k₂} →
             k₁ ≋ k₂ → (ρ : Sub Fin m n) → k₁ Kind′/Var ρ ≋ k₂ Kind′/Var ρ
    ≋-/Var (≋-Π j₁≋j₂ k₁≋k₂) ρ =
      ≋-Π (≋-/Var j₁≋j₂ ρ) (≋-/Var k₁≋k₂ (ρ V.↑))
    ≋-/Var (≋-⋯ a₁≈a₂ b₁≈b₂) ρ =
      ≋-⋯ (≈-/Var a₁≈a₂ ρ) (≈-/Var b₁≈b₂ ρ)

    ≈-/Var : ∀ {m n a₁ a₂} →
             a₁ ≈ a₂ → (ρ : Sub Fin m n) → a₁ Elim/Var ρ ≈ a₂ Elim/Var ρ
    ≈-/Var (≈-∙ a₁≈a₂ bs₁≈bs₂) ρ =
      ≈-∙∙ (≈Hd-/Var a₁≈a₂ ρ) (≈Sp-/Var bs₁≈bs₂ ρ)

    ≈Hd-/Var : ∀ {m n a₁ a₂} →
               a₁ ≈Hd a₂ → (ρ : Sub Fin m n) → a₁ Head/Var′ ρ ≈ a₂ Head/Var′ ρ
    ≈Hd-/Var (≈-var x)             ρ = ≈-var∙ (Vec.lookup ρ x)
    ≈Hd-/Var ≈-⊥                   ρ = ≈-⊥∙
    ≈Hd-/Var ≈-⊤                   ρ = ≈-⊤∙
    ≈Hd-/Var (≈-∀ k₁≋k₂ a₁≈a₂)     ρ =
      ≈-∀∙ (≋-/Var k₁≋k₂ ρ) (≈-/Var a₁≈a₂ (ρ V.↑))
    ≈Hd-/Var (≈-→ a₁≈a₂ b₁≈b₂)     ρ =
      ≈-⇒∙ (≈-/Var a₁≈a₂ ρ) (≈-/Var b₁≈b₂ ρ)
    ≈Hd-/Var (≈-Λ {k₁} {k₂} ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) ρ =
      ≈-Λ∙ (begin
             ⌊ k₁ Kind′/Var _ ⌋   ≡⟨ ⌊⌋-Kind′/Var k₁ ⟩
             ⌊ k₁ ⌋               ≡⟨ ⌊k₁⌋≡⌊k₂⌋ ⟩
             ⌊ k₂ ⌋               ≡⟨ sym (⌊⌋-Kind′/Var k₂) ⟩
             ⌊ k₂ Kind′/Var _ ⌋   ∎)
           (≈-/Var a₁≈a₂ (ρ V.↑))
      where open ≡-Reasoning
    ≈Hd-/Var (≈-λ a₁≈a₂)           ρ = ≈-λ∙ (≈-/Var a₁≈a₂ (ρ V.↑))
    ≈Hd-/Var (≈-⊡ a₁≈a₂ b₁≈b₂)     ρ =
      ≈-⊡∙ (≈-/Var a₁≈a₂ ρ) (≈-/Var b₁≈b₂ ρ)

    ≈Sp-/Var : ∀ {m n as₁ as₂} →
               as₁ ≈Sp as₂ → (ρ : Sub Fin m n) → as₁ //Var ρ ≈Sp as₂ //Var ρ
    ≈Sp-/Var ≈-[]                ρ = ≈-[]
    ≈Sp-/Var (≈-∷ a₁≈a₂ as₁≈as₂) ρ =
      ≈-∷ (≈-/Var a₁≈a₂ ρ) (≈Sp-/Var as₁≈as₂ ρ)

  ≈?-/Var : ∀ {m n r₁ r₂} →
            r₁ ≈? r₂ → (ρ : Sub Fin m n) → r₁ ?/Var ρ ≈? r₂ ?/Var ρ
  ≈?-/Var (≈-hit a₁≈a₂) ρ = ≈-hit (≈-/Var a₁≈a₂ ρ)
  ≈?-/Var (≈-miss x)    ρ = ≈-miss (Vec.lookup ρ x)

  ≈-weakenElim : ∀ {n} {a₁ a₂ : Elim n} →
                 a₁ ≈ a₂ → weakenElim a₁ ≈ weakenElim a₂
  ≈-weakenElim a₁≈a₂ = ≈-/Var a₁≈a₂ V.wk

  ≈-weakenSVRes : ∀ {n} {r₁ r₂ : SVRes n} →
                  r₁ ≈? r₂ → weakenSVRes r₁ ≈? weakenSVRes r₂
  ≈-weakenSVRes r₁≈r₂ = ≈?-/Var r₁≈r₂ V.wk

open Renaming

-- Look up a weak equation in a pair of pointwise weakly equal
-- single-variable substitutions.

⟨≈⟩-lookup : ∀ {m n σ₁} {σ₂ : SVSub m n} →
             σ₁ ⟨≈⟩ σ₂ → (x : Fin m) → lookupSV σ₁ x ≈? lookupSV σ₂ x
⟨≈⟩-lookup (≈-sub a₁≈a₂) zero    = ≈-hit a₁≈a₂
⟨≈⟩-lookup (≈-sub a₁≈a₂) (suc x) = ≈-miss x
⟨≈⟩-lookup (≈-↑ σ₁≈σ₂)   zero    = ≈-miss zero
⟨≈⟩-lookup (≈-↑ σ₁≈σ₂)   (suc x) = ≈-weakenSVRes (⟨≈⟩-lookup σ₁≈σ₂ x)

-- Weak equality lifted to hereditary substitutions.
--
-- The substitution lemmas below establishe that simoultaneous
-- hereditary substitutions of weakly equal types or terms in kinds,
-- heads, eliminations and spines preserve weak equality:
--
--                                ≈
--                           a ------- b
--                           |         |
--                      -/σ₁ |         | -/σ₂
--                           ↓    ≈    ↓
--                          a/σ₁ ···· b/σ₂
--
-- where σ₁ and σ₁ are weakly equal hereditary substitutions.

module WeakHereditarySubstitutionEquality where
  open Substitution hiding (_↑; sub)

  mutual

    -- Point-wise weakly equal hereditary substitutions preserve weak
    -- equality.

    ≋-/⟨⟩ : ∀ {k m n j₁ j₂} {σ₁ σ₂ : SVSub m n} →
            j₁ ≋ j₂ → σ₁ ⟨≈⟩ σ₂ → j₁ Kind/⟨ k ⟩ σ₁ ≋ j₂ Kind/⟨ k ⟩ σ₂
    ≋-/⟨⟩ (≋-Π j₁≋j₂ k₁≋k₂) σ₁≈σ₂ =
      ≋-Π (≋-/⟨⟩ j₁≋j₂ σ₁≈σ₂) (≋-/⟨⟩ k₁≋k₂ (≈-↑ σ₁≈σ₂))
    ≋-/⟨⟩ (≋-⋯ a₁≈a₂ b₁≈b₂) σ₁≈σ₂ =
      ≋-⋯ (≈-/⟨⟩ a₁≈a₂ σ₁≈σ₂) (≈-/⟨⟩ b₁≈b₂ σ₁≈σ₂)

    ≈-/⟨⟩ : ∀ {k m n a₁ a₂} {σ₁ σ₂ : SVSub m n} →
            a₁ ≈ a₂ → σ₁ ⟨≈⟩ σ₂ → a₁ /⟨ k ⟩ σ₁ ≈ a₂ /⟨ k ⟩ σ₂
    ≈-/⟨⟩ (≈-∙ (≈-var x) bs₁≈bs₂) σ₁≈σ₂ =
      ≈-?∙∙⟨⟩ _ (⟨≈⟩-lookup σ₁≈σ₂ x) (≈Sp-/⟨⟩ bs₁≈bs₂ σ₁≈σ₂)
    ≈-/⟨⟩ (≈-∙ ≈-⊥ bs₁≈bs₂) σ₁≈σ₂ = ≈-∙ ≈-⊥ (≈Sp-/⟨⟩ bs₁≈bs₂ σ₁≈σ₂)
    ≈-/⟨⟩ (≈-∙ ≈-⊤ bs₁≈bs₂) σ₁≈σ₂ = ≈-∙ ≈-⊤ (≈Sp-/⟨⟩ bs₁≈bs₂ σ₁≈σ₂)
    ≈-/⟨⟩ (≈-∙ (≈-∀ k₁≋k₂ a₁≈a₂) bs₁≈bs₂) σ₁≈σ₂ =
      ≈-∙ (≈-∀ (≋-/⟨⟩ k₁≋k₂ σ₁≈σ₂) (≈-/⟨⟩ a₁≈a₂ (≈-↑ σ₁≈σ₂)))
          (≈Sp-/⟨⟩ bs₁≈bs₂ σ₁≈σ₂)
    ≈-/⟨⟩ (≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) cs₁≈cs₂) σ₁≈σ₂ =
      ≈-∙ (≈-→ (≈-/⟨⟩ a₁≈a₂ σ₁≈σ₂) (≈-/⟨⟩ b₁≈b₂ σ₁≈σ₂))
          (≈Sp-/⟨⟩ cs₁≈cs₂ σ₁≈σ₂)
    ≈-/⟨⟩ (≈-∙ (≈-Λ {k₁} {k₂} ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) bs₁≈bs₂) σ₁≈σ₂ =
      ≈-∙ (≈-Λ (begin
                 ⌊ k₁ Kind/⟨ _ ⟩ _ ⌋   ≡⟨ ⌊⌋-Kind/⟨⟩ k₁ ⟩
                 ⌊ k₁ ⌋                ≡⟨ ⌊k₁⌋≡⌊k₂⌋ ⟩
                 ⌊ k₂ ⌋                ≡⟨ sym (⌊⌋-Kind/⟨⟩ k₂) ⟩
                 ⌊ k₂ Kind/⟨ _ ⟩ _ ⌋   ∎)
               (≈-/⟨⟩ a₁≈a₂ (≈-↑ σ₁≈σ₂)))
          (≈Sp-/⟨⟩ bs₁≈bs₂ σ₁≈σ₂)
      where open ≡-Reasoning
    ≈-/⟨⟩ (≈-∙ (≈-λ a₁≈a₂) bs₁≈bs₂) σ₁≈σ₂ =
      ≈-∙ (≈-λ (≈-/⟨⟩ a₁≈a₂ (≈-↑ σ₁≈σ₂))) (≈Sp-/⟨⟩ bs₁≈bs₂ σ₁≈σ₂)
    ≈-/⟨⟩ (≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) cs₁≈cs₂) σ₁≈σ₂ =
      ≈-∙ (≈-⊡ (≈-/⟨⟩ a₁≈a₂ σ₁≈σ₂) (≈-/⟨⟩ b₁≈b₂ σ₁≈σ₂))
          (≈Sp-/⟨⟩ cs₁≈cs₂ σ₁≈σ₂)

    ≈Sp-/⟨⟩ : ∀ {k m n as₁ as₂} {σ₁ σ₂ : SVSub m n} →
              as₁ ≈Sp as₂ → σ₁ ⟨≈⟩ σ₂ → as₁ //⟨ k ⟩ σ₁ ≈Sp as₂ //⟨ k ⟩ σ₂
    ≈Sp-/⟨⟩ ≈-[]                σ₁≈σ₂ = ≈-[]
    ≈Sp-/⟨⟩ (≈-∷ a₁≈a₂ as₁≈as₂) σ₁≈σ₂ =
      ≈-∷ (≈-/⟨⟩ a₁≈a₂ σ₁≈σ₂) (≈Sp-/⟨⟩ as₁≈as₂ σ₁≈σ₂)

    -- Weak equality is a congruence w.r.t reducing applications.

    ≈-?∙∙⟨⟩ : ∀ k {n} {r₁ r₂ : SVRes n} {as₁ as₂} →
              r₁ ≈? r₂ → as₁ ≈Sp as₂ → r₁ ?∙∙⟨ k ⟩ as₁ ≈ r₂ ?∙∙⟨ k ⟩ as₂
    ≈-?∙∙⟨⟩ k (≈-hit a₁≈a₂) as₁≈as₂ = ≈-∙∙⟨⟩ k a₁≈a₂ as₁≈as₂
    ≈-?∙∙⟨⟩ k (≈-miss x)    as₁≈as₂ = ≈-∙ (≈-var x) as₁≈as₂

    ≈-∙∙⟨⟩ : ∀ k {n} {a₁ a₂ : Elim n} {bs₁ bs₂} →
             a₁ ≈ a₂ → bs₁ ≈Sp bs₂ → a₁ ∙∙⟨ k ⟩ bs₁ ≈ a₂ ∙∙⟨ k ⟩ bs₂
    ≈-∙∙⟨⟩ k         a₁≈a₂ ≈-[]                = a₁≈a₂
    ≈-∙∙⟨⟩ ★         a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂) = ≈-∙∙ a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂)
    ≈-∙∙⟨⟩ (k₁ ⇒ k₂) a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂) =
      ≈-∙∙⟨⟩ k₂ (≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) a₁≈a₂ b₁≈b₂) bs₁≈bs₂

    ≈-⌜·⌝⟨⟩ : ∀ k {n} {a₁ a₂ : Elim n} {b₁ b₂} →
              a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ ⌜·⌝⟨ k ⟩ b₁ ≈ a₂ ⌜·⌝⟨ k ⟩ b₂
    ≈-⌜·⌝⟨⟩ ★         a₁≈a₂                            b₁≈b₂ = ≈-⌜·⌝ a₁≈a₂ b₁≈b₂
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂))  c₁≈c₂ =
      ≈-⌜·⌝ (≈-∙ a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂)) c₁≈c₂
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) ≈-[]) c₁≈c₂ =
      ≈-/⟨⟩ a₁≈a₂ (≈-sub c₁≈c₂)
    -- Degenerate cases.
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ ≈-⊥ ≈-[]) c₁≈c₂ = ≈-∙ ≈-⊥ (≈-∷ c₁≈c₂ ≈-[])
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ ≈-⊤ ≈-[]) c₁≈c₂ = ≈-∙ ≈-⊤ (≈-∷ c₁≈c₂ ≈-[])
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ (≈-var x) ≈-[])         c₁≈c₂ =
      ≈-∙ (≈-var x) (≈-∷ c₁≈c₂ ≈-[])
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ (≈-∀ j₁≋j₂ a₁≈a₂) ≈-[]) c₁≈c₂ =
      ≈-∙ (≈-∀ j₁≋j₂ a₁≈a₂) (≈-∷ c₁≈c₂ ≈-[])
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) ≈-[]) c₁≈c₂ =
      ≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) (≈-∷ c₁≈c₂ ≈-[])
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ (≈-λ a₁≈a₂) ≈-[])       c₁≈c₂ =
      ≈-∙ (≈-λ a₁≈a₂) (≈-∷ c₁≈c₂ ≈-[])
    ≈-⌜·⌝⟨⟩ (k₁ ⇒ k₂) (≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) ≈-[]) c₁≈c₂ =
      ≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) (≈-∷ c₁≈c₂ ≈-[])

  -- A corollary.
  ≈-[∈] : ∀ {k n a₁ a₂} {b₁ b₂ : Elim n} →
          a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ [ b₁ ∈ k ] ≈ a₂ [ b₂ ∈ k ]
  ≈-[∈] a₁≈a₂ b₁≈b₂ = ≈-/⟨⟩ a₁≈a₂ (≈-sub b₁≈b₂)

  -- Weak equality is a congruence w.r.t potentially reducing
  -- applications.
  ≈-↓⌜·⌝ : ∀ {n} {a₁ a₂ : Elim n} {b₁ b₂} → a₁ ≈ a₂ → b₁ ≈ b₂ →
                  a₁ ↓⌜·⌝ b₁ ≈ a₂ ↓⌜·⌝ b₂
  ≈-↓⌜·⌝ (≈-∙ a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂))  c₁≈c₂ =
    ≈-⌜·⌝ (≈-∙ a₁≈a₂ (≈-∷ b₁≈b₂ bs₁≈bs₂)) c₁≈c₂
  ≈-↓⌜·⌝ {_} {_} {_} {b₁} {b₂}
         (≈-∙ (≈-Λ {k₁} {k₂} {a₁} {a₂} ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) ≈-[]) c₁≈c₂ =
    begin
      a₁ [ b₁ ∈ ⌊ k₁ ⌋ ]   ≈⟨ ≈-/⟨⟩ a₁≈a₂ (≈-sub c₁≈c₂) ⟩
      a₂ [ b₂ ∈ ⌊ k₁ ⌋ ]   ≡⟨ cong (a₂ [ b₂ ∈_]) ⌊k₁⌋≡⌊k₂⌋ ⟩
      a₂ [ b₂ ∈ ⌊ k₂ ⌋ ]   ∎
    where open ≈-Reasoning
  -- Degenerate cases.
  ≈-↓⌜·⌝ (≈-∙ ≈-⊥ ≈-[]) c₁≈c₂ = ≈-∙ ≈-⊥ (≈-∷ c₁≈c₂ ≈-[])
  ≈-↓⌜·⌝ (≈-∙ ≈-⊤ ≈-[]) c₁≈c₂ = ≈-∙ ≈-⊤ (≈-∷ c₁≈c₂ ≈-[])
  ≈-↓⌜·⌝ (≈-∙ (≈-var x) ≈-[])         c₁≈c₂ =
    ≈-∙ (≈-var x) (≈-∷ c₁≈c₂ ≈-[])
  ≈-↓⌜·⌝ (≈-∙ (≈-∀ j₁≋j₂ a₁≈a₂) ≈-[]) c₁≈c₂ =
    ≈-∙ (≈-∀ j₁≋j₂ a₁≈a₂) (≈-∷ c₁≈c₂ ≈-[])
  ≈-↓⌜·⌝ (≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) ≈-[]) c₁≈c₂ =
    ≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) (≈-∷ c₁≈c₂ ≈-[])
  ≈-↓⌜·⌝ (≈-∙ (≈-λ a₁≈a₂) ≈-[])       c₁≈c₂ =
    ≈-∙ (≈-λ a₁≈a₂) (≈-∷ c₁≈c₂ ≈-[])
  ≈-↓⌜·⌝ (≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) ≈-[]) c₁≈c₂ =
    ≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) (≈-∷ c₁≈c₂ ≈-[])

open WeakHereditarySubstitutionEquality

module WeakEqEtaExpansion where
  private module TK = TrackSimpleKindsEtaExp
  open Substitution
  open SimpHSubstLemmas
  open ≈-Reasoning

  -- NOTE. The definition of the function ≈-η-exp′ in this module is
  -- structurally recursive in the *simple* kind parameter k, but
  -- *not* in the kinds (j₁ j₂ : Kind Elim n) because we need to
  -- weaken the domains j₁₁ and j₂₁ of the dependent kinds (j₁ = Π j₁₁
  -- j₁₂) and (j₂ = Π j₂₁ j₂₂) in the arrow case.  The additional
  -- premises ⌊ j₁ ⌋≡ k and ⌊ j₂ ⌋≡ k ensure that k is indeed the
  -- simplification of the kinds j₁ and j₂.

  -- Weak equality is a congruence w.r.t. untyped η-expansion.
  --
  -- NOTE. We do *not* require the kinds j₁ and j₂ to be weakly equal,
  -- instead, we only require them to simplify equally, i.e. ⌊ j₁ ⌋ ≡
  -- k ≡ ⌊ j₂ ⌋ (which is an even weaker requirement).

  ≈-η-exp′ : ∀ {n k j₁ j₂} {a₁ a₂ : Elim n}
             (hyp₁ : ⌊ j₁ ⌋≡ k) (hyp₂ : ⌊ j₂ ⌋≡ k) → a₁ ≈ a₂ →
             TK.η-exp j₁ hyp₁ a₁ ≈ TK.η-exp j₂ hyp₂ a₂
  ≈-η-exp′ (is-★) (is-★) c₁≈c₂ = c₁≈c₂
  ≈-η-exp′ (is-⇒ ⌊j₁⌋≡l₁ ⌊k₁⌋≡l₂) (is-⇒ ⌊j₂⌋≡l₁ ⌊k₂⌋≡l₂)
           (≈-∙ (≈-var x) as₁≈as₂) =
    ≈-Λ∙ ⌊j₁⌋≡⌊j₂⌋ (≈-η-exp′ ⌊k₁⌋≡l₂ ⌊k₂⌋≡l₂ x∙as₁≈x∙as₂′)
    where
      ⌊j₁⌋≡⌊j₂⌋    = trans (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡l₁) (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₂⌋≡l₁))
      x∙as₁≈x∙as₂′ =
        ≈-⌜·⌝ (≈-weakenElim (≈-∙ (≈-var x) as₁≈as₂))
              (≈-η-exp′ (⌊⌋≡-weaken ⌊j₁⌋≡l₁) (⌊⌋≡-weaken ⌊j₂⌋≡l₁) (≈-var∙ zero))
  -- Degenerate cases: either ill-kinded or not neutral.
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ ≈-⊥ bs₁≈bs₂) = ≈-∙ ≈-⊥ bs₁≈bs₂
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ ≈-⊤ bs₁≈bs₂) = ≈-∙ ≈-⊤ bs₁≈bs₂
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ (≈-∀ k₁≋k₂ a₁≈a₂) bs₁≈bs₂) =
    ≈-∙ (≈-∀ k₁≋k₂ a₁≈a₂) bs₁≈bs₂
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) cs₁≈cs₂) =
    ≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) cs₁≈cs₂
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) bs₁≈bs₂) =
    ≈-∙ (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) bs₁≈bs₂
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ (≈-λ a₁≈a₂) bs₁≈bs₂) =
    ≈-∙ (≈-λ a₁≈a₂) bs₁≈bs₂
  ≈-η-exp′ (is-⇒ _ _) (is-⇒ _ _) (≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) cs₁≈cs₂) =
    ≈-∙ (≈-⊡ a₁≈a₂ b₁≈b₂) cs₁≈cs₂

  ≈-η-exp : ∀ {n} {j₁ j₂ : Kind Elim n} {a₁ a₂} →
            ⌊ j₁ ⌋ ≡ ⌊ j₂ ⌋ → a₁ ≈ a₂ → η-exp j₁ a₁ ≈ η-exp j₂ a₂
  ≈-η-exp {_} {j₁} {j₂} {a₁} {a₂} ⌊j₁⌋≡⌊j₂⌋ a₁≈a₂ = begin
      η-exp j₁ a₁
    ≡⟨ TK.η-exp-⌊⌋≡ (⌊⌋-⌊⌋≡ j₁) (⌊⌋≡-trans ⌊j₁⌋≡⌊j₂⌋ (⌊⌋-⌊⌋≡ j₂))
                    refl ⌊j₁⌋≡⌊j₂⌋ ⟩
      TK.η-exp j₁ _ a₁
    ≈⟨ ≈-η-exp′ (⌊⌋≡-trans ⌊j₁⌋≡⌊j₂⌋ (⌊⌋-⌊⌋≡ j₂)) (⌊⌋-⌊⌋≡ j₂) a₁≈a₂ ⟩
      η-exp j₂ a₂
    ∎

  open SimpleCtx using (kd; ⌊_⌋Asc; kd-inj′)
  open ContextConversions using (⌊_⌋Ctx)

  -- A variant of `nf-var-kd' that is a corollary of the above.

  nf-var-kd-⌊⌋ : ∀ {n} (Γ : Ctx n) {k} x →
                 ⌊ lookup x Γ ⌋Asc ≡ kd ⌊ k ⌋ → nf Γ (var x) ≈ η-exp k (var∙ x)
  nf-var-kd-⌊⌋ Γ x hyp with lookup x Γ
  nf-var-kd-⌊⌋ Γ x hyp | kd j = ≈-η-exp (kd-inj′ hyp) (≈-var∙ x)
  nf-var-kd-⌊⌋ Γ x ()  | tp _


open WeakEqEtaExpansion

module WeakEqNormalization where
  open SimpleCtx using (kd; ⌊_⌋Asc; ⌊⌋-ElimAsc/Var; kd-inj′)
  open ContextConversions

  -- A helper lemma.
  ⌊⌋≡⌊⌋-lookup : ∀ {n} x (Γ₁ Γ₂ : Ctx n) → ⌊ Γ₁ ⌋Ctx ≡ ⌊ Γ₂ ⌋Ctx →
                 ⌊ lookup x Γ₁ ⌋Asc ≡ ⌊ lookup x Γ₂ ⌋Asc
  ⌊⌋≡⌊⌋-lookup x Γ₁ Γ₂ ⌊Γ₁⌋≡⌊Γ₂⌋ = begin
      ⌊ lookup x Γ₁ ⌋Asc
    ≡⟨ sym (L.lookup-map x ⌊_⌋Asc [] Γ₁ (λ a → sym (⌊⌋-ElimAsc/Var a))) ⟩
      SimpleCtx.lookup x ⌊ Γ₁ ⌋Ctx
    ≡⟨ cong (SimpleCtx.lookup x) ⌊Γ₁⌋≡⌊Γ₂⌋ ⟩
      SimpleCtx.lookup x ⌊ Γ₂ ⌋Ctx
    ≡⟨ L.lookup-map x ⌊_⌋Asc [] Γ₂ (λ a → sym (⌊⌋-ElimAsc/Var a)) ⟩
      ⌊ lookup x Γ₂ ⌋Asc
    ∎
    where
      open ≡-Reasoning
      module L = ⌊⌋Ctx-Lemmas

  -- If two contexts simplify equally, then kinds, types and terms
  -- normalize weakly equally in these contexts.

  mutual

    ≈-nf : ∀ {n} {Γ₁ Γ₂ : Ctx n} →
           ⌊ Γ₁ ⌋Ctx ≡ ⌊ Γ₂ ⌋Ctx → ∀ a → nf Γ₁ a ≈ nf Γ₂ a
    ≈-nf {_} {Γ₁} {Γ₂} ⌊Γ₁⌋≡⌊Γ₂⌋ (var x)
      with lookup x Γ₁ | lookup x Γ₂ | ⌊⌋≡⌊⌋-lookup x Γ₁ Γ₂ ⌊Γ₁⌋≡⌊Γ₂⌋
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (var x) | kd k₁ | kd k₂ | ⌊kd-k₁⌋≡⌊kd-k₂⌋ =
      ≈-η-exp (kd-inj′ ⌊kd-k₁⌋≡⌊kd-k₂⌋) (≈-var∙ x)
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (var x) | kd _  | tp _  | ()
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (var x) | tp _  | kd _  | ()
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (var x) | tp a₁ | tp a₂ | refl = ≈-var∙ x
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ ⊥       = ≈-⊥∙
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ ⊤       = ≈-⊤∙
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (Π k a) =
      let k≋k′ = ≋-nfKind ⌊Γ₁⌋≡⌊Γ₂⌋ k
      in ≈-∀∙ k≋k′ (≈-nf (cong₂ _∷_ (cong kd (≋-⌊⌋ k≋k′)) ⌊Γ₁⌋≡⌊Γ₂⌋) a)
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (a ⇒ b) = ≈-⇒∙ (≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ a) (≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ b)
    ≈-nf {_} {Γ₁} ⌊Γ₁⌋≡⌊Γ₂⌋ (Λ k a) =
      let k≋k′ = ≋-nfKind ⌊Γ₁⌋≡⌊Γ₂⌋ k
      in ≈-Λ∙ (≋-⌊⌋ k≋k′) (≈-nf (cong₂ _∷_ (cong kd (≋-⌊⌋ k≋k′)) ⌊Γ₁⌋≡⌊Γ₂⌋) a)
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (ƛ a b) = ≈-λ∙ (≈-refl ⌜ b ⌝)
    ≈-nf {_} {Γ₁} {Γ₂} ⌊Γ₁⌋≡⌊Γ₂⌋ (a · b) =
      ≈-↓⌜·⌝ (≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ a) (≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ b)
    ≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ (a ⊡ b) = ≈-⊡∙ (≈-refl ⌜ a ⌝) (≈-refl ⌜ b ⌝)

    ≋-nfKind : ∀ {n} {Γ₁ Γ₂ : Ctx n} →
               ⌊ Γ₁ ⌋Ctx ≡ ⌊ Γ₂ ⌋Ctx → ∀ k → nfKind Γ₁ k ≋ nfKind Γ₂ k
    ≋-nfKind ⌊Γ₁⌋≡⌊Γ₂⌋ (a ⋯ b) = ≋-⋯ (≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ a) (≈-nf ⌊Γ₁⌋≡⌊Γ₂⌋ b)
    ≋-nfKind ⌊Γ₁⌋≡⌊Γ₂⌋ (Π j k) =
      let j≋j′ = ≋-nfKind ⌊Γ₁⌋≡⌊Γ₂⌋ j
      in ≋-Π j≋j′ (≋-nfKind (cong₂ _∷_ (cong kd (≋-⌊⌋ j≋j′)) ⌊Γ₁⌋≡⌊Γ₂⌋) k)
