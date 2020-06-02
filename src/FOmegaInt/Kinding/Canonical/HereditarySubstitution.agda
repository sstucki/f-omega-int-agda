------------------------------------------------------------------------
-- Canonically kinded hereditary substitutions in Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Canonical.HereditarySubstitution where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Product as Prod using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProps
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Kinding.Canonical as CanonicalKinding
open import FOmegaInt.Kinding.Simple    as SimpleKinding

open Syntax
open ElimCtx
open SimpleCtx          using (⌊_⌋Asc; kd; tp)
open ContextConversions using (⌊_⌋Ctx)
open Substitution       hiding (_↑; sub; subst)
open RenamingCommutes
open SimpHSubstLemmas
open SimpleKinding.Kinding using (_⊢_kds; kds-Π)
open CanonicalKinding.Kinding
open KindedHereditarySubstitution
  using (_⊢/⟨_⟩_∈_; ∈-hsub; ∈-H↑; kds-/⟨⟩; kds-[]-/⟨⟩-↑⋆)
open CanonicalKinding.KindedRenaming
  using (typedVarSubst; kd-/Var; ≃-/Var; <∷-/Var; kd-weaken; <∷-weaken)
module TV = TypedVarSubst typedVarSubst
open ContextNarrowing


----------------------------------------------------------------------
-- Ascription order: a wrapper judgment that combines subtyping and
-- subkinding.
--
-- NOTE. Subtyping instances are always trivial, i.e. they only
-- support (syntactic) reflexivity.

infix 4 _⊢_≤_

data _⊢_≤_ {n} (Γ : Ctx n) : ElimAsc n → ElimAsc n → Set where
  ≤-<∷   : ∀ {j k} → Γ ⊢ j <∷ k → Γ ⊢ k kd → Γ ⊢ kd j ≤ kd k
  ≤-refl : ∀ {a} → Γ ⊢ a ≤ a

-- Transitivity of the ascription order.

≤-trans : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a ≤ b → Γ ⊢ b ≤ c → Γ ⊢ a ≤ c
≤-trans (≤-<∷ j<∷k _)    (≤-<∷ k<∷l l-kd) = ≤-<∷ (<∷-trans j<∷k k<∷l) l-kd
≤-trans (≤-<∷ j<∷k k-kd) ≤-refl           = ≤-<∷ j<∷k k-kd
≤-trans ≤-refl           a≤c              = a≤c

-- Kinds in related ascriptions simplify equally.

≤-⌊⌋ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ kd j ≤ kd k → ⌊ j ⌋ ≡ ⌊ k ⌋
≤-⌊⌋ (≤-<∷ j<∷k _) = <∷-⌊⌋ j<∷k
≤-⌊⌋ ≤-refl        = refl

-- Renamings preserve the ascription order.

≤-/Var : ∀ {m n Γ Δ a b} {ρ : Sub Fin m n} →
         Γ ⊢ a ≤ b → Δ TV.⊢/Var ρ ∈ Γ → Δ ⊢ a ElimAsc/Var ρ ≤ b ElimAsc/Var ρ
≤-/Var (≤-<∷ j<∷k k-kd) ρ∈Γ = ≤-<∷ (<∷-/Var j<∷k ρ∈Γ) (kd-/Var k-kd ρ∈Γ)
≤-/Var ≤-refl           ρ∈Γ = ≤-refl

-- Admissible subsumption rules w.r.t. the ascription order.

Nf⇇-⇑-≤ : ∀ {n} {Γ : Ctx n} {a k j} →
          Γ ⊢Nf a ⇇ k → Γ ⊢ kd k ≤ kd j → Γ ⊢Nf a ⇇ j
Nf⇇-⇑-≤ a⇇k (≤-<∷ k<∷j j-kd) = Nf⇇-⇑ a⇇k k<∷j
Nf⇇-⇑-≤ a⇇k ≤-refl           = a⇇k

≃-⇑-≤ : ∀ {n} {Γ : Ctx n} {a b k j} →
        Γ ⊢ a ≃ b ⇇ k → Γ ⊢ kd k ≤ kd j → Γ ⊢ a ≃ b ⇇ j
≃-⇑-≤ a≃b⇇k (≤-<∷ k<∷j j-kd) = ≃-⇑ a≃b⇇k k<∷j j-kd
≃-⇑-≤ a≃b⇇k ≤-refl           = a≃b⇇k

-- An admissible variable rule based on the ascription order.

Var∈-⇑-≤  : ∀ {n} {Γ : Ctx n} {a k} x →
            Γ ctx → lookup x Γ ≡ a → Γ ⊢ a ≤ kd k → Γ ⊢Var x ∈ k
Var∈-⇑-≤ x Γ-ctx Γ[x]≡j (≤-<∷ j<∷k k-kd) = ⇇-⇑ (⇉-var x Γ-ctx Γ[x]≡j) j<∷k k-kd
Var∈-⇑-≤ x Γ-ctx Γ[x]≡k ≤-refl           = ⇉-var x Γ-ctx Γ[x]≡k


----------------------------------------------------------------------
-- Well-kinded hereditary substitutions (i.e. substitution lemmas) in
-- canonical types

infix 4 _⊢/⟨_⟩_⇇_ _⊢/⟨_⟩_≃_⇇_ _⊢?⟨_⟩_⇇_ _⊢?⟨_⟩_≃_⇇_

-- Well-kinded pointwise equality of hereditary substitutions and
-- their lookup results.

data _⊢/⟨_⟩_≃_⇇_ : ∀ {m n} →
                   Ctx n → SKind → SVSub m n → SVSub m n → Ctx m → Set where
  ≃-hsub : ∀ {n} {Γ : Ctx n} {k a b j} →
           Γ ⊢ a ≃ b ⇇ j → ⌊ j ⌋≡ k →
           Γ ⊢/⟨ k ⟩ sub a ≃ sub b ⇇ kd j ∷ Γ
  ≃-H↑   : ∀ {m n Δ k Γ} {σ τ : SVSub m n} {j l} →
           Δ ⊢ j ≅ l Kind/⟨ k ⟩ σ → Δ ⊢ j ≅ l Kind/⟨ k ⟩ τ →
           Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ → kd j ∷ Δ ⊢/⟨ k ⟩ σ ↑ ≃ τ ↑ ⇇ kd l ∷ Γ

data _⊢?⟨_⟩_≃_⇇_ {n} (Γ : Ctx n) (k : SKind)
                 : SVRes n → SVRes n → ElimAsc n → Set where
  ≃-hit  : ∀ {a b j} →
           Γ ⊢ a ≃ b ⇇ j → ⌊ j ⌋≡ k → Γ ⊢?⟨ k ⟩ hit a ≃ hit b ⇇ kd j
  ≃-miss : ∀ y {a b} → Γ ctx → lookup y Γ ≡ a → Γ ⊢ a ≤ b →
           Γ ⊢?⟨ k ⟩ miss y ≃ miss y ⇇ b

-- Well-kinded suspended hereditary substations are just a degenerate
-- case of equal hereditary substitutions where the underlying
-- substitutions coincide (syntactically).

_⊢/⟨_⟩_⇇_ : ∀ {m n} → Ctx n → SKind → SVSub m n → Ctx m → Set
Δ ⊢/⟨ k ⟩ σ ⇇ Γ = Δ ⊢/⟨ k ⟩ σ ≃ σ ⇇ Γ

⇇-hsub : ∀ {n} {Γ : Ctx n} {k a j} →
         Γ ⊢Nf a ⇇ j → Γ ⊢ j kd → ⌊ j ⌋≡ k →
         Γ ⊢/⟨ k ⟩ sub a ⇇ kd j ∷ Γ
⇇-hsub a⇇j j-kd ⌊j⌋≡k = ≃-hsub (≃-reflNf⇇ a⇇j j-kd) ⌊j⌋≡k

⇇-H↑ : ∀ {m n Δ k Γ} {σ : SVSub m n} {j l} →
       Δ ⊢ j ≅ l Kind/⟨ k ⟩ σ → Δ ⊢/⟨ k ⟩ σ ⇇ Γ →
       kd j ∷ Δ ⊢/⟨ k ⟩ σ ↑ ⇇ kd l ∷ Γ
⇇-H↑ j≅l/σ σ⇇Γ = ≃-H↑ j≅l/σ j≅l/σ σ⇇Γ

_⊢?⟨_⟩_⇇_ : ∀ {n} → Ctx n → SKind → SVRes n → ElimAsc n → Set
Δ ⊢?⟨ k ⟩ σ ⇇ Γ = Δ ⊢?⟨ k ⟩ σ ≃ σ ⇇ Γ

⇇-hit  : ∀ {n} {Γ : Ctx n} {k a j} →
         Γ ⊢Nf a ⇇ j → Γ ⊢ j kd → ⌊ j ⌋≡ k → Γ ⊢?⟨ k ⟩ hit a ⇇ kd j
⇇-hit a⇇j j-kd ⌊j⌋≡k = ≃-hit (≃-reflNf⇇ a⇇j j-kd) ⌊j⌋≡k

⇇-miss = λ {n} {Γ} {k} → ≃-miss {n} {Γ} {k}

-- Renamings preserve equality of SV results.

?≃-/Var : ∀ {m n Γ k Δ r₁ r₂ a} {ρ : Sub Fin m n} →
          Γ ⊢?⟨ k ⟩ r₁ ≃ r₂ ⇇ a → Δ TV.⊢/Var ρ ∈ Γ →
          Δ ⊢?⟨ k ⟩ r₁ ?/Var ρ ≃ r₂ ?/Var ρ ⇇ a ElimAsc/Var ρ
?≃-/Var (≃-hit a≃b∈k ⌊j⌋≡k) ρ∈Γ =
  ≃-hit (≃-/Var a≃b∈k ρ∈Γ) (⌊⌋≡-/Var ⌊j⌋≡k)
?≃-/Var {Γ = Γ} {k} {Δ} {ρ = ρ} (≃-miss y {a} {b} _ Γ[x]≡a a≤b) ρ∈Γ =
  helper (cong (_ElimAsc/Var ρ) Γ[x]≡a) (TS.lookup y ρ∈Γ)
  where
    module TS = TypedSub TV.typedSub

    helper : ∀ {x c} → c ≡ a ElimAsc/Var ρ → Δ TV.⊢Var x ∈ c →
             Δ ⊢?⟨ k ⟩ miss x ≃ miss x ⇇ b ElimAsc/Var ρ
    helper Δ[x]≡a/ρ (TV.var x Δ-ctx) =
      ≃-miss x (TS./∈-wf ρ∈Γ) Δ[x]≡a/ρ (≤-/Var a≤b ρ∈Γ)

?≃-weaken : ∀ {n} {Γ : Ctx n} {k r₁ r₂ a b} →
            Γ ⊢ a wf → Γ ⊢?⟨ k ⟩ r₁ ≃ r₂ ⇇ b →
            (a ∷ Γ) ⊢?⟨ k ⟩ weakenSVRes r₁ ≃ weakenSVRes r₂ ⇇ weakenElimAsc b
?≃-weaken a-wf r₁≃r₂⇇a = ?≃-/Var r₁≃r₂⇇a (TV.∈-wk a-wf)

-- Look up a variable in a pair of well-kinded pointwise equal
-- hereditary substitution.

lookup-/⟨⟩≃ : ∀ {m n Δ k Γ} {σ τ : SVSub m n} →
              Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ → (x : Fin m) →
              Δ ⊢?⟨ k ⟩ lookupSV σ x ≃ lookupSV τ x ⇇ lookup x Γ Asc/⟨ k ⟩ σ
lookup-/⟨⟩≃ (≃-hsub {_} {Γ} {k} {a} {b} {j} a≃b⇇k ⌊j⌋≡k) zero =
  subst (Γ ⊢?⟨ k ⟩ hit a ≃ hit b ⇇_)
        (cong kd (sym (Kind/Var-wk-↑⋆-hsub-vanishes 0 j))) (≃-hit a≃b⇇k ⌊j⌋≡k)
lookup-/⟨⟩≃ (≃-hsub {Γ = Γ} {k} {a} {_} {j} a≃b⇇k ⌊j⌋≡k) (suc x) =
  subst (Γ ⊢?⟨ k ⟩ miss x ≃ miss x ⇇_) (begin
      lookup x Γ
    ≡˘⟨ Asc/Var-wk-↑⋆-hsub-vanishes 0 (lookup x Γ) ⟩
      weakenElimAsc (lookup x Γ) Asc/⟨ k ⟩ sub a
    ≡˘⟨ cong (_Asc/⟨ k ⟩ sub a) (VecProps.lookup-map x weakenElimAsc (toVec Γ)) ⟩
       lookup (suc x) (kd j ∷ Γ) Asc/⟨ k ⟩ sub a
    ∎) (≃-miss x (≃-ctx a≃b⇇k) refl ≤-refl)
lookup-/⟨⟩≃ (≃-H↑ {Δ = Δ} {k} {j = j} {l} j≅l/σ j≅l/τ σ≃τ⇇Γ) zero =
  let j-kd , l/σ-kd = ≅-valid j≅l/σ
      j-wf  = wf-kd j-kd
      j≤l/σ = ≤-<∷ (<∷-weaken j-wf (≅⇒<∷ j≅l/σ)) (kd-weaken j-wf l/σ-kd)
  in subst (kd j ∷ Δ ⊢?⟨ k ⟩ miss zero ≃ miss zero ⇇_)
           (sym (wk-Asc/⟨⟩-↑⋆ 0 (kd l)))
           (≃-miss zero (j-wf ∷ (kd-ctx j-kd)) refl j≤l/σ)
lookup-/⟨⟩≃ (≃-H↑ {k = k} {Γ} {σ} {_} {_} {l} j≅l/σ _ σ≃τ⇇Γ) (suc x) =
  subst (_ ⊢?⟨ k ⟩ _ ≃ _ ⇇_) (begin
      weakenElimAsc (lookup x Γ Asc/⟨ k ⟩ σ)
    ≡˘⟨ wk-Asc/⟨⟩-↑⋆ 0 (lookup x Γ) ⟩
      weakenElimAsc (lookup x Γ) Asc/⟨ k ⟩ σ ↑
    ≡˘⟨ cong (_Asc/⟨ k ⟩ σ ↑)
             (VecProps.lookup-map x weakenElimAsc (toVec Γ)) ⟩
      lookup (suc x) (kd l ∷ Γ) Asc/⟨ k ⟩ σ ↑
    ∎) (?≃-weaken (wf-kd (proj₁ (≅-valid j≅l/σ))) (lookup-/⟨⟩≃ σ≃τ⇇Γ x))

-- Equation and context validity lemmas for hereditary substitutions.

/⟨⟩≃-valid₁ : ∀ {k m n Δ Γ} {σ τ : SVSub m n} →
              Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ → Δ ⊢/⟨ k ⟩ σ ⇇ Γ
/⟨⟩≃-valid₁ (≃-hsub a≃b⇇j ⌊j⌋≡k) =
  ⇇-hsub (proj₁ (≃-valid a≃b⇇j)) (≃-valid-kd a≃b⇇j) ⌊j⌋≡k
/⟨⟩≃-valid₁ (≃-H↑ a≅b/σ _ σ≃τ∈Γ) = ⇇-H↑ a≅b/σ (/⟨⟩≃-valid₁ σ≃τ∈Γ)

/⟨⟩≃-valid₂ : ∀ {k m n Δ Γ} {σ τ : SVSub m n} →
              Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ → Δ ⊢/⟨ k ⟩ τ ⇇ Γ
/⟨⟩≃-valid₂ (≃-hsub a≃b⇇j ⌊j⌋≡k) =
  ⇇-hsub (proj₂ (≃-valid a≃b⇇j)) (≃-valid-kd a≃b⇇j) ⌊j⌋≡k
/⟨⟩≃-valid₂ (≃-H↑ _ a≅b/τ σ≃τ∈Γ) = ⇇-H↑ a≅b/τ (/⟨⟩≃-valid₂ σ≃τ∈Γ)

/⟨⟩≃-ctx : ∀ {k m n Γ Δ} {σ τ : SVSub m n} →
           Γ ctx → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ → Δ ctx
/⟨⟩≃-ctx j∷Γ-ctx (≃-hsub a≃b⇇j ⌊j⌋≡k)     = wf-∷₂ j∷Γ-ctx
/⟨⟩≃-ctx l∷Γ-ctx (≃-H↑ j≅l/σ j≅l/τ σ≃τ⇇Γ) =
  let j-kd , _ = ≅-valid j≅l/σ
      Γ-ctx    = wf-∷₂ l∷Γ-ctx
  in (wf-kd j-kd) ∷ /⟨⟩≃-ctx Γ-ctx σ≃τ⇇Γ

-- Symmetry of hereditary substitution equality.

/⟨⟩≃-sym : ∀ {k m n Δ Γ} {σ τ : SVSub m n} →
           Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ → Δ ⊢/⟨ k ⟩ τ ≃ σ ⇇ Γ
/⟨⟩≃-sym (≃-hsub a≃b⇇j ⌊j⌋≡k)     = ≃-hsub (≃-sym a≃b⇇j) ⌊j⌋≡k
/⟨⟩≃-sym (≃-H↑ a≅b/σ a≅b/τ σ≃τ∈Γ) = ≃-H↑ a≅b/τ a≅b/σ (/⟨⟩≃-sym σ≃τ∈Γ)

-- Simplification of kinded substitutions.

/⟨⟩⇇-/⟨⟩∈ : ∀ {k m n Δ Γ} {σ : SVSub m n} →
            Δ ⊢/⟨ k ⟩ σ ⇇ Γ → ⌊ Δ ⌋Ctx ⊢/⟨ k ⟩ σ ∈ ⌊ Γ ⌋Ctx
/⟨⟩⇇-/⟨⟩∈ (≃-hsub a≃a⇇j ⌊j⌋≡k) =
  subst (_ ⊢/⟨_⟩ _ ∈ _) (⌊⌋≡⇒⌊⌋-≡ ⌊j⌋≡k)
        (∈-hsub (Nf⇇-Nf∈ (proj₁ (≃-valid a≃a⇇j))))
/⟨⟩⇇-/⟨⟩∈ (≃-H↑ {Δ = Δ} {k} {Γ} {σ} {_} {j} {l} j≅l/σ _ σ≃σ∈Γ) =
  subst ((_⊢/⟨ k ⟩ σ ↑ ∈ ⌊ kd l ∷ Γ ⌋Ctx) ∘ (_∷ ⌊ Δ ⌋Ctx)) (begin
          ⌊ kd l ⌋Asc              ≡˘⟨ ⌊⌋-Asc/⟨⟩ (kd l) ⟩
          ⌊ kd l Asc/⟨ k ⟩ σ ⌋Asc  ≡˘⟨ cong kd (≅-⌊⌋ j≅l/σ) ⟩
          ⌊ kd j ⌋Asc              ∎)
        (∈-H↑ (/⟨⟩⇇-/⟨⟩∈ σ≃σ∈Γ))

-- TODO: explain why we need to track simple kinds explicitly.
module TrackSimpleKindsSubst where

  -- TODO: explain how/why preservation of (sub)kinding/subtyping
  -- under reducing applications, hereditary substitution and equal
  -- hereditary substitutions circularly depend on each other.

  mutual

    -- Hereditary substitutions preserve well-formedness of kinds.

    kd-/⟨⟩ : ∀ {k m n Γ Δ} {σ : SVSub m n} {j} →
             Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ⇇ Γ → Δ ⊢ j Kind/⟨ k ⟩ σ kd
    kd-/⟨⟩ (kd-⋯ a⇉a⋯a b⇉b⋯b) σ⇇Γ =
      kd-⋯ (Nf⇉-/⟨⟩ a⇉a⋯a σ⇇Γ) (Nf⇉-/⟨⟩ b⇉b⋯b σ⇇Γ)
    kd-/⟨⟩ (kd-Π j-kd k-kd)   σ⇇Γ =
      let j/σ-kd = kd-/⟨⟩ j-kd σ⇇Γ
      in kd-Π j/σ-kd (kd-/⟨⟩ k-kd (⇇-H↑ (≅-refl j/σ-kd) σ⇇Γ))

    -- Hereditary substitutions preserve synthesized kinds of normal
    -- types.

    Nf⇉-/⟨⟩ : ∀ {k m n Γ Δ} {σ : SVSub m n} {a j} →
              Γ ⊢Nf a ⇉ j → Δ ⊢/⟨ k ⟩ σ ⇇ Γ → Δ ⊢Nf a /⟨ k ⟩ σ ⇉ j Kind/⟨ k ⟩ σ
    Nf⇉-/⟨⟩ (⇉-⊥-f Γ-ctx) σ⇇Γ = ⇉-⊥-f (/⟨⟩≃-ctx Γ-ctx σ⇇Γ)
    Nf⇉-/⟨⟩ (⇉-⊤-f Γ-ctx) σ⇇Γ = ⇉-⊤-f (/⟨⟩≃-ctx Γ-ctx σ⇇Γ)
    Nf⇉-/⟨⟩ (⇉-∀-f k-kd a⇉a⋯a)  σ⇇Γ =
      let k/σ-kd = kd-/⟨⟩ k-kd σ⇇Γ
      in ⇉-∀-f k/σ-kd (Nf⇉-/⟨⟩ a⇉a⋯a (⇇-H↑ (≅-refl k/σ-kd) σ⇇Γ))
    Nf⇉-/⟨⟩ (⇉-→-f a⇉a⋯a b⇉b⋯b) σ⇇Γ =
      ⇉-→-f (Nf⇉-/⟨⟩ a⇉a⋯a σ⇇Γ) (Nf⇉-/⟨⟩ b⇉b⋯b σ⇇Γ)
    Nf⇉-/⟨⟩ (⇉-Π-i k-kd a⇉a⋯a)  σ⇇Γ =
      let k/σ-kd = kd-/⟨⟩ k-kd σ⇇Γ
      in ⇉-Π-i k/σ-kd (Nf⇉-/⟨⟩ a⇉a⋯a (⇇-H↑ (≅-refl k/σ-kd) σ⇇Γ))
    Nf⇉-/⟨⟩ (⇉-s-i a∈b⋯c) σ⇇Γ = Nf⇇-s-i (Ne∈-/⟨⟩ a∈b⋯c σ⇇Γ)

    -- Neutral proper types kind-check against their synthesized kinds
    -- after substitution.

    Ne∈-/⟨⟩ : ∀ {k m n Γ Δ} {σ : SVSub m n} {a b c} →
              Γ ⊢Ne a ∈ b ⋯ c → Δ ⊢/⟨ k ⟩ σ ⇇ Γ →
              Δ ⊢Nf a /⟨ k ⟩ σ ⇇ b /⟨ k ⟩ σ ⋯ c /⟨ k ⟩ σ
    Ne∈-/⟨⟩ (∈-∙ {x} x∈j j⇉as⇉b⋯c) σ⇇Γ =
      let j-kds = kd-kds (Var∈-valid x∈j)
      in Var∈-/⟨⟩-⇑-?∙∙ x∈j σ⇇Γ ≤-refl (Sp⇉-/⟨⟩ j-kds j⇉as⇉b⋯c σ⇇Γ)

    Var∈-/⟨⟩-⇑-?∙∙ : ∀ {k m n Γ Δ} {σ : SVSub m n} {x j l as b c} →
                     Γ ⊢Var x ∈ j → Δ ⊢/⟨ k ⟩ σ ⇇ Γ →
                     Δ ⊢ kd j Asc/⟨ k ⟩ σ ≤ kd l → Δ ⊢ l ⇉∙ as ⇉ b ⋯ c →
                     Δ ⊢Nf lookupSV σ x ?∙∙⟨ k ⟩ as ⇇ b ⋯ c
    Var∈-/⟨⟩-⇑-?∙∙ (⇉-var x _ Γ[x]≡kd-j) σ⇇Γ j/σ≤l l⇉as⇉b⋯c =
      ?⇇-⇑-?∙∙ (subst (_ ⊢?⟨ _ ⟩ _ ⇇_) (cong (_Asc/⟨ _ ⟩ _) Γ[x]≡kd-j)
                      (lookup-/⟨⟩≃ σ⇇Γ x))
               j/σ≤l l⇉as⇉b⋯c
    Var∈-/⟨⟩-⇑-?∙∙ (⇇-⇑ x∈j₁ j₁<∷j₂ j₂-kd) σ⇇Γ j₂/σ≤l l⇉as⇉b⋯c =
      let j₁/σ≤j₂/σ = ≤-<∷ (<∷-/⟨⟩≃ j₁<∷j₂ σ⇇Γ) (kd-/⟨⟩ j₂-kd σ⇇Γ)
      in Var∈-/⟨⟩-⇑-?∙∙ x∈j₁ σ⇇Γ (≤-trans j₁/σ≤j₂/σ j₂/σ≤l) l⇉as⇉b⋯c

    -- Hereditary substitutions preserve synthesized kinds of spines.
    Sp⇉-/⟨⟩ : ∀ {k m n Γ Δ} {σ : SVSub m n} {as j₁ j₂} →
              ⌊ Γ ⌋Ctx ⊢ j₁ kds → Γ ⊢ j₁ ⇉∙ as ⇉ j₂ → Δ ⊢/⟨ k ⟩ σ ⇇ Γ →
              Δ ⊢ j₁ Kind/⟨ k ⟩ σ ⇉∙ as //⟨ k ⟩ σ ⇉ j₂ Kind/⟨ k ⟩ σ
    Sp⇉-/⟨⟩ _ ⇉-[] σ⇇Γ = ⇉-[]
    Sp⇉-/⟨⟩ {k} (kds-Π j₁-kds j₂-kds)
            (⇉-∷ {a} {_} {j₁} {j₂} a⇇j₁ j₁-kd j₂[a]⇉as⇉j₃) σ⇇Γ =
      ⇉-∷ (Nf⇇-/⟨⟩ a⇇j₁ σ⇇Γ) (kd-/⟨⟩ j₁-kd σ⇇Γ)
          (subst (_ ⊢_⇉∙ _ ⇉ _) j₂[a]/σ≡j₂/σ[a/σ]
                 (Sp⇉-/⟨⟩ (kds-/⟨⟩ j₂-kds (∈-hsub a∈⌊j₁⌋)) j₂[a]⇉as⇉j₃ σ⇇Γ))
      where
        a∈⌊j₁⌋ = Nf⇇-Nf∈ a⇇j₁

        j₂[a]/σ≡j₂/σ[a/σ] = begin
            j₂ Kind[ a ∈ ⌊ j₁ ⌋ ] Kind/⟨ k ⟩ _
          ≡⟨ kds-[]-/⟨⟩-↑⋆ [] j₂-kds a∈⌊j₁⌋ (/⟨⟩⇇-/⟨⟩∈ σ⇇Γ) ⟩
            j₂ Kind/⟨ k ⟩ _ ↑ Kind/⟨ ⌊ j₁ ⌋ ⟩ sub (a /⟨ k ⟩ _)
          ≡⟨ cong (_ Kind[ a /⟨ k ⟩ _ ∈_]) (sym (⌊⌋-Kind/⟨⟩ j₁)) ⟩
            (j₂ Kind/⟨ k ⟩ _ ↑) Kind[ a /⟨ k ⟩ _ ∈ ⌊ j₁ Kind/⟨ k ⟩ _ ⌋ ]
          ∎

    -- Hereditary substitutions preserve checked kinds of normal
    -- types.
    Nf⇇-/⟨⟩ : ∀ {k m n Γ Δ} {σ : SVSub m n} {a j} →
              Γ ⊢Nf a ⇇ j → Δ ⊢/⟨ k ⟩ σ ⇇ Γ → Δ ⊢Nf a /⟨ k ⟩ σ ⇇ j Kind/⟨ k ⟩ σ
    Nf⇇-/⟨⟩ (⇇-⇑ a⇉j j<∷k) σ⇇Γ = ⇇-⇑ (Nf⇉-/⟨⟩ a⇉j σ⇇Γ) (<∷-/⟨⟩≃ j<∷k σ⇇Γ)

    -- Equal hereditary substitutions well-formed kinds to subkinds.
    kd-/⟨⟩≃-<∷ : ∀ {m n Γ k Δ} {σ τ : SVSub m n} {j} →
                 Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
                 Δ ⊢ j Kind/⟨ k ⟩ σ <∷ j Kind/⟨ k ⟩ τ
    kd-/⟨⟩≃-<∷ (kd-⋯ a⇉a⋯a b⇉b⋯b) σ≃τ⇇Γ =
      <∷-⋯ (Nf⇉-⋯-/⟨⟩≃ a⇉a⋯a (/⟨⟩≃-sym σ≃τ⇇Γ)) (Nf⇉-⋯-/⟨⟩≃ b⇉b⋯b σ≃τ⇇Γ)
    kd-/⟨⟩≃-<∷ (kd-Π j-kd k-kd)   σ≃τ⇇Γ =
      let σ⇇Γ     = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ     = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          τ≃σ⇇Γ   = /⟨⟩≃-sym σ≃τ⇇Γ
          j/σ≅j/σ = kd-/⟨⟩≃-≅ j-kd σ⇇Γ
          j/τ≅j/τ = kd-/⟨⟩≃-≅ j-kd τ⇇Γ
          j/τ≅j/σ = kd-/⟨⟩≃-≅ j-kd τ≃σ⇇Γ
      in <∷-Π (kd-/⟨⟩≃-<∷ j-kd τ≃σ⇇Γ)
              (kd-/⟨⟩≃-<∷ k-kd (≃-H↑ j/τ≅j/σ j/τ≅j/τ σ≃τ⇇Γ))
              (kd-Π (kd-/⟨⟩ j-kd σ⇇Γ) (kd-/⟨⟩ k-kd (⇇-H↑ j/σ≅j/σ σ⇇Γ)))

    -- Equal hereditary substitutions map well-formed kinds to kind
    -- identities.
    kd-/⟨⟩≃-≅ : ∀ {m n Γ k Δ} {σ τ : SVSub m n} {j} →
                Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
                Δ ⊢ j Kind/⟨ k ⟩ σ ≅ j Kind/⟨ k ⟩ τ
    kd-/⟨⟩≃-≅ k-kd σ≃τ⇇Γ =
      <∷-antisym (kd-/⟨⟩ k-kd (/⟨⟩≃-valid₁ σ≃τ⇇Γ))
                 (kd-/⟨⟩ k-kd (/⟨⟩≃-valid₂ σ≃τ⇇Γ))
                 (kd-/⟨⟩≃-<∷ k-kd σ≃τ⇇Γ) (kd-/⟨⟩≃-<∷ k-kd (/⟨⟩≃-sym σ≃τ⇇Γ))

    -- Equal hereditary substitutions map normal forms to subtypes.

    Nf⇉-⋯-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a b c} →
                 Γ ⊢Nf a ⇉ b ⋯ c → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
                 Δ ⊢ a /⟨ k ⟩ σ <: a /⟨ k ⟩ τ
    Nf⇉-⋯-/⟨⟩≃ (⇉-⊥-f Γ-ctx) σ≃τ⇇Γ =
      <:-⊥ (⇉-⊥-f (/⟨⟩≃-ctx Γ-ctx (/⟨⟩≃-valid₁ σ≃τ⇇Γ)))
    Nf⇉-⋯-/⟨⟩≃ (⇉-⊤-f Γ-ctx) σ≃τ⇇Γ =
      <:-⊤ (⇉-⊤-f (/⟨⟩≃-ctx Γ-ctx (/⟨⟩≃-valid₂ σ≃τ⇇Γ)))
    Nf⇉-⋯-/⟨⟩≃ (⇉-∀-f k-kd a⇉a⋯a) σ≃τ⇇Γ =
      let σ⇇Γ       = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ       = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          τ≃σ⇇Γ     = /⟨⟩≃-sym  σ≃τ⇇Γ
          k/τ≅k/τ   = kd-/⟨⟩≃-≅ k-kd τ⇇Γ
          k/σ≅k/σ   = kd-/⟨⟩≃-≅ k-kd σ⇇Γ
          k/τ≅k/σ   = kd-/⟨⟩≃-≅ k-kd τ≃σ⇇Γ
          σ≃τ⇇j/τ∷Γ = ≃-H↑ k/τ≅k/σ k/τ≅k/τ σ≃τ⇇Γ
      in <:-∀ (≅⇒<∷ k/τ≅k/σ) (Nf⇉-⋯-/⟨⟩≃ a⇉a⋯a σ≃τ⇇j/τ∷Γ)
              (⇉-∀-f (kd-/⟨⟩ k-kd σ⇇Γ)
                     (Nf⇉-/⟨⟩ a⇉a⋯a (⇇-H↑ k/σ≅k/σ σ⇇Γ)))
    Nf⇉-⋯-/⟨⟩≃ (⇉-→-f a⇉a⋯a b⇉b⋯b) σ≃τ⇇Γ =
      <:-→ (Nf⇉-⋯-/⟨⟩≃ a⇉a⋯a (/⟨⟩≃-sym σ≃τ⇇Γ)) (Nf⇉-⋯-/⟨⟩≃ b⇉b⋯b σ≃τ⇇Γ)
    Nf⇉-⋯-/⟨⟩≃ (⇉-s-i a∈b⋯c) σ≃τ⇇Γ = Ne∈-/⟨⟩≃ a∈b⋯c σ≃τ⇇Γ

    Nf⇉-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a j} →
               Γ ⊢Nf a ⇉ j → Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
               Δ ⊢ a /⟨ k ⟩ σ <: a /⟨ k ⟩ τ ⇇ j Kind/⟨ k ⟩ σ
    Nf⇉-/⟨⟩≃ a⇉b⋯c (kd-⋯ b⇉b⋯b c⇉c⋯c) σ≃τ⇇Γ =
      let σ⇇Γ   = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ   = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          τ≃σ⇇Γ = /⟨⟩≃-sym σ≃τ⇇Γ
      in <:-⇇ (Nf⇉⇒Nf⇇ (Nf⇉-/⟨⟩ a⇉b⋯c σ⇇Γ))
              (⇇-⇑ (Nf⇉-/⟨⟩ a⇉b⋯c τ⇇Γ)
                   (<∷-⋯ (Nf⇉-⋯-/⟨⟩≃ b⇉b⋯b σ≃τ⇇Γ) (Nf⇉-⋯-/⟨⟩≃ c⇉c⋯c τ≃σ⇇Γ)))
              (Nf⇉-⋯-/⟨⟩≃ a⇉b⋯c σ≃τ⇇Γ)
    Nf⇉-/⟨⟩≃ (⇉-Π-i _ a⇉l) (kd-Π j-kd l-kd) σ≃τ⇇Γ =
      let τ≃σ⇇Γ = /⟨⟩≃-sym σ≃τ⇇Γ
          σ⇇Γ   = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ   = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          j/σ-kd  = kd-/⟨⟩ j-kd σ⇇Γ
          j/τ-kd  = kd-/⟨⟩ j-kd τ⇇Γ
          j/σ≅j/σ = kd-/⟨⟩≃-≅ j-kd σ⇇Γ
          j/τ≅j/τ = kd-/⟨⟩≃-≅ j-kd τ⇇Γ
          j/σ≅j/τ = kd-/⟨⟩≃-≅ j-kd σ≃τ⇇Γ
          a/σ⇉l/σ = Nf⇉-/⟨⟩ a⇉l (⇇-H↑ j/σ≅j/σ σ⇇Γ)
          a/τ⇉l/τ = Nf⇉-/⟨⟩ a⇉l (⇇-H↑ j/τ≅j/τ τ⇇Γ)
          a/σ<:a/τ⇇l/σ = Nf⇉-/⟨⟩≃ a⇉l l-kd (≃-H↑ j/σ≅j/σ j/σ≅j/τ σ≃τ⇇Γ)
          Πjl/τ<∷Πjl/σ = kd-/⟨⟩≃-<∷ (kd-Π j-kd l-kd) τ≃σ⇇Γ
          Λja/σ⇇Πjl/σ = Nf⇉⇒Nf⇇ (⇉-Π-i j/σ-kd a/σ⇉l/σ)
          Λja/τ⇇Πjl/σ = ⇇-⇑ (⇉-Π-i j/τ-kd a/τ⇉l/τ) Πjl/τ<∷Πjl/σ
      in <:-λ a/σ<:a/τ⇇l/σ Λja/σ⇇Πjl/σ Λja/τ⇇Πjl/σ

    -- Equal hereditary substitutions map proper neutrals to subtypes.
    Ne∈-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a b c} →
               Γ ⊢Ne a ∈ b ⋯ c → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
               Δ ⊢ a /⟨ k ⟩ σ <: a /⟨ k ⟩ τ
    Ne∈-/⟨⟩≃ (∈-∙ {x} x∈j j⇉as⇉b⋯c) σ≃τ⇇Γ =
      let j-kds = kd-kds (Var∈-valid x∈j)
      in Var∈-/⟨⟩≃-⇑-?∙∙ x∈j σ≃τ⇇Γ ≤-refl (Sp⇉-/⟨⟩≃ j-kds j⇉as⇉b⋯c σ≃τ⇇Γ)

    Var∈-/⟨⟩≃-⇑-?∙∙ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {x j l as bs b c} →
                      Γ ⊢Var x ∈ j → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
                      Δ ⊢ kd j Asc/⟨ k ⟩ σ ≤ kd l → Δ ⊢ l ⇉∙ as ≃ bs ⇉ b ⋯ c →
                      Δ ⊢ lookupSV σ x ?∙∙⟨ k ⟩ as <: lookupSV τ x ?∙∙⟨ k ⟩ bs
    Var∈-/⟨⟩≃-⇑-?∙∙ (⇉-var x _ Γ[x]≡kd-j) σ≃τ⇇Γ j/σ≤l l⇉as≃bs⇉b⋯c =
      ?≃-⇑-?∙∙ (subst (_ ⊢?⟨ _ ⟩ _ ≃ _ ⇇_) (cong (_Asc/⟨ _ ⟩ _) Γ[x]≡kd-j)
                      (lookup-/⟨⟩≃ σ≃τ⇇Γ x))
               j/σ≤l l⇉as≃bs⇉b⋯c
    Var∈-/⟨⟩≃-⇑-?∙∙ (⇇-⇑ x∈j₁ j₁<∷j₂ j₂-kd) σ≃τ⇇Γ j₂/σ≤l l⇉as≃bs⇉b⋯c =
      let σ⇇Γ       = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          j₁/σ≤j₂/σ = ≤-<∷ (<∷-/⟨⟩≃ j₁<∷j₂ σ⇇Γ) (kd-/⟨⟩ j₂-kd σ⇇Γ)
      in Var∈-/⟨⟩≃-⇑-?∙∙ x∈j₁ σ≃τ⇇Γ (≤-trans j₁/σ≤j₂/σ j₂/σ≤l) l⇉as≃bs⇉b⋯c

    -- Equal hereditary substitutions map spines to spine identities.
    Sp⇉-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {as j₁ j₂} →
               ⌊ Γ ⌋Ctx ⊢ j₁ kds → Γ ⊢ j₁ ⇉∙ as ⇉ j₂ → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
               Δ ⊢ j₁ Kind/⟨ k ⟩ σ ⇉∙ as //⟨ k ⟩ σ ≃
                                      as //⟨ k ⟩ τ ⇉ j₂ Kind/⟨ k ⟩ σ
    Sp⇉-/⟨⟩≃ _ ⇉-[] σ⇇Γ = ≃-[]
    Sp⇉-/⟨⟩≃ {k} (kds-Π j₁-kds j₂-kds)
             (⇉-∷ {a} {_} {j₁} {j₂} a⇇j₁ j₁-kd j₂[a]⇉as⇉j₃) σ⇇Γ =
      ≃-∷ (Nf⇇-/⟨⟩≃-≃ a⇇j₁ j₁-kd σ⇇Γ)
          (subst (_ ⊢_⇉∙ _ ≃ _ ⇉ _) j₂[a]/σ≡j₂/σ[a/σ]
                 (Sp⇉-/⟨⟩≃ (kds-/⟨⟩ j₂-kds (∈-hsub a∈⌊j₁⌋)) j₂[a]⇉as⇉j₃ σ⇇Γ))
      where
        a∈⌊j₁⌋ = Nf⇇-Nf∈ a⇇j₁

        j₂[a]/σ≡j₂/σ[a/σ] = begin
            j₂ Kind[ a ∈ ⌊ j₁ ⌋ ] Kind/⟨ k ⟩ _
          ≡⟨ kds-[]-/⟨⟩-↑⋆ [] j₂-kds a∈⌊j₁⌋ (/⟨⟩⇇-/⟨⟩∈ (/⟨⟩≃-valid₁ σ⇇Γ)) ⟩
            j₂ Kind/⟨ k ⟩ _ ↑ Kind/⟨ ⌊ j₁ ⌋ ⟩ sub (a /⟨ k ⟩ _)
          ≡⟨ cong (_ Kind[ a /⟨ k ⟩ _ ∈_]) (sym (⌊⌋-Kind/⟨⟩ j₁)) ⟩
            (j₂ Kind/⟨ k ⟩ _ ↑) Kind[ a /⟨ k ⟩ _ ∈ ⌊ j₁ Kind/⟨ k ⟩ _ ⌋ ]
          ∎

    -- Equal hereditary substitutions map checked normal forms to
    -- subtypes.
    Nf⇇-/⟨⟩≃-<: : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a j} →
                  Γ ⊢Nf a ⇇ j → Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
                  Δ ⊢ a /⟨ k ⟩ σ <: a /⟨ k ⟩ τ ⇇ j Kind/⟨ k ⟩ σ
    Nf⇇-/⟨⟩≃-<: (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)) _ σ≃τ⇇Γ =
      let σ⇇Γ   = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ   = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          τ≃σ⇇Γ = /⟨⟩≃-sym σ≃τ⇇Γ
      in <:-⇇ (⇇-⇑ (Nf⇉-/⟨⟩ a⇉b₁⋯c₁ σ⇇Γ) (<∷-/⟨⟩≃ (<∷-⋯ b₂<:b₁ c₁<:c₂) σ⇇Γ))
              (⇇-⇑ (Nf⇉-/⟨⟩ a⇉b₁⋯c₁ τ⇇Γ) (<∷-/⟨⟩≃ (<∷-⋯ b₂<:b₁ c₁<:c₂) τ≃σ⇇Γ))
              (Nf⇉-⋯-/⟨⟩≃ a⇉b₁⋯c₁ σ≃τ⇇Γ)
    Nf⇇-/⟨⟩≃-<: (⇇-⇑ a⇉Πj₁l₁ (<∷-Π j₂<∷j₁ l₁<∷l₂ Πj₁l₁-kd)) Πj₂k₂-kd σ≃τ⇇Γ =
      let σ⇇Γ = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          Πj₁l₁/σ<∷Πj₂l₂/σ = <∷-/⟨⟩≃ (<∷-Π j₂<∷j₁ l₁<∷l₂ Πj₁l₁-kd) σ⇇Γ
          Πj₂l₂/σ-kd       = kd-/⟨⟩ Πj₂k₂-kd σ⇇Γ
      in <:⇇-⇑ (Nf⇉-/⟨⟩≃ a⇉Πj₁l₁ Πj₁l₁-kd σ≃τ⇇Γ) Πj₁l₁/σ<∷Πj₂l₂/σ Πj₂l₂/σ-kd

    -- Equal hereditary substitutions map checked normal forms to type
    -- identities.
    Nf⇇-/⟨⟩≃-≃ : ∀ {m n Γ k Δ} {σ τ : SVSub m n} {a j} →
                 Γ ⊢Nf a ⇇ j → Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
                 Δ ⊢ a /⟨ k ⟩ σ ≃ a /⟨ k ⟩ τ ⇇ j Kind/⟨ k ⟩ σ
    Nf⇇-/⟨⟩≃-≃ a⇇k k-kd σ≃τ⇇Γ =
      let τ≃σ⇇Γ  = /⟨⟩≃-sym σ≃τ⇇Γ
          k/σ-kd = kd-/⟨⟩ k-kd (/⟨⟩≃-valid₁ σ≃τ⇇Γ)
      in <:-antisym k/σ-kd (Nf⇇-/⟨⟩≃-<: a⇇k k-kd σ≃τ⇇Γ)
                    (<:⇇-⇑ (Nf⇇-/⟨⟩≃-<: a⇇k k-kd τ≃σ⇇Γ)
                    (kd-/⟨⟩≃-<∷ k-kd τ≃σ⇇Γ) k/σ-kd)

    -- Equal hereditary substitutions preserve subkinding.
    <∷-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {j₁ j₂} →
              Γ ⊢ j₁ <∷ j₂ → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
              Δ ⊢ j₁ Kind/⟨ k ⟩ σ <∷ j₂ Kind/⟨ k ⟩ τ
    <∷-/⟨⟩≃ (<∷-⋯ a₂<:a₁ b₁<:b₂) σ≃τ⇇Γ =
      <∷-⋯ (<:-/⟨⟩≃ a₂<:a₁ (/⟨⟩≃-sym σ≃τ⇇Γ)) (<:-/⟨⟩≃ b₁<:b₂ σ≃τ⇇Γ)
    <∷-/⟨⟩≃ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) σ≃τ⇇Γ =
      let τ≃σ⇇Γ = /⟨⟩≃-sym σ≃τ⇇Γ
          τ≃τ⇇Γ = /⟨⟩≃-valid₂ σ≃τ⇇Γ
      in <∷-Π (<∷-/⟨⟩≃ j₂<∷j₁ (/⟨⟩≃-sym σ≃τ⇇Γ))
              (<∷-/⟨⟩≃ k₁<∷k₂ (≃-H↑ (<∷-/⟨⟩≃-wf k₁<∷k₂ τ≃σ⇇Γ)
                                    (<∷-/⟨⟩≃-wf k₁<∷k₂ τ≃τ⇇Γ) σ≃τ⇇Γ))
              (kd-/⟨⟩ Πj₁k₁-kd (/⟨⟩≃-valid₁ σ≃τ⇇Γ))

    -- Equal hereditary substitutions preserve subtyping.

    <:-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a₁ a₂} →
              Γ ⊢ a₁ <: a₂ → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
              Δ ⊢ a₁ /⟨ k ⟩ σ <: a₂ /⟨ k ⟩ τ
    <:-/⟨⟩≃ (<:-trans a<:b b<:c) σ≃τ⇇Γ =
      <:-trans (<:-/⟨⟩≃ a<:b (/⟨⟩≃-valid₁ σ≃τ⇇Γ)) (<:-/⟨⟩≃ b<:c σ≃τ⇇Γ)
    <:-/⟨⟩≃ (<:-⊥ a⇉a⋯a) σ≃τ⇇Γ = <:-⊥ (Nf⇉-/⟨⟩ a⇉a⋯a (/⟨⟩≃-valid₂ σ≃τ⇇Γ))
    <:-/⟨⟩≃ (<:-⊤ a⇉a⋯a) σ≃τ⇇Γ = <:-⊤ (Nf⇉-/⟨⟩ a⇉a⋯a (/⟨⟩≃-valid₁ σ≃τ⇇Γ))
    <:-/⟨⟩≃ (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) σ≃τ⇇Γ =
      let τ≃σ⇇Γ = /⟨⟩≃-sym σ≃τ⇇Γ
          τ≃τ⇇Γ = /⟨⟩≃-valid₂ σ≃τ⇇Γ
      in <:-∀ (<∷-/⟨⟩≃ k₂<∷k₁ τ≃σ⇇Γ)
              (<:-/⟨⟩≃ a₁<:a₂ (≃-H↑ (<:-/⟨⟩≃-wf a₁<:a₂ τ≃σ⇇Γ)
                                    (<:-/⟨⟩≃-wf a₁<:a₂ τ≃τ⇇Γ) σ≃τ⇇Γ))
         (Nf⇉-/⟨⟩ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁ (/⟨⟩≃-valid₁ σ≃τ⇇Γ))
    <:-/⟨⟩≃ (<:-→ a₂<:a₁ b₁<:b₂) σ≃τ⇇Γ =
      <:-→ (<:-/⟨⟩≃ a₂<:a₁ (/⟨⟩≃-sym σ≃τ⇇Γ)) (<:-/⟨⟩≃ b₁<:b₂ σ≃τ⇇Γ)
    <:-/⟨⟩≃ {σ = σ} (<:-∙ {x} x∈j j⇉as≃bs⇉c⋯d) σ≃τ⇇Γ =
      let j-kds = kd-kds (Var∈-valid x∈j)
      in Var∈-/⟨⟩≃-⇑-?∙∙ x∈j σ≃τ⇇Γ ≤-refl (Sp≃-/⟨⟩≃ j-kds j⇉as≃bs⇉c⋯d σ≃τ⇇Γ)
    <:-/⟨⟩≃ (<:-⟨| a∈b⋯c) σ≃τ⇇Γ =
      let a/σ⇉b/σ⋯c/σ = Ne∈-/⟨⟩ a∈b⋯c (/⟨⟩≃-valid₁ σ≃τ⇇Γ)
      in <:-trans (<:-⟨|-Nf⇇ a/σ⇉b/σ⋯c/σ) (Ne∈-/⟨⟩≃ a∈b⋯c σ≃τ⇇Γ)
    <:-/⟨⟩≃ (<:-|⟩ a∈b⋯c) σ≃τ⇇Γ =
      let a/τ⇉b/τ⋯c/τ = Ne∈-/⟨⟩ a∈b⋯c (/⟨⟩≃-valid₂ σ≃τ⇇Γ)
      in <:-trans (Ne∈-/⟨⟩≃ a∈b⋯c σ≃τ⇇Γ) (<:-|⟩-Nf⇇ a/τ⇉b/τ⋯c/τ)

    <:⇇-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a₁ a₂ j} →
               Γ ⊢ a₁ <: a₂ ⇇ j → Γ ⊢ j kd → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
               Δ ⊢ a₁ /⟨ k ⟩ σ <: a₂ /⟨ k ⟩ τ ⇇ j Kind/⟨ k ⟩ σ
    <:⇇-/⟨⟩≃ (<:-⇇ a₁⇇b⋯c a₂⇇b⋯c a₁<:a₂) b⋯c-kd σ≃τ⇇Γ =
      let σ⇇Γ     = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ     = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          τ≃σ⇇Γ   = /⟨⟩≃-sym σ≃τ⇇Γ
      in <:-⇇ (Nf⇇-/⟨⟩ a₁⇇b⋯c σ⇇Γ)
              (Nf⇇-⇑ (Nf⇇-/⟨⟩ a₂⇇b⋯c τ⇇Γ) (kd-/⟨⟩≃-<∷ b⋯c-kd τ≃σ⇇Γ))
              (<:-/⟨⟩≃ a₁<:a₂ σ≃τ⇇Γ)
    <:⇇-/⟨⟩≃ (<:-λ a₁<:a₂⇇l Λj₁a₁⇇Πjl Λj₂a₂⇇Πjl) (kd-Π j-kd l-kd) σ≃τ⇇Γ =
      let σ⇇Γ     = /⟨⟩≃-valid₁ σ≃τ⇇Γ
          τ⇇Γ     = /⟨⟩≃-valid₂ σ≃τ⇇Γ
          τ≃σ⇇Γ   = /⟨⟩≃-sym σ≃τ⇇Γ
          j/σ≅j/σ = kd-/⟨⟩≃-≅ j-kd σ⇇Γ
          j/σ≅j/τ = kd-/⟨⟩≃-≅ j-kd σ≃τ⇇Γ
      in <:-λ (<:⇇-/⟨⟩≃ a₁<:a₂⇇l l-kd (≃-H↑ j/σ≅j/σ j/σ≅j/τ σ≃τ⇇Γ))
              (Nf⇇-/⟨⟩ Λj₁a₁⇇Πjl σ⇇Γ)
              (Nf⇇-⇑ (Nf⇇-/⟨⟩ Λj₂a₂⇇Πjl τ⇇Γ) (kd-/⟨⟩≃-<∷ (kd-Π j-kd l-kd) τ≃σ⇇Γ))

    -- Equal hereditary substitutions preserve spine equality.
    Sp≃-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {as₁ as₂ j₁ j₂} →
               ⌊ Γ ⌋Ctx ⊢ j₁ kds →
               Γ ⊢ j₁ ⇉∙ as₁ ≃ as₂ ⇉ j₂ → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
               Δ ⊢ j₁ Kind/⟨ k ⟩ σ ⇉∙ as₁ //⟨ k ⟩ σ ≃
                                      as₂ //⟨ k ⟩ τ ⇉ j₂ Kind/⟨ k ⟩ σ
    Sp≃-/⟨⟩≃ _ ≃-[] σ≃τ⇇Γ = ≃-[]
    Sp≃-/⟨⟩≃ {k} (kds-Π j₁-kds j₂-kds)
             (≃-∷ {a} {j = j₁} {j₂} a≃b as≃bs) σ≃τ⇇Γ =
      let a∈⌊j₁⌋            = Nf⇇-Nf∈ (proj₁ (≃-valid a≃b))
          j₂[a]/σ≡j₂/σ[a/σ] = begin
              j₂ Kind[ a ∈ ⌊ j₁ ⌋ ] Kind/⟨ k ⟩ _
            ≡⟨ kds-[]-/⟨⟩-↑⋆ [] j₂-kds a∈⌊j₁⌋ (/⟨⟩⇇-/⟨⟩∈ (/⟨⟩≃-valid₁ σ≃τ⇇Γ)) ⟩
              j₂ Kind/⟨ k ⟩ _ ↑ Kind/⟨ ⌊ j₁ ⌋ ⟩ sub (a /⟨ k ⟩ _)
            ≡⟨ cong (_ Kind[ a /⟨ k ⟩ _ ∈_]) (sym (⌊⌋-Kind/⟨⟩ j₁)) ⟩
              (j₂ Kind/⟨ k ⟩ _ ↑) Kind[ a /⟨ k ⟩ _ ∈ ⌊ j₁ Kind/⟨ k ⟩ _ ⌋ ]
            ∎
      in ≃-∷ (≃-/⟨⟩≃ a≃b σ≃τ⇇Γ)
             (subst (_ ⊢_⇉∙ _ ≃ _ ⇉ _) j₂[a]/σ≡j₂/σ[a/σ]
                    (Sp≃-/⟨⟩≃ (kds-/⟨⟩ j₂-kds (∈-hsub a∈⌊j₁⌋)) as≃bs σ≃τ⇇Γ))

    -- Equal hereditary substitutions preserve type equality.
    ≃-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {a₁ a₂ j} →
             Γ ⊢ a₁ ≃ a₂ ⇇ j → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
             Δ ⊢ a₁ /⟨ k ⟩ σ ≃ a₂ /⟨ k ⟩ τ ⇇ j Kind/⟨ k ⟩ σ
    ≃-/⟨⟩≃ (<:-antisym k-kd a<:b⇇k b<:a⇇k) σ≃τ⇇Γ =
      let τ≃σ⇇Γ = /⟨⟩≃-sym σ≃τ⇇Γ
          k/σ-kd = kd-/⟨⟩ k-kd (/⟨⟩≃-valid₁ σ≃τ⇇Γ)
      in <:-antisym k/σ-kd (<:⇇-/⟨⟩≃ a<:b⇇k k-kd σ≃τ⇇Γ)
                    (<:⇇-⇑ (<:⇇-/⟨⟩≃ b<:a⇇k k-kd τ≃σ⇇Γ)
                           (kd-/⟨⟩≃-<∷ k-kd τ≃σ⇇Γ) k/σ-kd)

    -- Applications in canonical kind checking are admissible.

    ?⇇-⇑-?∙∙ : ∀ {k n} {Γ : Ctx n} {r a j as b c} →
               Γ ⊢?⟨ k ⟩ r ⇇ a → Γ ⊢ a ≤ kd j →
               Γ ⊢ j ⇉∙ as ⇉ b ⋯ c → Γ ⊢Nf r ?∙∙⟨ k ⟩ as ⇇ b ⋯ c
    ?⇇-⇑-?∙∙ (≃-hit a≃a⇇j ⌊j⌋≡k) j≤l l⇉as⇉b⋯c =
      Nf⇇-∙∙ (Nf⇇-⇑-≤ (proj₁ (≃-valid a≃a⇇j)) j≤l) l⇉as⇉b⋯c
             (⌊⌋≡-trans (sym (≤-⌊⌋ j≤l)) ⌊j⌋≡k)
    ?⇇-⇑-?∙∙ (≃-miss y Γ-ctx Γ[y]≡a₁ a₁≤a₂) a₂≤l l⇉as⇉b⋯c =
      Nf⇇-ne (∈-∙ (Var∈-⇑-≤ y Γ-ctx Γ[y]≡a₁ (≤-trans a₁≤a₂ a₂≤l)) l⇉as⇉b⋯c)

    Nf⇇-∙∙ : ∀ {n} {Γ : Ctx n} {a as j₁ j₂ k} →
             Γ ⊢Nf a ⇇ j₁ → Γ ⊢ j₁ ⇉∙ as ⇉ j₂ → ⌊ j₁ ⌋≡ k →
             Γ ⊢Nf a ∙∙⟨ k ⟩ as ⇇ j₂
    Nf⇇-∙∙ a⇇j₁ ⇉-[] ⌊j₁⌋≡k = a⇇j₁
    Nf⇇-∙∙ a⇇Πj₁j₂ (⇉-∷ b⇇j₁ j₁-kd j₂[b]⇉as⇉j₃) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) =
      Nf⇇-∙∙ (Nf⇇-Π-e a⇇Πj₁j₂ b⇇j₁ j₁-kd (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂))
             j₂[b]⇉as⇉j₃ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)

    Nf⇇-Π-e : ∀ {n} {Γ : Ctx n} {a b j₁ j₂ k} →
              Γ ⊢Nf a ⇇ Π j₁ j₂ → Γ ⊢Nf b ⇇ j₁ → Γ ⊢ j₁ kd →
              ⌊ Π j₁ j₂ ⌋≡ k → Γ ⊢Nf a ⌜·⌝⟨ k ⟩ b ⇇ j₂ Kind[ b ∈ ⌊ j₁ ⌋ ]
    Nf⇇-Π-e {_} {Γ} {_} {b}
            (⇇-⇑ (⇉-Π-i j₁-kd a⇉l₁)
            (<∷-Π {j₁} {j₂} {l₁} {l₂} j₂<∷j₁ l₁<∷l₂ Πj₁l₁-kd))
            b⇇j₂ j₂-kd (is-⇒ {_} {_} {k₁} ⌊j₂⌋≡k₁ ⌊l₂⌋≡k₂) =
      let σ⇇j₂∷Γ = ⇇-hsub b⇇j₂ j₂-kd ⌊j₂⌋≡k₁
      in ⇇-⇑ (Nf⇉-/⟨⟩ (⇓-Nf⇉ j₂-kd j₂<∷j₁ a⇉l₁) σ⇇j₂∷Γ)
             (subst (λ k → Γ ⊢ l₁ Kind[ b ∈ k₁ ] <∷ l₂ Kind[ b ∈ k ])
                    (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₂⌋≡k₁))
                    (<∷-/⟨⟩≃ l₁<∷l₂ σ⇇j₂∷Γ))

    -- Applications in checked type equality are admissible.

    ?≃-⇑-?∙∙ : ∀ {k n} {Γ : Ctx n} {r₁ r₂ a j as bs c d} →
               Γ ⊢?⟨ k ⟩ r₁ ≃ r₂ ⇇ a → Γ ⊢ a ≤ kd j →
               Γ ⊢ j ⇉∙ as ≃ bs ⇉ c ⋯ d →
               Γ ⊢ r₁ ?∙∙⟨ k ⟩ as <: r₂ ?∙∙⟨ k ⟩ bs
    ?≃-⇑-?∙∙ (≃-hit a≃b⇇j ⌊j⌋≡k) j≤l l⇉as≃bs⇉c⋯d =
      ≃⇒<:-⋯ (≃-∙∙ (≃-⇑-≤ a≃b⇇j j≤l) l⇉as≃bs⇉c⋯d
                   (⌊⌋≡-trans (sym (≤-⌊⌋ j≤l)) ⌊j⌋≡k))
    ?≃-⇑-?∙∙ (≃-miss y Γ-ctx Γ[y]≡a₁ a₁≤a₂) a₂≤l l⇉as≃bs⇉c⋯d =
      <:-∙ (Var∈-⇑-≤ y Γ-ctx Γ[y]≡a₁ (≤-trans a₁≤a₂ a₂≤l)) l⇉as≃bs⇉c⋯d

    ≃-∙∙ : ∀ {n} {Γ : Ctx n} {a b as bs j₁ j₂ k} →
           Γ ⊢ a ≃ b ⇇ j₁ → Γ ⊢ j₁ ⇉∙ as ≃ bs ⇉ j₂ → ⌊ j₁ ⌋≡ k →
           Γ ⊢ a ∙∙⟨ k ⟩ as ≃ b ∙∙⟨ k ⟩ bs ⇇ j₂
    ≃-∙∙ a≃b⇇j₁ ≃-[] ⌊j₁⌋≡k = a≃b⇇j₁
    ≃-∙∙ a≃b⇇Πj₁j₂ (≃-∷ c≃d⇇j₁ j₂[b]⇉cs≃ds⇉j₃) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) =
      ≃-∙∙ (≃-Π-e a≃b⇇Πj₁j₂ c≃d⇇j₁ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂))
           j₂[b]⇉cs≃ds⇉j₃ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)

    ≃-Π-e : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j₁ j₂ k} →
            Γ ⊢ a₁ ≃ a₂ ⇇ Π j₁ j₂ → Γ ⊢ b₁ ≃ b₂ ⇇ j₁ → ⌊ Π j₁ j₂ ⌋≡ k →
            Γ ⊢ a₁ ⌜·⌝⟨ k ⟩ b₁ ≃ a₂ ⌜·⌝⟨ k ⟩ b₂ ⇇ j₂ Kind[ b₁ ∈ ⌊ j₁ ⌋ ]
    ≃-Π-e a₁≃a₂⇇Πj₁j₂ b₁≃b₂⇇j₂ (is-⇒ ⌊j₂⌋≡k₁ ⌊j₂⌋≡k₂) with ≃-Π-can a₁≃a₂⇇Πj₁j₂
    ≃-Π-e {_} {Γ} {_} {_} {b₁} {b₂} Λl₁a₁≃Λl₂a₂⇇Πj₁j₂ b₁≃b₂⇇j₁
          (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
      | l₁ , a₁ , l₂ , a₂ , Λl₁a₁⇇Πj₁j₂ , Λl₂a₂⇇Πj₁j₂ , kd-Π j₁-kd j₂-kd ,
        j₁<∷l₁ , l₁≅l₂ , a₁<:a₂⇇j₂ , a₂<:a₁⇇j₂ , refl , refl =
        let ⌊Πj₁j₂⌋≡k     = is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂
            k₁≡⌊j₁⌋       = sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
            b₁⇇j₁ , b₂⇇j₁ = ≃-valid b₁≃b₂⇇j₁
            σ≃τ⇇j₁∷Γ      = ≃-hsub b₁≃b₂⇇j₁ ⌊j₁⌋≡k₁
            τ≃σ⇇j₁∷Γ      = /⟨⟩≃-sym σ≃τ⇇j₁∷Γ
            σ⇇j₁∷Γ        = /⟨⟩≃-valid₁ σ≃τ⇇j₁∷Γ
        in <:-antisym (subst (λ k → _ ⊢ _ Kind[ _ ∈ k ] kd)
                             (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁))
                             (kd-/⟨⟩ j₂-kd (/⟨⟩≃-valid₁ σ≃τ⇇j₁∷Γ)))
                      (subst (λ k → _ ⊢ _ <: _ ⇇ _ Kind[ _ ∈ k ]) k₁≡⌊j₁⌋
                             (<:⇇-/⟨⟩≃ a₁<:a₂⇇j₂ j₂-kd σ≃τ⇇j₁∷Γ))
                      (<:⇇-⇑ (<:⇇-/⟨⟩≃ a₂<:a₁⇇j₂ j₂-kd τ≃σ⇇j₁∷Γ)
                             (subst (λ k → Γ ⊢ _ <∷ _ Kind[ _ ∈ k ]) k₁≡⌊j₁⌋
                                    (kd-/⟨⟩≃-<∷ j₂-kd τ≃σ⇇j₁∷Γ))
                             (subst (λ k → Γ ⊢ _ Kind[ _ ∈ k ] kd) k₁≡⌊j₁⌋
                                    (kd-/⟨⟩ j₂-kd σ⇇j₁∷Γ)))

    -- Helpers (to satisfy the termination checker).
    --
    -- These are simply (manual) expansions of the form
    --
    --   XX-/⟨⟩≃-wf x σ≃τ⇇Γ  =  kd-/⟨⟩≃-≅ (wf-kd-inv (wf-∷₁ (XX-ctx x))) σ≃τ⇇Γ
    --
    -- to ensure the above definitions remain structurally recursive
    -- in the various derivations.

    kd-/⟨⟩≃-wf : ∀ {m n Γ l Δ} {σ τ : SVSub m n} {j k} →
                 kd j ∷ Γ ⊢ k kd → Δ ⊢/⟨ l ⟩ σ ≃ τ ⇇ Γ →
                 Δ ⊢ j Kind/⟨ l ⟩ σ ≅ j Kind/⟨ l ⟩ τ
    kd-/⟨⟩≃-wf (kd-⋯ a⇉a⋯a _) σ≃τ⇇Γ = Nf⇉-/⟨⟩≃-wf a⇉a⋯a σ≃τ⇇Γ
    kd-/⟨⟩≃-wf (kd-Π j-kd _)  σ≃τ⇇Γ = kd-/⟨⟩≃-wf j-kd σ≃τ⇇Γ

    Nf⇉-/⟨⟩≃-wf : ∀ {m n Γ l Δ} {σ τ : SVSub m n} {j a k} →
                  kd j ∷ Γ ⊢Nf a ⇉ k → Δ ⊢/⟨ l ⟩ σ ≃ τ ⇇ Γ →
                  Δ ⊢ j Kind/⟨ l ⟩ σ ≅ j Kind/⟨ l ⟩ τ
    Nf⇉-/⟨⟩≃-wf (⇉-⊥-f (wf-kd j-kd ∷ Γ-ctx)) σ≃τ⇇Γ = kd-/⟨⟩≃-≅ j-kd σ≃τ⇇Γ
    Nf⇉-/⟨⟩≃-wf (⇉-⊤-f (wf-kd j-kd ∷ Γ-ctx)) σ≃τ⇇Γ = kd-/⟨⟩≃-≅ j-kd σ≃τ⇇Γ
    Nf⇉-/⟨⟩≃-wf (⇉-∀-f k-kd _)               σ≃τ⇇Γ = kd-/⟨⟩≃-wf k-kd σ≃τ⇇Γ
    Nf⇉-/⟨⟩≃-wf (⇉-→-f a⇉a⋯a _)              σ≃τ⇇Γ = Nf⇉-/⟨⟩≃-wf a⇉a⋯a σ≃τ⇇Γ
    Nf⇉-/⟨⟩≃-wf (⇉-Π-i j-kd _)               σ≃τ⇇Γ = kd-/⟨⟩≃-wf j-kd σ≃τ⇇Γ
    Nf⇉-/⟨⟩≃-wf (⇉-s-i a∈b⋯c)                σ≃τ⇇Γ = Ne∈-/⟨⟩≃-wf a∈b⋯c σ≃τ⇇Γ

    Ne∈-/⟨⟩≃-wf : ∀ {m n Γ l Δ} {σ τ : SVSub m n} {j a k} →
                  kd j ∷ Γ ⊢Ne a ∈ k → Δ ⊢/⟨ l ⟩ σ ≃ τ ⇇ Γ →
                  Δ ⊢ j Kind/⟨ l ⟩ σ ≅ j Kind/⟨ l ⟩ τ
    Ne∈-/⟨⟩≃-wf (∈-∙ x∈k _) σ≃τ⇇Γ = Var∈-/⟨⟩≃-wf x∈k σ≃τ⇇Γ

    Var∈-/⟨⟩≃-wf : ∀ {m n Γ l Δ} {σ τ : SVSub m n} {j a k} →
                   kd j ∷ Γ ⊢Var a ∈ k → Δ ⊢/⟨ l ⟩ σ ≃ τ ⇇ Γ →
                   Δ ⊢ j Kind/⟨ l ⟩ σ ≅ j Kind/⟨ l ⟩ τ
    Var∈-/⟨⟩≃-wf (⇉-var x (wf-kd j-kd ∷ Γ-ctx) _) σ≃τ⇇Γ = kd-/⟨⟩≃-≅ j-kd σ≃τ⇇Γ
    Var∈-/⟨⟩≃-wf (⇇-⇑ x∈k _ _)                    σ≃τ⇇Γ = Var∈-/⟨⟩≃-wf x∈k σ≃τ⇇Γ

    <∷-/⟨⟩≃-wf : ∀ {m n Γ l Δ} {σ τ : SVSub m n} {j k₁ k₂} →
                 kd j ∷ Γ ⊢ k₁ <∷ k₂ → Δ ⊢/⟨ l ⟩ σ ≃ τ ⇇ Γ →
                 Δ ⊢ j Kind/⟨ l ⟩ σ ≅ j Kind/⟨ l ⟩ τ
    <∷-/⟨⟩≃-wf (<∷-⋯ a₂<:a₁ _)   σ≃τ⇇Γ = <:-/⟨⟩≃-wf a₂<:a₁ σ≃τ⇇Γ
    <∷-/⟨⟩≃-wf (<∷-Π j₁<∷j₂ _ _) σ≃τ⇇Γ = <∷-/⟨⟩≃-wf j₁<∷j₂ σ≃τ⇇Γ

    <:-/⟨⟩≃-wf : ∀ {m n Γ l Δ} {σ τ : SVSub m n} {j a₁ a₂} →
                kd j ∷ Γ ⊢ a₁ <: a₂ → Δ ⊢/⟨ l ⟩ σ ≃ τ ⇇ Γ →
                Δ ⊢ j Kind/⟨ l ⟩ σ ≅ j Kind/⟨ l ⟩ τ
    <:-/⟨⟩≃-wf (<:-trans a<:b _) σ≃τ⇇Γ = <:-/⟨⟩≃-wf a<:b σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-⊥ a⇉a⋯a)      σ≃τ⇇Γ = Nf⇉-/⟨⟩≃-wf a⇉a⋯a σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-⊤ a⇉a⋯a)      σ≃τ⇇Γ = Nf⇉-/⟨⟩≃-wf a⇉a⋯a σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-∀ k₂<∷k₁ _ _) σ≃τ⇇Γ = <∷-/⟨⟩≃-wf k₂<∷k₁ σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-→ a₂<:a₁ _)   σ≃τ⇇Γ = <:-/⟨⟩≃-wf a₂<:a₁ σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-∙ x∈j _)      σ≃τ⇇Γ = Var∈-/⟨⟩≃-wf x∈j σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-⟨| a∈b⋯c)     σ≃τ⇇Γ = Ne∈-/⟨⟩≃-wf a∈b⋯c σ≃τ⇇Γ
    <:-/⟨⟩≃-wf (<:-|⟩ a∈b⋯c)     σ≃τ⇇Γ = Ne∈-/⟨⟩≃-wf a∈b⋯c σ≃τ⇇Γ

  -- Equal hereditary substitutions preserve kind equality.
  ≅-/⟨⟩≃ : ∀ {k m n Γ Δ} {σ τ : SVSub m n} {k₁ k₂} →
           Γ ⊢ k₁ ≅ k₂ → Δ ⊢/⟨ k ⟩ σ ≃ τ ⇇ Γ →
           Δ ⊢ k₁ Kind/⟨ k ⟩ σ ≅ k₂ Kind/⟨ k ⟩ τ
  ≅-/⟨⟩≃ (<∷-antisym j-kd k-kd j<∷k k<∷j) σ≃τ⇇Γ =
    <∷-antisym (kd-/⟨⟩ j-kd (/⟨⟩≃-valid₁ σ≃τ⇇Γ))
               (kd-/⟨⟩ k-kd (/⟨⟩≃-valid₂ σ≃τ⇇Γ))
               (<∷-/⟨⟩≃ j<∷k σ≃τ⇇Γ) (<∷-/⟨⟩≃ k<∷j (/⟨⟩≃-sym σ≃τ⇇Γ))
