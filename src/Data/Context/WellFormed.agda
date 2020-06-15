------------------------------------------------------------------------
-- Abstract well-formed typing contexts
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Context.WellFormed where

open import Level using (suc; _⊔_; Lift; lift)
open import Data.Fin using (Fin)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.All.Properties using (gmap)
open import Relation.Binary using (REL)
open import Relation.Unary using (Pred)

open import Data.Context


------------------------------------------------------------------------
-- Abstract well-formed typing

-- An abtract well-formedness judgment _⊢_wf : Wf Tp Tm is a binary
-- relation which, in a given Tp-context, asserts the well-formedness
-- of Tm-terms.

Wf : ∀ {t₁ t₂} → Pred ℕ t₁ → Pred ℕ t₂ → ∀ ℓ → Set (t₁ ⊔ t₂ ⊔ suc ℓ)
Wf Tp Tm ℓ = ∀ {n} → REL (Ctx Tp n) (Tm n) ℓ


------------------------------------------------------------------------
-- Abstract well-formed typing contexts and context extensions.
--
-- A well-formed typing context (Γ wf) is a context Γ in which every
-- participating T-type is well-formed.

module ContextFormation {t ℓ} {T : Pred ℕ t} (_⊢_wf : Wf T T ℓ) where

  infix  4 _wf _⊢_wfExt
  infixr 5 _∷_

  -- Well-formed typing contexts and context extensions.

  data _wf : ∀ {n} → Ctx T n → Set (t ⊔ ℓ) where
    []  :                                              [] wf
    _∷_ : ∀ {n t} {Γ : Ctx T n} → Γ ⊢ t wf → Γ wf → t ∷ Γ wf

  data _⊢_wfExt {m} (Γ : Ctx T m) : ∀ {n} → CtxExt T m n → Set (t ⊔ ℓ) where
    []  : Γ ⊢ [] wfExt
    _∷_ : ∀ {n t} {Δ : CtxExt T m n} →
          (Δ ++ Γ) ⊢ t wf → Γ ⊢ Δ wfExt → Γ ⊢ t ∷ Δ wfExt

  -- Inversions.

  wf-∷₁ : ∀ {n} {Γ : Ctx T n} {a} → a ∷ Γ wf → Γ ⊢ a wf
  wf-∷₁ (a-wf ∷ _) = a-wf

  wf-∷₂ : ∀ {n} {Γ : Ctx T n} {a} → a ∷ Γ wf → Γ wf
  wf-∷₂ (_ ∷ Γ-wf) = Γ-wf

  wfExt-∷₁ : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} {a} →
             Γ ⊢ a ∷ Δ wfExt → (Δ ++ Γ) ⊢ a wf
  wfExt-∷₁ (a-wf ∷ _) = a-wf

  wfExt-∷₂ : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} {a} →
             Γ ⊢ a ∷ Δ wfExt → Γ ⊢ Δ wfExt
  wfExt-∷₂ (_ ∷ Γ-wf) = Γ-wf

  -- Operations on well-formed contexts that require weakening of
  -- well-formedness judgments.

  record WellFormedWeakenOps (typeExtension : Extension T)
                             : Set (suc (t ⊔ ℓ)) where

    private module C = WeakenOps typeExtension
    open C hiding (lookup; extLookup)

    -- Weakening of well-formedness judgments.

    field wf-weaken : ∀ {n} {Γ : Ctx T n} {a b} → Γ ⊢ a wf → Γ ⊢ b wf →
                      (a ∷ Γ) ⊢ weaken b wf

    -- Convert a well-formed context (extension) to its All representation.

    toAll : ∀ {n} {Γ : Ctx T n} → Γ wf → All (λ t → Γ ⊢ t wf) (toVec Γ)
    toAll []            = []
    toAll (t-wf ∷ Γ-wf) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (toAll Γ-wf)

    extToAll : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} →
               All (λ t → Γ ⊢ t wf) (toVec Γ) → Γ ⊢ Δ wfExt →
               All (λ a → (Δ ++ Γ) ⊢ a wf) (toVec (Δ ++ Γ))
    extToAll ts-wf []               = ts-wf
    extToAll ts-wf (t-wf ∷ Δ-wfExt) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (extToAll ts-wf Δ-wfExt)

    -- Lookup the well-formedness proof of a variable in a context.

    lookup : ∀ {n} {Γ : Ctx T n} → Γ wf → (x : Fin n) → Γ ⊢ (C.lookup Γ x) wf
    lookup Γ-wf x = All.lookup x (toAll Γ-wf)

    extLookup : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} →
                All (λ t → Γ ⊢ t wf) (toVec Γ) → Γ ⊢ Δ wfExt →
                ∀ x → (Δ ++ Γ) ⊢ (C.lookup (Δ ++ Γ) x) wf
    extLookup ts-wf Γ-wf x = All.lookup x (extToAll ts-wf Γ-wf)


------------------------------------------------------------------------
-- Trivial well-formedness.
--
-- This module provides a trivial well-formedness relation and the
-- corresponding trivially well-formed contexts.  This is useful when
-- implmenting typed substitutions on types that either lack or do not
-- necessitate a notion of well-formedness.

module ⊤-WellFormed {ℓ} {T : Pred ℕ ℓ} (typeExtension : Extension T) where

  infix  4 _⊢_wf

  -- Trivial well-formedness.

  _⊢_wf : Wf T T ℓ
  _ ⊢ _ wf = Lift ℓ ⊤

  open ContextFormation _⊢_wf public

  -- Trivial well-formedness of contexts and context extensions.

  ctx-wf : ∀ {n} (Γ : Ctx T n) → Γ wf
  ctx-wf []      = []
  ctx-wf (a ∷ Γ) = lift tt ∷ ctx-wf Γ

  ctx-wfExt : ∀ {m n} (Δ : CtxExt T m n) {Γ : Ctx T m} → Γ ⊢ Δ wfExt
  ctx-wfExt []      = []
  ctx-wfExt (a ∷ Δ) = lift tt ∷ ctx-wfExt Δ

  module ⊤-WfWeakenOps where

    wfWeakenOps : WellFormedWeakenOps typeExtension
    wfWeakenOps = record { wf-weaken = λ _ _ → lift tt }

    open WellFormedWeakenOps public
