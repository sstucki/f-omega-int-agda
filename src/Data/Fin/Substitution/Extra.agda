------------------------------------------------------------------------
-- Extra definitions related to simultaneous substitutions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Fin.Substitution.Extra where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (_∷_; map)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Unary using (Pred)

-- Extension of substitutions and iterated weakening.

record Extension {ℓ} (T : Pred ℕ ℓ) : Set ℓ where
  infixr 5 _/∷_

  field weaken : ∀ {n} → T n → T (suc n)  -- Weakens Ts.

  -- Iterated weakening of Ts.

  weaken⋆ : ∀ m {n} → T n → T (m + n)
  weaken⋆ zero    t = t
  weaken⋆ (suc m) t = weaken (weaken⋆ m t)

  -- Extension.
  --
  -- The extension operation t /∷ ρ takes a substitution ρ and extends
  -- it with a term t for an additional free variable.  It is a
  -- generalization of the lifting substitution ρ ↑ = var zero /∷ ρ
  -- where the term for the additional free variable may be something
  -- other than var zero.  Note that the term t must itself admit an
  -- additional free variable so that the resulting substitution t /∷
  -- ρ has an extended domain *and* codomain.  This is in contrast to
  -- t ∷ ρ where the codomain has no additional free variables.
  -- I.e. given (ρ : Sub T m n) we have
  --
  --   t  ∷ ρ : Sub T (1 + m) m         for   t : T m
  --   u /∷ ρ : Sub T (1 + m) (1 + m)   for   u : T (1 + m)

  _/∷_ : ∀ {m n} → T (suc n) → Sub T m n → Sub T (suc m) (suc n)
  t /∷ ρ = t ∷ map weaken ρ

-- A helper module for unpacking an instance of the Simple record
-- together with the extra operations from the Extension module (as if
-- Simple contained an instance of Extension).

module SimpleExt {ℓ} {T : Pred ℕ ℓ} (simple : Simple T) where
  open Simple simple public

  extension : Extension T
  extension = record { weaken = weaken }
  open Extension extension public hiding (weaken)

-- T₂-substitutions in term-like T₁

record TermLikeSubst {ℓ} (T₁ : Pred ℕ ℓ) (T₂ : ℕ → Set)
                     : Set (lsuc (ℓ ⊔ lzero)) where
  field
    app       : ∀ {T₃} → Lift T₃ T₂ → ∀ {m n} → T₁ m → Sub T₃ m n → T₁ n
    termSubst : TermSubst T₂

  open TermSubst termSubst public
    hiding (app; var; weaken; _/Var_; _/_; _/✶_)

  termApplication : Application T₁ T₂
  termApplication = record { _/_ = app termLift }

  varApplication : Application T₁ Fin
  varApplication = record { _/_ = app varLift }

  open Application termApplication public using (_/_; _/✶_)
  open Application varApplication  public using () renaming (_/_ to _/Var_)

  -- Weakening of T₁s.

  weaken : ∀ {n} → T₁ n → T₁ (suc n)
  weaken t = t /Var VarSubst.wk
