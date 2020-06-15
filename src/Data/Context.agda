------------------------------------------------------------------------
-- Abstract typing contexts
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Context where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Relation.Unary using (Pred)


------------------------------------------------------------------------
-- Abstract typing contexts and context extensions.

infixr 5 _∷_

-- Typing contexts.
--
-- A |Ctx T n| is an indexed sequences of T-typed bindings mapping n
-- variables to T-types with 0 to (n - 1) free variables each.  Like
-- lists (Data.List) and vectors (Data.Vec), contexts are cons
-- sequences, i.e. new bindings are added to the front (rather than
-- the back, as is more common in the literature).  For example, a
-- typing context Γ represented in the usual notation as
--
--   Γ  =  xᵢ: Aᵢ, ..., x₁: A₁, x₀: A₀
--
-- is represented here by a term |Γ : Ctx Type i| of the form
--
--   Γ  =  A₀ ∷ A₁ ∷ ... ∷ Aᵢ
--
-- which is consistent with A₀ being the 0-th element of Γ, and with
-- the de Bruijn convention that the 0-th variable corresponds to the
-- closest binding.

data Ctx {ℓ} (T : Pred ℕ ℓ) : ℕ → Set ℓ where
  []  :                         Ctx T zero
  _∷_ : ∀ {n} → T n → Ctx T n → Ctx T (suc n)

module _ {ℓ} {T : Pred ℕ ℓ} where

  head : ∀ {n} → Ctx T (suc n) → T n
  head (t ∷ ts) = t

  tail : ∀ {n} → Ctx T (suc n) → Ctx T n
  tail (t ∷ ts) = ts

  -- Drop the m innermost elements of a context Γ.

  drop : ∀ {n} m → Ctx T (m + n) → Ctx T n
  drop zero         Γ  = Γ
  drop (suc m) (_ ∷ Γ) = drop m Γ

-- A map function that changes the entries in a context pointwise.

map : ∀ {ℓ₁ ℓ₂} {T₁ : Pred ℕ ℓ₁} {T₂ : Pred ℕ ℓ₂} {n} →
      (∀ {k} → T₁ k → T₂ k) → Ctx T₁ n → Ctx T₂ n
map f []      = []
map f (t ∷ Γ) = f t ∷ map f Γ

-- Extensions of typing contexts.
--
-- Context extensions are indexed sequences of bindings that can be
-- concatenated to the front of a typing context.  A |CtxExt T m n| is
-- an extension mapping n variables to T-types with m to (n + m - 1)
-- free variables each.
--
-- NOTE. It is tempting to define contexts as just a special case of
-- context extensions, i.e. as
--
--   Ctx T n  =  CtxExt T zero n
--
-- But this leads to problems when defining e.g. concatenation because
-- of the way context extensions are indexed.  This could be remedied
-- by indexing context extensions differently, but then the definition
-- of |mapExt| below becomes difficult.  An earlier version of this
-- module contained two different (but equivalent) representations for
-- context extensions, but this complicated (rather than simplified)
-- the development overall.

data CtxExt {ℓ} (T : Pred ℕ ℓ) (m : ℕ) : ℕ → Set ℓ where
  []  :                                    CtxExt T m zero
  _∷_ : ∀ {l} → T (l + m) → CtxExt T m l → CtxExt T m (suc l)

infixr 5 _++_

-- Concatenation of context extensions with contexts.

_++_ : ∀ {ℓ} {T : Pred ℕ ℓ} {m n} → CtxExt T m n → Ctx T m → Ctx T (n + m)
[]      ++ Γ = Γ
(t ∷ Δ) ++ Γ = t ∷ (Δ ++ Γ)

-- A map function that point-wise re-indexes and changes the entries
-- in a context extension.

mapExt : ∀ {ℓ₁ ℓ₂} {T₁ : Pred ℕ ℓ₁} {T₂ : Pred ℕ ℓ₂} {m n k} →
         (∀ l → T₁ (l + m) → T₂ (l + n)) → CtxExt T₁ m k → CtxExt T₂ n k
mapExt f []            = []
mapExt f (_∷_ {l} t Γ) = f l t ∷ mapExt (λ l → f l) Γ

-- Operations on contexts that require weakening of types.

module WeakenOps {ℓ} {T : Pred ℕ ℓ} (extension : Extension T) where

  -- Weakening of types.

  open Extension extension public

  -- Convert a context or context extension to its vector representation.

  toVec : ∀ {n} → Ctx T n → Vec (T n) n
  toVec []      = []
  toVec (t ∷ Γ) = weaken t /∷ toVec Γ

  extToVec : ∀ {k m n} → CtxExt T m n → Vec (T m) k → Vec (T (n + m)) (n + k)
  extToVec []      ts = ts
  extToVec (t ∷ Γ) ts = weaken t /∷ extToVec Γ ts

  -- Lookup the type of a variable in a context or context extension.

  lookup : ∀ {n} → Ctx T n → Fin n → T n
  lookup Γ x = Vec.lookup (toVec Γ) x

  extLookup : ∀ {k m n} → CtxExt T m n → Vec (T m) k → Fin (n + k) → T (n + m)
  extLookup Δ ts x = Vec.lookup (extToVec Δ ts) x

-- Operations on contexts that require substitutions in types.

module SubstOps {ℓ₁ ℓ₂} {T₁ : Pred ℕ ℓ₁} {T₂ : Pred ℕ ℓ₂}
                (application : Application T₁ T₂)
                (simple      : Simple T₂)
                where

  open Application application public -- Application of T′ substitutions to Ts.
  open Simple      simple      public -- Simple T′ substitutions.

  -- Application of substitutions to context extensions.

  _E/_ : ∀ {k m n} → CtxExt T₁ m k → Sub T₂ m n → CtxExt T₁ n k
  Γ E/ σ = mapExt (λ l t → t / σ ↑⋆ l) Γ
