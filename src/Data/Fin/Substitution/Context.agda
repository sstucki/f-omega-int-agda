------------------------------------------------------------------------
-- Abstract typing contexts
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Fin.Substitution.Context where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.All.Properties using (gmap)


------------------------------------------------------------------------
-- Abstract typing contexts and context extensions.
--
-- FIXME: Make the definitions in this module more
-- universe-polymorphic (following the style used in
-- Data.Fin.Substitution.Lemmas).

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

data Ctx (T : ℕ → Set) : ℕ → Set where
  []  :                         Ctx T zero
  _∷_ : ∀ {n} → T n → Ctx T n → Ctx T (suc n)

head : ∀ {T n} → Ctx T (suc n) → T n
head (t ∷ ts) = t

tail : ∀ {T n} → Ctx T (suc n) → Ctx T n
tail (t ∷ ts) = ts

-- Drop the m innermost elements of a context Γ.

drop : ∀ {T n} m → Ctx T (m + n) → Ctx T n
drop zero         Γ  = Γ
drop (suc m) (_ ∷ Γ) = drop m Γ

-- A map function that changes the entries in a context pointwise.

map : ∀ {T₁ T₂ n} → (∀ {k} → T₁ k → T₂ k) → Ctx T₁ n → Ctx T₂ n
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

data CtxExt (T : ℕ → Set) (m : ℕ) : ℕ → Set where
  []  :                                    CtxExt T m zero
  _∷_ : ∀ {l} → T (l + m) → CtxExt T m l → CtxExt T m (suc l)

infixr 5 _++_

-- Concatenation of context extensions with contexts.

_++_ : ∀ {T m n} → CtxExt T m n → Ctx T m → Ctx T (n + m)
[]      ++ Γ = Γ
(t ∷ Δ) ++ Γ = t ∷ (Δ ++ Γ)

-- A map function that point-wise re-indexes and changes the entries
-- in a context extension.

mapExt : ∀ {T₁ T₂ k m n} → (∀ l → T₁ (l + m) → T₂ (l + n)) →
         CtxExt T₁ m k → CtxExt T₂ n k
mapExt f []            = []
mapExt f (_∷_ {l} t Γ) = f l t ∷ mapExt (λ l → f l) Γ

-- Operations on contexts that require weakening of types.

module WeakenOps {T : ℕ → Set} (extension : Extension T) where

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

module SubstOps {T T′ : ℕ → Set}
                (application : Application T T′)
                (simple      : Simple T′)
                where

  open Application application public -- Application of T′ substitutions to Ts.
  open Simple      simple      public -- Simple T′ substitutions.

  -- Application of substitutions to context extensions.

  _E/_ : ∀ {k m n} → CtxExt T m k → Sub T′ m n → CtxExt T n k
  Γ E/ σ = mapExt (λ l t → t / σ ↑⋆ l) Γ


------------------------------------------------------------------------
-- Abstract well-formed typing contexts and context extensions.

-- Abstract well-formedness.
--
-- An abtract well-formedness relation _⊢_wf : Wf Tp is a binary
-- relation which, in a given Tp-context, asserts the well-formedness
-- of Tp-types.

Wf : (ℕ → Set) → Set₁
Wf Tp = ∀ {n} → Ctx Tp n → Tp n → Set

-- Well-formed contexts and context extensions.
--
-- A well-formed typing context (Γ wf) is a context Γ in which every
-- participating T-type is well-formed.

module WellFormedContext {T} (_⊢_wf : Wf T) where
  infix  4 _wf _⊢_wfExt
  infixr 5 _∷_

  -- Well-formed typing contexts and context extensions.

  data _wf : ∀ {n} → Ctx T n → Set where
    []  :                                              [] wf
    _∷_ : ∀ {n t} {Γ : Ctx T n} → Γ ⊢ t wf → Γ wf → t ∷ Γ wf

  data _⊢_wfExt {m} (Γ : Ctx T m) : ∀ {n} → CtxExt T m n → Set where
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

  record WfWeakenOps (extension : Extension T) : Set where
    private module W = WeakenOps extension

    -- Weakening of well-formedness judgments.

    field wf-weaken : ∀ {n} {Γ : Ctx T n} {a b} → Γ ⊢ a wf → Γ ⊢ b wf →
                      (a ∷ Γ) ⊢ W.weaken b wf

    -- Convert a well-formed context (extension) to its All representation.

    toAll : ∀ {n} {Γ : Ctx T n} → Γ wf → All (λ t → Γ ⊢ t wf) (W.toVec Γ)
    toAll []            = []
    toAll (t-wf ∷ Γ-wf) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (toAll Γ-wf)

    extToAll : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} →
               All (λ t → Γ ⊢ t wf) (W.toVec Γ) → Γ ⊢ Δ wfExt →
               All (λ a → (Δ ++ Γ) ⊢ a wf) (W.toVec (Δ ++ Γ))
    extToAll ts-wf []               = ts-wf
    extToAll ts-wf (t-wf ∷ Δ-wfExt) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (extToAll ts-wf Δ-wfExt)

    -- Lookup the well-formedness proof of a variable in a context.

    lookup : ∀ {n} {Γ : Ctx T n} → Γ wf → (x : Fin n) → Γ ⊢ (W.lookup Γ x) wf
    lookup Γ-wf x = All.lookup x (toAll Γ-wf)

    extLookup : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} →
                All (λ t → Γ ⊢ t wf) (W.toVec Γ) → Γ ⊢ Δ wfExt →
                ∀ x → (Δ ++ Γ) ⊢ (W.lookup (Δ ++ Γ) x) wf
    extLookup ts-wf Γ-wf x = All.lookup x (extToAll ts-wf Γ-wf)

-- Trivial well-formedness.
--
-- This module provides a trivial well-formedness relation and the
-- corresponding trivially well-formed contexts.  This is useful when
-- implmenting typed substitutions on types that either lack or do not
-- necessitate a notion of well-formedness.

module ⊤-WellFormed {T : ℕ → Set} (extension : Extension T) where

  infix  4 _⊢_wf

  -- Trivial well-formedness.
  _⊢_wf : Wf T
  _ ⊢ _ wf = ⊤

  open WellFormedContext _⊢_wf public

  -- Trivial well-formedness of contexts and context extensions.

  ctx-wf : ∀ {n} (Γ : Ctx T n) → Γ wf
  ctx-wf []      = []
  ctx-wf (a ∷ Γ) = tt ∷ ctx-wf Γ

  ctx-wfExt : ∀ {m n} (Δ : CtxExt T m n) {Γ : Ctx T m} → Γ ⊢ Δ wfExt
  ctx-wfExt []      = []
  ctx-wfExt (a ∷ Δ) = tt ∷ ctx-wfExt Δ

  module ⊤-WfWeakenOps where

    wfWeakenOps : WfWeakenOps extension
    wfWeakenOps = record { wf-weaken = λ _ _ → tt }

    open WfWeakenOps public
