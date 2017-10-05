------------------------------------------------------------------------
-- Abstract typing contexts
------------------------------------------------------------------------

module Data.Fin.Substitution.Context where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties        as NatProp
import Data.Nat.Properties.Simple as SimpleNatProp
open import Data.Unit using (⊤; tt)
open import Data.Vec     as Vec using (Vec; []; _∷_)
open import Data.Vec.All as All using (All; []; _∷_)
open import Data.Vec.All.Properties using (gmap)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


------------------------------------------------------------------------
-- Abstract typing contexts and context extensions.

infixr 5 _∷_

-- Extensions of typing contexts.
--
-- Context extensions are indexed sequences that can be concatenated
-- together to form typing contexts.  A CtxExt T m n is an extension
-- mapping (n - m) variables to T-types with m to n free variables
-- each.  I.e. the i-th type (for m ≤ i < n) may refer to any of the
-- previous (i - 1) free variables xₘ, ..., xᵢ₋₁.
data CtxExt (T : ℕ → Set) (m : ℕ) : ℕ → Set where
  []  :                              CtxExt T m m
  _∷_ : ∀ {n} → T n → CtxExt T m n → CtxExt T m (suc n)

-- Typing contexts.
--
-- Typing contexts are just initial context extensions, i.e. the
-- innermost type must not contain any free variables at all.
Ctx : (ℕ → Set) → ℕ → Set
Ctx T = CtxExt T 0

-- Drop the m innermost elements of a context Γ.
drop : ∀ {T n} m → Ctx T (m + n) → Ctx T n
drop zero         Γ  = Γ
drop (suc m) (_ ∷ Γ) = drop m Γ

-- A map function that point-wise changes the entries of a context
-- extension.
map : ∀ {T₁ T₂ m n} → (∀ {l} → T₁ l → T₂ l) → CtxExt T₁ m n → CtxExt T₂ m n
map f []      = []
map f (t ∷ Γ) = f t ∷ map f Γ

infixr 5 _++_

-- Concatenate two context extensions.
_++_ : ∀ {T k m n} → CtxExt T m n → CtxExt T k m → CtxExt T k n
[]      ++ Γ = Γ
(t ∷ Δ) ++ Γ = t ∷ (Δ ++ Γ)

-- The length of a context extension.
length : ∀ {T m n} → CtxExt T m n → ℕ
length []      = 0
length (_ ∷ Γ) = suc (length Γ)

-- Lemmas relating the length of a context extension to its indices.
--
-- NOTE.  Ideally, these lemmas should go into the
-- Data.Fin.Substitution.Context.Properties module but they are used
-- in the implementation of the conversion function CtxExt⇒CtxExt′
-- below so we include them in this module instead.

length-idx : ∀ {T m n} (Γ : CtxExt T m n) → length Γ + m ≡ n
length-idx []      = refl
length-idx (t ∷ Γ) = cong suc (length-idx Γ)

length-idx′ : ∀ {T m n} (Γ : CtxExt T m (n + m)) → length Γ ≡ n
length-idx′ {T} {m} {n} Γ = cancel-+-left m (begin
  m + length Γ    ≡⟨ +-comm m _ ⟩
  length Γ + m    ≡⟨ length-idx Γ ⟩
  n + m           ≡⟨ +-comm n m ⟩
  m + n           ∎)
  where
    open SimpleNatProp using (+-comm)
    open NatProp       using (cancel-+-left)

-- An alternative representation of context extension using
-- relative-indexing.
--
-- A CtxExt′ m n is an extension mapping n variables to T-types with m
-- to (m + n) free variables each.  I.e. the i-th type (for 0 ≤ i < n)
-- may refer to any of the previous (i - 1) free variables x₀, ...,
-- xᵢ₋₁.
--
-- The two representations are ismorphic, as witnessed by the
-- conversions CtxExt⇒CtxExt′ and CtxExt′⇒CtxExt below and the
-- associated lemmas in the Data.Fin.Substitution.Context.Properties
-- module.
data CtxExt′ (T : ℕ → Set) (m : ℕ) : ℕ → Set where
  []  :                                     CtxExt′ T m 0
  _∷_ : ∀ {l} → T (l + m) → CtxExt′ T m l → CtxExt′ T m (suc l)

head′ : ∀ {T m l} → CtxExt′ T m (suc l) → T (l + m)
head′ (t ∷ ts) = t

tail′ : ∀ {T m l} → CtxExt′ T m (suc l) → CtxExt′ T m l
tail′ (t ∷ ts) = ts

-- A map function that point-wise re-indexes and changes the entries
-- in a context.
map′ : ∀ {T₁ T₂ k m n} → (∀ l → T₁ (l + m) → T₂ (l + n)) →
       CtxExt′ T₁ m k → CtxExt′ T₂ n k
map′ f []            = []
map′ f (_∷_ {l} t Γ) = f l t ∷ map′ (λ l → f l) Γ

-- Conversions between the two representations.

module ConversionHelper where

  CtxExt⇒CtxExt′-helper : ∀ {T m n} → (Γ : CtxExt T m n) →
                          CtxExt′ T m (length Γ)
  CtxExt⇒CtxExt′-helper     []      = []
  CtxExt⇒CtxExt′-helper {T} (t ∷ Γ) =
    subst T (sym (length-idx Γ)) t ∷ CtxExt⇒CtxExt′-helper Γ

CtxExt⇒CtxExt′ : ∀ {T m l} → CtxExt T m (l + m) → CtxExt′ T m l
CtxExt⇒CtxExt′ Γ =
  subst (CtxExt′ _ _) (length-idx′ Γ) (CtxExt⇒CtxExt′-helper Γ)
  where open ConversionHelper

CtxExt′⇒CtxExt : ∀ {T m l} → CtxExt′ T m l → CtxExt T m (l + m)
CtxExt′⇒CtxExt []       = []
CtxExt′⇒CtxExt (t ∷ Γ′) = t ∷ CtxExt′⇒CtxExt Γ′

infixr 5 _′++_

-- A variant of concatenation where the prefix is given in the
-- alternative representation.
--
-- NOTE.  We could have defined this operation directly by recursion
-- on the prefix parameter Δ′ instead, but the following definition
-- works better with the definition of well-formed contexts in the
-- alternative representation (_⊢_wfCtx′) given in the module
-- WellFormedContext below.
_′++_ : ∀ {T k m n} → CtxExt′ T m n → CtxExt T k m → CtxExt T k (n + m)
Δ′ ′++ Γ = CtxExt′⇒CtxExt Δ′ ++ Γ

-- Operations on contexts that require weakening of types.
module WeakenOps {T} (extension : Extension T) where

  -- Weakening of types.
  open Extension extension public

  -- Convert a context extension to its vector representation.

  extToVec : ∀ {m n} → Vec (T m) m → CtxExt T m n → Vec (T n) n
  extToVec ts []      = ts
  extToVec ts (t ∷ Γ) = weaken t /∷ extToVec ts Γ

  extToVec′ : ∀ {k m n} → Vec (T m) k → CtxExt′ T m n →
              Vec (T (n + m)) (n + k)
  extToVec′ ts []      = ts
  extToVec′ ts (t ∷ Γ) = weaken t /∷ extToVec′ ts Γ

  -- Convert a context to its vector representation.
  toVec : ∀ {n} → Ctx T n → Vec (T n) n
  toVec = extToVec []

  -- Lookup the type of a variable in a context extension.

  extLookup : ∀ {m n} → Fin n → Vec (T m) m → CtxExt T m n → T n
  extLookup x ts Γ = Vec.lookup x (extToVec ts Γ)

  extLookup′ : ∀ {k m n} → Fin (n + k) → Vec (T m) k →
               CtxExt′ T m n → T (n + m)
  extLookup′ x ts Γ = Vec.lookup x (extToVec′ ts Γ)

  -- Lookup the type of a variable in a context.
  lookup : ∀ {n} → Fin n → Ctx T n → T n
  lookup x = extLookup x []

-- Operations on contexts that require substitutions in types.
module SubstOps {T T′}
                (application : Application T T′)
                (simple      : Simple T′)
                where

  open Application application public -- Application of T′ substitutions to Ts.
  open Simple      simple      public -- Simple T′ substitutions.

  -- Application of substitutions to context extensions.

  _E′/_ : ∀ {k m n} → CtxExt′ T m k → Sub T′ m n → CtxExt′ T n k
  Γ′ E′/ σ = map′ (λ l t → t / σ ↑⋆ l) Γ′

  _E/_ : ∀ {k m n} → CtxExt T m (k + m) → Sub T′ m n → CtxExt T n (k + n)
  _E/_ {k} Γ σ = CtxExt′⇒CtxExt (CtxExt⇒CtxExt′ {l = k} Γ E′/ σ)


------------------------------------------------------------------------
-- Abstract well-formed typing contexts and context extensions.
--
-- FIXME: maybe this should go into the Context.Properties module?

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
  infix  4 _wf _⊢_wfExt _⊢_wfExt′
  infixr 5 _∷_

  -- Well-formed typing contexts.
  data _wf : ∀ {n} → Ctx T n → Set where
    []  :                                              [] wf
    _∷_ : ∀ {n t} {Γ : Ctx T n} → Γ ⊢ t wf → Γ wf → t ∷ Γ wf

  -- Well-formed context extensions.
  data _⊢_wfExt {m} (Γ : Ctx T m) : ∀ {n} → CtxExt T m n → Set where
    []  : Γ ⊢ [] wfExt
    _∷_ : ∀ {n t} {Δ : CtxExt T m n} →
          (Δ ++ Γ) ⊢ t wf → Γ ⊢ Δ wfExt → Γ ⊢ t ∷ Δ wfExt

  _⊢_wfExt′ : ∀ {m n} → Ctx T m → CtxExt′ T m n → Set
  Γ ⊢ Δ′ wfExt′ = Γ ⊢ (CtxExt′⇒CtxExt Δ′) wfExt

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

    -- Convert a well-formed context to its All representation.
    toAll : ∀ {n} {Γ : Ctx T n} → Γ wf → All (λ t → Γ ⊢ t wf) (W.toVec Γ)
    toAll []            = []
    toAll (t-wf ∷ Γ-wf) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (toAll Γ-wf)

    -- Convert a well-formed context extension to its All representation.
    extToAll : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} →
               All (λ t → Γ ⊢ t wf) (W.toVec Γ) → Γ ⊢ Δ wfExt →
               All (λ a → (Δ ++ Γ) ⊢ a wf) (W.toVec (Δ ++ Γ))
    extToAll ts-wf []               = ts-wf
    extToAll ts-wf (t-wf ∷ Δ-wfExt) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (extToAll ts-wf Δ-wfExt)

    -- Lookup the well-formedness proof of a variable in a context.
    lookup : ∀ {n} {Γ : Ctx T n} (x : Fin n) → Γ wf → Γ ⊢ (W.lookup x Γ) wf
    lookup x = All.lookup x ∘ toAll

    -- Lookup the well-formedness proof of a variable in a context extension.
    extLookup : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} (x : Fin n) →
                All (λ t → Γ ⊢ t wf) (W.toVec Γ) → Γ ⊢ Δ wfExt →
                (Δ ++ Γ) ⊢ (W.lookup x (Δ ++ Γ)) wf
    extLookup x ts-wf = All.lookup x ∘ (extToAll ts-wf)

-- Trivial well-formedness.
--
-- This module provides a trivial well-formedness relation and the
-- corresponding trivially well-formed contexts.  This is useful when
-- implmenting typed substitutions on types that either lack or do not
-- necessitate a notion of well-formedness.
module ⊤-WellFormed {T} (extension : Extension T) where

  infix  4 _⊢_wf

  -- Trivial well-formedness.
  _⊢_wf : Wf T
  _ ⊢ _ wf = ⊤

  open WellFormedContext _⊢_wf public

  -- Trivial well-formedness of contexts.
  ctx-wf : ∀ {n} (Γ : Ctx T n) → Γ wf
  ctx-wf []      = []
  ctx-wf (a ∷ Γ) = tt ∷ ctx-wf Γ

  -- Trivial well-formedness of context extensions.
{--
  ctx-wfExt : ∀ {m n} (Δ : CtxExt T m n) {Γ : Ctx T m} → Γ ⊢ Δ wfExt
  ctx-wfExt []      = []
  ctx-wfExt (a ∷ Δ) = tt ∷ ctx-wfExt Δ

  ctx-wfExt′ : ∀ {m n} (Δ′ : CtxExt′ T m n) {Γ : Ctx T m} → Γ ⊢ Δ′ wfExt′
  ctx-wfExt′ Δ′ = ctx-wfExt (CtxExt′⇒CtxExt Δ′)
--}
  ctx-wfExt′ : ∀ {m n} (Δ′ : CtxExt′ T m n) {Γ : Ctx T m} → Γ ⊢ Δ′ wfExt′
  ctx-wfExt′ []      = []
  ctx-wfExt′ (a ∷ Δ) = tt ∷ ctx-wfExt′ Δ

  module ⊤-WfWeakenOps where

    wfWeakenOps : WfWeakenOps extension
    wfWeakenOps = record { wf-weaken = λ _ _ → tt }

    open WfWeakenOps public
