------------------------------------------------------------------------
-- Syntax of Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Syntax where

open import Algebra using (Monoid)
import Data.Context as Context
open import Data.Context.Properties
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.Extra using (Extension)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (proj₂)
open import Data.Vec as Vec using ([]; _∷_)
open import Data.List as List using (List; []; _∷_; foldl; map; _++_; _∷ʳ_)
open import Data.List.Properties using (++-monoid)
import Data.Maybe as Maybe
open import Function using (_∘_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open P.≡-Reasoning


----------------------------------------------------------------------
-- Raw terms: untyped syntax of terms, types and kinds.

-- NOTE 1.  Following the style of Pure Type System (PTS), we define
-- raw (i.e. untyped/unkinded) terms and types as a single syntactic
-- category rather than distinguishing them syntactically.
-- Concretely, we use the singe datatype Term to represent raw terms
-- and types.  This simplifies the definition of substitution in types
-- and terms as we don't need to distinguish between type and term
-- variables.  The difference between terms and types becomes manifest
-- only later in (sub-)typing and (sub-)kinding judgments.  However,
-- unlike PTS, we *do* treat kinds as a separate syntactic
-- category/datatype because there are no kind variables.  This
-- simplifies some definitions and proofs that rely on the syntactic
-- structure of kinds (e.g. kind simplification and related
-- properties).
--
-- NOTE 2.  We use well-scoped de Bruijn indexing to represent term
-- and type variables in raw terms/types.  The datatype `Term' is
-- indexed by the number of free variables its inhabitants may
-- contain, i.e. given a raw term
--
--    a : Term n
--
-- the set of "names" that may appear in `a' is
--
--   { 0, 1, ..., n-1 }.
--
-- Binders extend this set by increasing n by one for each fresh name
-- they introduce.  This ensures that raw terms are intrinsically
-- well-scoped.  This representation was adapted from previous Agda
-- formalizations of typed lambda calculi by Danielsson and others [1,
-- 2] and comes with some support in the Agda standard library.  See
-- Data.Fin.Substitution.Example for a simple example.
--
--  [1] N. A. Danielsson and T. Altenkirch, "Subtyping, Declaratively
--      An Exercise in Mixed Induction and Coinduction", Proc. MPC
--      2010.
--
--  [2] N. A. Danielsson, "Operational Semantics Using the Partiality
--      Monad", Proc. ICFP 2012.

module Syntax where

  infixl 9 _·_ _⊡_ _⊡∙_
  infixr 7 _⇒_ _⇒∙_
  infix  6 _⋯_

  -- Raw, T-dependent kinds with up to n free variables.

  data Kind (T : ℕ → Set) (n : ℕ) : Set where
    _⋯_ : (a b : T n)                         → Kind T n  -- interval
    Π   : (j : Kind T n) (k : Kind T (suc n)) → Kind T n  -- dependent arrow

  -- Raw terms and types with up to n free variables.
  --
  -- NOTE. The type instantiation operator _⊡_ should be considered
  -- specialized variant of the application operator _·_.  The reason
  -- for including a dedicated _⊡_ constructor is to distinguish term
  -- applications from type applications/instantiations in CBV
  -- reductions (see FOmegaInt.Reduction.Cbv).  Without the special
  -- treatment of type instantiation, CBV reduction would permit
  -- reduction of type arguments before contraction.  Not only is this
  -- counter to the usual CBV semantics for Fω (see e.g. TAPL p. 450),
  -- but it would require a proof of subject reduction (aka
  -- preservation) for kinding in order to prove preservation of
  -- typing even under CBV reduction.  By adopting the usual CBV
  -- semantics, this dependency can be avoided.  See
  -- FOmegaInt.Typing.Preservation for a proof of subject reduction
  -- for typing using the usual CBV semantics.

  data Term (n : ℕ) : Set where
    var : (x : Fin n)                          → Term n  -- variable
    ⊥   :                                        Term n  -- bottom (minimum)
    ⊤   :                                        Term n  -- top (maximum)
    Π   : (k : Kind Term n) (a : Term (suc n)) → Term n  -- universal quant.
    _⇒_ : (a b : Term n)                       → Term n  -- arrow
    Λ   : (k : Kind Term n) (a : Term (suc n)) → Term n  -- type abstraction
    ƛ   : (a : Term n)      (b : Term (suc n)) → Term n  -- term abstraction
    _⊡_ : (a b : Term n)                       → Term n  -- type instantiation
    _·_ : (a b : Term n)                       → Term n  -- term application

  -- A shorthand for the kind of proper types.

  * : ∀ {n} → Kind Term n
  * = ⊥ ⋯ ⊤

  infixl 9 _∙_

  -- Raw terms and types in spine form.
  --
  -- Spine form is an alternative representation of raw terms where
  -- the arguments of consecutive applications are grouped together
  -- into sequences of arguments called "spines".  This representation
  -- is better suited for the definition of "hereditary substitution"
  -- (see Syntax.HereditarySubstitution) and canonical kinding (see
  -- Kinding.Canonical).  The two representations are isomorphic, as
  -- witnessed by ⌜⌝∘⌞⌟-id and ⌞⌟∘⌜⌝-id below.
  --
  -- NOTE.  Below, we consider type instantiations (a ⊡ b) as heads
  -- rather than eliminations, despite the fact that, semantically,
  -- they are elimination forms.  However, for the purpose of
  -- hereditary substitution we will ignore their semantics and treat
  -- _⊡_ as an uninterpreted binary operation.  This is justified by
  -- the fact that *well-kinded* hereditary substitution is only
  -- defined on (well-kinded) types, in which _⊡_ cannot appear.
  --
  -- One may wonder: why include constructors for term-level forms
  -- such as ƛ or _⊡_ in this presentation of the syntax if it is only
  -- used to define type-level hereditary substitution?  The answer is
  -- that we often rely on the two presentations of the syntax being
  -- isomorphic to switch between them without loss of generality.  If
  -- we only included type formers, we could not prove this
  -- isomorphism.  Including the term formers thus adds a bit of
  -- overhead but simplifies things over all.

  mutual

    -- Eliminations are applications of (possibly empty) sequences of
    -- arguments to heads.

    data Elim (n : ℕ) : Set where
      _∙_ : (a : Head n) (as : Spine n) → Elim n  -- application

    -- Heads are those terms that are not eliminations.

    data Head (n : ℕ) : Set where
      var : (x : Fin n)                          → Head n  -- variable
      ⊥   :                                        Head n  -- bottom (minimum)
      ⊤   :                                        Head n  -- top (maximum)
      Π   : (k : Kind Elim n) (a : Elim (suc n)) → Head n  -- universal
      _⇒_ : (a b : Elim n)                       → Head n  -- arrow
      Λ   : (k : Kind Elim n) (a : Elim (suc n)) → Head n  -- type abstraction
      ƛ   : (a : Elim n)      (b : Elim (suc n)) → Head n  -- term abstraction
      _⊡_ : (a b : Elim n)                       → Head n  -- type inst.

    -- Spines are (possibly empty) sequences of eliminations.

    Spine : ℕ → Set
    Spine n = List (Elim n)

  -- Projections.

  headOf : ∀ {n} → Elim n → Head n
  headOf (a ∙ as) = a

  spineOf : ∀ {n} → Elim n → Spine n
  spineOf (a ∙ as) = as

  infixl 9 _⌜·⌝_ _⌞∙⌟_ _∙∙_

  -- Post-application of spines and eliminations to eliminations.

  _∙∙_ : ∀ {n} → Elim n → Spine n → Elim n
  a ∙ as ∙∙ bs = a ∙ (as ++ bs)

  _⌜·⌝_ : ∀ {n} → Elim n → Elim n → Elim n
  a ⌜·⌝ b = a ∙∙ (b ∷ [])

  -- Application of term sequences to terms.

  _⌞∙⌟_ : ∀ {n} → Term n → List (Term n) → Term n
  a ⌞∙⌟ as = foldl _·_ a as

  -- Shorthands for "unapplied" term/type constructors.

  var∙ : ∀ {n} → Fin n → Elim n
  var∙ x = var x ∙ []

  ⊥∙ : ∀ {n} → Elim n
  ⊥∙ = ⊥ ∙ []

  ⊤∙ : ∀ {n} → Elim n
  ⊤∙ = ⊤ ∙ []

  ∀∙ : ∀ {n} → Kind Elim n → Elim (suc n) → Elim n
  ∀∙ k a = Π k a ∙ []

  _⇒∙_ : ∀ {n} → Elim n → Elim n → Elim n
  a ⇒∙ b = (a ⇒ b) ∙ []

  Λ∙ : ∀ {n} → Kind Elim n → Elim (suc n) → Elim n
  Λ∙ k a = Λ k a ∙ []

  ƛ∙ : ∀ {n} → Elim n → Elim (suc n) → Elim n
  ƛ∙ a b = ƛ a b ∙ []

  _⊡∙_ : ∀ {n} → Elim n → Elim n → Elim n
  a ⊡∙ b = (a ⊡ b) ∙ []

  ⌜*⌝ : ∀ {n} → Kind Elim n
  ⌜*⌝ = ⊥∙ ⋯ ⊤∙

  -- Conversions between the two representations.

  mutual

    -- Turn raw eliminations into raw terms.

    ⌞_⌟ : ∀ {n} → Elim n → Term n
    ⌞ a ∙ as ⌟ = ⌞ a ⌟Hd ⌞∙⌟ ⌞ as ⌟Sp

    ⌞_⌟Kd : ∀ {n} → Kind Elim n → Kind Term n
    ⌞ a ⋯ b ⌟Kd = ⌞ a ⌟ ⋯ ⌞ b ⌟
    ⌞ Π j k ⌟Kd = Π ⌞ j ⌟Kd ⌞ k ⌟Kd

    ⌞_⌟Sp : ∀ {n} → Spine n → List (Term n)
    ⌞ []     ⌟Sp = []
    ⌞ a ∷ as ⌟Sp = ⌞ a ⌟ ∷ ⌞ as ⌟Sp

    ⌞_⌟Hd : ∀ {n} → Head n → Term n
    ⌞ var x ⌟Hd = var x
    ⌞ ⊥     ⌟Hd = ⊥
    ⌞ ⊤     ⌟Hd = ⊤
    ⌞ Π k a ⌟Hd = Π ⌞ k ⌟Kd ⌞ a ⌟
    ⌞ a ⇒ b ⌟Hd = ⌞ a ⌟ ⇒ ⌞ b ⌟
    ⌞ Λ k a ⌟Hd = Λ ⌞ k ⌟Kd ⌞ a ⌟
    ⌞ ƛ a b ⌟Hd = ƛ ⌞ a ⌟ ⌞ b ⌟
    ⌞ a ⊡ b ⌟Hd = ⌞ a ⌟ ⊡ ⌞ b ⌟

  mutual

    -- Turn raw terms into raw eliminations.

    ⌜_⌝ : ∀ {n} → Term n → Elim n
    ⌜ var x ⌝ = var x ∙ []
    ⌜ ⊥     ⌝ = ⊥∙
    ⌜ ⊤     ⌝ = ⊤∙
    ⌜ Π k a ⌝ = ∀∙ ⌜ k ⌝Kd ⌜ a ⌝
    ⌜ a ⇒ b ⌝ = ⌜ a ⌝ ⇒∙ ⌜ b ⌝
    ⌜ Λ k a ⌝ = Λ∙ ⌜ k ⌝Kd ⌜ a ⌝
    ⌜ ƛ a b ⌝ = ƛ∙ ⌜ a ⌝ ⌜ b ⌝
    ⌜ a ⊡ b ⌝ = ⌜ a ⌝ ⊡∙ ⌜ b ⌝
    ⌜ a · b ⌝ = ⌜ a ⌝ ⌜·⌝ ⌜ b ⌝

    ⌜_⌝Kd : ∀ {n} → Kind Term n → Kind Elim n
    ⌜ a ⋯ b ⌝Kd = ⌜ a ⌝ ⋯ ⌜ b ⌝
    ⌜ Π j k ⌝Kd = Π ⌜ j ⌝Kd ⌜ k ⌝Kd

  -- Shapes (aka simple kinds).

  data SKind : Set where
    ★   : SKind
    _⇒_ : SKind → SKind → SKind

  -- Kind simplification (aka erasure from kinds to shapes).

  ⌊_⌋ : ∀ {T n} → Kind T n → SKind
  ⌊ a ⋯ b ⌋ = ★
  ⌊ Π j k ⌋ = ⌊ j ⌋ ⇒ ⌊ k ⌋

  -- A wrapper for raw kind or type ascriptions.

  data KdOrTp (T : ℕ → Set) (n : ℕ) : Set where
    kd : Kind T n → KdOrTp T n
    tp : T n      → KdOrTp T n

  TermAsc = KdOrTp Term
  ElimAsc = KdOrTp Elim

  ⌞_⌟Asc : ∀ {n} → ElimAsc n → TermAsc n
  ⌞ kd k ⌟Asc = kd ⌞ k ⌟Kd
  ⌞ tp a ⌟Asc = tp ⌞ a ⌟

  ⌜_⌝Asc : ∀ {n} → TermAsc n → ElimAsc n
  ⌜ kd k ⌝Asc = kd ⌜ k ⌝Kd
  ⌜ tp a ⌝Asc = tp ⌜ a ⌝

open Syntax


----------------------------------------------------------------------
-- Some properties of raw terms and kinds

-- The kd constructor is injective.

kd-inj : ∀ {T n} {j k : Kind T n} → kd j ≡ kd k → j ≡ k
kd-inj refl = refl

-- Extensionality of eliminations.

∙-ext : ∀ {n} (a : Elim n) → headOf a ∙ spineOf a ≡ a
∙-ext (a ∙ as) = refl

-- The empty spine is a right unit of _∙∙_

∙∙-[] : ∀ {n} (a : Elim n) → a ∙∙ [] ≡ a
∙∙-[] (a ∙ as) = cong (a ∙_) (proj₂ identity as)
  where open Monoid (++-monoid (Elim _)) hiding (_∙_)

-- Spine application commutes with spine concatenation.

∙∙-++ : ∀ {n} (a : Elim n) bs cs → a ∙∙ bs ∙∙ cs ≡ a ∙∙ (bs ++ cs)
∙∙-++ (a ∙ as) bs cs = cong (a ∙_) (assoc as bs cs)
  where open Monoid (++-monoid (Elim _)) hiding (_∙_)

-- Spine application can be expressed as a left fold.

∙∙IsFold : ∀ {n} (a : Elim n) bs → a ∙∙ bs ≡ foldl _⌜·⌝_ a bs
∙∙IsFold (a ∙ as) []       = ∙∙-[] (a ∙ as)
∙∙IsFold (a ∙ as) (b ∷ bs) = begin
    a ∙ (as ++ b ∷ bs)
  ≡⟨ sym (∙∙-++ (a ∙ as) (b ∷ []) bs) ⟩
    a ∙ ((as ∷ʳ b) ++ bs)
  ≡⟨ ∙∙IsFold (a ∙ (as ∷ʳ b)) bs  ⟩
    foldl _⌜·⌝_ (a ∙ (as ∷ʳ b)) bs
  ∎

-- Conversion to raw terms commutes with (post-)application.

⌞⌟-· : ∀ {n} (a : Elim n) b → ⌞ a ⌜·⌝ b ⌟ ≡ ⌞ a ⌟ · ⌞ b ⌟
⌞⌟-· (a ∙ as) b = helper as b
  where
    helper : ∀ {n} {a : Term n} bs c →
             a ⌞∙⌟ ⌞ bs ∷ʳ c ⌟Sp ≡ a ⌞∙⌟ ⌞ bs ⌟Sp · ⌞ c ⌟
    helper []       c = refl
    helper (b ∷ bs) c = helper bs c

⌞⌟-∙∙ : ∀ {n} (a : Elim n) bs → ⌞ a ∙∙ bs ⌟ ≡ ⌞ a ⌟ ⌞∙⌟ ⌞ bs ⌟Sp
⌞⌟-∙∙ a []       = cong ⌞_⌟ (∙∙-[] a)
⌞⌟-∙∙ a (b ∷ bs) = begin
  ⌞ a ∙∙ (b ∷ bs) ⌟      ≡⟨ sym (cong ⌞_⌟ (∙∙-++ a (b ∷ []) bs)) ⟩
  ⌞ a ∙∙ (b ∷ []) ∙∙ bs ⌟          ≡⟨ ⌞⌟-∙∙ (a ∙∙ (b ∷ [])) bs ⟩
  ⌞ a ∙∙ (b ∷ []) ⌟ ⌞∙⌟ ⌞ bs ⌟Sp   ≡⟨ cong (_⌞∙⌟ ⌞ bs ⌟Sp) (⌞⌟-· a b) ⟩
  ⌞ a ⌟ · ⌞ b ⌟ ⌞∙⌟ ⌞ bs ⌟Sp  ∎

-- Conversion to eliminations commutes with spine application.

⌜⌝-∙ : ∀ {n} (a : Term n) bs → ⌜ a ⌞∙⌟ bs ⌝ ≡ ⌜ a ⌝ ∙∙ map ⌜_⌝ bs
⌜⌝-∙ a bs = begin
  ⌜ a ⌞∙⌟ bs ⌝                     ≡⟨ helper a bs ⟩
  foldl _⌜·⌝_ ⌜ a ⌝ (map ⌜_⌝ bs)   ≡⟨ sym (∙∙IsFold ⌜ a ⌝ (map ⌜_⌝ bs)) ⟩
  ⌜ a ⌝ ∙∙ map ⌜_⌝ bs              ∎
  where
    helper : ∀ {n} (a : Term n) bs →
             ⌜ a ⌞∙⌟ bs ⌝ ≡ foldl _⌜·⌝_ ⌜ a ⌝ (map ⌜_⌝ bs)
    helper a []       = refl
    helper a (b ∷ bs) = helper (a · b) bs

-- The two representations of raw terms are isomorphic.

mutual

  ⌞⌟∘⌜⌝-id : ∀ {n} (a : Term n) → ⌞ ⌜ a ⌝ ⌟ ≡ a
  ⌞⌟∘⌜⌝-id (var x) = refl
  ⌞⌟∘⌜⌝-id ⊥       = refl
  ⌞⌟∘⌜⌝-id ⊤       = refl
  ⌞⌟∘⌜⌝-id (Π k a) = cong₂ Π (⌞⌟Kd∘⌜⌝Kd-id k) (⌞⌟∘⌜⌝-id a)
  ⌞⌟∘⌜⌝-id (a ⇒ b) = cong₂ _⇒_ (⌞⌟∘⌜⌝-id a) (⌞⌟∘⌜⌝-id b)
  ⌞⌟∘⌜⌝-id (Λ k a) = cong₂ Λ (⌞⌟Kd∘⌜⌝Kd-id k) (⌞⌟∘⌜⌝-id a)
  ⌞⌟∘⌜⌝-id (ƛ a b) = cong₂ ƛ (⌞⌟∘⌜⌝-id a) (⌞⌟∘⌜⌝-id b)
  ⌞⌟∘⌜⌝-id (a ⊡ b) = cong₂ _⊡_ (⌞⌟∘⌜⌝-id a) (⌞⌟∘⌜⌝-id b)
  ⌞⌟∘⌜⌝-id (a · b) = begin
    ⌞ ⌜ a ⌝ ⌜·⌝ ⌜ b ⌝ ⌟     ≡⟨ ⌞⌟-· ⌜ a ⌝ ⌜ b ⌝ ⟩
    ⌞ ⌜ a ⌝ ⌟ · ⌞ ⌜ b ⌝ ⌟   ≡⟨ cong₂ _·_ (⌞⌟∘⌜⌝-id a) (⌞⌟∘⌜⌝-id b) ⟩
    a · b                   ∎

  ⌞⌟Kd∘⌜⌝Kd-id : ∀ {n} (k : Kind Term n) → ⌞ ⌜ k ⌝Kd ⌟Kd ≡ k
  ⌞⌟Kd∘⌜⌝Kd-id (a ⋯ b) = cong₂ _⋯_ (⌞⌟∘⌜⌝-id a) (⌞⌟∘⌜⌝-id b)
  ⌞⌟Kd∘⌜⌝Kd-id (Π j k) = cong₂ Π (⌞⌟Kd∘⌜⌝Kd-id j) (⌞⌟Kd∘⌜⌝Kd-id k)

mutual

  ⌜⌝∘⌞⌟-id : ∀ {n} (a : Elim n) → ⌜ ⌞ a ⌟ ⌝ ≡ a
  ⌜⌝∘⌞⌟-id (a ∙ bs) = begin
      ⌜ ⌞ a ⌟Hd ⌞∙⌟ ⌞ bs ⌟Sp ⌝
    ≡⟨ ⌜⌝-∙ ⌞ a ⌟Hd ⌞ bs ⌟Sp ⟩
      ⌜ ⌞ a ⌟Hd ⌝ ∙∙ map ⌜_⌝ ⌞ bs ⌟Sp
    ≡⟨ cong₂ _∙∙_ (⌜⌝∘⌞⌟Hd-∙-[] a) (map-⌜⌝∘⌞⌟Sp-id bs) ⟩
      a ∙ [] ∙∙ bs
    ∎

  map-⌜⌝∘⌞⌟Sp-id : ∀ {n} (as : Spine n) → map ⌜_⌝ ⌞ as ⌟Sp ≡ as
  map-⌜⌝∘⌞⌟Sp-id []       = refl
  map-⌜⌝∘⌞⌟Sp-id (a ∷ as) = cong₂ _∷_ (⌜⌝∘⌞⌟-id a) (map-⌜⌝∘⌞⌟Sp-id as)

  ⌜⌝∘⌞⌟Hd-∙-[] : ∀ {n} (a : Head n) → ⌜ ⌞ a ⌟Hd ⌝ ≡ a ∙ []
  ⌜⌝∘⌞⌟Hd-∙-[] (var x) = refl
  ⌜⌝∘⌞⌟Hd-∙-[] ⊥       = refl
  ⌜⌝∘⌞⌟Hd-∙-[] ⊤       = refl
  ⌜⌝∘⌞⌟Hd-∙-[] (Π k a) = cong₂ ∀∙ (⌜⌝Kd∘⌞⌟Kd-id k) (⌜⌝∘⌞⌟-id a)
  ⌜⌝∘⌞⌟Hd-∙-[] (a ⇒ b) = cong₂ _⇒∙_ (⌜⌝∘⌞⌟-id a) (⌜⌝∘⌞⌟-id b)
  ⌜⌝∘⌞⌟Hd-∙-[] (Λ k a) = cong₂ Λ∙ (⌜⌝Kd∘⌞⌟Kd-id k) (⌜⌝∘⌞⌟-id a)
  ⌜⌝∘⌞⌟Hd-∙-[] (ƛ a b) = cong₂ ƛ∙ (⌜⌝∘⌞⌟-id a) (⌜⌝∘⌞⌟-id b)
  ⌜⌝∘⌞⌟Hd-∙-[] (a ⊡ b) = cong₂ _⊡∙_ (⌜⌝∘⌞⌟-id a) (⌜⌝∘⌞⌟-id b)

  ⌜⌝Kd∘⌞⌟Kd-id : ∀ {n} (k : Kind Elim n) → ⌜ ⌞ k ⌟Kd ⌝Kd ≡ k
  ⌜⌝Kd∘⌞⌟Kd-id (a ⋯ b) = cong₂ _⋯_ (⌜⌝∘⌞⌟-id a) (⌜⌝∘⌞⌟-id b)
  ⌜⌝Kd∘⌞⌟Kd-id (Π j k) = cong₂ Π   (⌜⌝Kd∘⌞⌟Kd-id j) (⌜⌝Kd∘⌞⌟Kd-id k)

-- Simplified kinds are stable under conversions of term
-- representation.

⌊⌋-⌜⌝Kd : ∀ {n} (k : Kind Term n) → ⌊ ⌜ k ⌝Kd ⌋ ≡ ⌊ k ⌋
⌊⌋-⌜⌝Kd (a ⋯ b) = refl
⌊⌋-⌜⌝Kd (Π j k) = cong₂ _⇒_ (⌊⌋-⌜⌝Kd j) (⌊⌋-⌜⌝Kd k)

⌊⌋-⌞⌟Kd : ∀ {n} (k : Kind Elim n) → ⌊ ⌞ k ⌟Kd ⌋ ≡ ⌊ k ⌋
⌊⌋-⌞⌟Kd (a ⋯ b) = refl
⌊⌋-⌞⌟Kd (Π j k) = cong₂ _⇒_ (⌊⌋-⌞⌟Kd j) (⌊⌋-⌞⌟Kd k)


----------------------------------------------------------------------
-- Substitutions in raw terms
--
-- We use an intrinsically well-scoped variant of simultaneous
-- substitutions inspired by McBride's technique for defining
-- type-preserving substitutions [3].  These come with some support in
-- the Agda standard library.  In particular, the standard library
-- provides generic proofs for a plethora of standard untyped
-- substitution lemmas (e.g. substitutions commute, identity
-- substitutions vanish, etc.) which are easy but tedious to prove
-- (see the Data.Fin.Substitution.Lemmas module).  By using this
-- substitution framework, we get those lemmas for "free" (we still
-- need to provide some basic lemmas to bootstrap everything).
--
-- To use the standard framework, we must follow the following four
-- steps.
--
--  1. We define an application function `t / σ' of generic untyped
--     substitutions `σ' to well-scoped untyped terms `t'.  Generic
--     substitutions are defined over an abstract type `T', which will
--     later represent variables (to encode renamings) or terms (to
--     encode actual substitutions).  Hence the definition of
--     application must be parametrized over some abstract operations
--     on such substitutions (lifting, weakening, etc.) to be defined
--     later.  Concrete instances of these operations are collected in
--     the record `Lift' (see e.g. `SubstApp' module below).
--
--     Along with application, we define a few lemmas to be used in
--     step 4.  (They express the fact that application of
--     (multi-)substitutions is compositional w.r.t. the various
--     syntactic forms.)
--
--  2. Application is instantiated with `T = Fin' to obtain
--     well-scoped renamings, i.e. substitutions of variables in
--     terms.  The standard library provides a predefined instance of
--     `Lift Fin Term' to this end.
--
--  3. Using well-scoped renamings, an instance of `Lift Term Term' is
--     defined, and application is instantiated to concrete
--     substitutions of terms in terms.
--
--  4. Using the generic lemmas defined in step 1, many helpful
--     derived substitution lemmas are instantiated.
--     (E.g. "substitutions commute", "identity substitutions vanish",
--     etc.)
--
-- Most of the work is done in step 1, while steps 2-3 consists mostly
-- in calls to the substitution API of the Agda standard library.
--
--  [3] C. McBride, "Type-Preserving Renaming and Substitution"
--      http://strictlypositive.org/ren-sub.pdf

-- Application of generic substitutions lifted to type and kind
-- ascriptions.

module KdOrTpSubstApp {T T′ : ℕ → Set} (simple : Simple T)
                      (kdApp : Application (Kind T′) T)
                      (tpApp : Application T′ T) where
  open Simple simple
  open Application kdApp renaming (_/_ to _Kd/_; _/✶_ to _Kd/✶_)
  open Application tpApp renaming (_/_ to _Tp/_; _/✶_ to _Tp/✶_)

  infixl 8 _/_

  -- Apply a substitution to a kind or type ascription.

  _/_ : ∀ {m n} → KdOrTp T′ m → Sub T m n → KdOrTp T′ n
  (kd k) / σ = kd (k Kd/ σ)
  (tp a) / σ = tp (a Tp/ σ)

  open Application (record { _/_ = _/_     }) public hiding (_/_)

  -- Some helper lemmas about applying sequences of substitutions (to
  -- be used for instantiating TermSubstLemmas).

  -- Substitutions in kind ascriptions are compositional.

  kd-/✶-↑✶ : ∀ k {m n j} (σs : Subs T m n) →
             (kd j) /✶ σs ↑✶ k ≡ kd (j Kd/✶ σs ↑✶ k)
  kd-/✶-↑✶ k ε        = refl
  kd-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (kd-/✶-↑✶ k σs) refl

  -- Substitutions in type ascriptions are compositional.

  tp-/✶-↑✶ : ∀ k {m n a} (σs : Subs T m n) →
             (tp a) /✶ σs ↑✶ k ≡ tp (a Tp/✶ σs ↑✶ k)
  tp-/✶-↑✶ k ε        = refl
  tp-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (tp-/✶-↑✶ k σs) refl

-- Application of generic substitutions to terms

module SubstApp {T : ℕ → Set} (l : Lift T Term) where
  open Lift l hiding (var)

  infixl 8 _/_ _Kind/_ _Elim/_ _Head/_ _//_ _Kind′/_

  mutual

    -- Apply a substitution to a raw term/type.

    _/_ : ∀ {m n} → Term m → Sub T m n → Term n
    var x   / σ = lift (Vec.lookup σ x)
    ⊥       / σ = ⊥
    ⊤       / σ = ⊤
    Π k a   / σ = Π (k Kind/ σ) (a / σ ↑)
    (a ⇒ b) / σ = (a / σ) ⇒ (b / σ)
    Λ k a   / σ = Λ (k Kind/ σ) (a / σ ↑)
    ƛ a b   / σ = ƛ (a / σ) (b / σ ↑)
    a · b   / σ = (a / σ) · (b / σ)
    a ⊡ b   / σ = (a / σ) ⊡ (b / σ)

    -- Apply a substitution to a kind.

    _Kind/_ : ∀ {m n} → Kind Term m → Sub T m n → Kind Term n
    (a ⋯ b) Kind/ σ = (a / σ) ⋯ (b / σ)
    Π j k   Kind/ σ = Π (j Kind/ σ) (k Kind/ σ ↑)

  mutual

    -- Apply a substitution to an elimination.

    _Elim/_ : ∀ {m n} → Elim m → Sub T m n → Elim n
    a ∙ as Elim/ σ = (a Head/ σ) ∙∙ (as // σ)

    -- Apply a substitution to a head.

    _Head/_ : ∀ {m n} → Head m → Sub T m n → Elim n
    var x   Head/ σ = ⌜ lift (Vec.lookup σ x) ⌝
    ⊥       Head/ σ = ⊥∙
    ⊤       Head/ σ = ⊤∙
    Π k a   Head/ σ = ∀∙ (k Kind′/ σ) (a Elim/ σ ↑)
    (a ⇒ b) Head/ σ = (a Elim/ σ) ⇒∙ (b Elim/ σ)
    Λ k a   Head/ σ = Λ∙ (k Kind′/ σ) (a Elim/ σ ↑)
    ƛ a b   Head/ σ = ƛ∙ (a Elim/ σ) (b Elim/ σ ↑)
    a ⊡ b   Head/ σ = (a Elim/ σ) ⊡∙ (b Elim/ σ)

    -- Apply a substitution to a spine.

    _//_ : ∀ {m n} → Spine m → Sub T m n → Spine n
    []       // σ = []
    (a ∷ as) // σ = a Elim/ σ ∷ as // σ

    -- Apply a substitution to a (elimination-based) kind.
    _Kind′/_ : ∀ {m n} → Kind Elim m → Sub T m n → Kind Elim n
    (a ⋯ b) Kind′/ σ = (a Elim/ σ) ⋯ (b Elim/ σ)
    Π j k   Kind′/ σ = Π (j Kind′/ σ) (k Kind′/ σ ↑)

  private
    appTerm  = record { _/_ = _/_      }
    appKind  = record { _/_ = _Kind/_  }
    appElim  = record { _/_ = _Elim/_  }
    appKind′ = record { _/_ = _Kind′/_ }

  -- Some helper lemmas about applying sequences of substitutions (to
  -- be used for instantiating TermSubstLemmas).

  open Application appTerm hiding (_/_)
  open Application appKind using () renaming (_/✶_ to _Kind/✶_)

  -- The bottom and top types are invariant under substitution.

  ⊥-/✶-↑✶ : ∀ k {m n} (σs : Subs T m n) → ⊥ /✶ σs ↑✶ k ≡ ⊥
  ⊥-/✶-↑✶ k ε        = refl
  ⊥-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (⊥-/✶-↑✶ k σs) refl

  ⊤-/✶-↑✶ : ∀ k {m n} (σs : Subs T m n) → ⊤ /✶ σs ↑✶ k ≡ ⊤
  ⊤-/✶-↑✶ k ε        = refl
  ⊤-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (⊤-/✶-↑✶ k σs) refl

  -- Substitutions in the remaining term and type formers are
  -- compositional.
  
  Π-/✶-↑✶ : ∀ k {m n j a} (σs : Subs T m n) →
            (Π j a) /✶ σs ↑✶ k ≡ Π (j Kind/✶ σs ↑✶ k) (a /✶ σs ↑✶ suc k)
  Π-/✶-↑✶ k ε        = refl
  Π-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (Π-/✶-↑✶ k σs) refl

  ⇒-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
            (a ⇒ b) /✶ σs ↑✶ k ≡ (a /✶ σs ↑✶ k) ⇒ (b /✶ σs ↑✶ k)
  ⇒-/✶-↑✶ k ε        = refl
  ⇒-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (⇒-/✶-↑✶ k σs) refl

  Λ-/✶-↑✶ : ∀ k {m n j a} (σs : Subs T m n) →
            (Λ j a) /✶ σs ↑✶ k ≡ Λ (j Kind/✶ σs ↑✶ k) (a /✶ σs ↑✶ suc k)
  Λ-/✶-↑✶ k ε        = refl
  Λ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (Λ-/✶-↑✶ k σs) refl

  ƛ-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
            (ƛ a b) /✶ σs ↑✶ k ≡ ƛ (a /✶ σs ↑✶ k) (b /✶ σs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (ƛ-/✶-↑✶ k σs) refl

  ·-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
            (a · b) /✶ σs ↑✶ k ≡ (a /✶ σs ↑✶ k) · (b /✶ σs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (·-/✶-↑✶ k σs) refl

  ⊡-/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
            (a ⊡ b) /✶ σs ↑✶ k ≡ (a /✶ σs ↑✶ k) ⊡ (b /✶ σs ↑✶ k)
  ⊡-/✶-↑✶ k ε        = refl
  ⊡-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (⊡-/✶-↑✶ k σs) refl

  -- Substitutions in the kind formers are compositional.

  Π-Kind/✶-↑✶ : ∀ k {m n j l} (σs : Subs T m n) →
            (Π j l) Kind/✶ σs ↑✶ k ≡
              Π (j Kind/✶ σs ↑✶ k) (l Kind/✶ σs ↑✶ (suc k))
  Π-Kind/✶-↑✶ k ε        = refl
  Π-Kind/✶-↑✶ k (σ ◅ σs) = cong₂ _Kind/_ (Π-Kind/✶-↑✶ k σs) refl

  ⋯-Kind/✶-↑✶ : ∀ k {m n a b} (σs : Subs T m n) →
            (a ⋯ b) Kind/✶ σs ↑✶ k ≡ (a /✶ σs ↑✶ k) ⋯ (b /✶ σs ↑✶ k)
  ⋯-Kind/✶-↑✶ k ε        = refl
  ⋯-Kind/✶-↑✶ k (σ ◅ σs) = cong₂ _Kind/_ (⋯-Kind/✶-↑✶ k σs) refl

  -- Application of substitutions commutes with concatenation of spines.

  ++-// : ∀ {m n} (as bs : Spine m) {σ : Sub T m n} →
         (as ++ bs) // σ ≡ as // σ ++ bs // σ
  ++-// []       bs = refl
  ++-// (a ∷ as) bs = cong (a Elim/ _ ∷_) (++-// as bs)

  -- Application of substitutions commutes application of spines and
  -- eliminations.

  ∙∙-/ : ∀ {m n} a (as : Spine m) {σ : Sub T m n} →
         a ∙∙ as Elim/ σ ≡ (a Elim/ σ) ∙∙ (as // σ)
  ∙∙-/ (a ∙ as) bs = begin
      (a Head/ _) ∙∙ ((as ++ bs) // _)
    ≡⟨ cong (_ ∙∙_) (++-// as bs) ⟩
      (a Head/ _) ∙∙ (as // _ ++ bs // _)
    ≡⟨ sym (∙∙-++ _ (as // _) (bs // _)) ⟩
      (a Head/ _) ∙∙ (as // _) ∙∙ (bs // _)
    ∎

  ⌜·⌝-/ : ∀ {m n} (a b : Elim m) {σ : Sub T m n} →
          a ⌜·⌝ b Elim/ σ ≡ (a Elim/ σ) ⌜·⌝ (b Elim/ σ)
  ⌜·⌝-/ (a ∙ as) b {σ} = begin
      (a Head/ σ) ∙∙ ((as ∷ʳ b) // σ)
    ≡⟨ cong ((a Head/ σ) ∙∙_) (++-// as (b ∷ [])) ⟩
      (a Head/ σ) ∙∙ (as // σ ++ (b ∷ []) // σ)
    ≡⟨ sym (∙∙-++ (a Head/ σ) (as // σ) ((b ∷ []) // σ)) ⟩
      (a Head/ σ) ∙∙ (as // σ) ∙∙ ((b ∷ []) // σ)
    ≡⟨ ∙∙IsFold ((a Head/ σ) ∙∙ (as // σ)) ((b ∷ []) // σ) ⟩
      (a Head/ σ) ∙∙ (as // σ) ⌜·⌝ (b Elim/ σ)
    ∎

  -- Application of substitutions commutes with the conversions.

  mutual

    ⌜⌝-/ : ∀ {m n} a {σ : Sub T m n} → ⌜ a / σ ⌝ ≡ ⌜ a ⌝ Elim/ σ
    ⌜⌝-/ (var x) = sym (∙∙-[] _)
    ⌜⌝-/ ⊥       = refl
    ⌜⌝-/ ⊤       = refl
    ⌜⌝-/ (Π k a) = cong₂ ∀∙ (⌜⌝Kd-/ k) (⌜⌝-/ a)
    ⌜⌝-/ (a ⇒ b) = cong₂ _⇒∙_ (⌜⌝-/ a) (⌜⌝-/ b)
    ⌜⌝-/ (Λ k a) = cong₂ Λ∙ (⌜⌝Kd-/ k) (⌜⌝-/ a)
    ⌜⌝-/ (ƛ a b) = cong₂ ƛ∙ (⌜⌝-/ a) (⌜⌝-/ b)
    ⌜⌝-/ (a · b) {σ} = begin
      ⌜ a / σ ⌝ ⌜·⌝ ⌜ b / σ ⌝               ≡⟨ cong₂ _⌜·⌝_ (⌜⌝-/ a) (⌜⌝-/ b) ⟩
      (⌜ a ⌝ Elim/ σ) ⌜·⌝ (⌜ b ⌝ Elim/ σ)   ≡⟨ sym (⌜·⌝-/ ⌜ a ⌝ ⌜ b ⌝) ⟩
      ⌜ a ⌝ ⌜·⌝ ⌜ b ⌝ Elim/ σ               ∎
    ⌜⌝-/ (a ⊡ b) = cong₂ _⊡∙_ (⌜⌝-/ a) (⌜⌝-/ b)

    ⌜⌝Kd-/ : ∀ {m n} k {σ : Sub T m n} → ⌜ k Kind/ σ ⌝Kd ≡ ⌜ k ⌝Kd Kind′/ σ
    ⌜⌝Kd-/ (a ⋯ b) = cong₂ _⋯_ (⌜⌝-/ a) (⌜⌝-/ b)
    ⌜⌝Kd-/ (Π j k) = cong₂ Π (⌜⌝Kd-/ j) (⌜⌝Kd-/ k)

  ⌞⌟-/ : ∀ {m n} a {σ : Sub T m n} → ⌞ a Elim/ σ ⌟ ≡ ⌞ a ⌟ / σ
  ⌞⌟-/ a {σ} = begin
    ⌞ a         Elim/ σ ⌟   ≡⟨ cong (⌞_⌟ ∘ (_Elim/ σ)) (sym (⌜⌝∘⌞⌟-id a)) ⟩
    ⌞ ⌜ ⌞ a ⌟ ⌝ Elim/ σ ⌟   ≡⟨ cong ⌞_⌟ (sym (⌜⌝-/ ⌞ a ⌟)) ⟩
    ⌞ ⌜ ⌞ a ⌟ / σ     ⌝ ⌟   ≡⟨ ⌞⌟∘⌜⌝-id (⌞ a ⌟ / σ) ⟩
        ⌞ a ⌟ / σ       ∎

  ⌞⌟Kd-/ : ∀ {m n} k {σ : Sub T m n} → ⌞ k Kind′/ σ ⌟Kd ≡ ⌞ k ⌟Kd Kind/ σ
  ⌞⌟Kd-/ (a ⋯ b) = cong₂ _⋯_ (⌞⌟-/ a) (⌞⌟-/ b)
  ⌞⌟Kd-/ (Π j k) = cong₂ Π (⌞⌟Kd-/ j) (⌞⌟Kd-/ k)

  open Application appElim  using () renaming (_/✶_ to _Elim/✶_)
  open Application appKind′ using () renaming (_/✶_ to _Kind′/✶_)

  -- Application of multiple substitutions commutes with conversion to
  -- eliminations.

  ⌜⌝-/✶-↑✶ : ∀ k {m n a} (σs : Subs T m n) →
             ⌜ a /✶ σs ↑✶ k ⌝ ≡ ⌜ a ⌝ Elim/✶ σs ↑✶ k
  ⌜⌝-/✶-↑✶ k ε        = refl
  ⌜⌝-/✶-↑✶ k (σ ◅ σs) = begin
    ⌜ _ /✶ (σ ◅ σs) ↑✶ k ⌝          ≡⟨ ⌜⌝-/ (_ /✶ σs ↑✶ k) ⟩
    ⌜ _ /✶ σs ↑✶ k ⌝ Elim/ σ ↑⋆ k   ≡⟨ cong (_Elim/ _) (⌜⌝-/✶-↑✶ k σs) ⟩
    _ Elim/✶ (σ ◅ σs) ↑✶ k          ∎

  ⌜⌝Kd-/✶-↑✶ : ∀ k {m n j} (σs : Subs T m n) →
               ⌜ j Kind/✶ σs ↑✶ k ⌝Kd ≡ ⌜ j ⌝Kd Kind′/✶ σs ↑✶ k
  ⌜⌝Kd-/✶-↑✶ k ε        = refl
  ⌜⌝Kd-/✶-↑✶ k (σ ◅ σs) = begin
      ⌜ _ Kind/✶ (σ ◅ σs) ↑✶ k ⌝Kd
    ≡⟨ ⌜⌝Kd-/ (_ Kind/✶ σs ↑✶ k) ⟩
      ⌜ _ Kind/✶ σs ↑✶ k ⌝Kd Kind′/ σ ↑⋆ k
    ≡⟨ cong (_Kind′/ _) (⌜⌝Kd-/✶-↑✶ k σs) ⟩
      _ Kind′/✶ (σ ◅ σs) ↑✶ k
    ∎

  -- Simplified kinds are stable under application of substitutions.

  ⌊⌋-Kind/ : ∀ {m n} (k : Kind Term m) {σ : Sub T m n} → ⌊ k Kind/ σ ⌋ ≡ ⌊ k ⌋
  ⌊⌋-Kind/ (a ⋯ b) = refl
  ⌊⌋-Kind/ (Π j k) = cong₂ _⇒_ (⌊⌋-Kind/ j) (⌊⌋-Kind/ k)

  ⌊⌋-Kind′/ : ∀ {m n} (k : Kind Elim m) {σ : Sub T m n} →
              ⌊ k Kind′/ σ ⌋ ≡ ⌊ k ⌋
  ⌊⌋-Kind′/ (a ⋯ b) = refl
  ⌊⌋-Kind′/ (Π j k) = cong₂ _⇒_ (⌊⌋-Kind′/ j) (⌊⌋-Kind′/ k)

  -- Application of substitutions to type and kind ascriptions.

  open KdOrTpSubstApp simple appKind  appTerm public using ()
    renaming (_/_ to _TermAsc/_)
  open KdOrTpSubstApp simple appKind′ appElim public using ()
    renaming (_/_ to _ElimAsc/_)

-- Substitutions in terms and associated lemmas.

module Substitution where

  -- Term substitutions.

  termSubst : TermSubst Term
  termSubst = record { var = var; app = SubstApp._/_ }

  -- Variable substitutions (renamings) in heads.
  --
  -- NOTE. The special treatment of heads here reflects the fact that
  -- the structure of heads is preserved by renamings but not by
  -- general term substitutions.

  module HeadRenamings where
    open Simple VarSubst.simple hiding (var)
    open SubstApp (TermSubst.varLift termSubst)

    infixl 8 _Head/Var_

    _Head/Var_ : ∀ {m n} → Head m → Sub Fin m n → Head n
    var x   Head/Var σ = var (Vec.lookup σ x)
    ⊥       Head/Var σ = ⊥
    ⊤       Head/Var σ = ⊤
    Π k a   Head/Var σ = Π (k Kind′/ σ) (a Elim/ σ ↑)
    (a ⇒ b) Head/Var σ = (a Elim/ σ) ⇒ (b Elim/ σ)
    Λ k a   Head/Var σ = Λ (k Kind′/ σ) (a Elim/ σ ↑)
    ƛ a b   Head/Var σ = ƛ (a Elim/ σ) (b Elim/ σ ↑)
    (a ⊡ b) Head/Var σ = (a Elim/ σ) ⊡ (b Elim/ σ)

    -- A lemma relating the above definition of application to the
    -- previous ones.

    Head/Var-∙ : ∀ {m n} {σ : Sub Fin m n} a → (a Head/Var σ) ∙ [] ≡ a Head/ σ
    Head/Var-∙ (var x) = refl
    Head/Var-∙ ⊥       = refl
    Head/Var-∙ ⊤       = refl
    Head/Var-∙ (Π k a) = refl
    Head/Var-∙ (a ⇒ b) = refl
    Head/Var-∙ (Λ k a) = refl
    Head/Var-∙ (ƛ a b) = refl
    Head/Var-∙ (a ⊡ b) = refl

    headOf-Head/Var : ∀ {m n} {σ : Sub Fin m n} a →
                      a Head/Var σ ≡ headOf (a Head/ σ)
    headOf-Head/Var a = cong headOf (Head/Var-∙ a)

    Elim/Var-Head/Var : ∀ {m n} {σ : Sub Fin m n} a →
                        a ∙ [] Elim/ σ ≡ (a Head/Var σ) ∙ []
    Elim/Var-Head/Var {σ = σ} a = begin
      a ∙ [] Elim/ σ        ≡⟨ ∙∙-[] (a Head/ σ) ⟩
      a Head/ σ             ≡⟨ sym (Head/Var-∙ a) ⟩
      (a Head/Var σ) ∙ []   ∎

  open HeadRenamings public

  -- Lemmas relating application of sequences of generic substitutions
  -- lifted to any number of additional variables.
  --
  -- Using these generic lemmas, we can instantiate the record
  -- Data.Fin.Substitution.Lemmas.TermLemmas below, which gives access
  -- to a number of useful (derived) lemmas about path substitutions.

  module Lemmas {T₁ T₂ : ℕ → Set}
                {lift₁ : Lift T₁ Term} {lift₂ : Lift T₂ Term} where
    open SubstApp
    open Lift lift₁ using () renaming (_↑✶_ to _↑✶₁_)
    open Lift lift₂ using () renaming (_↑✶_ to _↑✶₂_)
    open Application (record { _/_ = SubstApp._/_ lift₁ }) using ()
      renaming (_/✶_ to _/✶₁_)
    open Application (record { _/_ = SubstApp._/_ lift₂ }) using ()
      renaming (_/✶_ to _/✶₂_)
    open Application (record { _/_ = SubstApp._Kind/_ lift₁ }) using ()
      renaming (_/✶_ to _Kind/✶₁_)
    open Application (record { _/_ = SubstApp._Kind/_ lift₂ }) using ()
      renaming (_/✶_ to _Kind/✶₂_)

    -- Sequences of (lifted) T₁ and T₂-substitutions are equivalent
    -- when applied to raw terms/types/kinds if they are equivalent
    -- when applied to variables.

    mutual

      /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                (∀ k x → var x /✶₁ σs₁ ↑✶₁ k ≡ var x /✶₂ σs₂ ↑✶₂ k) →
                 ∀ k a → a     /✶₁ σs₁ ↑✶₁ k ≡ a     /✶₂ σs₂ ↑✶₂ k
      /✶-↑✶ σs₁ σs₂ hyp k (var x) = hyp k x
      /✶-↑✶ σs₁ σs₂ hyp k ⊥ = begin
        ⊥ /✶₁ σs₁ ↑✶₁ k   ≡⟨ ⊥-/✶-↑✶ _ k σs₁ ⟩
        ⊥                 ≡⟨ sym (⊥-/✶-↑✶ _ k σs₂) ⟩
        ⊥ /✶₂ σs₂ ↑✶₂ k   ∎
      /✶-↑✶ σs₁ σs₂ hyp k ⊤ = begin
        ⊤ /✶₁ σs₁ ↑✶₁ k   ≡⟨ ⊤-/✶-↑✶ _ k σs₁ ⟩
        ⊤                 ≡⟨ sym (⊤-/✶-↑✶ _ k σs₂) ⟩
        ⊤ /✶₂ σs₂ ↑✶₂ k   ∎
      /✶-↑✶ σs₁ σs₂ hyp k (Π j a) = begin
          (Π j a) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ Π-/✶-↑✶ _ k σs₁ ⟩
          Π (j Kind/✶₁ σs₁ ↑✶₁ k) (a /✶₁ σs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ Π (Kind/✶-↑✶ σs₁ σs₂ hyp k j) (/✶-↑✶ σs₁ σs₂ hyp (suc k) a) ⟩
          Π (j Kind/✶₂ σs₂ ↑✶₂ k) (a /✶₂ σs₂ ↑✶₂ suc k)
        ≡⟨ sym (Π-/✶-↑✶ _ k σs₂) ⟩
          (Π j a) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (a ⇒ b) = begin
          (a ⇒ b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ ⇒-/✶-↑✶ _ k σs₁ ⟩
          (a /✶₁ σs₁ ↑✶₁ k) ⇒ (b /✶₁ σs₁ ↑✶₁ k)
        ≡⟨ cong₂ _⇒_ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp k b) ⟩
          (a /✶₂ σs₂ ↑✶₂ k) ⇒ (b /✶₂ σs₂ ↑✶₂ k)
        ≡⟨ sym (⇒-/✶-↑✶ _ k σs₂) ⟩
          (a ⇒ b) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (Λ j a) = begin
          (Λ j a) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ Λ-/✶-↑✶ _ k σs₁ ⟩
          Λ (j Kind/✶₁ σs₁ ↑✶₁ k) (a /✶₁ σs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ Λ (Kind/✶-↑✶ σs₁ σs₂ hyp k j) (/✶-↑✶ σs₁ σs₂ hyp (suc k) a) ⟩
          Λ (j Kind/✶₂ σs₂ ↑✶₂ k) (a /✶₂ σs₂ ↑✶₂ suc k)
        ≡⟨ sym (Λ-/✶-↑✶ _ k σs₂) ⟩
          (Λ j a) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (ƛ a b) = begin
          (ƛ a b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ ƛ-/✶-↑✶ _ k σs₁ ⟩
          ƛ (a /✶₁ σs₁ ↑✶₁ k) (b /✶₁ σs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ ƛ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp (suc k) b) ⟩
          ƛ (a /✶₂ σs₂ ↑✶₂ k) (b /✶₂ σs₂ ↑✶₂ suc k)
        ≡⟨ sym (ƛ-/✶-↑✶ _ k σs₂) ⟩
          (ƛ a b) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (a · b) = begin
          (a · b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ ·-/✶-↑✶ _ k σs₁ ⟩
          (a /✶₁ σs₁ ↑✶₁ k) · (b /✶₁ σs₁ ↑✶₁ k)
        ≡⟨ cong₂ _·_ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp k b) ⟩
          (a /✶₂ σs₂ ↑✶₂ k) · (b /✶₂ σs₂ ↑✶₂ k)
        ≡⟨ sym (·-/✶-↑✶ _ k σs₂) ⟩
          (a · b) /✶₂ σs₂ ↑✶₂ k
        ∎
      /✶-↑✶ σs₁ σs₂ hyp k (a ⊡ b) = begin
          (a ⊡ b) /✶₁ σs₁ ↑✶₁ k
        ≡⟨ ⊡-/✶-↑✶ _ k σs₁ ⟩
          (a /✶₁ σs₁ ↑✶₁ k) ⊡ (b /✶₁ σs₁ ↑✶₁ k)
        ≡⟨ cong₂ _⊡_ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp k b) ⟩
          (a /✶₂ σs₂ ↑✶₂ k) ⊡ (b /✶₂ σs₂ ↑✶₂ k)
        ≡⟨ sym (⊡-/✶-↑✶ _ k σs₂) ⟩
          (a ⊡ b) /✶₂ σs₂ ↑✶₂ k
        ∎

      Kind/✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                  (∀ k x → var x /✶₁ σs₁ ↑✶₁ k ≡ var x /✶₂ σs₂ ↑✶₂ k) →
                   ∀ k j → j Kind/✶₁ σs₁ ↑✶₁ k ≡ j Kind/✶₂ σs₂ ↑✶₂ k
      Kind/✶-↑✶ σs₁ σs₂ hyp k (a ⋯ b) = begin
          (a ⋯ b) Kind/✶₁ σs₁ ↑✶₁ k
        ≡⟨ ⋯-Kind/✶-↑✶ _ k σs₁ ⟩
          (a /✶₁ σs₁ ↑✶₁ k) ⋯ (b /✶₁ σs₁ ↑✶₁ k)
        ≡⟨ cong₂ _⋯_ (/✶-↑✶ σs₁ σs₂ hyp k a) (/✶-↑✶ σs₁ σs₂ hyp k b) ⟩
          (a /✶₂ σs₂ ↑✶₂ k) ⋯ (b /✶₂ σs₂ ↑✶₂ k)
        ≡⟨ sym (⋯-Kind/✶-↑✶ _ k σs₂) ⟩
          (a ⋯ b) Kind/✶₂ σs₂ ↑✶₂ k
        ∎
      Kind/✶-↑✶ σs₁ σs₂ hyp k (Π j l) = begin
          (Π j l) Kind/✶₁ σs₁ ↑✶₁ k
        ≡⟨ Π-Kind/✶-↑✶ _ k σs₁ ⟩
          Π (j Kind/✶₁ σs₁ ↑✶₁ k) (l Kind/✶₁ σs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ Π (Kind/✶-↑✶ σs₁ σs₂ hyp k j)
                   (Kind/✶-↑✶ σs₁ σs₂ hyp (suc k) l) ⟩
          Π (j Kind/✶₂ σs₂ ↑✶₂ k) (l Kind/✶₂ σs₂ ↑✶₂ suc k)
        ≡⟨ sym (Π-Kind/✶-↑✶ _ k σs₂) ⟩
          (Π j l) Kind/✶₂ σs₂ ↑✶₂ k
        ∎

    open Application (record { _/_ = SubstApp._Elim/_ lift₁ }) using ()
      renaming (_/✶_ to _Elim/✶₁_)
    open Application (record { _/_ = SubstApp._Elim/_ lift₂ }) using ()
      renaming (_/✶_ to _Elim/✶₂_)

    Elim/✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                  (∀ k x → var x /✶₁ σs₁ ↑✶₁ k ≡ var x /✶₂ σs₂ ↑✶₂ k) →
                   ∀ k a → a Elim/✶₁ σs₁ ↑✶₁ k ≡ a Elim/✶₂ σs₂ ↑✶₂ k
    Elim/✶-↑✶ σs₁ σs₂ hyp k a = begin
        a Elim/✶₁ σs₁ ↑✶₁ k
      ≡⟨ sym (cong (_Elim/✶₁ σs₁ ↑✶₁ k) (⌜⌝∘⌞⌟-id a)) ⟩
        ⌜ ⌞ a ⌟ ⌝ Elim/✶₁ σs₁ ↑✶₁ k
      ≡⟨ sym (⌜⌝-/✶-↑✶ _ k σs₁) ⟩
        ⌜ ⌞ a ⌟ /✶₁ σs₁ ↑✶₁ k ⌝
      ≡⟨ cong ⌜_⌝ (/✶-↑✶ σs₁ σs₂ hyp k ⌞ a ⌟) ⟩
        ⌜ ⌞ a ⌟ /✶₂ σs₂ ↑✶₂ k ⌝
      ≡⟨ ⌜⌝-/✶-↑✶ _ k σs₂ ⟩
        ⌜ ⌞ a ⌟ ⌝ Elim/✶₂ σs₂ ↑✶₂ k
      ≡⟨ cong (_Elim/✶₂ σs₂ ↑✶₂ k) (⌜⌝∘⌞⌟-id a) ⟩
        a Elim/✶₂ σs₂ ↑✶₂ k
      ∎

    open Application (record { _/_ = SubstApp._Kind′/_ lift₁ }) using ()
      renaming (_/✶_ to _Kind′/✶₁_)
    open Application (record { _/_ = SubstApp._Kind′/_ lift₂ }) using ()
      renaming (_/✶_ to _Kind′/✶₂_)

    Kind′/✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                  (∀ k x → var x  /✶₁ σs₁ ↑✶₁ k ≡ var x  /✶₂ σs₂ ↑✶₂ k) →
                   ∀ k j → j Kind′/✶₁ σs₁ ↑✶₁ k ≡ j Kind′/✶₂ σs₂ ↑✶₂ k
    Kind′/✶-↑✶ σs₁ σs₂ hyp k j = begin
        j Kind′/✶₁ σs₁ ↑✶₁ k
      ≡⟨ sym (cong (_Kind′/✶₁ σs₁ ↑✶₁ k) (⌜⌝Kd∘⌞⌟Kd-id j)) ⟩
        ⌜ ⌞ j ⌟Kd ⌝Kd Kind′/✶₁ σs₁ ↑✶₁ k
      ≡⟨ sym (⌜⌝Kd-/✶-↑✶ _ k σs₁) ⟩
        ⌜ ⌞ j ⌟Kd Kind/✶₁ σs₁ ↑✶₁ k ⌝Kd
      ≡⟨ cong ⌜_⌝Kd (Kind/✶-↑✶ σs₁ σs₂ hyp k ⌞ j ⌟Kd) ⟩
        ⌜ ⌞ j ⌟Kd Kind/✶₂ σs₂ ↑✶₂ k ⌝Kd
      ≡⟨ ⌜⌝Kd-/✶-↑✶ _ k σs₂ ⟩
        ⌜ ⌞ j ⌟Kd ⌝Kd Kind′/✶₂ σs₂ ↑✶₂ k
      ≡⟨ cong (_Kind′/✶₂ σs₂ ↑✶₂ k) (⌜⌝Kd∘⌞⌟Kd-id j) ⟩
        j Kind′/✶₂ σs₂ ↑✶₂ k
      ∎

  -- Lemmas relating application of sequences of generic substitutions
  -- in generic kind or type ascriptions, provided substitutions on
  -- the underlying kinds or types are similarly related.

  record KdOrTpLemmas {T₁ T₂ T′ : ℕ → Set}
                      (lift₁ : Lift T₁ Term)
                      (lift₂ : Lift T₂ Term)
                      : Set where
    field
      kdApp₁ : Application (Kind T′) T₁
      kdApp₂ : Application (Kind T′) T₂
      tpApp₁ : Application T′ T₁
      tpApp₂ : Application T′ T₂

    open Lift lift₁ using () renaming (_↑✶_ to _↑✶₁_)
    open Lift lift₂ using () renaming (_↑✶_ to _↑✶₂_)
    private
      module A₁  = Application (record { _/_ = SubstApp._/_ lift₁ })
      module A₂  = Application (record { _/_ = SubstApp._/_ lift₂ })
      module T₁  = Application tpApp₁
      module T₂  = Application tpApp₂
      module K₁  = Application kdApp₁
      module K₂  = Application kdApp₂
      module KT₁ = KdOrTpSubstApp (Lift.simple lift₁) kdApp₁ tpApp₁
      module KT₂ = KdOrTpSubstApp (Lift.simple lift₂) kdApp₂ tpApp₂

    -- Sequences of (lifted) T₁ and T₂-substitutions are equivalent
    -- when applied to kinds and raw types (represented as T′s) if
    -- they are equivalent when applied to variables (represented as
    -- raw terms).

    field
      Kd/✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                (∀ k x → var x A₁./✶ σs₁ ↑✶₁ k ≡ var x A₂./✶ σs₂ ↑✶₂ k) →
                 ∀ k a → a     K₁./✶ σs₁ ↑✶₁ k ≡ a      K₂./✶ σs₂ ↑✶₂ k

      Tp/✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                (∀ k x → var x A₁./✶ σs₁ ↑✶₁ k ≡ var x A₂./✶ σs₂ ↑✶₂ k) →
                 ∀ k a → a     T₁./✶ σs₁ ↑✶₁ k ≡ a     T₂./✶ σs₂ ↑✶₂ k

    /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
            (∀ k x → var x A₁./✶  σs₁ ↑✶₁ k ≡ var x A₂./✶  σs₂ ↑✶₂ k) →
             ∀ k a → a     KT₁./✶ σs₁ ↑✶₁ k ≡ a     KT₂./✶ σs₂ ↑✶₂ k
    /✶-↑✶ σs₁ σs₂ hyp k (kd j) = begin
      kd j KT₁./✶ σs₁ ↑✶₁ k    ≡⟨ KT₁.kd-/✶-↑✶ k σs₁ ⟩
      kd (j K₁./✶ σs₁ ↑✶₁ k)   ≡⟨ cong kd (Kd/✶-↑✶ σs₁ σs₂ hyp k j) ⟩
      kd (j K₂./✶ σs₂ ↑✶₂ k)   ≡⟨ sym (KT₂.kd-/✶-↑✶ k σs₂) ⟩
      kd j KT₂./✶ σs₂ ↑✶₂ k    ∎
    /✶-↑✶ σs₁ σs₂ hyp k (tp a) = begin
      tp a KT₁./✶ σs₁ ↑✶₁ k      ≡⟨ KT₁.tp-/✶-↑✶ k σs₁ ⟩
      tp (a T₁./✶ σs₁ ↑✶₁ k)   ≡⟨ cong tp (Tp/✶-↑✶ σs₁ σs₂ hyp k a) ⟩
      tp (a T₂./✶ σs₂ ↑✶₂ k)   ≡⟨ sym (KT₂.tp-/✶-↑✶ k σs₂) ⟩
      tp a KT₂./✶ σs₂ ↑✶₂ k      ∎

  termAscLemmas : ∀ {T₁ T₂} lift₁ lift₂ → KdOrTpLemmas {T₁} {T₂} lift₁ lift₂
  termAscLemmas lift₁ lift₂ = record
    { kdApp₁  = record { _/_ = SubstApp._Kind/_ lift₁ }
    ; kdApp₂  = record { _/_ = SubstApp._Kind/_ lift₂ }
    ; tpApp₁  = record { _/_ = SubstApp._/_ lift₁ }
    ; tpApp₂  = record { _/_ = SubstApp._/_ lift₂ }
    ; Kd/✶-↑✶ = Lemmas.Kind/✶-↑✶
    ; Tp/✶-↑✶ = Lemmas./✶-↑✶
    }

  elimAscLemmas : ∀ {T₁ T₂} lift₁ lift₂ → KdOrTpLemmas {T₁} {T₂} lift₁ lift₂
  elimAscLemmas lift₁ lift₂ = record
    { kdApp₁  = record { _/_ = SubstApp._Kind′/_ lift₁ }
    ; kdApp₂  = record { _/_ = SubstApp._Kind′/_ lift₂ }
    ; tpApp₁  = record { _/_ = SubstApp._Elim/_ lift₁ }
    ; tpApp₂  = record { _/_ = SubstApp._Elim/_ lift₂ }
    ; Kd/✶-↑✶ = Lemmas.Kind′/✶-↑✶
    ; Tp/✶-↑✶ = Lemmas.Elim/✶-↑✶
    }

  -- By instantiating TermLemmas, we get access to a number of useful
  -- (derived) lemmas about path substitutions.

  termLemmas : TermLemmas Term
  termLemmas = record
    { termSubst = termSubst
    ; app-var   = refl
    ; /✶-↑✶     = Lemmas./✶-↑✶
    }

  open TermLemmas termLemmas public hiding (var; termSubst; weaken-sub)
  open SubstApp (TermSubst.termLift termSubst) public using
    ( _Head/_; _//_
    ; ++-//; ∙∙-/; ⌜·⌝-/; ⌜⌝-/; ⌜⌝Kd-/; ⌞⌟-/; ⌞⌟Kd-/; ⌊⌋-Kind/; ⌊⌋-Kind′/
    )
  open SubstApp (TermSubst.varLift termSubst) public using () renaming
    ( _Head/_   to _Head/Var′_
    ; _//_      to _//Var_
    ; ++-//     to ++-//Var
    ; ∙∙-/      to ∙∙-/Var
    ; ⌜·⌝-/     to ⌜·⌝-/Var
    ; ⌜⌝-/      to ⌜⌝-/Var
    ; ⌜⌝Kd-/    to ⌜⌝Kd-/Var
    ; ⌞⌟-/      to ⌞⌟-/Var
    ; ⌞⌟Kd-/    to ⌞⌟Kd-/Var
    ; ⌊⌋-Kind/  to ⌊⌋-Kind/Var
    ; ⌊⌋-Kind′/ to ⌊⌋-Kind′/Var
    )

  -- By instantiating TermLikeLemmas, we get access to a number of
  -- useful (derived) lemmas about variable substitutions (renamings)
  -- and substitutions in kinds, eliminations and ascriptions.

  private
    termLikeLemmas : TermLikeLemmas Term Term
    termLikeLemmas = record
      { app        = SubstApp._/_
      ; termLemmas = termLemmas
      ; /✶-↑✶₁     = Lemmas./✶-↑✶
      ; /✶-↑✶₂     = Lemmas./✶-↑✶
      }

  open TermLikeLemmas termLikeLemmas public using
    ( varLiftAppLemmas; varLiftSubLemmas; _/Var_
    ; weaken-sub; weaken-/; weaken⋆; /-wk⋆
    )

  termLikeLemmasKind : TermLikeLemmas (Kind Term) Term
  termLikeLemmasKind = record
    { app        = SubstApp._Kind/_
    ; termLemmas = termLemmas
    ; /✶-↑✶₁     = Lemmas.Kind/✶-↑✶
    ; /✶-↑✶₂     = Lemmas.Kind/✶-↑✶
    }

  open TermLikeLemmas termLikeLemmasKind public using () renaming
    ( _/_     to _Kind/_
    ; _/Var_  to _Kind/Var_
    ; weaken  to weakenKind
    ; weaken⋆ to weakenKind⋆
    )

  termLikeLemmasElim : TermLikeLemmas Elim Term
  termLikeLemmasElim = record
    { app        = SubstApp._Elim/_
    ; termLemmas = termLemmas
    ; /✶-↑✶₁     = Lemmas.Elim/✶-↑✶
    ; /✶-↑✶₂     = Lemmas.Elim/✶-↑✶
    }

  open TermLikeLemmas termLikeLemmasElim public using () renaming
    ( _/_     to _Elim/_
    ; _/Var_  to _Elim/Var_
    ; weaken  to weakenElim
    ; weaken⋆ to weakenElim⋆
    )

  termLikeLemmasKind′ : TermLikeLemmas (Kind Elim) Term
  termLikeLemmasKind′ = record
    { app        = SubstApp._Kind′/_
    ; termLemmas = termLemmas
    ; /✶-↑✶₁     = Lemmas.Kind′/✶-↑✶
    ; /✶-↑✶₂     = Lemmas.Kind′/✶-↑✶
    }

  open TermLikeLemmas termLikeLemmasKind′ public using () renaming
    ( _/_     to _Kind′/_
    ; _/Var_  to _Kind′/Var_
    ; weaken  to weakenKind′
    ; weaken⋆ to weakenKind′⋆
    )

  termLikeLemmasTermAsc : TermLikeLemmas TermAsc Term
  termLikeLemmasTermAsc = record
    { app        = SubstApp._TermAsc/_
    ; termLemmas = termLemmas
    ; /✶-↑✶₁     = KdOrTpLemmas./✶-↑✶ (termAscLemmas _ _)
    ; /✶-↑✶₂     = KdOrTpLemmas./✶-↑✶ (termAscLemmas _ _)
    }

  open TermLikeLemmas termLikeLemmasTermAsc public using () renaming
    ( termLikeSubst to termAscTermSubst
    ; _/_           to _TermAsc/_
    ; _/Var_        to _TermAsc/Var_
    ; weaken        to weakenTermAsc
    )

  termLikeLemmasElimAsc : TermLikeLemmas ElimAsc Term
  termLikeLemmasElimAsc = record
    { app        = SubstApp._ElimAsc/_
    ; termLemmas = termLemmas
    ; /✶-↑✶₁     = KdOrTpLemmas./✶-↑✶ (elimAscLemmas _ _)
    ; /✶-↑✶₂     = KdOrTpLemmas./✶-↑✶ (elimAscLemmas _ _)
    }

  open TermLikeLemmas termLikeLemmasElimAsc public using () renaming
    ( termLikeSubst to elimAscTermSubst
    ; _/_           to _ElimAsc/_
    ; _/Var_        to _ElimAsc/Var_
    ; weaken        to weakenElimAsc
    ; weaken⋆       to weakenElimAsc⋆
    )

  -- Weakening of heads and spines.

  weakenHead : ∀ {n} → Head n → Head (suc n)
  weakenHead a = a Head/Var VarSubst.wk

  weakenSpine : ∀ {n} → Spine n → Spine (suc n)
  weakenSpine a = a //Var VarSubst.wk

  -- Conversion of ascriptions commutes with weakening.

  ⌜⌝Asc-weaken : ∀ {n} (a : TermAsc n) →
                 ⌜ weakenTermAsc a ⌝Asc ≡ weakenElimAsc ⌜ a ⌝Asc
  ⌜⌝Asc-weaken (kd k) = cong kd (⌜⌝Kd-/Var k)
  ⌜⌝Asc-weaken (tp a) = cong tp (⌜⌝-/Var a)

  ⌞⌟Asc-weaken : ∀ {n} (a : ElimAsc n) →
                 ⌞ weakenElimAsc a ⌟Asc ≡ weakenTermAsc ⌞ a ⌟Asc
  ⌞⌟Asc-weaken (kd k) = cong kd (⌞⌟Kd-/Var k)
  ⌞⌟Asc-weaken (tp a) = cong tp (⌞⌟-/Var a)

  -- Simplified kinds are stable under weakening.

  ⌊⌋-weaken : ∀ {n} (k : Kind Term n) → ⌊ weakenKind k ⌋ ≡ ⌊ k ⌋
  ⌊⌋-weaken k = ⌊⌋-Kind/Var k

  ⌊⌋-weaken′ : ∀ {n} (k : Kind Elim n) → ⌊ weakenKind′ k ⌋ ≡ ⌊ k ⌋
  ⌊⌋-weaken′ k = ⌊⌋-Kind′/Var k

  ⌊⌋-weaken⋆′ : ∀ {m} n (k : Kind Elim m) → ⌊ weakenKind′⋆ n k ⌋ ≡ ⌊ k ⌋
  ⌊⌋-weaken⋆′ zero    k = refl
  ⌊⌋-weaken⋆′ (suc n) k = begin
    ⌊ weakenKind′ (weakenKind′⋆ n k) ⌋   ≡⟨ ⌊⌋-weaken′ (weakenKind′⋆ n k) ⟩
    ⌊ weakenKind′⋆ n k ⌋                 ≡⟨ ⌊⌋-weaken⋆′ n k ⟩
    ⌊ k ⌋                                ∎

  infix 10 _[_] _Elim[_] _Kind[_] _Kind′[_] _TermAsc[_] _ElimAsc[_]

  -- Shorthands for single-variable term substitutions.

  _[_] : ∀ {n} → Term (suc n) → Term n → Term n
  a [ b ] = a / sub b

  _Elim[_] : ∀ {n} → Elim (suc n) → Term n → Elim n
  a Elim[ b ] = a Elim/ sub b

  _Kind[_] : ∀ {n} → Kind Term (suc n) → Term n → Kind Term n
  k Kind[ b ] = k Kind/ (sub b)

  _Kind′[_] : ∀ {n} → Kind Elim (suc n) → Term n → Kind Elim n
  k Kind′[ b ] = k Kind′/ (sub b)

  _TermAsc[_] : ∀ {n} → TermAsc (suc n) → Term n → TermAsc n
  a TermAsc[ b ] = a TermAsc/ sub b

  _ElimAsc[_] : ∀ {n} → ElimAsc (suc n) → Term n → ElimAsc n
  a ElimAsc[ b ] = a ElimAsc/ sub b

  private module V  = VarSubst

  -- Kinds are stable under substitutions of a variable for a fresh
  -- variable (up to α-equivalence).

  Kind-wk↑-sub-zero-vanishes : ∀ {n} (k : Kind Term (suc n)) →
                               (k Kind/Var V.wk V.↑) Kind[ var zero ] ≡ k
  Kind-wk↑-sub-zero-vanishes k = begin
      (k Kind/Var V.wk V.↑) Kind[ var zero ]
    ≡⟨ sym (KL./-sub (k Kind/Var _) zero) ⟩
      k Kind/Var V.wk V.↑ Kind/Var V.sub zero
    ≡⟨ sym (LiftAppLemmas./-⊙ KL.varLiftAppLemmas k) ⟩
      k Kind/Var V.wk V.↑ V.⊙ V.sub zero
    ≡⟨⟩
      k Kind/Var (zero ∷ (Vec.map suc V.wk V.⊙ V.sub zero))
    ≡⟨ cong (λ σ → k Kind/Var (zero ∷ σ)) VarLemmas.map-weaken-⊙-sub ⟩
      k Kind/Var (zero ∷ V.wk)
    ≡⟨⟩
      k Kind/Var V.id
    ≡⟨ LiftAppLemmas.id-vanishes KL.varLiftAppLemmas k ⟩
      k
    ∎
    where
      open ≡-Reasoning
      module KL = TermLikeLemmas termLikeLemmasKind


----------------------------------------------------------------------
-- Typing contexts containing kind and type ascriptions.

-- Generic typing contexts over T-ascriptions and useful operations.

record KdOrTpCtx (T : ℕ → Set) : Set₁ where
  open Context public hiding (Ctx; CtxExt)

  -- Contexts and context extensions.

  Ctx     = Context.Ctx     (KdOrTp T)
  CtxExt  = Context.CtxExt  (KdOrTp T)

  -- Operations such as context lookup and substitutions in context
  -- extensions require some extra substitution machinery for
  -- T-ascriptions, all of which is provided by the following instance
  -- of TermLikeLemmas.

  field termLikeLemmas : TermLikeLemmas (KdOrTp T) Term
  open TermLikeLemmas termLikeLemmas
    using (termApplication; weaken; termLemmas)
  open TermLemmas termLemmas using (simple)

  weakenOps : Extension (KdOrTp T)
  weakenOps = record { weaken = weaken }

  open WeakenOps        weakenOps           public hiding (weaken; weaken⋆)
  open WeakenOpsLemmas  weakenOps           public
  open ConversionLemmas weakenOps weakenOps public

  open SubstOps termApplication simple public using (_E/_)

open Substitution

-- Concrete typing contexts over raw term and raw elimination
-- ascriptions.

termCtx : KdOrTpCtx Term
termCtx = record { termLikeLemmas = termLikeLemmasTermAsc }
module TermCtx = KdOrTpCtx termCtx

elimCtx : KdOrTpCtx Elim
elimCtx = record { termLikeLemmas = termLikeLemmasElimAsc }
module ElimCtx = KdOrTpCtx elimCtx

-- Concrete typing contexts over shape ascriptions and useful
-- operations.

module SimpleCtx where
  open Context public hiding (Ctx; CtxExt)
  open Maybe   public using  (Maybe) renaming (just to kd; nothing to tp)

  -- Shape ascriptions.
  --
  -- NOTE.  We only use shape ascriptions (or "simple" kind
  -- ascriptions) in the simplified kinding system, which is defined
  -- exclusively on types (see the FOmegaInt.Kinding.Simple module).
  -- Because simple kinding judgments can never refer to term
  -- variables, we may as well forget the type of such variables.  We
  -- just need to remember that there are such variables in the
  -- context so as to maintain the de Bruijn indexes of (type)
  -- variables, e.g. when we convert full kinding judgments to
  -- simplified ones.  Accordingly, we implement shape ascriptions
  -- using `Maybe' from the standard library, but with the
  -- constructors `just' and `nothing' renamed to `kd' and `tp' to
  -- better reflect their meaning.  (This renaming happens during the
  -- import of the `Maybe' module above.)

  SAsc : ℕ → Set
  SAsc _ = Maybe SKind

  -- Simplification/erasure of ascriptions.

  ⌊_⌋Asc : ∀ {T n} → KdOrTp T n → SAsc n
  ⌊ kd k ⌋Asc = kd ⌊ k ⌋
  ⌊ tp a ⌋Asc = tp

  -- Injectivity of the (simple) `kd' constructor.

  kd-inj′ : {j k : SKind} → _≡_ {A = Maybe SKind} (kd j) (kd k) → j ≡ k
  kd-inj′ refl = refl

  -- Contexts and context extensions over shape ascriptions.

  Ctx     = Context.Ctx     SAsc
  CtxExt  = Context.CtxExt  SAsc

  weakenOps : Extension SAsc
  weakenOps = record { weaken = Function.id }

  open WeakenOps        weakenOps           public hiding (weaken; weaken⋆)
  open WeakenOpsLemmas  weakenOps           public
  open ConversionLemmas weakenOps weakenOps public

  -- Change the indexing of a context extension.

  re-idx : ∀ {k m n} → CtxExt k n → CtxExt m n
  re-idx Γ = mapExt (λ _ k → k) Γ

  open Extension weakenOps public using () renaming (weaken⋆ to weakenSAsc⋆)

  weakenSAsc⋆-id : ∀ m {n a} → weakenSAsc⋆ m {n} a ≡ a
  weakenSAsc⋆-id zero    = refl
  weakenSAsc⋆-id (suc m) = weakenSAsc⋆-id m

  ⌊⌋-TermAsc/ : ∀ {m n} a {σ : Sub Term m n} → ⌊ a TermAsc/ σ ⌋Asc ≡ ⌊ a ⌋Asc
  ⌊⌋-TermAsc/ (kd k) = cong kd (⌊⌋-Kind/ k)
  ⌊⌋-TermAsc/ (tp t) = refl

  ⌊⌋-ElimAsc/ : ∀ {m n} a {σ : Sub Term m n} → ⌊ a ElimAsc/ σ ⌋Asc ≡ ⌊ a ⌋Asc
  ⌊⌋-ElimAsc/ (kd k) = cong kd (⌊⌋-Kind′/ k)
  ⌊⌋-ElimAsc/ (tp t) = refl

  ⌊⌋-ElimAsc/Var : ∀ {m n} a {σ : Sub Fin m n} →
                   ⌊ a ElimAsc/Var σ ⌋Asc ≡ ⌊ a ⌋Asc
  ⌊⌋-ElimAsc/Var (kd k) = cong kd (⌊⌋-Kind′/Var k)
  ⌊⌋-ElimAsc/Var (tp t) = refl

-- Conversions between the different context representations.

module ContextConversions where
  open Context
  open SimpleCtx using (kd; ⌊_⌋Asc; ⌊⌋-ElimAsc/Var)

  ⌞_⌟Ctx : ∀ {n} → ElimCtx.Ctx n → TermCtx.Ctx n
  ⌞ Γ ⌟Ctx = ElimCtx.map ⌞_⌟Asc Γ

  ⌜_⌝Ctx : ∀ {n} → TermCtx.Ctx n → ElimCtx.Ctx n
  ⌜ Γ ⌝Ctx = TermCtx.map ⌜_⌝Asc Γ

  ⌊_⌋Ctx : ∀ {T n} → Ctx (KdOrTp T) n → SimpleCtx.Ctx n
  ⌊ Γ ⌋Ctx = SimpleCtx.map ⌊_⌋Asc Γ

  ⌊_⌋CtxExt : ∀ {T m n} → CtxExt (KdOrTp T) m n → SimpleCtx.CtxExt m n
  ⌊ Γ ⌋CtxExt = SimpleCtx.mapExt (λ _ → ⌊_⌋Asc) Γ

  module ⌞⌟Ctx-Lemmas = ConversionLemmas ElimCtx.weakenOps TermCtx.weakenOps
  module ⌜⌝Ctx-Lemmas = ConversionLemmas TermCtx.weakenOps ElimCtx.weakenOps
  module ⌊⌋Ctx-Lemmas = ConversionLemmas ElimCtx.weakenOps SimpleCtx.weakenOps

  -- Context conversions commute with context lookup.

  ⌞⌟Asc-lookup : ∀ {n} (Γ : ElimCtx.Ctx n) x →
                 TermCtx.lookup ⌞ Γ ⌟Ctx x ≡ ⌞ ElimCtx.lookup Γ x ⌟Asc
  ⌞⌟Asc-lookup Γ x =
    ⌞⌟Ctx-Lemmas.lookup-map ⌞_⌟Asc Γ x (λ a → sym (⌞⌟Asc-weaken a))

  ⌜⌝Asc-lookup : ∀ {n} (Γ : TermCtx.Ctx n) x →
                 ElimCtx.lookup ⌜ Γ ⌝Ctx x ≡ ⌜ TermCtx.lookup Γ x ⌝Asc
  ⌜⌝Asc-lookup Γ x =
    ⌜⌝Ctx-Lemmas.lookup-map ⌜_⌝Asc Γ x (λ a → sym (⌜⌝Asc-weaken a))

  ⌊⌋Asc-lookup : ∀ {n} (Γ : ElimCtx.Ctx n) x →
                 SimpleCtx.lookup ⌊ Γ ⌋Ctx x ≡ ⌊ ElimCtx.lookup Γ x ⌋Asc
  ⌊⌋Asc-lookup Γ x =
    ⌊⌋Ctx-Lemmas.lookup-map ⌊_⌋Asc Γ x (λ a → sym (⌊⌋-ElimAsc/Var a))

  ⌊⌋-lookup : ∀ {n} (Γ : ElimCtx.Ctx n) x {k} → ElimCtx.lookup Γ x ≡ kd k →
              SimpleCtx.lookup ⌊ Γ ⌋Ctx x ≡ kd ⌊ k ⌋
  ⌊⌋-lookup Γ x {k} Γ[x]≡kd-k = begin
      SimpleCtx.lookup ⌊ Γ ⌋Ctx x
    ≡⟨ ⌊⌋Asc-lookup Γ x ⟩
      ⌊ ElimCtx.lookup Γ x ⌋Asc
    ≡⟨ cong ⌊_⌋Asc Γ[x]≡kd-k ⟩
      kd ⌊ k ⌋
    ∎
    where open ≡-Reasoning
