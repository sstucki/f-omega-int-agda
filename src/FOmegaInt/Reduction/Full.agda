------------------------------------------------------------------------
-- Full β-reduction in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Reduction.Full where

open import Data.Fin using (suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.List using ([]; _∷_)
open import Data.Sum using ([_,_])
open import Data.Product using (_,_; ∃; _×_)
open import Function using (flip; _∘_)
open import Relation.Binary using (Setoid; Preorder)
import Relation.Binary.Construct.Closure.Equivalence as EqClos
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (ε; _◅_; gmap)
import Relation.Binary.Construct.Closure.Symmetric as SymClos
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.Reduction
import Function.Equivalence as Equiv

open import FOmegaInt.Syntax

open Syntax
open Substitution using (_[_]; weaken)

----------------------------------------------------------------------
-- Full β-reduction and equality relations

infixl 9  _·₁_ _·₂_ _⊡₁_ _⊡₂_
infixr 7  _⇒₁_ _⇒₂_
infix  6  _⋯₁_ _⋯₂_
infix  5  _→β_ _Kd→β_

mutual

  -- The compatible closure of a binary term relation.

  data Compat (_∼_ : TRel Term) {n} : Term n → Term n → Set where
    ⌈_⌉  : ∀ {a₁ a₂} → a₁ ∼ a₂                  → Compat _∼_ a₁ a₂
    Π₁   : ∀ {k₁ k₂} → KdCompat _∼_ k₁ k₂ → ∀ a → Compat _∼_ (Π k₁ a) (Π k₂ a)
    Π₂   : ∀ {a₁ a₂} k → Compat _∼_ a₁ a₂       → Compat _∼_ (Π k a₁) (Π k a₂)
    _⇒₁_ : ∀ {a₁ a₂} → Compat _∼_ a₁ a₂   → ∀ b → Compat _∼_ (a₁ ⇒ b) (a₂ ⇒ b)
    _⇒₂_ : ∀ {b₁ b₂} a → Compat _∼_ b₁ b₂       → Compat _∼_ (a ⇒ b₁) (a ⇒ b₂)
    Λ₁   : ∀ {k₁ k₂} → KdCompat _∼_ k₁ k₂ → ∀ a → Compat _∼_ (Λ k₁ a) (Λ k₂ a)
    Λ₂   : ∀ {a₁ a₂} k → Compat _∼_ a₁ a₂       → Compat _∼_ (Λ k a₁) (Λ k a₂)
    ƛ₁   : ∀ {a₁ a₂} → Compat _∼_ a₁ a₂   → ∀ b → Compat _∼_ (ƛ a₁ b) (ƛ a₂ b)
    ƛ₂   : ∀ {b₁ b₂} a → Compat _∼_ b₁ b₂       → Compat _∼_ (ƛ a b₁) (ƛ a b₂)
    _·₁_ : ∀ {a₁ a₂} → Compat _∼_ a₁ a₂   → ∀ b → Compat _∼_ (a₁ · b) (a₂ · b)
    _·₂_ : ∀ {b₁ b₂} a → Compat _∼_ b₁ b₂       → Compat _∼_ (a · b₁) (a · b₂)
    _⊡₁_ : ∀ {a₁ a₂} → Compat _∼_ a₁ a₂   → ∀ b → Compat _∼_ (a₁ ⊡ b) (a₂ ⊡ b)
    _⊡₂_ : ∀ {b₁ b₂} a → Compat _∼_ b₁ b₂       → Compat _∼_ (a ⊡ b₁) (a ⊡ b₂)

  data KdCompat (_∼_ : TRel Term) {n} : Kind Term n → Kind Term n → Set where
    _⋯₁_ : ∀ {a₁ a₂} → Compat _∼_ a₁ a₂ → ∀ b   → KdCompat _∼_ (a₁ ⋯ b) (a₂ ⋯ b)
    _⋯₂_ : ∀ {b₁ b₂} a → Compat _∼_ b₁ b₂       → KdCompat _∼_ (a ⋯ b₁) (a ⋯ b₂)
    Π₁   : ∀ {j₁ j₂} → KdCompat _∼_ j₁ j₂ → ∀ b → KdCompat _∼_ (Π j₁ b) (Π j₂ b)
    Π₂   : ∀ {k₁ k₂} k → KdCompat _∼_ k₁ k₂     → KdCompat _∼_ (Π k k₁) (Π k k₂)

-- β-contraction.
data BetaCont {n} : Term n → Term n → Set where
  cont-Tp· : ∀ k a b → BetaCont ((Λ k a) · b) (a [ b ])
  cont-Tm· : ∀ a b c → BetaCont ((ƛ a b) · c) (b [ c ])
  cont-⊡   : ∀ k a b → BetaCont ((Λ k a) ⊡ b) (a [ b ])

-- One-step β-reduction.

_→β_ : TRel Term
_→β_ = Compat BetaCont

_Kd→β_ : TRel (Kind Term)
_Kd→β_ = KdCompat BetaCont

-- Full β-reduction and equality.

β-reduction : Reduction Term
β-reduction = record { _→1_ = _→β_ }

β-reductionKind : Reduction (Kind Term)
β-reductionKind = record { _→1_ = _Kd→β_ }

open Reduction β-reduction public hiding (_→1_)
  renaming (_→*_ to _→β*_; _↔_ to _≡β_)

open Reduction β-reductionKind public hiding (_→1_)
  renaming (_→*_ to _Kd→β*_; _↔_ to _Kd≡β_)


----------------------------------------------------------------------
-- Simple properties of the β-reductions/equalities

-- Inclusions.

→β⇒→β* = →1⇒→* β-reduction
→β*⇒≡β = →*⇒↔  β-reduction
→β⇒≡β  = →1⇒↔  β-reduction

-- Reduction is a preorders.

→β*-preorder   = →*-preorder β-reduction
Kd→β*-preorder = →*-preorder β-reductionKind

-- Preorder reasoning for reduction.

module →β*-Reasoning    = →*-Reasoning β-reduction
module Kd→β*-Reasoning  = →*-Reasoning β-reductionKind

-- Raw terms and kinds together with β-equality form setoids.

≡β-setoid   = ↔-setoid β-reduction
Kd≡β-setoid = ↔-setoid β-reductionKind

-- Equational reasoning for the equality.

module ≡β-Reasoning   = ↔-Reasoning β-reduction
module Kd≡β-Reasoning = ↔-Reasoning β-reductionKind

-- Multistep and equality congruence lemmas.

module CongLemmas (_∼_ : TRel Term) where

  private
    reduction : Reduction Term
    reduction = record { _→1_ = Compat _∼_ }

    reductionKd : Reduction (Kind Term)
    reductionKd = record { _→1_ = KdCompat _∼_ }

    module O  {n} = Preorder (→*-preorder reduction   n)
    module S  {n} = Setoid   (↔-setoid    reduction   n)
    module OK {n} = Preorder (→*-preorder reductionKd n)
    module SK {n} = Setoid   (↔-setoid    reductionKd n)

  open Reduction reduction
  open Reduction reductionKd using () renaming (_→*_ to _Kd→*_; _↔_ to _Kd↔_)

  -- A Congruence lemma for _⌞∙⌟_.

  →1-⌞∙⌟₁ : ∀ {n} {a₁ a₂ : Term n} → a₁ →1 a₂ → ∀ bs → a₁ ⌞∙⌟ bs →1 a₂ ⌞∙⌟ bs
  →1-⌞∙⌟₁ a₁∼a₂ []       = a₁∼a₂
  →1-⌞∙⌟₁ a₁∼a₂ (b ∷ bs) = →1-⌞∙⌟₁ (a₁∼a₂ ·₁ b) bs

  -- Multistep congruence lemmas for transitive closures.

  →*-Π : ∀ {n} {k₁ k₂ : Kind Term n} {a₁ a₂} →
         k₁ Kd→* k₂ → a₁ →* a₂ → Π k₁ a₁ →* Π k₂ a₂
  →*-Π {a₁ = a₁} k₁→*k₂ a₁→*a₂ =
    O.trans (gmap (flip Π a₁) (λ j→k → Π₁ j→k a₁) k₁→*k₂)
            (gmap (Π _) (Π₂ _) a₁→*a₂)

  →*-⇒ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
         a₁ →* a₂ → b₁ →* b₂ → a₁ ⇒ b₁ →* a₂ ⇒ b₂
  →*-⇒ {b₁ = b₁} a₁→*a₂ b₁→*b₂ =
    O.trans (gmap (_⇒ b₁) (_⇒₁ b₁) a₁→*a₂) (gmap (_ ⇒_) (_ ⇒₂_) b₁→*b₂)

  →*-Λ : ∀ {n} {k₁ k₂ : Kind Term n} {a₁ a₂} →
         k₁ Kd→* k₂ → a₁ →* a₂ → Λ k₁ a₁ →* Λ k₂ a₂
  →*-Λ {a₁ = a₁} k₁→*k₂ a₁→*a₂ =
    O.trans (gmap (flip Λ a₁) (λ j→k → Λ₁ j→k a₁) k₁→*k₂)
            (gmap (Λ _) (Λ₂ _) a₁→*a₂)

  →*-ƛ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
         a₁ →* a₂ → b₁ →* b₂ → ƛ a₁ b₁ →* ƛ a₂ b₂
  →*-ƛ {b₁ = b₁} a₁→*a₂ b₁→*b₂ =
    O.trans (gmap (flip ƛ b₁) (flip ƛ₁ b₁) a₁→*a₂) (gmap (ƛ _) (ƛ₂ _) b₁→*b₂)

  →*-· : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
         a₁ →* a₂ → b₁ →* b₂ → a₁ · b₁ →* a₂ · b₂
  →*-· {b₁ = b₁} a₁→*a₂ b₁→*b₂ =
    O.trans (gmap (_· b₁) (_·₁ b₁) a₁→*a₂) (gmap (_ ·_) (_ ·₂_) b₁→*b₂)

  →*-⊡ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
         a₁ →* a₂ → b₁ →* b₂ → a₁ ⊡ b₁ →* a₂ ⊡ b₂
  →*-⊡ {b₁ = b₁} a₁→*a₂ b₁→*b₂ =
    O.trans (gmap (_⊡ b₁) (_⊡₁ b₁) a₁→*a₂) (gmap (_ ⊡_) (_ ⊡₂_) b₁→*b₂)

  Kd→*-⋯ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
         a₁ →* a₂ → b₁ →* b₂ → a₁ ⋯ b₁ Kd→* a₂ ⋯ b₂
  Kd→*-⋯ {b₁ = b₁} a₁→*a₂ b₁→*b₂ =
    OK.trans (gmap (_⋯ b₁) (_⋯₁ b₁) a₁→*a₂) (gmap (_ ⋯_) (_ ⋯₂_) b₁→*b₂)

  Kd→*-Π : ∀ {n} {j₁ j₂ : Kind Term n} {k₁ k₂} →
         j₁ Kd→* j₂ → k₁ Kd→* k₂ → Π j₁ k₁ Kd→* Π j₂ k₂
  Kd→*-Π {k₁ = k₁} j₁→*j₂ k₁→*k₂ =
    OK.trans (gmap (flip Π k₁) (λ j→k → Π₁ j→k k₁) j₁→*j₂)
             (gmap (Π _) (Π₂ _) k₁→*k₂)

  →*-⌞∙⌟₁ : ∀ {n} {a₁ a₂ : Term n} → a₁ →* a₂ → ∀ bs → a₁ ⌞∙⌟ bs →* a₂ ⌞∙⌟ bs
  →*-⌞∙⌟₁ a₁→*a₂ bs = gmap (_⌞∙⌟ bs) (flip →1-⌞∙⌟₁ bs) a₁→*a₂

  -- Congruence lemmas for equivalences closures.

  ↔-Π : ∀ {n} {k₁ k₂ : Kind Term n} {a₁ a₂} →
        k₁ Kd↔ k₂ → a₁ ↔ a₂ → Π k₁ a₁ ↔ Π k₂ a₂
  ↔-Π {a₁ = a₁} k₁↔k₂ a₁↔a₂ =
    S.trans (EqClos.gmap (flip Π a₁) (λ j→k → Π₁ j→k a₁) k₁↔k₂)
            (EqClos.gmap (Π _)       (Π₂ _)              a₁↔a₂)

  ↔-⇒ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
        a₁ ↔ a₂ → b₁ ↔ b₂ → a₁ ⇒ b₁ ↔ a₂ ⇒ b₂
  ↔-⇒ {b₁ = b₁} a₁↔a₂ b₁↔b₂ =
    S.trans (EqClos.gmap (_⇒ b₁) (_⇒₁ b₁) a₁↔a₂)
            (EqClos.gmap (_ ⇒_)  (_ ⇒₂_)  b₁↔b₂)

  ↔-Λ : ∀ {n} {k₁ k₂ : Kind Term n} {a₁ a₂} →
        k₁ Kd↔ k₂ → a₁ ↔ a₂ → Λ k₁ a₁ ↔ Λ k₂ a₂
  ↔-Λ {a₁ = a₁} k₁↔k₂ a₁↔a₂ =
    S.trans (EqClos.gmap (flip Λ a₁) (λ j→k → Λ₁ j→k a₁) k₁↔k₂)
            (EqClos.gmap (Λ _)       (Λ₂ _)              a₁↔a₂)

  ↔-ƛ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
        a₁ ↔ a₂ → b₁ ↔ b₂ → ƛ a₁ b₁ ↔ ƛ a₂ b₂
  ↔-ƛ {b₁ = b₁} a₁↔a₂ b₁↔b₂ =
    S.trans (EqClos.gmap (flip ƛ b₁) (flip ƛ₁ b₁) a₁↔a₂)
            (EqClos.gmap (ƛ _)       (ƛ₂ _)       b₁↔b₂)

  ↔-· : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
        a₁ ↔ a₂ → b₁ ↔ b₂ → a₁ · b₁ ↔ a₂ · b₂
  ↔-· {b₁ = b₁} a₁↔a₂ b₁↔b₂ =
    S.trans (EqClos.gmap (_· b₁) (_·₁ b₁) a₁↔a₂)
            (EqClos.gmap (_ ·_)  (_ ·₂_)  b₁↔b₂)

  ↔-⊡ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
        a₁ ↔ a₂ → b₁ ↔ b₂ → a₁ ⊡ b₁ ↔ a₂ ⊡ b₂
  ↔-⊡ {b₁ = b₁} a₁↔a₂ b₁↔b₂ =
    S.trans (EqClos.gmap (_⊡ b₁) (_⊡₁ b₁) a₁↔a₂)
            (EqClos.gmap (_ ⊡_)  (_ ⊡₂_)  b₁↔b₂)

  Kd↔-⋯ : ∀ {n} {a₁ a₂ : Term n} {b₁ b₂} →
          a₁ ↔ a₂ → b₁ ↔ b₂ → a₁ ⋯ b₁ Kd↔ a₂ ⋯ b₂
  Kd↔-⋯ {b₁ = b₁} a₁↔a₂ b₁↔b₂ =
    SK.trans (EqClos.gmap (_⋯ b₁) (_⋯₁ b₁) a₁↔a₂)
             (EqClos.gmap (_ ⋯_)  (_ ⋯₂_)  b₁↔b₂)

  Kd↔-Π : ∀ {n} {j₁ j₂ : Kind Term n} {k₁ k₂} →
          j₁ Kd↔ j₂ → k₁ Kd↔ k₂ → Π j₁ k₁ Kd↔ Π j₂ k₂
  Kd↔-Π {k₁ = k₁} j₁↔j₂ k₁↔k₂ =
    SK.trans (EqClos.gmap (flip Π k₁) (λ j→k → Π₁ j→k k₁) j₁↔j₂)
             (EqClos.gmap (Π _)       (Π₂ _)              k₁↔k₂)

  ↔-⌞∙⌟₁ : ∀ {n} {a₁ a₂ : Term n} → a₁ ↔ a₂ → ∀ bs → a₁ ⌞∙⌟ bs ↔ a₂ ⌞∙⌟ bs
  ↔-⌞∙⌟₁ a₁↔a₂ bs = EqClos.gmap (_⌞∙⌟ bs) (flip →1-⌞∙⌟₁ bs) a₁↔a₂

open CongLemmas BetaCont public renaming
  ( →1-⌞∙⌟₁ to →β-⌞∙⌟₁
  ; →*-Π    to →β*-Π
  ; →*-⇒    to →β*-⇒
  ; →*-Λ    to →β*-Λ
  ; →*-ƛ    to →β*-ƛ
  ; →*-·    to →β*-·
  ; →*-⊡    to →β*-⊡
  ; Kd→*-⋯  to Kd→β*-⋯
  ; Kd→*-Π  to Kd→β*-Π
  ; →*-⌞∙⌟₁ to →β*-⌞∙⌟₁
  ; ↔-Π     to ≡β-Π
  ; ↔-⇒     to ≡β-⇒
  ; ↔-Λ     to ≡β-Λ
  ; ↔-ƛ     to ≡β-ƛ
  ; ↔-·     to ≡β-·
  ; ↔-⊡     to ≡β-⊡
  ; Kd↔-⋯   to Kd≡β-⋯
  ; Kd↔-Π   to Kd≡β-Π
  ; ↔-⌞∙⌟₁  to ≡β-⌞∙⌟₁
  )
