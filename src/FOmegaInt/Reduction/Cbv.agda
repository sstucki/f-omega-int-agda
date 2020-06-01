------------------------------------------------------------------------
-- Call-by-value (CBV) reduction in Fω with interval kinds.
------------------------------------------------------------------------

module FOmegaInt.Reduction.Cbv where

open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
import Relation.Binary.Construct.Closure.Equivalence as EqClos
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (map; gmap)
import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.Reduction

open import FOmegaInt.Syntax
open import FOmegaInt.Reduction.Full

open Syntax
open Substitution using (_[_])

----------------------------------------------------------------------
-- Call-by-value (CBV) reduction and equivalence relations

-- Untyped term values with up to n free variables.
data Val {n} : Term n → Set where
  Λ : ∀ k a → Val (Λ k a)   -- type abstraction
  ƛ : ∀ a b → Val (ƛ a b)   -- term abstraction

infixl 9  _·₁_ _·₂_ _⊡_
infix  5  _→v_

-- One-step CBV reduction.
data _→v_ {n} : Term n → Term n → Set where
  cont-· : ∀ a b {c} (v : Val c)              → (ƛ a b) · c →v b [ c ]
  cont-⊡ : ∀ k a b                            → (Λ k a) ⊡ b →v a [ b ]
  _·₁_   : ∀ {a₁ a₂} → a₁ →v a₂ → ∀ b         →      a₁ · b →v a₂ · b
  _·₂_   : ∀ {a b₁ b₂} (v : Val a) → b₁ →v b₂ →      a · b₁ →v a · b₂
  _⊡_    : ∀ {a₁ a₂} → a₁ →v a₂ → ∀ b         →      a₁ ⊡ b →v a₂ ⊡ b

reduction : Reduction Term
reduction = record { _→1_ = _→v_ }

-- CBV reduction and equivalence.
open Reduction reduction public renaming (_→*_ to _→v*_; _↔_ to _≡v_)


----------------------------------------------------------------------
-- Simple properties of the CBV reductions/equivalence

-- Inclusions.
→v⇒→v* = →1⇒→* reduction
→v*⇒≡v = →*⇒↔  reduction
→v⇒≡v  = →1⇒↔  reduction

-- CBV reduction is a preorder.
→v*-predorder = →*-preorder reduction

-- Preorder reasoning for CBV reduction.
module →v*-Reasoning = →*-Reasoning reduction

-- Terms together with CBV equivalence form a setoid.
≡v-setoid = ↔-setoid reduction

-- Equational reasoning for CBV equivalence.
module ≡v-Reasoning = ↔-Reasoning reduction


----------------------------------------------------------------------
-- Relationships between CBV reduction and full β-reduction

-- One-step CBV reduction implies one-step β-reduction.
→v⇒→β : ∀ {n} {a b : Term n} → a →v b → a →β b
→v⇒→β (cont-· a b c) = ⌈ cont-Tm· a b _ ⌉
→v⇒→β (cont-⊡ k a b) = ⌈ cont-⊡ k a b ⌉
→v⇒→β (a₁→a₂ ·₁ b) = →v⇒→β a₁→a₂ ·₁ b
→v⇒→β (a ·₂ b₁→b₂) = _ ·₂ →v⇒→β b₁→b₂
→v⇒→β (a₁→a₂ ⊡ b)  = →v⇒→β a₁→a₂ ⊡₁ b

-- CBV reduction implies β-reduction.
→v*⇒→β* : ∀ {n} {a b : Term n} → a →v* b → a →β* b
→v*⇒→β* = map →v⇒→β

-- CBV equivalence implies β-equivalence.
≡v⇒≡β : ∀ {n} {a b : Term n} → a ≡v b → a ≡β b
≡v⇒≡β = EqClos.map →v⇒→β
