------------------------------------------------------------------------
-- Full β-reduction in pure type systems (PTS)
------------------------------------------------------------------------

module FOmegaInt.Reduction.Full where

open import Data.Fin using (suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.List using ([]; _∷_)
open import Data.Star using (ε; _◅_; gmap)
open import Data.Sum using ([_,_])
open import Data.Product using (_,_; ∃; _×_)
open import Function using (flip; _∘_)
open import Relation.Binary using (Setoid; Preorder)
import Relation.Binary.EquivalenceClosure as EqClos
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
import Relation.Binary.SymmetricClosure as SymClos
open import Relation.Binary.Reduction
import Function.Equivalence as Equiv

open import FOmegaInt.Syntax

open Syntax       hiding (⌈_⌉)
open Substitution using (_[_]; weaken)

----------------------------------------------------------------------
-- Full β-reduction and equality relations

infixl 9  _·₁_ _·₂_ _⊡₁_ _⊡₂_
infixr 7  _⇒₁_ _⇒₂_
infix  6  _⋯₁_ _⋯₂_
infix  5  _→β_ _Kd→β_ _→βη_ _Kd→βη_

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

-- β-contraction together with η-expansion of neutral types.
data BetaContEtaExp {n} : Term n → Term n → Set where
  cont-Tp· : ∀ k a b → BetaContEtaExp ((Λ k a) · b) (a [ b ])
  cont-Tm· : ∀ a b c → BetaContEtaExp ((ƛ a b) · c) (b [ c ])
  cont-⊡   : ∀ k a b → BetaContEtaExp ((Λ k a) ⊡ b) (a [ b ])
  exp-var  : ∀ k x   → BetaContEtaExp (var x) (Λ k (var (suc x)    · var zero))
  exp-·    : ∀ k a b → BetaContEtaExp (a · b) (Λ k (weaken (a · b) · var zero))

-- One-step β-reduction.

_→β_ : TRel Term
_→β_ = Compat BetaCont

_Kd→β_ : TRel (Kind Term)
_Kd→β_ = KdCompat BetaCont

-- One-step β-reduction and η-expansion.

_→βη_ : TRel Term
_→βη_ = Compat BetaContEtaExp

_Kd→βη_ : TRel (Kind Term)
_Kd→βη_ = KdCompat BetaContEtaExp

-- Full β-reduction and equality.

β-reduction : Reduction Term
β-reduction = record { _→1_ = _→β_ }

β-reductionKind : Reduction (Kind Term)
β-reductionKind = record { _→1_ = _Kd→β_ }

open Reduction β-reduction public hiding (_→1_)
  renaming (_→*_ to _→β*_; _↔_ to _≡β_)

open Reduction β-reductionKind public hiding (_→1_)
  renaming (_→*_ to _Kd→β*_; _↔_ to _Kd≡β_)

-- Full β-reduction, η-expansion of neutrals, and βη-equality.

βη-reductionExpansion : Reduction Term
βη-reductionExpansion = record { _→1_ = _→βη_ }

βη-reductionExpansionKind : Reduction (Kind Term)
βη-reductionExpansionKind = record { _→1_ = _Kd→βη_ }

open Reduction βη-reductionExpansion public hiding (_→1_)
  renaming (_→*_ to _→βη*_; _↔_ to _≡βη_)

open Reduction βη-reductionExpansionKind public hiding (_→1_)
  renaming (_→*_ to _Kd→βη*_; _↔_ to _Kd≡βη_)

----------------------------------------------------------------------
-- Simple properties of the β-reductions/equalities

-- Inclusions.

BetaCont⇒BetaContEtaExp : ∀ {n} {a b : Term n} →
                          BetaCont a b → BetaContEtaExp a b
BetaCont⇒BetaContEtaExp (cont-Tp· k a b) = cont-Tp· k a b
BetaCont⇒BetaContEtaExp (cont-Tm· a b c) = cont-Tm· a b c
BetaCont⇒BetaContEtaExp (cont-⊡   k a b) = cont-⊡   k a b

module CompatInclusion (_∼₁_ _∼₂_ : TRel Term) where

  mutual

    →₁⇒→₂ : (∀ {n} {a b : Term n} → a ∼₁ b → a ∼₂ b) →
             ∀ {n} {a b : Term n} → Compat _∼₁_ a b → Compat _∼₂_ a b
    →₁⇒→₂ ∼₁⇒∼₂ ⌈ a∼₁b ⌉      = ⌈ ∼₁⇒∼₂ a∼₁b ⌉
    →₁⇒→₂ ∼₁⇒∼₂ (Π₁ k₁→₁k₂ a) = Π₁ (Kd→₁⇒→₂ ∼₁⇒∼₂ k₁→₁k₂) a
    →₁⇒→₂ ∼₁⇒∼₂ (Π₂ k a₁→₁a₂) = Π₂ k (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂)
    →₁⇒→₂ ∼₁⇒∼₂ (a₁→₁a₂ ⇒₁ b) = (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂) ⇒₁ b
    →₁⇒→₂ ∼₁⇒∼₂ (a ⇒₂ b₁→₁b₂) = a ⇒₂ (→₁⇒→₂ ∼₁⇒∼₂ b₁→₁b₂)
    →₁⇒→₂ ∼₁⇒∼₂ (Λ₁ k₁→₁k₂ a) = Λ₁ (Kd→₁⇒→₂ ∼₁⇒∼₂ k₁→₁k₂) a
    →₁⇒→₂ ∼₁⇒∼₂ (Λ₂ k a₁→₁a₂) = Λ₂ k (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂)
    →₁⇒→₂ ∼₁⇒∼₂ (ƛ₁ a₁→₁a₂ b) = ƛ₁ (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂) b
    →₁⇒→₂ ∼₁⇒∼₂ (ƛ₂ a b₁→₁b₂) = ƛ₂ a (→₁⇒→₂ ∼₁⇒∼₂ b₁→₁b₂)
    →₁⇒→₂ ∼₁⇒∼₂ (a₁→₁a₂ ·₁ b) = (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂) ·₁ b
    →₁⇒→₂ ∼₁⇒∼₂ (a ·₂ b₁→₁b₂) = a ·₂ (→₁⇒→₂ ∼₁⇒∼₂ b₁→₁b₂)
    →₁⇒→₂ ∼₁⇒∼₂ (a₁→₁a₂ ⊡₁ b) = (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂) ⊡₁ b
    →₁⇒→₂ ∼₁⇒∼₂ (a ⊡₂ b₁→₁b₂) = a ⊡₂ (→₁⇒→₂ ∼₁⇒∼₂ b₁→₁b₂)

    Kd→₁⇒→₂ : (∀ {n} {a b : Term n} → a ∼₁ b → a ∼₂ b) →
               ∀ {n} {j k : Kind Term n} → KdCompat _∼₁_ j k → KdCompat _∼₂_ j k
    Kd→₁⇒→₂ ∼₁⇒∼₂ (a₁→₁a₂ ⋯₁ b) = (→₁⇒→₂ ∼₁⇒∼₂ a₁→₁a₂) ⋯₁ b
    Kd→₁⇒→₂ ∼₁⇒∼₂ (a ⋯₂ b₁→₁b₂) = a ⋯₂ (→₁⇒→₂ ∼₁⇒∼₂ b₁→₁b₂)
    Kd→₁⇒→₂ ∼₁⇒∼₂ (Π₁ j₁→₁j₂ k) = Π₁ (Kd→₁⇒→₂ ∼₁⇒∼₂ j₁→₁j₂) k
    Kd→₁⇒→₂ ∼₁⇒∼₂ (Π₂ j k₁→₁k₂) = Π₂ j (Kd→₁⇒→₂ ∼₁⇒∼₂ k₁→₁k₂)

→β⇒→βη = CompatInclusion.→₁⇒→₂ BetaCont BetaContEtaExp BetaCont⇒BetaContEtaExp

→β*⇒→βη* : ∀ {n} {a b : Term n} → a →β* b → a →βη* b
→β*⇒→βη* = gmap Function.id →β⇒→βη

≡β⇒≡βη : ∀ {n} {a b : Term n} → a ≡β b → a ≡βη b
≡β⇒≡βη = EqClos.map →β⇒→βη

→β⇒→β* = →1⇒→* β-reduction
→β*⇒≡β = →*⇒↔  β-reduction
→β⇒≡β  = →1⇒↔  β-reduction

→βη⇒→βη* = →1⇒→* βη-reductionExpansion
→βη*⇒≡βη = →*⇒↔  βη-reductionExpansion
→βη⇒≡βη  = →1⇒↔  βη-reductionExpansion

-- The reductions are preorders.

→β*-preorder   = →*-preorder β-reduction
Kd→β*-preorder = →*-preorder β-reductionKind

→βη*-preorder   = →*-preorder βη-reductionExpansion
Kd→βη*-preorder = →*-preorder βη-reductionExpansionKind

-- Preorder reasoning for the reductions.

module →β*-Reasoning    = →*-Reasoning β-reduction
module Kd→β*-Reasoning  = →*-Reasoning β-reductionKind

module →βη*-Reasoning   = →*-Reasoning βη-reductionExpansion
module Kd→βη*-Reasoning = →*-Reasoning βη-reductionExpansionKind

-- Raw terms and kinds together with β/βη-equality form setoids.

≡β-setoid   = ↔-setoid β-reduction
Kd≡β-setoid = ↔-setoid β-reductionKind

≡βη-setoid   = ↔-setoid βη-reductionExpansion
Kd≡βη-setoid = ↔-setoid βη-reductionExpansionKind

-- Equational reasoning for the equalities.

module ≡β-Reasoning   = ↔-Reasoning β-reduction
module Kd≡β-Reasoning = ↔-Reasoning β-reductionKind

module ≡βη-Reasoning   = ↔-Reasoning βη-reductionExpansion
module Kd≡βη-Reasoning = ↔-Reasoning βη-reductionExpansionKind

-- An admissible expansion rule for neutral terms.
exp-ne : ∀ {n} (k : Kind Term n) x as →
         BetaContEtaExp (var x ⌞∙⌟ as) (Λ k (weaken (var x ⌞∙⌟ as) · var zero))
exp-ne k x [] =
  P.subst (λ a → BetaContEtaExp (var x) (Λ k (a · var zero)))
          (P.sym weaken-var) (exp-var k x)
  where open Substitution using (weaken-var)
exp-ne k x (a ∷ as) with helper (var x) a as
  where
    helper : ∀ {n} (a b : Term n) bs →
             ∃ λ c → ∃ λ d → a ⌞∙⌟ (b ∷ bs) ≡ c · d
    helper a b []       = a , b , refl
    helper a b (c ∷ cs) = helper (a · b) c cs
... | c , d , x·a∙as≡c·d =
  P.subst (λ a → BetaContEtaExp a (Λ k (weaken a · var zero)))
          (P.sym x·a∙as≡c·d) (exp-· k c d)

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

open CongLemmas BetaContEtaExp public renaming
  ( →1-⌞∙⌟₁ to →βη-⌞∙⌟₁
  ; →*-Π    to →βη*-Π
  ; →*-⇒    to →βη*-⇒
  ; →*-Λ    to →βη*-Λ
  ; →*-ƛ    to →βη*-ƛ
  ; →*-·    to →βη*-·
  ; →*-⊡    to →βη*-⊡
  ; Kd→*-⋯  to Kd→βη*-⋯
  ; Kd→*-Π  to Kd→βη*-Π
  ; →*-⌞∙⌟₁ to →βη*-⌞∙⌟₁
  ; ↔-Π     to ≡βη-Π
  ; ↔-⇒     to ≡βη-⇒
  ; ↔-Λ     to ≡βη-Λ
  ; ↔-ƛ     to ≡βη-ƛ
  ; ↔-·     to ≡βη-·
  ; ↔-⊡     to ≡βη-⊡
  ; Kd↔-⋯   to Kd≡βη-⋯
  ; Kd↔-Π   to Kd≡βη-Π
  ; ↔-⌞∙⌟₁  to ≡βη-⌞∙⌟₁
  )

-- Shapes of type constructors are preserved by β-reduction and
-- η-expansion.

Π-→βη* : ∀ {n} {k : Kind Term n} {a b} → Π k a →βη* b →
         ∃ λ k′ → ∃ λ a′ → k Kd→βη* k′ × a →βη* a′ × Π k′ a′ ≡ b
Π-→βη* ε                     = _ , _ , ε , ε , refl
Π-→βη* (⌈ () ⌉ ◅ _)
Π-→βη* (Π₁ k₁→k₂ a ◅ Πk₂a→b) =
  let k′ , a′ , k₂→k′ , a→a′ , Πk′a′≡b = Π-→βη* Πk₂a→b
  in k′ , a′ , k₁→k₂ ◅ k₂→k′ , a→a′ , Πk′a′≡b
Π-→βη* (Π₂ k a₁→a₂ ◅ Πka₂→b) =
  let k′ , a′ , k→k′ , a₂→a′ , Πk′a′≡b = Π-→βη* Πka₂→b
  in k′ , a′ , k→k′ , a₁→a₂ ◅ a₂→a′ , Πk′a′≡b

⇒-→βη* : ∀ {n} {a : Term n} {b c} → a ⇒ b →βη* c →
         ∃ λ a′ → ∃ λ b′ → a →βη* a′ × b →βη* b′ × a′ ⇒ b′ ≡ c
⇒-→βη* ε                     = _ , _ , ε , ε , refl
⇒-→βη* (⌈ () ⌉ ◅ _)
⇒-→βη* (a₁→a₂ ⇒₁ b ◅ a⇒₂b→c) =
  let a′ , b′ , a₂→a′ , b→b′ , a⇒′b′≡c = ⇒-→βη* a⇒₂b→c
  in a′ , b′ , a₁→a₂ ◅ a₂→a′ , b→b′ , a⇒′b′≡c
⇒-→βη* (a ⇒₂ b₁→b₂ ◅ a⇒b₂→c) =
  let a′ , b′ , a→a′ , b₂→b′ , a⇒′b′≡c = ⇒-→βη* a⇒b₂→c
  in a′ , b′ , a→a′ , b₁→b₂ ◅ b₂→b′ , a⇒′b′≡c
