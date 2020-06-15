------------------------------------------------------------------------
-- Convenient syntax for relational reasoning using transitive
-- relations
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Relation.Binary.TransReasoning where

open import Level using (suc; _⊔_)
open import Data.Context using (Ctx)
open import Data.Fin.Substitution.Typed using (Typing)
open import Data.Fin.Substitution.TypedRelation using (TypedRel)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_; subst)
open import Relation.Binary
open import Relation.Unary using (Pred)


------------------------------------------------------------------------
-- Transitive relations that are not necessarily reflexive
--
-- Following the convention used in the standard library, we define
-- transitive binary relations using a pair of records (see
-- Relation.Binary).

record IsTransRel {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    trans         : Transitive _∼_

    -- _∼_ respects the underlying equality _≈_.
    --
    -- (This always true for preorders, but not necessarily for
    -- irreflexive relations.)
    ∼-resp-≈      : _∼_ Respects₂ _≈_

  module Eq = IsEquivalence isEquivalence

record TransRel c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isTransRel : IsTransRel _≈_ _∼_

  open IsTransRel isTransRel public

-- Sanity check: every pre-order is a transitive relation in the above
-- sense...
preorderIsTransRel : ∀ {c ℓ₁ ℓ₂} → Preorder c ℓ₁ ℓ₂ → TransRel c ℓ₁ ℓ₂
preorderIsTransRel P = record
 { isTransRel = record
   { isEquivalence = isEquivalence
   ; trans         = trans
   ; ∼-resp-≈      = ∼-resp-≈
   }
 }
 where open IsPreorder (Preorder.isPreorder P)

-- ... and so is every strict partial order.
strictPartialOrderIsTransRel : ∀ {c ℓ₁ ℓ₂} →
                               StrictPartialOrder c ℓ₁ ℓ₂ → TransRel c ℓ₁ ℓ₂
strictPartialOrderIsTransRel SPO = record
 { isTransRel = record
   { isEquivalence = isEquivalence
   ; trans         = trans
   ; ∼-resp-≈      = <-resp-≈
   }
 }
 where open IsStrictPartialOrder (StrictPartialOrder.isStrictPartialOrder SPO)


-- A form of relational reasoning for transitive relations.
--
-- The structure of this module is adapted from the
-- Relation.Binary.PreorderReasoning module of the standard library.
-- It differs from the latter in that
--
--  1. it allows reasoning about relations that are transitive but not
--     reflexive, and
--
--  2. the _IsRelatedTo_ predicate is extended with an additional
--     index that tracks whether elements of the carrier are actually
--     related in the transitive relation _∼_ or just in the
--     underlying equality _≈_.
--
-- Proofs that elements x, y are related as (x IsRelatedTo y In rel)
-- can be converted back to proofs that x ∼ y using begin_, whereas
-- proofs of (x IsRelatedTo y In eq) are too weak to do so.  Since the
-- relation _∼_ is not assumed to be reflexive (i.e. not necessarily a
-- preorder) _∎ can only construct proofs of the weaker form (x ∎ : x
-- IsRelatedTo x In eq).  Consequently, at least one use of _∼⟨_⟩_ is
-- necessary to conclude a proof.

module TransRelReasoning {c ℓ₁ ℓ₂} (R : TransRel c ℓ₁ ℓ₂) where

  open TransRel R

  infix  4 _IsRelatedTo_In_
  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_
  infix  1 begin_

  -- Codes for the relation _∼_ and the underlying equality _≈_.
  data RelC : Set where
    rel eq : RelC

  -- A generic relation combining _∼_ and equality.
  data _IsRelatedTo_In_ (x y : Carrier) : RelC → Set (ℓ₁ ⊔ ℓ₂) where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y In rel
    eqTo  : (x≈y : x ≈ y) → x IsRelatedTo y In eq

  begin_ : ∀ {x y} → x IsRelatedTo y In rel → x ∼ y
  begin (relTo x∼y) = x∼y

  _∼⟨_⟩_ : ∀ x {y z c} → x ∼ y → y IsRelatedTo z In c → x IsRelatedTo z In rel
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)
  _ ∼⟨ x∼y ⟩ eqTo  y≈z = relTo (proj₁ ∼-resp-≈ y≈z x∼y)

  _≈⟨_⟩_ : ∀ x {y z c} → x ≈ y → y IsRelatedTo z In c → x IsRelatedTo z In c
  x ≈⟨ x≈y ⟩ relTo y∼z = relTo (proj₂ ∼-resp-≈ (Eq.sym x≈y) y∼z)
  x ≈⟨ x≈y ⟩ eqTo  y≈z = eqTo (Eq.trans x≈y y≈z)

  _≈⟨⟩_ : ∀ x {y c} → x IsRelatedTo y In c → x IsRelatedTo y In c
  _ ≈⟨⟩ rt-x∼y = rt-x∼y

  _∎ : ∀ x → x IsRelatedTo x In eq
  _ ∎ = eqTo Eq.refl


------------------------------------------------------------------------
-- FIXME: the following should go into a different module (probably
-- into Data.Fin.Substitution.{Typed,TypedRel})

-- A form of pre-order reasoning for transitive relations in a context.
record TransCtxTermRelReasoning {t₁ t₂ ℓ} {T₁ : Pred ℕ t₁} {T₂ : Pred ℕ t₂}
                                (_⊢_∼_ : Typing T₁ T₂ T₂ ℓ)
                                : Set (t₁ ⊔ t₂ ⊔ ℓ) where

  -- Transitivity of _⊢_∼_ for a given context.
  field ∼-trans : ∀ {n} {Γ : Ctx T₁ n} → Transitive (Γ ⊢_∼_)

  module _ {n} {Γ : Ctx T₁ n} where

    ∼-transRel : TransRel _ _ _
    ∼-transRel = record
      { Carrier = T₂ n
      ; _≈_     = _≡_
      ; _∼_     = Γ ⊢_∼_
      ; isTransRel = record
        { isEquivalence = P.isEquivalence
        ; trans         = ∼-trans
        ; ∼-resp-≈      = subst (Γ ⊢ _ ∼_) , subst (Γ ⊢_∼ _)
        }
      }
    open TransRelReasoning ∼-transRel public
      renaming (_≈⟨_⟩_ to _≡⟨_⟩_; _≈⟨⟩_ to _≡⟨⟩_)

-- A form of pre-order reasoning for typed transitive relations.
record TypedTransRelReasoning {t₁ t₂ t₃ ℓ} {T₁ : Pred ℕ t₁}
                              {T₂ : Pred ℕ t₂} {T₃ : Pred ℕ t₃}
                              (_⊢_∼_∈_ : TypedRel T₁ T₂ T₂ T₃ ℓ)
                              : Set (t₁ ⊔ t₂ ⊔ t₃ ⊔ ℓ) where

  -- Transitivity of _⊢_∼_∈_ for a given context and T₃-"type".
  field ∼-trans : ∀ {n} {Γ : Ctx T₁ n} {t} → Transitive (Γ ⊢_∼_∈ t)

  module _ {n} {Γ : Ctx T₁ n} {t : T₃ n} where

    ∼-transRel : TransRel _ _ _
    ∼-transRel = record
      { Carrier = T₂ n
      ; _≈_     = _≡_
      ; _∼_     = Γ ⊢_∼_∈ t
      ; isTransRel = record
        { isEquivalence = P.isEquivalence
        ; trans         = ∼-trans
        ; ∼-resp-≈      = subst (Γ ⊢ _ ∼_∈ _) , subst (Γ ⊢_∼ _ ∈ _)
        }
      }
    open TransRelReasoning ∼-transRel public
      renaming (_≈⟨_⟩_ to _≡⟨_⟩_; _≈⟨⟩_ to _≡⟨⟩_)
