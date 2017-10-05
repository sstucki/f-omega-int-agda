------------------------------------------------------------------------
-- Convenient syntax for relational reasoning using transitive
-- relations
------------------------------------------------------------------------

module Relation.Binary.TransReasoning where

open import Level using (suc; _⊔_)
open import Data.Fin.Substitution.Context using (Ctx)
open import Data.Fin.Substitution.Typed using (CtxTermRel)
open import Data.Fin.Substitution.TypedParallel using (TypedRel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Rel; Transitive)


-- A form of relational reasoning for transitive relations.
--
-- NOTE. The structure of this module is adapted from the
-- Relation.Binary.PreorderReasoning module of the Agda standard
-- library.  It differs from the latter in that
--
--  1. we fix the underlying equality to be _≡_, and
--
--  2. the _IsRelatedTo_ predicate is extended with an additional
--     index that tracks whether elements of the carrier are actually
--     related in the transitive relation _∼_ or just in _≡_.
--
-- Proofs that elements x, y are related as (x IsRelatedTo y In rel)
-- can be converted back to proofs that x ∼ y using begin_, where as
-- proofs of (x IsRelatedTo y In eq) are too weak to do so.  Since the
-- relation _∼_ is not assumed to be reflexive (i.e. not necessarily a
-- pre-order) _∎ can only construct proofs of the weaker form (x ∎ : x
-- IsRelatedTo x In eq).  Consequently, at least one use of _∼⟨_⟩_ is
-- necessary to conclude a proof.
--
-- TODO.
--
--  1. This module should be refactored to follow the style of the
--     standard library by separating the record containing the
--     transitivity law ~-trans (i.e. the "structure" of the
--     transitive relation) form the reasoning module itself.
--
--  2. The module should be generalized to allow for other underlying
--     equalities _≈_ that compose with _∼_.
record TransRelReasoning {a b} {T : Set a}
                         (_∼_ : Rel T b) : Set (suc (a ⊔ b)) where

  -- Transitivity of _∼_.
  field ∼-trans : Transitive _∼_

  infix  4 _IsRelatedTo_In_
  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix  1 begin_

  -- Codes for the relation _∼_ and the underlying equality _≡_.
  data RelC : Set where
    rel eq : RelC

  -- A generic relation combining _∼_ and equality.
  data _IsRelatedTo_In_ (x y : T) : RelC → Set (a ⊔ b) where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y In rel
    eqTo  : (x≡y : x ≡ y) → x IsRelatedTo y In eq

  begin_ : ∀ {x y} → x IsRelatedTo y In rel → x ∼ y
  begin (relTo x∼y) = x∼y

  _∼⟨_⟩_ : ∀ x {y z c} → x ∼ y → y IsRelatedTo z In c → x IsRelatedTo z In rel
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (∼-trans x∼y y∼z)
  _ ∼⟨ x∼y ⟩ eqTo  y≡z  = relTo (subst (_ ∼_) y≡z x∼y)

  _≡⟨_⟩_ : ∀ x {y z c} → x ≡ y → y IsRelatedTo z In c → x IsRelatedTo z In c
  _ ≡⟨ x≡y ⟩ rt-y∼z = subst (_IsRelatedTo _ In _) (sym x≡y) rt-y∼z

  _≡⟨⟩_ : ∀ x {y c} → x IsRelatedTo y In c → x IsRelatedTo y In c
  _ ≡⟨⟩ rt-x∼y = rt-x∼y

  _∎ : ∀ x → x IsRelatedTo x In eq
  _ ∎ = eqTo refl

-- FIXME: the following should go into a different module (probably
-- into Data.Fin.Substitution.{Typed,TypedParallel})

-- A form of pre-order reasoning for transitive relations in a context.
record TransCtxTermRelReasoning {T₁ T₂}
                                (_⊢_∼_ : CtxTermRel T₁ T₂ T₂) : Set₁ where
  -- Transitivity of _⊢_∼_∈_ for a given context.
  field ∼-trans : ∀ {n} {Γ : Ctx T₁ n} → Transitive (Γ ⊢_∼_)

  module _ {n} {Γ : Ctx T₁ n} where

    ∼-reasoning : TransRelReasoning (Γ ⊢_∼_)
    ∼-reasoning = record { ∼-trans = ∼-trans }
    open TransRelReasoning ∼-reasoning public hiding (∼-trans)

-- A form of pre-order reasoning for typed transitive relations.
record TypedTransRelReasoning {T₁ T₂ T₃}
                              (_⊢_∼_∈_ : TypedRel T₁ T₂ T₂ T₃) : Set₁ where
  -- Transitivity of _⊢_∼_∈_ for a given context and T₃-"type".
  field ∼-trans : ∀ {n} {Γ : Ctx T₁ n} {t} → Transitive (Γ ⊢_∼_∈ t)

  module _ {n} {Γ : Ctx T₁ n} {t : T₃ n} where

    ∼-reasoning : TransRelReasoning (Γ ⊢_∼_∈ t)
    ∼-reasoning = record { ∼-trans = ∼-trans }
    open TransRelReasoning ∼-reasoning public hiding (∼-trans)
