------------------------------------------------------------------------
-- Inversion of canonical subtyping in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Kinding.Canonical.Inversion where

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Vec using ([]; _∷_; foldl)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Relation.Nullary using (¬_)

open import FOmegaInt.Syntax
open import FOmegaInt.Kinding.Canonical
open import FOmegaInt.Kinding.Canonical.Validity

open Syntax
open ElimCtx
open Kinding
open ContextNarrowing


------------------------------------------------------------------------
-- Inversion of canonical subtyping (in the empty context).

-- NOTE.  The lemmas in this module only hold in the empty context
-- because we can not invert instances of the interval projection
-- rules (<:-⟨| and (<:-|⟩) in arbitrary contexts.  This is because
-- instances of these rules can reflect arbitrary subtyping
-- assumptions into the subtyping relation.  Consider, e.g.
--
--     Γ, X :: ⊤..⊥ ctx    Γ(X) = ⊥..⊤
--     ------------------------------- (∈-var)
--     Γ, X :: ⊤..⊥ ⊢ X :: ⊤..⊥
--     -------------------------- (<:-⟨|, <:-|⟩)
--     Γ, X :: ⊤..⊥ ⊢ ⊤ <: X <: ⊥
--
-- Which allows us to prove that ⊤ <: ⊥ using (<:-trans) under the
-- assumption (X : ⊤..⊥).  On the other hand, it is impossible to give
-- a transitivity-free proof of ⊤ <: ⊥.  In general, it is therefore
-- impossible to invert subtyping statements in non-empty contexts,
-- i.e. one cannot prove lemmas like (<:-→-inv) or (<:-∀-inv) below
-- for arbitrary contexts.

infix 4 ⊢_<!_

-- Top-level transitivity-free canonical subtyping in the empty
-- context.
data ⊢_<!_ : Elim 0 → Elim 0 → Set where
  <!-⊥ : ∀ {a} → [] ⊢Nf a ⇉ a ⋯ a → ⊢ ⊥∙ <! a
  <!-⊤ : ∀ {a} → [] ⊢Nf a ⇉ a ⋯ a → ⊢ a  <! ⊤∙
  <!-∀ : ∀ {k₁ k₂ a₁ a₂} → [] ⊢ k₂ <∷ k₁ → kd k₂ ∷ [] ⊢ a₁ <: a₂ →
         [] ⊢Nf ∀∙ k₁ a₁ ⇉ ∀∙ k₁ a₁ ⋯ ∀∙ k₁ a₁ → ⊢ ∀∙ k₁ a₁ <! ∀∙ k₂ a₂
  <!-→ : ∀ {a₁ a₂ b₁ b₂} → [] ⊢ a₂ <: a₁ → [] ⊢ b₁ <: b₂ →
         ⊢ a₁ ⇒∙ b₁ <! a₂ ⇒∙ b₂

-- Soundness of <! with respect to <: in the empty context.
sound-<! : ∀ {a b : Elim 0} → ⊢ a <! b → [] ⊢ a <: b
sound-<! (<!-⊥ a⇉a⋯a)         = <:-⊥ a⇉a⋯a
sound-<! (<!-⊤ a⇉a⋯a)         = <:-⊤ a⇉a⋯a
sound-<! (<!-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) =
  <:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁
sound-<! (<!-→ a₂<:a₁ b₁<:b₂) = <:-→ a₂<:a₁ b₁<:b₂

-- The only proper (top-level) subtype of ⊥ is ⊥ itself.
⊥-<!-min : ∀ {a : Elim 0} → ⊢ a <! ⊥∙ → a ≡ ⊥∙
⊥-<!-min (<!-⊥ _) = refl

-- The only proper (top-level) supertype of ⊤ is ⊤ itself.
⊤-<!-max : ∀ {a : Elim 0} → ⊢ ⊤∙ <! a → a ≡ ⊤∙
⊤-<!-max (<!-⊤ _) = refl

-- Arrows are not (top-level) subtypes of universals and vice-versa.

⇒-≮!-Π : ∀ {a : Elim 0} {k b₁ b₂} → ¬ ⊢ a ⇒∙ b₁ <! ∀∙ k b₂
⇒-≮!-Π ()

Π-≮!-⇒ : ∀ {a : Elim 0} {k b₁ b₂} → ¬ ⊢ ∀∙ k b₁ <! a ⇒∙ b₂
Π-≮!-⇒ ()

-- Validity of <!
<!-valid : ∀ {a b} → ⊢ a <! b → [] ⊢Nf a ⇉ a ⋯ a × [] ⊢Nf b ⇉ b ⋯ b
<!-valid a<!b = <:-valid (sound-<! a<!b)

-- Top-level transitivity of canonical subtyping is admissible.
<!-trans : ∀ {a b c} → [] ⊢ a <: b → ⊢ b <! c → ⊢ a <! c
<!-trans (<:-trans a<:b b<:c) c<!d = <!-trans a<:b (<!-trans b<:c c<!d)
<!-trans (<:-⊥ a⇉a⋯a) a<!d     = <!-⊥ (proj₂ (<!-valid a<!d))
<!-trans (<:-⊤ a⇉a⋯a) (<!-⊤ _) = <!-⊤ a⇉a⋯a
<!-trans (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) (<!-⊤ _) =
  <!-⊤ (proj₁ (<:-valid (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁)))
<!-trans (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) (<!-∀ k₃<∷k₂ a₂<:a₃ _) =
  <!-∀ (<∷-trans k₃<∷k₂ k₂<∷k₁)
       (<:-trans (⇓-<: k₃-kd k₃<∷k₂ a₁<:a₂) a₂<:a₃) Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁
  where k₃-kd = wf-kd-inv (wf-∷₁ (<:-ctx a₂<:a₃))
<!-trans (<:-→ a₂<:a₁ b₁<:b₂) (<!-⊤ a₂⇒b₂⇉a₂⇒b₂⋯a₂⇒b₂) =
  <!-⊤ (proj₁ (<:-valid (<:-→ a₂<:a₁ b₁<:b₂)))
<!-trans (<:-→ a₂<:a₁ b₁<:b₂) (<!-→ a₃<:a₂ b₂<:b₃) =
  <!-→ (<:-trans a₃<:a₂ a₂<:a₁) (<:-trans b₁<:b₂ b₂<:b₃)
<!-trans (<:-∙ {()} _ _)        b<!c
<!-trans (<:-⟨| (∈-∙ {()} _ _)) b<!c
<!-trans (<:-|⟩ (∈-∙ {()} _ _)) b<!c

-- Completeness of <! with respect to <: in the empty context.
complete-<! : ∀ {a b : Elim 0} → [] ⊢ a <: b → ⊢ a <! b
complete-<! (<:-trans a<:b b<:c) = <!-trans a<:b (complete-<! b<:c)
complete-<! (<:-⊥ a⇉a⋯a)         = <!-⊥ a⇉a⋯a
complete-<! (<:-⊤ a⇉a⋯a)         = <!-⊤ a⇉a⋯a
complete-<! (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) =
  <!-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁
complete-<! (<:-→ a₂<:a₁ b₁<:b₂) = <!-→ a₂<:a₁ b₁<:b₂
complete-<! (<:-∙ {()} _ _)
complete-<! (<:-⟨| (∈-∙ {()} _ _))
complete-<! (<:-|⟩ (∈-∙ {()} _ _))

-- The only proper (top-level) subtype of ⊥ is ⊥ itself.
⊥-<:-min : ∀ {a : Elim 0} → [] ⊢ a <: ⊥∙ → a ≡ ⊥∙
⊥-<:-min a<:⊥ = ⊥-<!-min (complete-<! a<:⊥)

-- The only proper (top-level) supertype of ⊤ is ⊤ itself.
⊤-<:-max : ∀ {a : Elim 0} → [] ⊢ ⊤∙ <: a → a ≡ ⊤∙
⊤-<:-max ⊤<:a = ⊤-<!-max (complete-<! ⊤<:a)

-- Inversion of canonical subtyping for universals and arrow types.

<:-∀-inv : ∀ {k₁ k₂ : Kind Elim 0} {a₁ a₂} → [] ⊢ ∀∙ k₁ a₁ <: ∀∙ k₂ a₂ →
           [] ⊢ k₂ <∷ k₁ × kd k₂ ∷ [] ⊢ a₁ <: a₂
<:-∀-inv Πk₁a₁<:Πk₂a₂ with complete-<! Πk₁a₁<:Πk₂a₂
<:-∀-inv Πk₁a₁<:Πk₂a₂ | <!-∀ k₂<∷k₁ a₁<:a₂ _ = k₂<∷k₁ , a₁<:a₂

<:-→-inv : ∀ {a₁ a₂ : Elim 0} {b₁ b₂} → [] ⊢ a₁ ⇒∙ b₁ <: a₂ ⇒∙ b₂ →
           [] ⊢ a₂ <: a₁ × [] ⊢ b₁ <: b₂
<:-→-inv a₁⇒b₁<:a₂⇒b₂ with complete-<! a₁⇒b₁<:a₂⇒b₂
<:-→-inv a₁⇒b₁<:a₂⇒b₂ | <!-→ a₂<∷a₁ b₁<:b₂ = a₂<∷a₁ , b₁<:b₂

-- Arrows are not canonical subtypes of universals and vice-versa.

⇒-≮:-Π : ∀ {a : Elim 0} {k b₁ b₂} → ¬ [] ⊢ a ⇒∙ b₁ <: ∀∙ k b₂
⇒-≮:-Π = ⇒-≮!-Π ∘ complete-<!

Π-≮:-⇒ : ∀ {a : Elim 0} {k b₁ b₂} → ¬ [] ⊢ ∀∙ k b₁ <: a ⇒∙ b₂
Π-≮:-⇒ = Π-≮!-⇒ ∘ complete-<!
