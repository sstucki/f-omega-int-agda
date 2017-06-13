------------------------------------------------------------------------
-- Inversion of (sub)typing in Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Typing.Inversion where

open import Data.Product using (_,_; proj₁; proj₂; _×_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import FOmegaInt.Syntax
open import FOmegaInt.Typing
import FOmegaInt.Kinding.Declarative.Validity  as DeclVal
import FOmegaInt.Kinding.Declarative.Inversion as DeclInv
open import FOmegaInt.Kinding.Declarative.Equivalence
  using (sound-kd; sound-Tp∈; sound-<∷; sound-<:; complete-Tp∈; complete-<:)
open Syntax
open TermCtx hiding (map)
open Typing
open Substitution using (_[_]; weaken)
open WfCtxOps using (lookup-tp)
open TypedSubstitution


------------------------------------------------------------------------
-- Validity of kinding, subtyping and typing.

-- Validity of kinding: the kinds of well-kinded types are well-formed.
Tp∈-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ k kd
Tp∈-valid a∈k = sound-kd (DeclVal.Tp∈-valid (complete-Tp∈ a∈k))

-- Validity of subtyping: subtypes that are related in some kind `k'
-- inhabit `k'.
<:-valid : ∀ {n} {Γ : Ctx n} {a b k} →
           Γ ⊢ a <: b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
<:-valid a<:b∈k =
  map sound-Tp∈ sound-Tp∈ (DeclVal.<:-valid (complete-<: a<:b∈k))

-- Validity of typing: the types of well-typed terms are well-kinded.
Tm∈-valid : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢Tm a ∈ b → Γ ⊢Tp b ∈ *
Tm∈-valid (∈-var x Γ-ctx Γ[x]≡tp-a) = lookup-tp x Γ-ctx Γ[x]≡tp-a
Tm∈-valid (∈-∀-i k-kd a∈b)    = ∈-∀-f k-kd (Tm∈-valid a∈b)
Tm∈-valid (∈-→-i a∈* b∈c c∈*) = ∈-→-f a∈* c∈*
Tm∈-valid (∈-∀-e a∈∀kc b∈k)   =
  let k-kd , c∈* = Tp∈-∀-inv (Tm∈-valid a∈∀kc)
  in Tp∈-[] c∈* (∈-tp b∈k)
Tm∈-valid (∈-→-e a∈c⇒d b∈c)   =
  let c∈* , d∈* = Tp∈-→-inv (Tm∈-valid a∈c⇒d)
  in d∈*
Tm∈-valid (∈-⇑ a∈b b<:c)      = proj₂ (<:-valid b<:c)


------------------------------------------------------------------------
-- Generation/inversion of typing.

infix 4 _⊢Tm-gen_∈_

-- The possible types of a term (i.e. the possible results of
-- generating/inverting _⊢Tp_∈_).
data _⊢Tm-gen_∈_ {n} (Γ : Ctx n) : Term n → Term n → Set where
  ∈-var : ∀ {a b} x → Γ ctx → lookup x Γ ≡ tp a → Γ ⊢ a <: b ∈ * →
          Γ ⊢Tm-gen var x ∈ b
  ∈-∀-i : ∀ {k a b c} → Γ ⊢ k kd → kd k ∷ Γ ⊢Tm a ∈ b → Γ ⊢ Π k b <: c ∈ * →
          Γ ⊢Tm-gen Λ k a ∈ c
  ∈-→-i : ∀ {a b c d} → Γ ⊢Tp a ∈ * → tp a ∷ Γ ⊢Tm b ∈ weaken c →
          Γ ⊢ a ⇒ c <: d ∈ * → Γ ⊢Tm-gen ƛ a b ∈ d
  ∈-∀-e : ∀ {a b k c d} → Γ ⊢Tm a ∈ Π k c → Γ ⊢Tp b ∈ k → Γ ⊢ c [ b ] <: d ∈ * →
          Γ ⊢Tm-gen a ⊡ b ∈ d
  ∈-→-e : ∀ {a b c d e} → Γ ⊢Tm a ∈ c ⇒ d → Γ ⊢Tm b ∈ c → Γ ⊢ d <: e ∈ * →
          Γ ⊢Tm-gen a · b ∈ e

-- Generation/inversion of typing.
Tm∈-gen : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢Tm a ∈ b → Γ ⊢Tm-gen a ∈ b
Tm∈-gen (∈-var x Γ-ctx Γ[x]≡kd-a) =
  ∈-var x Γ-ctx Γ[x]≡kd-a (<:-refl (Tm∈-valid (∈-var x Γ-ctx Γ[x]≡kd-a)))
Tm∈-gen (∈-∀-i k-kd a∈b) =
  ∈-∀-i k-kd a∈b (<:-refl (Tm∈-valid (∈-∀-i k-kd a∈b)))
Tm∈-gen (∈-→-i a∈* b∈c c∈*) =
  ∈-→-i a∈* b∈c (<:-refl (Tm∈-valid (∈-→-i a∈* b∈c c∈*)))
Tm∈-gen (∈-∀-e a∈∀kc b∈k) =
  ∈-∀-e a∈∀kc b∈k (<:-refl (Tm∈-valid (∈-∀-e a∈∀kc b∈k)))
Tm∈-gen (∈-→-e a∈c⇒d b∈c) =
  ∈-→-e a∈c⇒d b∈c (<:-refl (Tm∈-valid (∈-→-e a∈c⇒d b∈c)))
Tm∈-gen (∈-⇑ a∈b   b<:c) with Tm∈-gen a∈b
Tm∈-gen (∈-⇑ x∈b   c<:d) | ∈-var x Γ-ctx Γ[x]≡kd-a a<:b =
  ∈-var x Γ-ctx Γ[x]≡kd-a (<:-trans a<:b c<:d)
Tm∈-gen (∈-⇑ Λka∈b b<:c) | ∈-∀-i k-kd a∈d ∀kd<:b   =
  ∈-∀-i k-kd a∈d (<:-trans ∀kd<:b b<:c)
Tm∈-gen (∈-⇑ ƛab∈c c<:d) | ∈-→-i a∈* b∈c a⇒c<:d    =
  ∈-→-i a∈* b∈c (<:-trans a⇒c<:d c<:d)
Tm∈-gen (∈-⇑ a·b∈e e<:f) | ∈-∀-e a∈Πcd b∈c d[b]<:e =
  ∈-∀-e a∈Πcd b∈c (<:-trans d[b]<:e e<:f)
Tm∈-gen (∈-⇑ a·b∈e e<:f) | ∈-→-e a∈c⇒d b∈c d<:e    =
  ∈-→-e a∈c⇒d b∈c (<:-trans d<:e e<:f)


------------------------------------------------------------------------
-- Inversion of subtyping (in the empty context).

-- NOTE.  The following two lemmas only hold in the empty context
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

<:-∀-inv : ∀ {k₁ k₂ : Kind Term 0} {a₁ a₂} → [] ⊢ Π k₁ a₁ <: Π k₂ a₂ ∈ * →
           [] ⊢ k₂ <∷ k₁ × kd k₂ ∷ [] ⊢ a₁ <: a₂ ∈ *
<:-∀-inv ∀k₁a₁<:∀k₂a₂∈* =
  map sound-<∷ sound-<: (DeclInv.<:-∀-inv (complete-<: ∀k₁a₁<:∀k₂a₂∈*))

<:-→-inv : ∀ {a₁ a₂ b₁ b₂ : Term 0} → [] ⊢ a₁ ⇒ b₁ <: a₂ ⇒ b₂ ∈ * →
           [] ⊢ a₂ <: a₁ ∈ * × [] ⊢ b₁ <: b₂ ∈ *
<:-→-inv a₁⇒b₁<:a₂⇒b₂∈* =
  map sound-<: sound-<: (DeclInv.<:-→-inv (complete-<: a₁⇒b₁<:a₂⇒b₂∈*))

-- Arrows are not canonical subtypes of universals and vice-versa.

⇒-≮:-Π : ∀ {a₁ b₁ : Term 0} {k₂ a₂} → ¬ [] ⊢ a₁ ⇒ b₁ <: Π k₂ a₂ ∈ *
⇒-≮:-Π a₁⇒b₁<:∀k₂a₂∈* = DeclInv.⇒-≮:-Π (complete-<: a₁⇒b₁<:∀k₂a₂∈*)

Π-≮:-⇒ : ∀ {k₁ a₁} {a₂ b₂ : Term 0} → ¬ [] ⊢ Π k₁ a₁ <: a₂ ⇒ b₂ ∈ *
Π-≮:-⇒ ∀k₁a₁<:a₂⇒b₂∈* = DeclInv.Π-≮:-⇒ (complete-<: ∀k₁a₁<:a₂⇒b₂∈*)
