------------------------------------------------------------------------
-- Equivalence of the two variants of declarative kinding of Fω with
-- interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Kinding.Declarative.Equivalence where

open import Data.Product using (proj₁)

open import FOmegaInt.Syntax
import FOmegaInt.Typing                   as Original
open import FOmegaInt.Kinding.Declarative as Extended
open import FOmegaInt.Kinding.Declarative.Validity

private
  module O where
    open Original public
    open Typing   public

  module E where
    open Extended public
    open Kinding  public

open Syntax
open TermCtx
open Kinding
open KindedSubstitution
open Original.Typing
  hiding (_ctx; _⊢_wf; _⊢_kd; _⊢Tp_∈_; _⊢_<∷_; _⊢_<:_∈_; _⊢_≅_; _⊢_≃_∈_)


-- Soundness of extended declarative (sub)kinding w.r.t. original
-- declarative (sub)kinding.
--
-- This soundness proof simply forgets about all the validity
-- conditions in the extended rules.

mutual

  sound-wf : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → Γ O.⊢ a wf
  sound-wf (wf-kd k-kd) = wf-kd (sound-kd k-kd)
  sound-wf (wf-tp a∈*)  = wf-tp (sound-Tp∈ a∈*)

  sound-ctx : ∀ {n} {Γ : Ctx n} → Γ ctx → Γ O.ctx
  sound-ctx E.[]             = O.[]
  sound-ctx (a-wf E.∷ Γ-ctx) = sound-wf a-wf O.∷ sound-ctx Γ-ctx

  sound-kd : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ O.⊢ k kd
  sound-kd (kd-⋯ a∈* b∈*)   = kd-⋯ (sound-Tp∈ a∈*) (sound-Tp∈ b∈*)
  sound-kd (kd-Π j-kd k-kd) = kd-Π (sound-kd j-kd) (sound-kd k-kd)

  sound-Tp∈ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ O.⊢Tp a ∈ k
  sound-Tp∈ (∈-var x Γ-ctx Γ[x]≡kd-k) =
    ∈-var x (sound-ctx Γ-ctx) Γ[x]≡kd-k
  sound-Tp∈ (∈-⊥-f Γ-ctx)         = ∈-⊥-f (sound-ctx Γ-ctx)
  sound-Tp∈ (∈-⊤-f Γ-ctx)         = ∈-⊤-f (sound-ctx Γ-ctx)
  sound-Tp∈ (∈-∀-f k-kd a∈*)      = ∈-∀-f (sound-kd k-kd) (sound-Tp∈ a∈*)
  sound-Tp∈ (∈-→-f a∈* b∈*)       = ∈-→-f (sound-Tp∈ a∈*) (sound-Tp∈ b∈*)
  sound-Tp∈ (∈-Π-i j-kd a∈k k-kd) = ∈-Π-i (sound-kd j-kd) (sound-Tp∈ a∈k)
  sound-Tp∈ (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) =
    ∈-Π-e (sound-Tp∈ a∈Πjk) (sound-Tp∈ b∈j)
  sound-Tp∈ (∈-s-i a∈b⋯c)     = ∈-s-i (sound-Tp∈ a∈b⋯c)
  sound-Tp∈ (∈-⇑ a∈j j<∷k)    = ∈-⇑ (sound-Tp∈ a∈j) (sound-<∷ j<∷k)

  sound-<∷ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ O.⊢ j <∷ k
  sound-<∷ (<∷-⋯ a₂<:a₁∈* b₁<:b₂∈*)      =
    <∷-⋯ (sound-<: a₂<:a₁∈*) (sound-<: b₁<:b₂∈*)
  sound-<∷ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) =
    <∷-Π (sound-<∷ j₂<∷j₁) (sound-<∷ k₁<∷k₂) (sound-kd Πj₁k₁-kd)

  sound-<: : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ∈ k → Γ O.⊢ a <: b ∈ k
  sound-<: (<:-refl a∈k) = <:-refl (sound-Tp∈ a∈k)
  sound-<: (<:-trans a<:b∈k b<:c∈k) =
    <:-trans (sound-<: a<:b∈k) (sound-<: b<:c∈k)
  sound-<: (<:-β₁ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    <:-β₁ (sound-Tp∈ a∈k) (sound-Tp∈ b∈j)
  sound-<: (<:-β₂ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    <:-β₂ (sound-Tp∈ a∈k) (sound-Tp∈ b∈j)
  sound-<: (<:-η₁ a∈Πjk) = <:-η₁ (sound-Tp∈ a∈Πjk)
  sound-<: (<:-η₂ a∈Πjk) = <:-η₂ (sound-Tp∈ a∈Πjk)
  sound-<: (<:-⊥ a∈b⋯c)  = <:-⊥ (sound-Tp∈ a∈b⋯c)
  sound-<: (<:-⊤ a∈b⋯c)  = <:-⊤ (sound-Tp∈ a∈b⋯c)
  sound-<: (<:-∀ k₂<∷k₁ a₁<:a₂∈* ∀k₁a₁∈*) =
    <:-∀ (sound-<∷ k₂<∷k₁) (sound-<: a₁<:a₂∈*) (sound-Tp∈ ∀k₁a₁∈*)
  sound-<: (<:-→ a₂<:a₁∈* b₁<:b₂∈*) =
    <:-→ (sound-<: a₂<:a₁∈*) (sound-<: b₁<:b₂∈*)
  sound-<: (<:-λ a₁<:a₂∈Πjk Λj₁a₁∈Πjk Λj₂a₂∈Πjk) =
    <:-λ (sound-<: a₁<:a₂∈Πjk)
         (sound-Tp∈ Λj₁a₁∈Πjk) (sound-Tp∈ Λj₂a₂∈Πjk)
  sound-<: (<:-· a₁<:a₂∈Πjk b₁≃b₁∈j b₁∈j k-kd k[b₁]-kd) =
    <:-· (sound-<: a₁<:a₂∈Πjk) (sound-≃ b₁≃b₁∈j)
  sound-<: (<:-⟨| a∈b⋯c)        = <:-⟨| (sound-Tp∈ a∈b⋯c)
  sound-<: (<:-|⟩ a∈b⋯c)        = <:-|⟩ (sound-Tp∈ a∈b⋯c)
  sound-<: (<:-⋯-i a₁<:a₂∈b⋯c)  = <:-⋯-i (sound-<: a₁<:a₂∈b⋯c)
  sound-<: (<:-⇑ a₁<:a₂∈j j<∷k) =
    <:-⇑ (sound-<: a₁<:a₂∈j) (sound-<∷ j<∷k)

  sound-≃ : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ∈ k → Γ O.⊢ a ≃ b ∈ k
  sound-≃ (<:-antisym a<:b∈k b<:a∈k) =
    <:-antisym (sound-<: a<:b∈k) (sound-<: b<:a∈k)

sound-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ O.⊢ j ≅ k
sound-≅ (<∷-antisym j<∷k k<∷j) =
  <∷-antisym (sound-<∷ j<∷k) (sound-<∷ k<∷j)

-- Completeness of extended declarative (sub)kinding w.r.t. original
-- declarative (sub)kinding.
--
-- This proves that the validity conditions in the extended rules are
-- in fact redundant, i.e. they follow from validity properties of the
-- remaining premises (of the rules in question)

mutual

  complete-wf : ∀ {n} {Γ : Ctx n} {a} → Γ O.⊢ a wf → Γ ⊢ a wf
  complete-wf (wf-kd k-kd) = wf-kd (complete-kd k-kd)
  complete-wf (wf-tp a∈*)  = wf-tp (complete-Tp∈ a∈*)

  complete-ctx : ∀ {n} {Γ : Ctx n} → Γ O.ctx → Γ ctx
  complete-ctx O.[]             = E.[]
  complete-ctx (a-wf O.∷ Γ-ctx) = complete-wf a-wf E.∷ complete-ctx Γ-ctx

  complete-kd : ∀ {n} {Γ : Ctx n} {k} → Γ O.⊢ k kd → Γ ⊢ k kd
  complete-kd (kd-⋯ a∈* b∈*)   = kd-⋯ (complete-Tp∈ a∈*) (complete-Tp∈ b∈*)
  complete-kd (kd-Π j-kd k-kd) = kd-Π (complete-kd j-kd) (complete-kd k-kd)

  complete-Tp∈ : ∀ {n} {Γ : Ctx n} {a k} → Γ O.⊢Tp a ∈ k → Γ ⊢Tp a ∈ k
  complete-Tp∈ (∈-var x Γ-ctx Γ[x]≡kd-k) =
    ∈-var x (complete-ctx Γ-ctx) Γ[x]≡kd-k
  complete-Tp∈ (∈-⊥-f Γ-ctx)     = ∈-⊥-f (complete-ctx Γ-ctx)
  complete-Tp∈ (∈-⊤-f Γ-ctx)     = ∈-⊤-f (complete-ctx Γ-ctx)
  complete-Tp∈ (∈-∀-f k-kd a∈*)  = ∈-∀-f (complete-kd k-kd) (complete-Tp∈ a∈*)
  complete-Tp∈ (∈-→-f a∈* b∈*)   = ∈-→-f (complete-Tp∈ a∈*) (complete-Tp∈ b∈*)
  complete-Tp∈ (∈-Π-i j-kd a∈k)  =
    ∈-Π-i (complete-kd j-kd) a∈k′ k-kd
    where
      a∈k′ = complete-Tp∈ a∈k
      k-kd = Tp∈-valid a∈k′
  complete-Tp∈ (∈-Π-e a∈Πjk b∈j) with Tp∈-valid (complete-Tp∈ a∈Πjk)
  ... | (kd-Π j-kd k-kd) =
    ∈-Π-e (complete-Tp∈ a∈Πjk) b∈j′ k-kd k[b]-kd
    where
      b∈j′    = complete-Tp∈ b∈j
      k[b]-kd = kd-[] k-kd (∈-tp b∈j′)
  complete-Tp∈ (∈-s-i a∈b⋯c)     = ∈-s-i (complete-Tp∈ a∈b⋯c)
  complete-Tp∈ (∈-⇑ a∈j j<∷k)    = ∈-⇑ (complete-Tp∈ a∈j) (complete-<∷ j<∷k)

  complete-<∷ : ∀ {n} {Γ : Ctx n} {j k} → Γ O.⊢ j <∷ k → Γ ⊢ j <∷ k
  complete-<∷ (<∷-⋯ a₂<:a₁∈* b₁<:b₂∈*)      =
    <∷-⋯ (complete-<: a₂<:a₁∈*) (complete-<: b₁<:b₂∈*)
  complete-<∷ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) =
    <∷-Π (complete-<∷ j₂<∷j₁) (complete-<∷ k₁<∷k₂) (complete-kd Πj₁k₁-kd)

  complete-<: : ∀ {n} {Γ : Ctx n} {a b k} → Γ O.⊢ a <: b ∈ k → Γ ⊢ a <: b ∈ k
  complete-<: (<:-refl a∈k) = <:-refl (complete-Tp∈ a∈k)
  complete-<: (<:-trans a<:b∈k b<:c∈k) =
    <:-trans (complete-<: a<:b∈k) (complete-<: b<:c∈k)
  complete-<: (<:-β₁ a∈k b∈j) =
    <:-β₁ a∈k′ b∈j′ a[b]∈k[b] k-kd k[b]-kd
    where
      a∈k′ = complete-Tp∈ a∈k
      b∈j′ = complete-Tp∈ b∈j
      k-kd = Tp∈-valid a∈k′
      a[b]∈k[b] = Tp∈-[] a∈k′ (∈-tp b∈j′)
      k[b]-kd   = kd-[] k-kd (∈-tp b∈j′)
  complete-<: (<:-β₂ a∈k b∈j) =
    <:-β₂ a∈k′ b∈j′ a[b]∈k[b] k-kd k[b]-kd
    where
      a∈k′ = complete-Tp∈ a∈k
      b∈j′ = complete-Tp∈ b∈j
      k-kd = Tp∈-valid a∈k′
      a[b]∈k[b] = Tp∈-[] a∈k′ (∈-tp b∈j′)
      k[b]-kd   = kd-[] k-kd (∈-tp b∈j′)
  complete-<: (<:-η₁ a∈Πjk) = <:-η₁ (complete-Tp∈ a∈Πjk)
  complete-<: (<:-η₂ a∈Πjk) = <:-η₂ (complete-Tp∈ a∈Πjk)
  complete-<: (<:-⊥ a∈b⋯c)  = <:-⊥ (complete-Tp∈ a∈b⋯c)
  complete-<: (<:-⊤ a∈b⋯c)  = <:-⊤ (complete-Tp∈ a∈b⋯c)
  complete-<: (<:-∀ k₂<∷k₁ a₁<:a₂∈* ∀k₁a₁∈*) =
    <:-∀ (complete-<∷ k₂<∷k₁) (complete-<: a₁<:a₂∈*) (complete-Tp∈ ∀k₁a₁∈*)
  complete-<: (<:-→ a₂<:a₁∈* b₁<:b₂∈*) =
    <:-→ (complete-<: a₂<:a₁∈*) (complete-<: b₁<:b₂∈*)
  complete-<: (<:-λ a₁<:a₂∈Πjk Λj₁a₁∈Πjk Λj₂a₂∈Πjk) =
    <:-λ (complete-<: a₁<:a₂∈Πjk)
         (complete-Tp∈ Λj₁a₁∈Πjk) (complete-Tp∈ Λj₂a₂∈Πjk)
  complete-<: (<:-· a₁<:a₂∈Πjk b₁≃b₁∈j)
    with <:-valid-kd (complete-<: a₁<:a₂∈Πjk)
  ... | (kd-Π j-kd k-kd) =
    <:-· (complete-<: a₁<:a₂∈Πjk) b₁≃b₂∈j′ b₁∈j k-kd k[b₁]-kd
    where
      b₁≃b₂∈j′ = complete-≃ b₁≃b₁∈j
      b₁∈j     = proj₁ (≃-valid b₁≃b₂∈j′)
      k[b₁]-kd = kd-[] k-kd (∈-tp b₁∈j)
  complete-<: (<:-⟨| a∈b⋯c)        = <:-⟨| (complete-Tp∈ a∈b⋯c)
  complete-<: (<:-|⟩ a∈b⋯c)        = <:-|⟩ (complete-Tp∈ a∈b⋯c)
  complete-<: (<:-⋯-i a₁<:a₂∈b⋯c)  = <:-⋯-i (complete-<: a₁<:a₂∈b⋯c)
  complete-<: (<:-⇑ a₁<:a₂∈j j<∷k) =
    <:-⇑ (complete-<: a₁<:a₂∈j) (complete-<∷ j<∷k)

  complete-≃ : ∀ {n} {Γ : Ctx n} {a b k} → Γ O.⊢ a ≃ b ∈ k → Γ ⊢ a ≃ b ∈ k
  complete-≃ (<:-antisym a<:b∈k b<:a∈k) =
    <:-antisym (complete-<: a<:b∈k) (complete-<: b<:a∈k)

complete-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ O.⊢ j ≅ k → Γ ⊢ j ≅ k
complete-≅ (<∷-antisym j<∷k k<∷j) =
  <∷-antisym (complete-<∷ j<∷k) (complete-<∷ k<∷j)
