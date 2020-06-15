------------------------------------------------------------------------
-- Validity of declarative kinding of Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Kinding.Declarative.Validity where

open import Data.Fin using (zero)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Product as Prod using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import FOmegaInt.Syntax
open import FOmegaInt.Kinding.Declarative


------------------------------------------------------------------------
-- Validity of declarative kinding, subkinding and subtyping

open Syntax
open Substitution hiding (subst)
open TermCtx
open Kinding
open WfCtxOps using (lookup-kd)
open KindedSubstitution
open WfSubstitutionEquality

-- An admissible rule for kinding η-expanded type operators.
Tp∈-η : ∀ {n} {Γ : Ctx n} {a j k} →
        Γ ⊢Tp a ∈ Π j k → Γ ⊢ j kd → kd j ∷ Γ ⊢ k kd →
        Γ ⊢Tp Λ j (weaken a · var zero) ∈ Π j k
Tp∈-η {k = k} a∈Πjk j-kd k-kd =
  ∈-Π-i j-kd (subst (_ ⊢Tp _ ∈_) k′[z]≡k (∈-Π-e a∈Πjk′ z∈k k-kd′ k[z]-kd)) k-kd
  where
    module KL = TermLikeLemmas termLikeLemmasKind

    j-wf    = wf-kd j-kd
    j-kd′   = kd-weaken j-wf j-kd
    k-kd′   = kd-/Var k-kd (Var∈-↑ (wf-kd j-kd′) (Var∈-wk j-wf))
    z∈k     = ∈-var zero (j-wf ∷ kd-ctx j-kd) refl
    a∈Πjk′  = Tp∈-weaken j-wf a∈Πjk
    k[z]-kd = kd-[] k-kd′ (∈-tp z∈k)
    k′[z]≡k = Kind-wk↑-sub-zero-vanishes k

mutual

  -- Validity of kinding: the kinds of well-kinded types are well-formed.
  Tp∈-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ k kd
  Tp∈-valid (∈-var x Γ-ctx Γ[x]≡kd-k) = lookup-kd x Γ-ctx Γ[x]≡kd-k
  Tp∈-valid (∈-⊥-f Γ-ctx)             = *-kd Γ-ctx
  Tp∈-valid (∈-⊤-f Γ-ctx)             = *-kd Γ-ctx
  Tp∈-valid (∈-∀-f k-kd a∈*)          = *-kd (kd-ctx k-kd)
  Tp∈-valid (∈-→-f a∈* b∈*)           = *-kd (Tp∈-ctx a∈*)
  Tp∈-valid (∈-Π-i j-kd a∈k k-kd)     = kd-Π j-kd (Tp∈-valid a∈k)
  Tp∈-valid (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) = k[b]-kd
  Tp∈-valid (∈-s-i a∈b⋯c)             = let a∈* = Tp∈-⋯-* a∈b⋯c in kd-⋯ a∈* a∈*
  Tp∈-valid (∈-⇑ a∈j j<∷k)            = proj₂ (<∷-valid j<∷k)

  -- Validity of subkinding: subkinds are well-formed.
  <∷-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ ⊢ j kd × Γ ⊢ k kd
  <∷-valid (<∷-⋯ a₂<:a₁∈* b₁<:b₂∈*)      =
    let a₂∈* , a₁∈* = <:-valid a₂<:a₁∈*
        b₁∈* , b₂∈* = <:-valid b₁<:b₂∈*
    in kd-⋯ a₁∈* b₁∈* , kd-⋯ a₂∈* b₂∈*
  <∷-valid (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) =
    Πj₁k₁-kd ,
    kd-Π (proj₁ (<∷-valid j₂<∷j₁)) (proj₂ (<∷-valid k₁<∷k₂))

  -- Validity of subtyping: subtypes that are related in some kind `k'
  -- inhabit `k'.
  <:-valid : ∀ {n} {Γ : Ctx n} {a b k} →
             Γ ⊢ a <: b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
  <:-valid (<:-refl a∈k)            = a∈k , a∈k
  <:-valid (<:-trans a<:b∈k b<:c∈k) =
    proj₁ (<:-valid a<:b∈k) , proj₂ (<:-valid b<:c∈k)
  <:-valid (<:-β₁ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    ∈-Π-e (∈-Π-i j-kd a∈k k-kd) b∈j k-kd k[b]-kd , a[b]∈k[b]
    where j-kd = wf-kd-inv (wf-∷₁ (Tp∈-ctx a∈k))
  <:-valid (<:-β₂ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    a[b]∈k[b] , ∈-Π-e (∈-Π-i j-kd a∈k k-kd) b∈j k-kd k[b]-kd
    where j-kd = wf-kd-inv (wf-∷₁ (Tp∈-ctx a∈k))
  <:-valid (<:-η₁ a∈Πjk) with Tp∈-valid a∈Πjk
  ... | (kd-Π j-kd k-kd) = Tp∈-η a∈Πjk j-kd k-kd , a∈Πjk
  <:-valid (<:-η₂ a∈Πjk) with Tp∈-valid a∈Πjk
  ... | (kd-Π j-kd k-kd) = a∈Πjk , Tp∈-η a∈Πjk j-kd k-kd
  <:-valid (<:-⊥ b∈c⋯d) = ∈-⊥-f (Tp∈-ctx b∈c⋯d) , Tp∈-⋯-* b∈c⋯d
  <:-valid (<:-⊤ b∈c⋯d) = Tp∈-⋯-* b∈c⋯d , ∈-⊤-f (Tp∈-ctx b∈c⋯d)
  <:-valid (<:-∀ k₂<∷k₁ a₁<:a₂∈* ∀k₁a₁∈*) =
    ∀k₁a₁∈* ,
    ∈-∀-f (proj₁ (<∷-valid k₂<∷k₁)) (proj₂ (<:-valid a₁<:a₂∈*))
  <:-valid (<:-→ a₂<:a₁∈* b₁<:b₂∈*) =
    let a₂∈* , a₁∈* = <:-valid a₂<:a₁∈*
        b₁∈* , b₂∈* = <:-valid b₁<:b₂∈*
    in ∈-→-f a₁∈* b₁∈* , ∈-→-f a₂∈* b₂∈*
  <:-valid (<:-λ a₁<:a₂∈k Λj₁a₁∈Πjk Λj₂a₂∈Πjk) = Λj₁a₁∈Πjk , Λj₂a₂∈Πjk
  <:-valid (<:-· a₁<:a₂∈Πjk b₁≃b₂∈j b₁∈j k-kd k[b₁]-kd) =
    let a₁∈Πjk , a₂∈Πjk = <:-valid a₁<:a₂∈Πjk
        b₁∈j   , b₂∈j   = ≃-valid  b₁≃b₂∈j
    in ∈-Π-e a₁∈Πjk b₁∈j k-kd k[b₁]-kd ,
       ∈-⇑ (∈-Π-e a₂∈Πjk b₂∈j k-kd (kd-[] k-kd (∈-tp b₂∈j)))
           (≅⇒<∷ (kd-[≃′] k-kd b₂∈j b₁∈j (≃-sym b₁≃b₂∈j)))
  <:-valid (<:-⟨| a∈b⋯c) with Tp∈-valid a∈b⋯c
  ... | (kd-⋯ b∈* c∈*) = b∈* , Tp∈-⋯-* a∈b⋯c
  <:-valid (<:-|⟩ a∈b⋯c) with Tp∈-valid a∈b⋯c
  ... | (kd-⋯ b∈* c∈*) = Tp∈-⋯-* a∈b⋯c , c∈*
  <:-valid (<:-⋯-i a<:b∈c⋯d) =
    let a∈c⋯d , b∈c⋯d = <:-valid a<:b∈c⋯d
        a<:b∈*        = <:-⋯-*   a<:b∈c⋯d
    in ∈-⇑ (∈-s-i a∈c⋯d) (<∷-⋯ (<:-refl (Tp∈-⋯-* a∈c⋯d)) a<:b∈*) ,
       ∈-⇑ (∈-s-i b∈c⋯d) (<∷-⋯ a<:b∈* (<:-refl (Tp∈-⋯-* b∈c⋯d)))
  <:-valid (<:-⇑ a<:b∈j j<∷k) =
    let a∈j , b∈j = <:-valid a<:b∈j
    in ∈-⇑ a∈j j<∷k , ∈-⇑ b∈j j<∷k

  -- Validity of type equality: types that are equal in some kind `k'
  -- inhabit `k'.
  ≃-valid : ∀ {n} {Γ : Ctx n} {a b k} →
            Γ ⊢ a ≃ b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
  ≃-valid (<:-antisym a<:b∈k b<:a∈k) = <:-valid a<:b∈k

  -- Subtypes inhabiting interval kinds are proper types.
  <:-⋯-* : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a <: b ∈ c ⋯ d → Γ ⊢ a <: b ∈ *
  <:-⋯-* a<:b∈c⋯d =
    let a∈c⋯d , b∈c⋯d = <:-valid a<:b∈c⋯d
    in <:-⇑ (<:-⋯-i a<:b∈c⋯d) (<∷-⋯ (<:-⊥ a∈c⋯d) (<:-⊤ b∈c⋯d))

-- Validity of kind equality: equal kinds are well-formed.
≅-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ j kd × Γ ⊢ k kd
≅-valid (<∷-antisym j<∷k k<∷j) = <∷-valid j<∷k

-- A corollary.
<:-valid-kd : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ∈ k → Γ ⊢ k kd
<:-valid-kd a<:b∈k = Tp∈-valid (proj₁ (<:-valid a<:b∈k))


----------------------------------------------------------------------
-- Strengthened versions of kind formation and kinding functionality.

-- Functionality of kind formation (strong version).
kd-[≃] : ∀ {n} {Γ : Ctx n} {a b j k} →
         kd j ∷ Γ ⊢ k kd → Γ ⊢ a ≃ b ∈ j → Γ ⊢ k Kind[ a ] ≅ k Kind[ b ]
kd-[≃] k-kd a≃b∈j = let a∈j , b∈j = ≃-valid a≃b∈j in kd-[≃′] k-kd a∈j b∈j a≃b∈j

-- Functionality of kinding (strong version).
Tp∈-[≃] : ∀ {n} {Γ : Ctx n} {a b c j k} →
          kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢ b ≃ c ∈ j →
          Γ ⊢ a [ b ] ≃ a [ c ] ∈ k Kind[ b ]
Tp∈-[≃] a∈k b≃c∈j = let b∈j , c∈j = ≃-valid b≃c∈j in Tp∈-[≃′] a∈k b∈j c∈j b≃c∈j
