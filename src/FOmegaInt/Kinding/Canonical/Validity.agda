------------------------------------------------------------------------
-- Validity of canonical kinding in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Kinding.Canonical.Validity where

open import Data.Product using (∃; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Kinding.Canonical
open import FOmegaInt.Kinding.Canonical.HereditarySubstitution as HS
  hiding (Nf⇇-Π-e)

open Syntax
open ElimCtx
open Substitution hiding (subst)
open Kinding
open WfCtxOps
open ContextNarrowing


------------------------------------------------------------------------
-- Validity of canonical kinding, subkinding and subtyping.

-- Validity of spine kinding: the kind of an elimination is
-- well-formed, provided that the spine is well-kinded and the kind of
-- the head is well-formed.

Sp⇉-valid : ∀ {n} {Γ : Ctx n} {as j k} → Γ ⊢ j kd → Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢ k kd
Sp⇉-valid j-kd ⇉-[] = j-kd
Sp⇉-valid (kd-Π j-kd k-kd) (⇉-∷ a⇇j _ k[a]⇉as⇉l) =
  Sp⇉-valid (kd-/⟨⟩ k-kd (⇇-hsub a⇇j j-kd (⌊⌋-⌊⌋≡ _))) k[a]⇉as⇉l

-- Validity of kinding for neutral types: the kinds of neutral types
-- are well-formed.

Ne∈-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Ne a ∈ k → Γ ⊢ k kd
Ne∈-valid (∈-∙ x∈j j⇉as⇉k) = Sp⇉-valid (Var∈-valid x∈j) j⇉as⇉k

-- Validity of spine equality.

Sp≃-valid : ∀ {n} {Γ : Ctx n} {as bs j₁ j₂ k₂} →
            Γ ⊢ j₁ <∷ j₂ → Γ ⊢ j₂ ⇉∙ as ≃ bs ⇉ k₂ →
            ∃ λ k₁ → Γ ⊢ j₂ ⇉∙ as ⇉ k₂ × Γ ⊢ j₁ ⇉∙ bs ⇉ k₁ × Γ ⊢ k₁ <∷ k₂
Sp≃-valid k₁<∷k₂ ≃-[] = _ , ⇉-[] , ⇉-[] , k₁<∷k₂
Sp≃-valid (<∷-Π j₂<∷j₁ k₁<∷k₂ (kd-Π j₁-kd k₁-kd))
          (≃-∷ a≃b⇇j₂ k₂[a]⇉as≃bs⇉l₂) =
  let j₂-kd        = ≃-valid-kd a≃b⇇j₂
      a⇇j₂ , b⇇j₂  = ≃-valid a≃b⇇j₂
      b⇇j₁         = Nf⇇-⇑ b⇇j₂ j₂<∷j₁
      k₁[b]<∷k₂[a] = <∷-/⟨⟩≃ k₁<∷k₂ (≃-hsub (≃-sym a≃b⇇j₂) (⌊⌋-⌊⌋≡ _))
      l₁ , k₂[a]⇉as⇉l₂ , k₁[b]⇉bs⇉l₁ , l₁<∷l₂ = Sp≃-valid k₁[b]<∷k₂[a]
                                                          k₂[a]⇉as≃bs⇉l₂
  in l₁ ,
     ⇉-∷ a⇇j₂ j₂-kd k₂[a]⇉as⇉l₂ ,
     ⇉-∷ b⇇j₁ j₁-kd (subst (λ k → _ ⊢ _ Kind[ _ ∈ k ] ⇉∙ _ ⇉ l₁)
                           (<∷-⌊⌋ j₂<∷j₁) k₁[b]⇉bs⇉l₁) ,
     l₁<∷l₂

-- Validity of subkinding and subtyping: well-formed subkinds
-- resp. well-kinded subtypes are also well-formed resp. well-kinded.

mutual

  <∷-valid : ∀ {n} {Γ : Ctx n} {j k} →
             Γ ⊢ j <∷ k → Γ ⊢ j kd × Γ ⊢ k kd
  <∷-valid (<∷-⋯ a₂<:a₁ b₁<:b₂) =
    let a₂⇉a₂⋯a₂ , a₁⇉a₁⋯a₁ = <:-valid a₂<:a₁
        b₁⇉b₁⋯b₁ , b₂⇉b₂⋯b₂ = <:-valid b₁<:b₂
    in kd-⋯ a₁⇉a₁⋯a₁ b₁⇉b₁⋯b₁ , kd-⋯ a₂⇉a₂⋯a₂ b₂⇉b₂⋯b₂
  <∷-valid (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) =
    let j₂-kd , j₁-kd = <∷-valid j₂<∷j₁
        k₁-kd , k₂-kd = <∷-valid k₁<∷k₂
    in Πj₁k₁-kd , kd-Π j₂-kd k₂-kd

  <:-valid : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a <: b →
             Γ ⊢Nf a ⇉ a ⋯ a × Γ ⊢Nf b ⇉ b ⋯ b
  <:-valid (<:-trans a<:b b<:c) =
    proj₁ (<:-valid a<:b) , proj₂ (<:-valid b<:c)
  <:-valid (<:-⊥ a⇉a⋯a) = ⇉-⊥-f (Nf⇉-ctx a⇉a⋯a) , a⇉a⋯a
  <:-valid (<:-⊤ a⇉a⋯a) = a⇉a⋯a , ⇉-⊤-f (Nf⇉-ctx a⇉a⋯a)
  <:-valid (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) =
    let k₂-kd   , k₁-kd   = <∷-valid  k₂<∷k₁
        a₁⇉a₁⋯a₁ , a₂⇉a₂⋯a₂ = <:-valid a₁<:a₂
    in Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁ , ⇉-∀-f k₂-kd a₂⇉a₂⋯a₂
  <:-valid (<:-→ a₂<:a₁ b₁<:b₂) =
    let a₂⇉a₂⋯a₂ , a₁⇉a₁⋯a₁ = <:-valid a₂<:a₁
        b₁⇉b₁⋯b₁ , b₂⇉b₂⋯b₂ = <:-valid b₁<:b₂
    in ⇉-→-f a₁⇉a₁⋯a₁ b₁⇉b₁⋯b₁ , ⇉-→-f a₂⇉a₂⋯a₂ b₂⇉b₂⋯b₂
  <:-valid (<:-∙ x∈j j⇉as≃bs⇉c⋯d)
    with Sp≃-valid (<∷-refl (Var∈-valid x∈j)) j⇉as≃bs⇉c⋯d
  <:-valid (<:-∙ x∈j j⇉as≃bs⇉c₂⋯d₂)
    | _ , j⇉as⇉c₂⋯d₂ , j⇉bs⇉c₁⋯d₁ , <∷-⋯ c₂<:c₁ d₁<:d₂ =
      ⇉-s-i (∈-∙ x∈j j⇉as⇉c₂⋯d₂) , ⇉-s-i (∈-∙ x∈j j⇉bs⇉c₁⋯d₁)
  <:-valid (<:-⟨| a∈b⋯c) with Ne∈-valid a∈b⋯c
  <:-valid (<:-⟨| a∈b⋯c) | kd-⋯ b⇉b⋯b _ = b⇉b⋯b , ⇉-s-i a∈b⋯c
  <:-valid (<:-|⟩ a∈b⋯c) with Ne∈-valid a∈b⋯c
  <:-valid (<:-|⟩ a∈b⋯c) | kd-⋯ _ c⇉c⋯c = ⇉-s-i a∈b⋯c , c⇉c⋯c

-- Validity of kind checking: if a normal type checks against a kind,
-- then that kind is well-formed.

Nf⇇-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇇ k → Γ ⊢ k kd
Nf⇇-valid (⇇-⇑ a⇉j j<∷k) = proj₂ (<∷-valid j<∷k)


------------------------------------------------------------------------
-- Some corollaries of validity

-- The checked kinds of subtypes are well-formed.

<:⇇-valid-kd : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ⇇ k → Γ ⊢ k kd
<:⇇-valid-kd a<:b⇇k = Nf⇇-valid (proj₁ (<:⇇-valid a<:b⇇k))

-- Canonical kinding of applications is admissible (strong version).

Nf⇇-Π-e : ∀ {n} {Γ : Ctx n} {a b j k} →
          Γ ⊢Nf a ⇇ Π j k → Γ ⊢Nf b ⇇ j →
          Γ ⊢Nf a ⌜·⌝⟨ ⌊ Π j k ⌋ ⟩ b ⇇ k Kind[ b ∈ ⌊ j ⌋ ]
Nf⇇-Π-e a⇇Πjk b⇇j = HS.Nf⇇-Π-e a⇇Πjk b⇇j (Nf⇇-valid b⇇j) (⌊⌋-⌊⌋≡ _)

-- Canonical subtyping of applications is admissible.

<:-⌜·⌝ : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j k} →
         Γ ⊢ a₁ <: a₂ ⇇ Π j k → Γ ⊢ b₁ ≃ b₂ ⇇ j →
         Γ ⊢ a₁ ⌜·⌝⟨ ⌊ Π j k ⌋ ⟩ b₁ <: a₂ ⌜·⌝⟨ ⌊ Π j k ⌋ ⟩ b₂ ⇇
           k Kind[ b₁ ∈ ⌊ j ⌋ ]
<:-⌜·⌝ a₁<:a₂⇇Πjk b₁≃b₂⇇j with <:⇇-valid-kd a₁<:a₂⇇Πjk
<:-⌜·⌝ (<:-λ a₁<:a₂⇇k Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) b₁≃b₂⇇j | (kd-Π _ k-kd) =
  <:⇇-/⟨⟩≃ a₁<:a₂⇇k k-kd (≃-hsub b₁≃b₂⇇j (⌊⌋-⌊⌋≡ _))

-- Subtyping of proper types checks against the kind of proper types.

<:-⋯-* : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a <: b → Γ ⊢ a <: b ⇇ ⌜*⌝
<:-⋯-* a<:b with <:-valid a<:b
<:-⋯-* a<:b | a⇉a⋯a , b⇉b⋯b = <:-⇇ (Nf⇉-⋯-* a⇉a⋯a) (Nf⇉-⋯-* b⇉b⋯b) a<:b

-- Some commonly used (hereditary) substitution lemmas.

kd-[] : ∀ {n} {Γ : Ctx n} {a j k} →
        kd k ∷ Γ ⊢ j kd → Γ ⊢Nf a ⇇ k → Γ ⊢ j Kind[ a ∈ ⌊ k ⌋ ] kd
kd-[] j-kd a⇇k = kd-/⟨⟩ j-kd (⇇-hsub a⇇k (Nf⇇-valid a⇇k) (⌊⌋-⌊⌋≡ _))

Nf⇇-[] : ∀ {n} {Γ : Ctx n} {a b j k} →
         kd j ∷ Γ ⊢Nf a ⇇ k → Γ ⊢Nf b ⇇ j →
         Γ ⊢Nf a [ b ∈ ⌊ j ⌋ ] ⇇ k Kind[ b ∈ ⌊ j ⌋ ]
Nf⇇-[] a⇇k b⇇j = Nf⇇-/⟨⟩ a⇇k (⇇-hsub b⇇j (Nf⇇-valid b⇇j) (⌊⌋-⌊⌋≡ _))

<∷-[≃] : ∀ {n} {Γ : Ctx n} {j k₁ k₂ a₁ a₂} →
         kd j ∷ Γ ⊢ k₁ <∷ k₂ → Γ ⊢ a₁ ≃ a₂ ⇇ j →
         Γ ⊢ k₁ Kind[ a₁ ∈ ⌊ j ⌋ ] <∷ k₂ Kind[ a₂ ∈ ⌊ j ⌋ ]
<∷-[≃] k₁<∷k₂ a₁≃a₂⇇j =
  <∷-/⟨⟩≃ k₁<∷k₂ (≃-hsub a₁≃a₂⇇j (⌊⌋-⌊⌋≡ _))

<:-[≃] : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j k} →
         kd j ∷ Γ ⊢ a₁ <: a₂ ⇇ k → Γ ⊢ b₁ ≃ b₂ ⇇ j →
         Γ ⊢ a₁ [ b₁ ∈ ⌊ j ⌋ ] <: a₂ [ b₂ ∈ ⌊ j ⌋ ] ⇇ k Kind[ b₁ ∈ ⌊ j ⌋ ]
<:-[≃] a₁<:a₂⇇k b₁≃b₂⇇j =
  <:⇇-/⟨⟩≃ a₁<:a₂⇇k (<:⇇-valid-kd a₁<:a₂⇇k) (≃-hsub b₁≃b₂⇇j (⌊⌋-⌊⌋≡ _))

-- Another admissible kinding rule for applications.

Nf⇇-Π-e′ : ∀ {n} {Γ : Ctx n} {a b j k} →
           Γ ⊢Nf a ⇇ Π j k → Γ ⊢Nf b ⇇ j →
           Γ ⊢Nf a ↓⌜·⌝ b ⇇ k Kind[ b ∈ ⌊ j ⌋ ]
Nf⇇-Π-e′ {b = b} (⇇-⇑ (⇉-Π-i {_} {a₁} j₁-kd a⇉k₁) (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd))
         b⇇j₂ =
  subst (_ ⊢Nf_⇇ _) (cong (a₁ [ b ∈_]) (<∷-⌊⌋ j₂<∷j₁))
        (Nf⇇-[] (⇇-⇑ (⇓-Nf⇉ (Nf⇇-valid b⇇j₂) j₂<∷j₁ a⇉k₁) k₁<∷k₂) b⇇j₂)

-- Another admissible subtyping rule for applications.

<:-↓⌜·⌝ : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j k} →
         Γ ⊢ a₁ <: a₂ ⇇ Π j k → Γ ⊢ b₁ ≃ b₂ ⇇ j →
         Γ ⊢ a₁ ↓⌜·⌝ b₁ <: a₂ ↓⌜·⌝ b₂ ⇇ k Kind[ b₁ ∈ ⌊ j ⌋ ]
<:-↓⌜·⌝ {b₁ = b₁} {b₂}
        (<:-λ a₁<:a₂⇇k (⇇-⇑ (⇉-Π-i {_} {a₁} _ _) (<∷-Π j₁<∷j _ _))
                       (⇇-⇑ (⇉-Π-i {_} {a₂} _ _) (<∷-Π j₂<∷j _ _))) b₁≃b₂⇇j =
  subst₂ (_ ⊢_<:_⇇ _)
         (cong (a₁ [ b₁ ∈_]) (<∷-⌊⌋ j₁<∷j)) (cong (a₂ [ b₂ ∈_]) (<∷-⌊⌋ j₂<∷j))
         (<:-[≃] a₁<:a₂⇇k b₁≃b₂⇇j)
