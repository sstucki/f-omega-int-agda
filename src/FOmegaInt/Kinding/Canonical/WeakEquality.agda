------------------------------------------------------------------------
-- Lifting of weak equality to canonical equality
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Kinding.Canonical.WeakEquality where

open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Syntax.WeakEquality
open import FOmegaInt.Kinding.Canonical
open import FOmegaInt.Kinding.Canonical.HereditarySubstitution


------------------------------------------------------------------------
-- Lifting of weak kind/type equality into canonical equality.
--
-- The lemmas below state that a variant of reflexivity is admissible
-- in canonical subkinding, subtyping as well as kind and type
-- equality, which uses weak equality (instead of syntactic equality)
-- along with proofs of canonical well-formedness
-- resp. well-kindedness of *both* the kinds resp. types being
-- related.

open Syntax
open ElimCtx
open Kinding
open ContextNarrowing

-- Lifting of weak kind/type equality into canonical
-- subkinding/subtyping and type/kind equality.

mutual

  ≋-<∷ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j kd → Γ ⊢ k kd → j ≋ k → Γ ⊢ j <∷ k
  ≋-<∷ (kd-⋯ a₁⇉a₁⋯a₁ b₁⇉b₁⋯b₁) (kd-⋯ a₂⇉a₂⋯a₂ b₂⇉b₂⋯b₂) (≋-⋯ a₁≈a₂ b₁≈b₂) =
    <∷-⋯ (≈-<: a₂⇉a₂⋯a₂ a₁⇉a₁⋯a₁ (≈-sym a₁≈a₂)) (≈-<: b₁⇉b₁⋯b₁ b₂⇉b₂⋯b₂ b₁≈b₂)
  ≋-<∷ (kd-Π j₁-kd k₁-kd) (kd-Π j₂-kd k₂-kd) (≋-Π j₁≋j₂ k₁≋k₂) =
    let j₂<∷j₁ = ≋-<∷ j₂-kd j₁-kd (≋-sym j₁≋j₂)
    in <∷-Π j₂<∷j₁ (≋-<∷ (⇓-kd j₂-kd j₂<∷j₁ k₁-kd) k₂-kd k₁≋k₂)
            (kd-Π j₁-kd k₁-kd)

  ≈-<: : ∀ {n} {Γ : Ctx n} {a b} →
         Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢Nf b ⇉ b ⋯ b → a ≈ b → Γ ⊢ a <: b
  ≈-<: (⇉-⊥-f Γ-ctx) (⇉-⊥-f _)  (≈-∙ ≈-⊥ ≈-[]) = <:-⊥ (⇉-⊥-f Γ-ctx)
  ≈-<: (⇉-⊥-f _)     (⇉-s-i ()) (≈-∙ ≈-⊥ ≈-[])
  ≈-<: (⇉-⊤-f Γ-ctx) (⇉-⊤-f _)  (≈-∙ ≈-⊤ ≈-[]) = <:-⊤ (⇉-⊤-f Γ-ctx)
  ≈-<: (⇉-⊤-f _)     (⇉-s-i ()) (≈-∙ ≈-⊤ ≈-[])
  ≈-<: (⇉-∀-f k₁-kd a₁⇉a₁⋯a₁) (⇉-∀-f k₂-kd a₂⇉a₂⋯a₂)
       (≈-∙ (≈-∀ k₁≋k₂ a₁≈a₂) ≈-[]) =
    let k₂<∷k₁ = ≋-<∷ k₂-kd k₁-kd (≋-sym k₁≋k₂)
    in <:-∀ k₂<∷k₁ (≈-<: (⇓-Nf⇉ k₂-kd k₂<∷k₁ a₁⇉a₁⋯a₁) a₂⇉a₂⋯a₂ a₁≈a₂)
            (⇉-∀-f k₁-kd a₁⇉a₁⋯a₁)
  ≈-<: (⇉-∀-f _ _) (⇉-s-i ()) (≈-∙ (≈-∀ _ _) ≈-[])
  ≈-<: (⇉-→-f a₁⇉a₁⋯a₁ b₁⇉b₁⋯b₁) (⇉-→-f a₂⇉a₂⋯a₂ b₂⇉b₂⋯b₂)
       (≈-∙ (≈-→ a₁≈a₂ b₁≈b₂) ≈-[]) =
    <:-→ (≈-<: a₂⇉a₂⋯a₂ a₁⇉a₁⋯a₁ (≈-sym a₁≈a₂)) (≈-<: b₁⇉b₁⋯b₁ b₂⇉b₂⋯b₂ b₁≈b₂)
  ≈-<: (⇉-→-f _ _) (⇉-s-i ()) (≈-∙ (≈-→ _ _) ≈-[])
  ≈-<: (⇉-s-i (∈-∙ x∈j₁ j₁⇉as₁⇉k₁)) (⇉-s-i (∈-∙ x∈j₂ j₂⇉as₂⇉k₂))
       (≈-∙ (≈-var x) as₁≈as₂) =
    let j  , Γ[x]≡kd-j  , j<∷j₁  , j-kd , _ = Var∈-inv x∈j₁
        j′ , Γ[x]≡kd-j′ , j′<∷j₂ , _    , _ = Var∈-inv x∈j₂
        j′≡j  = kd-inj (trans (sym Γ[x]≡kd-j′) Γ[x]≡kd-j)
        j<∷j₂ = subst (_ ⊢_<∷ _) j′≡j j′<∷j₂
        c , d , j⇉as₁≃as₂⇉c⋯d = ≈Sp-Sp≃ j-kd j<∷j₁ j<∷j₂
                                        j₁⇉as₁⇉k₁ j₂⇉as₂⇉k₂ as₁≈as₂
    in <:-∙ (⇉-var x (Var∈-ctx x∈j₁) Γ[x]≡kd-j) j⇉as₁≃as₂⇉c⋯d

  ≈-<:⇇ : ∀ {n} {Γ : Ctx n} {a b j} →
          Γ ⊢ j kd → Γ ⊢Nf a ⇇ j → Γ ⊢Nf b ⇇ j → a ≈ b → Γ ⊢ a <: b ⇇ j
  ≈-<:⇇ b⋯c-kd
        (⇇-⇑ a₁⇉b₁⋯c₁ (<∷-⋯ b<:b₁ c₁<:c))
        (⇇-⇑ a₂⇉b₂⋯c₂ (<∷-⋯ b<:b₂ c₂<:c)) a₁≈a₂ =
    <:-⇇ (⇇-⇑ a₁⇉b₁⋯c₁ (<∷-⋯ b<:b₁ c₁<:c)) (⇇-⇑ a₂⇉b₂⋯c₂ (<∷-⋯ b<:b₂ c₂<:c))
         (≈-<: (Nf⇉-s-i a₁⇉b₁⋯c₁) (Nf⇉-s-i a₂⇉b₂⋯c₂) a₁≈a₂)
  ≈-<:⇇ (kd-Π j-kd k-kd)
        (⇇-⇑ (⇉-Π-i j₁-kd a₁⇉k₁) (<∷-Π j<∷j₁ k₁<∷k Πj₁k₁-kd))
        (⇇-⇑ (⇉-Π-i j₂-kd a₂⇉k₂) (<∷-Π j<∷j₂ k₂<∷k Πj₂k₂-kd))
        (≈-∙ (≈-Λ ⌊k₁⌋≡⌊k₂⌋ a₁≈a₂) ≈-[]) =
    let a₁⇇k = ⇇-⇑ (⇓-Nf⇉ j-kd j<∷j₁ a₁⇉k₁) k₁<∷k
        a₂⇇k = ⇇-⇑ (⇓-Nf⇉ j-kd j<∷j₂ a₂⇉k₂) k₂<∷k
        a₁<:a₂⇇k = ≈-<:⇇ k-kd a₁⇇k a₂⇇k a₁≈a₂
    in <:-λ a₁<:a₂⇇k
            (⇇-⇑ (⇉-Π-i j₁-kd a₁⇉k₁) (<∷-Π j<∷j₁ k₁<∷k Πj₁k₁-kd))
            (⇇-⇑ (⇉-Π-i j₂-kd a₂⇉k₂) (<∷-Π j<∷j₂ k₂<∷k Πj₂k₂-kd))

  ≈Sp-Sp≃ : ∀ {n} {Γ : Ctx n} {as₁ as₂ j j₁ j₂ b₁ b₂ c₁ c₂} →
            Γ ⊢ j kd → Γ ⊢ j <∷ j₁ → Γ ⊢ j <∷ j₂ →
            Γ ⊢ j₁ ⇉∙ as₁ ⇉ b₁ ⋯ c₁ → Γ ⊢ j₂ ⇉∙ as₂ ⇉ b₂ ⋯ c₂ → as₁ ≈Sp as₂ →
            ∃ λ b → ∃ λ c → Γ ⊢ j ⇉∙ as₁ ≃ as₂ ⇉ b ⋯ c
  ≈Sp-Sp≃ j-kd (<∷-⋯ b₁<:b c<:c₁) j<∷b₂⋯c₂ ⇉-[] ⇉-[] ≈-[] = _ , _ , ≃-[]
  ≈Sp-Sp≃ (kd-Π j-kd k-kd)
          (<∷-Π j₁<∷j k<∷k₁ Πj₁k₁-kd) (<∷-Π j₂<∷j k<∷k₂ Πj₂k₂-kd)
          (⇉-∷ a₁⇇j₁ j₁-kd k₁[a₁]⇉bs₁⇉c₁⋯d₁)
          (⇉-∷ a₂⇇j₂ j₂-kd k₂[a₂]⇉bs₂⇉c₂⋯d₂) (≈-∷ a₁≈a₂ bs₁≈bs₂) =
    let a₁⇇j     = Nf⇇-⇑ a₁⇇j₁ j₁<∷j
        k[a₁]-kd = TK.kd-/⟨⟩ k-kd (⇇-hsub a₁⇇j j-kd (⌊⌋-⌊⌋≡ _))
        a₁≃a₂⇇j  = ≈-≃ j-kd a₁⇇j (Nf⇇-⇑ a₂⇇j₂ j₂<∷j) a₁≈a₂
        k[a₁]<∷k₁[a₁] = subst (λ l → _ ⊢ _ Kind[ _ ∈ l ] <∷ _) (<∷-⌊⌋ j₁<∷j)
                              (TK.<∷-/⟨⟩≃ k<∷k₁ (⇇-hsub a₁⇇j₁ j₁-kd (⌊⌋-⌊⌋≡ _)))
        k[a₂]<∷k₂[a₂] = subst (λ l → _ ⊢ _ Kind[ _ ∈ l ] <∷ _) (<∷-⌊⌋ j₂<∷j)
                              (TK.<∷-/⟨⟩≃ k<∷k₂ (⇇-hsub a₂⇇j₂ j₂-kd (⌊⌋-⌊⌋≡ _)))
        k[a₁]<∷k[a₂]  = TK.kd-/⟨⟩≃-<∷ k-kd (≃-hsub a₁≃a₂⇇j (⌊⌋-⌊⌋≡ _))
        k[a₁]<∷k₂[a₂] = <∷-trans k[a₁]<∷k[a₂] k[a₂]<∷k₂[a₂]
        c , d , k[a₁]⇉bs₁≃bs₂⇉c⋯d = ≈Sp-Sp≃ k[a₁]-kd k[a₁]<∷k₁[a₁] k[a₁]<∷k₂[a₂]
                                            k₁[a₁]⇉bs₁⇉c₁⋯d₁ k₂[a₂]⇉bs₂⇉c₂⋯d₂
                                            bs₁≈bs₂
    in c , d , ≃-∷ a₁≃a₂⇇j k[a₁]⇉bs₁≃bs₂⇉c⋯d
    where
      module TK = TrackSimpleKindsSubst

  ≈-≃ : ∀ {n} {Γ : Ctx n} {a b j} →
        Γ ⊢ j kd → Γ ⊢Nf a ⇇ j → Γ ⊢Nf b ⇇ j → a ≈ b → Γ ⊢ a ≃ b ⇇ j
  ≈-≃ j-kd a⇇j b⇇j a≈b =
    <:-antisym j-kd (≈-<:⇇ j-kd a⇇j b⇇j a≈b) (≈-<:⇇ j-kd b⇇j a⇇j (≈-sym a≈b))

  ≋-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j kd → Γ ⊢ k kd → j ≋ k → Γ ⊢ j ≅ k
  ≋-≅ j-kd k-kd j≋k =
    <∷-antisym j-kd k-kd (≋-<∷ j-kd k-kd j≋k) (≋-<∷ k-kd j-kd (≋-sym j≋k))
