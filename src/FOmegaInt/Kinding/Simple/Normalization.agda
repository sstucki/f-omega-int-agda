------------------------------------------------------------------------
-- Normalization/simplification of kinding in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Kinding.Simple.Normalization where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution using (module VarSubst)
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Context.Properties
open import Data.List using ([]; _∷_; _∷ʳ_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (_,_)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProp
open import Function using (flip; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution
  renaming (sub to hsub; _↑ to _H↑)
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Syntax.WeakEquality
open import FOmegaInt.Kinding.Simple as Simple
open import FOmegaInt.Kinding.Simple.EtaExpansion
open import FOmegaInt.Kinding.Declarative as Declarative

------------------------------------------------------------------------
-- Normalization/simplification of kinded types to simply kinded
-- types.
--
-- TODO: explain the point of this and how "simple" kinding differs
-- from "canonical" kinding.

open Syntax
open TermCtx
open SimpleCtx    using (kd; tp; ⌊_⌋Asc; kd-inj′)
open Substitution hiding (subst)
open ContextConversions
open RenamingCommutesNorm
open WeakHereditarySubstitutionEquality
open WeakEqEtaExpansion
open WeakEqNormalization
open KindedHereditarySubstitution
open Simple.Kinding
open Declarative.Kinding

private
  module S where
    open Simple.Kinding public
    open SimpleCtx      public
    open SimplyWfCtx    public
  module D where
    open Declarative.Kinding public
    open TermCtx             public
  module E = ElimCtx

mutual

  -- Normalization and simultaneous simplification of kinding:
  -- well-kinded types normalize to simply kinded normal forms.
  nf-Tp∈ : ∀ {n} {Γ : Ctx n} {a k} →
           let Γ′ = nfCtx Γ in Γ ⊢Tp a ∈ k → ⌊ Γ′ ⌋Ctx ⊢Nf nf Γ′ a ∈ ⌊ k ⌋
  nf-Tp∈ {_} {Γ} (∈-var {j} x Γ-ctx Γ[x]≡kd-k)
    with E.lookup x (nfCtx Γ) | nfCtx-lookup-kd x Γ Γ[x]≡kd-k
  nf-Tp∈ {_} {Γ} (∈-var {j} x Γ-ctx Γ[x]≡kd-j) | kd ._ | refl =
    subst (_ ⊢Nf η-exp (nfKind _ j) (var∙ x) ∈_) (⌊⌋-nf _)
          (η-exp-Var∈ (lookup-kd x (nf-ctx Γ-ctx) nf-Γ[x]≡kd-nf-j)
                      (∈-var x (⌊⌋-lookup x (nfCtx Γ) nf-Γ[x]≡kd-nf-j)))
    where
      open WfsCtxOps using (lookup-kd)
      nf-Γ[x]≡kd-nf-j = nfCtx-lookup-kd x Γ Γ[x]≡kd-j
  nf-Tp∈ (∈-var x Γ-ctx Γ[x]≡kd-k) | tp _  | ()
  nf-Tp∈ (∈-⊥-f Γ-ctx)    = ∈-⊥-f
  nf-Tp∈ (∈-⊤-f Γ-ctx)    = ∈-⊤-f
  nf-Tp∈ (∈-∀-f k-kd a∈*) = ∈-∀-f (nf-kd k-kd) (nf-Tp∈ a∈*)
  nf-Tp∈ (∈-→-f a∈* b∈*)  = ∈-→-f (nf-Tp∈ a∈*) (nf-Tp∈ b∈*)
  nf-Tp∈ (∈-Π-i {j} {a} j-kd a∈k k-kd) =
    let j′ = nfKind _ j
    in subst (λ l → _ ⊢Nf Λ∙ j′ (nf (kd j′ ∷ _) a) ∈ l ⇒ _) (⌊⌋-nf j)
             (∈-Π-i (nf-kd j-kd) (nf-Tp∈ a∈k))
  nf-Tp∈ (∈-Π-e {a} {b} a∈Πjk b∈j _ _) =
    subst (_ ⊢Nf nf _ a ↓⌜·⌝ nf _ b ∈_) (sym (⌊⌋-Kind/ _))
          (Nf∈-Π-e′ (nf-Tp∈ a∈Πjk) (nf-Tp∈ b∈j))
  nf-Tp∈ (∈-s-i a∈a⋯b)  = nf-Tp∈ a∈a⋯b
  nf-Tp∈ (∈-⇑ a∈j j<∷k) = subst (_ ⊢Nf _ ∈_) (<∷-⌊⌋ j<∷k) (nf-Tp∈ a∈j)

  -- Normalization and simultaneous simplification of kind
  -- well-formedness: well-formed kinds normalize to simply
  -- well-formed kinds.
  nf-kd : ∀ {n} {Γ : Ctx n} {k} →
          let Γ′ = nfCtx Γ in Γ ⊢ k kd → ⌊ Γ′ ⌋Ctx ⊢ nfKind Γ′ k kds
  nf-kd (kd-⋯ a∈* b∈*)   = kds-⋯ (nf-Tp∈ a∈*) (nf-Tp∈ b∈*)
  nf-kd (kd-Π j-kd k-kd) = kds-Π (nf-kd j-kd) (nf-kd k-kd)

  -- Normalization and simultaneous simplification of contexts:
  -- well-formed contexts normalize to simply well-formed simple
  -- contexts.

  nf-wf : ∀ {n} {Γ : Ctx n} {a} →
          let Γ′ = nfCtx Γ in Γ ⊢ a wf → ⌊ Γ′ ⌋Ctx ⊢ nfAsc Γ′ a wfs
  nf-wf (wf-kd k-kds) = wfs-kd (nf-kd k-kds)
  nf-wf (wf-tp a∈*)   = wfs-tp (nf-Tp∈ a∈*)

  nf-ctx : ∀ {n} {Γ : Ctx n} → Γ ctx → nfCtx Γ ctxs
  nf-ctx D.[]             = S.[]
  nf-ctx (a-wf D.∷ Γ-ctx) = nf-wf a-wf S.∷ nf-ctx Γ-ctx

-- Normal forms of type operators are η-long.
≈-η-nf : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢Tp a ∈ Π j k →
         let nf-Γ = nfCtx Γ
         in nf nf-Γ (Λ j (weaken a · var zero)) ≈ nf nf-Γ a
≈-η-nf a∈Πjk with Nf∈-⇒-inv (nf-Tp∈ a∈Πjk)
≈-η-nf {_} {Γ} {a} {j} {k} a∈Πjk
  | l , b , l-kds , b∈⌊k⌋ , ⌊l⌋≡⌊j⌋ , nf-a≡Λlb =
  begin
    nf nf-Γ (Λ j (weaken a · var zero))
  ≈⟨ ≈-Λ∙ ⌊nf-j⌋≡⌊l⌋ (begin
        nf-a′ ↓⌜·⌝ η-exp (weakenKind′ nf-j) (var∙ zero)
      ≡⟨ cong (_↓⌜·⌝ η-exp (weakenKind′ nf-j) (var∙ zero))
              (trans (sym (nf-weaken (kd nf-j) a)) (cong weakenElim nf-a≡Λlb)) ⟩
        weakenElim (Λ∙ l b) ↓⌜·⌝ η-exp (weakenKind′ nf-j) (var∙ zero)
      ≡⟨⟩
        b Elim/Var (VarSubst.wk VarSubst.↑) /⟨ ⌊ weakenKind′ l ⌋ ⟩
          hsub (η-exp (weakenKind′ nf-j) (var∙ zero))
      ≈⟨ ≈-[∈] (≈-refl (b Elim/Var (VarSubst.wk VarSubst.↑)))
               (≈-η-exp ⌊nf-j/wk⌋≡⌊l/wk⌋ (≈-var∙ zero)) ⟩
        b Elim/Var (VarSubst.wk VarSubst.↑) /⟨ ⌊ weakenKind′ l ⌋ ⟩
          hsub (η-exp (weakenKind′ l) (var∙ zero))
      ≈⟨ Nf∈-[]-η-var [] l-kds
                      (subst (λ l → kd l ∷ _ ⊢Nf b ∈ _) (sym ⌊l⌋≡⌊j⌋) b∈⌊k⌋) ⟩
        b
      ∎) ⟩
    Λ∙ l b
  ≡⟨ sym nf-a≡Λlb ⟩
    nf nf-Γ a
  ∎
  where
    nf-Γ   = nfCtx Γ
    nf-j   = nfKind nf-Γ j
    nf-j∷Γ = kd nf-j ∷ nf-Γ
    nf-a′  = nf nf-j∷Γ (weaken a)
    ⌊nf-j⌋≡⌊l⌋ = begin
      ⌊ nf-j ⌋ ≡⟨ ⌊⌋-nf j ⟩
      ⌊ j ⌋    ≡⟨ sym ⌊l⌋≡⌊j⌋ ⟩
      ⌊ l ⌋    ∎
      where open ≡-Reasoning
    ⌊nf-j/wk⌋≡⌊l/wk⌋ = begin
      ⌊ weakenKind′ nf-j ⌋   ≡⟨ ⌊⌋-Kind′/Var nf-j ⟩
      ⌊ nf-j ⌋               ≡⟨ ⌊nf-j⌋≡⌊l⌋ ⟩
      ⌊ l ⌋                  ≡⟨ sym (⌊⌋-Kind′/Var l) ⟩
      ⌊ weakenKind′ l ⌋      ∎
      where open ≡-Reasoning
    open ≈-Reasoning

-- Well-kinded hereditary substitions.

infix 4 _⊢/Tp⟨_⟩_∈_

data _⊢/Tp⟨_⟩_∈_ : ∀ {m n} → Ctx n → SKind → SVSub m n → Ctx m → Set where
  ∈-hsub : ∀ {n} {Γ : Ctx n} {k a} →
           Γ ⊢Tp a ∈ k → Γ ⊢/Tp⟨ ⌊ k ⌋ ⟩ hsub ⌜ a ⌝ ∈ kd k ∷ Γ
  ∈-H↑   : ∀ {m n Δ k Γ} {σ : SVSub m n} {a} →
           Δ ⊢/Tp⟨ k ⟩ σ ∈ Γ → (a TermAsc/ toSub σ) ∷ Δ ⊢/Tp⟨ k ⟩ σ H↑ ∈ a ∷ Γ

-- Normalize and simplify a well-kinded hereditary substitution.

nf-/⟨⟩∈ : ∀ {m n k Δ} {σ : SVSub m n} {Γ} → Δ ⊢/Tp⟨ k ⟩ σ ∈ Γ →
          ⌊ nfCtx Δ ⌋Ctx ⊢/⟨ k ⟩ nfSVSub (nfCtx Δ) σ ∈ ⌊ nfCtx Γ ⌋Ctx
nf-/⟨⟩∈ (∈-hsub {Γ = Γ} {k} {a} a∈k) =
  subst₂ (⌊ nfCtx Γ ⌋Ctx ⊢/⟨ ⌊ k ⌋ ⟩_∈_)
         (cong (hsub ∘ nf (nfCtx Γ)) (sym (⌞⌟∘⌜⌝-id a)))
         (cong (λ j → kd j ∷ ⌊ nfCtx Γ ⌋Ctx) (sym (⌊⌋-nf k)))
         (∈-hsub (nf-Tp∈ a∈k))
nf-/⟨⟩∈ (∈-H↑ {Δ = Δ} {k} {Γ} {σ} {a} σ∈Γ) =
  subst (_⊢/⟨ k ⟩ nfSVSub (nfCtx (a/σ ∷ Δ)) (σ H↑) ∈ ⌊ nfCtx (a ∷ Γ) ⌋Ctx)
        (cong (_∷ ⌊ nfCtx Δ ⌋Ctx) (begin
          ⌊ nfAsc (nfCtx Γ) a ⌋Asc                     ≡⟨ ⌊⌋Asc-nf a ⟩
          ⌊ a ⌋Asc                                     ≡˘⟨ S.⌊⌋-TermAsc/ a ⟩
          ⌊ a TermAsc/ toSub σ ⌋Asc                    ≡˘⟨ ⌊⌋Asc-nf _ ⟩
          ⌊ nfAsc (nfCtx Δ) (a TermAsc/ toSub σ) ⌋Asc  ∎))
        (∈-H↑ (nf-/⟨⟩∈ σ∈Γ))
  where
    open ≡-Reasoning
    a/σ = a TermAsc/ toSub σ

open ≈-Reasoning
private module P = ≡-Reasoning

mutual

  -- Substitution (weakly) commutes with normalization.

  nf-/⟨⟩ : ∀ {m n Δ k Γ} {σ : SVSub m n} {a j} →
           Γ ⊢Tp a ∈ j → Δ ⊢/Tp⟨ k ⟩ σ ∈ Γ →
           nf (nfCtx Δ) (a / toSub σ)  ≈
             nf (nfCtx Γ) a /⟨ k ⟩ nfSVSub (nfCtx Δ) σ
  nf-/⟨⟩ {Γ = Γ} (∈-var x Γ-ctx Γ[x]≡kd-j) σ∈Γ
    with E.lookup x (nfCtx Γ) | nfCtx-lookup-kd x Γ Γ[x]≡kd-j
  nf-/⟨⟩ {Δ = Δ} {k} {Γ} {σ} {_} {j} (∈-var x Γ-ctx Γ[x]≡kd-j) σ∈Γ
    | kd nf-j | refl with hit? σ x
  ... | hit a hitP =
    let open WfsCtxOps using (lookup-kd)
        nf-Γ-ctxs       = nf-ctx Γ-ctx
        nf-Γ[x]≡kd-nf-j = nfCtx-lookup-kd x Γ Γ[x]≡kd-j
        nf-j-kds  = lookup-kd x nf-Γ-ctxs nf-Γ[x]≡kd-nf-j
        hitP-nf-σ = nf-Hit (nfCtx Δ) hitP
        x∈⌊j⌋     = ∈-var x (⌊⌋-lookup x (nfCtx Γ) nf-Γ[x]≡kd-nf-j)
    in begin
      nf (nfCtx Δ) (Vec.lookup (toSub σ) x)
    ≡⟨ cong (nf (nfCtx Δ)) (lookup-toSub σ x) ⟩
      nf (nfCtx Δ) (⌞ toElim (lookupSV σ x) ⌟)
    ≡⟨ cong (nf (nfCtx Δ) ∘ ⌞_⌟ ∘ toElim) (lookup-Hit hitP) ⟩
      nf (nfCtx Δ) ⌞ a ⌟
    ≡˘⟨ cong (_?∙∙⟨ k ⟩ []) (lookup-Hit hitP-nf-σ) ⟩
      var∙ x /⟨ k ⟩ nfSVSub (nfCtx Δ) σ
    ≈˘⟨ η-exp-var-Hit-/⟨⟩ hitP-nf-σ nf-j-kds x∈⌊j⌋ (nf-/⟨⟩∈ σ∈Γ) ⟩
      η-exp (nfKind (nfCtx Γ) j) (var∙ x) /⟨ k ⟩ nfSVSub (nfCtx Δ) σ
    ∎
  ... | miss y missP =
    let open WfsCtxOps using (lookup-kd)
        nf-Γ-ctxs       = nf-ctx Γ-ctx
        nf-Γ[x]≡kd-nf-j = nfCtx-lookup-kd x Γ Γ[x]≡kd-j
        nf-j-kds   = lookup-kd x nf-Γ-ctxs nf-Γ[x]≡kd-nf-j
        missP-nf-σ = nf-Miss (nfCtx Δ) missP
        x∈⌊j⌋      = ∈-var x (⌊⌋-lookup x (nfCtx Γ) nf-Γ[x]≡kd-nf-j)
    in begin
      nf (nfCtx Δ) (Vec.lookup (toSub σ) x)
    ≡⟨ cong (nf (nfCtx Δ)) (lookup-toSub σ x) ⟩
      nf (nfCtx Δ) ⌞ toElim (lookupSV σ x) ⌟
    ≡⟨ cong (nf (nfCtx Δ) ∘ ⌞_⌟ ∘ toElim) (lookup-Miss missP) ⟩
      nf (nfCtx Δ) (var y)
    ≈⟨ nf-var-kd-⌊⌋ (nfCtx Δ) y (P.begin
          ⌊ E.lookup y (nfCtx Δ) ⌋Asc
        P.≡˘⟨ ⌊⌋Asc-lookup y (nfCtx Δ) ⟩
          S.lookup y ⌊ nfCtx Δ ⌋Ctx
        P.≡⟨ lookup-/⟨⟩∈-Miss (nf-/⟨⟩∈ σ∈Γ) x∈⌊j⌋ missP-nf-σ  ⟩
          S.lookup x ⌊ nfCtx Γ ⌋Ctx
        P.≡⟨ ⌊⌋-lookup x (nfCtx Γ) nf-Γ[x]≡kd-nf-j ⟩
          kd ⌊ nfKind (nfCtx Γ) j ⌋
        P.≡˘⟨ cong kd (⌊⌋-Kind/⟨⟩ (nfKind (nfCtx Γ) j)) ⟩
          kd ⌊ nfKind (nfCtx Γ) j Kind/⟨ k ⟩ nfSVSub (nfCtx Δ) σ ⌋
        P.∎) ⟩
      η-exp (nfKind (nfCtx Γ) j Kind/⟨ k ⟩ nfSVSub (nfCtx Δ) σ) (var∙ y) 
    ≡˘⟨ η-exp-ne-Miss-/⟨⟩ x y [] (nfKind (nfCtx Γ) j) missP-nf-σ ⟩
      η-exp (nfKind (nfCtx Γ) j) (var∙ x) /⟨ k ⟩ nfSVSub (nfCtx Δ) σ
    ∎
  nf-/⟨⟩ (∈-var _ _ _) σ∈Γ | tp a | ()
  nf-/⟨⟩ (∈-⊥-f Γ-ctx) σ∈Γ = ≈-refl _
  nf-/⟨⟩ (∈-⊤-f Γ-ctx) σ∈Γ = ≈-refl _
  nf-/⟨⟩ (∈-∀-f {j} j-kd a∈*) σ∈Γ =
    ≈-∀∙ (nfKind-/⟨⟩ j-kd σ∈Γ) (nf-/⟨⟩ a∈* (∈-H↑ σ∈Γ))
  nf-/⟨⟩ (∈-→-f a∈* b∈*) σ∈Γ =
    ≈-⇒∙ (nf-/⟨⟩ a∈* σ∈Γ) (nf-/⟨⟩ b∈* σ∈Γ)
  nf-/⟨⟩ (∈-Π-i j-kd a∈k k-kd) σ∈Γ =
    ≈-Λ∙ (≋-⌊⌋ (nfKind-/⟨⟩ j-kd σ∈Γ)) (nf-/⟨⟩ a∈k (∈-H↑ σ∈Γ))
  nf-/⟨⟩ {Δ = Δ} {k} {Γ} {σ} {a · b} (∈-Π-e a∈Πjk b∈j _ _) σ∈Γ = begin
      nf (nfCtx Δ) (a / toSub σ) ↓⌜·⌝ nf (nfCtx Δ) (b / toSub σ)
    ≈⟨ ≈-↓⌜·⌝ (nf-/⟨⟩ a∈Πjk σ∈Γ) (nf-/⟨⟩ b∈j σ∈Γ) ⟩
      (nf (nfCtx Γ) a /⟨ k ⟩ nfSVSub (nfCtx Δ) σ) ↓⌜·⌝
        (nf (nfCtx Γ) b /⟨ k ⟩ nfSVSub (nfCtx Δ) σ)
    ≡⟨ sym (Nf∈-Π-e-/⟨⟩′ (nf-Tp∈ a∈Πjk) (nf-Tp∈ b∈j) (nf-/⟨⟩∈ σ∈Γ)) ⟩
      nf (nfCtx Γ) a ↓⌜·⌝ nf (nfCtx Γ) b /⟨ k ⟩ nfSVSub (nfCtx Δ) σ
    ∎
  nf-/⟨⟩ (∈-s-i a∈c⋯d)  σ∈Γ = nf-/⟨⟩ a∈c⋯d σ∈Γ
  nf-/⟨⟩ (∈-⇑ a∈j j<∷k) σ∈Γ = nf-/⟨⟩ a∈j σ∈Γ

  nfKind-/⟨⟩ : ∀ {m n Δ k Γ} {σ : SVSub m n} {j} →
               Γ ⊢ j kd → Δ ⊢/Tp⟨ k ⟩ σ ∈ Γ →
               nfKind (nfCtx Δ) (j Kind/ toSub σ)  ≋
                 nfKind (nfCtx Γ) j Kind/⟨ k ⟩ nfSVSub (nfCtx Δ) σ
  nfKind-/⟨⟩ (kd-⋯ a∈* b∈*)   σ∈Γ = ≋-⋯ (nf-/⟨⟩ a∈* σ∈Γ) (nf-/⟨⟩ b∈* σ∈Γ)
  nfKind-/⟨⟩ (kd-Π j-kd k-kd) σ∈Γ =
    ≋-Π (nfKind-/⟨⟩ j-kd σ∈Γ) (nfKind-/⟨⟩ k-kd (∈-H↑ σ∈Γ))

-- Shorthands.

nf-[] : ∀ {n} {Γ : Ctx n} {k a j b} →
        kd k ∷ Γ ⊢Tp a ∈ j → Γ ⊢Tp b ∈ k →
        nf (nfCtx Γ) (a [ b ])  ≈
          nf (nfCtx (kd k ∷ Γ)) a [ nf (nfCtx Γ) b ∈ ⌊ k ⌋ ]
nf-[] {_} {Γ} {k} {a} a∈j b∈k =
  subst (λ c → nf (nfCtx Γ) (a [ c ]) ≈
               (nf (nfCtx (kd k ∷ Γ)) a [ nf (nfCtx Γ) c ∈ ⌊ k ⌋ ]))
        (⌞⌟∘⌜⌝-id _) (nf-/⟨⟩ a∈j (∈-hsub b∈k))

nfKind-[] : ∀ {n} {Γ : Ctx n} {k j b} →
            kd k ∷ Γ ⊢ j kd → Γ ⊢Tp b ∈ k →
            nfKind (nfCtx Γ) (j Kind[ b ])  ≋
              nfKind (nfCtx (kd k ∷ Γ)) j Kind[ nf (nfCtx Γ) b ∈ ⌊ k ⌋ ]
nfKind-[] {_} {Γ} {k} {j} j-kd b∈k =
  subst (λ c → nfKind (nfCtx Γ) (j Kind[ c ]) ≋
               (nfKind (nfCtx (kd k ∷ Γ)) j Kind[ nf (nfCtx Γ) c ∈ ⌊ k ⌋ ]))
        (⌞⌟∘⌜⌝-id _) (nfKind-/⟨⟩ j-kd (∈-hsub b∈k))
