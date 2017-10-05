------------------------------------------------------------------------
-- Normalization/simplification of kinding in Fω with interval kinds
------------------------------------------------------------------------

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
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
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
  nf-Tp∈ (∈-⊥-f Γ-ctx) = ∈-⊥-f
  nf-Tp∈ (∈-⊤-f Γ-ctx) = ∈-⊤-f
  nf-Tp∈ (∈-∀-f {k} {a} k-kd a∈*) =
    ∈-∀-f (nf-kd k-kd) (nf-Tp∈ a∈*)
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
  nf-kd (kd-⋯ a∈* b∈*)           = kds-⋯ (nf-Tp∈ a∈*) (nf-Tp∈ b∈*)
  nf-kd (kd-Π {j} {k} j-kd k-kd) =
    kds-Π (nf-kd j-kd) (nf-kd k-kd)

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
        b Elim/Var (VarSubst.wk VarSubst.↑) /H
          0 ← η-exp (weakenKind′ nf-j) (var∙ zero) ∈ ⌊ weakenKind′ l ⌋
      ≈⟨ ≈-[∈] (≈-refl (b Elim/Var (VarSubst.wk VarSubst.↑)))
               (≈-η-exp ⌊nf-j/wk⌋≡⌊l/wk⌋ (≈-var∙ zero)) ⟩
        b Elim/Var (VarSubst.wk VarSubst.↑) /H
          0 ← η-exp (weakenKind′ l) (var∙ zero) ∈ ⌊ weakenKind′ l ⌋
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

-- A helper for constructing well-kinded hereditary substitutions from
-- normalized well-kinded types.
nf-∈-hsub : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} {a k} →
            Γ₁ ⊢Tp a ∈ k →
            ⌊ nfCtx (Γ₂ E′/ sub a ′++ Γ₁) ⌋Ctx ⊢/H
              (n ← nf (nfCtx Γ₁) a ∈ ⌊ k ⌋) ∈ ⌊ nfCtx (Γ₂ ′++ kd k ∷ Γ₁) ⌋Ctx
nf-∈-hsub Γ₂ {Γ₁} {a} {k} a∈k = subst₂ (_⊢/H _ ∈_) (begin
    S.re-idx ⌊ Γ₂ ⌋CtxExt E.′++ ⌊ nfCtx Γ₁ ⌋Ctx
  ≡⟨ cong₂ _′++_ (begin
      S.re-idx ⌊ Γ₂ ⌋CtxExt
    ≡⟨ sym (map′-∘ (λ _ a → a) (λ _ → ⌊_⌋Asc) Γ₂) ⟩
      map′ (λ _ → ⌊_⌋Asc) Γ₂
    ≡⟨ map′-cong (λ a → sym (S.⌊⌋-TermAsc/ a)) Γ₂ ⟩
      map′ (λ n b → ⌊ b TermAsc/ sub a ↑⋆ n ⌋Asc) Γ₂
    ≡⟨ map′-∘ (λ _ → ⌊_⌋Asc) (λ n b → b TermAsc/ sub a ↑⋆ n) Γ₂ ⟩
      ⌊ Γ₂ E′/ sub a ⌋CtxExt
    ∎) (⌊⌋Ctx-nf Γ₁) ⟩
    ⌊ Γ₂ E′/ sub a ⌋CtxExt E.′++ ⌊ Γ₁ ⌋Ctx
  ≡⟨ ′++-map ⌊_⌋Asc (Γ₂ E′/ _) Γ₁ ⟩
    ⌊ Δ ⌋Ctx
  ≡⟨ sym (⌊⌋Ctx-nf Δ) ⟩
    ⌊ nfCtx Δ ⌋Ctx
  ∎) (begin
    ⌊ Γ₂ ⌋CtxExt ′++ kd ⌊ k ⌋ E.∷ ⌊ nfCtx Γ₁ ⌋Ctx
  ≡⟨ cong (λ Γ → ⌊ Γ₂ ⌋CtxExt E.′++ kd ⌊ k ⌋ E.∷ Γ) (⌊⌋Ctx-nf Γ₁) ⟩
    ⌊ Γ₂ ⌋CtxExt ′++ kd ⌊ k ⌋ E.∷ ⌊ Γ₁ ⌋Ctx
  ≡⟨ ′++-map ⌊_⌋Asc Γ₂ (kd k ∷ Γ₁) ⟩
    ⌊ Γ ⌋Ctx
  ≡⟨ sym (⌊⌋Ctx-nf Γ) ⟩
    ⌊ nfCtx Γ ⌋Ctx
  ∎) (∈-hsub ⌊ Γ₂ ⌋CtxExt (nf-Tp∈ a∈k))
  where
    open ≡-Reasoning
    Γ = Γ₂ ′++ kd k ∷ Γ₁
    Δ = Γ₂ E′/ sub a ′++ Γ₁

open ≈-Reasoning
private module P = ≡-Reasoning

mutual

  -- Substitution (weakly) commutes with normalization.
  nf-[] : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a b j k} →
          let Γ = Γ₂ ′++ kd k ∷ Γ₁
          in Γ ⊢Tp a ∈ j → Γ₁ ⊢Tp b ∈ k →
             nf (nfCtx (Γ₂ E′/ sub b ′++ Γ₁)) (a / sub b ↑⋆ n)  ≈
               nf (nfCtx Γ) a /H n ← nf (nfCtx Γ₁) b ∈ ⌊ k ⌋
  nf-[] {_} {n} Γ₂ (∈-var x Γ-ctx Γ[x]≡kd-k) b∈k with compare n x
  nf-[] {_} {n} Γ₂ {Γ₁} {_} {b} {j} {k} (∈-var ._ Γ-ctx Γ[x]≡kd-k) b∈k
    | yes refl = begin
      nf (nfCtx Δ) (var x / sub b ↑⋆ n)
    ≡⟨ cong (nf (nfCtx Δ)) (raise-/-↑⋆ n zero) ⟩
      nf (nfCtx Δ) (b / wk⋆ n)
    ≡⟨ cong₂ nf (nf-++ (Γ₂ E′/ sub b) Γ₁) (/-wk⋆ n) ⟩
      nf (nfCtxExt (nfCtx Γ₁) (Γ₂ E′/ sub b) ′++ nfCtx Γ₁) (weaken⋆ n b)
    ≡⟨ sym (nf-weaken⋆ (nfCtxExt (nfCtx Γ₁) (Γ₂ E′/ sub b)) b) ⟩
      weakenElim⋆ n (nf (nfCtx Γ₁) b)
    ≡⟨ sym (TermLikeLemmas./-wk⋆ termLikeLemmasElim n) ⟩
      nf (nfCtx Γ₁) b Elim/ wk⋆ n
    ≡⟨ cong (_Elim/ wk⋆ n) (sym (⌜⌝∘⌞⌟-id (nf (nfCtx Γ₁) b))) ⟩
      ⌜ ⌞ nf (nfCtx Γ₁) b ⌟ ⌝ Elim/ wk⋆ n
    ≡⟨ sym (⌜⌝-/ ⌞ nf (nfCtx Γ₁) b ⌟) ⟩
      ⌜ ⌞ nf (nfCtx Γ₁) b ⌟ / wk⋆ n ⌝
    ≡⟨ cong ⌜_⌝ (sym (raise-/-↑⋆ n zero)) ⟩
      ⌜ var x / sub ⌞ nf (nfCtx Γ₁) b ⌟ ↑⋆ n ⌝
    ≡⟨ sym (ne-yes-/H n) ⟩
      var∙ x /H n ← nf (nfCtx Γ₁) b ∈ ⌊ k ⌋
    ≈⟨ ≈-sym (η-exp-var-Hit-/H refl nf-k-kds x∈⌊k⌋ (nf-∈-hsub Γ₂ b∈k)) ⟩
      η-exp (nfKind (nfCtx Γ) j) (var∙ x) /H n ← nf (nfCtx Γ₁) b ∈ ⌊ k ⌋
    ≡⟨ cong (_/H n ← nf (nfCtx Γ₁) b ∈ ⌊ k ⌋)
            (sym (nf-var-kd (nfCtx Γ) x (nfCtx-lookup-kd x Γ Γ[x]≡kd-k))) ⟩
      nf (nfCtx Γ) (var x) /H n ← nf (nfCtx Γ₁) b ∈ ⌊ k ⌋
    ∎
    where
      open WfsCtxOps using (lookup-kd)
      open ExtLemmas₄ lemmas₄ using (raise-/-↑⋆)
      x = raise n zero
      Γ = Γ₂ ′++ kd k ∷ Γ₁
      Δ = Γ₂ E′/ sub b ′++ Γ₁
      nf-Γ-ctxs       = nf-ctx Γ-ctx
      nf-Γ[x]≡kd-nf-k = nfCtx-lookup-kd x Γ Γ[x]≡kd-k
      nf-k-kds = lookup-kd x nf-Γ-ctxs nf-Γ[x]≡kd-nf-k
      x∈⌊k⌋    = ∈-var x (⌊⌋-lookup x (nfCtx Γ) nf-Γ[x]≡kd-nf-k)
  nf-[] {_} {n} Γ₂ {Γ₁} {_} {b} {j} {k} (∈-var ._ Γ-ctx Γ[x]≡kd-j) b∈k
    | no y refl = begin
      nf (nfCtx Δ) (var x / sub b ↑⋆ n)
    ≡⟨ cong (nf (nfCtx Δ)) (lookup-sub-↑⋆ n y) ⟩
      nf (nfCtx Δ) (var y)
    ≈⟨ ≈-nf (≈Ctx-⌊⌋ (nfCtx-[] Γ₂ Γ-ctx b∈k)) (var y) ⟩
      nf nf-Δ (var y)
    ≡⟨ nf-var-kd nf-Δ y (P.begin
        E.lookup y nf-Δ
      P.≡⟨ cong (λ l → E.lookup y (nf-Γ₂ E[ nf nf-Γ₁ b ∈ l ] ′++ nf-Γ₁))
                (sym (⌊⌋-nf k)) ⟩
        E.lookup y (nf-Γ₂ E[ nf nf-Γ₁ b ∈ ⌊ nfKind nf-Γ₁ k ⌋ ] ′++ nf-Γ₁)
      P.≡⟨ lookup-E[] nf-Γ₂ (nf nf-Γ₁ b) (nfKind nf-Γ₁ k) y ⟩
        E.lookup x (nf-Γ₂ ′++ kd (nfKind nf-Γ₁ k) ∷ nf-Γ₁) Asc/H _
      P.≡⟨ cong₂ (λ Γ l → E.lookup x Γ Asc/H n ← nf nf-Γ₁ b ∈ l)
                 (sym (nf-++ Γ₂ (kd k ∷ Γ₁))) (⌊⌋-nf k) ⟩
        E.lookup x (nfCtx Γ) Asc/H ρ
      P.≡⟨ cong (_Asc/H ρ) (nfCtx-lookup-kd x Γ Γ[x]≡kd-j) ⟩
        kd ((nfKind (nfCtx Γ) j) Kind/H ρ)
      P.∎) ⟩
      η-exp ((nfKind (nfCtx Γ) j) Kind/H ρ) (var∙ y)
    ≡⟨ sym (η-exp-ne-Miss-/H x y [] (nfKind (nfCtx Γ) j) {ρ} refl)  ⟩
      η-exp (nfKind (nfCtx Γ) j) (var∙ x) /H ρ
    ≡⟨ cong (_/H ρ) (sym (nf-var-kd (nfCtx Γ) x
                                    (nfCtx-lookup-kd x Γ Γ[x]≡kd-j))) ⟩
      nf (nfCtx Γ) (var x) /H ρ
    ∎
    where
      x     = lift n suc y
      Γ     = Γ₂ ′++ kd k ∷ Γ₁
      Δ     = Γ₂ E′/ sub b ′++ Γ₁
      nf-Γ₁ = nfCtx Γ₁
      ρ     = n ← nf nf-Γ₁ b ∈ ⌊ k ⌋
      nf-Γ₂ = nfCtxExt (kd (nfKind nf-Γ₁ k) ∷ nf-Γ₁) Γ₂
      nf-Δ  = nf-Γ₂ E[ nf nf-Γ₁ b ∈ ⌊ k ⌋ ] ′++ nf-Γ₁
  nf-[] Γ₂ (∈-⊥-f Γ-ctx) b∈k = ≈-refl _
  nf-[] Γ₂ (∈-⊤-f Γ-ctx) b∈k = ≈-refl _
  nf-[] Γ₂ (∈-∀-f {j} j-kd a∈*) b∈k =
    ≈-∀∙ (nfKind-[] Γ₂ j-kd b∈k) (nf-[] (kd j ∷ Γ₂) a∈* b∈k)
  nf-[] Γ₂ (∈-→-f a∈* b∈*) c∈k =
    ≈-⇒∙ (nf-[] Γ₂ a∈* c∈k) (nf-[] Γ₂ b∈* c∈k)
  nf-[] Γ₂ (∈-Π-i {j} j-kd a∈k k-kd) b∈l =
    ≈-Λ∙ (≋-⌊⌋ (nfKind-[] Γ₂ j-kd b∈l)) (nf-[] (kd j ∷ Γ₂) a∈k b∈l)
  nf-[] {_} {n} Γ₂ {Γ₁} {_} {c} {_} {l}
        (∈-Π-e {a} {b} {j} {k} a∈Πjk b∈j _ _) c∈l =
      begin
        nf-a[c] ↓⌜·⌝ nf (nfCtx Δ) (b / sub c ↑⋆ n)
      ≈⟨ ≈-↓⌜·⌝ (nf-[] Γ₂ a∈Πjk c∈l) (nf-[] Γ₂ b∈j c∈l) ⟩
        nf-a/ρ ↓⌜·⌝ (nf (nfCtx Γ) b /H n ← nf-c ∈ ⌊ l ⌋)
      ≡⟨ sym (Nf∈-Π-e-/H′ nf-a∈⌊j⌋⇒⌊k⌋ (nf-Tp∈ b∈j) ρ∈⌊Γ⌋) ⟩
        nf-a ↓⌜·⌝ nf (nfCtx Γ) b /H n ← nf-c ∈ ⌊ l ⌋
      ∎
    where
      Γ       = Γ₂ ′++ kd l ∷ Γ₁
      Δ       = Γ₂ E′/ sub c ′++ Γ₁
      nf-c    = nf (nfCtx Γ₁) c
      nf-a    = nf (nfCtx Γ) a
      nf-a[c] = nf (nfCtx Δ) (a / sub c ↑⋆ n)
      nf-a/ρ  = nf-a /H n ← nf-c ∈ ⌊ l ⌋
      nf-a∈⌊j⌋⇒⌊k⌋ = nf-Tp∈ a∈Πjk
      ρ∈⌊Γ⌋   = nf-∈-hsub Γ₂ c∈l
  nf-[] Γ₂ (∈-s-i a∈c⋯d)  b∈k = nf-[] Γ₂ a∈c⋯d b∈k
  nf-[] Γ₂ (∈-⇑ a∈j j<∷k) b∈l = nf-[] Γ₂ a∈j b∈l

  nfKind-[] : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a j k} →
              let Γ = Γ₂ ′++ kd k ∷ Γ₁
              in Γ ⊢ j kd → Γ₁ ⊢Tp a ∈ k →
                 nfKind (nfCtx (Γ₂ E′/ sub a ′++ Γ₁)) (j Kind/ sub a ↑⋆ n)  ≋
                   nfKind (nfCtx Γ) j Kind/H n ← nf (nfCtx Γ₁) a ∈ ⌊ k ⌋
  nfKind-[] Γ₂ (kd-⋯ a∈* b∈*) c∈k =
    ≋-⋯ (nf-[] Γ₂ a∈* c∈k) (nf-[] Γ₂ b∈* c∈k)
  nfKind-[] Γ₂ (kd-Π {j} j-kd k-kd) a∈l =
    ≋-Π (nfKind-[] Γ₂ j-kd a∈l) (nfKind-[] (kd j ∷ Γ₂) k-kd a∈l)

  nfAsc-[] : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a b k} →
             let Γ = Γ₂ ′++ kd k ∷ Γ₁
             in Γ ⊢ a wf → Γ₁ ⊢Tp b ∈ k →
                nfAsc (nfCtx (Γ₂ E′/ sub b ′++ Γ₁)) (a TermAsc/ sub b ↑⋆ n) ≈Asc
                  nfAsc (nfCtx Γ) a Asc/H n ← nf (nfCtx Γ₁) b ∈ ⌊ k ⌋
  nfAsc-[] Γ₂ (wf-kd k-kd) b∈k = ≈-kd (nfKind-[] Γ₂ k-kd b∈k)
  nfAsc-[] Γ₂ (wf-tp a∈*)  b∈k = ≈-tp (nf-[] Γ₂ a∈* b∈k)

  nfCtx-[] : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a k} →
             let nf-Γ₁ = nfCtx Γ₁
                 nf-Γ₂ = nfCtxExt (kd (nfKind nf-Γ₁ k) ∷ nf-Γ₁) Γ₂
             in Γ₂ ′++ kd k ∷ Γ₁ ctx → Γ₁ ⊢Tp a ∈ k →
                nfCtx (Γ₂ E′/ sub a ′++ Γ₁)  ≈Ctx
                  nf-Γ₂ E[ nf nf-Γ₁ a ∈ ⌊ k ⌋ ] ′++ nf-Γ₁
  nfCtx-[]             []                    Γ-ctx            a∈k = ≈Ctx-refl _
  nfCtx-[] {_} {suc n} (a ∷ Γ₂) {Γ₁} {b} {k} (a-wf D.∷ Γ-ctx) b∈k =
    ≈-∷ (≈Asc-begin
        nfAsc (nfCtx (Γ₂ E′/ sub b ′++ Γ₁)) (a TermAsc/ sub b ↑⋆ n)
      ≈Asc⟨ nfAsc-[] Γ₂ a-wf b∈k ⟩
        nfAsc (nfCtx (Γ₂ ′++ kd k ∷ Γ₁)) a Asc/H n ← nf nf-Γ₁ b ∈ ⌊ k ⌋
      ≡Asc⟨ cong (λ Δ → nfAsc Δ a Asc/H n ← nf nf-Γ₁ b ∈ ⌊ k ⌋)
              (nf-++ Γ₂ (kd k ∷ Γ₁)) ⟩
        nfAsc (nfCtxExt (kd nf-k ∷ nf-Γ₁) Γ₂ ′++ kd nf-k ∷ nf-Γ₁) a Asc/H
              n ← nf nf-Γ₁ b ∈ ⌊ k ⌋
      ∎Asc) (nfCtx-[] Γ₂ Γ-ctx b∈k)
    where
      nf-Γ₁ = nfCtx Γ₁
      nf-k  = nfKind nf-Γ₁ k
