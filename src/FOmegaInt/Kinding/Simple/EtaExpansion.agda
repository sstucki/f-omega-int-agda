------------------------------------------------------------------------
-- η-expansion of simply-kinded types in Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Simple.EtaExpansion where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (zero; suc)
open import Data.Product as Prod using (_,_)
open import Data.Vec as Vec using ([])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Syntax.WeakEquality
open import FOmegaInt.Kinding.Simple

------------------------------------------------------------------------
-- η-expansion of simply kinded types.
--
-- TODO: explain the point of this and how "simple" kinding differs
-- from "canonical" kinding.

open Syntax renaming (_,_ to ⟨_,_⟩)
open SimpleCtx
open Substitution hiding (subst)
open SimpHSubstLemmas
open RenamingCommutes
open WeakHereditarySubstitutionEquality
open WeakEqEtaExpansion
open KindedRenaming
open KindedHereditarySubstitution
open Kinding

module TrackSimpleKindsKindedEtaExp where
  private
    module V  = VarSubst
    module TK = TrackSimpleKindsEtaExp

  -- NOTE. The definition of the functions η-exp-Var∈ and η-exp-Ne∈
  -- below are structurally recursive in the *simple* kind parameter
  -- k, but *not* in the kind j because we need to weaken the domain
  -- j₁ of the dependent kind (j = Π j₁ j₂) in the arrow case.  The
  -- additional hypothesis ⌊ j ⌋≡ k ensures that k is indeed the
  -- simplification of the kind j.

  mutual

    -- η-expansion preserves simple kinding of neutral types.

    η-exp-Var∈ : ∀ {n} {Γ : Ctx n} {x j k} (hyp : ⌊ j ⌋≡ k) →
                 Γ ⊢ j kds → Γ ⊢Var var x ∈ k →
                 Γ ⊢Nf TK.η-exp j hyp (var∙ x) ∈ k
    η-exp-Var∈ hyp j-kd x∈k = η-exp-Ne∈ hyp j-kd (∈-∙ x∈k ∈-[])

    η-exp-Ne∈ : ∀ {n} {Γ : Ctx n} {a j k} (hyp : ⌊ j ⌋≡ k) →
                Γ ⊢ j kds → Γ ⊢Ne a ∈ k → Γ ⊢Nf TK.η-exp j hyp a ∈ k
    η-exp-Ne∈ at-⋯ (kds-⋯ b∈* c∈*) a∈★ = ∈-ne a∈★
    η-exp-Ne∈ (at-Π ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (kds-Π j₁-kds j₂-kds)
              (∈-∙ {x} {_} {_} {as} x∈l l∋as∈k₁⇒k₂) =
      subst (λ j → _ ⊢Nf η-x∙as ∈ j ⇒ _) (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
            (∈-Π-i j₁-kds (η-exp-Ne∈ ⌊j₂⌋≡k₂ j₂-kds x∙as·z∈k₂))
      where
        η-x∙as = TK.η-exp _ (at-Π ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as)
        η-z∈k₁ = η-exp-Var∈ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (kds-weaken j₁-kds)
                            (∈-var zero (cong kd (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)))
        x∙as·z∈k₂ = Ne∈-Π-e (Ne∈-weaken (∈-∙ x∈l l∋as∈k₁⇒k₂)) η-z∈k₁
    η-exp-Ne∈ at-◆ kds-◆ a∈⋄ = ∈-◆-i
    η-exp-Ne∈ (at-Σ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (kds-Σ j₁-kds j₂-kds)
              (∈-∙ {x} {_} {_} {as} x∈l l∋as∈k₁⊗k₂) =
      ∈-Σ-i η-x∙as₁∈k₁ η-x∙as₂∈k₂
      where
        η-x∙as₁    = TK.η-exp _ ⌊j₁⌋≡k₁ (⌜π₁⌝ (var x ∙ as))
        η-x∙as₁∈k₁ = η-exp-Ne∈ ⌊j₁⌋≡k₁ j₁-kds (Ne∈-Σ-e₁ (∈-∙ x∈l l∋as∈k₁⊗k₂))
        j₂[η-x∙as₁]-kds =
          kds-/H j₂-kds (subst (λ l → _ ⊢/H (0 ← η-x∙as₁ ∈ _) ∈ kd l ∷ _)
                               (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)) (∈-hsub [] η-x∙as₁∈k₁))
        η-x∙as₂∈k₂ = η-exp-Ne∈ (⌊⌋≡-/H ⌊j₂⌋≡k₂) j₂[η-x∙as₁]-kds
                               (Ne∈-Σ-e₂ (∈-∙ x∈l l∋as∈k₁⊗k₂))

  -- η-expansion of neutrals commutes with hereditary substitutions
  -- that miss the head of the neutral.
  η-exp-ne-Miss-/H : ∀ {k l m n Γ Δ} y {x as j} (hyp : ⌊ j ⌋≡ k)
                       {ρ : HSub l m n} → Miss ρ x y →
                     Γ ⊢ j kds → Γ ⊢Ne var x ∙ as ∈ k → Δ ⊢/H ρ ∈ Γ →
                     TK.η-exp j hyp (var x ∙ as) /H ρ  ≈
                       TK.η-exp (j Kind/H ρ) (⌊⌋≡-/H hyp) (var y ∙ (as //H ρ))
  η-exp-ne-Miss-/H y {x} (at-⋯ {a} {b}) {ρ} miss j-kds x∙as∈k ρ∈Γ = begin
      TK.η-exp (a ⋯ b) at-⋯ (var x ∙ _) /H ρ
    ≡⟨ ne-/H-Miss x y miss ⟩
      TK.η-exp (a /H ρ ⋯ b /H ρ) at-⋯ (var y ∙ (_ //H ρ))
    ∎
    where open ≈-Reasoning
  η-exp-ne-Miss-/H y {x} {as} (at-Π {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) {ρ} miss
                   (kds-Π j₁-kds j₂-kds) x∙as∈k₁⇒k₂ ρ∈Γ =
    ≈-Λ∙ refl (begin
       TK.η-exp j₂ ⌊j₂⌋≡k₂ ((weakenElim (var x ∙ as)) ⌜·⌝
         TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H ρ H↑
      ≡⟨ cong (λ x → TK.η-exp _ ⌊j₂⌋≡k₂ (var x ∙ weakenSpine as ⌜·⌝ _) /H ρ H↑)
              (VarLemmas.lookup-wk x) ⟩
       TK.η-exp j₂ ⌊j₂⌋≡k₂ (var (suc x) ∙ (weakenSpine as) ⌜·⌝
         TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H ρ H↑
      ≈⟨ η-exp-ne-Miss-/H (suc y) ⌊j₂⌋≡k₂ miss-↑ j₂-kds x∙as·z∈k₂ (∈-H↑ ρ∈Γ) ⟩
       TK.η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var (suc y) ∙
         (((weakenSpine as) ∷ʳ
           arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                         (var∙ zero))) //H ρ H↑))
      ≡⟨ cong (λ bs → TK.η-exp _ (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var _ ∙ bs))
              (++-//H (weakenSpine as) (_ ∷ [])) ⟩
       TK.η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
         (var (suc y) ∙ ((weakenSpine as) //H ρ H↑) ⌜·⌝
           (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H ρ H↑))
      ≡⟨ cong (λ a → TK.η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                              (a ⌜·⌝ (TK.η-exp _ (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                                               (var∙ zero) /H ρ H↑)))
              (cong₂ (λ x as → var x ∙ as)
                     (sym (VarLemmas.lookup-wk y)) (wk-//H-↑⋆ 0 as)) ⟩
       TK.η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
         (weakenElim (var y ∙ (as //H ρ)) ⌜·⌝
           (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H ρ H↑))
      ≈⟨ ≈-η-exp′ (⌊⌋≡-/H ⌊j₂⌋≡k₂) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                  (≈-⌜·⌝ (≈-refl (weakenElim (var y ∙ (as //H ρ))))
                         (begin
            TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H ρ H↑
          ≈⟨ η-exp-ne-Miss-/H zero (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (↑-zero-Miss ρ)
                              (kds-weaken {a = kd ⌊ j₁ ⌋} j₁-kds) z∈k₁
                              (∈-H↑ ρ∈Γ) ⟩
            TK.η-exp ((weakenKind′ j₁) Kind/H ρ H↑)
                     (⌊⌋≡-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁)) (var∙ zero)
          ≈⟨ ≈-η-exp′ (⌊⌋≡-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                      (⌊⌋≡-weaken (⌊⌋≡-/H ⌊j₁⌋≡k₁)) (≈-var∙ zero) ⟩
            TK.η-exp (weakenKind′ (j₁ Kind/H ρ)) (⌊⌋≡-weaken (⌊⌋≡-/H ⌊j₁⌋≡k₁))
                     (var∙ zero)
          ∎)) ⟩
       TK.η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
         ((weakenElim (var y ∙ (as //H ρ))) ⌜·⌝
           TK.η-exp (weakenKind′ (j₁ Kind/H ρ)) (⌊⌋≡-weaken (⌊⌋≡-/H ⌊j₁⌋≡k₁))
                    (var∙ zero))
      ∎)
      where
        open ≈-Reasoning
        open RenamingCommutes
        miss-↑ = ↑-Miss ρ miss
        z∈k₁ = subst (_ ⊢Ne var∙ zero ∈_) (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
                     (∈-∙ (∈-var zero refl) ∈-[])
        η-z∈k₁ = η-exp-Ne∈ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (kds-weaken j₁-kds) z∈k₁
        x∙as·z∈k₂ = subst (λ x → _ ⊢Ne var x ∙ _ ∈ _) (VarLemmas.lookup-wk x)
                          (Ne∈-Π-e (Ne∈-weaken x∙as∈k₁⇒k₂) η-z∈k₁)
  η-exp-ne-Miss-/H y {x} at-◆ miss j-kds x∙as∈⋄ ρ∈Γ = ≈-refl _
  η-exp-ne-Miss-/H y {x} {as} (at-Σ {j₁} {j₂} {k₁} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) {ρ} miss
                   (kds-Σ j₁-kds j₂-kds) x∙as∈k₁⊗k₂ ρ∈Γ =
    ≈-,∙ eq₁ (begin
        TK.η-exp (j₂ Kind[ TK.η-exp j₁ ⌊j₁⌋≡k₁ _ ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                 (⌜π₂⌝ (var x ∙ as)) /H ρ
      ≈⟨ η-exp-ne-Miss-/H y (⌊⌋≡-/H ⌊j₂⌋≡k₂) miss
                          j₂[η-x∙as]-kds (Ne∈-Σ-e₂ x∙as∈k₁⊗k₂) ρ∈Γ ⟩
        TK.η-exp (j₂ Kind[ TK.η-exp j₁ ⌊j₁⌋≡k₁ _ ∈ k₁ ] Kind/H ρ)
                 (⌊⌋≡-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂)) (var y ∙ ((as ∷ʳ π₂) //H ρ))
      ≈⟨ ≈-η-exp′ (⌊⌋≡-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂)) (⌊⌋≡-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂))
                  (≈-refl (var y ∙ ((as ∷ʳ π₂) //H ρ))) ⟩
        TK.η-exp ((j₂ Kind/H ρ H↑) Kind[ η-y∙as/ρ₁ ∈ k₁ ])
                 (⌊⌋≡-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂)) (var y ∙ ((as ∷ʳ π₂) //H ρ))
      ≡⟨ cong (TK.η-exp (_ Kind[ η-y∙as/ρ₁ ∈ k₁ ])
                        (⌊⌋≡-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂)) ∘ (var y ∙_))
              (++-//H as (π₂ ∷ [])) ⟩
        TK.η-exp ((j₂ Kind/H ρ H↑) Kind[ η-y∙as/ρ₁ ∈ k₁ ])
                 (⌊⌋≡-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂)) (⌜π₂⌝ (var y ∙ (as //H ρ)))
      ∎)
      where
        open ≈-Reasoning
        open RenamingCommutes
        η-x∙as    = TK.η-exp j₁ ⌊j₁⌋≡k₁ (⌜π₁⌝ (var x ∙ as))
        η-x∙as∈k₁ = η-exp-Ne∈ ⌊j₁⌋≡k₁ j₁-kds (Ne∈-Σ-e₁ x∙as∈k₁⊗k₂)
        η-y∙as/ρ₁ = TK.η-exp (j₁ Kind/H ρ) (⌊⌋≡-/H ⌊j₁⌋≡k₁)
                             (⌜π₁⌝ (var y ∙ (as //H ρ)))
        j₂[η-x∙as]-kds =
          kds-/H j₂-kds (subst (λ l → _ ⊢/H (0 ← η-x∙as ∈ k₁) ∈ kd l ∷ _)
                               (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)) (∈-hsub [] η-x∙as∈k₁))
        eq₁ = begin
            η-x∙as /H ρ
          ≈⟨ η-exp-ne-Miss-/H y ⌊j₁⌋≡k₁ miss j₁-kds (Ne∈-Σ-e₁ x∙as∈k₁⊗k₂) ρ∈Γ ⟩
            TK.η-exp (j₁ Kind/H ρ) (⌊⌋≡-/H ⌊j₁⌋≡k₁)
                     (var y ∙ ((as ∷ʳ π₁) //H ρ))
          ≡⟨ cong (TK.η-exp (j₁ Kind/H ρ) (⌊⌋≡-/H ⌊j₁⌋≡k₁) ∘ (var y ∙_))
                  (++-//H as (π₁ ∷ [])) ⟩
            η-y∙as/ρ₁
          ∎
        miss-↑ = ↑-Miss ρ miss

  mutual

    -- η-expansion of neutrals followed by hereditary substitution
    -- vanishes if the substitution hits the head of the neutral.

    η-exp-var-Hit-/H : ∀ {k m n Γ Δ x j} (hyp : ⌊ j ⌋≡ k) {ρ : HSub k m n} →
                       Hit ρ x → Γ ⊢ j kds → Γ ⊢Var var x ∈ k → Δ ⊢/H ρ ∈ Γ →
                       TK.η-exp j hyp (var∙ x) /H ρ  ≈  var∙ x /H ρ
    η-exp-var-Hit-/H hyp hit j-kds x∈k ρ∈Γ =
      η-exp-ne-Hit-/H hyp hit j-kds (∈-∙ x∈k ∈-[]) ρ∈Γ

    η-exp-ne-Hit-/H : ∀ {k l m n Γ Δ x as j} (hyp : ⌊ j ⌋≡ k)
                      {ρ : HSub l m n} →
                      Hit ρ x → Γ ⊢ j kds → Γ ⊢Ne var x ∙ as ∈ k → Δ ⊢/H ρ ∈ Γ →
                      TK.η-exp j hyp (var x ∙ as) /H ρ  ≈  var x ∙ as /H ρ
    η-exp-ne-Hit-/H at-⋯ hit j-kds a∈k ρ∈Γ = ≈-refl _
    η-exp-ne-Hit-/H (at-Π ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) hit (kds-Π j₁-kds j₂-kds)
                    (∈-∙ x∈l l∋as∈k₁⇒k₂) ρ∈Γ
      with Var∈-Hit-/H′ x∈l ρ∈Γ hit
    η-exp-ne-Hit-/H {Γ = Γ} (at-Π {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) {ρ} hit
                    (kds-Π j₁-kds j₂-kds)
                    (∈-∙ {as = as} (∈-var {l} x Γ[x]≡kd-l) l∋as∈k₁⇒k₂) ρ∈Γ |
                    _ , refl =
      let hit-↑            = ↑-Hit ρ hit
          kd-l∷Γ[x+1]≡kd-l = trans (lookup-suc x (kd l) [] Γ) Γ[x]≡kd-l
          x+1∈l            = ∈-var (suc x) kd-l∷Γ[x+1]≡kd-l
          l∋as∈k₁⇒k₂′      = Sp∈-weaken l∋as∈k₁⇒k₂
          η-z∈k₁           = η-exp-Var∈ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (kds-weaken j₁-kds)
                                        (∈-var zero refl)
          x+1∙as·η-z∈k₂    = ∈-∙ x+1∈l (∈-∷ʳ l∋as∈k₁⇒k₂′ η-z∈k₁)
          ρ↑∈k₁∷Γ          = ∈-H↑ ρ∈Γ
          x∙as/ρ∈k₁⇒k₂     = Ne∈-Hit-/H (∈-∙ (∈-var x Γ[x]≡kd-l) l∋as∈k₁⇒k₂)
                                        ρ∈Γ hit
          j′ , a′ , j′-kds , a′∈k₁⇒k₂ , rest = Nf∈-⇒-inv x∙as/ρ∈k₁⇒k₂
          ⌊j′⌋≡k₁ , x∙as/ρ≡Λj′a′             = rest
          ⌊j₁/ρ⌋≡⌊j′⌋ = let open ≡-Reasoning in begin
            ⌊ j₁ Kind/H ρ ⌋   ≡⟨ ⌊⌋-Kind/H j₁ ⟩
            ⌊ j₁ ⌋            ≡⟨ ⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁ ⟩
            k₁                ≡⟨ sym ⌊j′⌋≡k₁ ⟩
            ⌊ j′ ⌋            ∎
          open ≈-Reasoning
      in begin
        TK.η-exp (Π j₁ j₂) (at-Π ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) /H ρ
      ≈⟨ ≈-Λ∙ ⌊j₁/ρ⌋≡⌊j′⌋ (begin
          TK.η-exp j₂ ⌊j₂⌋≡k₂
            (weakenElim (var x ∙ as) ⌜·⌝
              TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H ρ H↑
        ≡⟨ cong (λ y → TK.η-exp _ ⌊j₂⌋≡k₂ (var y ∙ weakenSpine as ⌜·⌝ _) /H ρ H↑)
                (VarLemmas.lookup-wk x) ⟩
          TK.η-exp j₂ ⌊j₂⌋≡k₂
            (var (suc x) ∙ weakenSpine as ⌜·⌝
              TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H ρ H↑
        ≈⟨ η-exp-ne-Hit-/H ⌊j₂⌋≡k₂ hit-↑
                           (subst (λ k → kd k ∷ _ ⊢ _ kds) (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
                                  j₂-kds)
                           x+1∙as·η-z∈k₂ ρ↑∈k₁∷Γ ⟩
          var (suc x) ∙ weakenSpine as ⌜·⌝
            TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H ρ H↑
        ≡⟨ ne-/H-Hit (suc x) hit-↑ ⟩
          (var∙ (suc x) /H ρ H↑) ∙∙⟨ _ ⟩ ((weakenSpine as ∷ʳ
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero))) //H ρ H↑)
        ≡⟨ cong (_ ∙∙⟨ _ ⟩_) (++-//H (weakenSpine as) (_ ∷ [])) ⟩
          (var∙ (suc x) /H ρ H↑) ∙∙⟨ _ ⟩ (weakenSpine as //H ρ H↑ ∷ʳ
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero) /H ρ H↑))
        ≡⟨ Nf∈-++-∙∙⟨⟩ (Prod.proj₁ (Var∈-Hit-/H′ x+1∈l ρ↑∈k₁∷Γ hit-↑))
                       (Sp∈-/H l∋as∈k₁⇒k₂′ ρ↑∈k₁∷Γ)
                       (∈-arg (Nf∈-/H η-z∈k₁ ρ↑∈k₁∷Γ) ∈-[]) ⟩
          (var∙ (suc x) /H ρ H↑) ∙∙⟨ _ ⟩ (weakenSpine as //H ρ H↑) ·′⟨ k₁ ⇒ k₂ ⟩
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero) /H ρ H↑)
        ≡⟨ cong (_·′⟨ k₁ ⇒ k₂ ⟩ _) (sym (ne-/H-Hit (suc x) hit-↑)) ⟩
          (var (suc x) ∙ weakenSpine as /H ρ H↑) ·′⟨ k₁ ⇒ k₂ ⟩
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                (var∙ zero) /H ρ H↑)
        ≡⟨ cong (λ y → (var y ∙ weakenSpine as /H ρ H↑) ·′⟨ k₁ ⇒ k₂ ⟩ _)
                (sym (VarLemmas.lookup-wk x)) ⟩
          (weakenElim (var x ∙ as) /H ρ H↑) ·′⟨ k₁ ⇒ k₂ ⟩
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero) /H ρ H↑)
        ≡⟨ cong (_·′⟨ k₁ ⇒ k₂ ⟩ _) (wk-/H-↑⋆ 0 (var x ∙ as) {ρ}) ⟩
          weakenElim (var x ∙ as /H ρ) ·′⟨ k₁ ⇒ k₂ ⟩
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero) /H ρ H↑)
        ≡⟨ cong ((_·′⟨ k₁ ⇒ k₂ ⟩ _) ∘ weakenElim) x∙as/ρ≡Λj′a′ ⟩
          weakenElim (Λ∙ j′ a′) ·′⟨ k₁ ⇒ k₂ ⟩
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero) /H ρ H↑)
        ≈⟨ ≈-·′⟨⟩ (k₁ ⇒ k₂) (≈-refl (weakenElim (Λ∙ j′ a′)))
                  (≈-arg (η-exp-ne-Miss-/H zero (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                                           (↑-zero-Miss ρ) (kds-weaken j₁-kds)
                                           (∈-∙ (∈-var zero refl) ∈-[])
                                           ρ↑∈k₁∷Γ)) ⟩
          weakenElim (Λ∙ j′ a′) ·′⟨ k₁ ⇒ k₂ ⟩
            arg (TK.η-exp (weakenKind′ j₁ Kind/H ρ H↑)
                          (⌊⌋≡-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁)) (var∙ zero))
        ≈⟨ Nf∈-[]-η-var [] (⌊⌋≡-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                        (kds-/H (kds-weaken j₁-kds) ρ↑∈k₁∷Γ) a′∈k₁⇒k₂ ⟩
          a′
        ∎) ⟩
        Λ∙ j′ a′
      ≡⟨ sym x∙as/ρ≡Λj′a′ ⟩
        var x ∙ as /H ρ
      ∎
    η-exp-ne-Hit-/H at-◆ {ρ} hit kds-◆ x∙as∈⋄ ρ∈Γ =
      let x∙as/ρ∈⋄  = Ne∈-Hit-/H x∙as∈⋄ ρ∈Γ hit
          x∙as/ρ≡⟨⟩ = Nf∈-⋄-inv x∙as/ρ∈⋄
          open ≈-Reasoning
      in begin
        ⟨⟩∙
      ≡⟨ sym x∙as/ρ≡⟨⟩ ⟩
        var _ ∙ _ /H ρ
      ∎
    η-exp-ne-Hit-/H (at-Σ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) hit (kds-Σ j₁-kds j₂-kds)
                    (∈-∙ x∈l l∋as∈k₁⊗k₂) ρ∈Γ
      with Var∈-Hit-/H′ x∈l ρ∈Γ hit
    η-exp-ne-Hit-/H {Γ = Γ} (at-Σ {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) {ρ} hit
                    (kds-Σ j₁-kds j₂-kds)
                    (∈-∙ {as = as} (∈-var {l} x Γ[x]≡kd-l) l∋as∈k₁⊗k₂) ρ∈Γ |
                    _ , refl =
      let η-x∙as₁      = TK.η-exp j₁ ⌊j₁⌋≡k₁ (⌜π₁⌝ (var x ∙ as))
          x∈l          = ∈-var x Γ[x]≡kd-l
          x/ρ∈l , _    = Var∈-Hit-/H′ x∈l ρ∈Γ hit
          l∋as/ρ∈k₁⊗k₂ = Sp∈-/H l∋as∈k₁⊗k₂ ρ∈Γ
          x∙as∈k₁⊗k₂   = ∈-∙ x∈l l∋as∈k₁⊗k₂
          x∙as₁∈k₁     = Ne∈-Σ-e₁ x∙as∈k₁⊗k₂
          η-x∙as₁∈k₁   = η-exp-Ne∈ ⌊j₁⌋≡k₁ j₁-kds x∙as₁∈k₁
          x∙as/ρ∈k₁⊗k₂ = Ne∈-Hit-/H x∙as∈k₁⊗k₂ ρ∈Γ hit
          b₁ , b₂ , b₁∈k₁ , b₂∈k₂ , x∙as/ρ≡b₁,b₂ = Nf∈-⊗-inv x∙as/ρ∈k₁⊗k₂
          [η-x∙as₁]∈⌊j₁⌋∷Γ = subst (λ k → _ ⊢/H (0 ← η-x∙as₁ ∈ k₁) ∈ kd k ∷ _)
                                   (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁))
                                   (∈-hsub [] η-x∙as₁∈k₁)
          j₂[η-x∙as₁]-kds  = kds-/H j₂-kds [η-x∙as₁]∈⌊j₁⌋∷Γ
          open ≈-Reasoning
      in begin
        (η-x∙as₁ /H ρ) ,∙
        (TK.η-exp (j₂ Kind[ η-x∙as₁ ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                  (⌜π₂⌝ (var x ∙ as)) /H ρ)
      ≈⟨ ≈-,∙ (begin
            η-x∙as₁ /H ρ
          ≈⟨ η-exp-ne-Hit-/H ⌊j₁⌋≡k₁ hit j₁-kds x∙as₁∈k₁ ρ∈Γ ⟩
            ⌜π₁⌝ (var x ∙ as) /H ρ
          ≡⟨ ne-/H-Hit x hit ⟩
            (var∙ x /H ρ) ∙∙⟨ _ ⟩ ((as ∷ʳ π₁) //H ρ)
          ≡⟨ cong (_ ∙∙⟨ _ ⟩_) (++-//H as (π₁ ∷ [])) ⟩
            (var∙ x /H ρ) ∙∙⟨ _ ⟩ ((as //H ρ) ∷ʳ π₁)
          ≡⟨ Nf∈-++-∙∙⟨⟩ x/ρ∈l l∋as/ρ∈k₁⊗k₂ (∈-π₁ ∈-[]) ⟩
            (var∙ x /H ρ) ∙∙⟨ _ ⟩ (as //H ρ) ∙∙⟨ k₁ ⊗ k₂ ⟩ (π₁ ∷ [])
          ≡⟨ cong (_∙∙⟨ k₁ ⊗ k₂ ⟩ (π₁ ∷ [])) (sym (ne-/H-Hit x hit)) ⟩
            (var x ∙ as /H ρ) ∙∙⟨ k₁ ⊗ k₂ ⟩ (π₁ ∷ [])
          ≡⟨ cong (_∙∙⟨ k₁ ⊗ k₂ ⟩ (π₁ ∷ [])) x∙as/ρ≡b₁,b₂ ⟩
            (b₁ ,∙ b₂) ∙∙⟨ k₁ ⊗ k₂ ⟩ (π₁ ∷ [])
          ≡⟨⟩
            b₁
          ∎) (begin
            TK.η-exp (j₂ Kind[ η-x∙as₁ ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                     (⌜π₂⌝ (var x ∙ as)) /H ρ
          ≈⟨ η-exp-ne-Hit-/H (⌊⌋≡-/H ⌊j₂⌋≡k₂) hit j₂[η-x∙as₁]-kds
                             (Ne∈-Σ-e₂ x∙as∈k₁⊗k₂) ρ∈Γ ⟩
            ⌜π₂⌝ (var x ∙ as) /H ρ
          ≡⟨ ne-/H-Hit x hit ⟩
            (var∙ x /H ρ) ∙∙⟨ _ ⟩ ((as ∷ʳ π₂) //H ρ)
          ≡⟨ cong (_ ∙∙⟨ _ ⟩_) (++-//H as (π₂ ∷ [])) ⟩
            (var∙ x /H ρ) ∙∙⟨ _ ⟩ ((as //H ρ) ∷ʳ π₂)
          ≡⟨ Nf∈-++-∙∙⟨⟩ x/ρ∈l l∋as/ρ∈k₁⊗k₂ (∈-π₂ ∈-[]) ⟩
            (var∙ x /H ρ) ∙∙⟨ _ ⟩ (as //H ρ) ∙∙⟨ k₁ ⊗ k₂ ⟩ (π₂ ∷ [])
          ≡⟨ cong (_∙∙⟨ k₁ ⊗ k₂ ⟩ (π₂ ∷ [])) (sym (ne-/H-Hit x hit)) ⟩
            (var x ∙ as /H ρ) ∙∙⟨ k₁ ⊗ k₂ ⟩ (π₂ ∷ [])
          ≡⟨ cong (_∙∙⟨ k₁ ⊗ k₂ ⟩ (π₂ ∷ [])) x∙as/ρ≡b₁,b₂ ⟩
            (b₁ ,∙ b₂) ∙∙⟨ k₁ ⊗ k₂ ⟩ (π₂ ∷ [])
          ≡⟨⟩
            b₂
          ∎) ⟩
        b₁ ,∙ b₂
      ≡⟨ sym x∙as/ρ≡b₁,b₂ ⟩
        var x ∙ as /H ρ
      ∎

    -- Hereditary substitutions of a variable by its η-expansion vanish.

    kds-[]-η-var : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ j l}
                   (hyp : ⌊ j ⌋≡ k) → kd k ∷ Γ₁ ⊢ j kds →
                   Γ₂ ′++ kd k ∷ Γ₁ ⊢ l kds →
                   let l′ = l Kind′/Var (V.wk V.↑) V.↑⋆ n
                   in l′ Kind/H (n ← TK.η-exp j hyp (var∙ zero) ∈ k) ≋ l
    kds-[]-η-var Γ₂ hyp j-kds (kds-⋯ a∈★ b∈★) =
      ≋-⋯ (Nf∈-[]-η-var Γ₂ hyp j-kds a∈★) (Nf∈-[]-η-var Γ₂ hyp j-kds b∈★)
    kds-[]-η-var Γ₂ hyp j-kds (kds-Π k-kds l-kds) =
      ≋-Π (kds-[]-η-var Γ₂ hyp j-kds k-kds)
          (kds-[]-η-var (_ ∷ Γ₂) hyp j-kds l-kds)
    kds-[]-η-var Γ₂ hyp j-kds kds-◆ = ≋-◆
    kds-[]-η-var Γ₂ hyp j-kds (kds-Σ k-kds l-kds) =
      ≋-Σ (kds-[]-η-var Γ₂ hyp j-kds k-kds)
          (kds-[]-η-var (_ ∷ Γ₂) hyp j-kds l-kds)

    Nf∈-[]-η-var : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a j l}
                   (hyp : ⌊ j ⌋≡ k) → kd k ∷ Γ₁ ⊢ j kds →
                   Γ₂ ′++ kd k ∷ Γ₁ ⊢Nf a ∈ l →
                   let a′ = a Elim/Var (V.wk V.↑) V.↑⋆ n
                   in a′ /H (n ← TK.η-exp j hyp (var∙ zero) ∈ k) ≈ a
    Nf∈-[]-η-var Γ₂ hyp j-kds ∈-⊥-f = ≈-⊥∙
    Nf∈-[]-η-var Γ₂ hyp j-kds ∈-⊤-f = ≈-⊤∙
    Nf∈-[]-η-var Γ₂ hyp j-kds (∈-∀-f k-kds a∈★) =
      ≈-∀∙ (kds-[]-η-var Γ₂ hyp j-kds k-kds)
           (Nf∈-[]-η-var (_ ∷ Γ₂) hyp j-kds a∈★)
    Nf∈-[]-η-var Γ₂ hyp j-kds (∈-→-f a∈★ b∈★) =
      ≈-⇒∙ (Nf∈-[]-η-var Γ₂ hyp j-kds a∈★) (Nf∈-[]-η-var Γ₂ hyp j-kds b∈★)
    Nf∈-[]-η-var {k} {_} {n} Γ₂ hyp j-kds (∈-Π-i {l} l-kds a∈k) =
      ≈-Λ∙ (begin
             ⌊ l Kind′/Var σ Kind/H ρ ⌋   ≡⟨ ⌊⌋-Kind/H (l Kind′/Var σ) ⟩
             ⌊ l Kind′/Var σ ⌋            ≡⟨ ⌊⌋-Kind′/Var l ⟩
             ⌊ l ⌋                        ∎)
           (Nf∈-[]-η-var (_ ∷ Γ₂) hyp j-kds a∈k)
      where
        open ≡-Reasoning
        σ = (V.wk V.↑) V.↑⋆ n
        ρ = n ← TK.η-exp _ hyp (var∙ zero) ∈ k
    Nf∈-[]-η-var {_} {_} {n} Γ₂ hyp j-kds (∈-ne (∈-∙ (∈-var x _) k∋as∈★))
      with compare n x
    Nf∈-[]-η-var {k} {_} {n} Γ₂ {_} {_} {j} hyp j-kds
                 (∈-ne (∈-∙ {as = as} (∈-var ._ Γ[x]≡kd-k′) k′∋as∈★))
      | yes refl =
      begin
        var (Vec.lookup (raise n zero) ((V.wk V.↑) V.↑⋆ n)) ∙
          (as //Var (V.wk V.↑) V.↑⋆ n) /H n ← η-z ∈ k
      ≡⟨ cong (λ y → var y ∙ (as //Var _ V.↑⋆ n) /H n ← η-z ∈ k)
              (lookup-raise-↑⋆ n zero refl) ⟩
        var (raise n zero) ∙ (as //Var (V.wk V.↑) V.↑⋆ n) /H n ← η-z ∈ k
      ≡⟨ ne-yes-/H n ⟩
        ⌜ var (raise n zero) / sub ⌞ η-z ⌟ ↑⋆ n ⌝ ∙∙⟨ k ⟩
          (as //Var (V.wk V.↑) V.↑⋆ n //H n ← η-z ∈ k)
      ≈⟨ ≈-∙∙⟨⟩ k (≈-refl _) (Sp∈-[]-η-var Γ₂ hyp j-kds k′∋as∈★) ⟩
        ⌜ var (raise n zero) / sub ⌞ η-z ⌟ ↑⋆ n ⌝ ∙∙⟨ k ⟩ as
      ≡⟨ cong ((_∙∙⟨ k ⟩ as) ∘ ⌜_⌝) (raise-/-↑⋆ n zero) ⟩
        ⌜ ⌞ η-z ⌟ / wk⋆ n ⌝ ∙∙⟨ k ⟩ as
      ≡⟨ cong (_∙∙⟨ k ⟩ as) (⌜⌝-/ ⌞ η-z ⌟) ⟩
        (⌜ ⌞ η-z ⌟ ⌝ Elim/ wk⋆ n) ∙∙⟨ k ⟩ as
      ≡⟨ cong ((_∙∙⟨ k ⟩ as) ∘ (_Elim/ wk⋆ n)) (⌜⌝∘⌞⌟-id η-z) ⟩
        (η-z Elim/ wk⋆ n) ∙∙⟨ k ⟩ as
      ≡⟨ cong ((_∙∙⟨ k ⟩ as) ∘ (η-z Elim/_)) (sym (L.liftSub-wk⋆ n)) ⟩
        (η-z Elim/ L.liftSub (V.wk⋆ n)) ∙∙⟨ k ⟩ as
      ≡⟨ cong (_∙∙⟨ k ⟩ as) (sym (L./-liftSub η-z)) ⟩
        (η-z Elim/Var V.wk⋆ n) ∙∙⟨ k ⟩ as
      ≡⟨ cong (_∙∙⟨ k ⟩ as) (TK.η-exp-/Var hyp (var∙ zero)) ⟩
        TK.η-exp (j Kind′/Var V.wk⋆ n) (⌊⌋≡-/Var hyp)
                 (var∙ zero Elim/Var V.wk⋆ n) ∙∙⟨ k ⟩ as
      ≡⟨ cong (λ y → TK.η-exp (j Kind′/Var V.wk⋆ n) (⌊⌋≡-/Var hyp)
                              (var∙ y) ∙∙⟨ k ⟩ as)
              (lookup-wk⋆ zero n) ⟩
        TK.η-exp (j Kind′/Var V.wk⋆ n) (⌊⌋≡-/Var hyp)
                 (var∙ (raise n zero)) ∙∙⟨ k ⟩ as
      ≈⟨ η-exp-ne-∙∙ (⌊⌋≡-/Var hyp)
                     (subst (_ ⊢_kds) (helper n) (kds-weaken⋆ Γ₂ j-kds))
                     (∈-∙ (∈-var (raise n zero) Γ[x]≡kd-k) ∈-[]) k∋as∈★ ⟩
        var (raise n zero) ∙ as
      ∎
      where
        helper : ∀ {m} n {j : Kind Elim m} →
                 weakenKind′⋆ n j ≡ j Kind′/Var V.wk⋆ n
        helper n {j} = sym (begin
          j Kind′/Var V.wk⋆ n            ≡⟨ K./-liftSub j ⟩
          j Kind′/ K.liftSub (V.wk⋆ n)   ≡⟨ cong (j Kind′/_) (K.liftSub-wk⋆ n) ⟩
          j Kind′/ wk⋆ n                 ≡⟨ K./-wk⋆ n ⟩
          weakenKind′⋆ n j               ∎)
          where
            open ≡-Reasoning
            module K = TermLikeLemmas termLikeLemmasKind′

        open ≈-Reasoning
        open ExtLemmas₁ VarLemmas.lemmas₁ using (lookup-wk⋆; lookup-raise-↑⋆)
        open ExtLemmas₄ lemmas₄           using (raise-/-↑⋆)
        module L = TermLikeLemmas termLikeLemmasElim

        η-z       = TK.η-exp j hyp (var∙ zero)
        Γ[x]≡kd-k = trans (lookup-weaken⋆′ n zero [] Γ₂ _)
                          (weakenSAsc⋆-id n)
        k′≡k      = kd-inj′ (trans (sym Γ[x]≡kd-k′) Γ[x]≡kd-k)
        k∋as∈★    = subst (_ ⊢_∋∙ _ ∈ _) k′≡k k′∋as∈★
    Nf∈-[]-η-var {k} {_} {n} Γ₂ {_} {_} {j} hyp j-kds
                 (∈-ne (∈-∙ {as = as} (∈-var ._ Γ[x]≡kd-k′) k′∋as∈★))
      | no y refl =
      begin
        var x ∙ as Elim/Var (V.wk V.↑) V.↑⋆ n /H n ← η-z ∈ k
      ≡⟨ cong (λ z → var z ∙ _ /H n ← η-z ∈ k)
              (VarLemmas.lookup-wk-↑⋆-↑⋆ 1 n x) ⟩
        var (lift n (lift 1 suc) x) ∙ (as //Var (V.wk V.↑) V.↑⋆ n) /H
          n ← η-z ∈ k
      ≡⟨ cong (λ z → var z ∙ _ /H n ← η-z ∈ k) (sym (lift-commutes 0 n y)) ⟩
        var (lift n suc x) ∙ (as //Var (V.wk V.↑) V.↑⋆ n) /H n ← η-z ∈ k
      ≡⟨ ne-no-/H n x ⟩
        var x ∙ (as //Var (V.wk V.↑) V.↑⋆ n //H n ← η-z ∈ k)
      ≈⟨ ≈-∙ (≈-var x) (Sp∈-[]-η-var Γ₂ hyp j-kds k′∋as∈★) ⟩
        var x ∙ as
      ∎
      where
        open ≈-Reasoning
        x   = lift n suc y
        η-z = TK.η-exp j hyp (var∙ zero)
    Nf∈-[]-η-var Γ₂ hyp j-kds ∈-◆-i = ≈-⟨⟩∙
    Nf∈-[]-η-var Γ₂ hyp j-kds (∈-Σ-i a∈k₁ b∈k₂) =
      ≈-,∙ (Nf∈-[]-η-var Γ₂ hyp j-kds a∈k₁) (Nf∈-[]-η-var Γ₂ hyp j-kds b∈k₂)

    Sp∈-[]-η-var : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ as j l₁ l₂}
                   (hyp : ⌊ j ⌋≡ k) → kd k ∷ Γ₁ ⊢ j kds →
                   Γ₂ ′++ kd k ∷ Γ₁ ⊢ l₁ ∋∙ as ∈ l₂ →
                   let as′ = as //Var (V.wk V.↑) V.↑⋆ n
                   in as′ //H (n ← TK.η-exp j hyp (var∙ zero) ∈ k) ≈Sp as
    Sp∈-[]-η-var Γ₂ hyp j-kds ∈-[] = ≈-[]
    Sp∈-[]-η-var Γ₂ hyp j-kds (∈-arg a∈l₁ l₂∋as∈l₃) =
      ≈-∷ (≈-arg (Nf∈-[]-η-var Γ₂ hyp j-kds a∈l₁))
          (Sp∈-[]-η-var Γ₂ hyp j-kds l₂∋as∈l₃)
    Sp∈-[]-η-var Γ₂ hyp j-kds (∈-π₁ l₁∋as∈l₃) =
      ≈-∷ ≈-π₁ (Sp∈-[]-η-var Γ₂ hyp j-kds l₁∋as∈l₃)
    Sp∈-[]-η-var Γ₂ hyp j-kds (∈-π₂ l₂∋as∈l₃) =
      ≈-∷ ≈-π₂ (Sp∈-[]-η-var Γ₂ hyp j-kds l₂∋as∈l₃)

    -- Reducing applications cancel out η-expansion of neutrals.

    η-exp-ne-∙∙ : ∀ {n} {Γ : Ctx n} {a bs j k} (hyp : ⌊ j ⌋≡ k) →
                  Γ ⊢ j kds → Γ ⊢Ne a ∈ k → Γ ⊢ k ∋∙ bs ∈ ★ →
                  TK.η-exp j hyp a ∙∙⟨ k ⟩ bs  ≈  a ∙∙ bs
    η-exp-ne-∙∙ at-⋯ j-kds a∈k ∈-[] = subst (_ ≈_) (sym (∙∙-[] _)) (≈-refl _)
    η-exp-ne-∙∙ {a = a} (at-Π {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
                (kds-Π j₁-kds j₂-kds) a∈k₁⇒k₂ (∈-arg {b} {bs} b∈k₁ k₂∋bs∈★) =
      begin
        TK.η-exp (Π j₁ j₂) (at-Π ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a ·′⟨ k₁ ⇒ k₂ ⟩
          arg b ∙∙⟨ k₂ ⟩ bs
      ≈⟨ ≈-∙∙⟨⟩ k₂ (η-exp-ne-⌜·⌝ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ (kds-Π j₁-kds j₂-kds)
                                 a∈k₁⇒k₂ b∈k₁) (≈Sp-refl bs) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (a ⌜·⌝ b) ∙∙⟨ k₂ ⟩ bs
      ≈⟨ η-exp-ne-∙∙ (⌊⌋≡-/H ⌊j₂⌋≡k₂) j₂[b]-kds (Ne∈-Π-e a∈k₁⇒k₂ b∈k₁) k₂∋bs∈★ ⟩
        (a ⌜·⌝ b) ∙∙ bs
      ≡⟨ ∙∙-++ a (arg b ∷ []) bs ⟩
        a ∙∙ (arg b ∷ bs)
      ∎
      where
        open ≈-Reasoning
        j₂[b]-kds = kds-/H (subst (λ k → kd k ∷ _ ⊢ j₂ kds)
                                  (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁) j₂-kds)
                           (∈-hsub [] b∈k₁)
    η-exp-ne-∙∙ {a = a} (at-Σ {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
                (kds-Σ j₁-kds j₂-kds) a∈k₁⊗k₂ (∈-π₁ {bs} k₁∋bs∈★) =
      begin
        TK.η-exp _ (at-Σ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a ·′⟨ k₁ ⊗ k₂ ⟩ π₁ ∙∙⟨ k₁ ⟩ bs
      ≈⟨ ≈-∙∙⟨⟩ k₁ (η-exp-ne-⌜π₁⌝ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ a∈k₁⊗k₂)
                (≈Sp-refl bs) ⟩
        TK.η-exp j₁ ⌊j₁⌋≡k₁ (⌜π₁⌝ a) ∙∙⟨ k₁ ⟩ bs
      ≈⟨ η-exp-ne-∙∙ ⌊j₁⌋≡k₁ j₁-kds (Ne∈-Σ-e₁ a∈k₁⊗k₂) k₁∋bs∈★ ⟩
        (⌜π₁⌝ a) ∙∙ bs
      ≡⟨ ∙∙-++ a (π₁ ∷ []) bs ⟩
        a ∙∙ (π₁ ∷ bs)
      ∎
      where
        open ≈-Reasoning
    η-exp-ne-∙∙ {a = a} (at-Σ {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
                (kds-Σ j₁-kds j₂-kds) a∈k₁⊗k₂ (∈-π₂ {bs} k₂∋bs∈★) =
      begin
        TK.η-exp _ (at-Σ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a ·′⟨ k₁ ⊗ k₂ ⟩ π₂ ∙∙⟨ k₂ ⟩ bs
      ≈⟨ ≈-∙∙⟨⟩ k₂ (η-exp-ne-⌜π₂⌝ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ a∈k₁⊗k₂)
                (≈Sp-refl bs) ⟩
        TK.η-exp (j₂ Kind[ η-a₁ ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (⌜π₂⌝ a) ∙∙⟨ k₂ ⟩ bs
      ≈⟨ η-exp-ne-∙∙ (⌊⌋≡-/H ⌊j₂⌋≡k₂) j₂[a₁]-kds (Ne∈-Σ-e₂ a∈k₁⊗k₂) k₂∋bs∈★ ⟩
        (⌜π₂⌝ a) ∙∙ bs
      ≡⟨ ∙∙-++ a (π₂ ∷ []) bs ⟩
        a ∙∙ (π₂ ∷ bs)
      ∎
      where
        open ≈-Reasoning
        η-a₁    = TK.η-exp j₁ ⌊j₁⌋≡k₁ (⌜π₁⌝ a)
        η-a₁∈k₁ = η-exp-Ne∈ ⌊j₁⌋≡k₁ j₁-kds (Ne∈-Σ-e₁ a∈k₁⊗k₂)
        j₂[a₁]-kds = kds-/H (subst (λ k → kd k ∷ _ ⊢ j₂ kds)
                                   (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁) j₂-kds)
                            (∈-hsub [] η-a₁∈k₁)

    η-exp-ne-⌜·⌝ : ∀ {n} {Γ : Ctx n} {a b j₁ j₂ k₁ k₂}
                   (hyp₁ : ⌊ j₁ ⌋≡ k₁) (hyp₂ : ⌊ j₂ ⌋≡ k₂) →
                   Γ ⊢ Π j₁ j₂ kds → Γ ⊢Ne a ∈ k₁ ⇒ k₂ → Γ ⊢Nf b ∈ k₁ →
                   TK.η-exp (Π j₁ j₂) (at-Π hyp₁ hyp₂) a ·′⟨ k₁ ⇒ k₂ ⟩ arg b  ≈
                     TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H hyp₂) (a ⌜·⌝ b)
    η-exp-ne-⌜·⌝ {_} {Γ} {_} {b} {j₁} {j₂} {k₁} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂
                 (kds-Π j₁-kds j₂-kds)
                 (∈-∙ {_} {l} {_} {as} (∈-var x Γ[x]≡kd-l) l∋as∈k₁⇒k₂) b∈k₁ =
      begin
        TK.η-exp j₂ ⌊j₂⌋≡k₂ (weakenElim (var∙ x) ∙∙ weakenSpine as ⌜·⌝
          TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H
            0 ← b ∈ k₁
      ≡⟨ cong (λ y → TK.η-exp _ ⌊j₂⌋≡k₂ (var y ∙ weakenSpine as ⌜·⌝ _) /H _)
              (VarLemmas.lookup-wk x)  ⟩
        TK.η-exp j₂ ⌊j₂⌋≡k₂ (var (suc x) ∙ weakenSpine as ⌜·⌝
          TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H
            0 ← b ∈ k₁
      ≈⟨ η-exp-ne-Miss-/H x ⌊j₂⌋≡k₂ refl j₂-kds′ x+1∙as·η-z∈k₂
                          (∈-hsub [] b∈k₁) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
          (var x ∙ ((weakenSpine as ∷ʳ
            arg (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                          (var∙ zero))) //H 0 ← b ∈ k₁))
      ≡⟨ cong (λ bs → TK.η-exp _ (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var x ∙ bs))
              (++-//H (weakenSpine as) _) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
          (var x ∙ (weakenSpine as //H 0 ← b ∈ k₁) ⌜·⌝
            (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H
              0 ← b ∈ k₁))
      ≡⟨ cong (λ bs → TK.η-exp _ (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var x ∙ bs ⌜·⌝ _))
              (//-wk-↑⋆-hsub-vanishes 0 as) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var x ∙ as ⌜·⌝
          (TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H
            0 ← b ∈ k₁))
      ≈⟨ ≈-η-exp′ (⌊⌋≡-/H ⌊j₂⌋≡k₂) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                  (≈-⌜·⌝ (≈-refl (var x ∙ as))
                         (η-exp-var-Hit-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁) refl
                                           (kds-weaken j₁-kds)
                                           (∈-var zero refl) (∈-hsub [] b∈k₁))) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var x ∙ as ⌜·⌝
          (var∙ zero /H 0 ← b ∈ k₁))
      ≡⟨ cong (λ c → TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                              (var x ∙ as ⌜·⌝ c))
              (⌜⌝∘⌞⌟-id b) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var x ∙ as ⌜·⌝ b)
      ∎
      where
        open ≈-Reasoning
        j₂-kds′ = subst (λ k → kd k ∷ _ ⊢ j₂ kds) (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁) j₂-kds
        kd-l∷Γ[x+1]≡kd-l = trans (lookup-suc x (kd l) [] Γ) Γ[x]≡kd-l
        x+1∈l            = ∈-var (suc x) kd-l∷Γ[x+1]≡kd-l
        l∋as∈k₁⇒k₂′      = Sp∈-weaken l∋as∈k₁⇒k₂
        η-z∈k₁           = η-exp-Var∈ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (kds-weaken j₁-kds)
                                      (∈-var zero refl)
        x+1∙as·η-z∈k₂    = ∈-∙ x+1∈l (∈-∷ʳ l∋as∈k₁⇒k₂′ η-z∈k₁)

    η-exp-ne-⌜π₁⌝ : ∀ {n} {Γ : Ctx n} {a j₁ j₂ k₁ k₂}
                    (hyp₁ : ⌊ j₁ ⌋≡ k₁) (hyp₂ : ⌊ j₂ ⌋≡ k₂) →
                    Γ ⊢Ne a ∈ k₁ ⊗ k₂ →
                    TK.η-exp (Σ j₁ j₂) (at-Σ hyp₁ hyp₂) a ·′⟨ k₁ ⊗ k₂ ⟩ π₁  ≈
                      TK.η-exp j₁ hyp₁ (⌜π₁⌝ a)
    η-exp-ne-⌜π₁⌝ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ (∈-∙ x∈l l∋as∈k₁⊗k₂) = ≈-refl _

    η-exp-ne-⌜π₂⌝ : ∀ {n} {Γ : Ctx n} {a j₁ j₂ k₁ k₂}
                    (hyp₁ : ⌊ j₁ ⌋≡ k₁) (hyp₂ : ⌊ j₂ ⌋≡ k₂) →
                    Γ ⊢Ne a ∈ k₁ ⊗ k₂ →
                    TK.η-exp (Σ j₁ j₂) (at-Σ hyp₁ hyp₂) a ·′⟨ k₁ ⊗ k₂ ⟩ π₂  ≈
                      TK.η-exp (j₂ Kind[ TK.η-exp j₁ hyp₁ (⌜π₁⌝ a) ∈ k₁ ])
                               (⌊⌋≡-/H hyp₂) (⌜π₂⌝ a)
    η-exp-ne-⌜π₂⌝ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ (∈-∙ x∈l l∋as∈k₁⊗k₂) = ≈-refl _

private module TK  = TrackSimpleKindsEtaExp
private module TKK = TrackSimpleKindsKindedEtaExp

-- η-expansion preserves simple kinding of neutral types.

η-exp-Var∈ : ∀ {n} {Γ : Ctx n} {x k} →
             Γ ⊢ k kds → Γ ⊢Var var x ∈ ⌊ k ⌋ → Γ ⊢Nf η-exp k (var∙ x) ∈ ⌊ k ⌋
η-exp-Var∈ k-kd x∈⌊k⌋ = TKK.η-exp-Var∈ (⌊⌋-⌊⌋≡ _) k-kd x∈⌊k⌋

η-exp-Ne∈ : ∀ {n} {Γ : Ctx n} {a k} →
            Γ ⊢ k kds → Γ ⊢Ne a ∈ ⌊ k ⌋ → Γ ⊢Nf η-exp k a ∈ ⌊ k ⌋
η-exp-Ne∈ k-kd a∈⌊k⌋ = TKK.η-exp-Ne∈ (⌊⌋-⌊⌋≡ _) k-kd a∈⌊k⌋

-- η-expansion of neutrals commutes with hereditary substitutions
-- that miss the head of the neutral.
η-exp-ne-Miss-/H : ∀ {k m n Γ Δ} y {x as j} {ρ : HSub k m n} → Miss ρ x y →
                   Γ ⊢ j kds → Γ ⊢Ne var x ∙ as ∈ ⌊ j ⌋ → Δ ⊢/H ρ ∈ Γ →
                   η-exp j (var x ∙ as) /H ρ  ≈
                     η-exp (j Kind/H ρ) (var y ∙ (as //H ρ))
η-exp-ne-Miss-/H y {x} {as} {j} {ρ} miss j-kds x∙as∈k ρ∈Γ =
  begin
    η-exp j (var x ∙ as) /H ρ
  ≈⟨ TKK.η-exp-ne-Miss-/H y (⌊⌋-⌊⌋≡ j) miss j-kds x∙as∈k ρ∈Γ ⟩
    TK.η-exp (j Kind/H ρ) (⌊⌋≡-/H (⌊⌋-⌊⌋≡ j)) (var y ∙ (as //H ρ))
  ≡⟨ TK.η-exp-⌊⌋≡ (⌊⌋≡-/H (⌊⌋-⌊⌋≡ j)) (⌊⌋-⌊⌋≡ (j Kind/H ρ)) refl
                  (sym (⌊⌋-Kind/H j)) ⟩
    η-exp (j Kind/H ρ) (var y ∙ (as //H ρ))
  ∎
  where open ≈-Reasoning

-- η-expansion of neutrals followed by hereditary substitution
-- vanish if the substitution hits the head of the neutral.

η-exp-ne-Hit-/H : ∀ {k m n Γ Δ x as j} {ρ : HSub k m n} →
                  Hit ρ x → Γ ⊢ j kds → Γ ⊢Ne var x ∙ as ∈ ⌊ j ⌋ → Δ ⊢/H ρ ∈ Γ →
                  η-exp j (var x ∙ as) /H ρ  ≈  var x ∙ as /H ρ
η-exp-ne-Hit-/H hit j-kds x∙as∈k ρ∈Γ =
  TKK.η-exp-ne-Hit-/H (⌊⌋-⌊⌋≡ _) hit j-kds x∙as∈k ρ∈Γ

η-exp-var-Hit-/H : ∀ {k m n Γ Δ} {x j} {ρ : HSub k m n} →
                   Hit ρ x → Γ ⊢ j kds → Γ ⊢Var var x ∈ ⌊ j ⌋ → Δ ⊢/H ρ ∈ Γ →
                   η-exp j (var∙ x) /H ρ  ≈  var∙ x /H ρ
η-exp-var-Hit-/H hit j-kds x∈k ρ∈Γ =
  η-exp-ne-Hit-/H hit j-kds (∈-∙ x∈k ∈-[]) ρ∈Γ

-- Hereditary substitutions of a variable by its η-expansion vanish.

kds-[]-η-var : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ j k} →
               Γ₁ ⊢ j kds → Γ₂ ′++ kd ⌊ j ⌋ ∷ Γ₁ ⊢ k kds →
               let j′ = weakenKind′ j
                   k′ = k Kind′/Var (VarSubst.wk VarSubst.↑) VarSubst.↑⋆ n
               in k′ Kind/H (n ← η-exp j′ (var∙ zero) ∈ ⌊ j′ ⌋) ≋ k
kds-[]-η-var Γ₂ {Γ₁} {j} j-kds k-kds =
  TKK.kds-[]-η-var Γ₂ (⌊⌋-⌊⌋≡ _) (kds-weaken j-kds)
                   (subst (λ l → Γ₂ ′++ kd l ∷ Γ₁ ⊢ _ kds)
                          (sym (⌊⌋-Kind′/Var j)) k-kds)

Nf∈-[]-η-var : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a j k} →
               Γ₁ ⊢ j kds → Γ₂ ′++ kd ⌊ j ⌋ ∷ Γ₁ ⊢Nf a ∈ k →
               let j′ = weakenKind′ j
                   a′ = a Elim/Var (VarSubst.wk VarSubst.↑) VarSubst.↑⋆ n
               in a′ /H (n ← η-exp j′ (var∙ zero) ∈ ⌊ j′ ⌋) ≈ a
Nf∈-[]-η-var Γ₂ {Γ₁} {a} {j} j-kds a∈k =
  TKK.Nf∈-[]-η-var Γ₂ (⌊⌋-⌊⌋≡ _) (kds-weaken j-kds)
                   (subst (λ l → Γ₂ ′++ kd l ∷ Γ₁ ⊢Nf _ ∈ _)
                          (sym (⌊⌋-Kind′/Var j)) a∈k)
