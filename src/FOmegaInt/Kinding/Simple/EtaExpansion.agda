------------------------------------------------------------------------
-- η-expansion of simply-kinded types in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

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
open import FOmegaInt.Syntax.SingleVariableSubstitution
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Syntax.WeakEquality
open import FOmegaInt.Kinding.Simple

------------------------------------------------------------------------
-- η-expansion of simply kinded types.
--
-- TODO: explain the point of this and how "simple" kinding differs
-- from "canonical" kinding.

open Syntax
open SimpleCtx
open Substitution hiding (_↑; _↑⋆_; sub; subst)
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
                 Γ ⊢ j kds → Γ ⊢Var x ∈ k →
                 Γ ⊢Nf TK.η-exp j hyp (var∙ x) ∈ k
    η-exp-Var∈ hyp j-kd x∈k = η-exp-Ne∈ hyp j-kd (∈-∙ x∈k ∈-[])

    η-exp-Ne∈ : ∀ {n} {Γ : Ctx n} {a j k} (hyp : ⌊ j ⌋≡ k) →
                Γ ⊢ j kds → Γ ⊢Ne a ∈ k → Γ ⊢Nf TK.η-exp j hyp a ∈ k
    η-exp-Ne∈ is-★ (kds-⋯ b∈* c∈*) a∈★ = ∈-ne a∈★
    η-exp-Ne∈ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (kds-Π j₁-kds j₂-kds)
              (∈-∙ {x} {_} {_} {as} x∈l l∋as∈k₁⇒k₂) =
      subst (λ j → _ ⊢Nf η-x∙as ∈ j ⇒ _) (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
            (∈-Π-i j₁-kds (η-exp-Ne∈ ⌊j₂⌋≡k₂ j₂-kds x∙as·z∈k₂))
      where
        η-x∙as = TK.η-exp _ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as)
        z∈k₁ = η-exp-Var∈ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (kds-weaken j₁-kds)
                          (∈-var zero (cong kd (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)))
        x∙as·z∈k₂ = Ne∈-Π-e (Ne∈-weaken (∈-∙ x∈l l∋as∈k₁⇒k₂)) z∈k₁

  mutual

    -- η-expansion of neutrals followed by hereditary substitution
    -- vanishes if the substitution hits the head of the neutral.

    η-exp-var-Hit-/⟨⟩ : ∀ {k m n Γ Δ} {x a j} (hyp : ⌊ j ⌋≡ k) {σ : SVSub m n} →
                       Hit σ x a → Γ ⊢ j kds → Γ ⊢Var x ∈ k → Δ ⊢/⟨ k ⟩ σ ∈ Γ →
                       TK.η-exp j hyp (var∙ x) /⟨ k ⟩ σ  ≈  var∙ x /⟨ k ⟩ σ
    η-exp-var-Hit-/⟨⟩ hyp hitP j-kds x∈k σ∈Γ =
      η-exp-ne-Hit-/⟨⟩ hyp hitP j-kds (∈-∙ x∈k ∈-[]) σ∈Γ

    η-exp-ne-Hit-/⟨⟩ : ∀ {k l m n Γ Δ} {x a as j} (hyp : ⌊ j ⌋≡ k)
                       {σ : SVSub m n} → Hit σ x a → Γ ⊢ j kds →
                       Γ ⊢Ne var x ∙ as ∈ k → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                       TK.η-exp j hyp (var x ∙ as) /⟨ l ⟩ σ  ≈
                         var x ∙ as /⟨ l ⟩ σ
    η-exp-ne-Hit-/⟨⟩ is-★ hitP j-kds a∈k σ∈Γ = ≈-refl _
    η-exp-ne-Hit-/⟨⟩ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) hitP
                     (kds-Π j₁-kds j₂-kds) (∈-∙ {as = as} x∈l l∋as∈k₁⇒k₂) σ∈Γ
      with lookup-/⟨⟩∈-Hit σ∈Γ x∈l hitP
    η-exp-ne-Hit-/⟨⟩ {l = l} {Γ = Γ} {a = a}
                     (is-⇒ {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) {σ} hitP
                     (kds-Π j₁-kds j₂-kds)
                     (∈-∙ {as = as} (∈-var {l} x Γ[x]≡kd-l) l∋as∈k₁⇒k₂) σ∈Γ
                   | a∈l , refl =
      let hitP-σ↑ = hitP ↑
          ηz      = TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
          as′     = weakenSpine as
          ηz∈k₁   = η-exp-Var∈ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (kds-weaken j₁-kds)
                               (∈-var zero refl)
          kd-l∷Γ[x+1]≡kd-l = trans (lookup-suc x (kd l) [] Γ) Γ[x]≡kd-l
          x+1∈l            = ∈-var (suc x) kd-l∷Γ[x+1]≡kd-l
          l∋as∈k₁⇒k₂′      = Sp∈-weaken l∋as∈k₁⇒k₂
          σ↑∈k₁∷Γ          = ∈-H↑ σ∈Γ
          l∋as//σ∈k₁⇒k₂    = Sp∈-/⟨⟩ l∋as∈k₁⇒k₂ σ∈Γ
          a∙as/σ∈k₁⇒k₂     = Nf∈-∙∙ a∈l l∋as//σ∈k₁⇒k₂
          j′ , a′ , j′-kds , a′∈k₁⇒k₂ , rest = Nf∈-⇒-inv a∙as/σ∈k₁⇒k₂
          ⌊j′⌋≡k₁ , a∙as/σ≡Λj′a′             = rest
          ⌊j₁/σ⌋≡⌊j′⌋ = let open ≡-Reasoning in begin
            ⌊ j₁ Kind/⟨ l ⟩ σ ⌋  ≡⟨ ⌊⌋-Kind/⟨⟩ j₁ ⟩
            ⌊ j₁ ⌋               ≡⟨ ⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁ ⟩
            k₁                   ≡⟨ sym ⌊j′⌋≡k₁ ⟩
            ⌊ j′ ⌋               ∎
          open ≈-Reasoning
      in begin
        TK.η-exp (Π j₁ j₂) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) /⟨ l ⟩ σ
      ≈⟨ ≈-Λ∙ ⌊j₁/σ⌋≡⌊j′⌋ (begin
          TK.η-exp j₂ ⌊j₂⌋≡k₂
            (weakenElim (var x ∙ as) ⌜·⌝ ηz) /⟨ l ⟩ σ ↑
        ≡⟨ cong (λ y → TK.η-exp _ ⌊j₂⌋≡k₂ (var y ∙ as′ ⌜·⌝ ηz) /⟨ l ⟩ σ ↑)
                (VarLemmas.lookup-wk x) ⟩
          TK.η-exp j₂ ⌊j₂⌋≡k₂ (var (suc x) ∙ as′ ⌜·⌝ ηz) /⟨ l ⟩ σ ↑
        ≈⟨ η-exp-ne-Hit-/⟨⟩ ⌊j₂⌋≡k₂ hitP-σ↑
                            (subst (λ k → kd k ∷ _ ⊢ _ kds) (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
                                   j₂-kds)
                            (∈-∙ x+1∈l (∈-∷ʳ l∋as∈k₁⇒k₂′ ηz∈k₁)) σ↑∈k₁∷Γ ⟩
          var (suc x) ∙ as′ ⌜·⌝ ηz /⟨ l ⟩ σ ↑
        ≡⟨ cong (_?∙∙⟨ l ⟩ ((as′ ∷ʳ ηz) //⟨ l ⟩ σ ↑)) (lookup-Hit hitP-σ↑) ⟩
          weakenElim a ∙∙⟨ l ⟩ ((as′ ∷ʳ ηz) //⟨ l ⟩ σ ↑)
        ≡⟨ cong (_ ∙∙⟨ l ⟩_) (++-//⟨⟩ (as′) (_ ∷ [])) ⟩
          weakenElim a ∙∙⟨ l ⟩ (as′ //⟨ l ⟩ σ ↑ ∷ʳ ηz /⟨ l ⟩ σ ↑)
        ≡⟨ Nf∈-++-∙∙⟨⟩ (Nf∈-weaken a∈l) (Sp∈-/⟨⟩ l∋as∈k₁⇒k₂′ σ↑∈k₁∷Γ)
                       (∈-∷ (Nf∈-/⟨⟩ ηz∈k₁ σ↑∈k₁∷Γ) ∈-[]) ⟩
          weakenElim a ∙∙⟨ l ⟩ (as′ //⟨ l ⟩ σ ↑) ⌜·⌝⟨ k₁ ⇒ k₂ ⟩ (ηz /⟨ l ⟩ σ ↑)
        ≡⟨ cong (λ bs → weakenElim a ∙∙⟨ l ⟩ bs ⌜·⌝⟨ k₁ ⇒ k₂ ⟩ (ηz /⟨ l ⟩ σ ↑))
                (wk-//⟨⟩-↑⋆ 0 as) ⟩
          weakenElim a ∙∙⟨ l ⟩ weakenSpine (as //⟨ l ⟩ σ) ⌜·⌝⟨ k₁ ⇒ k₂ ⟩
            (ηz /⟨ l ⟩ σ ↑)
        ≡˘⟨ cong (_⌜·⌝⟨ k₁ ⇒ k₂ ⟩ (ηz /⟨ l ⟩ σ ↑))
                 (∙∙⟨⟩-/Var a l (as //⟨ l ⟩ σ)) ⟩
          weakenElim (a ∙∙⟨ l ⟩ (as //⟨ l ⟩ σ)) ⌜·⌝⟨ k₁ ⇒ k₂ ⟩ (ηz /⟨ l ⟩ σ ↑)
        ≡⟨ cong ((_⌜·⌝⟨ k₁ ⇒ k₂ ⟩ _) ∘ weakenElim) a∙as/σ≡Λj′a′ ⟩
          weakenElim (Λ∙ j′ a′) ⌜·⌝⟨ k₁ ⇒ k₂ ⟩ (ηz /⟨ l ⟩ σ ↑)
        ≡⟨ cong (weakenElim (Λ∙ j′ a′) ⌜·⌝⟨ k₁ ⇒ k₂ ⟩_)
                (TK.η-exp-ne-Miss-/⟨⟩ zero zero (⌊⌋≡-weaken ⌊j₁⌋≡k₁) under) ⟩
          weakenElim (Λ∙ j′ a′) ⌜·⌝⟨ k₁ ⇒ k₂ ⟩
            TK.η-exp (weakenKind′ j₁ Kind/⟨ l ⟩ σ ↑) (⌊⌋≡-/⟨⟩ (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                     (var∙ zero)
        ≈⟨ Nf∈-[]-η-var [] (⌊⌋≡-/⟨⟩ (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                        (kds-/⟨⟩ (kds-weaken j₁-kds) σ↑∈k₁∷Γ) a′∈k₁⇒k₂ ⟩
          a′
        ∎) ⟩
        Λ∙ j′ a′
      ≡⟨ sym a∙as/σ≡Λj′a′ ⟩
        a ∙∙⟨ l ⟩ (as //⟨ l ⟩ σ)
      ≡˘⟨ cong (_?∙∙⟨ l ⟩ (as //⟨ l ⟩ σ)) (lookup-Hit hitP) ⟩
        var x ∙ as /⟨ l ⟩ σ
      ∎

    -- Hereditary substitutions of a variable by its η-expansion vanish.
    --
    -- NOTE.  Both the statement and the proof of this lemma are
    -- complicated by the use of de Bruijn notation in combination
    -- with single-variable (hereditary) substitution.  When
    -- formulated using the usual, human-readable variable notation,
    -- the lemma simply says that
    --
    --   e [ηⱼ(x)/ʲx] = e
    --
    -- where "e [a/ʲx]" denotes hereditary substitution of a for x in
    -- expression e at kind j, and "ηⱼ(x)" denotes the η-expansion of
    -- x at kind j.  Using de Bruijn notation, this substitution only
    -- makes sense if there are actually _two_ copies of the variable
    -- x in e on the LHS (say x and x′): one to be replaced (x) and a
    -- second one (x′) to be η-expanded and substituted for x.  To
    -- make the equation well-scoped, we therefore weaken e to
    -- introduce a new variable x′ = (suc x) just after x, which after
    -- substitution for x will correspond precisely to the de Bruijn
    -- index of x itself.  The stated form of the lemma is obtained by
    -- letting x be the n-th variable in a context with (n + m) free
    -- variables, i.e. we fix x = (raise n zero) in e.
    --
    -- Note also that the proof of this lemma is currently the only
    -- place in the development where the Eq? predicate from the
    -- FOmegaInt.Syntax.SingleVariableSubstitution module is used.
    -- It's probably possible to reformulate the proof without using
    -- this predicate, but that will likely render the proof even
    -- harder to follow than it already is.

    kds-[]-η-var : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ j l}
                   (hyp : ⌊ j ⌋≡ k) → kd k ∷ Γ₁ ⊢ j kds →
                   Γ₂ ′++ kd k ∷ Γ₁ ⊢ l kds →
                   let l′ = l Kind′/Var (V.wk V.↑) V.↑⋆ n
                   in l′ Kind/⟨ k ⟩ sub (TK.η-exp j hyp (var∙ zero)) ↑⋆ n ≋ l
    kds-[]-η-var Γ₂ hyp j-kds (kds-⋯ a∈★ b∈★) =
      ≋-⋯ (Nf∈-[]-η-var Γ₂ hyp j-kds a∈★) (Nf∈-[]-η-var Γ₂ hyp j-kds b∈★)
    kds-[]-η-var Γ₂ hyp j-kds (kds-Π k-kds l-kds) =
      ≋-Π (kds-[]-η-var Γ₂ hyp j-kds k-kds)
          (kds-[]-η-var (_ ∷ Γ₂) hyp j-kds l-kds)

    Nf∈-[]-η-var : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a j l}
                   (hyp : ⌊ j ⌋≡ k) → kd k ∷ Γ₁ ⊢ j kds →
                   Γ₂ ′++ kd k ∷ Γ₁ ⊢Nf a ∈ l →
                   let a′ = a Elim/Var (V.wk V.↑) V.↑⋆ n
                   in a′ /⟨ k ⟩ sub (TK.η-exp j hyp (var∙ zero)) ↑⋆ n ≈ a
    Nf∈-[]-η-var Γ₂ hyp j-kds ∈-⊥-f = ≈-refl ⊥∙
    Nf∈-[]-η-var Γ₂ hyp j-kds ∈-⊤-f = ≈-refl ⊤∙
    Nf∈-[]-η-var Γ₂ hyp j-kds (∈-∀-f k-kds a∈★) =
      ≈-∀∙ (kds-[]-η-var Γ₂ hyp j-kds k-kds)
           (Nf∈-[]-η-var (_ ∷ Γ₂) hyp j-kds a∈★)
    Nf∈-[]-η-var Γ₂ hyp j-kds (∈-→-f a∈★ b∈★) =
      ≈-⇒∙ (Nf∈-[]-η-var Γ₂ hyp j-kds a∈★) (Nf∈-[]-η-var Γ₂ hyp j-kds b∈★)
    Nf∈-[]-η-var {k} {_} {n} Γ₂ hyp j-kds (∈-Π-i {l} l-kds a∈k) =
      let open ≡-Reasoning
          ρ = (V.wk V.↑) V.↑⋆ n
          σ = sub (TK.η-exp _ hyp (var∙ zero)) ↑⋆ n
      in ≈-Λ∙ (begin
             ⌊ l Kind′/Var ρ Kind/⟨ k ⟩ σ ⌋  ≡⟨ ⌊⌋-Kind/⟨⟩ (l Kind′/Var ρ) ⟩
             ⌊ l Kind′/Var ρ ⌋               ≡⟨ ⌊⌋-Kind′/Var l ⟩
             ⌊ l ⌋                           ∎)
           (Nf∈-[]-η-var (_ ∷ Γ₂) hyp j-kds a∈k)
    Nf∈-[]-η-var {_} {_} {n} Γ₂ hyp j-kds (∈-ne (∈-∙ (∈-var x _) k∋as∈★))
      with compare n x
    Nf∈-[]-η-var {k} {_} {n} Γ₂ {Γ₁} {_} {j} hyp j-kds
                 (∈-ne (∈-∙ {as = as} (∈-var ._ Γ[x]≡kd-k′) k′∋as∈★))
      | yes refl =
      begin
        lookupSV σ (x V./ (V.wk V.↑) V.↑⋆ n) ?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)
      ≡⟨ cong (λ z → lookupSV σ z ?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ))
              (lookup-raise-↑⋆ n zero refl) ⟩
        lookupSV σ (raise n zero) ?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)
      ≡⟨ cong (_?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)) (lookup-Hit hitP) ⟩
        weakenElim⋆ n ηz ∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)
      ≡˘⟨ cong (_∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)) (EL./Var-wk⋆ n) ⟩
        (ηz Elim/Var V.wk⋆ n) ∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)
      ≈⟨ ≈-∙∙⟨⟩ k (≈-refl _) (Sp∈-[]-η-var Γ₂ hyp j-kds k∋as∈★) ⟩
        (ηz Elim/Var V.wk⋆ n) ∙∙⟨ k ⟩ as
      ≡⟨ cong (_∙∙⟨ k ⟩ as) (TK.η-exp-/Var hyp (var∙ zero)) ⟩
        TK.η-exp (j Kind′/Var V.wk⋆ n) (⌊⌋≡-/Var hyp)
                 (var∙ zero Elim/Var V.wk⋆ n) ∙∙⟨ k ⟩ as
      ≡⟨ cong (λ y → TK.η-exp (j Kind′/Var V.wk⋆ n) (⌊⌋≡-/Var hyp)
                              (var∙ y) ∙∙⟨ k ⟩ as)
              (lookup-wk⋆ zero n) ⟩
        TK.η-exp (j Kind′/Var V.wk⋆ n) (⌊⌋≡-/Var hyp) (var∙ x) ∙∙⟨ k ⟩ as
      ≈⟨ η-exp-ne-∙∙ (⌊⌋≡-/Var hyp)
                     (subst (_ ⊢_kds) (sym (KL./Var-wk⋆ n))
                            (kds-weaken⋆ Γ₂ j-kds))
                     (∈-∙ (∈-var x Γ[x]≡kd-k) ∈-[]) k∋as∈★ ⟩
        var x ∙ as
      ∎
      where
        x = raise n zero
        Γ = Γ₂ ′++ kd k ∷ Γ₁

        Γ[x]≡kd-k = begin
          lookup (raise n zero) Γ   ≡⟨ lookup-weaken⋆′ n zero [] Γ₂ _ ⟩
          weakenSAsc⋆ n (kd k)      ≡⟨ weakenSAsc⋆-id n ⟩
          kd k                      ∎
          where open ≡-Reasoning

        ηz     = TK.η-exp j hyp (var∙ zero)
        σ      = sub ηz ↑⋆ n
        as′    = as //Var (V.wk V.↑) V.↑⋆ n
        hitP   = Hit-sub-↑⋆ n
        k′≡k   = kd-inj′ (trans (sym Γ[x]≡kd-k′) Γ[x]≡kd-k)
        k∋as∈★ = subst (_ ⊢_∋∙ _ ∈ _) k′≡k k′∋as∈★

        open ≈-Reasoning
        open ExtLemmas₁ VarLemmas.lemmas₁ using (lookup-wk⋆; lookup-raise-↑⋆)
        module EL = TermLikeLemmas termLikeLemmasElim
        module KL = TermLikeLemmas termLikeLemmasKind′
    Nf∈-[]-η-var {k} {_} {n} Γ₂ {_} {_} {j} hyp j-kds
                 (∈-ne (∈-∙ {as = as} (∈-var ._ Γ[x]≡kd-k′) k′∋as∈★))
      | no y refl =
      begin
        lookupSV σ (x V./ (V.wk V.↑) V.↑⋆ n) ?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)
      ≡⟨ cong (λ z → lookupSV σ z ?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)) eq ⟩
        lookupSV σ (lift n suc x) ?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)
      ≡⟨ cong (_?∙∙⟨ k ⟩ (as′ //⟨ k ⟩ σ)) (lookup-Miss (Miss-sub-↑⋆ n x)) ⟩
        var x ∙ (as′ //⟨ k ⟩ σ)
      ≈⟨ ≈-∙ (≈-var x) (Sp∈-[]-η-var Γ₂ hyp j-kds k′∋as∈★) ⟩
        var x ∙ as
      ∎
      where
        x   = lift n suc y
        ηz  = TK.η-exp j hyp (var∙ zero)
        σ   = sub ηz ↑⋆ n
        as′ = as //Var (V.wk V.↑) V.↑⋆ n

        eq = begin
          x V./ (V.wk V.↑) V.↑⋆ n       ≡⟨ VarLemmas.lookup-wk-↑⋆-↑⋆ 1 n x ⟩
          lift n (lift 1 suc) x               ≡⟨⟩
          lift n (lift 1 suc) (lift n suc y)  ≡⟨ sym (lift-commutes 0 n y) ⟩
          lift n suc (lift n suc y)           ≡⟨⟩
          lift n suc x                        ∎
          where open ≡-Reasoning

        open ≈-Reasoning

    Sp∈-[]-η-var : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ as j l₁ l₂}
                   (hyp : ⌊ j ⌋≡ k) → kd k ∷ Γ₁ ⊢ j kds →
                   Γ₂ ′++ kd k ∷ Γ₁ ⊢ l₁ ∋∙ as ∈ l₂ →
                   let as′ = as //Var (V.wk V.↑) V.↑⋆ n
                   in as′ //⟨ k ⟩ sub (TK.η-exp j hyp (var∙ zero)) ↑⋆ n ≈Sp as
    Sp∈-[]-η-var Γ₂ hyp j-kds ∈-[] = ≈-[]
    Sp∈-[]-η-var Γ₂ hyp j-kds (∈-∷ a∈l₁ l₂∋as∈l₃) =
      ≈-∷ (Nf∈-[]-η-var Γ₂ hyp j-kds a∈l₁) (Sp∈-[]-η-var Γ₂ hyp j-kds l₂∋as∈l₃)

    -- Reducing applications cancel out η-expansion of neutrals.

    η-exp-ne-∙∙ : ∀ {n} {Γ : Ctx n} {a bs j k} (hyp : ⌊ j ⌋≡ k) →
                  Γ ⊢ j kds → Γ ⊢Ne a ∈ k → Γ ⊢ k ∋∙ bs ∈ ★ →
                  TK.η-exp j hyp a ∙∙⟨ k ⟩ bs  ≈  a ∙∙ bs
    η-exp-ne-∙∙ is-★ j-kds a∈k ∈-[] = subst (_ ≈_) (sym (∙∙-[] _)) (≈-refl _)
    η-exp-ne-∙∙ {a = a} (is-⇒ {j₁} {j₂} {k₁} {k₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
                (kds-Π j₁-kds j₂-kds) a∈k₁⇒k₂ (∈-∷ {b} {bs} b∈k₁ k₂∋bs∈★) =
      begin
        TK.η-exp (Π j₁ j₂) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a ⌜·⌝⟨ k₁ ⇒ k₂ ⟩ b ∙∙⟨ k₂ ⟩ bs
      ≈⟨ ≈-∙∙⟨⟩ k₂ (η-exp-ne-⌜·⌝ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ j₁-kds a∈k₁⇒k₂ b∈k₁)
                (≈Sp-refl bs) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (a ⌜·⌝ b) ∙∙⟨ k₂ ⟩ bs
      ≈⟨ η-exp-ne-∙∙ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) j₂[b]-kds (Ne∈-Π-e a∈k₁⇒k₂ b∈k₁) k₂∋bs∈★ ⟩
        (a ⌜·⌝ b) ∙∙ bs
      ≡⟨ ∙∙-++ a (b ∷ []) bs ⟩
        a ∙∙ (b ∷ bs)
      ∎
      where
        open ≈-Reasoning
        j₂[b]-kds = kds-/⟨⟩ (subst (λ k → kd k ∷ _ ⊢ j₂ kds)
                                   (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁) j₂-kds)
                            (∈-hsub b∈k₁)

    η-exp-ne-⌜·⌝ : ∀ {n} {Γ : Ctx n} {a b j₁ j₂ k₁ k₂}
                   (hyp₁ : ⌊ j₁ ⌋≡ k₁) (hyp₂ : ⌊ j₂ ⌋≡ k₂) →
                   Γ ⊢ j₁ kds → Γ ⊢Ne a ∈ k₁ ⇒ k₂ → Γ ⊢Nf b ∈ k₁ →
                   TK.η-exp (Π j₁ j₂) (is-⇒ hyp₁ hyp₂) a ⌜·⌝⟨ k₁ ⇒ k₂ ⟩ b  ≈
                     TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ hyp₂) (a ⌜·⌝ b)
    η-exp-ne-⌜·⌝ {b = b} {j₁} {j₂} {k₁} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂ j₁-kds
                 (∈-∙ {x} {_} {_} {as} x∈l l∋as∈k₁⇒k₂) b∈k₁ =
      let ηz = TK.η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
      in begin
        TK.η-exp j₂ ⌊j₂⌋≡k₂
                 (weakenElim (var∙ x) ∙∙ weakenSpine as ⌜·⌝ ηz) /⟨ k₁ ⟩ sub b
      ≡⟨ cong (λ y → TK.η-exp _ ⌊j₂⌋≡k₂ (var y ∙ weakenSpine as ⌜·⌝ ηz) /⟨ k₁ ⟩ _)
              (VarLemmas.lookup-wk x)  ⟩
        TK.η-exp j₂ ⌊j₂⌋≡k₂ (var (suc x) ∙ weakenSpine as ⌜·⌝ ηz) /⟨ k₁ ⟩ sub b
      ≡⟨ TK.η-exp-ne-Miss-/⟨⟩ (suc x) x ⌊j₂⌋≡k₂ over ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
          (var x ∙ ((weakenSpine as ∷ʳ ηz) //⟨ k₁ ⟩ sub b))
      ≡⟨ cong (λ bs → TK.η-exp _ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (var x ∙ bs))
              (++-//⟨⟩ (weakenSpine as) _) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
          (var x ∙ (weakenSpine as //⟨ k₁ ⟩ sub b) ⌜·⌝ (ηz /⟨ k₁ ⟩ sub b))
      ≡⟨ cong (λ bs → TK.η-exp _ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (var x ∙ bs ⌜·⌝ _))
              (//Var-wk-↑⋆-hsub-vanishes 0 as) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
                 (var x ∙ as ⌜·⌝ (ηz /⟨ k₁ ⟩ sub b))
      ≈⟨ ≈-η-exp′ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
                  (≈-⌜·⌝ (≈-refl (var x ∙ as))
                         (η-exp-var-Hit-/⟨⟩ (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (Hit-sub-↑⋆ 0)
                                            (kds-weaken j₁-kds)
                                            (∈-var zero refl) (∈-hsub b∈k₁))) ⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (var x ∙ as ⌜·⌝
          (var∙ zero /⟨ k₁ ⟩ sub b))
      ≡⟨⟩
        TK.η-exp (j₂ Kind[ b ∈ k₁ ]) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (var x ∙ as ⌜·⌝ b)
      ∎
      where open ≈-Reasoning

private module TK = TrackSimpleKindsKindedEtaExp

-- η-expansion preserves simple kinding of neutral types.

η-exp-Var∈ : ∀ {n} {Γ : Ctx n} {x k} →
             Γ ⊢ k kds → Γ ⊢Var x ∈ ⌊ k ⌋ → Γ ⊢Nf η-exp k (var∙ x) ∈ ⌊ k ⌋
η-exp-Var∈ k-kd x∈⌊k⌋ = TK.η-exp-Var∈ (⌊⌋-⌊⌋≡ _) k-kd x∈⌊k⌋

η-exp-Ne∈ : ∀ {n} {Γ : Ctx n} {a k} →
            Γ ⊢ k kds → Γ ⊢Ne a ∈ ⌊ k ⌋ → Γ ⊢Nf η-exp k a ∈ ⌊ k ⌋
η-exp-Ne∈ k-kd a∈⌊k⌋ = TK.η-exp-Ne∈ (⌊⌋-⌊⌋≡ _) k-kd a∈⌊k⌋

-- η-expansion of neutrals followed by hereditary substitution
-- vanish if the substitution hits the head of the neutral.

η-exp-ne-Hit-/⟨⟩ : ∀ {k m n Γ Δ} {x a as j} {σ : SVSub m n} →
                   Hit σ x a → Γ ⊢ j kds → Γ ⊢Ne var x ∙ as ∈ ⌊ j ⌋ →
                   Δ ⊢/⟨ k ⟩ σ ∈ Γ →
                   η-exp j (var x ∙ as) /⟨ k ⟩ σ  ≈  var x ∙ as /⟨ k ⟩ σ
η-exp-ne-Hit-/⟨⟩ hitP j-kds x∙as∈k σ∈Γ =
  TK.η-exp-ne-Hit-/⟨⟩ (⌊⌋-⌊⌋≡ _) hitP j-kds x∙as∈k σ∈Γ

η-exp-var-Hit-/⟨⟩ : ∀ {k m n Γ Δ} {x a j} {σ : SVSub m n} →
                    Hit σ x a → Γ ⊢ j kds → Γ ⊢Var x ∈ ⌊ j ⌋ →
                    Δ ⊢/⟨ k ⟩ σ ∈ Γ →
                    η-exp j (var∙ x) /⟨ k ⟩ σ  ≈  var∙ x /⟨ k ⟩ σ
η-exp-var-Hit-/⟨⟩ hitP j-kds x∈k σ∈Γ =
  η-exp-ne-Hit-/⟨⟩ hitP j-kds (∈-∙ x∈k ∈-[]) σ∈Γ

-- Hereditary substitutions of a variable by its η-expansion vanish.

kds-[]-η-var : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ j k} →
               Γ₁ ⊢ j kds → Γ₂ ′++ kd ⌊ j ⌋ ∷ Γ₁ ⊢ k kds →
               let j′ = weakenKind′ j
                   k′ = k Kind′/Var (VarSubst.wk VarSubst.↑) VarSubst.↑⋆ n
               in k′ Kind/⟨ ⌊ j′ ⌋ ⟩ sub (η-exp j′ (var∙ zero)) ↑⋆ n ≋ k
kds-[]-η-var Γ₂ {Γ₁} {j} j-kds k-kds =
  TK.kds-[]-η-var Γ₂ (⌊⌋-⌊⌋≡ _) (kds-weaken j-kds)
                  (subst (λ l → Γ₂ ′++ kd l ∷ Γ₁ ⊢ _ kds)
                         (sym (⌊⌋-Kind′/Var j)) k-kds)

Nf∈-[]-η-var : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ a j k} →
               Γ₁ ⊢ j kds → Γ₂ ′++ kd ⌊ j ⌋ ∷ Γ₁ ⊢Nf a ∈ k →
               let j′ = weakenKind′ j
                   a′ = a Elim/Var (VarSubst.wk VarSubst.↑) VarSubst.↑⋆ n
               in a′ /⟨ ⌊ j′ ⌋ ⟩ sub (η-exp j′ (var∙ zero)) ↑⋆ n ≈ a
Nf∈-[]-η-var Γ₂ {Γ₁} {a} {j} j-kds a∈k =
  TK.Nf∈-[]-η-var Γ₂ (⌊⌋-⌊⌋≡ _) (kds-weaken j-kds)
                  (subst (λ l → Γ₂ ′++ kd l ∷ Γ₁ ⊢Nf _ ∈ _)
                         (sym (⌊⌋-Kind′/Var j)) a∈k)
