------------------------------------------------------------------------
-- Soundness of normalization w.r.t. to declarative kinding of Fω with
-- interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Kinding.Declarative.Normalization where

open import Data.Fin using (zero)
open import Data.Fin.Substitution
open import Data.Product using (_,_; proj₂; _×_)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Typing
open import FOmegaInt.Typing.Validity

open Syntax
open TermCtx
open Substitution hiding (subst)
open ContextConversions
open Typing
open TypedSubstitution


------------------------------------------------------------------------
-- Soundness of hereditary substitutions

-- NOTE. The following are corollaries of the corresponding soundness
-- lemmas using untyped β-reduction and the subject reduction property
-- for kinding (see the Syntax.HereditarySubstitution and
-- Typing.Validity modules for details).

-- Soundness of hereditary substitution: the results of ordinary and
-- hereditary substitutions in well-formed kinds resp. well-kinded
-- types are equal (w.r.t. type resp. kind equality).

kd-⌞⌟-[]-≅ : ∀ {n} {Γ : Ctx n} {j k a} →
             kd ⌞ j ⌟Kd ∷ Γ ⊢ ⌞ k ⌟Kd kd → Γ ⊢Tp ⌞ a ⌟ ∈ ⌞ j ⌟Kd →
             Γ ⊢ ⌞ k ⌟Kd Kind[ ⌞ a ⌟ ] ≅ ⌞ k Kind[ a ∈ ⌊ j ⌋ ] ⌟Kd
kd-⌞⌟-[]-≅ {k = k} ⌞k⌟-kd ⌞a⌟∈⌞j⌟ =
  kd-→β*-≅ (kd-[] ⌞k⌟-kd (∈-tp ⌞a⌟∈⌞j⌟)) (⌞⌟Kd-/⟨⟩-β k)

Tp∈-⌞⌟-[]-≃ : ∀ {n} {Γ : Ctx n} {j a k b} →
              kd ⌞ j ⌟Kd ∷ Γ ⊢Tp ⌞ a ⌟ ∈ ⌞ k ⌟Kd → Γ ⊢Tp ⌞ b ⌟ ∈ ⌞ j ⌟Kd →
              Γ ⊢ ⌞ a ⌟ [ ⌞ b ⌟ ] ≃ ⌞ a [ b ∈ ⌊ j ⌋ ] ⌟ ∈ ⌞ k ⌟Kd Kind[ ⌞ b ⌟ ]
Tp∈-⌞⌟-[]-≃ {a = a} ⌞a⌟∈⌞k⌟ ⌞b⌟∈⌞j⌟ =
  Tp∈-→β*-≃ (Tp∈-[] ⌞a⌟∈⌞k⌟ (∈-tp ⌞b⌟∈⌞j⌟)) (⌞⌟-/⟨⟩-β a)

-- Soundness of potentially reducing application: ordinary and
-- potentially reducing application of well-kinded types are equal
-- (w.r.t. type equality).
Tp∈-⌞⌟-·-≃ : ∀ {n} {Γ : Ctx n} {a b j k} →
             Γ ⊢Tp ⌞ a ⌟ ∈ Π j k → Γ ⊢Tp ⌞ b ⌟ ∈ j →
             Γ ⊢ ⌞ a ⌟ · ⌞ b ⌟ ≃ ⌞ a ↓⌜·⌝ b ⌟ ∈ k Kind[ ⌞ b ⌟ ]
Tp∈-⌞⌟-·-≃ {_} {_} {a} {b} {j} {k} ⌞a⌟∈Πjk ⌞b⌟∈j =
  Tp∈-→β*-≃ (∈-Π-e ⌞a⌟∈Πjk ⌞b⌟∈j) (⌞⌟-↓⌜·⌝-β a b)


------------------------------------------------------------------------
-- Soundness of η-expansion.

module TrackSimpleKindsDeclarativeEtaExp where
  open RenamingCommutes
  open SimpHSubstLemmas
  private
    module V   = VarSubst
    module TK  = TrackSimpleKindsEtaExp

  -- NOTE. The definition of the function Tp∈-⌞⌟-≃-η below is
  -- structurally recursive in the *simple* kind parameter k, but
  -- *not* in the kind j because we need to weaken the domain j₁ of
  -- the dependent kind (j = Π j₁ j₂) in the arrow case.  The
  -- additional hypothesis ⌊ j ⌋≡ k ensures that k is indeed the
  -- simplification of the kind j.

  -- Well-kinded neutrals are equal to to their η-expansions.
  Tp∈-⌞⌟-≃-η : ∀ {n} {Γ : Ctx n} {x as j k} (hyp : ⌊ j ⌋≡ k) →
               Γ ⊢ ⌞ j ⌟Kd kd → Γ ⊢Tp ⌞ var x ∙ as ⌟ ∈ ⌞ j ⌟Kd →
               Γ ⊢ ⌞ var x ∙ as ⌟ ≃ ⌞ TK.η-exp j hyp (var x ∙ as) ⌟ ∈ ⌞ j ⌟Kd
  Tp∈-⌞⌟-≃-η is-★ ⌞b₂⋯c₂⌟-kd ⌞x∙as⌟∈⌞b₁⋯c₁⌟ = ≃-refl ⌞x∙as⌟∈⌞b₁⋯c₁⌟
  Tp∈-⌞⌟-≃-η {_} {Γ} {x} {as} (is-⇒ {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
             (kd-Π ⌞j₁⌟-kd ⌞j₂⌟-kd) ⌞x∙as⌟∈⌞Πj₁j₂⌟ =
    begin
      ⌞ var x ∙ as ⌟
    ≃⟨ ≃-sym (≃-η ⌞x∙as⌟∈⌞Πj₁j₂⌟) ⟩
      Λ ⌞ j₁ ⌟Kd (weaken ⌞ var x ∙ as ⌟ · var zero)
    ≃⟨ ≃-λ′ (≅-refl ⌞j₁⌟-kd) (begin
        weaken ⌞ var x ∙ as ⌟ · var zero
      ≃⟨ ⌞x∙as⌟·z≃⌞x∙as⌟·⌞η-z⌟∈⌞j₂⌟ ⟩
        weaken ⌞ var x ∙ as ⌟ ·
          ⌞ TK.η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟
      ≡⟨ ⌞x∙as⌟·⌞η-z⌟≡⌞x∙as⌜·⌝η-z⌟ ⟩
        ⌞ weakenElim (var x ∙ as) ⌜·⌝
          TK.η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟
      ≃⟨ Tp∈-⌞⌟-≃-η ⌊j₂⌋≡k₂ ⌞j₂⌟-kd
                    (subst (_ ⊢Tp_∈ _) ⌞x∙as⌟·⌞η-z⌟≡⌞x∙as⌜·⌝η-z⌟
                           ⌞x∙as⌟·⌞η-z⌟∈⌞j₂⌟) ⟩
        ⌞ TK.η-exp j₂ ⌊j₂⌋≡k₂ _ ⌟
      ∎) ⟩
      ⌞ TK.η-exp (Π j₁ j₂) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) ⌟
    ∎
    where
      ⌞j₁⌟-wf     = wf-kd ⌞j₁⌟-kd
      ⌞j₁⌟′-kd    = kd-weaken ⌞j₁⌟-wf ⌞j₁⌟-kd
      ⌞j₁⌟′≡⌞j₁′⌟ = sym (⌞⌟Kd-/Var j₁)
      ⌞j₁′⌟-kd    = subst (kd ⌞ j₁ ⌟Kd ∷ _ ⊢_kd) ⌞j₁⌟′≡⌞j₁′⌟ ⌞j₁⌟′-kd
      ⌞j₁⌟∷Γ-ctx  = ⌞j₁⌟-wf ∷ Tp∈-ctx ⌞x∙as⌟∈⌞Πj₁j₂⌟

      ⌞x∙as⌟′∈⌞Πj₁j₂′⌟ = subst (kd ⌞ j₁ ⌟Kd ∷ Γ ⊢Tp weaken ⌞ var x ∙ as ⌟ ∈_)
                               (sym (⌞⌟Kd-/Var (Π j₁ j₂)))
                               (Tp∈-weaken ⌞j₁⌟-wf ⌞x∙as⌟∈⌞Πj₁j₂⌟)

      z∈⌞j₁⌟      = ∈-var zero ⌞j₁⌟∷Γ-ctx (cong kd ⌞j₁⌟′≡⌞j₁′⌟ )
      z≃η-z∈⌞j₁⌟  = Tp∈-⌞⌟-≃-η (⌊⌋≡-weaken ⌊j₁⌋≡k₁) ⌞j₁′⌟-kd z∈⌞j₁⌟
      ⌞j₂′⌟[z]≡⌞j₂⌟ =
        begin
          ⌞ j₂ Kind′/Var V.wk V.↑ ⌟Kd Kind[ var zero ]
        ≡⟨ cong (_Kind[ var zero ]) (⌞⌟Kd-/Var j₂) ⟩
          (⌞ j₂ ⌟Kd Kind/Var V.wk V.↑) Kind[ var zero ]
        ≡⟨ Kind-wk↑-sub-zero-vanishes ⌞ j₂ ⌟Kd ⟩
          ⌞ j₂ ⌟Kd
        ∎
        where open ≡-Reasoning

      ⌞x∙as⌟·z≃⌞x∙as⌟·⌞η-z⌟∈⌞j₂⌟ =
        subst (_ ⊢ _ ≃ _ ∈_) ⌞j₂′⌟[z]≡⌞j₂⌟
              (≃-· (≃-refl (⌞x∙as⌟′∈⌞Πj₁j₂′⌟)) z≃η-z∈⌞j₁⌟)
      ⌞x∙as⌟·⌞η-z⌟∈⌞j₂⌟ = proj₂ (≃-valid ⌞x∙as⌟·z≃⌞x∙as⌟·⌞η-z⌟∈⌞j₂⌟)
      ⌞x∙as⌟·⌞η-z⌟≡⌞x∙as⌜·⌝η-z⌟ =
        begin
          weaken ⌞ var x ∙ as ⌟ ·
            ⌞ TK.η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟
        ≡⟨ cong (_· _) (sym (⌞⌟-/Var (var x ∙ as)))  ⟩
          ⌞ weakenElim (var x ∙ as) ⌟ ·
            ⌞ TK.η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟
        ≡⟨ sym (⌞⌟-· (weakenElim (var x ∙ as)) _) ⟩
          ⌞ weakenElim (var x ∙ as) ⌜·⌝
            TK.η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟
        ∎
        where open ≡-Reasoning

      open ≃-Reasoning

private module TK  = TrackSimpleKindsDeclarativeEtaExp

-- Soundness of η-expansion of neutrals: well-kinded neutral types are
-- equal to their η-expansions (w.r.t. to type equality).
Tp∈-⌞⌟-≃-η : ∀ {n} {Γ : Ctx n} {x as k} →
             Γ ⊢Tp ⌞ var x ∙ as ⌟ ∈ ⌞ k ⌟Kd →
             Γ ⊢ ⌞ var x ∙ as ⌟ ≃ ⌞ η-exp k (var x ∙ as) ⌟ ∈ ⌞ k ⌟Kd
Tp∈-⌞⌟-≃-η ⌞x∙as⌟∈⌞k⌟ =
  TK.Tp∈-⌞⌟-≃-η (⌊⌋-⌊⌋≡ _) (Tp∈-valid ⌞x∙as⌟∈⌞k⌟) ⌞x∙as⌟∈⌞k⌟


------------------------------------------------------------------------
-- Soundness of normalization

mutual

  -- Soundness of normalization: well-formed kinds and well-kinded
  -- types are equal to their normal forms (w.r.t. to kind resp. type
  -- equality).

  Tp∈-≃-⌞⌟-nf : ∀ {n} {Γ : Ctx n} {a k} →
                Γ ⊢Tp a ∈ k → Γ ⊢ a ≃ ⌞ nf (nfCtx Γ) a ⌟ ∈ k
  Tp∈-≃-⌞⌟-nf {_} {Γ} (∈-var {k} x Γ-ctx Γ[x]≡kd-k)
    with ElimCtx.lookup (nfCtx Γ) x | nfCtx-lookup-kd x Γ Γ[x]≡kd-k
  ... | kd ._ | refl =
    ≃-⇑ (Tp∈-⌞⌟-≃-η (∈-⇑ (∈-var x Γ-ctx Γ[x]≡kd-k) (≅⇒<∷ k≅⌞nf-k⌟)))
        (≅⇒<∷ (≅-sym k≅⌞nf-k⌟))
    where
      open ≡-Reasoning
      open CtxEqOps using (lookup-≃-kd)

      Γ≃⌞nf-Γ⌟         = ctx-≃-⌞⌟-nf Γ-ctx
      ⌞nf-Γ⌟[x]≡kd-⌞k⌟ = begin
          lookup ⌞ nfCtx Γ ⌟Ctx x
        ≡⟨ ⌞⌟Asc-lookup (nfCtx Γ) x ⟩
          ⌞ ElimCtx.lookup (nfCtx Γ) x ⌟Asc
        ≡⟨ cong ⌞_⌟Asc (nfCtx-lookup-kd x Γ Γ[x]≡kd-k) ⟩
          kd ⌞ nfKind (nfCtx Γ) k ⌟Kd
        ∎

      k≅⌞nf-k⌟ : Γ ⊢ k ≅ ⌞ nfKind (nfCtx Γ) k ⌟Kd
      k≅⌞nf-k⌟ = lookup-≃-kd x Γ≃⌞nf-Γ⌟ Γ[x]≡kd-k ⌞nf-Γ⌟[x]≡kd-⌞k⌟
  Tp∈-≃-⌞⌟-nf (∈-⊥-f Γ-ctx) = ≃-refl (∈-⊥-f Γ-ctx)
  Tp∈-≃-⌞⌟-nf (∈-⊤-f Γ-ctx) = ≃-refl (∈-⊤-f Γ-ctx)
  Tp∈-≃-⌞⌟-nf (∈-∀-f k-kd a∈*) = ≃-∀ (kd-≅-⌞⌟-nf k-kd) (Tp∈-≃-⌞⌟-nf a∈*)
  Tp∈-≃-⌞⌟-nf (∈-→-f a∈* b∈*)  = ≃-→ (Tp∈-≃-⌞⌟-nf a∈*) (Tp∈-≃-⌞⌟-nf b∈*)
  Tp∈-≃-⌞⌟-nf (∈-Π-i j-kd a∈k) = ≃-λ′ (kd-≅-⌞⌟-nf j-kd) (Tp∈-≃-⌞⌟-nf a∈k)
  Tp∈-≃-⌞⌟-nf {_} {Γ} (∈-Π-e {a} {b} {j} {k} a∈Πjk b∈j) with Tp∈-valid a∈Πjk
  ... | (kd-Π j-kd k-kd) =
    begin
      a · b
    ≃⟨ ≃-· a≃⌞nf-a⌟∈Πjk b≃⌞nf-b⌟∈j ⟩
      ⌞ nf (nfCtx Γ) a ⌟ · ⌞ nf (nfCtx Γ) b ⌟
    ≃⟨ ≃-⇑ (Tp∈-⌞⌟-·-≃ {a = nf (nfCtx Γ) a} {nf (nfCtx Γ) b}
                       ⌞nf-a⌟∈Πjk ⌞nf-b⌟∈j)
           (≅⇒<∷ (≅-sym (kd-[≃] k-kd b≃⌞nf-b⌟∈j))) ⟩
      ⌞ nf (nfCtx Γ) a ↓⌜·⌝ nf (nfCtx Γ) b ⌟
    ∎
    where
      open ≃-Reasoning

      a≃⌞nf-a⌟∈Πjk = Tp∈-≃-⌞⌟-nf a∈Πjk
      ⌞nf-a⌟∈Πjk   = proj₂ (≃-valid a≃⌞nf-a⌟∈Πjk)

      b≃⌞nf-b⌟∈j = Tp∈-≃-⌞⌟-nf b∈j
      ⌞nf-b⌟∈j   = proj₂ (≃-valid b≃⌞nf-b⌟∈j)
  Tp∈-≃-⌞⌟-nf (∈-s-i a∈b⋯c)  = ≃-s-i (Tp∈-≃-⌞⌟-nf a∈b⋯c)
  Tp∈-≃-⌞⌟-nf (∈-⇑ a∈j j<∷k) = ≃-⇑ (Tp∈-≃-⌞⌟-nf a∈j) j<∷k

  kd-≅-⌞⌟-nf : ∀ {n} {Γ : Ctx n} {k} →
               Γ ⊢ k kd → Γ ⊢ k ≅ ⌞ nfKind (nfCtx Γ) k ⌟Kd
  kd-≅-⌞⌟-nf (kd-⋯ a∈* b∈*)   = ≅-⋯ (Tp∈-≃-⌞⌟-nf a∈* ) (Tp∈-≃-⌞⌟-nf b∈*)
  kd-≅-⌞⌟-nf (kd-Π j-kd k-kd) = ≅-Π (kd-≅-⌞⌟-nf j-kd) (kd-≅-⌞⌟-nf k-kd)

  -- Well-formed ascriptions and contexts are equal to their normal
  -- forms.

  wf-≃-⌞⌟-nf : ∀ {n} {Γ : Ctx n} {a} →
               Γ ⊢ a wf → Γ ⊢ a ≃ ⌞ nfAsc (nfCtx Γ) a ⌟Asc wf
  wf-≃-⌞⌟-nf (wf-kd k-kd) = ≃wf-≅ (kd-≅-⌞⌟-nf k-kd)
  wf-≃-⌞⌟-nf (wf-tp a∈*)  = ≃wf-≃ (Tp∈-≃-⌞⌟-nf a∈*)

  ctx-≃-⌞⌟-nf : ∀ {n} {Γ : Ctx n} → Γ ctx → Γ ≃ ⌞ nfCtx Γ ⌟Ctx ctx
  ctx-≃-⌞⌟-nf []             = ≃-[]
  ctx-≃-⌞⌟-nf (a-wf ∷ Γ-ctx) = ≃-∷ (wf-≃-⌞⌟-nf a-wf) (ctx-≃-⌞⌟-nf Γ-ctx)


-- Some corollaries.

-- The domain and co-domain of universal types are equal to their
-- normal forms.
Tp∈-∀-≃-⌞⌟-nf : ∀ {n} {Γ : Ctx n} {k a} → Γ ⊢Tp Π k a ∈ * →
                Γ ⊢ k ≅ ⌞ nfKind (nfCtx Γ) k ⌟Kd ×
                  kd k ∷ Γ ⊢ a ≃ ⌞ nf (nfCtx (kd k ∷ Γ)) a ⌟ ∈ *
Tp∈-∀-≃-⌞⌟-nf ∀ka∈* with Tp∈-∀-inv ∀ka∈*
... | k-kd , a∈* = kd-≅-⌞⌟-nf k-kd , Tp∈-≃-⌞⌟-nf a∈*

-- The domain and co-domain of arrow types are equal to their normal
-- forms.
Tp∈-→-≃-⌞⌟-nf : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢Tp a ⇒ b ∈ * →
                Γ ⊢ a ≃ ⌞ nf (nfCtx Γ) a ⌟ ∈ * × Γ ⊢ b ≃ ⌞ nf (nfCtx Γ) b ⌟ ∈ *
Tp∈-→-≃-⌞⌟-nf a⇒b∈* with Tp∈-→-inv a⇒b∈*
... | a∈* , b∈* = Tp∈-≃-⌞⌟-nf a∈* , Tp∈-≃-⌞⌟-nf b∈*
