------------------------------------------------------------------------
-- Equivalence of declarative and canonical kinding of Fω with
-- interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Canonical.Equivalence where

open import Data.Fin using (zero)
open import Data.Fin.Substitution using (module VarSubst)
open import Data.Fin.Substitution.Typed
open import Data.Product as Prod using (_,_; proj₁; proj₂)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Syntax.WeakEquality
import FOmegaInt.Kinding.Declarative          as Declarative
import FOmegaInt.Kinding.Declarative.Validity as DeclarativeValidity
open import FOmegaInt.Kinding.Declarative.Normalization
open import FOmegaInt.Kinding.Canonical as Canonical
open import FOmegaInt.Kinding.Canonical.Validity
open import FOmegaInt.Kinding.Canonical.WeakEquality
import FOmegaInt.Kinding.Simple as SimpKind
import FOmegaInt.Kinding.Simple.EtaExpansion as SimpEtaExp
open import FOmegaInt.Kinding.Simple.Normalization

private
  module D where
    open Declarative         public
    open Declarative.Kinding public
    open TermCtx             public
    open KindedSubstitution  public
    open DeclarativeValidity public

  module C where
    open Canonical public
    open Kinding   public
    open ElimCtx   public

open Syntax
open ElimCtx
open SimpleCtx using (kd)
open ContextConversions
open ParallelNormalization
open Kinding
open KindedRenaming
open ContextNarrowing
open Declarative.Kinding hiding (_ctx; _⊢_wf; _⊢_kd; _⊢_<∷_; _⊢_<:_∈_; _⊢_≅_)


------------------------------------------------------------------------
-- Soundness of canonical (sub)kinding w.r.t. declarative (sub)kinding

mutual

  sound-wf : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → ⌞ Γ ⌟Ctx D.⊢ ⌞ a ⌟Asc wf
  sound-wf (wf-kd k-kd)  = wf-kd (sound-kd k-kd)
  sound-wf (wf-tp a⇉a⋯a) = wf-tp (D.Tp∈-⋯-* (sound-Nf⇉ a⇉a⋯a))

  sound-ctx : ∀ {n} {Γ : Ctx n} → Γ ctx → ⌞ Γ ⌟Ctx D.ctx
  sound-ctx C.[]             = D.[]
  sound-ctx (a-wf C.∷ Γ-ctx) = sound-wf a-wf D.∷ sound-ctx Γ-ctx

  sound-kd : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → ⌞ Γ ⌟Ctx D.⊢ ⌞ k ⌟Kd kd
  sound-kd (kd-⋯ a⇉a⋯a b⇉b⋯b) =
    kd-⋯ (D.Tp∈-⋯-* (sound-Nf⇉ a⇉a⋯a)) (D.Tp∈-⋯-* (sound-Nf⇉ b⇉b⋯b))
  sound-kd (kd-Π j-kd k-kd)   = kd-Π (sound-kd j-kd) (sound-kd k-kd)

  sound-Nf⇉ : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢Nf a ⇉ k → ⌞ Γ ⌟Ctx ⊢Tp ⌞ a ⌟ ∈ ⌞ k ⌟Kd
  sound-Nf⇉ (⇉-⊥-f Γ-ctx)       = ∈-s-i (∈-⊥-f (sound-ctx Γ-ctx))
  sound-Nf⇉ (⇉-⊤-f Γ-ctx)       = ∈-s-i (∈-⊤-f (sound-ctx Γ-ctx))
  sound-Nf⇉ (⇉-∀-f k-kd a⇉a⋯a)  =
    ∈-s-i (∈-∀-f (sound-kd k-kd) (D.Tp∈-⋯-* (sound-Nf⇉ a⇉a⋯a)))
  sound-Nf⇉ (⇉-→-f a⇉a⋯a b⇉b⋯b) =
    ∈-s-i (∈-→-f (D.Tp∈-⋯-* (sound-Nf⇉ a⇉a⋯a)) (D.Tp∈-⋯-* (sound-Nf⇉ b⇉b⋯b)))
  sound-Nf⇉ (⇉-Π-i j-kd a⇉k)    =
    let ⌞a⌟∈⌞k⌟ = sound-Nf⇉ a⇉k
        ⌞k⌟-kd  = D.Tp∈-valid ⌞a⌟∈⌞k⌟
    in ∈-Π-i (sound-kd j-kd) ⌞a⌟∈⌞k⌟ ⌞k⌟-kd
  sound-Nf⇉ (⇉-s-i a⇉b⋯c)       = ∈-s-i (sound-Ne∈ a⇉b⋯c)

  sound-Ne∈ : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢Ne a ∈ k → ⌞ Γ ⌟Ctx ⊢Tp ⌞ a ⌟ ∈ ⌞ k ⌟Kd
  sound-Ne∈ (∈-∙ x∈j j⇉as⇉k) = sound-Sp⇉ (sound-Var∈ x∈j) j⇉as⇉k

  sound-Sp⇉ : ∀ {n} {Γ : Ctx n} {a bs j k} →
              ⌞ Γ ⌟Ctx ⊢Tp a ∈ ⌞ j ⌟Kd → Γ ⊢ j ⇉∙ bs ⇉ k →
              ⌞ Γ ⌟Ctx ⊢Tp a ⌞∙⌟ ⌞ bs ⌟Sp ∈ ⌞ k ⌟Kd
  sound-Sp⇉ a∈⌞j⌟ ⇉-[] = a∈⌞j⌟
  sound-Sp⇉ a∈⌞Πjk⌟ (⇉-∷ b⇇j j-kd k[b]⇉bs⇉l) with D.Tp∈-valid a∈⌞Πjk⌟
  ... | (kd-Π ⌞j⌟-kd ⌞k⌟-kd) =
    let ⌞b⌟∈⌞j⌟ = sound-Nf⇇ b⇇j
    in sound-Sp⇉ (∈-⇑ (∈-Π-e a∈⌞Πjk⌟ ⌞b⌟∈⌞j⌟ ⌞k⌟-kd
                             (D.kd-[] ⌞k⌟-kd (∈-tp ⌞b⌟∈⌞j⌟)))
                      (D.≅⇒<∷ (kd-⌞⌟-[]-≅ ⌞k⌟-kd ⌞b⌟∈⌞j⌟)))
                 k[b]⇉bs⇉l

  sound-Nf⇇ : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢Nf a ⇇ k → ⌞ Γ ⌟Ctx ⊢Tp ⌞ a ⌟ ∈ ⌞ k ⌟Kd
  sound-Nf⇇ (⇇-⇑ a⇉j j<∷k) = ∈-⇑ (sound-Nf⇉ a⇉j) (sound-<∷ j<∷k)

  sound-Var∈ : ∀ {n} {Γ : Ctx n} {x k} →
               Γ ⊢Var var x ∈ k → ⌞ Γ ⌟Ctx ⊢Tp var x ∈ ⌞ k ⌟Kd
  sound-Var∈ {_} {Γ} (⇉-var {k} x Γ-ctx Γ[x]≡kd-k) =
    ∈-var x (sound-ctx Γ-ctx) (begin
        TermCtx.lookup x ⌞ Γ ⌟Ctx
      ≡⟨ ⌞⌟Ctx-Lemmas.lookup-map x ⌞_⌟Asc [] Γ (λ a → sym (⌞⌟Asc-weaken a)) ⟩
        ⌞ lookup x Γ ⌟Asc
      ≡⟨ cong ⌞_⌟Asc Γ[x]≡kd-k ⟩
        kd ⌞ k ⌟Kd
      ∎)
    where
      open ≡-Reasoning
      open Substitution using (⌞⌟Asc-weaken)
  sound-Var∈ (⇇-⇑ x∈j j<∷k k-kd) = ∈-⇑ (sound-Var∈ x∈j) (sound-<∷ j<∷k)

  sound-<∷ : ∀ {n} {Γ : Ctx n} {j k} →
             Γ ⊢ j <∷ k → ⌞ Γ ⌟Ctx D.⊢ ⌞ j ⌟Kd <∷ ⌞ k ⌟Kd
  sound-<∷ (<∷-⋯ a₂<:a₁ b₁<:b₂)          =
    <∷-⋯ (sound-<: a₂<:a₁) (sound-<: b₁<:b₂)
  sound-<∷ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) =
    <∷-Π (sound-<∷ j₂<∷j₁) (sound-<∷ k₁<∷k₂) (sound-kd Πj₁k₁-kd)

  sound-<: : ∀ {n} {Γ : Ctx n} {a b} →
             Γ ⊢ a <: b → ⌞ Γ ⌟Ctx D.⊢ ⌞ a ⌟ <: ⌞ b ⌟ ∈ *
  sound-<: (<:-trans a<:b b<:c) =
    <:-trans (sound-<: a<:b) (sound-<: b<:c)
  sound-<: (<:-⊥ a⇉a⋯a) = <:-⊥ (D.Tp∈-⋯-* (sound-Nf⇉ a⇉a⋯a))
  sound-<: (<:-⊤ a⇉a⋯a) = <:-⊤ (D.Tp∈-⋯-* (sound-Nf⇉ a⇉a⋯a))
  sound-<: (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) =
    <:-∀ (sound-<∷ k₂<∷k₁) (sound-<: a₁<:a₂)
         (D.Tp∈-⋯-* (sound-Nf⇉ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁))
  sound-<: (<:-→ a₂<:a₁ b₁<:b₂) =
    <:-→ (sound-<: a₂<:a₁) (sound-<: b₁<:b₂)
  sound-<: (<:-∙ x∈j j⇉as⇉k) =
    D.<:-⋯-* (sound-<:-∙-≃ (<:-refl (sound-Var∈ x∈j)) j⇉as⇉k)
  sound-<: (<:-⟨| a∈b⋯c) = <:-⟨| (sound-Ne∈ a∈b⋯c)
  sound-<: (<:-|⟩ a∈b⋯c) = <:-|⟩ (sound-Ne∈ a∈b⋯c)

  sound-<:⇇ : ∀ {n} {Γ : Ctx n} {a b k} →
              Γ ⊢ a <: b ⇇ k → ⌞ Γ ⌟Ctx D.⊢ ⌞ a ⌟ <: ⌞ b ⌟ ∈ ⌞ k ⌟Kd
  sound-<:⇇ (<:-⇇ (⇇-⇑ a₁⇉c₁⋯d₁ (<∷-⋯ c₁<:c d<:d₁))
                  (⇇-⇑ a₂⇉c₂⋯d₂ (<∷-⋯ c₂<:c d<:d₂)) a<:b)
    with Nf⇉-≡ a₁⇉c₁⋯d₁ | Nf⇉-≡ a₂⇉c₂⋯d₂
  sound-<:⇇ (<:-⇇ (⇇-⇑ a₁⇉a₁⋯a₁ (<∷-⋯ c<:a₁ _))
                  (⇇-⇑ a₂⇉a₂⋯a₂ (<∷-⋯ _ a₂<:d)) a<:b)
    | refl , refl | refl , refl =
      <:-⇑ (<:-⋯-i (sound-<: a<:b)) (<∷-⋯ (sound-<: c<:a₁) (sound-<: a₂<:d))
  sound-<:⇇ (<:-λ a₁<:a₂⇇k Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) =
    <:-λ (sound-<:⇇ a₁<:a₂⇇k) (sound-Nf⇇ Λj₁a₁⇇Πjk) (sound-Nf⇇ Λj₂a₂⇇Πjk)

  sound-≅ : ∀ {n} {Γ : Ctx n} {j k} →
            Γ ⊢ j ≅ k → ⌞ Γ ⌟Ctx D.⊢ ⌞ j ⌟Kd ≅ ⌞ k ⌟Kd
  sound-≅ (<∷-antisym _ _ j<∷k k<∷j) =
    <∷-antisym (sound-<∷ j<∷k) (sound-<∷ k<∷j)

  sound-≃ : ∀ {n} {Γ : Ctx n} {a b k} →
            Γ ⊢ a ≃ b ⇇ k → ⌞ Γ ⌟Ctx D.⊢ ⌞ a ⌟ ≃ ⌞ b ⌟ ∈ ⌞ k ⌟Kd
  sound-≃ (<:-antisym k-kd a<:b⇇k b<:a⇇k) =
    <:-antisym (sound-<:⇇ a<:b⇇k) (sound-<:⇇ b<:a⇇k)

  sound-<:-∙-≃ : ∀ {n} {Γ : Ctx n} {a b as bs j k} →
                 ⌞ Γ ⌟Ctx D.⊢ a <: b ∈ ⌞ j ⌟Kd → Γ ⊢ j ⇉∙ as ≃ bs ⇉ k →
                 ⌞ Γ ⌟Ctx D.⊢ a ⌞∙⌟ ⌞ as ⌟Sp <: b ⌞∙⌟ ⌞ bs ⌟Sp ∈ ⌞ k ⌟Kd
  sound-<:-∙-≃ a<:b∈⌞j⌟ ≃-[] = a<:b∈⌞j⌟
  sound-<:-∙-≃ a<:b∈⌞Πjk⌟ (≃-∷ c≃d⇇j k[c]⇉cs≃ds⇉l) with D.<:-valid-kd a<:b∈⌞Πjk⌟
  ... | (kd-Π ⌞j⌟-kd ⌞k⌟-kd) =
    let ⌞c⌟≃⌞d⌟∈⌞j⌟ = sound-≃ c≃d⇇j
        ⌞c⌟∈⌞j⌟ , _ = D.≃-valid ⌞c⌟≃⌞d⌟∈⌞j⌟
    in sound-<:-∙-≃ (<:-⇑ (<:-· a<:b∈⌞Πjk⌟ ⌞c⌟≃⌞d⌟∈⌞j⌟ ⌞c⌟∈⌞j⌟ ⌞k⌟-kd
                                (D.kd-[] ⌞k⌟-kd (∈-tp ⌞c⌟∈⌞j⌟)))
                          (D.≅⇒<∷ (kd-⌞⌟-[]-≅ ⌞k⌟-kd ⌞c⌟∈⌞j⌟)))
                    k[c]⇉cs≃ds⇉l


------------------------------------------------------------------------
-- Completeness of canonical (sub)kinding w.r.t. declarative
-- (sub)kinding

open Substitution hiding (subst)

module TrackSimpleKindsCanonicalEtaExp where
  open RenamingCommutes
  open SimpHSubstLemmas
  private
    module V   = VarSubst
    module TK  = TrackSimpleKindsEtaExp
    module TKE = SimpEtaExp.TrackSimpleKindsKindedEtaExp

  -- Hereditary substitutions of a variable by its well-kinded
  -- η-expansion in well-formed kinds vanish.
  --
  -- NOTE. We will strengthen this lemma below, once we have proven
  -- that η-expansion preserves canonical kinding.
  kd-[]-η-var : ∀ {k n} {Γ : Ctx n} {j l} →
                Γ ⊢ j kd → kd j ∷ Γ ⊢ l kd →
                let j′  = weakenKind′ j in (hyp : ⌊ j′ ⌋≡ k) →
                let η-z = TK.η-exp j′ hyp (var∙ zero)
                in kd j ∷ Γ ⊢Nf η-z ⇇ j′ →
                   kd j ∷ Γ ⊢ (l Kind′/Var V.wk V.↑) Kind[ η-z ∈ ⌊ j′ ⌋ ] ≅ l
  kd-[]-η-var j-kd l-kd hyp η-z⇇j =
    let open TypedVarSubst    typedVarSubst
        open SimpKind.Kinding using (_⊢_kds)
        open SimpleCtx        using (kd)

        j-wf     = wf-kd j-kd
        j-kd′    = kd-weaken j-wf j-kd
        ⌊j⌋≡k    = trans (sym (⌊⌋-Kind′/Var _)) (⌊⌋≡⇒⌊⌋-≡ hyp)
        η-z      = TK.η-exp _ hyp (var∙ zero)
        j-kds′   = subst (λ k → kd k ∷ _ ⊢ _ kds) ⌊j⌋≡k (kd-kds j-kd′)
        l-kds    = subst (λ k → kd k ∷ _ ⊢ _ kds) ⌊j⌋≡k (kd-kds l-kd)
        l[z]≋l   = TKE.kds-[]-η-var [] hyp j-kds′ l-kds
        wk↑∈j∷Γ  = ∈-↑′ j-kd′ (∈-wk j-wf)
        l[z]-kd  = kd-[] (kd-/Var l-kd wk↑∈j∷Γ) η-z⇇j
    in ≋-≅ l[z]-kd l-kd (subst (λ l → _ Kind[ η-z ∈ l ] ≋ _)
                               (sym (⌊⌋≡⇒⌊⌋-≡ hyp)) l[z]≋l)

  -- NOTE. The definition of the function η-exp-Ne∈ below is
  -- structurally recursive in the *simple* kind parameter k, but
  -- *not* in the kind j because we need to weaken the domain j₁ of
  -- the dependent kind (j = Π j₁ j₂) in the arrow case.  The
  -- additional hypothesis ⌊ j ⌋≡ k ensures that k is indeed the
  -- simplification of the kind j.

  -- η-expansion preserves canonical kinding of neutral types.
  η-exp-Ne∈ : ∀ {n} {Γ : Ctx n} {a j k l} (hyp : ⌊ j ⌋≡ k) →
              Γ ⊢ j kd → Γ ⊢Ne a ∈ l → Γ ⊢ l <∷ j → Γ ⊢Nf TK.η-exp j hyp a ⇇ j
  η-exp-Ne∈ is-★ b₂⋯c₂-kd a∈b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂) =
    Nf⇇-⇑ (Nf⇇-ne a∈b₁⋯c₁) (<∷-⋯ b₂<:b₁ c₁<:c₂)
  η-exp-Ne∈ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (kd-Π j₁-kd j₂-kd)
            (∈-∙ {x} {_} {_} {as} x∈l l⇉as∈Πl₁l₂)
            (<∷-Π j₁<∷l₁ l₂<∷j₂ (kd-Π l₁-kd l₂-kd)) =
    Nf⇇-Π-i j₁-kd (η-exp-Ne∈ ⌊j₂⌋≡k₂ j₂-kd x∙as·z∈l₂[z] l₂[z]<∷j₂)
    where
      open TypedVarSubst    typedVarSubst

      j₁-wf     = wf-kd j₁-kd
      j₁∷Γ-ctx  = j₁-wf C.∷ Var∈-ctx x∈l
      j₁-kd′    = kd-weaken j₁-wf j₁-kd
      l₁-kd′    = kd-weaken j₁-wf l₁-kd
      ⌊j₁′⌋≡k₁  = ⌊⌋≡-weaken ⌊j₁⌋≡k₁
      η-z       = TK.η-exp _ ⌊j₁′⌋≡k₁ (var∙ zero)
      z⇇j₁      = η-exp-Ne∈ ⌊j₁′⌋≡k₁ j₁-kd′
                            (∈-∙ (⇉-var zero j₁∷Γ-ctx refl) ⇉-[])
                            (<∷-refl j₁-kd′)
      z⇇l₁      = Nf⇇-⇑ z⇇j₁ (<∷-weaken j₁-wf j₁<∷l₁)
      wk↑∈j₁∷Γ  = ∈-↑′ j₁-kd′ (∈-wk j₁-wf)
      j₂[z]<∷j₂ = ≅⇒<∷ (kd-[]-η-var j₁-kd j₂-kd ⌊j₁′⌋≡k₁ z⇇j₁)
      l₂[z]<∷j₂[z] = <∷-[≃] (<∷-/Var l₂<∷j₂ wk↑∈j₁∷Γ) (≃-reflNf⇇ z⇇j₁ j₁-kd′)
      l₂[z]<∷j₂ = subst (λ l → _ ⊢ _ Kind[ η-z ∈ l ] <∷ _)
                        (<∷-⌊⌋ (<∷-weaken j₁-wf j₁<∷l₁))
                        (<∷-trans l₂[z]<∷j₂[z] j₂[z]<∷j₂)
      x∙as·z∈l₂[z] = (∈-∙ (Var∈-weaken j₁-wf x∈l)
                          (⇉-∷ʳ (Sp⇉-weaken j₁-wf l⇉as∈Πl₁l₂) z⇇l₁ l₁-kd′))

private module TK  = TrackSimpleKindsCanonicalEtaExp

-- η-expansion preserves canonical kinding of neutral types.

η-exp-Ne∈ : ∀ {n} {Γ : Ctx n} {a k} →
            Γ ⊢ k kd → Γ ⊢Ne a ∈ k → Γ ⊢Nf η-exp k a ⇇ k
η-exp-Ne∈ k-kd a∈k = TK.η-exp-Ne∈ (⌊⌋-⌊⌋≡ _) k-kd a∈k (<∷-refl k-kd)

η-exp-Var∈ : ∀ {n} {Γ : Ctx n} {x k} → Γ ⊢ k kd → Γ ⊢Var var x ∈ k →
             Γ ⊢Nf η-exp k (var∙ x) ⇇ k
η-exp-Var∈ k-kd x∈k = η-exp-Ne∈ k-kd (∈-∙ x∈k ⇉-[])

-- Hereditary substitutions in well-formed kinds of a variable by its
-- η-expansion vanish.
kd-[]-η-var : ∀ {n} {Γ : Ctx n} {j l} → Γ ⊢ j kd → kd j ∷ Γ ⊢ l kd →
              let j′  = weakenKind′ j
                  l′  = l Kind′/Var VarSubst.wk VarSubst.↑
              in kd j ∷ Γ ⊢ l′ Kind[ η-exp j′ (var∙ zero) ∈ ⌊ j′ ⌋ ] ≅ l
kd-[]-η-var j-kd l-kd =
  let j-kd′ = kd-weaken (wf-kd j-kd) j-kd
  in TK.kd-[]-η-var j-kd l-kd (⌊⌋-⌊⌋≡ _)
                    (η-exp-Var∈ j-kd′ (⇉-var zero (kd-ctx j-kd′) refl))

open RenamingCommutesNorm

-- Completeness of canonical (sub)kinding w.r.t. declarative
-- (sub)kinding

mutual

  complete-wf : ∀ {n} {Γ : D.Ctx n} {a} → Γ D.⊢ a wf →
                nfCtx Γ ⊢ nfAsc (nfCtx Γ) a wf
  complete-wf (wf-kd k-kd) = wf-kd (complete-kd k-kd)
  complete-wf (wf-tp a∈*)  = wf-tp (Nf⇇-s-i (complete-Tp∈ a∈*))

  complete-ctx : ∀ {n} {Γ : D.Ctx n} → Γ D.ctx → nfCtx Γ ctx
  complete-ctx D.[]             = C.[]
  complete-ctx (a-wf D.∷ Γ-ctx) = complete-wf a-wf C.∷ complete-ctx Γ-ctx

  complete-kd : ∀ {n} {Γ : D.Ctx n} {k} → Γ D.⊢ k kd →
                nfCtx Γ ⊢ nfKind (nfCtx Γ) k kd
  complete-kd (kd-⋯ a∈* b∈*)   =
    kd-⋯ (Nf⇇-s-i (complete-Tp∈ a∈*)) (Nf⇇-s-i (complete-Tp∈ b∈*))
  complete-kd (kd-Π j-kd k-kd) = kd-Π (complete-kd j-kd) (complete-kd k-kd)

  complete-Tp∈ : ∀ {n} {Γ : D.Ctx n} {a k} → Γ D.⊢Tp a ∈ k →
                 nfCtx Γ ⊢Nf nf (nfCtx Γ) a ⇇ nfKind (nfCtx Γ) k
  complete-Tp∈ {_} {Γ} (∈-var x Γ-ctx Γ[x]≡kd-k)
    with C.lookup x (nfCtx Γ) | nfCtx-lookup-kd x Γ Γ[x]≡kd-k
  complete-Tp∈ {_} {Γ} (∈-var x Γ-ctx Γ[x]≡kd-k) | kd ._ | refl =
    η-exp-Var∈ (WfCtxOps.lookup-kd x nf-Γ-ctx nf-Γ[x]≡kd-nf-k)
               (⇉-var x nf-Γ-ctx nf-Γ[x]≡kd-nf-k)
    where
      nf-Γ-ctx        = complete-ctx Γ-ctx
      nf-Γ[x]≡kd-nf-k = nfCtx-lookup-kd x Γ Γ[x]≡kd-k
  complete-Tp∈ (∈-⊥-f Γ-ctx) = Nf⇉-⋯-* (⇉-⊥-f (complete-ctx Γ-ctx))
  complete-Tp∈ (∈-⊤-f Γ-ctx) = Nf⇉-⋯-* (⇉-⊤-f (complete-ctx Γ-ctx))
  complete-Tp∈ (∈-∀-f k-kd a∈*) = Nf⇇-∀-f (complete-kd k-kd) (complete-Tp∈ a∈*)
  complete-Tp∈ (∈-→-f a∈* b∈*)  = Nf⇇-→-f (complete-Tp∈ a∈*) (complete-Tp∈ b∈*)
  complete-Tp∈ (∈-Π-i j-kd a∈k k-kd) =
    Nf⇇-Π-i (complete-kd j-kd) (complete-Tp∈ a∈k)
  complete-Tp∈ (∈-Π-e {a} {b} a∈Πjk b∈j k-kd k[a]-kd) =
    Nf⇇-⇑ (Nf⇇-Π-e′ (complete-Tp∈ a∈Πjk) (complete-Tp∈ b∈j))
          (≅⇒<∷ (≅-nfKind-[] k-kd b∈j k[a]-kd))
  complete-Tp∈ (∈-s-i a∈b⋯c) =
    let nf-a⇉a⋯a = Nf⇇-s-i (complete-Tp∈ a∈b⋯c)
    in ⇇-⇑ nf-a⇉a⋯a (<∷-⋯ (<:-reflNf⇉ nf-a⇉a⋯a) (<:-reflNf⇉ nf-a⇉a⋯a))
  complete-Tp∈ (∈-⇑ a∈j j<∷k) = Nf⇇-⇑ (complete-Tp∈ a∈j) (complete-<∷ j<∷k)

  complete-<∷ : ∀ {n} {Γ : D.Ctx n} {j k} → Γ D.⊢ j <∷ k →
                nfCtx Γ ⊢ nfKind (nfCtx Γ) j <∷ nfKind (nfCtx Γ) k
  complete-<∷ (<∷-⋯ a₂<:a₁ b₁<:b₂) =
    <∷-⋯ (complete-<:-⋯ a₂<:a₁) (complete-<:-⋯ b₁<:b₂)
  complete-<∷ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) with complete-kd Πj₁k₁-kd
  ... | kd-Π nf-j₁-kd nf-k₁-kd =
    let nf-j₂<∷j₁  = complete-<∷ j₂<∷j₁
        nf-k₁′<∷k₂ = complete-<∷ k₁<∷k₂
        ⌊nf-j₁∷Γ⌋≡⌊nf-j₂∷Γ⌋ = cong (λ k → kd k ∷ _) (sym (<∷-⌊⌋ nf-j₂<∷j₁))
        nf-k₁≋k₁′  = ≋-nfKind ⌊nf-j₁∷Γ⌋≡⌊nf-j₂∷Γ⌋ _
        nf-j₂-kd   = proj₁ (<∷-valid nf-j₂<∷j₁)
        nf-k₁′-kd  = proj₁ (<∷-valid nf-k₁′<∷k₂)
        nf-k₁<∷k₁′ = ≋-<∷ (⇓-kd [] nf-j₂-kd nf-j₂<∷j₁ nf-k₁-kd)
                          nf-k₁′-kd nf-k₁≋k₁′
        nf-k₁<∷k₂ = <∷-trans nf-k₁<∷k₁′ nf-k₁′<∷k₂
    in <∷-Π nf-j₂<∷j₁ nf-k₁<∷k₂ (kd-Π nf-j₁-kd nf-k₁-kd)

  complete-<:-⋯ : ∀ {n} {Γ : D.Ctx n} {a b c d} → Γ D.⊢ a <: b ∈ c ⋯ d →
                  nfCtx Γ ⊢ nf (nfCtx Γ) a <: nf (nfCtx Γ) b
  complete-<:-⋯ a<:b∈c⋯d with complete-<: a<:b∈c⋯d
  complete-<:-⋯ a<:b∈c⋯d | <:-⇇ _ _ a<:b = a<:b

  complete-<: : ∀ {n} {Γ : D.Ctx n} {a b k} → Γ D.⊢ a <: b ∈ k →
                nfCtx Γ ⊢ nf (nfCtx Γ) a <: nf (nfCtx Γ) b ⇇ nfKind (nfCtx Γ) k
  complete-<: (<:-refl a∈k) =
    let nf-a∈k  = complete-Tp∈ a∈k
    in <:⇇-reflNf⇇ nf-a∈k (Nf⇇-valid nf-a∈k)
  complete-<: (<:-trans a<:b b<:c) =
    <:⇇-trans (complete-<: a<:b) (complete-<: b<:c)
  complete-<: (<:-β₁ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    ≃⇒<: (≃-β-nf a∈k b∈j k-kd a[b]∈k[b] k[b]-kd)
  complete-<: (<:-β₂ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    ≃⇒<: (≃-sym (≃-β-nf a∈k b∈j k-kd a[b]∈k[b] k[b]-kd))
  complete-<: (<:-η₁ a∈Πjk) = ≃⇒<: (≃-η-nf a∈Πjk)
  complete-<: (<:-η₂ a∈Πjk) = ≃⇒<: (≃-sym (≃-η-nf a∈Πjk))
  complete-<: (<:-⊥ a∈b⋯c) = <:-⋯-* (<:-⊥ (Nf⇇-s-i (complete-Tp∈ a∈b⋯c)))
  complete-<: (<:-⊤ a∈b⋯c) = <:-⋯-* (<:-⊤ (Nf⇇-s-i (complete-Tp∈ a∈b⋯c)))
  complete-<: (<:-∀ {a₁ = a₁} k₂<∷k₁ a₁<:a₂ Πk₁a₁∈*) with complete-Tp∈ Πk₁a₁∈*
  ... | (⇇-⇑ (⇉-∀-f nf-k₁-kd nf-a₁⇉a₁⋯a₁) _) =
    let nf-k₂<∷k₁    = complete-<∷ k₂<∷k₁
        nf-a₁′<:a₂   = complete-<:-⋯ a₁<:a₂
        ⌊nf-k₁∷Γ⌋≡⌊nf-k₂∷Γ⌋ = cong (λ k → kd k ∷ _) (sym (<∷-⌊⌋ nf-k₂<∷k₁))
        nf-a₁≈a₁′    = ≈-nf ⌊nf-k₁∷Γ⌋≡⌊nf-k₂∷Γ⌋ a₁
        nf-k₂-kd     = proj₁ (<∷-valid nf-k₂<∷k₁)
        nf-a₁⇉a₁⋯a₁′ = proj₁ (<:-valid nf-a₁′<:a₂)
        nf-a₁<:a₁′   = ≈-<: (⇓-Nf⇉ [] nf-k₂-kd nf-k₂<∷k₁ nf-a₁⇉a₁⋯a₁)
                            nf-a₁⇉a₁⋯a₁′ nf-a₁≈a₁′
        nf-a₁<:a₂ = <:-trans nf-a₁<:a₁′ nf-a₁′<:a₂
    in <:-⋯-* (<:-∀ nf-k₂<∷k₁ nf-a₁<:a₂ (⇉-∀-f nf-k₁-kd nf-a₁⇉a₁⋯a₁))
  ... | (⇇-⇑ (⇉-s-i ()) _)
  complete-<: (<:-→ a₂<:a₁ b₁<:b₂) =
    <:-⋯-* (<:-→ (complete-<:-⋯ a₂<:a₁) (complete-<:-⋯ b₁<:b₂))
  complete-<: (<:-λ {a₁ = a₁} {a₂} a₁<:a₂∈k Λj₁a₁∈Πjk Λj₂a₂∈Πjk)
    with complete-Tp∈ Λj₁a₁∈Πjk | complete-Tp∈ Λj₂a₂∈Πjk
  ... | ⇇-⇑ (⇉-Π-i nf-j₁-kd nf-a₁⇉k₁) (<∷-Π nf-j<∷j₁ nf-k₁<∷k Πj₁k₁-kd)
      | ⇇-⇑ (⇉-Π-i nf-j₂-kd nf-a₂⇉k₂) (<∷-Π nf-j<∷j₂ nf-k₂<∷k Πj₂k₂-kd) =
    let nf-a₁′<:a₂′⇇k = complete-<: a₁<:a₂∈k
        nf-a₁′⇇k , nf-a₂′⇇k = <:⇇-valid nf-a₁′<:a₂′⇇k
        j-kd          = proj₁ (<∷-valid nf-j<∷j₁)
        k-kd          = proj₂ (<∷-valid nf-k₁<∷k)
        ⌊nf-j₁∷Γ⌋≡⌊nf-j∷Γ⌋  = cong (λ k → kd k ∷ _) (sym (<∷-⌊⌋ nf-j<∷j₁))
        ⌊nf-j∷Γ⌋≡⌊nf-j₂∷Γ⌋  = cong (λ k → kd k ∷ _) (<∷-⌊⌋ nf-j<∷j₂)
        nf-a₁≈a₁′     = ≈-nf ⌊nf-j₁∷Γ⌋≡⌊nf-j∷Γ⌋ a₁
        nf-a₂′≈a₂     = ≈-nf ⌊nf-j∷Γ⌋≡⌊nf-j₂∷Γ⌋ a₂
        nf-a₁<:a₁′⇇k  = ≈-<:⇇ k-kd
                              (⇇-⇑ (⇓-Nf⇉ [] j-kd nf-j<∷j₁ nf-a₁⇉k₁) nf-k₁<∷k)
                              nf-a₁′⇇k nf-a₁≈a₁′
        nf-a₂′<:a₂⇇k  = ≈-<:⇇ k-kd nf-a₂′⇇k
                              (⇇-⇑ (⇓-Nf⇉ [] j-kd nf-j<∷j₂ nf-a₂⇉k₂) nf-k₂<∷k)
                              nf-a₂′≈a₂
        nf-a₁<:a₂⇇k   = <:⇇-trans (<:⇇-trans nf-a₁<:a₁′⇇k nf-a₁′<:a₂′⇇k)
                                  nf-a₂′<:a₂⇇k
    in <:-λ nf-a₁<:a₂⇇k
            (⇇-⇑ (⇉-Π-i nf-j₁-kd nf-a₁⇉k₁) (<∷-Π nf-j<∷j₁ nf-k₁<∷k Πj₁k₁-kd))
            (⇇-⇑ (⇉-Π-i nf-j₂-kd nf-a₂⇉k₂) (<∷-Π nf-j<∷j₂ nf-k₂<∷k Πj₂k₂-kd))
  ... | ⇇-⇑ (⇉-Π-i _ _) _ | ⇇-⇑ (⇉-s-i ()) _
  ... | ⇇-⇑ (⇉-s-i ()) _  | _
  complete-<: (<:-· {a₁} {a₂} {b₁} {b₂} a₁<:a₂∈Πjk b₁≃b₂∈j b₁∈j k-kd k[b₁]-kd) =
    let nf-a₁<:a₂⇇Πjk         = complete-<: a₁<:a₂∈Πjk
        nf-a₁⇇Πjk , nf-a₂⇇Πjk = <:⇇-valid nf-a₁<:a₂⇇Πjk
    in <:⇇-⇑ (<:-↓⌜·⌝ nf-a₁<:a₂⇇Πjk (complete-≃ b₁≃b₂∈j))
             (≅⇒<∷ (≅-nfKind-[] k-kd b₁∈j k[b₁]-kd)) (complete-kd k[b₁]-kd)
  complete-<: (<:-⟨| a∈b⋯c) = <:-⋯-* (<:-⟨|-Nf⇇ (complete-Tp∈ a∈b⋯c))
  complete-<: (<:-|⟩ a∈b⋯c) = <:-⋯-* (<:-|⟩-Nf⇇ (complete-Tp∈ a∈b⋯c))
  complete-<: (<:-⋯-i a<:b) = <:⇇-⋯-i (complete-<: a<:b)
  complete-<: (<:-⇑ a<:b∈j j<∷k) =
    let nf-j<∷k = complete-<∷ j<∷k
    in <:⇇-⇑ (complete-<: a<:b∈j) nf-j<∷k (proj₂ (<∷-valid nf-j<∷k))

  complete-≅ : ∀ {n} {Γ : D.Ctx n} {j k} → Γ D.⊢ j ≅ k →
               nfCtx Γ ⊢ nfKind (nfCtx Γ) j ≅ nfKind (nfCtx Γ) k
  complete-≅ (<∷-antisym j<∷k k<∷j) =
    let nf-j<∷k           = complete-<∷ j<∷k
        nf-j-kd , nf-k-kd = <∷-valid nf-j<∷k
    in <∷-antisym nf-j-kd nf-k-kd nf-j<∷k (complete-<∷ k<∷j)

  complete-≃ : ∀ {n} {Γ : D.Ctx n} {a b k} → Γ D.⊢ a ≃ b ∈ k →
               nfCtx Γ ⊢ nf (nfCtx Γ) a ≃ nf (nfCtx Γ) b ⇇ nfKind (nfCtx Γ) k
  complete-≃ (<:-antisym a<:b∈k b<:a∈k) =
    let nf-a<:b⇇k = complete-<: a<:b∈k
    in <:-antisym (<:⇇-valid-kd nf-a<:b⇇k) nf-a<:b⇇k (complete-<: b<:a∈k)

  -- η-expansion of normal forms is admissible in canonical kinding.
  ≃-η-nf : ∀ {n} {Γ : D.Ctx n} {a j k} → Γ ⊢Tp a ∈ Π j k →
           nfCtx Γ ⊢ nf (nfCtx Γ) (Λ j (weaken a · var zero))  ≃
             nf (nfCtx Γ) a ⇇ nfKind (nfCtx Γ) (Π j k)
  ≃-η-nf                 a∈Πjk with complete-Tp∈ a∈Πjk
  ≃-η-nf {_} {Γ} {a} {j} a∈Πjk | nf-a⇇Πjk with Nf⇇-valid nf-a⇇Πjk
  ... | (kd-Π nf-j-kd nf-k-kd) =
    let nf-Γ      = nfCtx Γ
        nf-j      = nfKind nf-Γ j
        nf-j-wf   = wf-kd nf-j-kd
        nf-j-kd′  = kd-weaken nf-j-wf nf-j-kd
        nf-a⇇Πjk′ = subst (kd nf-j ∷ nf-Γ ⊢Nf_⇇ _) (nf-weaken (kd nf-j) a)
                          (Nf⇇-weaken nf-j-wf nf-a⇇Πjk)
        η-z⇇j′    = η-exp-Var∈ nf-j-kd′ (⇉-var zero (kd-ctx nf-j-kd′) refl)
        nf-a·z⇇k[z] = Nf⇇-Π-e′ nf-a⇇Πjk′ η-z⇇j′
        nf-a·z⇇k    = Nf⇇-⇑ nf-a·z⇇k[z] (≅⇒<∷ (kd-[]-η-var nf-j-kd nf-k-kd))
    in ≈-≃ (kd-Π nf-j-kd nf-k-kd) (Nf⇇-Π-i nf-j-kd nf-a·z⇇k) nf-a⇇Πjk
           (≈-η-nf a∈Πjk)

  -- Substitution in well-formed kinds commutes with normalization.
  ≅-nfKind-[] : ∀ {n} {Γ : D.Ctx n} {a j k} →
                kd k ∷ Γ D.⊢ j kd → Γ ⊢Tp a ∈ k → Γ D.⊢ j Kind[ a ] kd →
                nfCtx Γ ⊢ (nfKind (nfCtx (kd k ∷ Γ)) j) Kind[
                  nf (nfCtx Γ) a ∈ ⌊ nfKind (nfCtx Γ) k ⌋ ]  ≅
                    nfKind (nfCtx Γ) (j Kind[ a ])
  ≅-nfKind-[] {_} {Γ} {a} {j} {k} j-kd a∈k j[a]-kd =
    let nf-Γ         = nfCtx Γ
        nf-k         = nfKind nf-Γ k
        nf-a         = nf nf-Γ a
        nf-k∷Γ       = kd nf-k ∷ nf-Γ
        nf-j         = nfKind (nf-k∷Γ) j
        ⌊k⌋≡⌊nf-k⌋   = sym (⌊⌋-nf {_} {nf-Γ} k)
        nf-j-kd      = complete-kd j-kd
        nf-a⇇k       = complete-Tp∈ a∈k
        nf-j[a]-kd   = complete-kd j[a]-kd
        nf-j[a∈⌊k⌋]-kd   = kd-[] nf-j-kd nf-a⇇k
        nf-j[a∈⌊k⌋]≋j[a] = subst (λ l → nf-j Kind[ nf-a ∈ l ] ≋ _)
                                 ⌊k⌋≡⌊nf-k⌋ (≋-sym (nfKind-[] [] j-kd a∈k))
    in ≋-≅ nf-j[a∈⌊k⌋]-kd nf-j[a]-kd nf-j[a∈⌊k⌋]≋j[a]

  -- β-reduction of normal forms is admissible in canonical kinding.
  ≃-β-nf : ∀ {n} {Γ : D.Ctx n} {a b j k} →
           kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j → kd j ∷ Γ D.⊢ k kd →
           Γ ⊢Tp a [ b ] ∈ k Kind[ b ] → Γ D.⊢ k Kind[ b ] kd →
           nfCtx Γ ⊢ nf (nfCtx Γ) ((Λ j a) · b)  ≃
             nf (nfCtx Γ) (a [ b ]) ⇇ nfKind (nfCtx Γ) (k Kind[ b ])
  ≃-β-nf {_} {Γ} {a} {b} {j} {k} a∈k b∈j k-kd a[b]∈k[b] k[b]-kd =
    let nf-Γ         = nfCtx Γ
        nf-j         = nfKind nf-Γ j
        nf-b         = nf nf-Γ b
        nf-j∷Γ       = kd nf-j ∷ nf-Γ
        nf-a         = nf (nf-j∷Γ) a
        ⌊j⌋≡⌊nf-j⌋   = sym (⌊⌋-nf {_} {nf-Γ} j)
        nf-a⇇k       = complete-Tp∈ a∈k
        nf-b⇇j       = complete-Tp∈ b∈j
        nf-a[b]⇇k[b] = complete-Tp∈ a[b]∈k[b]
        nf-k[b]-kd   = complete-kd k[b]-kd
        nf-a[b∈⌊j⌋]⇇k[b∈⌊j⌋] = Nf⇇-[] nf-a⇇k nf-b⇇j
        nf-k[b∈⌊j⌋]<∷k[b]    = ≅⇒<∷ (≅-nfKind-[] k-kd b∈j k[b]-kd)
        nf-a[b∈⌊j⌋]⇇k[b]     = Nf⇇-⇑ nf-a[b∈⌊j⌋]⇇k[b∈⌊j⌋] nf-k[b∈⌊j⌋]<∷k[b]
        nf-a[b∈⌊j⌋]≈a[b]     = subst (λ l → nf-a [ nf-b ∈ l ] ≈ _) ⌊j⌋≡⌊nf-j⌋
                                     (≈-sym (nf-[] [] a∈k b∈j))
    in ≈-≃ nf-k[b]-kd nf-a[b∈⌊j⌋]⇇k[b] nf-a[b]⇇k[b] nf-a[b∈⌊j⌋]≈a[b]
