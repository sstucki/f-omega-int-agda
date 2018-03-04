------------------------------------------------------------------------
-- Normalization of raw terms in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

module FOmegaInt.Syntax.Normalization where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas using (module VarLemmas)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.List.All using (All; []; _∷_)
open import Data.Star using (ε)
open import Data.Unit using (tt)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProps
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])

open import FOmegaInt.Reduction.Full
open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution

open Syntax

----------------------------------------------------------------------
-- Untyped η-expansion of neutral terms.

-- TODO: explain this

infix 4 ⌊_⌋≡_

-- Kind simplification as a relation.
data ⌊_⌋≡_ {T n} : Kind T n → SKind → Set where
  is-★ : ∀ {a b}                                   → ⌊ a ⋯ b ⌋≡ ★
  is-⇒ : ∀ {j₁ j₂ k₁ k₂} → ⌊ j₁ ⌋≡ k₁ → ⌊ j₂ ⌋≡ k₂ → ⌊ Π j₁ j₂ ⌋≡ k₁ ⇒ k₂

-- Kind simplification as a relation agrees with kind simplification
-- as a function.

⌊⌋-⌊⌋≡ : ∀ {T n} (k : Kind T n) → ⌊ k ⌋≡ ⌊ k ⌋
⌊⌋-⌊⌋≡ (a ⋯ b) = is-★
⌊⌋-⌊⌋≡ (Π j k) = is-⇒ (⌊⌋-⌊⌋≡ j) (⌊⌋-⌊⌋≡ k)

⌊⌋≡⇒⌊⌋-≡ : ∀ {T n k} {j : Kind T n} → ⌊ j ⌋≡ k → ⌊ j ⌋ ≡ k
⌊⌋≡⇒⌊⌋-≡ is-★                   = refl
⌊⌋≡⇒⌊⌋-≡ (is-⇒ ⌊j₁⌋=k₁ ⌊j₂⌋=k₂) =
  cong₂ _⇒_ (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋=k₁) (⌊⌋≡⇒⌊⌋-≡ ⌊j₂⌋=k₂)

⌊⌋≡-trans : ∀ {T n m k} {j : Kind T n} {l : Kind T m} →
            ⌊ j ⌋ ≡ ⌊ l ⌋ → ⌊ l ⌋≡ k → ⌊ j ⌋≡ k
⌊⌋≡-trans ⌊j⌋≡⌊l⌋ ⌊l⌋≡k rewrite (sym (⌊⌋≡⇒⌊⌋-≡ ⌊l⌋≡k)) =
  subst (⌊ _ ⌋≡_) ⌊j⌋≡⌊l⌋ (⌊⌋-⌊⌋≡ _)

-- Kind simplification is proof-irrelevant.
⌊⌋≡-pirr : ∀ {T n k} {j : Kind T n} → (p₁ p₂ : ⌊ j ⌋≡ k) → p₁ ≡ p₂
⌊⌋≡-pirr is-★ is-★                     = refl
⌊⌋≡-pirr (is-⇒ p₁₁ p₁₂) (is-⇒ p₂₁ p₂₂) =
  cong₂ is-⇒ (⌊⌋≡-pirr p₁₁ p₂₁) (⌊⌋≡-pirr p₁₂ p₂₂)

-- A type of abstract lemma stating that kind simplification as a
-- relation commutes with substitution.
KindSimpAppLemma : ∀ {T T′} (app : Application (Kind T) T′) → Set
KindSimpAppLemma {_} {T′} app =
  ∀ {m n j k} {σ : Sub T′ m n} → ⌊ j ⌋≡ k → ⌊ j / σ ⌋≡ k
  where open Application app

-- Lemmas relating kind simplification to operations on T-kinds.
record KindSimpLemmas (T : ℕ → Set) : Set₁ where

  field lemmas : TermLikeLemmas (Kind T) Term
  open TermLikeLemmas lemmas
    using (termApplication; varApplication; weaken; weaken⋆)

  field
    ⌊⌋≡-/    : KindSimpAppLemma termApplication
    ⌊⌋≡-/Var : KindSimpAppLemma varApplication

  -- Kind simplification as a relation commutes with weakening.

  ⌊⌋≡-weaken : ∀ {n k} {j : Kind T n} → ⌊ j ⌋≡ k → ⌊ weaken j ⌋≡ k
  ⌊⌋≡-weaken ⌊j⌋≡k = ⌊⌋≡-/Var ⌊j⌋≡k

  ⌊⌋≡-weaken⋆ : ∀ m {n k} {j : Kind T n} → ⌊ j ⌋≡ k → ⌊ weaken⋆ m j ⌋≡ k
  ⌊⌋≡-weaken⋆ zero    ⌊j⌋≡k = ⌊j⌋≡k
  ⌊⌋≡-weaken⋆ (suc m) ⌊j⌋≡k = ⌊⌋≡-weaken (⌊⌋≡-weaken⋆ m ⌊j⌋≡k)

module KindSimpSubstApp {T} {l : Lift T Term} where
  open SubstApp l

  -- Kind simplification as a relation commutes with substitution.

  ⌊⌋≡-Kind/ : ∀ {m n j k} {σ : Sub T m n} → ⌊ j ⌋≡ k → ⌊ j Kind/ σ ⌋≡ k
  ⌊⌋≡-Kind/ is-★                   = is-★
  ⌊⌋≡-Kind/ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) =
    is-⇒ (⌊⌋≡-Kind/ ⌊j₁⌋≡k₁) (⌊⌋≡-Kind/ ⌊j₂⌋≡k₂)

  ⌊⌋≡-Kind′/ : ∀ {m n j k} {σ : Sub T m n} → ⌊ j ⌋≡ k → ⌊ j Kind′/ σ ⌋≡ k
  ⌊⌋≡-Kind′/ is-★                   = is-★
  ⌊⌋≡-Kind′/ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) =
    is-⇒ (⌊⌋≡-Kind′/ ⌊j₁⌋≡k₁) (⌊⌋≡-Kind′/ ⌊j₂⌋≡k₂)

simpLemmasKind : KindSimpLemmas Term
simpLemmasKind = record
  { lemmas   = termLikeLemmasKind
  ; ⌊⌋≡-/    = KindSimpSubstApp.⌊⌋≡-Kind/
  ; ⌊⌋≡-/Var = KindSimpSubstApp.⌊⌋≡-Kind/
  }
  where open Substitution

simpLemmasKind′ : KindSimpLemmas Elim
simpLemmasKind′ = record
  { lemmas   = termLikeLemmasKind′
  ; ⌊⌋≡-/    = KindSimpSubstApp.⌊⌋≡-Kind′/
  ; ⌊⌋≡-/Var = KindSimpSubstApp.⌊⌋≡-Kind′/
  }
  where open Substitution

module SimpHSubstLemmas where
  open KindSimpLemmas simpLemmasKind′ public

  -- Kind simplification as a relation commutes with hereditary
  -- substitution.

  ⌊⌋≡-/H : ∀ {m n j k l} {ρ : HSub l m n} → ⌊ j ⌋≡ k → ⌊ j Kind/H ρ ⌋≡ k
  ⌊⌋≡-/H is-★                   = is-★
  ⌊⌋≡-/H (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) = is-⇒ (⌊⌋≡-/H ⌊j₁⌋≡k₁) (⌊⌋≡-/H ⌊j₂⌋≡k₂)

open SimpHSubstLemmas

module TrackSimpleKindsEtaExp where
  open Substitution

  -- NOTE. The definition of the function η-exp in this module is
  -- structurally recursive in the *simple* kind parameter k, but
  -- *not* in the kind (j : Kind Elim n) because we need to weaken the
  -- domain j₁ of the dependent kind (j = Π j₁ j₂) in the arrow case.
  -- The additional hypothesis ⌊ j ⌋≡ k ensures that k is indeed the
  -- simplification of the kind j.

  -- Kind-driven untyped η-expansion of eliminations.
  --
  -- NOTE.  We only expand neutral types since these are the only
  -- non-lambda forms of arrow kind, and thus the only ones that
  -- require expansion to reach η-long β-normal forms.
  η-exp : ∀ {n k} (j : Kind Elim n) → ⌊ j ⌋≡ k → Elim n → Elim n
  η-exp (a ⋯ b)   (is-★)                 c            = c
  η-exp (Π j₁ j₂) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) =
    Λ∙ j₁ (η-exp j₂ ⌊j₂⌋≡k₂ x∙as′)
    where
      x∙as′ = weakenElim (var x ∙ as) ⌜·⌝
                η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
  -- Degenerate cases: either ill-kinded or not neutral.
  {-# CATCHALL #-}
  η-exp (Π j₁ j₂) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (a ∙ bs) = a ∙ bs

  -- η-expansion is sound (w.r.t. βη-reduction)
  η-exp-βη : ∀ {n j k} (hyp : ⌊ j ⌋≡ k) (a : Elim n) →
             ⌞ a ⌟ →βη* ⌞ η-exp j hyp a ⌟
  η-exp-βη is-★                             _            = ε
  η-exp-βη (is-⇒ {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) = begin
      ⌞ var x ∙ as ⌟
    ⟶⟨ ⌈ exp-ne ⌞ j₁ ⌟Kd x ⌞ as ⌟Sp ⌉ ⟩
      Λ _ ((weaken ⌞ var x ∙ as ⌟) · var zero)
    ≡⟨ cong (λ a → Λ _ (a · var zero)) (sym (⌞⌟-/Var (var x ∙ as)) )  ⟩
      Λ _ (⌞ weakenElim (var x ∙ as) ⌟ · var zero)
    ⟶⋆⟨ →βη*-Λ ε (→βη*-· ε (η-exp-βη (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero))) ⟩
      Λ _ (⌞ weakenElim (var x ∙ as) ⌟ ·
             ⌞ η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟)
    ≡⟨ cong (Λ _) (sym (⌞⌟-· (weakenElim (var x ∙ as)) _)) ⟩
      Λ _ ⌞ weakenElim (var x ∙ as) ⌜·⌝
             η-exp (weakenKind′ _) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) ⌟
    ⟶⋆⟨ →βη*-Λ ε (η-exp-βη ⌊j₂⌋≡k₂ _) ⟩
      Λ _ ⌞ η-exp _ ⌊j₂⌋≡k₂ _ ⌟
    ∎
    where open →βη*-Reasoning
  -- Degenerate cases.
  η-exp-βη (is-⇒ _ _) (⊥       ∙ _) = ε
  η-exp-βη (is-⇒ _ _) (⊤       ∙ _) = ε
  η-exp-βη (is-⇒ _ _) (Π _ _   ∙ _) = ε
  η-exp-βη (is-⇒ _ _) ((_ ⇒ _) ∙ _) = ε
  η-exp-βη (is-⇒ _ _) (Λ _ _   ∙ _) = ε
  η-exp-βη (is-⇒ _ _) (ƛ _ _   ∙ _) = ε
  η-exp-βη (is-⇒ _ _) ((_ ⊡ _) ∙ _) = ε

  -- A helper lemma.
  η-exp-⌊⌋≡ : ∀ {n j₁ j₂ k₁ k₂} {a : Elim n}
              (hyp₁ : ⌊ j₁ ⌋≡ k₁) (hyp₂ : ⌊ j₂ ⌋≡ k₂) → j₁ ≡ j₂ → k₁ ≡ k₂ →
              η-exp j₁ hyp₁ a ≡ η-exp j₂ hyp₂ a
  η-exp-⌊⌋≡ hyp₁ hyp₂ refl refl =
    cong (λ hyp → η-exp _ hyp _) (⌊⌋≡-pirr hyp₁ hyp₂)

  -- η-expansion commutes with renaming.
  η-exp-/Var : ∀ {m n j k} (hyp : ⌊ j ⌋≡ k) a {ρ : Sub Fin m n} →
               η-exp j hyp a Elim/Var ρ ≡
                 η-exp (j Kind′/Var ρ) (⌊⌋≡-/Var hyp) (a Elim/Var ρ)
  η-exp-/Var is-★ a = refl
  η-exp-/Var (is-⇒ {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) {ρ} = begin
      η-exp _ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) (var x ∙ as) Elim/Var ρ
    ≡⟨ cong (Λ∙ (j₁ Kind′/Var ρ)) (η-exp-/Var ⌊j₂⌋≡k₂ _) ⟩
      Λ∙ (j₁ Kind′/Var ρ) (η-exp (j₂ Kind′/Var ρ V.↑) (⌊⌋≡-/Var ⌊j₂⌋≡k₂)
        ((weakenElim (var x ∙ as) ⌜·⌝
          η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) Elim/Var
            ρ V.↑))
    ≡⟨ cong (λ c → Λ∙ (j₁ Kind′/Var ρ)
                      (η-exp (j₂ Kind′/Var ρ V.↑) (⌊⌋≡-/Var ⌊j₂⌋≡k₂) c))
            (begin
                weakenElim (var x ∙ as) ⌜·⌝
                  η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
                    Elim/Var ρ V.↑
              ≡⟨ ⌜·⌝-/Var (weakenElim (var x ∙ as)) _ ⟩
                (weakenElim (var x ∙ as) Elim/Var ρ V.↑) ⌜·⌝
                  (η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
                    Elim/Var ρ V.↑)
              ≡⟨ cong₂ _⌜·⌝_ (sym (EVL.wk-commutes (var x ∙ as)))
                       (η-exp-/Var (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) ⟩
                (weakenElim (var x ∙ as Elim/Var ρ)) ⌜·⌝
                  (η-exp (weakenKind′ j₁ Kind′/Var ρ V.↑)
                         (⌊⌋≡-/Var (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                         ((var∙ zero) Elim/Var ρ V.↑))
              ≡⟨ cong ((weakenElim (var x ∙ as Elim/Var ρ)) ⌜·⌝_)
                      (η-exp-⌊⌋≡ (⌊⌋≡-/Var (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                                 (⌊⌋≡-weaken (⌊⌋≡-/Var ⌊j₁⌋≡k₁))
                                 (sym (KVL.wk-commutes j₁)) refl) ⟩
                (weakenElim (var x ∙ as Elim/Var ρ)) ⌜·⌝
                  (η-exp (weakenKind′ (j₁ Kind′/Var ρ))
                         (⌊⌋≡-weaken (⌊⌋≡-/Var ⌊j₁⌋≡k₁))
                         (var∙ zero))
              ∎) ⟩
      η-exp _ (is-⇒ (⌊⌋≡-/Var ⌊j₁⌋≡k₁) (⌊⌋≡-/Var ⌊j₂⌋≡k₂))
              (var x ∙ as Elim/Var ρ)
    ∎
    where
      open ≡-Reasoning
      module V  = VarSubst
      module EL = TermLikeLemmas termLikeLemmasElim
      module KL = TermLikeLemmas termLikeLemmasKind′
      module EVL = LiftAppLemmas EL.varLiftAppLemmas
      module KVL = LiftAppLemmas KL.varLiftAppLemmas
  η-exp-/Var (is-⇒ _ _) (⊥       ∙ _) = refl
  η-exp-/Var (is-⇒ _ _) (⊤       ∙ _) = refl
  η-exp-/Var (is-⇒ _ _) (Π _ _   ∙ _) = refl
  η-exp-/Var (is-⇒ _ _) ((_ ⇒ _) ∙ _) = refl
  η-exp-/Var (is-⇒ _ _) (Λ _ _   ∙ _) = refl
  η-exp-/Var (is-⇒ _ _) (ƛ _ _   ∙ _) = refl
  η-exp-/Var (is-⇒ _ _) (_ ⊡ _   ∙ _) = refl

  -- η-expansion of neutrals commutes with hereditary substitutions
  -- that miss the head of the neutral.
  η-exp-ne-Miss-/H : ∀ {l m n j k} x y {as} {ρ : HSub l m n}
                     (hyp : ⌊ j ⌋≡ k) → Miss ρ x y →
                     η-exp j hyp (var x ∙ as) /H ρ  ≡
                       η-exp (j Kind/H ρ) (⌊⌋≡-/H hyp) (var y ∙ (as //H ρ))
  η-exp-ne-Miss-/H x y is-★ miss = ne-/H-Miss x y miss
  η-exp-ne-Miss-/H x y {as} {ρ} (is-⇒ {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) miss =
    cong (Λ∙ (j₁ Kind/H ρ)) (begin
       η-exp j₂ ⌊j₂⌋≡k₂ ((weakenElim (var x ∙ as)) ⌜·⌝
         η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H ρ H↑
      ≡⟨ cong (λ x → η-exp _ ⌊j₂⌋≡k₂ (var x ∙ weakenSpine as ⌜·⌝ _) /H ρ H↑)
              (VarLemmas.lookup-wk x) ⟩
       η-exp j₂ ⌊j₂⌋≡k₂ (var (suc x) ∙ (weakenSpine as) ⌜·⌝
         η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) /H ρ H↑
      ≡⟨ η-exp-ne-Miss-/H (suc x) (suc y) ⌊j₂⌋≡k₂ miss-↑ ⟩
       η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var (suc y) ∙
         (((weakenSpine as) ∷ʳ
           η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                    (var∙ zero)) //H ρ H↑))
      ≡⟨ cong (λ bs → η-exp _ (⌊⌋≡-/H ⌊j₂⌋≡k₂) (var _ ∙ bs))
              (++-//H (weakenSpine as) (_ ∷ [])) ⟩
       η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
         (var (suc y) ∙ ((weakenSpine as) //H ρ H↑) ⌜·⌝
           (η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero) /H ρ H↑))
      ≡⟨ cong₂ (λ a b → η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂) (a ⌜·⌝ b))
               (cong₂ (λ x as → var x ∙ as)
                      (sym (VarLemmas.lookup-wk y)) (wk-//H-↑⋆ 0 as))
               (η-exp-ne-Miss-/H zero zero (⌊⌋≡-weaken ⌊j₁⌋≡k₁)
                                 (↑-zero-Miss ρ)) ⟩
       η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
         (weakenElim (var y ∙ (as //H ρ)) ⌜·⌝
           η-exp ((weakenKind′ j₁) Kind/H ρ H↑)
                    (⌊⌋≡-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁)) (var∙ zero))
      ≡⟨ cong (λ a → η-exp _ (⌊⌋≡-/H ⌊j₂⌋≡k₂)
                       (weakenElim (var y ∙ (as //H ρ)) ⌜·⌝ a))
              (η-exp-⌊⌋≡ (⌊⌋≡-/H (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                            (⌊⌋≡-weaken (⌊⌋≡-/H ⌊j₁⌋≡k₁))
                            (wk-Kind/H-↑⋆ 0 j₁) refl) ⟩
       η-exp (j₂ Kind/H ρ H↑) (⌊⌋≡-/H ⌊j₂⌋≡k₂)
         ((weakenElim (var y ∙ (as //H ρ))) ⌜·⌝
           η-exp (weakenKind′ (j₁ Kind/H ρ)) (⌊⌋≡-weaken (⌊⌋≡-/H ⌊j₁⌋≡k₁))
                    (var∙ zero))
      ∎)
      where
        open ≡-Reasoning
        open RenamingCommutes
        miss-↑ = ↑-Miss ρ miss

private module TK = TrackSimpleKindsEtaExp

-- Kind-driven untyped η-expansion.
η-exp : ∀ {n} → Kind Elim n → Elim n → Elim n
η-exp k a = TK.η-exp k (⌊⌋-⌊⌋≡ k) a

-- η-expansion is sound (w.r.t. βη-reduction)
η-exp-βη : ∀ {n} k (a : Elim n) → ⌞ a ⌟ →βη* ⌞ η-exp k a ⌟
η-exp-βη k a = TK.η-exp-βη (⌊⌋-⌊⌋≡ k) a

module _ where
  open Substitution
  open ≡-Reasoning

  -- η-expansion commutes with renaming.
  η-exp-/Var : ∀ {m n} k a {ρ : Sub Fin m n} →
               η-exp k a Elim/Var ρ ≡ η-exp (k Kind′/Var ρ) (a Elim/Var ρ)
  η-exp-/Var k a {ρ} = begin
      η-exp k a Elim/Var ρ
    ≡⟨ TK.η-exp-/Var (⌊⌋-⌊⌋≡ k) a ⟩
      TK.η-exp (k Kind′/Var ρ) (⌊⌋≡-/Var (⌊⌋-⌊⌋≡ k)) (a Elim/Var ρ)
    ≡⟨ TK.η-exp-⌊⌋≡ (⌊⌋≡-/Var (⌊⌋-⌊⌋≡ k)) (⌊⌋-⌊⌋≡ (k Kind′/Var ρ))
                    refl (sym (⌊⌋-Kind′/Var k)) ⟩
      η-exp (k Kind′/Var ρ) (a Elim/Var ρ)
    ∎

  -- A corollary: η-expansion commutes with weakening.
  η-exp-weaken : ∀ {n} k (a : Elim n) →
                 weakenElim (η-exp k a) ≡ η-exp (weakenKind′ k) (weakenElim a)
  η-exp-weaken k a = η-exp-/Var k a

  -- η-expansion of neutrals commutes with hereditary substitutions
  -- that miss the head of the neutral.
  η-exp-ne-Miss-/H : ∀ {l m n} x y as k {ρ : HSub l m n} → Miss ρ x y →
                     η-exp k (var x ∙ as) /H ρ  ≡
                       η-exp (k Kind/H ρ) (var y ∙ (as //H ρ))
  η-exp-ne-Miss-/H x y as k {ρ} miss = begin
      η-exp k (var x ∙ as) /H ρ
    ≡⟨ TK.η-exp-ne-Miss-/H x y (⌊⌋-⌊⌋≡ k) miss ⟩
      TK.η-exp (k Kind/H ρ) (⌊⌋≡-/H (⌊⌋-⌊⌋≡ k)) (var y ∙ (as //H ρ))
    ≡⟨ TK.η-exp-⌊⌋≡ (⌊⌋≡-/H (⌊⌋-⌊⌋≡ k)) (⌊⌋-⌊⌋≡ (k Kind/H ρ)) refl
                    (sym (⌊⌋-Kind/H k)) ⟩
      η-exp (k Kind/H ρ) (var y ∙ (as //H ρ))
    ∎


----------------------------------------------------------------------
-- Untyped normalization.

open ElimCtx

-- Normalize an raw type or kind into η-long β-normal form if
-- possible.  Degenerate cases are marked "!".

mutual

  nf : ∀ {n} → Ctx n → Term n → Elim n
  nf Γ (var x) with lookup x Γ
  nf Γ (var x) | kd k = η-exp k (var∙ x)
  nf Γ (var x) | tp a = var x ∙ []                -- ! a not a kind
  nf Γ ⊥       = ⊥ ∙ []
  nf Γ ⊤       = ⊤ ∙ []
  nf Γ (Π k a) = let k′ = nfKind Γ k in ∀∙ k′ (nf (kd k′ ∷ Γ) a)
  nf Γ (a ⇒ b) = (nf Γ a ⇒ nf Γ b) ∙ []
  nf Γ (Λ k a) = let k′ = nfKind Γ k in Λ∙ k′ (nf (kd k′ ∷ Γ) a)
  nf Γ (ƛ a b) = ƛ∙ ⌜ a ⌝ ⌜ b ⌝                   -- ! ƛ a b not a type
  nf Γ (a · b) = nf Γ a ↓⌜·⌝ nf Γ b
  nf Γ (a ⊡ b) = ⌜ a ⌝ ⊡ ⌜ b ⌝ ∙ []               -- ! a ⊡ b not a type

  nfKind : ∀ {n} → Ctx n → Kind Term n → Kind Elim n
  nfKind Γ (a ⋯ b) = nf Γ a ⋯ nf Γ b
  nfKind Γ (Π j k) = let j′ = nfKind Γ j in Π j′ (nfKind (kd j′ ∷ Γ) k)

-- Normalization extended to contexts.

nfAsc : ∀ {n} → Ctx n → TermAsc n → ElimAsc n
nfAsc Γ (kd k) = kd (nfKind Γ k)
nfAsc Γ (tp a) = tp (nf Γ a)

nfCtx : ∀ {n} → TermCtx.Ctx n → Ctx n
nfCtx []      = []
nfCtx (a ∷ Γ) = let Γ′ = nfCtx Γ in nfAsc Γ′ a ∷ Γ′

nfCtxExt : ∀ {m n} → Ctx m → TermCtx.CtxExt′ m n → CtxExt′ m n
nfCtxExt Γ []      = []
nfCtxExt Γ (a ∷ Δ) = let Δ′ = nfCtxExt Γ Δ in nfAsc (Δ′ ′++ Γ) a ∷ Δ′

-- Simple kinds are stable w.r.t. normalization.
⌊⌋-nf : ∀ {n} {Γ : Ctx n} k → ⌊ nfKind Γ k ⌋ ≡ ⌊ k ⌋
⌊⌋-nf (a ⋯ b) = refl
⌊⌋-nf (Π j k) = cong₂ _⇒_ (⌊⌋-nf j) (⌊⌋-nf k)

open SimpleCtx using (⌊_⌋Asc; kd; tp)
open ContextConversions using (⌊_⌋Ctx)

-- Simple contexts are stable w.r.t. normalization.

⌊⌋Asc-nf : ∀ {n} {Γ : Ctx n} a → ⌊ nfAsc Γ a ⌋Asc ≡ ⌊ a ⌋Asc
⌊⌋Asc-nf (kd k) = cong kd (⌊⌋-nf k)
⌊⌋Asc-nf (tp a) = refl

⌊⌋Ctx-nf : ∀ {n} (Γ : TermCtx.Ctx n) → ⌊ nfCtx Γ ⌋Ctx ≡ ⌊ Γ ⌋Ctx
⌊⌋Ctx-nf []      = refl
⌊⌋Ctx-nf (a ∷ Γ) = cong₂ _∷_ (⌊⌋Asc-nf a) (⌊⌋Ctx-nf Γ)

-- Normalization commutes with context concatenation.
nf-++ : ∀ {m n} (Δ : TermCtx.CtxExt′ m n) Γ →
        nfCtx (Δ ′++ Γ) ≡ nfCtxExt (nfCtx Γ) Δ ′++ nfCtx Γ
nf-++ []      Γ = refl
nf-++ (a ∷ Δ) Γ = cong₂ _∷_ (cong (λ Δ → nfAsc Δ a) (nf-++ Δ Γ)) (nf-++ Δ Γ)

-- A helper lemma about normalization of variables.
nf-var-kd : ∀ {n} (Γ : Ctx n) {k} x →
            lookup x Γ ≡ kd k → nf Γ (var x) ≡ η-exp k (var∙ x)
nf-var-kd Γ x Γ[x]≡kd-k with lookup x Γ
nf-var-kd Γ x refl | kd k = refl
nf-var-kd Γ x ()   | tp _

module RenamingCommutesNorm where
  open Substitution hiding (subst; varLiftAppLemmas)
  open TermLikeLemmas termLikeLemmasElimAsc
    using (varApplication; varLiftAppLemmas)
  open RenamingCommutes
  open ⊤-WellFormed weakenOps
  open ≡-Reasoning

  private
    module V  = VarSubst
    module AL = LiftAppLemmas varLiftAppLemmas

  -- Well-formed renamings.
  --
  -- A renaming `ρ' is well-formed `Δ ⊢/ ρ ∈ Γ' if it maps ascriptions
  -- from the source contxt `Γ' to the target context `Δ' in a manner
  -- that is consistent with the renaming, i.e. such that we have
  -- `Δ(ρ(x)) = Γ(x)ρ'.
  kindedVarSubst : TypedVarSubst (_⊢_wf)
  kindedVarSubst = record
    { application = varApplication
    ; weakenOps   = weakenOps
    ; /-wk        = refl
    ; id-vanishes = AL.id-vanishes
    ; /-⊙         = AL./-⊙
    ; wf-wf       = λ _ → ctx-wf _
    }
  open TypedVarSubst kindedVarSubst
  private module TS = TypedSub typedSub

  -- Extract a "consistency" proof from a well-formed renaming, i.e. a
  -- proof that `Δ(ρ(x)) = Γ(x)ρ'.
  lookup-≡ : ∀ {m n Δ Γ} {ρ : Sub Fin m n} x → Δ ⊢/Var ρ ∈ Γ →
             lookup (Vec.lookup x ρ) Δ ≡ lookup x Γ ElimAsc/Var ρ
  lookup-≡ {_} {_} {Δ} {Γ} {ρ} x ρ∈Γ
    with Vec.lookup x ρ | lookup x Γ ElimAsc/Var ρ | TS.lookup x ρ∈Γ
  lookup-≡ x ρ∈Γ | y | _ | VarTyping.var .y _ = refl

  mutual

    -- A helper.
    ∈-↑′ : ∀ {m n Δ Γ} {ρ : Sub Fin m n} k → Δ ⊢/Var ρ ∈ Γ →
           kd (nfKind Δ (k Kind/Var ρ)) ∷ Δ ⊢/Var ρ V.↑ ∈ (nfAsc Γ (kd k) ∷ Γ)
    ∈-↑′ k ρ∈Γ =
      subst (λ k → kd k ∷ _ ⊢/Var _ ∈ _) (nfKind-/Var k ρ∈Γ) (∈-↑ tt ρ∈Γ)

    -- Normalization commutes with renaming.

    nf-/Var : ∀ {m n Δ Γ} {ρ : Sub Fin m n} a → Δ ⊢/Var ρ ∈ Γ →
              nf Γ a Elim/Var ρ ≡ nf Δ (a /Var ρ)
    nf-/Var {_} {_} {Δ} {Γ} {ρ} (var x) ρ∈Γ
      with lookup x Γ | lookup (Vec.lookup x ρ) Δ | lookup-≡ x ρ∈Γ
    nf-/Var (var x) ρ∈Γ | kd k | _ | refl = η-exp-/Var k (var∙ x)
    nf-/Var (var x) ρ∈Γ | tp a | _ | refl = refl
    nf-/Var ⊥       ρ∈Γ = refl
    nf-/Var ⊤       ρ∈Γ = refl
    nf-/Var (Π k a) ρ∈Γ = cong₂ ∀∙ (nfKind-/Var k ρ∈Γ) (nf-/Var a (∈-↑′ k ρ∈Γ))
    nf-/Var (a ⇒ b) ρ∈Γ = cong₂ _⇒∙_ (nf-/Var a ρ∈Γ) (nf-/Var b ρ∈Γ)
    nf-/Var (Λ j a) ρ∈Γ = cong₂ Λ∙ (nfKind-/Var j ρ∈Γ) (nf-/Var a (∈-↑′ j ρ∈Γ))
    nf-/Var (ƛ a b) ρ∈Γ = cong₂ ƛ∙ (sym (⌜⌝-/Var a)) (sym (⌜⌝-/Var b))
    nf-/Var {m} {_} {Δ} {Γ} {ρ} (a · b) ρ∈Γ = begin
        (nf Γ a ↓⌜·⌝ nf Γ b) Elim/Var ρ
      ≡⟨ ↓⌜·⌝-/ (nf Γ a) (nf Γ b) ⟩
        (nf Γ a Elim/Var ρ) ↓⌜·⌝ (nf Γ b Elim/Var ρ)
      ≡⟨ cong₂ (_↓⌜·⌝_) (nf-/Var a ρ∈Γ) (nf-/Var b ρ∈Γ) ⟩
        nf Δ (a · b /Var ρ)
      ∎
    nf-/Var (a ⊡ b) ρ∈Γ =
      cong₂ (λ a b → a ⊡ b ∙ []) (sym (⌜⌝-/Var a)) (sym (⌜⌝-/Var b))

    nfKind-/Var : ∀ {m n Δ Γ} {ρ : Sub Fin m n} k → Δ ⊢/Var ρ ∈ Γ →
                  nfKind Γ k Kind′/Var ρ ≡ nfKind Δ (k Kind/Var ρ)
    nfKind-/Var (a ⋯ b) ρ∈Γ = cong₂ _⋯_ (nf-/Var a ρ∈Γ) (nf-/Var b ρ∈Γ)
    nfKind-/Var (Π j k) ρ∈Γ =
      cong₂ Π (nfKind-/Var j ρ∈Γ) (nfKind-/Var k (∈-↑′ j ρ∈Γ))

  -- Normalization of ascriptions commutes with renaming.
  nfAsc-/Var : ∀ {m n Δ Γ} {ρ : Sub Fin m n} a → Δ ⊢/Var ρ ∈ Γ →
               nfAsc Γ a ElimAsc/Var ρ ≡ nfAsc Δ (a TermAsc/Var ρ)
  nfAsc-/Var (kd k) ρ∈Γ = cong kd (nfKind-/Var k ρ∈Γ)
  nfAsc-/Var (tp a) ρ∈Γ = cong tp (nf-/Var a ρ∈Γ)

  -- Corollaries: normalization commutes with weakening.

  nf-weaken : ∀ {n} {Γ : Ctx n} a b →
              weakenElim (nf Γ b) ≡ nf (a ∷ Γ) (weaken b)
  nf-weaken a b = nf-/Var b (∈-wk tt)

  nf-weaken⋆ : ∀ {m n} (Γ₂ : CtxExt′ m n) {Γ₁ : Ctx m} a →
               weakenElim⋆ n (nf Γ₁ a) ≡ nf (Γ₂ ′++ Γ₁) (weaken⋆ n a)
  nf-weaken⋆             []            a = refl
  nf-weaken⋆ {_} {suc n} (b ∷ Γ₂) {Γ₁} a = begin
      weakenElim⋆ (suc n) (nf Γ₁ a)
    ≡⟨ cong weakenElim (nf-weaken⋆ Γ₂ a) ⟩
      weakenElim (nf (Γ₂ ′++ Γ₁) (weaken⋆ n a))
    ≡⟨ nf-weaken b (weaken⋆ n a) ⟩
      nf ((b ∷ Γ₂) ′++ Γ₁) (weaken⋆ (suc n) a)
    ∎

  nfKind-weaken : ∀ {n} {Γ : Ctx n} a k →
                  weakenKind′ (nfKind Γ k) ≡ nfKind (a ∷ Γ) (weakenKind k)
  nfKind-weaken a k = nfKind-/Var k (∈-wk tt)

  nfAsc-weaken : ∀ {n} {Γ : Ctx n} a b →
                 weakenElimAsc (nfAsc Γ b) ≡ nfAsc (a ∷ Γ) (weakenTermAsc b)
  nfAsc-weaken a b = nfAsc-/Var b (∈-wk tt)

open RenamingCommutesNorm

module _ where
  open Substitution
  open ≡-Reasoning
  open VecProps using (map-cong; map-∘)

  -- Normalization commutes conversion from context to vector representation.
  nfCtx-toVec : ∀ {n} (Γ : TermCtx.Ctx n) →
                toVec (nfCtx Γ) ≡ Vec.map (nfAsc (nfCtx Γ)) (TermCtx.toVec Γ)
  nfCtx-toVec []      = refl
  nfCtx-toVec (a ∷ Γ) =
    cong₂ _∷_ (nfAsc-weaken (nfAsc (nfCtx Γ) a) a) (begin
        Vec.map weakenElimAsc (toVec (nfCtx Γ))
      ≡⟨ cong (Vec.map weakenElimAsc) (nfCtx-toVec Γ) ⟩
        Vec.map weakenElimAsc (Vec.map (nfAsc (nfCtx Γ)) (TermCtx.toVec Γ))
      ≡⟨ sym (map-∘ weakenElimAsc (nfAsc (nfCtx Γ)) (TermCtx.toVec Γ)) ⟩
        Vec.map (weakenElimAsc ∘ nfAsc (nfCtx Γ)) (TermCtx.toVec Γ)
      ≡⟨ map-cong (nfAsc-weaken (nfAsc (nfCtx Γ) a)) (TermCtx.toVec Γ) ⟩
        Vec.map (nfAsc (nfCtx (a ∷ Γ)) ∘ weakenTermAsc) (TermCtx.toVec Γ)
      ≡⟨ map-∘ (nfAsc (nfCtx (a ∷ Γ))) weakenTermAsc (TermCtx.toVec Γ) ⟩
        Vec.map (nfAsc (nfCtx (a ∷ Γ)))
                (Vec.map weakenTermAsc (TermCtx.toVec Γ))
      ∎)

  -- Normalization commutes with context lookup.
  nfCtx-lookup : ∀ {n} x (Γ : TermCtx.Ctx n) →
                 lookup x (nfCtx Γ) ≡ nfAsc (nfCtx Γ) (TermCtx.lookup x Γ)
  nfCtx-lookup x Γ = begin
      lookup x (nfCtx Γ)
    ≡⟨ cong (Vec.lookup x) (nfCtx-toVec Γ) ⟩
      Vec.lookup x (Vec.map (nfAsc (nfCtx Γ)) (TermCtx.toVec Γ))
    ≡⟨ VecProps.lookup-map x _ _ ⟩
      nfAsc (nfCtx Γ) (TermCtx.lookup x Γ)
    ∎

  -- A corollary of the above.
  nfCtx-lookup-kd : ∀ {n k} x (Γ : TermCtx.Ctx n) → TermCtx.lookup x Γ ≡ kd k →
                    lookup x (nfCtx Γ) ≡ kd (nfKind (nfCtx Γ) k)
  nfCtx-lookup-kd x Γ Γ[x]≡kd-k with TermCtx.lookup x Γ | nfCtx-lookup x Γ
  nfCtx-lookup-kd x Γ refl | kd k | nf-Γ[x]≡kd-nf-k = nf-Γ[x]≡kd-nf-k
  nfCtx-lookup-kd x Γ ()   | tp t | _

open →βη*-Reasoning

mutual

  -- Normalization preserves types and kinds up to βη-reduction (and
  -- conversion of representation).

  ⌞⌟-nf-βη : ∀ {n} (Γ : Ctx n) a → a →βη* ⌞ nf Γ a ⌟
  ⌞⌟-nf-βη Γ (var x) with lookup x Γ
  ⌞⌟-nf-βη Γ (var x) | kd a = η-exp-βη a (var∙ x)
  ⌞⌟-nf-βη Γ (var x) | tp a = ε
  ⌞⌟-nf-βη Γ ⊥       = ε
  ⌞⌟-nf-βη Γ ⊤       = ε
  ⌞⌟-nf-βη Γ (Π k a) =
    →βη*-Π (⌞⌟Kd-nf-βη Γ k) (⌞⌟-nf-βη (kd (nfKind Γ k) ∷ Γ) a)
  ⌞⌟-nf-βη Γ (a ⇒ b) = →βη*-⇒ (⌞⌟-nf-βη Γ a) (⌞⌟-nf-βη Γ b)
  ⌞⌟-nf-βη Γ (Λ k a) =
    →βη*-Λ (⌞⌟Kd-nf-βη Γ k) (⌞⌟-nf-βη (kd (nfKind Γ k) ∷ Γ) a)
  ⌞⌟-nf-βη Γ (ƛ a b) = begin
    ƛ a b              ≡⟨ cong₂ ƛ (sym (⌞⌟∘⌜⌝-id a)) (sym (⌞⌟∘⌜⌝-id b)) ⟩
    ⌞ nf Γ (ƛ a b) ⌟   ∎
  ⌞⌟-nf-βη Γ (a · b) = begin
      a · b
    ⟶⋆⟨ →βη*-· (⌞⌟-nf-βη Γ a) (⌞⌟-nf-βη Γ b) ⟩
      ⌞ nf Γ a ⌟ · ⌞ nf Γ b ⌟
    ⟶⋆⟨ →β*⇒→βη* (⌞⌟-↓⌜·⌝-β (nf Γ a) (nf Γ b)) ⟩
      ⌞ nf Γ a ↓⌜·⌝ nf Γ b ⌟
    ∎
  ⌞⌟-nf-βη Γ (a ⊡ b) = begin
    a ⊡ b              ≡⟨ cong₂ _⊡_ (sym (⌞⌟∘⌜⌝-id a)) (sym (⌞⌟∘⌜⌝-id b)) ⟩
    ⌞ nf Γ (a ⊡ b) ⌟   ∎

  ⌞⌟Kd-nf-βη : ∀ {n} (Γ : Ctx n) k → k Kd→βη* ⌞ nfKind Γ k ⌟Kd
  ⌞⌟Kd-nf-βη Γ (a ⋯ b) = Kd→βη*-⋯ (⌞⌟-nf-βη Γ a) (⌞⌟-nf-βη Γ b)
  ⌞⌟Kd-nf-βη Γ (Π j k) =
    Kd→βη*-Π (⌞⌟Kd-nf-βη Γ j) (⌞⌟Kd-nf-βη (kd (nfKind Γ j) ∷ Γ) k)
