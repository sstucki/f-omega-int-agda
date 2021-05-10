------------------------------------------------------------------------
-- Normalization of raw terms in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --exact-split --without-K #-}

module FOmegaInt.Syntax.Normalization where

open import Data.Context.WellFormed using (module ⊤-WellFormed)
open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas using (module VarLemmas)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProps
open import Function using (_∘_; flip)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)
open import Relation.Binary.PropositionalEquality as P hiding ([_])

open import FOmegaInt.Reduction.Full
open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution
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

  ⌊⌋≡-/⟨⟩ : ∀ {m n j k l} {σ : SVSub m n} → ⌊ j ⌋≡ k → ⌊ j Kind/⟨ l ⟩ σ ⌋≡ k
  ⌊⌋≡-/⟨⟩ is-★                   = is-★
  ⌊⌋≡-/⟨⟩ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) = is-⇒ (⌊⌋≡-/⟨⟩ ⌊j₁⌋≡k₁) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)

open SimpHSubstLemmas

module TrackSimpleKindsEtaExp where
  open Substitution hiding (_↑; sub)

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
  η-exp (c ⋯ d)   (is-★)                 a = a
  η-exp (Π j₁ j₂) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a =
    Λ∙ j₁ (η-exp j₂ ⌊j₂⌋≡k₂ a·ηz)
    where
      a·ηz = weakenElim a ⌜·⌝
               η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)

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
  η-exp-/Var (is-⇒ {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a {ρ} = begin
      η-exp _ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) a Elim/Var ρ
    ≡⟨ cong (Λ∙ (j₁ Kind′/Var ρ)) (η-exp-/Var ⌊j₂⌋≡k₂ _) ⟩
      Λ∙ (j₁ Kind′/Var ρ) (η-exp (j₂ Kind′/Var ρ V.↑) (⌊⌋≡-/Var ⌊j₂⌋≡k₂)
        ((weakenElim a ⌜·⌝
          η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) Elim/Var
            ρ V.↑))
    ≡⟨ cong (λ c → Λ∙ (j₁ Kind′/Var ρ)
                      (η-exp (j₂ Kind′/Var ρ V.↑) (⌊⌋≡-/Var ⌊j₂⌋≡k₂) c))
            (begin
                weakenElim a ⌜·⌝
                  η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
                    Elim/Var ρ V.↑
              ≡⟨ ⌜·⌝-/Var (weakenElim a) _ ⟩
                (weakenElim a Elim/Var ρ V.↑) ⌜·⌝
                  (η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)
                    Elim/Var ρ V.↑)
              ≡⟨ cong₂ _⌜·⌝_ (sym (EVL.wk-commutes a))
                       (η-exp-/Var (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)) ⟩
                (weakenElim (a Elim/Var ρ)) ⌜·⌝
                  (η-exp (weakenKind′ j₁ Kind′/Var ρ V.↑)
                         (⌊⌋≡-/Var (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                         ((var∙ zero) Elim/Var ρ V.↑))
              ≡⟨ cong ((weakenElim (a Elim/Var ρ)) ⌜·⌝_)
                      (η-exp-⌊⌋≡ (⌊⌋≡-/Var (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                                 (⌊⌋≡-weaken (⌊⌋≡-/Var ⌊j₁⌋≡k₁))
                                 (sym (KVL.wk-commutes j₁)) refl) ⟩
                (weakenElim (a Elim/Var ρ)) ⌜·⌝
                  (η-exp (weakenKind′ (j₁ Kind′/Var ρ))
                         (⌊⌋≡-weaken (⌊⌋≡-/Var ⌊j₁⌋≡k₁))
                         (var∙ zero))
              ∎) ⟩
      η-exp _ (is-⇒ (⌊⌋≡-/Var ⌊j₁⌋≡k₁) (⌊⌋≡-/Var ⌊j₂⌋≡k₂)) (a Elim/Var ρ)
    ∎
    where
      open ≡-Reasoning
      module V  = VarSubst
      module EL = TermLikeLemmas termLikeLemmasElim
      module KL = TermLikeLemmas termLikeLemmasKind′
      module EVL = LiftAppLemmas EL.varLiftAppLemmas
      module KVL = LiftAppLemmas KL.varLiftAppLemmas


  -- η-expansion of neutrals commutes with hereditary substitutions
  -- that miss the head of the neutral.

  η-exp-ne-Miss-/⟨⟩ : ∀ {l m n j k} x y {as} {σ : SVSub m n}
                      (hyp : ⌊ j ⌋≡ k) → Miss σ x y →
                      η-exp j hyp (var x ∙ as) /⟨ l ⟩ σ  ≡
                        η-exp (j Kind/⟨ l ⟩ σ) (⌊⌋≡-/⟨⟩ hyp)
                              (var y ∙ (as //⟨ l ⟩ σ))
  η-exp-ne-Miss-/⟨⟩ x y is-★ missP = cong (_?∙∙⟨ _ ⟩ _) (lookup-Miss missP)
  η-exp-ne-Miss-/⟨⟩ {l} x y {as} {σ} (is-⇒ {j₁} {j₂} ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) missP =
    cong (Λ∙ (j₁ Kind/⟨ l ⟩ σ)) (begin
       η-exp j₂ ⌊j₂⌋≡k₂ ((weakenElim (var x ∙ as)) ⌜·⌝ ηz) /⟨ l ⟩ σ ↑
      ≡⟨ cong (λ x → η-exp _ ⌊j₂⌋≡k₂ (var x ∙ weakenSpine as ⌜·⌝ _) /⟨ l ⟩ σ ↑)
              (VarLemmas.lookup-wk x) ⟩
       η-exp j₂ ⌊j₂⌋≡k₂ (var (suc x) ∙ (weakenSpine as) ⌜·⌝ ηz) /⟨ l ⟩ σ ↑
      ≡⟨ η-exp-ne-Miss-/⟨⟩ (suc x) (suc y) ⌊j₂⌋≡k₂ (missP ↑) ⟩
       η-exp (j₂ Kind/⟨ l ⟩ σ ↑) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (var (suc y) ∙
         (((weakenSpine as) ∷ʳ ηz) //⟨ l ⟩ σ ↑))
      ≡⟨ cong (λ bs → η-exp _ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (var _ ∙ bs))
              (++-//⟨⟩ (weakenSpine as) (_ ∷ [])) ⟩
       η-exp (j₂ Kind/⟨ l ⟩ σ ↑) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
         (var (suc y) ∙ ((weakenSpine as) //⟨ l ⟩ σ ↑) ⌜·⌝ (ηz /⟨ l ⟩ σ ↑))
      ≡⟨ cong₂ (λ a b → η-exp (j₂ Kind/⟨ l ⟩ σ ↑) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂) (a ⌜·⌝ b))
               (cong₂ (λ x as → var x ∙ as)
                      (sym (VarLemmas.lookup-wk y)) (wk-//⟨⟩-↑⋆ 0 as))
               (η-exp-ne-Miss-/⟨⟩ zero zero (⌊⌋≡-weaken ⌊j₁⌋≡k₁) under) ⟩
       η-exp (j₂ Kind/⟨ l ⟩ σ ↑) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
         (weakenElim (var y ∙ (as //⟨ l ⟩ σ)) ⌜·⌝
           η-exp ((weakenKind′ j₁) Kind/⟨ l ⟩ σ ↑)
                 (⌊⌋≡-/⟨⟩ (⌊⌋≡-weaken ⌊j₁⌋≡k₁)) (var∙ zero))
      ≡⟨ cong (λ a → η-exp _ (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
                       (weakenElim (var y ∙ (as //⟨ l ⟩ σ)) ⌜·⌝ a))
              (η-exp-⌊⌋≡ (⌊⌋≡-/⟨⟩ (⌊⌋≡-weaken ⌊j₁⌋≡k₁))
                         (⌊⌋≡-weaken (⌊⌋≡-/⟨⟩ ⌊j₁⌋≡k₁))
                         (wk-Kind/⟨⟩-↑⋆ 0 j₁) refl) ⟩
       η-exp (j₂ Kind/⟨ l ⟩ σ ↑) (⌊⌋≡-/⟨⟩ ⌊j₂⌋≡k₂)
         ((weakenElim (var y ∙ (as //⟨ l ⟩ σ))) ⌜·⌝
           η-exp (weakenKind′ (j₁ Kind/⟨ l ⟩ σ))
                 (⌊⌋≡-weaken (⌊⌋≡-/⟨⟩ ⌊j₁⌋≡k₁)) (var∙ zero))
      ∎)
      where
        open ≡-Reasoning
        open RenamingCommutes
        ηz = η-exp (weakenKind′ j₁) (⌊⌋≡-weaken ⌊j₁⌋≡k₁) (var∙ zero)

private module TK = TrackSimpleKindsEtaExp

-- Kind-driven untyped η-expansion.
η-exp : ∀ {n} → Kind Elim n → Elim n → Elim n
η-exp k a = TK.η-exp k (⌊⌋-⌊⌋≡ k) a

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
  η-exp-ne-Miss-/⟨⟩ : ∀ {l m n} x y as k {σ : SVSub m n} → Miss σ x y →
                      η-exp k (var x ∙ as) /⟨ l ⟩ σ  ≡
                        η-exp (k Kind/⟨ l ⟩ σ) (var y ∙ (as //⟨ l ⟩ σ))
  η-exp-ne-Miss-/⟨⟩ {l} x y as k {σ} missP = begin
      η-exp k (var x ∙ as) /⟨ l ⟩ σ
    ≡⟨ TK.η-exp-ne-Miss-/⟨⟩ x y (⌊⌋-⌊⌋≡ k) missP ⟩
      TK.η-exp (k Kind/⟨ l ⟩ σ) (⌊⌋≡-/⟨⟩ (⌊⌋-⌊⌋≡ k)) (var y ∙ (as //⟨ l ⟩ σ))
    ≡⟨ TK.η-exp-⌊⌋≡ (⌊⌋≡-/⟨⟩ (⌊⌋-⌊⌋≡ k)) (⌊⌋-⌊⌋≡ (k Kind/⟨ l ⟩ σ)) refl
                    (sym (⌊⌋-Kind/⟨⟩ k)) ⟩
      η-exp (k Kind/⟨ l ⟩ σ) (var y ∙ (as //⟨ l ⟩ σ))
    ∎


----------------------------------------------------------------------
-- Untyped normalization.

open ElimCtx

-- Normalize an raw type or kind into η-long β-normal form if
-- possible.  Degenerate cases are marked "!".

mutual

  nf : ∀ {n} → Ctx n → Term n → Elim n
  nf Γ (var x) with lookup Γ x
  nf Γ (var x) | kd k = η-exp k (var∙ x)
  nf Γ (var x) | tp a = var∙ x                    -- ! a not a kind
  nf Γ ⊥       = ⊥∙
  nf Γ ⊤       = ⊤∙
  nf Γ (Π k a) = let k′ = nfKind Γ k in ∀∙ k′ (nf (kd k′ ∷ Γ) a)
  nf Γ (a ⇒ b) = (nf Γ a ⇒ nf Γ b) ∙ []
  nf Γ (Λ k a) = let k′ = nfKind Γ k in Λ∙ k′ (nf (kd k′ ∷ Γ) a)
  nf Γ (ƛ a b) = ƛ∙ ⌜ a ⌝ ⌜ b ⌝                   -- ! ƛ a b not a type
  nf Γ (a · b) = nf Γ a ↓⌜·⌝ nf Γ b
  nf Γ (a ⊡ b) = ⌜ a ⌝ ⊡∙ ⌜ b ⌝                   -- ! a ⊡ b not a type

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

nfCtxExt : ∀ {m n} → Ctx m → TermCtx.CtxExt m n → CtxExt m n
nfCtxExt Γ []      = []
nfCtxExt Γ (a ∷ Δ) = let Δ′ = nfCtxExt Γ Δ in nfAsc (Δ′ ++ Γ) a ∷ Δ′

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
nf-++ : ∀ {m n} (Δ : TermCtx.CtxExt m n) Γ →
        nfCtx (Δ ++ Γ) ≡ nfCtxExt (nfCtx Γ) Δ ++ nfCtx Γ
nf-++ []      Γ = refl
nf-++ (a ∷ Δ) Γ = cong₂ _∷_ (cong (λ Δ → nfAsc Δ a) (nf-++ Δ Γ)) (nf-++ Δ Γ)

-- A helper lemma about normalization of variables.

nf-var-kd : ∀ {n} (Γ : Ctx n) {k} x →
            lookup Γ x ≡ kd k → nf Γ (var x) ≡ η-exp k (var∙ x)
nf-var-kd Γ x Γ[x]≡kd-k with lookup Γ x
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

  kindedVarSubst : TypedVarSubst ElimAsc _
  kindedVarSubst = record
    { _⊢_wf              = _⊢_wf
    ; typeExtension      = weakenOps
    ; typeVarApplication = varApplication
    ; wf-wf              = λ _ → ctx-wf _
    ; /-wk               = refl
    ; id-vanishes        = AL.id-vanishes
    ; /-⊙                = AL./-⊙
    }
  open TypedVarSubst kindedVarSubst renaming (lookup to /∈-lookup)

  -- Extract a "consistency" proof from a well-formed renaming, i.e. a
  -- proof that `Δ(ρ(x)) = Γ(x)ρ'.
  lookup-≡ : ∀ {m n Δ Γ} {ρ : Sub Fin m n} → Δ ⊢/Var ρ ∈ Γ → ∀ x →
             lookup Δ (Vec.lookup ρ x) ≡ lookup Γ x ElimAsc/Var ρ
  lookup-≡ {_} {_} {Δ} {Γ} {ρ} ρ∈Γ x
    with Vec.lookup ρ x | lookup Γ x ElimAsc/Var ρ | /∈-lookup ρ∈Γ x
  lookup-≡ ρ∈Γ x | y | _ | VarTyping.∈-var .y _ = refl

  mutual

    -- A helper.
    ∈-↑′ : ∀ {m n Δ Γ} {ρ : Sub Fin m n} k → Δ ⊢/Var ρ ∈ Γ →
           kd (nfKind Δ (k Kind/Var ρ)) ∷ Δ ⊢/Var ρ V.↑ ∈ (nfAsc Γ (kd k) ∷ Γ)
    ∈-↑′ k ρ∈Γ =
      subst (λ k → kd k ∷ _ ⊢/Var _ ∈ _) (nfKind-/Var k ρ∈Γ) (∈-↑ _ ρ∈Γ)

    -- Normalization commutes with renaming.

    nf-/Var : ∀ {m n Δ Γ} {ρ : Sub Fin m n} a → Δ ⊢/Var ρ ∈ Γ →
              nf Γ a Elim/Var ρ ≡ nf Δ (a /Var ρ)
    nf-/Var {_} {_} {Δ} {Γ} {ρ} (var x) ρ∈Γ
      with lookup Γ x | lookup Δ (Vec.lookup ρ x) | lookup-≡ ρ∈Γ x
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
      ≡⟨ ↓⌜·⌝-/Var (nf Γ a) (nf Γ b) ⟩
        (nf Γ a Elim/Var ρ) ↓⌜·⌝ (nf Γ b Elim/Var ρ)
      ≡⟨ cong₂ (_↓⌜·⌝_) (nf-/Var a ρ∈Γ) (nf-/Var b ρ∈Γ) ⟩
        nf Δ (a · b /Var ρ)
      ∎
    nf-/Var (a ⊡ b) ρ∈Γ = cong₂ _⊡∙_ (sym (⌜⌝-/Var a)) (sym (⌜⌝-/Var b))

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
  nf-weaken a b = nf-/Var b (∈-wk _)

  nfKind-weaken : ∀ {n} {Γ : Ctx n} a k →
                  weakenKind′ (nfKind Γ k) ≡ nfKind (a ∷ Γ) (weakenKind k)
  nfKind-weaken a k = nfKind-/Var k (∈-wk _)

  nfAsc-weaken : ∀ {n} {Γ : Ctx n} a b →
                 weakenElimAsc (nfAsc Γ b) ≡ nfAsc (a ∷ Γ) (weakenTermAsc b)
  nfAsc-weaken a b = nfAsc-/Var b (∈-wk _)

open RenamingCommutesNorm

module _ where
  open Substitution hiding (sub; _↑; subst)
  open ≡-Reasoning
  open VecProps using (map-cong; map-∘)

  -- Normalization extended to single-variable substitutions

  nfSVSub : ∀ {m n} → Ctx n → SVSub m n → SVSub m n
  nfSVSub      Γ  (sub a) = sub (nf Γ (⌞ a ⌟))
  nfSVSub (_ ∷ Γ) (σ ↑)   = (nfSVSub Γ σ) ↑

  nf-Hit : ∀ {m n} Γ {σ : SVSub m n} {x a} → Hit σ x a →
           Hit (nfSVSub Γ σ) x (nf Γ ⌞ a ⌟)
  nf-Hit      Γ        here                  = here
  nf-Hit (a ∷ Γ) {σ ↑} (_↑ {x = x} {b} hitP) =
    subst (Hit (nfSVSub Γ σ ↑) (suc x))
          (trans (nf-weaken a ⌞ b ⌟) (cong (nf _) (sym (⌞⌟-/Var b))))
          (nf-Hit Γ hitP ↑)

  nf-Miss : ∀ {m n} Γ {σ : SVSub m n} {x y} → Miss σ x y → Miss (nfSVSub Γ σ) x y
  nf-Miss      Γ  over      = over
  nf-Miss (a ∷ Γ) under     = under
  nf-Miss (a ∷ Γ) (missP ↑) = (nf-Miss Γ missP) ↑

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
  nfCtx-lookup : ∀ {n} (Γ : TermCtx.Ctx n) x →
                 lookup (nfCtx Γ) x ≡ nfAsc (nfCtx Γ) (TermCtx.lookup Γ x)
  nfCtx-lookup Γ x = begin
      lookup (nfCtx Γ) x
    ≡⟨ cong (flip Vec.lookup x) (nfCtx-toVec Γ) ⟩
      Vec.lookup (Vec.map (nfAsc (nfCtx Γ)) (TermCtx.toVec Γ)) x
    ≡⟨ VecProps.lookup-map x _ (TermCtx.toVec Γ) ⟩
      nfAsc (nfCtx Γ) (TermCtx.lookup Γ x)
    ∎

  -- A corollary of the above.
  nfCtx-lookup-kd : ∀ {n k} x (Γ : TermCtx.Ctx n) → TermCtx.lookup Γ x ≡ kd k →
                    lookup (nfCtx Γ) x ≡ kd (nfKind (nfCtx Γ) k)
  nfCtx-lookup-kd x Γ Γ[x]≡kd-k with TermCtx.lookup Γ x | nfCtx-lookup Γ x
  nfCtx-lookup-kd x Γ refl | kd k | nf-Γ[x]≡kd-nf-k = nf-Γ[x]≡kd-nf-k
  nfCtx-lookup-kd x Γ ()   | tp t | _
