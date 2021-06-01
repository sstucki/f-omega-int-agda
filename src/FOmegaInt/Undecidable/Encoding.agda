------------------------------------------------------------------------
-- The SKI encoding into types
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Undecidable.Encoding where

open import Data.Context.WellFormed
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Relation.Binary.PropositionalEquality hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Kinding.Canonical
open import FOmegaInt.Undecidable.SK

open Syntax
open ElimCtx
open ContextConversions using (⌞_⌟Ctx)
open RenamingCommutes
open Kinding
open ≡-Reasoning

----------------------------------------------------------------------
-- Support for the encoding: injection of shapes into kinds.

-- For every shape `k' there is a kind `⌈ k ⌉' that erases/simplifies
-- back to `k', i.e. `⌈_⌉' is a right inverse of kind erasure `⌊_⌋'.
--
-- NOTE. The definition here is almost identical to that in
-- FOmegaInt.Typing.Encodings except we inject shapes into `Kind Elim
-- n' rather than `Kind Term n'.

⌈_⌉ : ∀ {n} → SKind → Kind Elim n
⌈ ★     ⌉ = ⌜*⌝
⌈ j ⇒ k ⌉ = Π ⌈ j ⌉ ⌈ k ⌉

⌊⌋∘⌈⌉-id : ∀ {n} k → ⌊ ⌈_⌉ {n} k ⌋ ≡ k
⌊⌋∘⌈⌉-id ★       = refl
⌊⌋∘⌈⌉-id (j ⇒ k) = cong₂ _⇒_ (⌊⌋∘⌈⌉-id j) (⌊⌋∘⌈⌉-id k)

-- The kind `⌈ k ⌉' is well-formed (in any well-formed context).

⌈⌉-kd : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉ kd
⌈⌉-kd ★       Γ-ctx = kd-⌜*⌝ Γ-ctx
⌈⌉-kd (j ⇒ k) Γ-ctx =
  let ⌈j⌉-kd = ⌈⌉-kd j Γ-ctx
  in kd-Π ⌈j⌉-kd (⌈⌉-kd k (wf-kd ⌈j⌉-kd ∷ Γ-ctx))

-- Injected kinds are stable under application of substitutions.

module InjSubstAppLemmas {T : ℕ → Set} (l : Lift T Term) where
  open Lift l
  open SubstApp l

  ⌈⌉-Kind/ : ∀ {m n} k {σ : Sub T m n} → ⌈ k ⌉ Kind′/ σ ≡ ⌈ k ⌉
  ⌈⌉-Kind/ ★       = refl
  ⌈⌉-Kind/ (j ⇒ k) = cong₂ Π (⌈⌉-Kind/ j) (⌈⌉-Kind/ k)

open Substitution hiding (subst; _[_]; _↑; sub)
open TermSubst termSubst using (varLift; termLift)

open InjSubstAppLemmas varLift public renaming (⌈⌉-Kind/ to ⌈⌉-Kind/Var)

⌈⌉-weaken : ∀ {n} k → weakenKind′ {n} ⌈ k ⌉ ≡ ⌈ k ⌉
⌈⌉-weaken k = ⌈⌉-Kind/Var k

kd-⌈⌉-weaken : ∀ {n} k → weakenElimAsc {n} (kd ⌈ k ⌉) ≡ kd ⌈ k ⌉
kd-⌈⌉-weaken k = cong kd (⌈⌉-weaken k)

kd-⌈⌉-weaken⋆ : ∀ {n k} m → weakenElimAsc⋆ m {n} (kd ⌈ k ⌉) ≡ kd ⌈ k ⌉
kd-⌈⌉-weaken⋆ zero    = refl
kd-⌈⌉-weaken⋆ (suc m) =
  trans (cong weakenElimAsc (kd-⌈⌉-weaken⋆ m)) (kd-⌈⌉-weaken _)

lookup-raise-* : ∀ {n m} {Γ : Ctx n} (E : CtxExt n m) {x} k →
                 lookup Γ x ≡ kd ⌈ k ⌉ →
                 lookup (E ++ Γ) (raise m x) ≡ kd ⌈ k ⌉
lookup-raise-* {_} {m} {Γ} E {x} k hyp = begin
  lookup (E ++ Γ) (raise m x)    ≡⟨ lookup-weaken⋆ m E Γ x ⟩
  weakenElimAsc⋆ m (lookup Γ x)  ≡⟨ cong (weakenElimAsc⋆ m) hyp ⟩
  weakenElimAsc⋆ m (kd ⌈ k ⌉)    ≡⟨ kd-⌈⌉-weaken⋆ m ⟩
  kd ⌈ k ⌉                       ∎


------------------------------------------------------------------------
-- Encoding of SK terms into types

-- The encoding uses 7 type variables:
--
--  2 nullary operators encoding the combinators S and K,
--  1 binary operator encoding application,
--  2 ternary operators encoding the S reduction/expansion laws,
--  2 binary operators encoding the K reduction/expansion laws.
--
-- We define some pattern synonyms for readability of definitions.

|Γ| = 7

pattern x₀ = zero
pattern x₁ = suc zero
pattern x₂ = suc (suc zero)
pattern x₃ = suc (suc (suc zero))
pattern x₄ = suc (suc (suc (suc zero)))
pattern x₅ = suc (suc (suc (suc (suc zero))))
pattern x₆ = suc (suc (suc (suc (suc (suc zero)))))

module _ {n} where

  -- Shorthands to help with the encodings

  v₀ : Elim (1 + n)
  v₀ = var∙ x₀

  v₁ : Elim (2 + n)
  v₁ = var∙ x₁

  v₂ : Elim (3 + n)
  v₂ = var∙ x₂

module EncodingWeakened {n} m where

  -- NOTE. Here we assume (m + 3) variables in context, with the names
  -- of S, K and App being the first three.

  infixl 9 _⊛_

  encS : Elim (m + (3 + n))
  encS = var∙ (raise m x₂)

  encK : Elim (m + (3 + n))
  encK = var∙ (raise m x₁)

  _⊛_ : (a b : Elim (m + (3 + n))) → Elim (m + (3 + n))
  a ⊛ b = var (raise m x₀) ∙ (a ∷ b ∷ [])

  -- Encoding of SK terms into raw types with (m + 3) free variables.

  encode : SKTerm → Elim (m + (3 + n))
  encode S       = encS
  encode K       = encK
  encode (s · t) = (encode s) ⊛ (encode t)

module Encoding = EncodingWeakened {0} 4

module _ {n} where

  -- Operator kinds for combinator terms.

  kdS : Kind Elim (0 + n)
  kdS = ⌜*⌝

  kdK : Kind Elim (1 + n)
  kdK = ⌜*⌝

  kdApp : Kind Elim (2 + n)
  kdApp = Π ⌜*⌝ (Π ⌜*⌝ ⌜*⌝)

  -- Operator kinds reduction/expansion laws.

  kdSRed : Kind Elim (3 + n)
  kdSRed = Π ⌜*⌝ (Π ⌜*⌝ (Π ⌜*⌝
    (encS ⊛ v₂ ⊛ v₁ ⊛ v₀ ⋯ v₂ ⊛ v₀ ⊛ (v₁ ⊛ v₀))))
    where open EncodingWeakened (3 + 0)

  kdKRed : Kind Elim (4 + n)
  kdKRed = Π ⌜*⌝ (Π ⌜*⌝
    (encK ⊛ v₁ ⊛ v₀ ⋯ v₁))
    where open EncodingWeakened (2 + 1)

  kdSExp : Kind Elim (5 + n)
  kdSExp = Π ⌜*⌝ (Π ⌜*⌝ (Π ⌜*⌝
    (v₂ ⊛ v₀ ⊛ (v₁ ⊛ v₀) ⋯ encS ⊛ v₂ ⊛ v₁ ⊛ v₀)))
    where open EncodingWeakened (3 + 2)

  kdKExp : Kind Elim (6 + n)
  kdKExp = Π ⌜*⌝ (Π ⌜*⌝
    (v₁ ⋯ encK ⊛ v₁ ⊛ v₀))
    where open EncodingWeakened (2 + 3)

-- The context for the SK encoding (aka the signature)

Γ-SK : Ctx 3
Γ-SK = kd kdApp ∷ kd kdK ∷ kd kdS ∷ []

Γ-SK? : Ctx |Γ|
Γ-SK? = kd kdKExp ∷ kd kdSExp ∷ kd kdKRed ∷ kd kdSRed ∷ Γ-SK

⌞Γ-SK?⌟ : TermCtx.Ctx |Γ|
⌞Γ-SK?⌟ = ⌞ Γ-SK? ⌟Ctx

module _ where
  open Encoding
  private Γ-nf = nfCtx ⌞Γ-SK?⌟

  -- Encoded SK terms are in normal form.

  nf-encode : ∀ t → nf Γ-nf ⌞ encode t ⌟ ≡ encode t
  nf-encode S       = refl
  nf-encode K       = refl
  nf-encode (s · t) =
    cong₂ _⊛_ (begin
        weakenElim (nf Γ-nf ⌞ encode s ⌟) /⟨ ★ ⟩ sub (nf Γ-nf ⌞ encode t ⌟)
      ≡⟨ /Var-wk-↑⋆-hsub-vanishes 0 (nf Γ-nf ⌞ encode s ⌟) ⟩
        nf Γ-nf ⌞ encode s ⌟
      ≡⟨ nf-encode s ⟩
        encode s
      ∎) (nf-encode t)


------------------------------------------------------------------------
-- Canonical operator kinding of encodings

module KindedEncodingWeakened {m} (E : CtxExt 3 m)
                              (Γ-ctx : E ++ Γ-SK ctx) where

  open EncodingWeakened {0} m

  private Γ = E ++ Γ-SK


  -- Kinded encodings of the SK terms

  Ne∈-S : Γ ⊢Ne encS ∈ ⌜*⌝
  Ne∈-S = ∈-∙ (⇉-var _ Γ-ctx (lookup-raise-* E ★ refl)) ⇉-[]

  Ne∈-K : Γ ⊢Ne encK ∈ ⌜*⌝
  Ne∈-K = ∈-∙ (⇉-var _ Γ-ctx (lookup-raise-* E ★ refl)) ⇉-[]

  Ne∈-⊛ : ∀ {a b} → Γ ⊢Ne a ∈ ⌜*⌝ → Γ ⊢Ne b ∈ ⌜*⌝ → Γ ⊢Ne a ⊛ b ∈ ⌜*⌝
  Ne∈-⊛ a∈* b∈* =
    ∈-∙ (⇉-var _ Γ-ctx (lookup-raise-* E (★ ⇒ ★ ⇒ ★) refl))
        (⇉-∷ (Nf⇇-ne a∈*) (kd-⌜*⌝ Γ-ctx)
             (⇉-∷ (Nf⇇-ne b∈*) (kd-⌜*⌝ Γ-ctx) ⇉-[]))

  Ne∈-encode : (t : SKTerm) → Γ ⊢Ne encode t ∈ ⌜*⌝
  Ne∈-encode S       = Ne∈-S
  Ne∈-encode K       = Ne∈-K
  Ne∈-encode (s · t) = Ne∈-⊛ (Ne∈-encode s) (Ne∈-encode t)

-- Another shorthand

Ne∈-var : ∀ {n} {Γ : Ctx n} {k} x →
          Γ ctx → lookup Γ x ≡ kd k → Γ ⊢Ne var∙ x ∈ k
Ne∈-var x Γ-ctx Γ[x]≡k = ∈-∙ (⇉-var x Γ-ctx Γ[x]≡k) ⇉-[]

-- The signatures Γ-SK and Γ-SK? are well-formed

kdS-kd : [] ⊢ kdS kd
kdS-kd = kd-⌜*⌝ []

Γ₁-ctx : kd kdS ∷ [] ctx
Γ₁-ctx = wf-kd kdS-kd ∷ []

kdK-kd : kd kdS ∷ [] ⊢ kdK kd
kdK-kd = kd-⌜*⌝ Γ₁-ctx

Γ₂-ctx : kd kdK ∷ kd kdS ∷ [] ctx
Γ₂-ctx = wf-kd kdK-kd ∷ Γ₁-ctx

kdApp-kd : kd kdK ∷ kd kdS ∷ [] ⊢ kdApp kd
kdApp-kd = kd-Π *₂-kd (kd-Π *₃-kd (kd-⌜*⌝ (wf-kd *₃-kd ∷ Γ₃-ctx′)))
  where
    *₂-kd   = kd-⌜*⌝ Γ₂-ctx
    Γ₃-ctx′ = wf-kd *₂-kd ∷ Γ₂-ctx
    *₃-kd   = kd-⌜*⌝ Γ₃-ctx′

Γ-SK-ctx : Γ-SK ctx
Γ-SK-ctx = wf-kd kdApp-kd ∷ Γ₂-ctx

kdSRed-kd : Γ-SK ⊢ kdSRed kd
kdSRed-kd = kd-Π *₃-kd (kd-Π *₄-kd (kd-Π *₅-kd (kd-⋯
  (⇉-s-i (Ne∈-⊛ (Ne∈-⊛ (Ne∈-⊛ Ne∈-S (Ne∈-var x₂ Γ₆-ctx′ refl))
                       (Ne∈-var x₁ Γ₆-ctx′ refl)) (Ne∈-var x₀ Γ₆-ctx′ refl)))
  (⇉-s-i (Ne∈-⊛ (Ne∈-⊛ (Ne∈-var x₂ Γ₆-ctx′ refl) (Ne∈-var x₀ Γ₆-ctx′ refl))
                (Ne∈-⊛ (Ne∈-var x₁ Γ₆-ctx′ refl) (Ne∈-var x₀ Γ₆-ctx′ refl)))))))
  where
    *₃-kd   = kd-⌜*⌝ Γ-SK-ctx
    Γ₄-ctx′ = wf-kd *₃-kd ∷ Γ-SK-ctx
    *₄-kd   = kd-⌜*⌝ Γ₄-ctx′
    Γ₅-ctx′ = wf-kd *₄-kd ∷ Γ₄-ctx′
    *₅-kd   = kd-⌜*⌝ Γ₅-ctx′
    Γ₆-ctx′ = wf-kd *₅-kd ∷ Γ₅-ctx′

    open KindedEncodingWeakened (kd ⌜*⌝ ∷ kd ⌜*⌝ ∷ kd ⌜*⌝ ∷ []) Γ₆-ctx′

Γ₄-ctx : kd kdSRed ∷ Γ-SK ctx
Γ₄-ctx = wf-kd kdSRed-kd ∷ Γ-SK-ctx

kdKRed-kd : kd kdSRed ∷ Γ-SK ⊢ kdKRed kd
kdKRed-kd = (kd-Π *₄-kd (kd-Π *₅-kd (kd-⋯
  (⇉-s-i (Ne∈-⊛ (Ne∈-⊛ Ne∈-K (Ne∈-var x₁ Γ₆-ctx′ refl))
                (Ne∈-var x₀ Γ₆-ctx′ refl)))
  (⇉-s-i (Ne∈-var x₁ Γ₆-ctx′ refl)))))
  where
    *₄-kd   = kd-⌜*⌝ Γ₄-ctx
    Γ₅-ctx′ = wf-kd *₄-kd ∷ Γ₄-ctx
    *₅-kd   = kd-⌜*⌝ Γ₅-ctx′
    Γ₆-ctx′ = wf-kd *₅-kd ∷ Γ₅-ctx′

    open KindedEncodingWeakened (kd ⌜*⌝ ∷ kd ⌜*⌝ ∷ kd kdSRed ∷ []) Γ₆-ctx′

Γ₅-ctx : kd kdKRed ∷ kd kdSRed ∷ Γ-SK ctx
Γ₅-ctx = wf-kd kdKRed-kd ∷ Γ₄-ctx

kdSExp-kd : kd kdKRed ∷ kd kdSRed ∷ Γ-SK ⊢ kdSExp kd
kdSExp-kd = kd-Π *₅-kd (kd-Π *₆-kd (kd-Π *₇-kd (kd-⋯
  (⇉-s-i (Ne∈-⊛ (Ne∈-⊛ (Ne∈-var x₂ Γ₈-ctx′ refl) (Ne∈-var x₀ Γ₈-ctx′ refl))
                (Ne∈-⊛ (Ne∈-var x₁ Γ₈-ctx′ refl) (Ne∈-var x₀ Γ₈-ctx′ refl))))
  (⇉-s-i (Ne∈-⊛ (Ne∈-⊛ (Ne∈-⊛ Ne∈-S (Ne∈-var x₂ Γ₈-ctx′ refl))
                       (Ne∈-var x₁ Γ₈-ctx′ refl))
                (Ne∈-var x₀ Γ₈-ctx′ refl))))))
  where
    *₅-kd   = kd-⌜*⌝ Γ₅-ctx
    Γ₆-ctx′ = wf-kd *₅-kd ∷ Γ₅-ctx
    *₆-kd   = kd-⌜*⌝ Γ₆-ctx′
    Γ₇-ctx′ = wf-kd *₆-kd ∷ Γ₆-ctx′
    *₇-kd   = kd-⌜*⌝ Γ₇-ctx′
    Γ₈-ctx′ = wf-kd *₇-kd ∷ Γ₇-ctx′

    open KindedEncodingWeakened
      (kd ⌜*⌝ ∷ kd ⌜*⌝ ∷ kd ⌜*⌝ ∷ kd kdKRed ∷ kd kdSRed ∷ []) Γ₈-ctx′

Γ₆-ctx : kd kdSExp ∷ kd kdKRed ∷ kd kdSRed ∷ Γ-SK ctx
Γ₆-ctx = wf-kd kdSExp-kd ∷ Γ₅-ctx

kdKExp-kd : kd kdSExp ∷ kd kdKRed ∷ kd kdSRed ∷ Γ-SK ⊢ kdKExp kd
kdKExp-kd = (kd-Π *₆-kd (kd-Π *₇-kd (kd-⋯
  (⇉-s-i (Ne∈-var x₁ Γ₈-ctx′ refl))
  (⇉-s-i (Ne∈-⊛ (Ne∈-⊛ Ne∈-K (Ne∈-var x₁ Γ₈-ctx′ refl))
                (Ne∈-var x₀ Γ₈-ctx′ refl))))))
  where
    *₆-kd   = kd-⌜*⌝ Γ₆-ctx
    Γ₇-ctx′ = wf-kd *₆-kd ∷ Γ₆-ctx
    *₇-kd   = kd-⌜*⌝ Γ₇-ctx′
    Γ₈-ctx′ = wf-kd *₇-kd ∷ Γ₇-ctx′

    open KindedEncodingWeakened
      (kd ⌜*⌝ ∷ kd ⌜*⌝ ∷ kd kdSExp ∷ kd kdKRed ∷ kd kdSRed ∷ []) Γ₈-ctx′

Γ-SK?-ctx : Γ-SK? ctx
Γ-SK?-ctx = wf-kd kdKExp-kd ∷ Γ₆-ctx

module KindedEncoding =
  KindedEncodingWeakened
    (kd kdKExp ∷ kd kdSExp ∷ kd kdKRed ∷ kd kdSRed ∷ []) Γ-SK?-ctx


------------------------------------------------------------------------
-- Encoding of SK term equality in canonical subtyping

open Encoding
open KindedEncoding

-- Some helper lemmas.

wk-hsub-helper : ∀ {n} (a b c : Elim n) →
                 (weakenElim (weakenElim a) /⟨ ★ ⟩ sub b ↑) [ c ∈ ★ ] ≡ a
wk-hsub-helper a b c = begin
    (weakenElim (weakenElim a) /⟨ ★ ⟩ sub b ↑) [ c ∈ ★ ]
  ≡⟨ cong (λ a → (a /⟨ ★ ⟩ sub b ↑) [ c ∈ ★ ]) (ELV.wk-commutes a) ⟩
    (weakenElim a Elim/Var V.wk V.↑ /⟨ ★ ⟩ sub b ↑) [ c ∈ ★ ]
  ≡⟨ cong (_[ c ∈ ★ ]) (/Var-wk-↑⋆-hsub-vanishes 1 (weakenElim a)) ⟩
    weakenElim a [ c ∈ ★ ]
  ≡⟨ /Var-wk-↑⋆-hsub-vanishes 0 a ⟩
    a
  ∎
  where
    module EL  = TermLikeLemmas termLikeLemmasElim
    module ELV = LiftAppLemmas EL.varLiftAppLemmas
    module V   = VarSubst

-- Admissible kinding and subtyping rules for construction the encoded
-- SK derivations.

<:-⊛ : ∀ {a₁ a₂ b₁ b₂} → Γ-SK? ⊢ a₁ ≃ a₂ ⇇ ⌜*⌝ → Γ-SK? ⊢ b₁ ≃ b₂ ⇇ ⌜*⌝ →
       Γ-SK? ⊢ a₁ ⊛ b₁ <: a₂ ⊛ b₂
<:-⊛ a₁≃a₂ b₁≃b₂ = <:-∙ (⇉-var _ Γ-SK?-ctx refl) (≃-∷ a₁≃a₂ (≃-∷ b₁≃b₂ ≃-[]))

Ne∈-Sᵣ : ∀ {a b c} →
         Γ-SK? ⊢Ne a ∈ ⌜*⌝ → Γ-SK? ⊢Ne b ∈ ⌜*⌝ → Γ-SK? ⊢Ne c ∈ ⌜*⌝ →
         Γ-SK? ⊢Ne var x₃ ∙ (a ∷ b ∷ c ∷ []) ∈
                   encS ⊛ a ⊛ b ⊛ c ⋯ a ⊛ c ⊛ (b ⊛ c)
Ne∈-Sᵣ {a} {b} {c} a∈* b∈* c∈* =
  ∈-∙ (⇉-var _ Γ-SK?-ctx refl)
      (⇉-∷ (Nf⇇-ne a∈*) *-kd
           (⇉-∷ (Nf⇇-ne b∈*) *-kd (⇉-∷ (Nf⇇-ne c∈*) *-kd ⇉-[]′)))
  where
    *-kd = kd-⌜*⌝ Γ-SK?-ctx
    a≡⟨⟨a/wk⟩/wk⟩[b][c] = wk-hsub-helper a b c
    b≡⟨b/wk⟩[c] = /Var-wk-↑⋆-hsub-vanishes 0 b
    ⇉-[]′ =
      subst₂ (λ a′ b′ →
        Γ-SK? ⊢ encS ⊛ a′ ⊛ b′ ⊛ c ⋯ a′ ⊛ c ⊛ (b′ ⊛ c) ⇉∙ [] ⇉
                encS ⊛ a ⊛ b ⊛ c ⋯ a ⊛ c ⊛ (b ⊛ c))
        (sym a≡⟨⟨a/wk⟩/wk⟩[b][c]) (sym b≡⟨b/wk⟩[c]) ⇉-[]

<:-Sᵣ : ∀ {a b c} →
        Γ-SK? ⊢Ne a ∈ ⌜*⌝ → Γ-SK? ⊢Ne b ∈ ⌜*⌝ → Γ-SK? ⊢Ne c ∈ ⌜*⌝ →
        Γ-SK? ⊢ encS ⊛ a ⊛ b ⊛ c <: a ⊛ c ⊛ (b ⊛ c)
<:-Sᵣ a∈* b∈* c∈* =
  <:-trans (<:-⟨| (Ne∈-Sᵣ a∈* b∈* c∈*)) (<:-|⟩ (Ne∈-Sᵣ a∈* b∈* c∈*))

Ne∈-Kᵣ : ∀ {a b} → Γ-SK? ⊢Ne a ∈ ⌜*⌝ → Γ-SK? ⊢Ne b ∈ ⌜*⌝ →
         Γ-SK? ⊢Ne var x₂ ∙ (a ∷ b ∷ []) ∈ encK ⊛ a ⊛ b ⋯ a
Ne∈-Kᵣ {a} {b} a∈* b∈* =
  ∈-∙ (⇉-var _ Γ-SK?-ctx refl)
      (⇉-∷ (Nf⇇-ne a∈*) *-kd
           (⇉-∷ (Nf⇇-ne b∈*) *-kd ⇉-[]′))
  where
    *-kd  = kd-⌜*⌝ Γ-SK?-ctx
    ⇉-[]′ =
      subst (λ a′ → Γ-SK? ⊢ encK ⊛ a′ ⊛ b ⋯ a′ ⇉∙ [] ⇉ encK ⊛ a ⊛ b ⋯ a)
            (sym (/Var-wk-↑⋆-hsub-vanishes 0 a)) ⇉-[]

<:-Kᵣ : ∀ {a b} → Γ-SK? ⊢Ne a ∈ ⌜*⌝ →
        Γ-SK? ⊢Ne b ∈ ⌜*⌝ → Γ-SK? ⊢ encK ⊛ a ⊛ b <: a
<:-Kᵣ a∈* b∈* = <:-trans (<:-⟨| (Ne∈-Kᵣ a∈* b∈*)) (<:-|⟩ (Ne∈-Kᵣ a∈* b∈*))

Ne∈-Sₑ : ∀ {a b c} →
         Γ-SK? ⊢Ne a ∈ ⌜*⌝ → Γ-SK? ⊢Ne b ∈ ⌜*⌝ → Γ-SK? ⊢Ne c ∈ ⌜*⌝ →
         Γ-SK? ⊢Ne var x₁ ∙ (a ∷ b ∷ c ∷ []) ∈
                   a ⊛ c ⊛ (b ⊛ c) ⋯ encS ⊛ a ⊛ b ⊛ c
Ne∈-Sₑ {a} {b} {c} a∈* b∈* c∈* =
  ∈-∙ (⇉-var _ Γ-SK?-ctx refl)
      (⇉-∷ (Nf⇇-ne a∈*) *-kd
           (⇉-∷ (Nf⇇-ne b∈*) *-kd (⇉-∷ (Nf⇇-ne c∈*) *-kd ⇉-[]′)))
  where
    *-kd = kd-⌜*⌝ Γ-SK?-ctx
    a≡⟨⟨a/wk⟩/wk⟩[b][c] = wk-hsub-helper a b c
    b≡⟨b/wk⟩[c] = /Var-wk-↑⋆-hsub-vanishes 0 b
    ⇉-[]′ =
      subst₂ (λ a′ b′ →
        Γ-SK? ⊢ a′ ⊛ c ⊛ (b′ ⊛ c) ⋯ encS ⊛ a′ ⊛ b′ ⊛ c ⇉∙ [] ⇉
                a ⊛ c ⊛ (b ⊛ c) ⋯ encS ⊛ a ⊛ b ⊛ c)
        (sym a≡⟨⟨a/wk⟩/wk⟩[b][c]) (sym b≡⟨b/wk⟩[c]) ⇉-[]

<:-Sₑ : ∀ {a b c} →
        Γ-SK? ⊢Ne a ∈ ⌜*⌝ → Γ-SK? ⊢Ne b ∈ ⌜*⌝ → Γ-SK? ⊢Ne c ∈ ⌜*⌝ →
        Γ-SK? ⊢ a ⊛ c ⊛ (b ⊛ c) <: encS ⊛ a ⊛ b ⊛ c
<:-Sₑ a∈* b∈* c∈* =
  <:-trans (<:-⟨| (Ne∈-Sₑ a∈* b∈* c∈*)) (<:-|⟩ (Ne∈-Sₑ a∈* b∈* c∈*))

Ne∈-Kₑ : ∀ {a b} → Γ-SK? ⊢Ne a ∈ ⌜*⌝ → Γ-SK? ⊢Ne b ∈ ⌜*⌝ →
         Γ-SK? ⊢Ne var x₀ ∙ (a ∷ b ∷ []) ∈ a ⋯ encK ⊛ a ⊛ b
Ne∈-Kₑ {a} {b} a∈* b∈* =
  ∈-∙ (⇉-var _ Γ-SK?-ctx refl)
      (⇉-∷ (Nf⇇-ne a∈*) *-kd
           (⇉-∷ (Nf⇇-ne b∈*) *-kd ⇉-[]′))
  where
    *-kd  = kd-⌜*⌝ Γ-SK?-ctx
    ⇉-[]′ =
      subst (λ a′ → Γ-SK? ⊢ a′ ⋯ encK ⊛ a′ ⊛ b ⇉∙ [] ⇉ a ⋯ encK ⊛ a ⊛ b)
            (sym (/Var-wk-↑⋆-hsub-vanishes 0 a)) ⇉-[]

<:-Kₑ : ∀ {a b} → Γ-SK? ⊢Ne a ∈ ⌜*⌝ →
        Γ-SK? ⊢Ne b ∈ ⌜*⌝ → Γ-SK? ⊢ a <: encK ⊛ a ⊛ b
<:-Kₑ a∈* b∈* = <:-trans (<:-⟨| (Ne∈-Kₑ a∈* b∈*)) (<:-|⟩ (Ne∈-Kₑ a∈* b∈*))

-- Encoding of SK term equality in canonical subtyping

mutual

  <:-encode : ∀ {s t} → s ≡SK t → Γ-SK? ⊢ encode s <: encode t
  <:-encode (≡-refl {t})         = <:-reflNf⇉ (⇉-s-i (Ne∈-encode t))
  <:-encode (≡-trans s≡t t≡u)    = <:-trans (<:-encode s≡t) (<:-encode t≡u)
  <:-encode (≡-sym t≡s)          = :>-encode t≡s
  <:-encode (≡-Sred {s} {t} {u}) =
    <:-Sᵣ (Ne∈-encode s) (Ne∈-encode t) (Ne∈-encode u)
  <:-encode (≡-Kred {s} {t})     = <:-Kᵣ (Ne∈-encode s) (Ne∈-encode t)
  <:-encode (≡-· s₁≡t₁ s₂≡t₂)    = <:-⊛ (≃-encode s₁≡t₁) (≃-encode s₂≡t₂)

  :>-encode : ∀ {s t} → s ≡SK t → Γ-SK? ⊢ encode t <: encode s
  :>-encode (≡-refl {t})         = <:-reflNf⇉ (⇉-s-i (Ne∈-encode t))
  :>-encode (≡-trans s≡t t≡u)    = <:-trans (:>-encode t≡u) (:>-encode s≡t)
  :>-encode (≡-sym t≡s)          = <:-encode t≡s
  :>-encode (≡-Sred {s} {t} {u}) =
    <:-Sₑ (Ne∈-encode s) (Ne∈-encode t) (Ne∈-encode u)
  :>-encode (≡-Kred {s} {t})     = <:-Kₑ (Ne∈-encode s) (Ne∈-encode t)
  :>-encode (≡-· s₁≡t₁ s₂≡t₂)    =
    <:-⊛ (≃-sym (≃-encode s₁≡t₁)) (≃-sym (≃-encode s₂≡t₂))

  ≃-encode : ∀ {s t} → s ≡SK t → Γ-SK? ⊢ encode s ≃ encode t ⇇ ⌜*⌝
  ≃-encode {s} {t} s≡t =
    let es⇇* = Nf⇇-ne (Ne∈-encode s)
        et⇇* = Nf⇇-ne (Ne∈-encode t)
    in <:-antisym (kd-⌜*⌝ Γ-SK?-ctx)
                  (<:-⇇ es⇇* et⇇* (<:-encode s≡t))
                  (<:-⇇ et⇇* es⇇* (:>-encode s≡t))

<:⇇-encode : ∀ {s t} → s ≡SK t → Γ-SK? ⊢ encode s <: encode t ⇇ ⌜*⌝
<:⇇-encode {s} {t} s≡t =
  <:-⇇ (Nf⇇-ne (Ne∈-encode s)) (Nf⇇-ne (Ne∈-encode t)) (<:-encode s≡t)
