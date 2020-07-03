------------------------------------------------------------------------
-- Decoding types and subtypes into SK terms and equality
------------------------------------------------------------------------

{-# OPTIONS --safe --exact-split --without-K #-}

module FOmegaInt.Undecidable.Decoding where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Fin using (zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Kinding.Canonical as Canonical
open import FOmegaInt.Kinding.Canonical.Reduced as Reduced
open import FOmegaInt.Undecidable.SK
open import FOmegaInt.Undecidable.Encoding

open Syntax
open ElimCtx
open Substitution hiding (subst)
open Canonical.Kinding using (_⊢_<:_; _⊢_<:_⇇_; <:-⇇)
open Reduced.Kinding
open Encoding
open ≡-Reasoning
module V   = VarSubst
module EL  = TermLikeLemmas Substitution.termLikeLemmasElim
module ELV = LiftAppLemmas EL.varLiftAppLemmas


------------------------------------------------------------------------
-- Decoding of types into SK? terms

decode : Elim |Γ| → SK?Term
decode (var x₀ ∙ (a ∷ b ∷ _))     = K · (decode a) · (decode b)
decode (var x₁ ∙ (a ∷ b ∷ c ∷ _)) = S · (decode a) · (decode b) · (decode c)
decode (var x₂ ∙ (a ∷ b ∷ _))     = K · (decode a) · (decode b)
decode (var x₃ ∙ (a ∷ b ∷ c ∷ _)) = S · (decode a) · (decode b) · (decode c)
decode (var x₄ ∙ (a ∷ b ∷ _))     = decode a · decode b
decode (var x₅ ∙ _)               = K
decode (var x₆ ∙ _)               = S
decode (⊥ ∙ _)                    = ⊥
decode (⊤ ∙ _)                    = ⊤
{-# CATCHALL #-}
decode _ = ⊤

-- Decoding is the left-inverse of encoding.
--
-- NOTE. We encode SK terms but decode to SK? terms, so decoding is
-- strictly speaking only left-inverse when restricted to (pure) SK
-- terms.  Hence the use of `inject' here.

decode-encode : ∀ t → decode (encode t) ≡ inject t
decode-encode S       = refl
decode-encode K       = refl
decode-encode (s · t) = cong₂ _·_ (decode-encode s) (decode-encode t)

-- Decoding subsumes squashing

decode-squash : ∀ (a : Elim |Γ|) → decode (squashElim a) ≡ decode a
decode-squash (var x₀ ∙ [])              = refl   -- degenerate case
decode-squash (var x₀ ∙ (_ ∷ []))        = refl   -- degenerate case
decode-squash (var x₀ ∙ (a ∷ b ∷ _))     =
  cong₂ (λ a b → K · a · b) (decode-squash a) (decode-squash b)
decode-squash (var x₁ ∙ [])              = refl   -- degenerate case
decode-squash (var x₁ ∙ (_ ∷ []))        = refl   -- degenerate case
decode-squash (var x₁ ∙ (_ ∷ _ ∷ []))    = refl   -- degenerate case
decode-squash (var x₁ ∙ (a ∷ b ∷ c ∷ _)) =
  trans (cong (S · _ · _ ·_) (decode-squash c))
        (cong₂ (λ a b → S · a · b · _) (decode-squash a) (decode-squash b))
decode-squash (var x₂ ∙ [])              = refl   -- degenerate case
decode-squash (var x₂ ∙ (_ ∷ []))        = refl   -- degenerate case
decode-squash (var x₂ ∙ (a ∷ b ∷ _))     =
  cong₂ (λ a b → K · a · b) (decode-squash a) (decode-squash b)
decode-squash (var x₃ ∙ [])              = refl   -- degenerate case
decode-squash (var x₃ ∙ (_ ∷ []))        = refl   -- degenerate case
decode-squash (var x₃ ∙ (_ ∷ _ ∷ []))    = refl   -- degenerate case
decode-squash (var x₃ ∙ (a ∷ b ∷ c ∷ _)) =
  trans (cong (S · _ · _ ·_) (decode-squash c))
        (cong₂ (λ a b → S · a · b · _) (decode-squash a) (decode-squash b))
decode-squash (var x₄ ∙ [])              = refl   -- degenerate case
decode-squash (var x₄ ∙ (_ ∷ []))        = refl   -- degenerate case
decode-squash (var x₄ ∙ (a ∷ b ∷ _))     =
  cong₂ _·_ (decode-squash a) (decode-squash b)
decode-squash (var x₅ ∙ as) = refl
decode-squash (var x₆ ∙ as) = refl
decode-squash (⊥ ∙ as)      = refl
decode-squash (⊤ ∙ as)      = refl
-- squashed cases
decode-squash (Π k a   ∙ as) = refl
decode-squash ((a ⇒ b) ∙ as) = refl
decode-squash (Λ k a   ∙ as) = refl
decode-squash (ƛ a b   ∙ as) = refl
decode-squash (a ⊡ b   ∙ as) = refl

-- Helper lemmas to be used when decoding kinding derivations.

⌜⌝-⌞⌟-∙∙ : ∀ {n} (a : Elim n) → ⌜ ⌞ a ⌟ ⌝ ∙∙ [] ≡ a
⌜⌝-⌞⌟-∙∙ a = begin
  ⌜ ⌞ a ⌟ ⌝ ∙∙ []  ≡⟨ ∙∙-[] ⌜ ⌞ a ⌟ ⌝ ⟩
  ⌜ ⌞ a ⌟ ⌝        ≡⟨ ⌜⌝∘⌞⌟-id a ⟩
  a                ∎

⌜⌝-⌞⌟-weaken-sub₁ : ∀ {n} (a b : Elim n) →
                    (⌜ weaken ⌞ a ⌟ ⌝ ∙∙ []) Elim[ ⌞ b ⌟ ] ≡ a
⌜⌝-⌞⌟-weaken-sub₁ a b = begin
    (⌜ weaken ⌞ a ⌟ ⌝ ∙∙ []) Elim[ ⌞ b ⌟ ]
  ≡˘⟨ cong (λ a → (⌜ a ⌝ ∙∙ []) Elim[ ⌞ b ⌟ ]) (⌞⌟-/Var a) ⟩
    (⌜ ⌞ weakenElim a ⌟ ⌝ ∙∙ []) Elim[ ⌞ b ⌟ ]
  ≡⟨ cong (_Elim[ ⌞ b ⌟ ]) (⌜⌝-⌞⌟-∙∙ (weakenElim a)) ⟩
    weakenElim a Elim[ ⌞ b ⌟ ]
  ≡⟨ EL.weaken-sub a ⟩
    a
  ∎

⌜⌝-⌞⌟-weaken-sub₂ : ∀ {n} (a b c : Elim n) →
  ((⌜ weaken (weaken ⌞ a ⌟) ⌝ ∙∙ []) Elim/ sub ⌞ b ⌟ ↑) Elim[ ⌞ c ⌟ ] ≡ a
⌜⌝-⌞⌟-weaken-sub₂ a b c = begin
    ((⌜ weaken (weaken ⌞ a ⌟) ⌝ ∙∙ []) Elim/ sub ⌞ b ⌟ ↑) Elim[ ⌞ c ⌟ ]
  ≡˘⟨ cong (λ a → ((⌜ a ⌝ ∙∙ []) Elim/ sub ⌞ b ⌟ ↑) Elim[ ⌞ c ⌟ ])
           (trans (⌞⌟-/Var (weakenElim a)) (cong weaken (⌞⌟-/Var a))) ⟩
    ((⌜ ⌞ weakenElim (weakenElim a) ⌟ ⌝ ∙∙ []) Elim/ sub ⌞ b ⌟ ↑) Elim[ ⌞ c ⌟ ]
  ≡⟨ cong (λ a → (a Elim/ sub ⌞ b ⌟ ↑) Elim[ ⌞ c ⌟ ])
          (⌜⌝-⌞⌟-∙∙ (weakenElim (weakenElim a))) ⟩
    (weakenElim (weakenElim a) Elim/ sub ⌞ b ⌟ ↑) Elim[ ⌞ c ⌟ ]
  ≡⟨ cong (_Elim[ ⌞ c ⌟ ]) (sym (EL.weaken-/ (weakenElim a))) ⟩
    weakenElim (weakenElim a Elim/ sub ⌞ b ⌟) Elim[ ⌞ c ⌟ ]
  ≡⟨ cong ((_Elim[ ⌞ c ⌟ ]) ∘ weakenElim) (EL.weaken-sub a) ⟩
    weakenElim a Elim[ ⌞ c ⌟ ]
  ≡⟨ EL.weaken-sub a ⟩
    a
  ∎

-- Decoding of (reduced) canonical type order into the SK? term order.

mutual

  decode-∼ : ∀ {a b} → Γ-SK? ⊢ a ∼ b → decode a ≤SK? decode b
  decode-∼ (∼-trans a∼b b∼c) = ≤?-trans (decode-∼ a∼b) (decode-∼ b∼c)
  decode-∼ (∼-⊥ b⇉b⋯b)       = ≤?-⊥
  decode-∼ (∼-⊤ a⇉a⋯a)       = ≤?-⊤
  decode-∼ (∼-∙ (⇉-var x₀ _ refl) (∼-∷ _ _ a₁∼b₁ (∼-∷ _ _ a₂∼b₂ ∼-[]))) =
    ≤?-· (≤?-· ≤?-refl (decode-∼ a₁∼b₁)) (decode-∼ a₂∼b₂)
  decode-∼ (∼-∙ (⇉-var x₁ _ refl)
           (∼-∷ _ _ a₁∼b₁ (∼-∷ _ _ a₂∼b₂ (∼-∷ _ _ a₃∼b₃ ∼-[])))) =
    ≤?-· (≤?-· (≤?-· ≤?-refl (decode-∼ a₁∼b₁)) (decode-∼ a₂∼b₂))
         (decode-∼ a₃∼b₃)
  decode-∼ (∼-∙ (⇉-var x₂ _ refl) (∼-∷ _ _ a₁∼b₁ (∼-∷ _ _ a₂∼b₂ ∼-[]))) =
    ≤?-· (≤?-· ≤?-refl (decode-∼ a₁∼b₁)) (decode-∼ a₂∼b₂)
  decode-∼ (∼-∙ (⇉-var x₃ _ refl)
           (∼-∷ _ _ a₁∼b₁ (∼-∷ _ _ a₂∼b₂ (∼-∷ _ _ a₃∼b₃ ∼-[])))) =
    ≤?-· (≤?-· (≤?-· ≤?-refl (decode-∼ a₁∼b₁)) (decode-∼ a₂∼b₂))
         (decode-∼ a₃∼b₃)
  decode-∼ (∼-∙ (⇉-var x₄ _ refl) (∼-∷ _ _ a₁∼b₁ (∼-∷ _ _ a₂∼b₂ ∼-[]))) =
    ≤?-· (decode-∼ a₁∼b₁) (decode-∼ a₂∼b₂)
  decode-∼ (∼-∙ (⇉-var x₅ _ refl) ∼-[]) = ≤?-refl
  decode-∼ (∼-∙ (⇉-var x₆ _ refl) ∼-[]) = ≤?-refl
  decode-∼ (∼-⟨| a⇉b⋯c) = proj₁ (decode-Ne⇉ a⇉b⋯c)
  decode-∼ (∼-|⟩ a⇉b⋯c) = proj₂ (decode-Ne⇉ a⇉b⋯c)

  decode-Ne⇉ : ∀ {a b c} → Γ-SK? ⊢Ne a ⇉ b ⋯ c →
               decode b ≤SK? decode a × decode a ≤SK? decode c
  decode-Ne⇉ (⇉-∙ (⇉-var x₀ _ refl) (⇉-∷ {a} a∈* (⇉-∷ {b} b∈* ⇉-[]))) =
    subst (λ a′ → decode a′ ≤SK? K · (decode a) · (decode b))
          (sym (⌜⌝-⌞⌟-weaken-sub₁ a b)) ≤?-Kexp ,
    subst₂ (λ a′ b′ → K · decode a  · decode b ≤SK?
                      K · decode a′ · decode b′)
           (sym (⌜⌝-⌞⌟-weaken-sub₁ a b)) (sym (⌜⌝-⌞⌟-∙∙ b)) ≤?-refl
  decode-Ne⇉ (⇉-∙ (⇉-var x₁ _ refl)
                  (⇉-∷ {a} a∈* (⇉-∷ {b} b∈* (⇉-∷ {c} c∈* ⇉-[])))) =
    subst₂ (λ a′ b′ → decode a′ · decode c′ · (decode b′ · decode c′) ≤SK?
                      S · decode a · decode b · decode c)
      (sym (⌜⌝-⌞⌟-weaken-sub₂ a b c)) (sym (⌜⌝-⌞⌟-weaken-sub₁ b c))
      (subst (λ c′ → decode a · decode c′ · (decode b · decode c′) ≤SK?
                     S · decode a · decode b · decode c)
        (sym (⌜⌝-⌞⌟-∙∙ c)) ≤?-Sexp) ,
    subst₂ (λ a′ b′ → S · decode a  · decode b  · decode c ≤SK?
                      S · decode a′ · decode b′ · decode c′)
      (sym (⌜⌝-⌞⌟-weaken-sub₂ a b c)) (sym (⌜⌝-⌞⌟-weaken-sub₁ b c))
      (subst (λ c′ → S · decode a · decode b · decode c ≤SK?
                     S · decode a · decode b · decode c′)
        (sym (⌜⌝-⌞⌟-∙∙ c)) ≤?-refl)
    where c′ = ⌜ ⌞ c ⌟ ⌝ ∙∙ []
  decode-Ne⇉ (⇉-∙ (⇉-var x₂ _ refl) (⇉-∷ {a} a∈* (⇉-∷ {b} b∈* ⇉-[]))) =
    subst₂ (λ a′ b′ → K · decode a′ · decode b′ ≤SK?
                      K · decode a  · decode b)
           (sym (⌜⌝-⌞⌟-weaken-sub₁ a b)) (sym (⌜⌝-⌞⌟-∙∙ b)) ≤?-refl ,
    subst (λ a′ → K · decode a · decode b ≤SK? decode a′)
          (sym (⌜⌝-⌞⌟-weaken-sub₁ a b)) ≤?-Kred
  decode-Ne⇉ (⇉-∙ (⇉-var x₃ _ refl)
             (⇉-∷ {a} a∈* (⇉-∷ {b} b∈* (⇉-∷ {c} c∈* ⇉-[])))) =
    subst₂ (λ a′ b′ → S · decode a′ · decode b′ · decode c′ ≤SK?
                      S · decode a  · decode b  · decode c)
      (sym (⌜⌝-⌞⌟-weaken-sub₂ a b c)) (sym (⌜⌝-⌞⌟-weaken-sub₁ b c))
      (subst (λ c′ → S · decode a · decode b · decode c′ ≤SK?
                     S · decode a · decode b · decode c)
        (sym (⌜⌝-⌞⌟-∙∙ c)) ≤?-refl) ,
    subst₂ (λ a′ b′ → S · decode a · decode b · decode c ≤SK?
                      decode a′ · decode c′ · (decode b′ · decode c′))
      (sym (⌜⌝-⌞⌟-weaken-sub₂ a b c)) (sym (⌜⌝-⌞⌟-weaken-sub₁ b c))
      (subst (λ c′ → S · decode a · decode b · decode c ≤SK?
                     decode a · decode c′ · (decode b · decode c′))
        (sym (⌜⌝-⌞⌟-∙∙ c)) ≤?-Sred)
    where c′ = ⌜ ⌞ c ⌟ ⌝ ∙∙ []
  decode-Ne⇉ (⇉-∙ (⇉-var x₄ _ refl) (⇉-∷ a∈* (⇉-∷ b∈* ⇉-[]))) = ≤?-⊥ , ≤?-⊤
  decode-Ne⇉ (⇉-∙ (⇉-var x₅ _ refl) ⇉-[]) = ≤?-⊥ , ≤?-⊤
  decode-Ne⇉ (⇉-∙ (⇉-var x₆ _ refl) ⇉-[]) = ≤?-⊥ , ≤?-⊤

-- The SK? signature is a first-order context.

kdS-fo : FOKind (kdS {0})
kdS-fo = fo-⋯

kdK-fo : FOKind (kdK {0})
kdK-fo = fo-⋯

kdApp-fo : FOKind (kdApp {0})
kdApp-fo = fo-Π (fo-Π fo-⋯)

kdSRed-fo : FOKind (kdSRed {0})
kdSRed-fo = fo-Π (fo-Π (fo-Π fo-⋯))

kdKRed-fo : FOKind (kdKRed {0})
kdKRed-fo = fo-Π (fo-Π fo-⋯)

kdSExp-fo : FOKind (kdSExp {0})
kdSExp-fo = fo-Π (fo-Π (fo-Π fo-⋯))

kdKExp-fo : FOKind (kdKExp {0})
kdKExp-fo = fo-Π (fo-Π fo-⋯)

Γ-SK?-fo : FOCtx Γ-SK?
Γ-SK?-fo =
  fo-∷ (fo-kd kdKExp-fo)
       (fo-∷ (fo-kd kdSExp-fo)
             (fo-∷ (fo-kd kdKRed-fo)
                   (fo-∷ (fo-kd kdSRed-fo)
                         (fo-∷ (fo-kd kdApp-fo)
                               (fo-∷ (fo-kd kdK-fo)
                                     (fo-∷ (fo-kd kdS-fo) fo-[]))))))

-- Decoding of canonical subtyping into the SK? term order.

decode-<: : ∀ {a b} → Γ-SK? ⊢ a <: b → decode a ≤SK? decode b
decode-<: {a} {b} a<:b =
  subst₂ (_≤SK?_) (decode-squash a) (decode-squash b)
         (decode-∼ (reduce-<: Γ-SK?-fo a<:b))

decode-<:⇇ : ∀ {a b} → Γ-SK? ⊢ a <: b ⇇ ⌜*⌝ → decode a ≤SK? decode b
decode-<:⇇ {a} {b} (<:-⇇ _ _ a<:b) = decode-<: a<:b

-- Full decoding to SK term equality.

decode-<:⇇-encode : ∀ {s t} → Γ-SK? ⊢ encode s <: encode t ⇇ ⌜*⌝ → s ≡SK t
decode-<:⇇-encode {s} {t} es<:et⇇* =
  inject-≤SK?-≡SK (subst₂ (_≤SK?_) (decode-encode s) (decode-encode t)
                          (decode-<:⇇ es<:et⇇*))

