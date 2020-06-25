------------------------------------------------------------------------
-- Untyped hereditary substitution in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --exact-split --without-K #-}

module FOmegaInt.Syntax.HereditarySubstitution where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)
open import Relation.Binary.PropositionalEquality as P hiding ([_])

open import FOmegaInt.Reduction.Full
open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution

open Syntax


----------------------------------------------------------------------
-- Untyped hereditary substitution.

infixl 9 _?∙∙⟨_⟩_ _∙∙⟨_⟩_ _⌜·⌝⟨_⟩_ _↓⌜·⌝_
infixl 8 _/⟨_⟩_ _//⟨_⟩_ _Kind/⟨_⟩_ _Asc/⟨_⟩_

-- TODO: explain why there are degenerate cases.
mutual

  -- Apply a herediary substition to an elimination, kind or spine.

  _/⟨_⟩_ : ∀ {m n} → Elim m → SKind → SVSub m n → Elim n
  var x   ∙ as /⟨ k ⟩ σ = lookupSV σ x ?∙∙⟨ k ⟩ (as //⟨ k ⟩ σ)
  ⊥       ∙ as /⟨ k ⟩ σ = ⊥ ∙ (as //⟨ k ⟩ σ)
  ⊤       ∙ as /⟨ k ⟩ σ = ⊤ ∙ (as //⟨ k ⟩ σ)
  Π j a   ∙ as /⟨ k ⟩ σ = Π (j Kind/⟨ k ⟩ σ) (a /⟨ k ⟩ σ ↑) ∙ (as //⟨ k ⟩ σ)
  (a ⇒ b) ∙ as /⟨ k ⟩ σ = ((a /⟨ k ⟩ σ) ⇒ (b /⟨ k ⟩ σ))  ∙ (as //⟨ k ⟩ σ)
  Λ j a   ∙ as /⟨ k ⟩ σ = Λ (j Kind/⟨ k ⟩ σ) (a /⟨ k ⟩ σ ↑) ∙ (as //⟨ k ⟩ σ)
  ƛ a b   ∙ as /⟨ k ⟩ σ = ƛ (a /⟨ k ⟩ σ) (b /⟨ k ⟩ σ ↑) ∙ (as //⟨ k ⟩ σ)
  a ⊡ b   ∙ as /⟨ k ⟩ σ = (a /⟨ k ⟩ σ) ⊡ (b /⟨ k ⟩ σ)    ∙ (as //⟨ k ⟩ σ)

  _Kind/⟨_⟩_ : ∀ {m n} → Kind Elim m → SKind → SVSub m n → Kind Elim n
  (a ⋯ b) Kind/⟨ k ⟩ σ = (a /⟨ k ⟩ σ) ⋯ (b /⟨ k ⟩ σ)
  Π j₁ j₂   Kind/⟨ k ⟩ σ = Π (j₁ Kind/⟨ k ⟩ σ) (j₂ Kind/⟨ k ⟩ σ ↑)

  _//⟨_⟩_ : ∀ {m n} → Spine m → SKind → SVSub m n → Spine n
  []       //⟨ k ⟩ σ = []
  (a ∷ as) //⟨ k ⟩ σ = a /⟨ k ⟩ σ ∷ as //⟨ k ⟩ σ

  -- Apply a lookup-result to a spine, performing β-reduction if possible.

  _?∙∙⟨_⟩_ : ∀ {n} → SVRes n → SKind → Spine n → Elim n
  hit a  ?∙∙⟨ k ⟩ as = a  ∙∙⟨ k ⟩ as
  miss y ?∙∙⟨ k ⟩ as = var y ∙ as

  -- Apply an elimination to a spine, performing β-reduction if possible.
  --
  -- NOTE.  Degenerate cases are marked "!".

  _∙∙⟨_⟩_ : ∀ {n} → Elim n → SKind → Spine n → Elim n
  a ∙∙⟨ k ⟩     []       = a
  a ∙∙⟨ ★ ⟩     (b ∷ bs) = a ∙∙ (b ∷ bs)               -- ! a ill-kinded
  a ∙∙⟨ j ⇒ k ⟩ (b ∷ bs) = a ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs

  -- Apply one elimination to another, performing β-reduction if possible.
  --
  -- NOTE.  Degenerate cases are marked "!".

  _⌜·⌝⟨_⟩_ : ∀ {n} → Elim n → SKind → Elim n → Elim n
  a              ⌜·⌝⟨ ★ ⟩     b = a ⌜·⌝ b              -- ! a ill-kinded
  (a ∙ (c ∷ cs)) ⌜·⌝⟨ j ⇒ k ⟩ b = a ∙ (c ∷ cs) ⌜·⌝ b   -- ! unless a = var x
  (Λ l a ∙ [])   ⌜·⌝⟨ j ⇒ k ⟩ b = a /⟨ j ⟩ (sub b)
  {-# CATCHALL #-}
  (a ∙ [])       ⌜·⌝⟨ j ⇒ k ⟩ b = a ∙ (b ∷ [])         -- ! unless a = var x

-- Apply a herediary substition to a kind or type ascription.

_Asc/⟨_⟩_ : ∀ {m n} → ElimAsc m → SKind → SVSub m n → ElimAsc n
kd j Asc/⟨ k ⟩ σ = kd (j Kind/⟨ k ⟩ σ)
tp a Asc/⟨ k ⟩ σ = tp (a /⟨ k ⟩ σ)

-- Some shorthands.

_[_∈_] : ∀ {n} → Elim (suc n) → Elim n → SKind → Elim n
a [ b ∈ k ] = a /⟨ k ⟩ sub b

_Kind[_∈_] : ∀ {n} → Kind Elim (suc n) → Elim n → SKind → Kind Elim n
j Kind[ a ∈ k ] = j Kind/⟨ k ⟩ sub a

-- A variant of application that is reducing (only) if the first
-- argument is a type abstraction.

_↓⌜·⌝_ : ∀ {n} → Elim n → Elim n → Elim n
(a ∙ (b ∷ bs)) ↓⌜·⌝ c = (a ∙ (b ∷ bs)) ⌜·⌝ c
(Λ k a ∙ [])   ↓⌜·⌝ b = a [ b ∈ ⌊ k ⌋ ]
{-# CATCHALL #-}
(a ∙ [])       ↓⌜·⌝ b = a ∙ (b ∷ [])


----------------------------------------------------------------------
-- Properties of (untyped) hereditary substitution.

-- Some exact lemmas about hereditary substitutions (up to
-- α-equality).

module _ where
  open SimpleCtx using (⌊_⌋Asc; kd; tp)

  -- Simplified kinds are stable under application of hereditary
  -- substitutions.

  ⌊⌋-Kind/⟨⟩ : ∀ {m n} (j : Kind Elim m) {k} {σ : SVSub m n} →
              ⌊ j Kind/⟨ k ⟩ σ ⌋ ≡ ⌊ j ⌋
  ⌊⌋-Kind/⟨⟩ (a ⋯ b) = refl
  ⌊⌋-Kind/⟨⟩ (Π j k) = cong₂ _⇒_ (⌊⌋-Kind/⟨⟩ j) (⌊⌋-Kind/⟨⟩ k)

  ⌊⌋-Asc/⟨⟩ : ∀ {m n} (a : ElimAsc m) {k} {σ : SVSub m n} →
             ⌊ a Asc/⟨ k ⟩ σ ⌋Asc ≡ ⌊ a ⌋Asc
  ⌊⌋-Asc/⟨⟩ (kd k) = cong kd (⌊⌋-Kind/⟨⟩ k)
  ⌊⌋-Asc/⟨⟩ (tp a) = refl

  -- Hereditary substitutions in spines commute with concatenation.

  ++-//⟨⟩ : ∀ {k m n} (as bs : Spine m) {σ : SVSub m n} →
            (as ++ bs) //⟨ k ⟩ σ ≡ as //⟨ k ⟩ σ ++ bs //⟨ k ⟩ σ
  ++-//⟨⟩ []       bs     = refl
  ++-//⟨⟩ (a ∷ as) bs {σ} = cong (a /⟨ _ ⟩ σ ∷_) (++-//⟨⟩ as bs)

  open Substitution using (_Elim/_; _Kind′/_; _//_)

  -- Hereditary substitutions and reducing applications at ★
  -- degenerate to ordinary substitutions and applications.

  mutual

    /⟨★⟩-/ : ∀ {m n} (a : Elim m) {σ : SVSub m n} →
             a /⟨ ★ ⟩ σ ≡ a Elim/ toSub σ
    /⟨★⟩-/ (var x   ∙ as) {σ} = begin
        lookupSV σ x ?∙∙⟨ ★ ⟩ (as //⟨ ★ ⟩ σ)
      ≡⟨ ?∙∙⟨★⟩-∙∙ (lookupSV σ x) ⟩
        toElim (lookupSV σ x) ∙∙ (as //⟨ ★ ⟩ σ)
      ≡⟨ cong₂ _∙∙_ (sym (⌜⌝∘⌞⌟-id _)) (//⟨★⟩-// as) ⟩
        ⌜ ⌞ toElim (lookupSV σ x) ⌟ ⌝ ∙∙ (as // toSub σ)
      ≡˘⟨ cong (_∙∙ _) (cong ⌜_⌝ (lookup-toSub σ x)) ⟩
        var x ∙ as Elim/ toSub σ
      ∎
      where open ≡-Reasoning
    /⟨★⟩-/ (⊥       ∙ as) = cong (⊥ ∙_) (//⟨★⟩-// as)
    /⟨★⟩-/ (⊤       ∙ as) = cong (⊤ ∙_) (//⟨★⟩-// as)
    /⟨★⟩-/ (Π k b   ∙ as) =
      cong₂ _∙_ (cong₂ Π (Kind/⟨★⟩-/ k) (/⟨★⟩-/ b)) (//⟨★⟩-// as)
    /⟨★⟩-/ ((b ⇒ c) ∙ as) =
      cong₂ _∙_ (cong₂ _⇒_ (/⟨★⟩-/ b) (/⟨★⟩-/ c)) (//⟨★⟩-// as)
    /⟨★⟩-/ (Λ k b   ∙ as) =
      cong₂ _∙_ (cong₂ Λ (Kind/⟨★⟩-/ k) (/⟨★⟩-/ b)) (//⟨★⟩-// as)
    /⟨★⟩-/ (ƛ b c   ∙ as) =
      cong₂ _∙_ (cong₂ ƛ (/⟨★⟩-/ b) (/⟨★⟩-/ c)) (//⟨★⟩-// as)
    /⟨★⟩-/ (b ⊡ c   ∙ as) =
      cong₂ _∙_ (cong₂ _⊡_ (/⟨★⟩-/ b) (/⟨★⟩-/ c)) (//⟨★⟩-// as)

    //⟨★⟩-// : ∀ {m n} (as : Spine m) {σ : SVSub m n} →
               as //⟨ ★ ⟩ σ ≡ as // toSub σ
    //⟨★⟩-// []       = refl
    //⟨★⟩-// (a ∷ as) = cong₂ _∷_ (/⟨★⟩-/ a) (//⟨★⟩-// as)

    Kind/⟨★⟩-/ : ∀ {m n} (k : Kind Elim m) {σ : SVSub m n} →
                 k Kind/⟨ ★ ⟩ σ ≡ k Kind′/ toSub σ
    Kind/⟨★⟩-/ (a ⋯ b) = cong₂ _⋯_ (/⟨★⟩-/ a) (/⟨★⟩-/ b)
    Kind/⟨★⟩-/ (Π j k) = cong₂ Π (Kind/⟨★⟩-/ j) (Kind/⟨★⟩-/ k)

    ?∙∙⟨★⟩-∙∙ : ∀ {n} (r : SVRes n) {as} → r ?∙∙⟨ ★ ⟩ as ≡ toElim r ∙∙ as
    ?∙∙⟨★⟩-∙∙ (hit a)  = ∙∙⟨★⟩-∙∙ a
    ?∙∙⟨★⟩-∙∙ (miss y) = refl

    ∙∙⟨★⟩-∙∙ : ∀ {n} (a : Elim n) {bs} → a ∙∙⟨ ★ ⟩ bs ≡ a ∙∙ bs
    ∙∙⟨★⟩-∙∙ a {[]}     = sym (∙∙-[] a)
    ∙∙⟨★⟩-∙∙ a {b ∷ bs} = refl

module RenamingCommutes where
  open Substitution
    hiding (_↑; _↑⋆_; sub; _/Var_) renaming (_Elim/Var_ to _/Var_)
  open P.≡-Reasoning
  private
    module S = Substitution
    module V = VarSubst

  mutual

    -- Hereditary substitution commutes with renaming.
    --
    -- NOTE: this is a variant of the `sub-commutes' lemma from
    -- Data.Fin.Substitution.Lemmas adapted to hereditary
    -- substitutions and renaming.

    /⟨⟩-/Var-↑⋆ : ∀ i {m n} a k b {ρ : Sub Fin m n} →
                  b /⟨ k ⟩ sub a ↑⋆ i /Var ρ V.↑⋆ i ≡
                    b /Var (ρ V.↑) V.↑⋆ i /⟨ k ⟩ sub (a /Var ρ) ↑⋆ i
    /⟨⟩-/Var-↑⋆ i a k (var x ∙ bs) {ρ} = begin
        var x ∙ bs /⟨ k ⟩ sub a ↑⋆ i /Var ρ V.↑⋆ i
      ≡⟨⟩
        lookupSV (sub a ↑⋆ i) x ?∙∙⟨ k ⟩ (bs //⟨ k ⟩ sub a ↑⋆ i) /Var ρ V.↑⋆ i
      ≡⟨ ?∙∙⟨⟩-/Var (lookupSV (sub a ↑⋆ i) x) k (bs //⟨ k ⟩ sub a ↑⋆ i) ⟩
        (lookupSV (sub a ↑⋆ i) x ?/Var ρ V.↑⋆ i) ?∙∙⟨ k ⟩
          (bs //⟨ k ⟩ sub a ↑⋆ i //Var ρ V.↑⋆ i)
      ≡⟨ cong₂ _?∙∙⟨ k ⟩_ (lookup-sub-/Var-↑⋆ a i x) (//⟨⟩-/Var-↑⋆ i a k bs) ⟩
        lookupSV (sub (a /Var ρ) ↑⋆ i) (x V./ (ρ V.↑) V.↑⋆ i) ?∙∙⟨ k ⟩
          (bs //Var (ρ V.↑) V.↑⋆ i //⟨ k ⟩ sub (a /Var ρ) ↑⋆ i)
      ≡⟨⟩
        var x ∙ bs /Var (ρ V.↑) V.↑⋆ i /⟨ k ⟩ sub (a /Var ρ) ↑⋆ i
      ∎
    /⟨⟩-/Var-↑⋆ i a k (⊥     ∙ bs)   = cong (⊥ ∙_) (//⟨⟩-/Var-↑⋆ i a k bs)
    /⟨⟩-/Var-↑⋆ i a k (⊤     ∙ bs)   = cong (⊤ ∙_) (//⟨⟩-/Var-↑⋆ i a k bs)
    /⟨⟩-/Var-↑⋆ i a k (Π j b ∙ bs)   =
      cong₂ _∙_ (cong₂ Π (Kind/⟨⟩-/Var-↑⋆ i a k j) (/⟨⟩-/Var-↑⋆ (suc i) a k b))
                (//⟨⟩-/Var-↑⋆ i a k bs)
    /⟨⟩-/Var-↑⋆ i a k ((b ⇒ c) ∙ bs) =
      cong₂ _∙_ (cong₂ _⇒_ (/⟨⟩-/Var-↑⋆ i a k b) (/⟨⟩-/Var-↑⋆ i a k c))
                (//⟨⟩-/Var-↑⋆ i a k bs)
    /⟨⟩-/Var-↑⋆ i a k (Λ j b ∙ bs)   =
      cong₂ _∙_ (cong₂ Λ (Kind/⟨⟩-/Var-↑⋆ i a k j) (/⟨⟩-/Var-↑⋆ (suc i) a k b))
                (//⟨⟩-/Var-↑⋆ i a k bs)
    /⟨⟩-/Var-↑⋆ i a k (ƛ b c ∙ bs)   =
      cong₂ _∙_ (cong₂ ƛ (/⟨⟩-/Var-↑⋆ i a k b) (/⟨⟩-/Var-↑⋆ (suc i) a k c))
                (//⟨⟩-/Var-↑⋆ i a k bs)
    /⟨⟩-/Var-↑⋆ i a k (b ⊡ c ∙ bs)   =
      cong₂ _∙_ (cong₂ _⊡_ (/⟨⟩-/Var-↑⋆ i a k b) (/⟨⟩-/Var-↑⋆ i a k c))
                (//⟨⟩-/Var-↑⋆ i a k bs)

    Kind/⟨⟩-/Var-↑⋆ : ∀ i {m n} a k j {ρ : Sub Fin m n} →
                      j Kind/⟨ k ⟩ sub a ↑⋆ i Kind′/Var ρ V.↑⋆ i ≡
                        j Kind′/Var (ρ V.↑) V.↑⋆ i Kind/⟨ k ⟩ sub (a /Var ρ) ↑⋆ i
    Kind/⟨⟩-/Var-↑⋆ i a k (b ⋯ c) =
      cong₂ _⋯_ (/⟨⟩-/Var-↑⋆ i a k b) (/⟨⟩-/Var-↑⋆ i a k c)
    Kind/⟨⟩-/Var-↑⋆ i a k (Π j l) =
      cong₂ Π (Kind/⟨⟩-/Var-↑⋆ i a k j) (Kind/⟨⟩-/Var-↑⋆ (suc i) a k l)

    //⟨⟩-/Var-↑⋆ : ∀ i {n m} a k bs {ρ : Sub Fin m n} →
                   bs //⟨ k ⟩ sub a ↑⋆ i //Var ρ V.↑⋆ i ≡
                     (bs //Var (ρ V.↑) V.↑⋆ i) //⟨ k ⟩ sub (a /Var ρ) ↑⋆ i
    //⟨⟩-/Var-↑⋆ i a k []       = refl
    //⟨⟩-/Var-↑⋆ i a k (b ∷ bs) =
      cong₂ _∷_ (/⟨⟩-/Var-↑⋆ i a k b) (//⟨⟩-/Var-↑⋆ i a k bs)

    -- Reducing applications commute with renaming.

    ?∙∙⟨⟩-/Var : ∀ {m n} r k bs {ρ : Sub Fin m n} →
                 r ?∙∙⟨ k ⟩ bs /Var ρ ≡ (r ?/Var ρ) ?∙∙⟨ k ⟩ (bs //Var ρ)
    ?∙∙⟨⟩-/Var (hit a)  k as = ∙∙⟨⟩-/Var a k as
    ?∙∙⟨⟩-/Var (miss y) k as = refl

    ∙∙⟨⟩-/Var : ∀ {m n} a k bs {ρ : Sub Fin m n} →
                a ∙∙⟨ k ⟩ bs /Var ρ ≡ (a /Var ρ) ∙∙⟨ k ⟩ (bs //Var ρ)
    ∙∙⟨⟩-/Var a k       []           = refl
    ∙∙⟨⟩-/Var a ★       (b ∷ bs)     = S.∙∙-/Var a (b ∷ bs)
    ∙∙⟨⟩-/Var a (j ⇒ k) (b ∷ bs) {ρ} = begin
        a ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs /Var ρ
      ≡⟨ ∙∙⟨⟩-/Var (a ⌜·⌝⟨ j ⇒ k ⟩ b) k bs ⟩
        (a ⌜·⌝⟨ j ⇒ k ⟩ b /Var ρ) ∙∙⟨ k ⟩ (bs //Var ρ)
      ≡⟨ cong (_∙∙⟨ k ⟩ (bs //Var ρ)) (⌜·⌝⟨⟩-/Var a (j ⇒ k) b) ⟩
        (a /Var ρ) ⌜·⌝⟨ j ⇒ k ⟩ (b /Var ρ) ∙∙⟨ k ⟩ (bs //Var ρ)
      ∎

    ⌜·⌝⟨⟩-/Var : ∀ {m n} a k b {ρ : Sub Fin m n} →
                 a ⌜·⌝⟨ k ⟩ b /Var ρ ≡ (a /Var ρ) ⌜·⌝⟨ k ⟩ (b /Var ρ)
    ⌜·⌝⟨⟩-/Var a ★                    b     = S.⌜·⌝-/Var a b
    ⌜·⌝⟨⟩-/Var (a ∙ (c ∷ cs)) (j ⇒ k) b {ρ} = begin
        a ∙ (c ∷ cs) ⌜·⌝ b /Var ρ
      ≡⟨ S.⌜·⌝-/Var (a ∙ (c ∷ cs)) b ⟩
        (a ∙ (c ∷ cs) /Var ρ) ⌜·⌝ (b /Var ρ)
      ≡˘⟨ cong (λ a → a ∙∙ _ ⌜·⌝ (b /Var ρ)) (S.Head/Var-∙ a) ⟩
        (a Head/Var ρ) ∙ ((c ∷ cs) //Var ρ) ⌜·⌝⟨ j ⇒ k ⟩ (b /Var ρ)
      ≡⟨ cong (λ a → a ∙∙ _ ⌜·⌝⟨ j ⇒ k ⟩ (b /Var ρ)) (S.Head/Var-∙ a) ⟩
        (a ∙ (c ∷ cs) /Var ρ) ⌜·⌝⟨ j ⇒ k ⟩ (b /Var ρ)
      ∎
    ⌜·⌝⟨⟩-/Var (var x   ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/Var (⊥       ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/Var (⊤       ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/Var (Π l a   ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/Var ((a ⇒ b) ∙ []) (j ⇒ k) c = refl
    ⌜·⌝⟨⟩-/Var (Λ l a   ∙ []) (j ⇒ k) b = /⟨⟩-/Var-↑⋆ 0 b j a
    ⌜·⌝⟨⟩-/Var (ƛ a b   ∙ []) (j ⇒ k) c = refl
    ⌜·⌝⟨⟩-/Var (a ⊡ b   ∙ []) (j ⇒ k) c = refl

  -- Some corollaries of the above.

  Asc/⟨⟩-/Var-↑⋆ : ∀ i {m n} a k b {ρ : Sub Fin m n} →
                   b Asc/⟨ k ⟩ sub a ↑⋆ i ElimAsc/Var ρ V.↑⋆ i ≡
                     b ElimAsc/Var (ρ V.↑) V.↑⋆ i Asc/⟨ k ⟩ sub (a /Var ρ) ↑⋆ i
  Asc/⟨⟩-/Var-↑⋆ i a k (kd j) = cong kd (Kind/⟨⟩-/Var-↑⋆ i a k j)
  Asc/⟨⟩-/Var-↑⋆ i a k (tp b) = cong tp (/⟨⟩-/Var-↑⋆ i a k b)

  [∈⌊⌋]-/Var : ∀ {m n} a b k {ρ : Sub Fin m n} →
               a [ b ∈ ⌊ k ⌋ ] /Var ρ ≡
                 (a /Var ρ V.↑) [ b /Var ρ ∈ ⌊ k Kind′/Var ρ ⌋ ]
  [∈⌊⌋]-/Var a b k {ρ} = begin
      (a [ b ∈ ⌊ k ⌋ ] /Var ρ)
    ≡⟨ /⟨⟩-/Var-↑⋆ 0 b ⌊ k ⌋ a ⟩
      ((a /Var ρ V.↑) [ b /Var ρ ∈ ⌊ k ⌋ ])
    ≡˘⟨ cong (a /Var ρ V.↑ /⟨_⟩ sub (b /Var ρ)) (S.⌊⌋-Kind′/Var k) ⟩
      ((a /Var ρ V.↑) [ b /Var ρ ∈ ⌊ k Kind′/Var ρ ⌋ ])
    ∎

  Kind[∈⌊⌋]-/Var : ∀ {m n} j a k {ρ : Sub Fin m n} →
                   j Kind[ a ∈ ⌊ k ⌋ ] Kind′/Var ρ ≡
                     (j Kind′/Var ρ V.↑) Kind[ a /Var ρ ∈ ⌊ k Kind′/Var ρ ⌋ ]
  Kind[∈⌊⌋]-/Var j a k {ρ} = begin
      j Kind[ a ∈ ⌊ k ⌋ ] Kind′/Var ρ
    ≡⟨ Kind/⟨⟩-/Var-↑⋆ 0 a ⌊ k ⌋ j ⟩
      (j Kind′/Var ρ V.↑) Kind[ a /Var ρ ∈ ⌊ k ⌋ ]
    ≡˘⟨ cong (j Kind′/Var ρ V.↑ Kind/⟨_⟩ sub (a /Var ρ)) (S.⌊⌋-Kind′/Var k) ⟩
      (j Kind′/Var ρ V.↑) Kind[ a /Var ρ ∈ ⌊ k Kind′/Var ρ ⌋ ]
    ∎

  -- Potentially reducing applications commute with renaming.

  ↓⌜·⌝-/Var : ∀ {m n} a b {ρ : Sub Fin m n} →
              a ↓⌜·⌝ b /Var ρ ≡ (a /Var ρ) ↓⌜·⌝ (b /Var ρ)
  ↓⌜·⌝-/Var (a ∙ (c ∷ cs)) b {ρ} = begin
      a ∙ (c ∷ cs) ⌜·⌝ b /Var ρ
    ≡⟨ S.⌜·⌝-/Var (a ∙ (c ∷ cs)) b ⟩
      (a ∙ (c ∷ cs) /Var ρ) ⌜·⌝ (b /Var ρ)
    ≡˘⟨ cong (λ a → a ∙∙ _ ⌜·⌝ (b /Var ρ)) (S.Head/Var-∙ a) ⟩
      (a Head/Var ρ) ∙ ((c ∷ cs) //Var ρ) ↓⌜·⌝ (b /Var ρ)
    ≡⟨ cong (λ a → a ∙∙ _ ↓⌜·⌝ (b /Var ρ)) (S.Head/Var-∙ a) ⟩
      (a ∙ (c ∷ cs) /Var ρ) ↓⌜·⌝ (b /Var ρ)
    ∎
  ↓⌜·⌝-/Var (var x   ∙ []) b = refl
  ↓⌜·⌝-/Var (⊥       ∙ []) b = refl
  ↓⌜·⌝-/Var (⊤       ∙ []) b = refl
  ↓⌜·⌝-/Var (Π l a   ∙ []) b = refl
  ↓⌜·⌝-/Var ((a ⇒ b) ∙ []) c = refl
  ↓⌜·⌝-/Var (Λ l a   ∙ []) b = [∈⌊⌋]-/Var a b l
  ↓⌜·⌝-/Var (ƛ a b   ∙ []) c = refl
  ↓⌜·⌝-/Var (a ⊡ b   ∙ []) c = refl

  mutual

    -- Weakening commutes with application of lifted hereditary
    -- substitutions.
    --
    -- NOTE: this is a variant of the `wk-commutes' lemma from
    -- Data.Fin.Substitution.Lemmas adapted to hereditary
    -- substitutions.

    wk-/⟨⟩-↑⋆ : ∀ i {k m n} a {σ : SVSub m n} →
                a /Var V.wk V.↑⋆ i /⟨ k ⟩ (σ ↑) ↑⋆ i ≡
                  a /⟨ k ⟩ σ ↑⋆ i /Var V.wk V.↑⋆ i
    wk-/⟨⟩-↑⋆ i {k} (var x ∙ as) {σ} = begin
        var x ∙ as /Var V.wk V.↑⋆ i /⟨ k ⟩ (σ ↑) ↑⋆ i
      ≡⟨⟩
        lookupSV ((σ ↑) ↑⋆ i) (x V./ V.wk V.↑⋆ i) ?∙∙⟨ k ⟩
          (as //Var V.wk V.↑⋆ i //⟨ k ⟩ ((σ ↑) ↑⋆ i))
      ≡⟨ (cong₂ (_?∙∙⟨ k ⟩_)) (sym (lookup-/Var-wk-↑⋆ i x)) (wk-//⟨⟩-↑⋆ i as) ⟩
        (lookupSV (σ ↑⋆ i) x ?/Var V.wk V.↑⋆ i) ?∙∙⟨ k ⟩
          (as //⟨ k ⟩ (σ ↑⋆ i) //Var V.wk V.↑⋆ i)
      ≡˘⟨ ?∙∙⟨⟩-/Var (lookupSV (σ ↑⋆ i) x) k (as //⟨ k ⟩ (σ ↑⋆ i)) ⟩
        lookupSV (σ ↑⋆ i) x ?∙∙⟨ k ⟩ (as //⟨ k ⟩ (σ ↑⋆ i)) /Var V.wk V.↑⋆ i
      ≡⟨⟩
        var x ∙ as /⟨ k ⟩ σ ↑⋆ i /Var V.wk V.↑⋆ i
      ∎
    wk-/⟨⟩-↑⋆ i (⊥ ∙ as)       = cong (⊥ ∙_) (wk-//⟨⟩-↑⋆ i as)
    wk-/⟨⟩-↑⋆ i (⊤ ∙ as)       = cong (⊤ ∙_) (wk-//⟨⟩-↑⋆ i as)
    wk-/⟨⟩-↑⋆ i (Π k a ∙ as)   =
      cong₂ _∙_ (cong₂ Π (wk-Kind/⟨⟩-↑⋆ i k) (wk-/⟨⟩-↑⋆ (suc i) a))
                (wk-//⟨⟩-↑⋆ i as)
    wk-/⟨⟩-↑⋆ i ((a ⇒ b) ∙ as) =
      cong₂ _∙_ (cong₂ _⇒_ (wk-/⟨⟩-↑⋆ i a) (wk-/⟨⟩-↑⋆ i b)) (wk-//⟨⟩-↑⋆ i as)
    wk-/⟨⟩-↑⋆ i (Λ k a ∙ as)   =
      cong₂ _∙_ (cong₂ Λ (wk-Kind/⟨⟩-↑⋆ i k) (wk-/⟨⟩-↑⋆ (suc i) a))
                (wk-//⟨⟩-↑⋆ i as)
    wk-/⟨⟩-↑⋆ i (ƛ a b ∙ as)   =
      cong₂ _∙_ (cong₂ ƛ (wk-/⟨⟩-↑⋆ i a) (wk-/⟨⟩-↑⋆ (suc i) b)) (wk-//⟨⟩-↑⋆ i as)
    wk-/⟨⟩-↑⋆ i (a ⊡ b ∙ as)   =
      cong₂ _∙_ (cong₂ _⊡_ (wk-/⟨⟩-↑⋆ i a) (wk-/⟨⟩-↑⋆ i b)) (wk-//⟨⟩-↑⋆ i as)

    wk-Kind/⟨⟩-↑⋆ : ∀ i {k m n} j {σ : SVSub m n} →
                    j Kind′/Var V.wk V.↑⋆ i Kind/⟨ k ⟩ (σ ↑) ↑⋆ i ≡
                      j Kind/⟨ k ⟩ σ ↑⋆ i Kind′/Var V.wk V.↑⋆ i
    wk-Kind/⟨⟩-↑⋆ i (a ⋯ b) = cong₂ _⋯_ (wk-/⟨⟩-↑⋆ i a) (wk-/⟨⟩-↑⋆ i b)
    wk-Kind/⟨⟩-↑⋆ i (Π j k) =
      cong₂ Π (wk-Kind/⟨⟩-↑⋆ i j) (wk-Kind/⟨⟩-↑⋆ (suc i) k)

    wk-//⟨⟩-↑⋆ : ∀ i {k m n} as {σ : SVSub m n} →
                 as //Var V.wk V.↑⋆ i //⟨ k ⟩ (σ ↑) ↑⋆ i ≡
                   as //⟨ k ⟩ σ ↑⋆ i //Var V.wk V.↑⋆ i
    wk-//⟨⟩-↑⋆ i []       = refl
    wk-//⟨⟩-↑⋆ i (a ∷ as) = cong₂ _∷_ (wk-/⟨⟩-↑⋆ i a) (wk-//⟨⟩-↑⋆ i as)

  -- A corollary of the above.

  wk-Asc/⟨⟩-↑⋆ : ∀ i {k m n} a {σ : SVSub m n} →
                a ElimAsc/Var V.wk V.↑⋆ i Asc/⟨ k ⟩ (σ ↑) ↑⋆ i ≡
                  a Asc/⟨ k ⟩ σ ↑⋆ i ElimAsc/Var V.wk V.↑⋆ i
  wk-Asc/⟨⟩-↑⋆ i (kd a) = cong kd (wk-Kind/⟨⟩-↑⋆ i a)
  wk-Asc/⟨⟩-↑⋆ i (tp a) = cong tp (wk-/⟨⟩-↑⋆ i a)

  mutual

    -- Weakening of a term followed by hereditary substitution of the
    -- newly introduced extra variable leaves the term unchanged.
    --
    -- NOTE: this is a variant of the `wk-sub-vanishes' lemma from
    -- Data.Fin.Substitution.Lemmas adapted to hereditary
    -- substitutions.

    /Var-wk-↑⋆-hsub-vanishes : ∀ i {k m} a {b : Elim m} →
                               a /Var V.wk V.↑⋆ i /⟨ k ⟩ sub b ↑⋆ i ≡ a
    /Var-wk-↑⋆-hsub-vanishes i {k} (var x ∙ as) {b} = begin
        var x ∙ as /Var V.wk V.↑⋆ i /⟨ k ⟩ sub b ↑⋆ i
      ≡⟨ cong₂ _?∙∙⟨ k ⟩_ (lookup-sub-wk-↑⋆ i x)
                          (//Var-wk-↑⋆-hsub-vanishes i as) ⟩
        var x ∙ as
      ∎
    /Var-wk-↑⋆-hsub-vanishes i (⊥ ∙ as)       =
      cong (⊥ ∙_) (//Var-wk-↑⋆-hsub-vanishes i as)
    /Var-wk-↑⋆-hsub-vanishes i (⊤ ∙ as)       =
      cong (⊤ ∙_) (//Var-wk-↑⋆-hsub-vanishes i as)
    /Var-wk-↑⋆-hsub-vanishes i (Π k a ∙ as)   =
      cong₂ _∙_ (cong₂ Π (Kind/Var-wk-↑⋆-hsub-vanishes i k)
                         (/Var-wk-↑⋆-hsub-vanishes (suc i) a))
                (//Var-wk-↑⋆-hsub-vanishes i as)
    /Var-wk-↑⋆-hsub-vanishes i ((a ⇒ b) ∙ as) =
      cong₂ _∙_ (cong₂ _⇒_ (/Var-wk-↑⋆-hsub-vanishes i a)
                           (/Var-wk-↑⋆-hsub-vanishes i b))
                (//Var-wk-↑⋆-hsub-vanishes i as)
    /Var-wk-↑⋆-hsub-vanishes i (Λ k a ∙ as)   =
      cong₂ _∙_ (cong₂ Λ (Kind/Var-wk-↑⋆-hsub-vanishes i k)
                         (/Var-wk-↑⋆-hsub-vanishes (suc i) a))
                (//Var-wk-↑⋆-hsub-vanishes i as)
    /Var-wk-↑⋆-hsub-vanishes i (ƛ a b ∙ as)   =
      cong₂ _∙_ (cong₂ ƛ (/Var-wk-↑⋆-hsub-vanishes i a)
                           (/Var-wk-↑⋆-hsub-vanishes (suc i) b))
                (//Var-wk-↑⋆-hsub-vanishes i as)
    /Var-wk-↑⋆-hsub-vanishes i (a ⊡ b ∙ as)   =
      cong₂ _∙_ (cong₂ _⊡_ (/Var-wk-↑⋆-hsub-vanishes i a)
                           (/Var-wk-↑⋆-hsub-vanishes i b))
                (//Var-wk-↑⋆-hsub-vanishes i as)

    Kind/Var-wk-↑⋆-hsub-vanishes
      : ∀ i {k m} j {b : Elim m} →
        j Kind′/Var V.wk V.↑⋆ i Kind/⟨ k ⟩ sub b ↑⋆ i ≡ j
    Kind/Var-wk-↑⋆-hsub-vanishes i (a ⋯ b) =
      cong₂ _⋯_ (/Var-wk-↑⋆-hsub-vanishes i a) (/Var-wk-↑⋆-hsub-vanishes i b)
    Kind/Var-wk-↑⋆-hsub-vanishes i (Π j k) =
      cong₂ Π (Kind/Var-wk-↑⋆-hsub-vanishes i j)
              (Kind/Var-wk-↑⋆-hsub-vanishes (suc i) k)

    //Var-wk-↑⋆-hsub-vanishes : ∀ i {k m} as {b : Elim m} →
                                as //Var V.wk V.↑⋆ i //⟨ k ⟩ sub b ↑⋆ i ≡ as
    //Var-wk-↑⋆-hsub-vanishes i []       = refl
    //Var-wk-↑⋆-hsub-vanishes i (a ∷ as) =
      cong₂ _∷_ (/Var-wk-↑⋆-hsub-vanishes i a) (//Var-wk-↑⋆-hsub-vanishes i as)

  -- A corollary of the above.
  Asc/Var-wk-↑⋆-hsub-vanishes
    : ∀ i {k m} a {b : Elim m} →
      a S.ElimAsc/Var V.wk V.↑⋆ i Asc/⟨ k ⟩ sub b ↑⋆ i ≡ a
  Asc/Var-wk-↑⋆-hsub-vanishes i (kd a) =
    cong kd (Kind/Var-wk-↑⋆-hsub-vanishes i a)
  Asc/Var-wk-↑⋆-hsub-vanishes i (tp a) =
    cong tp (/Var-wk-↑⋆-hsub-vanishes i a)

open RenamingCommutes

module _ where
  private
    module EL = TermLikeLemmas Substitution.termLikeLemmasElim
    module KL = TermLikeLemmas Substitution.termLikeLemmasKind′
  open Substitution hiding (_↑; _↑⋆_; sub)
  open ≡-Reasoning

  -- Repeated weakening commutes with application of lifted hereditary
  -- substitutions.

  wk⋆-/⟨⟩-↑⋆ : ∀ i {k m n} a {σ : SVSub m n} →
               a Elim/ wk⋆ i /⟨ k ⟩ σ ↑⋆ i ≡ a /⟨ k ⟩ σ Elim/ wk⋆ i
  wk⋆-/⟨⟩-↑⋆ zero {k} a {σ} = begin
    a Elim/ id /⟨ k ⟩ σ   ≡⟨ cong (_/⟨ k ⟩ σ) (EL.id-vanishes a) ⟩
    a /⟨ k ⟩ σ            ≡˘⟨ EL.id-vanishes (a /⟨ k ⟩ σ) ⟩
    a /⟨ k ⟩ σ Elim/ id   ∎
  wk⋆-/⟨⟩-↑⋆ (suc i) {k} a {σ} = begin
      a Elim/ wk⋆ (suc i) /⟨ k ⟩ (σ ↑⋆ i) ↑
    ≡⟨ cong (_/⟨ k ⟩ (σ ↑⋆ i) ↑) (EL./-weaken a) ⟩
      a Elim/ wk⋆ i Elim/ wk /⟨ k ⟩ (σ ↑⋆ i) ↑
    ≡⟨ cong (_/⟨ k ⟩ (σ ↑⋆ i) ↑) (EL./-wk {t = a Elim/ wk⋆ i}) ⟩
      weakenElim (a Elim/ wk⋆ i) /⟨ k ⟩ (σ ↑⋆ i) ↑
    ≡⟨ wk-/⟨⟩-↑⋆ zero (a Elim/ wk⋆ i) ⟩
      weakenElim (a Elim/ wk⋆ i /⟨ k ⟩ σ ↑⋆ i)
    ≡⟨ cong weakenElim (wk⋆-/⟨⟩-↑⋆ i a) ⟩
      weakenElim (a /⟨ k ⟩ σ Elim/ wk⋆ i)
    ≡˘⟨ (EL./-wk {t = a /⟨ k ⟩ σ Elim/ wk⋆ i}) ⟩
      a /⟨ k ⟩ σ Elim/ wk⋆ i Elim/ wk
    ≡˘⟨ EL./-weaken (a /⟨ k ⟩ σ)  ⟩
      a /⟨ k ⟩ σ Elim/ wk⋆ (suc i)
    ∎

  wk⋆-Kind/⟨⟩-↑⋆ : ∀ i {k m n} j {σ : SVSub m n} →
                   j Kind′/ wk⋆ i Kind/⟨ k ⟩ σ ↑⋆ i ≡
                     j Kind/⟨ k ⟩ σ Kind′/ wk⋆ i
  wk⋆-Kind/⟨⟩-↑⋆ zero {k} j {σ} = begin
    j Kind′/ id Kind/⟨ k ⟩ σ   ≡⟨ cong (_Kind/⟨ k ⟩ σ) (KL.id-vanishes j) ⟩
    j Kind/⟨ k ⟩ σ             ≡˘⟨ KL.id-vanishes (j Kind/⟨ k ⟩ σ) ⟩
    j Kind/⟨ k ⟩ σ Kind′/ id   ∎
  wk⋆-Kind/⟨⟩-↑⋆ (suc i) {k} j {σ} = begin
      j Kind′/ wk⋆ (suc i) Kind/⟨ k ⟩ (σ ↑⋆ i) ↑
    ≡⟨ cong (_Kind/⟨ k ⟩ (σ ↑⋆ i) ↑) (KL./-weaken j) ⟩
      j Kind′/ wk⋆ i Kind′/ wk Kind/⟨ k ⟩ (σ ↑⋆ i) ↑
    ≡⟨ cong (_Kind/⟨ k ⟩ (σ ↑⋆ i) ↑) (KL./-wk {t = j Kind′/ wk⋆ i}) ⟩
      weakenKind′ (j Kind′/ wk⋆ i) Kind/⟨ k ⟩ (σ ↑⋆ i) ↑
    ≡⟨ wk-Kind/⟨⟩-↑⋆ zero (j Kind′/ wk⋆ i) ⟩
      weakenKind′ (j Kind′/ wk⋆ i Kind/⟨ k ⟩ σ ↑⋆ i)
    ≡⟨ cong weakenKind′ (wk⋆-Kind/⟨⟩-↑⋆ i j) ⟩
      weakenKind′ (j Kind/⟨ k ⟩ σ Kind′/ wk⋆ i)
    ≡˘⟨ (KL./-wk {t = j Kind/⟨ k ⟩ σ Kind′/ wk⋆ i}) ⟩
      j Kind/⟨ k ⟩ σ Kind′/ wk⋆ i Kind′/ wk
    ≡˘⟨ KL./-weaken (j Kind/⟨ k ⟩ σ)  ⟩
      j Kind/⟨ k ⟩ σ Kind′/ wk⋆ (suc i)
    ∎

  -- A corollary of the above.
  weaken⋆-/⟨⟩-↑⋆ : ∀ i {k m n} a {σ : SVSub m n} →
                   weakenElim⋆ i (a /⟨ k ⟩ σ) ≡ weakenElim⋆ i a /⟨ k ⟩ σ ↑⋆ i
  weaken⋆-/⟨⟩-↑⋆ i {k} a {σ} = begin
    weakenElim⋆ i (a /⟨ k ⟩ σ)     ≡˘⟨ EL./-wk⋆ i ⟩
    a /⟨ k ⟩ σ Elim/ wk⋆ i         ≡˘⟨ wk⋆-/⟨⟩-↑⋆ i a ⟩
    a Elim/ wk⋆ i /⟨ k ⟩ σ ↑⋆ i    ≡⟨ cong (_/⟨ k ⟩ σ ↑⋆ i) (EL./-wk⋆ i) ⟩
    weakenElim⋆ i a /⟨ k ⟩ σ ↑⋆ i  ∎

  -- NOTE. Unfortunately, we cannot prove that arbitrary untyped
  -- hereditary substitutions commute, because *untyped* hereditary
  -- substitutions need not commute with reducting applications in
  -- general.  We will prove a weaker result, namely that well-kinded
  -- hereditary substitutions in well-kinded types commute, later.
  -- See e.g. `Nf∈-[]-/⟨⟩-↑⋆` etc. in module Kinding.Simple.

-- Some commutation lemmas up to βη-equality.

module _ where
  open →β*-Reasoning
  open Substitution hiding (_↑; _↑⋆_; sub)
  private module Kd = Kd→β*-Reasoning

  mutual

    -- Hereditary substitution commutes with ⌞_⌟ up to β-reduction.

    ⌞⌟-/⟨⟩-β : ∀ {m n} a {k} {σ : SVSub m n} →
               ⌞ a ⌟ / toSub σ  →β*  ⌞ a /⟨ k ⟩ σ ⌟
    ⌞⌟-/⟨⟩-β (var x ∙ bs) {k} {σ} = begin
        ⌞ var x ∙ bs ⌟ / toSub σ
      ⟶⋆⟨ ⌞∙⌟-/⟨⟩-β (var x / toSub σ) (var x) bs ε ⟩
        (var x / toSub σ) ⌞∙⌟ ⌞ bs //⟨ k ⟩ σ ⌟Sp
      ≡⟨ cong (_⌞∙⌟ ⌞ bs //⟨ k ⟩ σ ⌟Sp) (lookup-toSub σ x) ⟩
        ⌞ toElim (lookupSV σ x) ⌟ ⌞∙⌟ ⌞ bs //⟨ k ⟩ σ ⌟Sp
      ⟶⋆⟨ ⌞⌟-?∙∙-β (lookupSV σ x) k (bs //⟨ k ⟩ σ) ⟩
        ⌞ lookupSV σ x ?∙∙⟨ k ⟩ (bs //⟨ k ⟩ σ) ⌟
      ∎
    ⌞⌟-/⟨⟩-β (⊥ ∙ bs) = ⌞∙⌟-/⟨⟩-β ⊥ ⊥ bs ε
    ⌞⌟-/⟨⟩-β (⊤ ∙ bs) = ⌞∙⌟-/⟨⟩-β ⊤ ⊤ bs ε
    ⌞⌟-/⟨⟩-β (Π j b ∙ bs) {k} {σ} = ⌞∙⌟-/⟨⟩-β _ _ bs (begin
        ⌞ Π j b ⌟Hd / toSub σ
      ⟶⋆⟨ →β*-Π (⌞⌟Kd-/⟨⟩-β j) (⌞⌟-/⟨⟩-β b) ⟩
        Π ⌞ j Kind/⟨ k ⟩ σ ⌟Kd ⌞ b /⟨ k ⟩ σ ↑ ⌟
      ∎)
    ⌞⌟-/⟨⟩-β ((a ⇒ b) ∙ bs) {k} {σ} = ⌞∙⌟-/⟨⟩-β _ _ bs (begin
        ⌞ a ⇒ b ⌟Hd / toSub σ
      ⟶⋆⟨ →β*-⇒ (⌞⌟-/⟨⟩-β a) (⌞⌟-/⟨⟩-β b) ⟩
        ⌞ a /⟨ k ⟩ σ ⌟ ⇒ ⌞ b /⟨ k ⟩ σ ⌟
      ∎)
    ⌞⌟-/⟨⟩-β (Λ j b ∙ bs) {k} {σ}  = ⌞∙⌟-/⟨⟩-β _ _ bs (begin
        ⌞ Λ j b ⌟Hd / toSub σ
      ⟶⋆⟨ →β*-Λ (⌞⌟Kd-/⟨⟩-β j) (⌞⌟-/⟨⟩-β b) ⟩
        Λ ⌞ j Kind/⟨ k ⟩ σ ⌟Kd ⌞ b /⟨ k ⟩ σ ↑ ⌟
      ∎)
    ⌞⌟-/⟨⟩-β (ƛ a b ∙ bs) {k} {σ}  = ⌞∙⌟-/⟨⟩-β _ _ bs (begin
        ⌞ ƛ a b ⌟Hd / toSub σ
      ⟶⋆⟨ →β*-ƛ (⌞⌟-/⟨⟩-β a) (⌞⌟-/⟨⟩-β b) ⟩
        ƛ ⌞ a /⟨ k ⟩ σ ⌟ ⌞ b /⟨ k ⟩ σ ↑ ⌟
      ∎)
    ⌞⌟-/⟨⟩-β (a ⊡ b ∙ bs) {k} {σ}  = ⌞∙⌟-/⟨⟩-β _ _ bs (begin
        ⌞ a ⊡ b ⌟Hd / toSub σ
      ⟶⋆⟨ →β*-⊡ (⌞⌟-/⟨⟩-β a) (⌞⌟-/⟨⟩-β b) ⟩
        ⌞ a /⟨ k ⟩ σ ⌟ ⊡ ⌞ b /⟨ k ⟩ σ ⌟
      ∎)

    ⌞⌟Kd-/⟨⟩-β : ∀ {m n} j {k} {σ : SVSub m n} →
                 ⌞ j ⌟Kd Kind/ toSub σ  Kd→β*  ⌞ j Kind/⟨ k ⟩ σ ⌟Kd
    ⌞⌟Kd-/⟨⟩-β (a ⋯ b) {k} {σ} = Kd.begin
        (⌞ a ⋯ b ⌟Kd Kind/ toSub σ)
      Kd.⟶⋆⟨ Kd→β*-⋯ (⌞⌟-/⟨⟩-β a) (⌞⌟-/⟨⟩-β b) ⟩
        ⌞ a /⟨ k ⟩ σ ⌟ ⋯ ⌞ b /⟨ k ⟩ σ ⌟
      Kd.∎
    ⌞⌟Kd-/⟨⟩-β (Π j l) {k} {σ} = Kd.begin
        (⌞ Π j l ⌟Kd Kind/ toSub σ)
      Kd.⟶⋆⟨ Kd→β*-Π (⌞⌟Kd-/⟨⟩-β j) (⌞⌟Kd-/⟨⟩-β l) ⟩
        Π ⌞ j Kind/⟨ k ⟩ σ ⌟Kd ⌞ l Kind/⟨ k ⟩ σ ↑ ⌟Kd
      Kd.∎

    ⌞∙⌟-/⟨⟩-β : ∀ {m n} a b bs {k} {σ : SVSub m n} →
                b / toSub σ →β* a →
                (b ⌞∙⌟ ⌞ bs ⌟Sp) / toSub σ  →β*  a ⌞∙⌟ ⌞ bs //⟨ k ⟩ σ ⌟Sp
    ⌞∙⌟-/⟨⟩-β a b []               hyp = hyp
    ⌞∙⌟-/⟨⟩-β a b (c ∷ cs) {k} {σ} hyp =
      ⌞∙⌟-/⟨⟩-β (a · ⌞ c /⟨ k ⟩ σ ⌟) (b · ⌞ c ⌟) cs
               (→β*-· hyp (⌞⌟-/⟨⟩-β c))

    -- Reducing applications commute with ⌞_⌟ up to β-reduction.

    ⌞⌟-?∙∙-β : ∀ {n} (r : SVRes n) k bs →
               ⌞ toElim r ⌟ ⌞∙⌟ ⌞ bs ⌟Sp →β* ⌞ r ?∙∙⟨ k ⟩ bs ⌟
    ⌞⌟-?∙∙-β (hit a)  k bs = ⌞⌟-∙∙-β a k bs
    ⌞⌟-?∙∙-β (miss y) k bs = ε

    ⌞⌟-∙∙-β : ∀ {n} (a : Elim n) k bs → ⌞ a ⌟ ⌞∙⌟ ⌞ bs ⌟Sp →β* ⌞ a ∙∙⟨ k ⟩ bs ⌟
    ⌞⌟-∙∙-β a k       []       = ε
    ⌞⌟-∙∙-β a ★       (b ∷ bs) = begin
      ⌞ a ⌟ ⌞∙⌟ (⌞ b ⌟ ∷ ⌞ bs ⌟Sp) ≡˘⟨ ⌞⌟-∙∙ a (b ∷ bs) ⟩
      ⌞ a ∙∙ (b ∷ bs) ⌟            ∎
    ⌞⌟-∙∙-β a (j ⇒ k) (b ∷ bs) = begin
        ⌞ a ⌟ ⌞∙⌟ (⌞ b ⌟ ∷ ⌞ bs ⌟Sp)
      ⟶⋆⟨ →β*-⌞∙⌟₁ (⌞⌟-⌜·⌝-β a (j ⇒ k) b) ⌞ bs ⌟Sp  ⟩
        ⌞ a ⌜·⌝⟨ j ⇒ k ⟩ b ⌟ ⌞∙⌟ ⌞ bs ⌟Sp
      ⟶⋆⟨ ⌞⌟-∙∙-β (a ⌜·⌝⟨ j ⇒ k ⟩ b) k bs ⟩
        ⌞ a ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs ⌟
      ∎

    ⌞⌟-⌜·⌝-β : ∀ {n} (a : Elim n) k b → ⌞ a ⌟ · ⌞ b ⌟ →β* ⌞ a ⌜·⌝⟨ k ⟩ b ⌟
    ⌞⌟-⌜·⌝-β a ★ b = begin
      ⌞ a ⌟ · ⌞ b ⌟              ≡˘⟨ ⌞⌟-· a b ⟩
      ⌞ a ⌜·⌝ b ⌟                ∎
    ⌞⌟-⌜·⌝-β (a ∙ (c ∷ cs)) (j ⇒ k) b = begin
      ⌞ a ∙ (c ∷ cs) ⌟ · ⌞ b ⌟   ≡˘⟨ ⌞⌟-· (a ∙ (c ∷ cs)) b ⟩
      ⌞ a ∙ (c ∷ cs) ⌜·⌝ b ⌟     ∎
    ⌞⌟-⌜·⌝-β (var x   ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β (⊥       ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β (⊤       ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β (Π l a   ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β ((a ⇒ b) ∙ []) (j ⇒ k) c = ε
    ⌞⌟-⌜·⌝-β (Λ l a ∙ []) (j ⇒ k) b = begin
      Λ ⌞ l ⌟Kd ⌞ a ⌟ · ⌞ b ⌟    ⟶⟨ ⌈ cont-Tp· ⌞ l ⌟Kd ⌞ a ⌟ ⌞ b ⌟ ⌉ ⟩
      ⌞ a ⌟ [ ⌞ b ⌟ ]            ⟶⋆⟨ ⌞⌟-/⟨⟩-β a {j} {sub b} ⟩
      ⌞ a [ b ∈ j ] ⌟            ∎
    ⌞⌟-⌜·⌝-β (ƛ a b   ∙ []) (j ⇒ k) c = ε
    ⌞⌟-⌜·⌝-β (a ⊡ b   ∙ []) (j ⇒ k) c = ε

  -- Potentially reducing applications commute with ⌞_⌟ up to β-reduction.

  ⌞⌟-↓⌜·⌝-β : ∀ {n} (a : Elim n) b → ⌞ a ⌟ · ⌞ b ⌟ →β* ⌞ a ↓⌜·⌝ b ⌟
  ⌞⌟-↓⌜·⌝-β (a ∙ (c ∷ cs)) b = begin
    ⌞ a ∙ (c ∷ cs) ⌟ · ⌞ b ⌟   ≡˘⟨ ⌞⌟-· (a ∙ (c ∷ cs)) b ⟩
    ⌞ a ∙ (c ∷ cs) ⌜·⌝ b ⌟     ∎
  ⌞⌟-↓⌜·⌝-β (var x   ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β (⊥       ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β (⊤       ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β (Π l a   ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β ((a ⇒ b) ∙ []) c = ε
  ⌞⌟-↓⌜·⌝-β (Λ l a ∙ []) b = begin
    Λ ⌞ l ⌟Kd ⌞ a ⌟ · ⌞ b ⌟    ⟶⟨ ⌈ cont-Tp· ⌞ l ⌟Kd ⌞ a ⌟ ⌞ b ⌟ ⌉ ⟩
    ⌞ a ⌟ [ ⌞ b ⌟ ]            ⟶⋆⟨ ⌞⌟-/⟨⟩-β a {⌊ l ⌋} {sub b} ⟩
    ⌞ a [ b ∈ ⌊ l ⌋ ] ⌟        ∎
  ⌞⌟-↓⌜·⌝-β (ƛ a b   ∙ []) c = ε
  ⌞⌟-↓⌜·⌝-β (a ⊡ b   ∙ []) c = ε
