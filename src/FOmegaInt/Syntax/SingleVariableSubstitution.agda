------------------------------------------------------------------------
-- Untyped hereditary substitution in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --exact-split --without-K #-}

module FOmegaInt.Syntax.SingleVariableSubstitution where

open import Data.Fin using (Fin; zero; suc; _↑ʳ_; lift)
open import Data.Fin.Substitution using (Sub; Subs; Lift; Application)
open import Data.Fin.Substitution.Lemmas using (AppLemmas)
  renaming (module VarLemmas to V)
open import Data.Fin.Substitution.ExtraLemmas
  using (TermLikeLemmas; LiftAppLemmas)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Vec as Vec
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])

open import FOmegaInt.Syntax renaming (module Substitution to Sub)


----------------------------------------------------------------------
-- Untyped single-variable substitution.

open Syntax
open Sub using (weaken; weakenElim; weakenElim⋆; _Elim/Var_)

-- Suspended single-variable substitions.
--
-- Traditionally, a single-variable substitution [t/x] consists of two
-- data: the name x of the variable to be substituted and the
-- substitute t for the variable.
--
-- The following inductive definition is an alternative representation
-- of this data.  Instead of specifying the variable name (i.e. the de
-- Bruijn index) to be substituted, we use two constructors: one for
-- substituting the zero-th variable (sub) and one for lifting the
-- substitution over an a new free variable (_↑).  The advantage of
-- this representation is that it corresponds more closely to the
-- explicit substitution calculus and the inductive structure of both
-- de Bruijn indices and dependent contexts.  Among other things, this
-- avoids green slime in the definition.
--
-- Since we are working with intrinsically well-scoped syntax, the
-- datatype is parametrized by the number of free variables in the
-- source and target context: a substitution |σ : SVSub m n|, when
-- applied to a term with at most m variables, yields a term with at
-- most n variables.

data SVSub : ℕ → ℕ → Set where
  sub : ∀ {n}   (a : Elim n)    → SVSub (suc n) n
  _↑  : ∀ {m n} (σ : SVSub m n) → SVSub (suc m) (suc n)

-- Repeated lifting.

_↑⋆_ : ∀ {m n} (σ : SVSub m n) k → SVSub (k + m) (k + n)
σ ↑⋆ zero  = σ
σ ↑⋆ suc k = (σ ↑⋆ k) ↑

-- Turn a single-variable substitution into a multi-variable
-- substitution.

toSub : ∀ {m n} → SVSub m n → Sub Term m n
toSub (sub a) = Sub.sub ⌞ a ⌟
toSub (σ ↑)   = (toSub σ) Sub.↑

-- The result of looking up a single-variable substitution.

data SVRes : ℕ → Set where
  hit  : ∀ {n} (a : Elim n) → SVRes n  -- hit: looked up t at x in [t/x]
  miss : ∀ {n} (y : Fin n)  → SVRes n  -- miss: looked up y ≠ x in [t/x]

toElim : ∀ {n} → SVRes n → Elim n
toElim (hit a)  = a
toElim (miss y) = var∙ y

-- Renamings in single-variable substitutions and results.

infixl 8 _?/Var_

_?/Var_ : ∀ {m n} → SVRes m → Sub Fin m n → SVRes n
hit a  ?/Var ρ = hit (a Elim/Var ρ)
miss y ?/Var ρ = miss (Vec.lookup ρ y)

-- Weakening of SV results.

weakenSVRes : ∀ {n} → SVRes n → SVRes (suc n)
weakenSVRes r = r ?/Var V.wk

-- Look up a variable in a single-variable substitution.

lookupSV : ∀ {m n} → SVSub m n → Fin m → SVRes n
lookupSV (sub a) zero    = hit a
lookupSV (sub a) (suc x) = miss x
lookupSV (σ ↑)   zero    = miss zero
lookupSV (σ ↑)   (suc x) = weakenSVRes (lookupSV σ x)


----------------------------------------------------------------------
-- Properties of single-variable substitution and results.

open P.≡-Reasoning

-- Lifting commutes with conversion of substitutions.

↑⋆-toSub : ∀ {m n} {σ : SVSub m n} k → toSub (σ ↑⋆ k) ≡ (toSub σ) Sub.↑⋆ k
↑⋆-toSub zero    = refl
↑⋆-toSub (suc k) = cong Sub._↑ (↑⋆-toSub k)

-- Application of renamings commutes with conversion to terms.

toElim-/Var : ∀ {m n} r {ρ : Sub Fin m n} →
              toElim (r ?/Var ρ) ≡ toElim r Elim/Var ρ
toElim-/Var (hit a)  = refl
toElim-/Var (miss y) = refl

-- Lookup commutes with conversion of substitutions.

lookup-toSub : ∀ {m n} (σ : SVSub m n) (x : Fin m) →
               Vec.lookup (toSub σ) x ≡ ⌞ toElim (lookupSV σ x) ⌟
lookup-toSub (sub a) zero    = refl
lookup-toSub (sub a) (suc x) = Sub.lookup-id x
lookup-toSub (σ ↑)   zero    = refl
lookup-toSub (σ ↑)   (suc x) = begin
  Vec.lookup ((toSub σ) Sub.↑) (suc x)      ≡⟨⟩
  Vec.lookup (Vec.map weaken (toSub σ)) x   ≡⟨ lookup-map x weaken (toSub σ) ⟩
  weaken (Vec.lookup (toSub σ) x)           ≡⟨ cong weaken (lookup-toSub σ x) ⟩
  weaken ⌞ toElim σ[x] ⌟                    ≡˘⟨ Sub.⌞⌟-/Var (toElim σ[x]) ⟩
  ⌞ weakenElim (toElim σ[x]) ⌟              ≡˘⟨ cong ⌞_⌟ (toElim-/Var σ[x]) ⟩
  ⌞ toElim (weakenSVRes σ[x]) ⌟             ≡⟨⟩
  ⌞ toElim (lookupSV (σ ↑) (suc x)) ⌟       ∎
  where
    open P.≡-Reasoning
    σ[x] = lookupSV σ x

-- Lemmas about applications of renamings to SV results

open TermLikeLemmas Sub.termLikeLemmasElim using (varLiftAppLemmas)
open LiftAppLemmas varLiftAppLemmas using (id-vanishes; /-⊙; wk-commutes)

?/Var-id : ∀ {n} (r : SVRes n) → r ?/Var V.id ≡ r
?/Var-id (hit a)  = cong hit (id-vanishes a)
?/Var-id (miss y) = cong miss (V.id-vanishes y)

?/Var-⊙ : ∀ {m n k} {ρ₁ : Sub Fin m n} {ρ₂ : Sub Fin n k} r →
          r ?/Var ρ₁ V.⊙ ρ₂ ≡ r ?/Var ρ₁ ?/Var ρ₂
?/Var-⊙                (hit a)  = cong hit (/-⊙ a)
?/Var-⊙ {ρ₁ = ρ₁} {ρ₂} (miss y) = cong miss (V./-⊙ {ρ₁ = ρ₁} {ρ₂} y)

resAppLemmas : AppLemmas SVRes Fin
resAppLemmas = record
  { application = record { _/_ = _?/Var_ }
  ; lemmas₄     = V.lemmas₄
  ; id-vanishes = ?/Var-id
  ; /-⊙         = ?/Var-⊙
  }

module SVResAppLemmas = AppLemmas resAppLemmas

-- Lookup in a single-variable substitution commutes with renaming

lookup-sub-/Var-↑⋆ : ∀ {m n} a i x {ρ : Sub Fin m n} →
                     lookupSV (sub a ↑⋆ i) x ?/Var ρ V.↑⋆ i  ≡
                     lookupSV (sub (a Elim/Var ρ) ↑⋆ i) (x V./ (ρ V.↑) V.↑⋆ i)
lookup-sub-/Var-↑⋆ a zero zero        = refl
lookup-sub-/Var-↑⋆ a zero (suc x) {ρ} = begin
    miss (Vec.lookup ρ x)
  ≡⟨⟩
    lookupSV (sub (a Elim/Var ρ)) (suc (Vec.lookup ρ x))
  ≡˘⟨ cong (lookupSV (sub (a Elim/Var ρ))) (lookup-map x suc ρ) ⟩
    lookupSV (sub (a Elim/Var ρ)) (Vec.lookup (Vec.map suc ρ) x)
  ≡⟨⟩
    lookupSV (sub (a Elim/Var ρ)) (suc x V./ ρ V.↑)
  ∎
lookup-sub-/Var-↑⋆ a (suc i) zero        = refl
lookup-sub-/Var-↑⋆ a (suc i) (suc x) {ρ} = begin
    weakenSVRes (lookupSV (sub a ↑⋆ i) x) ?/Var (ρ V.↑⋆ i) V.↑
  ≡⟨⟩
    lookupSV (sub a ↑⋆ i) x ?/Var V.wk ?/Var (ρ V.↑⋆ i) V.↑
  ≡˘⟨ SVResAppLemmas.wk-commutes (lookupSV (sub a ↑⋆ i) x) ⟩
    lookupSV (sub a ↑⋆ i) x ?/Var (ρ V.↑⋆ i) ?/Var V.wk
  ≡⟨ cong (_?/Var V.wk) (lookup-sub-/Var-↑⋆ a i x) ⟩
    lookupSV (sub (a Elim/Var ρ) ↑⋆ i) (x V./ ((ρ V.↑) V.↑⋆ i)) ?/Var V.wk
  ≡⟨⟩
    lookupSV ((sub (a Elim/Var ρ) ↑⋆ i) ↑) (suc (x V./ (ρ V.↑) V.↑⋆ i))
  ≡˘⟨ cong (lookupSV ((sub (a Elim/Var ρ) ↑⋆ i) ↑))
           (lookup-map x suc ((ρ V.↑) V.↑⋆ i)) ⟩
    lookupSV ((sub (a Elim/Var ρ) ↑⋆ i) ↑)
             (Vec.lookup (Vec.map suc ((ρ V.↑) V.↑⋆ i)) x)
  ≡⟨⟩
    lookupSV ((sub (a Elim/Var ρ) ↑⋆ i) ↑) (suc x V./ ((ρ V.↑) V.↑⋆ i) V.↑)
  ∎

-- Lookup commutes with weakening

lookup-/Var-wk-↑⋆ : ∀ {m n} i x {σ : SVSub m n} →
                    lookupSV (σ ↑⋆ i) x ?/Var V.wk V.↑⋆ i ≡
                    lookupSV ((σ ↑) ↑⋆ i) (x V./ V.wk V.↑⋆ i)
lookup-/Var-wk-↑⋆ zero x {σ} = begin
    lookupSV σ x ?/Var V.wk
  ≡⟨⟩
    lookupSV (σ ↑) (suc x)
  ≡˘⟨ cong (lookupSV (σ ↑)) V./-wk ⟩
    lookupSV (σ ↑) (x V./ V.wk)
  ∎
lookup-/Var-wk-↑⋆ (suc i) zero        = refl
lookup-/Var-wk-↑⋆ (suc i) (suc x) {σ} = begin
    lookupSV (σ ↑⋆ i) x ?/Var V.wk ?/Var (V.wk V.↑⋆ i) V.↑
  ≡˘⟨ SVResAppLemmas.wk-commutes (lookupSV (σ ↑⋆ i) x) ⟩
    lookupSV (σ ↑⋆ i) x ?/Var V.wk V.↑⋆ i ?/Var V.wk 
  ≡⟨ cong weakenSVRes (lookup-/Var-wk-↑⋆ i x) ⟩
    lookupSV (((σ ↑) ↑⋆ i) ↑) (suc (Vec.lookup (V.wk V.↑⋆ i) x))
  ≡˘⟨ cong (lookupSV (((σ ↑) ↑⋆ i) ↑)) (lookup-map x suc (V.wk V.↑⋆ i)) ⟩
    lookupSV (((σ ↑) ↑⋆ i) ↑) (Vec.lookup (Vec.map suc (V.wk V.↑⋆ i)) x)
  ≡⟨⟩
    lookupSV (((σ ↑) ↑⋆ i) ↑) (suc x V./ V.wk V.↑⋆ suc i)
  ∎


----------------------------------------------------------------------
-- Predicates relating SV substitutions to variables.

data Hit : ∀ {m n} → SVSub m n → Fin m → Elim n → Set where
  here : ∀ {n} {a : Elim n} → Hit (sub a) zero a
  _↑   : ∀ {m n} {σ : SVSub m n} {x a} →
         Hit σ x a → Hit (σ ↑) (suc x) (weakenElim a)

data Miss : ∀ {m n} → SVSub m n → Fin m → Fin n → Set where
  over  : ∀ {n} {a : Elim n} {y : Fin n} → Miss (sub a) (suc y) y
  under : ∀ {m n} {σ : SVSub m n} → Miss (σ ↑) zero zero
  _↑    : ∀ {m n} {σ : SVSub m n} {x y} →
          Miss σ x y → Miss (σ ↑) (suc x) (suc y)

data Hit? {m n} (σ : SVSub m n) (x : Fin m) : Set where
  hit  : ∀ a → Hit  σ x a → Hit? σ x
  miss : ∀ y → Miss σ x y → Hit? σ x

toRes : ∀ {m n} {σ : SVSub m n} {x : Fin m} → Hit? σ x → SVRes n
toRes (hit a _)  = hit a
toRes (miss y _) = miss y

-- A version of `lookupSV' that produces a more a more informative
-- result.

hit? : ∀ {m n} (σ : SVSub m n) (x : Fin m) → Hit? σ x
hit? (sub a) zero    = hit a here
hit? (sub a) (suc x) = miss x over
hit? (σ ↑)   zero    = miss zero under
hit? (σ ↑)   (suc x) with hit? σ x
... | hit a hitP   = hit (weakenElim a) (hitP ↑)
... | miss y missP = miss (suc y) (missP ↑)

-- The two versions of lookup agree.

lookup-Hit : ∀ {m n} {σ : SVSub m n} {x : Fin m} {a : Elim n} →
             Hit σ x a → lookupSV σ x ≡ hit a
lookup-Hit here  = refl
lookup-Hit (hitP ↑) = cong weakenSVRes (lookup-Hit hitP)

lookup-Miss : ∀ {m n} {σ : SVSub m n} {x : Fin m} {y : Fin n} →
              Miss σ x y → lookupSV σ x ≡ miss y
lookup-Miss                           over      = refl
lookup-Miss                           under     = refl
lookup-Miss {σ = σ ↑} {suc x} {suc y} (missP ↑) = begin
  weakenSVRes (lookupSV σ x)  ≡⟨ cong weakenSVRes (lookup-Miss missP) ⟩
  miss (y V./ V.wk)           ≡⟨ cong miss V./-wk ⟩
  miss (suc y)                ∎

hit?-lookup : ∀ {m n} (σ : SVSub m n) (x : Fin m) →
              lookupSV σ x ≡ toRes (hit? σ x)
hit?-lookup σ x with hit? σ x
... | (hit a hitP)   = lookup-Hit hitP
... | (miss y missP) = lookup-Miss missP

-- The Hit predicate is functional.

Hit-functional₁ : ∀ {m n} {σ : SVSub m n} {x y : Fin m} {a b : Elim n} →
                  Hit σ x a → Hit σ y b → x ≡ y
Hit-functional₁ here      here      = refl
Hit-functional₁ (hitP₁ ↑) (hitP₂ ↑) = cong suc (Hit-functional₁ hitP₁ hitP₂)

Hit-functional₂ : ∀ {m n} {σ : SVSub m n} {x y : Fin m} {a b : Elim n} →
                  Hit σ x a → Hit σ y b → a ≡ b
Hit-functional₂ here      here      = refl
Hit-functional₂ (hitP₁ ↑) (hitP₂ ↑) =
  cong weakenElim (Hit-functional₂ hitP₁ hitP₂)

-- For a fixed σ, the Miss predicate is injective.

Miss-injective : ∀ {m n} {σ : SVSub m n} {x y : Fin m} {z : Fin n} →
                 Miss σ x z → Miss σ y z → x ≡ y
Miss-injective over      over      = refl
Miss-injective under     under     = refl
Miss-injective (hitP₁ ↑) (hitP₂ ↑) = cong suc (Miss-injective hitP₁ hitP₂)

-- Lifting preserves the predicates

Hit-↑⋆ : ∀ {m n} {σ : SVSub m n} {x : Fin m} {a : Elim n} i →
         Hit σ x a → Hit (σ ↑⋆ i) (i ↑ʳ x) (weakenElim⋆ i a)
Hit-↑⋆ zero    hyp = hyp
Hit-↑⋆ (suc i) hyp = (Hit-↑⋆ i hyp) ↑

Miss-↑⋆ : ∀ {m n} {σ : SVSub m n} {x : Fin m} {y : Fin n} i →
          Miss σ x y → Miss (σ ↑⋆ i) (i ↑ʳ x) (i ↑ʳ y)
Miss-↑⋆ zero    hyp = hyp
Miss-↑⋆ (suc i) hyp = (Miss-↑⋆ i hyp) ↑

Hit-↑-↑⋆ : ∀ {m n} {σ : SVSub m n} i {x a} → Hit (σ ↑⋆ i) x a →
           Hit ((σ ↑) ↑⋆ i) (lift i suc x) (a Elim/Var V.wk V.↑⋆ i)
Hit-↑-↑⋆ zero    hyp               = hyp ↑
Hit-↑-↑⋆ (suc i) (_↑ {a = a} hyp ) =
  subst (Hit _ _) (wk-commutes a) (Hit-↑-↑⋆ i hyp ↑)

Miss-↑-↑⋆ : ∀ {m n} {σ : SVSub m n} i {x y} → Miss (σ ↑⋆ i) x y →
            Miss ((σ ↑) ↑⋆ i) (lift i suc x) (lift i suc y)
Miss-↑-↑⋆ zero    hyp     = hyp ↑
Miss-↑-↑⋆ (suc i) under   = under
Miss-↑-↑⋆ (suc i) (hyp ↑) = (Miss-↑-↑⋆ i hyp) ↑

-- Yet another way to characterize hits/misses of single-variable
-- substitutions.

Hit-sub-↑⋆ : ∀ {n} {a : Elim n} i →
             Hit (sub a ↑⋆ i) (i ↑ʳ zero) (weakenElim⋆ i a)
Hit-sub-↑⋆ i = Hit-↑⋆ i here

Hit-sub-↑⋆₁ : ∀ {n} {a : Elim n} i {x b} →
              Hit (sub a ↑⋆ i) x b → x ≡ i ↑ʳ zero
Hit-sub-↑⋆₁ i hyp = Hit-functional₁ hyp (Hit-sub-↑⋆ i)

Hit-sub-↑⋆₂ : ∀ {n} {a : Elim n} i {x b} →
              Hit (sub a ↑⋆ i) x b → b ≡ weakenElim⋆ i a
Hit-sub-↑⋆₂ i hyp = Hit-functional₂ hyp (Hit-sub-↑⋆ i)

Miss-sub-↑⋆ : ∀ {n} {a : Elim n} i x → Miss (sub a ↑⋆ i) (lift i suc x) x
Miss-sub-↑⋆ zero    x       = over
Miss-sub-↑⋆ (suc i) zero    = under
Miss-sub-↑⋆ (suc i) (suc x) = Miss-sub-↑⋆ i x ↑

Miss-sub-↑⋆′ : ∀ {n} {a : Elim n} i {x} y →
               Miss (sub a ↑⋆ i) x y → x ≡ lift i suc y
Miss-sub-↑⋆′ i y hyp = Miss-injective hyp (Miss-sub-↑⋆ i y)

-- Looking up a sufficiently weakened variable will always miss.

lookup-sub-wk-↑⋆ : ∀ {n} i x {a : Elim n} →
                   lookupSV (sub a ↑⋆ i) (x V./ V.wk V.↑⋆ i) ≡ miss x
lookup-sub-wk-↑⋆ i x {a} = begin
    lookupSV (sub a ↑⋆ i) (x V./ V.wk V.↑⋆ i)
  ≡⟨ cong (lookupSV (sub a ↑⋆ i)) (V.lookup-wk-↑⋆ i x) ⟩
    lookupSV (sub a ↑⋆ i) (lift i suc x)
  ≡⟨ lookup-Miss (Miss-sub-↑⋆ i x) ⟩
    miss x
  ∎

-- A predicate for comparing variable names to naturals.
--
-- Instances of |Eq? n x| are proofs that a natural number |n| is or
-- is not "equal" to a variable name |x|.  Given two natural numbers
-- m, n and a "name" x in the interval { 0, ..., (n + 1 + m) }, "yes"
-- instances of the |Eq? n x| prove that "n = x", while "no" instances
-- prove that x is any one of the other names in the interval.
--
-- The predicate is useful for deciding whether a lookup of |x| in
-- some single-variable substitutions will lead to a hit or miss,
-- independently of the actual substitution.
--
-- NOTE. This predicate is only used in the proof of one lemma, namely
-- FOmegaInt.Kinding.Simple.EtaExpansion.Nf∈-[]-η-var.  Maybe the
-- proof of the lemma could be rewritten so as to avoid the
-- introduction of this extra predicate, but this might reduce
-- clarity.

data Eq? {m : ℕ} (n : ℕ) (x : Fin (n + suc m)) : Set where
  yes : n ↑ʳ zero ≡ x          → Eq? n x
  no  : ∀ y → lift n suc y ≡ x → Eq? n x

-- Eq? is stable w.r.t. increments.

suc-Eq? : ∀ {m n} {x : Fin (n + suc m)} → Eq? n x → Eq? (suc n) (suc x)
suc-Eq? (yes refl)  = yes refl
suc-Eq? (no y refl) = no (suc y) refl

-- A decision procedure for Eq?.

compare : ∀ {m} n (x : Fin (n + suc m)) → Eq? n x
compare zero    zero    = yes refl
compare zero    (suc x) = no x refl
compare (suc n) zero    = no zero refl
compare (suc n) (suc x) = suc-Eq? (compare n x)

-- Turn Eq? instances into Hit? instances for a given substitution.

toHit? : ∀ {m n} {a : Elim m} {x} → Eq? n x → Hit? (sub a ↑⋆ n) x
toHit? {_} {n} (yes refl)  = hit _ (Hit-sub-↑⋆ n)
toHit? {_} {n} (no y refl) = miss y (Miss-sub-↑⋆ n y)
