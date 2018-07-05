------------------------------------------------------------------------
-- Untyped hereditary substitution in Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

module FOmegaInt.Syntax.HereditarySubstitution where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (∃; _,_; _×_)
open import Data.Star using (ε)
import Data.Vec as Vec
import Data.Vec.Properties as VecProp
open import Data.List using ([]; _∷_; _++_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import FOmegaInt.Reduction.Full
open import FOmegaInt.Syntax


----------------------------------------------------------------------
-- Untyped hereditary substitution.

open Syntax
open ElimCtx hiding (_++_)

-- A specialized comparison predicate for comparing variable names.
--
-- Instances of Eq? n x are proofs that a natural number n is or is
-- not equal to a variable name x.  Given two natural numbers m, n and
-- a "name" x in the interval { 0, ..., (n + 1 + m) }, "yes" instances
-- of the (Eq? n x) predicate prove that "n = x", while "no" instances
-- prove the contrary, roughly, by exhibiting a name z ≠ x s.t. "n =
-- z".
data Eq? {m : ℕ} (n : ℕ) (x : Fin (n + suc m)) : Set where
  yes : raise n zero ≡ x       → Eq? n x
  no  : ∀ y → lift n suc y ≡ x → Eq? n x

-- Eq? is stable w.r.t. increments.
suc-Eq? : ∀ {m n} {x : Fin (n + suc m)} → Eq? n x → Eq? (suc n) (suc x)
suc-Eq? (yes refl)  = yes refl
suc-Eq? (no y refl) = no (suc y) refl

-- A decision procedure for "variable equality": compare n to x and
-- return an instance of Eq? n x.
compare : ∀ {m} n (x : Fin (n + suc m)) → Eq? n x
compare zero    zero    = yes refl
compare zero    (suc x) = no x refl
compare (suc n) zero    = no zero refl
compare (suc n) (suc x) = suc-Eq? (compare n x)

private
  -- A helper.
  suc-injective : ∀ {n} {x y : Fin n} → _≡_ {A = Fin _} (suc x) (suc y) → x ≡ y
  suc-injective refl = refl

-- The predicate Eq? n x cannot contain both "yes" and "no".
yes-≠-no : ∀ {m} n (x : Fin (n + m)) → raise n (zero {m}) ≢ lift n suc x
yes-≠-no zero    x       ()
yes-≠-no (suc n) zero    ()
yes-≠-no (suc n) (suc x) hyp = yes-≠-no n x (suc-injective hyp)

-- "lift" is injective, so "no" instances are proof-irrelevant.
lift-inj : ∀ {m} n (x y : Fin (n + m)) → lift n suc x ≡ lift n suc y → x ≡ y
lift-inj zero    x       .x      refl = refl
lift-inj (suc n) zero    zero    _    = refl
lift-inj (suc n) zero    (suc y) ()
lift-inj (suc n) (suc x) zero    ()
lift-inj (suc n) (suc x) (suc y) hyp =
  cong suc (lift-inj n x y (suc-injective hyp))

infix  10 _H↑
infixl 10 _H↑⋆_
infixl 9  _∙∙⟨_⟩_ _⌜·⌝⟨_⟩_ _↓⌜·⌝_
infixl 8 _/H_ _//H_ _Kind/H_ _Asc/H_ _E/H_

-- Suspended hereditary substitions.
--
-- A hereditary substitution consists of three data: the name of the
-- variable to be substituted (as a natural number), the substitute
-- for the variable, and the kind of the two.
--
-- TODO: explain the point of working with "suspended" hereditary
-- substitutions.
--
-- FIXME: there is some green slime in this definition, i.e. the
-- indices of the type of the constructor _←_∈_ contain computations:
-- (n + suc m) and (n + m).  This can (and does) cause problems when
-- pattern matching and could probably be avoided by changing the
-- definition (e.g. by splitting _←_∈_ into two constructors, one for
-- the base case where n = 0, and another one _↑H for the lifting case
-- where n = suc n′).
data HSub : SKind → ℕ → ℕ → Set where
  _←_∈_ : ∀ n {m} → Elim m → (k : SKind) → HSub k (n + suc m) (n + m)

-- Lift a hereditary substitution over an additional variable.
--
-- This operations corresponds to weakening in the following sence:
-- first weakening a term `a`, then applying the lifted substitution
-- `ρ H↑` corresponds to first applying the substitution directly,
-- then lifting the result.  This intuition is made precise in the
-- `wk-/H-↑` lemma below.
_H↑ : ∀ {k m n} → HSub k m n → HSub k (suc m) (suc n)
(i ← a ∈ k) H↑ = (suc i ← a ∈ k)

-- Lift a hereditary substitution over multiple additional variables.
_H↑⋆_ : ∀ {k m n} → HSub k m n → ∀ i → HSub k (i + m) (i + n)
ρ H↑⋆ zero  = ρ
ρ H↑⋆ suc n = (ρ H↑⋆ n) H↑

-- Turn a suspended hereditary substitution into an ordinary one.
toSub : ∀ {k m n} → HSub k m n → Sub Term m n
toSub (i ← a ∈ k) = sub ⌞ a ⌟ ↑⋆ i
  where open Substitution using (sub; _↑⋆_)

-- TODO: explain why there are degenerate cases.
mutual

  -- Apply a herediary substition to an elimination.
  _/H_ : ∀ {k m n} → Elim m → HSub k m n → Elim n
  var x ∙ as /H i ← b ∈ k with compare i x
  ... | yes _  = ⌜ var x / sub ⌞ b ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩ (as //H i ← b ∈ k)
                 where open Substitution using (_/_; sub; _↑⋆_)
  ... | no y _ = var y ∙ (as //H i ← b ∈ k)
  ⊥       ∙ as /H ρ = ⊥ ∙ (as //H ρ)
  ⊤       ∙ as /H ρ = ⊤ ∙ (as //H ρ)
  Π k a   ∙ as /H ρ = Π (k Kind/H ρ) (a /H ρ H↑) ∙ (as //H ρ)
  (a ⇒ b) ∙ as /H ρ = ((a /H ρ) ⇒ (b /H ρ))  ∙ (as //H ρ)
  Λ k a   ∙ as /H ρ = Λ (k Kind/H ρ) (a /H ρ H↑) ∙ (as //H ρ)
  ƛ a b   ∙ as /H ρ = ƛ (a /H ρ) (b /H ρ H↑) ∙ (as //H ρ)
  a ⊡ b   ∙ as /H ρ = (a /H ρ) ⊡ (b /H ρ)    ∙ (as //H ρ)

  -- Apply a herediary substition to a kind.
  _Kind/H_ : ∀ {k m n} → Kind Elim m → HSub k m n → Kind Elim n
  (a ⋯ b) Kind/H ρ = (a /H ρ) ⋯ (b /H ρ)
  Π j k   Kind/H ρ = Π (j Kind/H ρ) (k Kind/H ρ H↑)

  -- Apply a herediary substition to a spine.
  _//H_ : ∀ {k m n} → Spine m → HSub k m n → Spine n
  []       //H ρ = []
  (a ∷ as) //H ρ = a /H ρ ∷ as //H ρ

  -- Apply a spine to an elimination, performing β-reduction if possible.
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
  (Λ l a ∙ [])   ⌜·⌝⟨ j ⇒ k ⟩ b = a /H (0 ← b ∈ j)
  {-# CATCHALL #-}
  (a ∙ [])       ⌜·⌝⟨ j ⇒ k ⟩ b = a ∙ (b ∷ [])         -- ! unless a = var x

-- Apply a herediary substition to a kind or type ascription.
_Asc/H_ : ∀ {k m n} → ElimAsc m → HSub k m n → ElimAsc n
kd k Asc/H ρ = kd (k Kind/H ρ)
tp a Asc/H ρ = tp (a /H ρ)

-- Apply a herediary substition to a context extension.
_E/H_ : ∀ {k m n l} → CtxExt′ m l → HSub k m n → CtxExt′ n l
Γ′ E/H ρ = map′ (λ i a → a Asc/H ρ H↑⋆ i) Γ′

-- Some shorthands.

_[_∈_] : ∀ {n} → Elim (suc n) → Elim n → SKind → Elim n
a [ b ∈ k ] = a /H 0 ← b ∈ k

_Kind[_∈_] : ∀ {n} → Kind Elim (suc n) → Elim n → SKind → Kind Elim n
j Kind[ b ∈ k ] = j Kind/H 0 ← b ∈ k

_E[_∈_] : ∀ {m n} → CtxExt′ (suc m) n → Elim m → SKind → CtxExt′ m n
Γ′ E[ b ∈ k ] = map′ (λ i a → a Asc/H i ← b ∈ k) Γ′  --Γ′ E/H 0 ← b ∈ k

-- A variant of application that is reducing (only) if the first
-- argument is a type abstraction.
_↓⌜·⌝_ : ∀ {n} → Elim n → Elim n → Elim n
(a ∙ (b ∷ bs)) ↓⌜·⌝ c = (a ∙ (b ∷ bs)) ⌜·⌝ c
(Λ k a ∙ [])   ↓⌜·⌝ b = a [ b ∈ ⌊ k ⌋ ]
{-# CATCHALL #-}
(a ∙ [])       ↓⌜·⌝ b = a ∙ (b ∷ [])

-- Predicates relating suspended substitutions to variables.
--
-- A variable x is a "hit" w.r.t. a suspended hereditary substitution
-- ρ = (i ← a ∈ k) if ρ changes x, and a "miss" otherwise.  In other
-- words, "yes" instances of `Eq? i x' correspond to "hits", while
-- "no" instances correspond to "misses".

Hit : ∀ {k m n} → HSub k m n → Fin m → Set
Hit (i ← a ∈ k) x = raise i zero ≡ x

Miss : ∀ {k m n} → HSub k m n → Fin m → Fin n → Set
Miss (i ← a ∈ k) x y = lift i suc y ≡ x

data Hit? {k m n} (ρ : HSub k m n) (x : Fin m) : Set where
  yes :       Hit  ρ x   → Hit? ρ x
  no  : ∀ y → Miss ρ x y → Hit? ρ x

-- Decide whether a variable is a hit or a miss w.r.t. a given
-- hereditary substitution.
hit? : ∀ {k m n} (ρ : HSub k m n) (x : Fin m) → Hit? ρ x
hit? (i ← a ∈ k) x with compare i x
... | yes pf  = yes pf
... | no y pf = no y pf

-- Lifting preserves all of the above predicates.

↑-Hit : ∀ {k m n} (ρ : HSub k m n) {x} → Hit ρ x → Hit (ρ H↑) (suc x)
↑-Hit (i ← a ∈ k) refl = refl

↑⋆-Hit : ∀ i {k m n} {ρ : HSub k m n} {x} → Hit ρ x → Hit (ρ H↑⋆ i) (raise i x)
↑⋆-Hit zero    hit = hit
↑⋆-Hit (suc i) hit = ↑-Hit (_ H↑⋆ i) (↑⋆-Hit i hit)

↑-Miss : ∀ {k m n} (ρ : HSub k m n) {x y} → Miss ρ x y →
         Miss (ρ H↑) (suc x) (suc y)
↑-Miss (i ← a ∈ k) refl = refl

↑⋆-Miss : ∀ i {k m n} {ρ : HSub k m n} {x y} → Miss ρ x y →
          Miss (ρ H↑⋆ i) (raise i x) (raise i y)
↑⋆-Miss zero    hit = hit
↑⋆-Miss (suc i) hit = ↑-Miss (_ H↑⋆ i) (↑⋆-Miss i hit)

↑-Hit? : ∀ {k m n} (ρ : HSub k m n) {x} → Hit? ρ x → Hit? (ρ H↑) (suc x)
↑-Hit? (i ← a ∈ k) (yes refl)  = yes refl
↑-Hit? (i ← a ∈ k) (no y refl) = no (suc y) refl

↑⋆-Hit? : ∀ i {k m n} {ρ : HSub k m n} {x} → Hit? ρ x →
          Hit? (ρ H↑⋆ i) (raise i x)
↑⋆-Hit? zero    h? = h?
↑⋆-Hit? (suc i) h? = ↑-Hit? (_ H↑⋆ i) (↑⋆-Hit? i h?)

-- Lifting a substitution makes it miss the first variable.
↑-zero-Miss : ∀ {k m n} (ρ : HSub k m n) → Miss (ρ H↑) zero zero
↑-zero-Miss (i ← a ∈ k) = refl

-- We can lift the above predicates across an additional variable.

lift-↑⋆-Miss : ∀ {k m n} (ρ : HSub k m n) i x y → Miss (ρ H↑⋆ i) x y →
               Miss ((ρ H↑) H↑⋆ i) (lift i suc x) (lift i suc y)
lift-↑⋆-Miss ρ zero    x y       hyp = ↑-Miss ρ hyp
lift-↑⋆-Miss ρ (suc i) x zero    hyp with zero-helper (ρ H↑⋆ i) x hyp
  where
    zero-helper : ∀ {k m n} (ρ : HSub k m n) x → Miss (ρ H↑) x zero →
                  x ≡ zero
    zero-helper (i ← a ∈ k) .zero refl = refl
lift-↑⋆-Miss ρ (suc i) .zero zero hyp | refl = ↑-zero-Miss ((ρ H↑) H↑⋆ i)
lift-↑⋆-Miss ρ (suc i)  x (suc y) hyp with suc-helper (ρ H↑⋆ i) x y hyp
  where
    suc-helper : ∀ {k m n} (ρ : HSub k m n) x y → Miss (ρ H↑) x (suc y) →
                 ∃ λ x′ → x ≡ suc x′ × Miss ρ x′ y
    suc-helper (i ← a ∈ k) .(suc (lift i suc y)) y refl =
      lift i suc y , refl , refl
lift-↑⋆-Miss ρ (suc i) .(suc x) (suc y) hyp | x , refl , miss =
  ↑-Miss ((ρ H↑) H↑⋆ i) (lift-↑⋆-Miss ρ i x y miss)

lift-↑⋆-Hit : ∀ {k m n} (ρ : HSub k m n) i x → Hit (ρ H↑⋆ i) x →
              Hit ((ρ H↑) H↑⋆ i) (lift i suc x)
lift-↑⋆-Hit ρ zero    x    hyp = ↑-Hit ρ hyp
lift-↑⋆-Hit ρ (suc i) zero hyp = contradiction hyp (zero-helper (ρ H↑⋆ i))
  where
    zero-helper : ∀ {k m n} (ρ : HSub k m n) → ¬ Hit (ρ H↑) zero
    zero-helper (i ← a ∈ k) ()
lift-↑⋆-Hit ρ (suc i) (suc x) hyp =
  ↑-Hit ((ρ H↑) H↑⋆ i) (lift-↑⋆-Hit ρ i x (suc-helper (ρ H↑⋆ i) x hyp))
  where
    suc-helper : ∀ {k m n} (ρ : HSub k m n) x → Hit (ρ H↑) (suc x) → Hit ρ x
    suc-helper (i ← a ∈ k) .(raise i zero) refl = refl


----------------------------------------------------------------------
-- Properties of (untyped) hereditary substitution.

-- Some exact lemmas about hereditary substitutions (up to
-- α-equality).

private
  module EL = TermLikeLemmas Substitution.termLikeLemmasElim
  module KL = TermLikeLemmas Substitution.termLikeLemmasKind′

module _ where
  open P.≡-Reasoning
  open Substitution
  open SimpleCtx using (⌊_⌋Asc; kd; tp)

  -- Lifting commutes with conversion of substitutions.

  ↑-toSub : ∀ {k m n} (ρ : HSub k m n) → toSub (ρ H↑) ≡ toSub ρ ↑
  ↑-toSub (n ← a ∈ k) = refl

  ↑⋆-toSub : ∀ {k m n} i {ρ : HSub k m n} → toSub (ρ H↑⋆ i) ≡ toSub ρ ↑⋆ i
  ↑⋆-toSub zero        = refl
  ↑⋆-toSub (suc i) {ρ} = begin
    toSub (ρ H↑⋆ suc i)   ≡⟨ ↑-toSub (ρ H↑⋆ i) ⟩
    toSub (ρ H↑⋆ i) ↑     ≡⟨ cong (_↑) (↑⋆-toSub i) ⟩
    toSub ρ ↑⋆ suc i      ∎

  -- Simplified kinds are stable under application of hereditary
  -- substitutions.

  ⌊⌋-Kind/H : ∀ {k m n} (j : Kind Elim m) {ρ : HSub k m n} →
              ⌊ j Kind/H ρ ⌋ ≡ ⌊ j ⌋
  ⌊⌋-Kind/H (a ⋯ b) = refl
  ⌊⌋-Kind/H (Π j k) = cong₂ _⇒_ (⌊⌋-Kind/H j) (⌊⌋-Kind/H k)

  ⌊⌋-Asc/H : ∀ {k m n} (a : ElimAsc m) {ρ : HSub k m n} →
             ⌊ a Asc/H ρ ⌋Asc ≡ ⌊ a ⌋Asc
  ⌊⌋-Asc/H (kd k) = cong kd (⌊⌋-Kind/H k)
  ⌊⌋-Asc/H (tp a) = refl

  -- Hereditary substitutions in spines commute with concatenation.
  ++-//H : ∀ {k m n} (as bs : Spine m) {ρ : HSub k m n} →
           (as ++ bs) //H ρ ≡ as //H ρ ++ bs //H ρ
  ++-//H []       bs     = refl
  ++-//H (a ∷ as) bs {ρ} = cong (a /H ρ ∷_) (++-//H as bs)

  -- Iterated lifting corresponds to raising the variable to be
  -- substituted.
  zero-←-↑⋆ : ∀ i {n k} {a : Elim n} → (0 ← a ∈ k) H↑⋆ i ≡ (i ← a ∈ k)
  zero-←-↑⋆ zero    = refl
  zero-←-↑⋆ (suc i) = cong _H↑ (zero-←-↑⋆ i)

  -- Reducing applications of neutral terms are applications.

  var-⌜·⌝⟨⟩ : ∀ {n} {x : Fin n} as k {b} →
              var x ∙ as ⌜·⌝⟨ k ⟩ b ≡ var x ∙ as ⌜·⌝ b
  var-⌜·⌝⟨⟩ as       ★       = refl
  var-⌜·⌝⟨⟩ []       (j ⇒ k) = refl
  var-⌜·⌝⟨⟩ (a ∷ as) (j ⇒ k) = refl

  var-∙∙⟨⟩ : ∀ {n} (x : Fin n) as k bs →
             var x ∙ as ∙∙⟨ k ⟩ bs ≡ var x ∙ as ∙∙ bs
  var-∙∙⟨⟩ x as k       []       = sym (∙∙-[] _)
  var-∙∙⟨⟩ x as ★       (b ∷ bs) = refl
  var-∙∙⟨⟩ x as (j ⇒ k) (b ∷ bs) = begin
      var x ∙ as ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs
    ≡⟨ cong (_∙∙⟨ k ⟩ bs) (var-⌜·⌝⟨⟩ as (j ⇒ k)) ⟩
      var x ∙ as ⌜·⌝ b ∙∙⟨ k ⟩ bs
    ≡⟨ var-∙∙⟨⟩ x _ k bs ⟩
      var x ∙ as ∙∙ (b ∷ []) ∙∙ bs
    ≡⟨ ∙∙-++ (var x ∙ as) (b ∷ []) bs ⟩
      var x ∙ as ∙∙ (b ∷ bs)
    ∎

  -- Neutral terms headed by the first variable are stable under
  -- lifted hereditary substitutions.
  zero-/H-↑ : ∀ {k m n} as (ρ : HSub k m n) →
              var zero ∙ as /H ρ H↑ ≡ var zero ∙ (as //H ρ H↑)
  zero-/H-↑ as (i ← a ∈ k) = refl

  -- Looking up a variables in a lifted hereditary substitution
  -- results in weakening.
  suc-/H-↑ : ∀ {k m n} (ρ : HSub k m n) x →
             var∙ (suc x) /H ρ H↑ ≡ var∙ x /H ρ Elim/ wk
  suc-/H-↑ (n ← a ∈ k) x with compare n x
  suc-/H-↑ (n ← a ∈ k) ._ | yes refl  = begin
      ⌜ var (suc (raise n zero)) / sub ⌞ a ⌟ ↑⋆ (suc n) ⌝
    ≡⟨ cong ⌜_⌝ (suc-/-↑ {_} {_} {sub ⌞ a ⌟ ↑⋆ n} (raise n zero)) ⟩
      ⌜ var (raise n zero) / sub ⌞ a ⌟ ↑⋆ n / wk ⌝
    ≡⟨ ⌜⌝-/ (var (raise n zero) / sub ⌞ a ⌟ ↑⋆ n) ⟩
      ⌜ var (raise n zero) / sub ⌞ a ⌟ ↑⋆ n ⌝ Elim/ wk
    ∎
  suc-/H-↑ (n ← a ∈ k) ._ | no y refl = begin
    var∙ (suc y)         ≡⟨ cong ⌜_⌝ (sym EL.weaken-var) ⟩
    weakenElim (var∙ y)  ≡⟨ EL./-wk {t = var∙ y} ⟩
    var∙ y Elim/ wk      ∎

  raise-/H-↑⋆ : ∀ {k m n} i {ρ : HSub k m n} x →
                var∙ (raise i x) /H ρ H↑⋆ i ≡ var∙ x /H ρ Elim/ wk⋆ i
  raise-/H-↑⋆ zero    {ρ} x = sym (EL.id-vanishes (var∙ x /H ρ))
  raise-/H-↑⋆ (suc i) {ρ} x = begin
      var∙ (suc (raise i x)) /H (ρ H↑⋆ i) H↑
    ≡⟨ suc-/H-↑ (ρ H↑⋆ i) (raise i x) ⟩
      var∙ (raise i x) /H (ρ H↑⋆ i) Elim/ wk
    ≡⟨ cong (_Elim/ wk) (raise-/H-↑⋆ i x) ⟩
      var∙ x /H ρ Elim/ wk⋆ i Elim/ wk
    ≡⟨ sym (EL./-weaken (var∙ x /H ρ)) ⟩
      var∙ x /H ρ Elim/ wk⋆ (suc i)
    ∎

  -- Hereditary substitutions in variables degenerate to substitutions.

  var∙-/H-/ : ∀ {k m n} (ρ : HSub k m n) x →
              var∙ x /H ρ ≡ ⌜ var x / toSub ρ ⌝
  var∙-/H-/ (i ← a ∈ k) x  with compare i x
  var∙-/H-/ (i ← a ∈ k) x  | yes _     = refl
  var∙-/H-/ (i ← a ∈ k) ._ | no y refl = cong ⌜_⌝ (sym (lookup-sub-↑⋆ i y))

  var∙-/H-/-↑⋆ : ∀ {k m n} (ρ : HSub k m n) i x →
                 var∙ x /H ρ H↑⋆ i ≡ ⌜ var x / toSub ρ ↑⋆ i ⌝
  var∙-/H-/-↑⋆ ρ zero    x       = var∙-/H-/ ρ x
  var∙-/H-/-↑⋆ ρ (suc i) zero    = zero-/H-↑ [] (ρ H↑⋆ i)
  var∙-/H-/-↑⋆ ρ (suc i) (suc x) = begin
      var∙ (suc x) /H (ρ H↑⋆ i) H↑
    ≡⟨ suc-/H-↑ (ρ H↑⋆ i) x ⟩
      var∙ x /H (ρ H↑⋆ i) Elim/ wk
    ≡⟨ cong (_Elim/ wk) (var∙-/H-/-↑⋆ ρ i x) ⟩
      ⌜ var x / toSub ρ ↑⋆ i ⌝ Elim/ wk
    ≡⟨ sym (⌜⌝-/ (var x / toSub ρ ↑⋆ i)) ⟩
      ⌜ var x / toSub ρ ↑⋆ i / wk ⌝
    ≡⟨ cong ⌜_⌝ (sym (suc-/-↑ {_} {_} {toSub ρ ↑⋆ i} x)) ⟩
      ⌜ var (suc x) / toSub ρ ↑⋆ suc i ⌝
    ∎

  -- Hereditary substitutions applied to "yes" and "no" instances
  -- behave as intended.
  --
  -- NOTE. The reason these "obvious" lemmas are useful is that Agda
  -- cannot decide Eq? for abstract "i" nor does it know that "yes"
  -- and "no" instances of Eq? are proof-irrelevant.  So we have to
  -- prove and use these facts explicitly.

  ne-yes-/H : ∀ {m} i {b : Elim m} {as k} →
              var (raise i zero) ∙ as /H (i ← b ∈ k) ≡
                ⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩
                  (as //H i ← b ∈ k)
  ne-yes-/H {m} i with compare {m} i (raise i zero)
  ... | yes _    = refl
  ... | no y pf  = contradiction (sym pf) (yes-≠-no i y)

  ne-no-/H : ∀ {m} i (x : Fin (i + m)) {as b k} →
             var (lift i suc x) ∙ as /H (i ← b ∈ k) ≡
               var x ∙ (as //H i ← b ∈ k)
  ne-no-/H i x with compare i (lift i suc x)
  ... | yes pf  = contradiction pf (yes-≠-no i x)
  ... | no y pf = cong (λ z → var z ∙ _) (lift-inj i y x pf)

  -- The following two pairs of lemmas characterize the effect of
  -- suspended hereditary substitutions on neutral terms based on
  -- their effect on the head.  The first pair of lemmas concern cases
  -- where the head is a hit, the remaining pair those where it is a
  -- miss.  Note that the suspended hereditary substitutions remain
  -- abstract in all of the lemmas, i.e. the lemmas make no
  -- assumptions about the target variable or its substitute.  This is
  -- useful when proving properties about suspended substitutions that
  -- are themselves the result of some computation, e.g. lifted
  -- substitutions.
  --
  -- The lemmas are at the heart of the following strategy for proving
  -- properties of hereditary substitutions in neutral terms:
  --
  --  1. prove the property for variables,
  --
  --  2. perform a case distinction on whether the head of the neutral
  --     term is a hit w.r.t. the hereditary substitution (e.g. using
  --     the `hit?' decision procedure above),
  --
  --  3. use the lemmas below to prove the property extends to the
  --     neutral form in both cases.
  --
  --  For an example, see the neutral cases of the `wk-/H-↑⋆' lemma
  --  below.

  -- Hereditary substitutions that hit the head of a neutral term
  -- result in reducing applications.

  ne-/H-Hit : ∀ {k m n} x {ρ : HSub k m n} {as} → Hit ρ x →
              var x ∙ as /H ρ ≡ (var∙ x /H ρ) ∙∙⟨ k ⟩ (as //H ρ)
  ne-/H-Hit .(raise i zero) {i ← b ∈ k} {as} refl = begin
      var (raise i zero) ∙ as /H (i ← b ∈ k)
    ≡⟨ ne-yes-/H i ⟩
      ⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩ (as //H i ← b ∈ k)
    ≡⟨ cong (_∙∙⟨ k ⟩ (as //H i ← b ∈ k)) (sym (ne-yes-/H i)) ⟩
      (var∙ (raise i zero) /H i ← b ∈ k) ∙∙⟨ k ⟩ (as //H i ← b ∈ k)
    ∎

  ne-/H-↑⋆-Hit : ∀ i {k m n} x {ρ : HSub k m n} {as} → Hit ρ x →
                 var (raise i x) ∙ as /H ρ H↑⋆ i ≡
                   (var∙ x /H ρ Elim/ wk⋆ i) ∙∙⟨ k ⟩ (as //H ρ H↑⋆ i)
  ne-/H-↑⋆-Hit i {k} x {ρ} {as} hit = begin
      var (raise i x) ∙ as /H ρ H↑⋆ i
    ≡⟨ ne-/H-Hit (raise i x) (↑⋆-Hit i hit) ⟩
      (var∙ (raise i x) /H ρ H↑⋆ i) ∙∙⟨ k ⟩ (as //H ρ H↑⋆ i)
    ≡⟨ cong (_∙∙⟨ k ⟩ (as //H ρ H↑⋆ i)) (raise-/H-↑⋆ i x) ⟩
      (var∙ x /H ρ Elim/ wk⋆ i) ∙∙⟨ k ⟩ (as //H ρ H↑⋆ i)
    ∎

  -- Neutral terms are stable under hereditary substitutions that miss
  -- the head.

  ne-/H-Miss : ∀ {k m n} x y {ρ : HSub k m n} {as} → Miss ρ x y →
               var x ∙ as /H ρ ≡ var y ∙ (as //H ρ)
  ne-/H-Miss .(lift i suc y) y {i ← a ∈ _} refl = ne-no-/H i y

  ne-/H-↑⋆-Miss : ∀ i {k m n} x y {ρ : HSub k m n} {as} → Miss ρ x y →
                  var (raise i x) ∙ as /H ρ H↑⋆ i ≡
                    var (raise i y) ∙ (as //H ρ H↑⋆ i)
  ne-/H-↑⋆-Miss i x y miss =
    ne-/H-Miss (raise i x) (raise i y) (↑⋆-Miss i miss)

  -- A helper lemma which will be subsumed by the more general
  -- weakening lemma (wk-/H-↑⋆) below.
  var∙-lift-/H-↑⋆ : ∀ {k m n} (ρ : HSub k m n) i x →
                    var∙ (lift i suc x) /H (ρ H↑) H↑⋆ i ≡
                      var∙ x /H ρ H↑⋆ i Elim/ wk ↑⋆ i
  var∙-lift-/H-↑⋆ (n ← a ∈ k) i x = begin
      var∙ (lift i suc x) /H (suc n ← a ∈ k) H↑⋆ i
    ≡⟨ var∙-/H-/-↑⋆ (suc n ← a ∈ k) i (lift i suc x) ⟩
      ⌜ var (lift i suc x) / sub ⌞ a ⌟ ↑⋆ (suc n) ↑⋆ i ⌝
    ≡⟨ cong ⌜_⌝ (sym (Lemmas₂.lookup-wk-↑⋆-⊙ lemmas₂ i)) ⟩
      ⌜ var x / wk ↑⋆ i ⊙ sub ⌞ a ⌟ ↑⋆ (suc n) ↑⋆ i ⌝
    ≡⟨ cong (⌜_⌝ ∘ (var x /_)) (sym (↑⋆-distrib i)) ⟩
      ⌜ var x / (wk ⊙ sub ⌞ a ⌟ ↑⋆ (suc n)) ↑⋆ i ⌝
    ≡⟨ cong (⌜_⌝ ∘ (var x /_) ∘ (_↑⋆ i)) (sym ⊙-wk) ⟩
      ⌜ var x / (sub ⌞ a ⌟ ↑⋆ n ⊙ wk) ↑⋆ i ⌝
    ≡⟨ cong (⌜_⌝ ∘ (var x /_)) (↑⋆-distrib i) ⟩
      ⌜ var x / sub ⌞ a ⌟ ↑⋆ n ↑⋆ i ⊙ wk ↑⋆ i ⌝
    ≡⟨ cong ⌜_⌝ (/-⊙ {_} {_} {_} {sub ⌞ a ⌟ ↑⋆ n ↑⋆ i} (var x)) ⟩
      ⌜ var x / sub ⌞ a ⌟ ↑⋆ n ↑⋆ i / wk ↑⋆ i ⌝
    ≡⟨ ⌜⌝-/ (var x / sub ⌞ a ⌟ ↑⋆ n ↑⋆ i) ⟩
      ⌜ var x / sub ⌞ a ⌟ ↑⋆ n ↑⋆ i ⌝ Elim/ wk ↑⋆ i
    ≡⟨ cong (_Elim/ wk ↑⋆ i) (sym (var∙-/H-/-↑⋆ (n ← a ∈ k) i x)) ⟩
      var∙ x /H (n ← a ∈ k) H↑⋆ i Elim/ wk ↑⋆ i
    ∎

module RenamingCommutes where
  open Substitution using
    (termLikeLemmasElim; _//Var_; _Head/Var′_; _Head/Var_; _Kind′/Var_)
  open TermLikeLemmas termLikeLemmasElim
    using (varLiftAppLemmas; varLiftSubLemmas)
  open LiftAppLemmas varLiftAppLemmas hiding (lift)
  open LiftSubLemmas varLiftSubLemmas
  open LiftSubLemmas Substitution.varLiftSubLemmas using ()
    renaming (/-liftSub-↑⋆ to /Var-liftSub-↑⋆)
  open ExtLemmas₁ lemmas₁
  open P.≡-Reasoning
  private module S = Substitution

  -- A helper lemma.
  lookup-lift-↑⋆′ : ∀ {k m} n x {σ : Sub Fin m k} →
                    Vec.lookup ((σ ↑) ↑⋆ n) (lift n suc x) ≡
                      lift n suc (Vec.lookup (σ ↑⋆ n) x)
  lookup-lift-↑⋆′ zero    x       {σ} = lookup-map-weaken x {_} {σ} refl
  lookup-lift-↑⋆′ (suc n) zero        = refl
  lookup-lift-↑⋆′ (suc n) (suc x) {σ} = begin
        Vec.lookup (Vec.map suc ((σ ↑) ↑⋆ n)) (lift n suc x)
      ≡⟨ lookup-map-weaken (lift n suc x) {_} {(σ ↑) ↑⋆ n} refl ⟩
        suc (Vec.lookup ((σ ↑) ↑⋆ n) (lift n suc x))
      ≡⟨ cong suc (lookup-lift-↑⋆′ n x) ⟩
        suc (lift n suc (Vec.lookup (σ ↑⋆ n) x))
      ≡⟨ cong (lift (suc n) suc)
              (sym (lookup-map-weaken x {_} {σ ↑⋆ n} refl)) ⟩
        lift (suc n) suc (Vec.lookup (Vec.map suc (σ ↑⋆ n)) x)
      ∎

  -- TODO: could the following lemma be generalized so it also covers
  -- the case of weakening?

  mutual

    -- Hereditary substitution commutes with renaming.

    []-/-↑⋆ : ∀ i {m n} a k b {σ : Sub Fin m n} →
              b /H (i ← a ∈ k) / σ ↑⋆ i ≡ b / (σ ↑) ↑⋆ i /H (i ← a / σ ∈ k)
    []-/-↑⋆ i a k (var x ∙ bs)  {σ} with compare i x
    []-/-↑⋆ i a k (var ._ ∙ bs) {σ} | yes refl = begin
        (⌜ var x S./ S.sub ⌞ a ⌟ S.↑⋆ i ⌝ ∙∙⟨ k ⟩ (bs //H i ← a ∈ k)) / σ ↑⋆ i
      ≡⟨ ∙∙⟨⟩-/ ⌜ Vec.lookup (S.sub ⌞ a ⌟ S.↑⋆ i) x ⌝ k (bs //H i ← a ∈ k) ⟩
        (⌜ var x S./ S.sub ⌞ a ⌟ S.↑⋆ i ⌝ / σ ↑⋆ i) ∙∙⟨ k ⟩
          (bs //H i ← a ∈ k //Var σ ↑⋆ i)
      ≡⟨ cong₂ (_∙∙⟨ k ⟩_) (begin
            ⌜ var x S./ S.sub ⌞ a ⌟ S.↑⋆ i ⌝ / σ ↑⋆ i
          ≡⟨ /-liftSub-↑⋆ i ⌜ var x S./ S.sub ⌞ a ⌟ S.↑⋆ i ⌝ ⟩
            ⌜ var x S./ S.sub ⌞ a ⌟ S.↑⋆ i ⌝ S.Elim/ σ′ S.↑⋆ i
          ≡⟨ sym (S.⌜⌝-/ (var x S./ S.sub ⌞ a ⌟ S.↑⋆ i)) ⟩
            ⌜ var x S./ S.sub ⌞ a ⌟ S.↑⋆ i S./ σ′ S.↑⋆ i ⌝
          ≡⟨ cong ⌜_⌝ (sym (S./-⊙ {_} {_} {_} {S.sub ⌞ a ⌟ S.↑⋆ i} (var x))) ⟩
            ⌜ var x S./ (S.sub ⌞ a ⌟ S.↑⋆ i S.⊙ σ′ S.↑⋆ i) ⌝
          ≡⟨ cong (⌜_⌝ ∘ (var x S./_)) (sym (S.↑⋆-distrib i)) ⟩
            ⌜ var x S./ (S.sub ⌞ a ⌟ S.⊙ σ′) S.↑⋆ i ⌝
          ≡⟨ cong (⌜_⌝ ∘ (var x S./_) ∘ (S._↑⋆ i)) (S.sub-⊙ ⌞ a ⌟) ⟩
            ⌜ var x S./ (σ′ S.↑ S.⊙ S.sub (⌞ a ⌟ S./ σ′)) S.↑⋆ i ⌝
          ≡⟨ cong (λ b → ⌜ var x S./ (σ′ S.↑ S.⊙ S.sub b) S.↑⋆ i ⌝)
                  (sym (S.⌞⌟-/ a)) ⟩
            ⌜ var x S./ (σ′ S.↑ S.⊙ S.sub ⌞ a S.Elim/ σ′ ⌟) S.↑⋆ i ⌝
          ≡⟨ cong (λ b → ⌜ var x S./ (σ′ S.↑ S.⊙ S.sub ⌞ b ⌟) S.↑⋆ i ⌝)
                   (sym (/-liftSub-↑⋆ zero a)) ⟩
            ⌜ var x S./ (σ′ S.↑ S.⊙ S.sub ⌞ a / σ ⌟) S.↑⋆ i ⌝
          ≡⟨ cong (⌜_⌝ ∘ (var x S./_)) (S.↑⋆-distrib i) ⟩
            ⌜ var x S./ (σ′ S.↑ S.↑⋆ i S.⊙ S.sub ⌞ a / σ ⌟ S.↑⋆ i) ⌝
          ≡⟨ cong ⌜_⌝ (S./-⊙ {_} {_} {_} {σ′ S.↑ S.↑⋆ i} (var x)) ⟩
            ⌜ var x S./ (σ′ S.↑) S.↑⋆ i S./ S.sub ⌞ a / σ ⌟ S.↑⋆ i ⌝
          ≡⟨ cong (⌜_⌝ ∘ (S._/ S.sub ⌞ a / σ ⌟ S.↑⋆ i))
                  (ExtLemmas₁.lookup-raise-↑⋆ S.lemmas₁ i zero refl) ⟩
            ⌜ var (raise i zero) S./ S.sub ⌞ a / σ ⌟ S.↑⋆ i ⌝
          ∎) ([]Sp-/-↑⋆ i a k bs) ⟩
        ⌜ var (raise i zero) S./ S.sub ⌞ a / σ ⌟ S.↑⋆ i ⌝ ∙∙⟨ k ⟩
          (bs //Var (σ ↑) ↑⋆ i //H (i ← a / σ ∈ k))
      ≡⟨ sym (ne-yes-/H i) ⟩
        var (raise i zero) ∙ (bs //Var (σ ↑) ↑⋆ i) /H (i ← a / σ ∈ k)
      ≡⟨ cong (λ z → ⌜ var z ⌝ ∙∙ (bs //Var (σ ↑) ↑⋆ i) /H (i ← a / σ ∈ k))
              (sym (lookup-raise-↑⋆ i zero refl)) ⟩
        (var∙ x / (σ ↑) ↑⋆ i) ∙∙ (bs //Var (σ ↑) ↑⋆ i) /H (i ← a / σ ∈ k)
      ∎
      where
        x  = raise i zero
        σ′ = liftSub σ
    []-/-↑⋆ i a k (var ._ ∙ bs) {σ} | no y₁ refl = begin
        var y₁ ∙ (bs //H (i ← a ∈ k)) / σ ↑⋆ i
      ≡⟨ cong (var y₂ ∙_) ([]Sp-/-↑⋆ i a k bs) ⟩
        var y₂ ∙ (bs //Var (σ ↑) ↑⋆ i //H (i ← a / σ ∈ k))
      ≡⟨ sym (ne-no-/H i y₂) ⟩
        (var (lift i suc y₂) ∙ (bs //Var (σ ↑) ↑⋆ i)) /H (i ← a / σ ∈ k)
      ≡⟨ cong ((_/H (i ← a / σ ∈ k)) ∘ (_∙ (bs //Var (σ ↑) ↑⋆ i)) ∘ var)
              (sym (lookup-lift-↑⋆′ i y₁)) ⟩
        var (lift i suc y₁) ∙ bs / (σ ↑) ↑⋆ i /H (i ← a / σ ∈ k)
      ∎
      where y₂ = Vec.lookup (σ ↑⋆ i) y₁
    []-/-↑⋆ i a k (⊥     ∙ bs)   = cong (⊥ ∙_) ([]Sp-/-↑⋆ i a k bs)
    []-/-↑⋆ i a k (⊤     ∙ bs)   = cong (⊤ ∙_) ([]Sp-/-↑⋆ i a k bs)
    []-/-↑⋆ i a k (Π j b ∙ bs)   =
      cong₂ _∙_ (cong₂ Π ([]Kd-/-↑⋆ i a k j) ([]-/-↑⋆ (suc i) a k b))
                ([]Sp-/-↑⋆ i a k bs)
    []-/-↑⋆ i a k ((b ⇒ c) ∙ bs) =
      cong₂ _∙_ (cong₂ _⇒_ ([]-/-↑⋆ i a k b) ([]-/-↑⋆ i a k c))
                ([]Sp-/-↑⋆ i a k bs)
    []-/-↑⋆ i a k (Λ j b ∙ bs)   =
      cong₂ _∙_ (cong₂ Λ ([]Kd-/-↑⋆ i a k j) ([]-/-↑⋆ (suc i) a k b))
                ([]Sp-/-↑⋆ i a k bs)
    []-/-↑⋆ i a k (ƛ b c ∙ bs)   =
      cong₂ _∙_ (cong₂ ƛ ([]-/-↑⋆ i a k b) ([]-/-↑⋆ (suc i) a k c))
                ([]Sp-/-↑⋆ i a k bs)
    []-/-↑⋆ i a k (b ⊡ c ∙ bs)   =
      cong₂ _∙_ (cong₂ _⊡_ ([]-/-↑⋆ i a k b) ([]-/-↑⋆ i a k c))
                ([]Sp-/-↑⋆ i a k bs)

    []Kd-/-↑⋆ : ∀ i {m n} a k j {σ : Sub Fin m n} →
                j Kind/H (i ← a ∈ k) Kind′/Var σ ↑⋆ i ≡
                  j Kind′/Var (σ ↑) ↑⋆ i Kind/H (i ← a / σ ∈ k)
    []Kd-/-↑⋆ i a k (b ⋯ c) =
      cong₂ _⋯_ ([]-/-↑⋆ i a k b) ([]-/-↑⋆ i a k c)
    []Kd-/-↑⋆ i a k (Π j l) =
      cong₂ Π ([]Kd-/-↑⋆ i a k j) ([]Kd-/-↑⋆ (suc i) a k l)

    []Sp-/-↑⋆ : ∀ i {n m} a k bs {σ : Sub Fin m n} →
                bs //H (i ← a ∈ k) //Var σ ↑⋆ i ≡
                  (bs //Var (σ ↑) ↑⋆ i) //H (i ← a / σ ∈ k)
    []Sp-/-↑⋆ i a k []       = refl
    []Sp-/-↑⋆ i a k (b ∷ bs) = cong₂ _∷_ ([]-/-↑⋆ i a k b) ([]Sp-/-↑⋆ i a k bs)

    -- Reducing applications commute with renaming.

    ∙∙⟨⟩-/ : ∀ {m n} a k bs {σ : Sub Fin m n} →
             a ∙∙⟨ k ⟩ bs / σ ≡ (a / σ) ∙∙⟨ k ⟩ (bs //Var σ)
    ∙∙⟨⟩-/ a k       []           = refl
    ∙∙⟨⟩-/ a ★       (b ∷ bs)     = S.∙∙-/Var a (b ∷ bs)
    ∙∙⟨⟩-/ a (j ⇒ k) (b ∷ bs) {σ} = begin
        a ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs / σ
      ≡⟨ ∙∙⟨⟩-/ (a ⌜·⌝⟨ j ⇒ k ⟩ b) k bs ⟩
        (a ⌜·⌝⟨ j ⇒ k ⟩ b / σ) ∙∙⟨ k ⟩ (bs //Var σ)
      ≡⟨ cong (_∙∙⟨ k ⟩ (bs //Var σ)) (⌜·⌝⟨⟩-/ a (j ⇒ k) b) ⟩
        (a / σ) ⌜·⌝⟨ j ⇒ k ⟩ (b / σ) ∙∙⟨ k ⟩ (bs //Var σ)
      ∎

    ⌜·⌝⟨⟩-/ : ∀ {m n} a k b {σ : Sub Fin m n} →
              a ⌜·⌝⟨ k ⟩ b / σ ≡ (a / σ) ⌜·⌝⟨ k ⟩ (b / σ)
    ⌜·⌝⟨⟩-/ a ★                    b     = S.⌜·⌝-/Var a b
    ⌜·⌝⟨⟩-/ (a ∙ (c ∷ cs)) (j ⇒ k) b {σ} = begin
        a ∙ (c ∷ cs) ⌜·⌝ b / σ
      ≡⟨ S.⌜·⌝-/Var (a ∙ (c ∷ cs)) b ⟩
        (a ∙ (c ∷ cs) / σ) ⌜·⌝ (b / σ)
      ≡⟨ sym (cong (λ a → a ∙∙ _ ⌜·⌝ (b / σ)) (S.Head/Var-∙ a)) ⟩
        (a Head/Var σ) ∙ ((c ∷ cs) //Var σ) ⌜·⌝⟨ j ⇒ k ⟩ (b / σ)
      ≡⟨ cong (λ a → a ∙∙ _ ⌜·⌝⟨ j ⇒ k ⟩ (b / σ)) (S.Head/Var-∙ a) ⟩
        (a ∙ (c ∷ cs) / σ) ⌜·⌝⟨ j ⇒ k ⟩ (b / σ)
      ∎
    ⌜·⌝⟨⟩-/ (var x   ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/ (⊥       ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/ (⊤       ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/ (Π l a   ∙ []) (j ⇒ k) b = refl
    ⌜·⌝⟨⟩-/ ((a ⇒ b) ∙ []) (j ⇒ k) c = refl
    ⌜·⌝⟨⟩-/ (Λ l a   ∙ []) (j ⇒ k) b = []-/-↑⋆ 0 b j a
    ⌜·⌝⟨⟩-/ (ƛ a b   ∙ []) (j ⇒ k) c = refl
    ⌜·⌝⟨⟩-/ (a ⊡ b   ∙ []) (j ⇒ k) c = refl

  -- Some corollaries of the above.

  []Asc-/-↑⋆ : ∀ i {m n} a k b {σ : Sub Fin m n} →
               b Asc/H (i ← a ∈ k) S.ElimAsc/Var σ ↑⋆ i ≡
                 b S.ElimAsc/Var (σ ↑) ↑⋆ i Asc/H (i ← a / σ ∈ k)
  []Asc-/-↑⋆ i a k (kd j) = cong kd ([]Kd-/-↑⋆ i a k j)
  []Asc-/-↑⋆ i a k (tp b) = cong tp ([]-/-↑⋆ i a k b)

  [∈⌊⌋]-/ : ∀ {m n} a b k {σ : Sub Fin m n} →
            a [ b ∈ ⌊ k ⌋ ] / σ ≡ (a / σ ↑) [ b / σ ∈ ⌊ k Kind′/Var σ ⌋ ]
  [∈⌊⌋]-/ a b k {σ} = begin
      a [ b ∈ ⌊ k ⌋ ] / σ
    ≡⟨ []-/-↑⋆ 0 b ⌊ k ⌋ a ⟩
      a / σ ↑ /H 0 ← b / σ ∈ ⌊ k ⌋
    ≡⟨ cong ((a / σ ↑ /H_) ∘ (0 ← b / σ ∈_)) (sym (S.⌊⌋-Kind′/Var k)) ⟩
      (a / σ ↑) [ b / σ ∈ ⌊ k Kind′/Var σ ⌋ ]
    ∎

  Kind[∈⌊⌋]-/ : ∀ {m n} j a k {σ : Sub Fin m n} →
                j Kind[ a ∈ ⌊ k ⌋ ] Kind′/Var σ ≡
                  (j Kind′/Var σ ↑) Kind[ a / σ ∈ ⌊ k Kind′/Var σ ⌋ ]
  Kind[∈⌊⌋]-/ j a k {σ} = begin
      j Kind[ a ∈ ⌊ k ⌋ ] Kind′/Var σ
    ≡⟨ []Kd-/-↑⋆ 0 a ⌊ k ⌋ j ⟩
      j Kind′/Var σ ↑ Kind/H 0 ← a / σ ∈ ⌊ k ⌋
    ≡⟨ cong ((j Kind′/Var σ ↑ Kind/H_) ∘ (0 ← a / σ ∈_))
            (sym (S.⌊⌋-Kind′/Var k)) ⟩
      (j Kind′/Var σ ↑) Kind[ a / σ ∈ ⌊ k Kind′/Var σ ⌋ ]
    ∎

  -- Potentially reducing applications commute with renaming.

  ↓⌜·⌝-/ : ∀ {m n} a b {σ : Sub Fin m n} →
           a ↓⌜·⌝ b / σ ≡ (a / σ) ↓⌜·⌝ (b / σ)
  ↓⌜·⌝-/ (a ∙ (c ∷ cs)) b {σ} = begin
      a ∙ (c ∷ cs) ⌜·⌝ b / σ
    ≡⟨ S.⌜·⌝-/Var (a ∙ (c ∷ cs)) b ⟩
      (a ∙ (c ∷ cs) / σ) ⌜·⌝ (b / σ)
    ≡⟨ sym (cong (λ a → a ∙∙ _ ⌜·⌝ (b / σ)) (S.Head/Var-∙ a)) ⟩
      (a Head/Var σ) ∙ ((c ∷ cs) //Var σ) ↓⌜·⌝ (b / σ)
    ≡⟨ cong (λ a → a ∙∙ _ ↓⌜·⌝ (b / σ)) (S.Head/Var-∙ a) ⟩
      (a ∙ (c ∷ cs) / σ) ↓⌜·⌝ (b / σ)
    ∎
  ↓⌜·⌝-/ (var x   ∙ []) b = refl
  ↓⌜·⌝-/ (⊥       ∙ []) b = refl
  ↓⌜·⌝-/ (⊤       ∙ []) b = refl
  ↓⌜·⌝-/ (Π l a   ∙ []) b = refl
  ↓⌜·⌝-/ ((a ⇒ b) ∙ []) c = refl
  ↓⌜·⌝-/ (Λ l a   ∙ []) b {σ} = begin
      (a [ b ∈ ⌊ l ⌋ ]) / σ
    ≡⟨ []-/-↑⋆ 0 b ⌊ l ⌋ a ⟩
      (a / σ ↑) [ b / σ ∈ ⌊ l ⌋ ]
    ≡⟨ cong (λ k → (a / σ ↑) [ b / σ ∈ k ]) (sym (S.⌊⌋-Kind′/Var l)) ⟩
      (a / σ ↑) [ b / σ ∈ ⌊ l Kind′/Var σ ⌋ ]
    ∎
  ↓⌜·⌝-/ (ƛ a b   ∙ []) c = refl
  ↓⌜·⌝-/ (a ⊡ b   ∙ []) c = refl

  mutual

    -- Weakening commutes with application of lifted hereditary
    -- substitutions.

    wk-/H-↑⋆ : ∀ i {k m n} a {ρ : HSub k m n} →
               a / wk ↑⋆ i /H (ρ H↑) H↑⋆ i ≡ a /H ρ H↑⋆ i / wk ↑⋆ i
    wk-/H-↑⋆ i {k} (var x ∙ as) {ρ} with hit? (ρ H↑⋆ i) x
    ... | yes hit = begin
        var x ∙ as / wk ↑⋆ i /H (ρ H↑) H↑⋆ i
      ≡⟨ cong ((_/H (ρ H↑) H↑⋆ i) ∘ (_∙∙ (as //Var wk ↑⋆ i)) ∘ var∙)
              (lookup-wk-↑⋆ i x) ⟩
        var (lift i suc x) ∙ (as //Var wk ↑⋆ i) /H (ρ H↑) H↑⋆ i
      ≡⟨ ne-/H-Hit (lift i suc x) (lift-↑⋆-Hit ρ i x hit) ⟩
        (var∙ (lift i suc x) /H (ρ H↑) H↑⋆ i)
          ∙∙⟨ k ⟩ (as //Var wk ↑⋆ i //H (ρ H↑) H↑⋆ i)
      ≡⟨ cong₂ _∙∙⟨ k ⟩_ (begin
            var∙ (lift i suc x) /H (ρ H↑) H↑⋆ i
          ≡⟨ var∙-lift-/H-↑⋆ ρ i x ⟩
            var∙ x /H ρ H↑⋆ i S.Elim/ S.wk S.↑⋆ i
          ≡⟨ sym (/-wk-↑⋆ i {t = var∙ x /H ρ H↑⋆ i}) ⟩
            var∙ x /H ρ H↑⋆ i / wk ↑⋆ i
          ∎) (wk-//H-↑⋆ i as) ⟩
        (var∙ x /H ρ H↑⋆ i / wk ↑⋆ i) ∙∙⟨ k ⟩ (as //H ρ H↑⋆ i //Var wk ↑⋆ i)
      ≡⟨ sym (∙∙⟨⟩-/ (var∙ x /H ρ H↑⋆ i) k (as //H ρ H↑⋆ i)) ⟩
        (var∙ x /H ρ H↑⋆ i) ∙∙⟨ k ⟩ (as //H ρ H↑⋆ i) / wk ↑⋆ i
      ≡⟨ cong (_/ wk ↑⋆ i) (sym (ne-/H-Hit x hit)) ⟩
        var x ∙ as /H ρ H↑⋆ i / wk ↑⋆ i
      ∎
    ... | no y miss = begin
        var x ∙ as / wk ↑⋆ i /H (ρ H↑) H↑⋆ i
      ≡⟨ cong ((_/H (ρ H↑) H↑⋆ i) ∘ (_∙∙ (as //Var wk ↑⋆ i)) ∘ var∙)
              (lookup-wk-↑⋆ i x) ⟩
        var (lift i suc x) ∙ (as //Var wk ↑⋆ i) /H (ρ H↑) H↑⋆ i
      ≡⟨ ne-/H-Miss (lift i suc x) (lift i suc y) (lift-↑⋆-Miss ρ i x y miss) ⟩
        var (lift i suc y) ∙ (as //Var wk ↑⋆ i //H (ρ H↑) H↑⋆ i)
      ≡⟨ cong₂ _∙∙_ (cong var∙ (sym (lookup-wk-↑⋆ i y))) (wk-//H-↑⋆ i as) ⟩
        var y ∙ (as //H ρ H↑⋆ i) / wk ↑⋆ i
      ≡⟨ cong (_/ wk ↑⋆ i) (sym (ne-/H-Miss x y miss)) ⟩
        var x ∙ as /H ρ H↑⋆ i / wk ↑⋆ i
      ∎
    wk-/H-↑⋆ i (⊥ ∙ as)       = cong (⊥ ∙_) (wk-//H-↑⋆ i as)
    wk-/H-↑⋆ i (⊤ ∙ as)       = cong (⊤ ∙_) (wk-//H-↑⋆ i as)
    wk-/H-↑⋆ i (Π k a ∙ as)   =
      cong₂ _∙_ (cong₂ Π (wk-Kind/H-↑⋆ i k) (wk-/H-↑⋆ (suc i) a))
                (wk-//H-↑⋆ i as)
    wk-/H-↑⋆ i ((a ⇒ b) ∙ as) =
      cong₂ _∙_ (cong₂ _⇒_ (wk-/H-↑⋆ i a) (wk-/H-↑⋆ i b)) (wk-//H-↑⋆ i as)
    wk-/H-↑⋆ i (Λ k a ∙ as)   =
      cong₂ _∙_ (cong₂ Λ (wk-Kind/H-↑⋆ i k) (wk-/H-↑⋆ (suc i) a))
                (wk-//H-↑⋆ i as)
    wk-/H-↑⋆ i (ƛ a b ∙ as)   =
      cong₂ _∙_ (cong₂ ƛ (wk-/H-↑⋆ i a) (wk-/H-↑⋆ (suc i) b)) (wk-//H-↑⋆ i as)
    wk-/H-↑⋆ i (a ⊡ b ∙ as)   =
      cong₂ _∙_ (cong₂ _⊡_ (wk-/H-↑⋆ i a) (wk-/H-↑⋆ i b)) (wk-//H-↑⋆ i as)


    wk-Kind/H-↑⋆ : ∀ i {k m n} j {ρ : HSub k m n} →
                   j Kind′/Var wk ↑⋆ i Kind/H (ρ H↑) H↑⋆ i ≡
                     j Kind/H ρ H↑⋆ i Kind′/Var wk ↑⋆ i
    wk-Kind/H-↑⋆ i (a ⋯ b) = cong₂ _⋯_ (wk-/H-↑⋆ i a) (wk-/H-↑⋆ i b)
    wk-Kind/H-↑⋆ i (Π j k) =
      cong₂ Π (wk-Kind/H-↑⋆ i j) (wk-Kind/H-↑⋆ (suc i) k)

    wk-//H-↑⋆ : ∀ i {k m n} as {ρ : HSub k m n} →
                as //Var wk ↑⋆ i //H (ρ H↑) H↑⋆ i ≡
                  as //H ρ H↑⋆ i //Var wk ↑⋆ i
    wk-//H-↑⋆ i []       = refl
    wk-//H-↑⋆ i (a ∷ as) = cong₂ _∷_ (wk-/H-↑⋆ i a) (wk-//H-↑⋆ i as)

  -- A corollary of the above.
  wk-Asc/H-↑⋆ : ∀ i {k m n} a {ρ : HSub k m n} →
                a S.ElimAsc/Var wk ↑⋆ i Asc/H (ρ H↑) H↑⋆ i ≡
                  a Asc/H ρ H↑⋆ i S.ElimAsc/Var wk ↑⋆ i
  wk-Asc/H-↑⋆ i (kd a) = cong kd (wk-Kind/H-↑⋆ i a)
  wk-Asc/H-↑⋆ i (tp a) = cong tp (wk-/H-↑⋆ i a)

  mutual

    -- Weakening of a term followed by hereditary substitution of the
    -- newly introduced extra variable leaves the term unchanged.

    /-wk-↑⋆-hsub-vanishes : ∀ i {k m} a {b : Elim m} →
                            a / wk ↑⋆ i /H i ← b ∈ k ≡ a
    /-wk-↑⋆-hsub-vanishes i {k} (var x ∙ as) {b} = begin
        var x ∙ as / wk ↑⋆ i /H i ← b ∈ k
      ≡⟨ cong (λ y → var y ∙ (as //Var wk ↑⋆ i) /H i ← b ∈ k)
              (lookup-wk-↑⋆ i x) ⟩
        var (lift i suc x) ∙ (as //Var wk ↑⋆ i) /H i ← b ∈ k
      ≡⟨ ne-no-/H i x ⟩
        var x ∙ (as //Var wk ↑⋆ i //H i ← b ∈ k)
      ≡⟨ cong (var x ∙_) (//-wk-↑⋆-hsub-vanishes i as) ⟩
        var x ∙ as
      ∎
    /-wk-↑⋆-hsub-vanishes i (⊥ ∙ as)       =
      cong (⊥ ∙_) (//-wk-↑⋆-hsub-vanishes i as)
    /-wk-↑⋆-hsub-vanishes i (⊤ ∙ as)       =
      cong (⊤ ∙_) (//-wk-↑⋆-hsub-vanishes i as)
    /-wk-↑⋆-hsub-vanishes i (Π k a ∙ as)   =
      cong₂ _∙_ (cong₂ Π (Kind/-wk-↑⋆-hsub-vanishes i k)
                         (/-wk-↑⋆-hsub-vanishes (suc i) a))
                (//-wk-↑⋆-hsub-vanishes i as)
    /-wk-↑⋆-hsub-vanishes i ((a ⇒ b) ∙ as) =
      cong₂ _∙_ (cong₂ _⇒_ (/-wk-↑⋆-hsub-vanishes i a)
                           (/-wk-↑⋆-hsub-vanishes i b))
                (//-wk-↑⋆-hsub-vanishes i as)
    /-wk-↑⋆-hsub-vanishes i (Λ k a ∙ as)   =
      cong₂ _∙_ (cong₂ Λ (Kind/-wk-↑⋆-hsub-vanishes i k)
                         (/-wk-↑⋆-hsub-vanishes (suc i) a))
                (//-wk-↑⋆-hsub-vanishes i as)
    /-wk-↑⋆-hsub-vanishes i (ƛ a b ∙ as)   =
      cong₂ _∙_ (cong₂ ƛ (/-wk-↑⋆-hsub-vanishes i a)
                           (/-wk-↑⋆-hsub-vanishes (suc i) b))
                (//-wk-↑⋆-hsub-vanishes i as)
    /-wk-↑⋆-hsub-vanishes i (a ⊡ b ∙ as)   =
      cong₂ _∙_ (cong₂ _⊡_ (/-wk-↑⋆-hsub-vanishes i a)
                           (/-wk-↑⋆-hsub-vanishes i b))
                (//-wk-↑⋆-hsub-vanishes i as)

    Kind/-wk-↑⋆-hsub-vanishes : ∀ i {k m} j {b : Elim m} →
                                j Kind′/Var wk ↑⋆ i Kind/H i ← b ∈ k ≡ j
    Kind/-wk-↑⋆-hsub-vanishes i (a ⋯ b) =
      cong₂ _⋯_ (/-wk-↑⋆-hsub-vanishes i a) (/-wk-↑⋆-hsub-vanishes i b)
    Kind/-wk-↑⋆-hsub-vanishes i (Π j k) =
      cong₂ Π (Kind/-wk-↑⋆-hsub-vanishes i j)
              (Kind/-wk-↑⋆-hsub-vanishes (suc i) k)

    //-wk-↑⋆-hsub-vanishes : ∀ i {k m} as {b : Elim m} →
                             as //Var wk ↑⋆ i //H i ← b ∈ k ≡ as
    //-wk-↑⋆-hsub-vanishes i []       = refl
    //-wk-↑⋆-hsub-vanishes i (a ∷ as) =
      cong₂ _∷_ (/-wk-↑⋆-hsub-vanishes i a) (//-wk-↑⋆-hsub-vanishes i as)

  -- A corollary of the above.
  Asc/-wk-↑⋆-hsub-vanishes : ∀ i {k m} a {b : Elim m} →
                             a S.ElimAsc/Var wk ↑⋆ i Asc/H i ← b ∈ k ≡ a
  Asc/-wk-↑⋆-hsub-vanishes i (kd a) =
    cong kd (Kind/-wk-↑⋆-hsub-vanishes i a)
  Asc/-wk-↑⋆-hsub-vanishes i (tp a) =
    cong tp (/-wk-↑⋆-hsub-vanishes i a)

open RenamingCommutes

module _ where
  open Substitution
  open ≡-Reasoning

  -- Repeated weakening commutes with application of lifted hereditary
  -- substitutions.

  wk⋆-/H-↑⋆ : ∀ i {k m n} a {ρ : HSub k m n} →
              a Elim/ wk⋆ i /H ρ H↑⋆ i ≡ a /H ρ Elim/ wk⋆ i
  wk⋆-/H-↑⋆ zero a {ρ} = begin
    a Elim/ id /H ρ   ≡⟨ cong (_/H ρ) (EL.id-vanishes a) ⟩
    a /H ρ            ≡⟨ sym (EL.id-vanishes (a /H ρ)) ⟩
    a /H ρ Elim/ id   ∎
  wk⋆-/H-↑⋆ (suc i) a {ρ} = begin
      a Elim/ wk⋆ (suc i) /H (ρ H↑⋆ i) H↑
    ≡⟨ cong (_/H (ρ H↑⋆ i) H↑) (EL./-weaken a) ⟩
      a Elim/ wk⋆ i Elim/ wk /H (ρ H↑⋆ i) H↑
    ≡⟨ cong (_/H (ρ H↑⋆ i) H↑) (sym (EL./-wk {t = a Elim/ wk⋆ i})) ⟩
      weakenElim (a Elim/ wk⋆ i) /H (ρ H↑⋆ i) H↑
    ≡⟨ wk-/H-↑⋆ zero (a Elim/ wk⋆ i) ⟩
      weakenElim (a Elim/ wk⋆ i /H ρ H↑⋆ i)
    ≡⟨ cong weakenElim (wk⋆-/H-↑⋆ i a) ⟩
      weakenElim (a /H ρ Elim/ wk⋆ i)
    ≡⟨ (EL./-wk {t = a /H ρ Elim/ wk⋆ i}) ⟩
      a /H ρ Elim/ wk⋆ i Elim/ wk
    ≡⟨ sym (EL./-weaken (a /H ρ))  ⟩
      a /H ρ Elim/ wk⋆ (suc i)
    ∎

  wk⋆-Kind/H-↑⋆ : ∀ i {k m n} j {ρ : HSub k m n} →
                  j Kind′/ wk⋆ i Kind/H ρ H↑⋆ i ≡ j Kind/H ρ Kind′/ wk⋆ i
  wk⋆-Kind/H-↑⋆ zero j {ρ} = begin
    j Kind′/ id Kind/H ρ   ≡⟨ cong (_Kind/H ρ) (KL.id-vanishes j) ⟩
    j Kind/H ρ             ≡⟨ sym (KL.id-vanishes (j Kind/H ρ)) ⟩
    j Kind/H ρ Kind′/ id   ∎
  wk⋆-Kind/H-↑⋆ (suc i) j {ρ} = begin
      j Kind′/ wk⋆ (suc i) Kind/H (ρ H↑⋆ i) H↑
    ≡⟨ cong (_Kind/H (ρ H↑⋆ i) H↑) (KL./-weaken j) ⟩
      j Kind′/ wk⋆ i Kind′/ wk Kind/H (ρ H↑⋆ i) H↑
    ≡⟨ cong (_Kind/H (ρ H↑⋆ i) H↑) (sym (KL./-wk {t = j Kind′/ wk⋆ i})) ⟩
      weakenKind′ (j Kind′/ wk⋆ i) Kind/H (ρ H↑⋆ i) H↑
    ≡⟨ wk-Kind/H-↑⋆ zero (j Kind′/ wk⋆ i) ⟩
      weakenKind′ (j Kind′/ wk⋆ i Kind/H ρ H↑⋆ i)
    ≡⟨ cong weakenKind′ (wk⋆-Kind/H-↑⋆ i j) ⟩
      weakenKind′ (j Kind/H ρ Kind′/ wk⋆ i)
    ≡⟨ (KL./-wk {t = j Kind/H ρ Kind′/ wk⋆ i}) ⟩
      j Kind/H ρ Kind′/ wk⋆ i Kind′/ wk
    ≡⟨ sym (KL./-weaken (j Kind/H ρ))  ⟩
      j Kind/H ρ Kind′/ wk⋆ (suc i)
    ∎

  -- Context lookup commutes with hereditary substitution.
  lookup-E[] : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} a k x →
               lookup x (Γ₂ E[ a ∈ ⌊ k ⌋ ] ′++ Γ₁)  ≡
                 lookup (lift n suc x) (Γ₂ ′++ kd k ∷ Γ₁) Asc/H n ← a ∈ ⌊ k ⌋
  lookup-E[] {m} {n} Γ₂ {Γ₁} a k x = begin
      lookup x (Γ₂ E[ a ∈ ⌊ k ⌋ ] ′++ Γ₁)
    ≡⟨ lookup-′++ x [] (Γ₂ E[ a ∈ ⌊ k ⌋ ]) Γ₁ ⟩
      extLookup′ x (toVec Γ₁) (Γ₂ E[ a ∈ ⌊ k ⌋ ])
    ≡⟨ lookup′-lift x (kd k) (toVec Γ₁) (Γ₂ E[ a ∈ ⌊ k ⌋ ]) ⟩
      extLookup′ (lift n suc x) (kd k ∷ toVec Γ₁) (Γ₂ E[ a ∈ ⌊ k ⌋ ])
    ≡⟨ cong (λ ts → extLookup′ (lift n suc x) ts (Γ₂ E[ a ∈ ⌊ k ⌋ ])) (begin
          kd k ∷ toVec Γ₁
        ≡⟨ sym (map-id (kd k ∷ toVec Γ₁)) ⟩
          Vec.map Function.id (kd k ∷ toVec Γ₁)
        ≡⟨ sym (map-cong (λ a → Asc/-wk-↑⋆-hsub-vanishes 0 a)
               (kd k ∷ toVec Γ₁)) ⟩
          Vec.map ((_Asc/H (0 ← a ∈ ⌊ k ⌋)) ∘ weakenElimAsc)
                  (kd k ∷ toVec Γ₁)
        ≡⟨ map-∘ (_Asc/H (0 ← a ∈ ⌊ k ⌋)) weakenElimAsc (kd k ∷ toVec Γ₁) ⟩
          Vec.map (_Asc/H (0 ← a ∈ ⌊ k ⌋)) (toVec (kd k ∷ Γ₁))
        ∎) ⟩
      extLookup′ (lift n suc x)
                 (Vec.map (_Asc/H 0 ← a ∈ ⌊ k ⌋) (toVec (kd k ∷ Γ₁)))
                 (Γ₂ E[ a ∈ ⌊ k ⌋ ])
    ≡⟨ lookup′-map′ (lift n suc x) (λ i → _Asc/H i ← a ∈ ⌊ k ⌋)
                    (toVec (kd k ∷ Γ₁)) Γ₂ (λ a → sym (wk-Asc/H-↑⋆ 0 a)) ⟩
      extLookup′ (lift n suc x) (toVec (kd k ∷ Γ₁)) Γ₂ Asc/H n ← a ∈ ⌊ k ⌋
    ≡⟨ cong (_Asc/H _) (sym (lookup-′++ (lift n suc x) [] Γ₂ (kd k ∷ Γ₁))) ⟩
      lookup (lift n suc x) (Γ₂ ′++ kd k ∷ Γ₁) Asc/H n ← a ∈ ⌊ k ⌋
    ∎
    where
      open Vec     using ([]; _∷_)
      open VecProp using (map-cong; map-id; map-∘)

  -- NOTE. Unfortunately, we cannot prove that arbitrary untyped
  -- hereditary substitutions commute, because *untyped* hereditary
  -- substitutions need not commute with reducting applications
  -- (i.e. the lemmas `∙∙⟨⟩-/H-↑⋆' and `⌜·⌝⟨⟩-/H-↑⋆' do not hold in
  -- that general case).  We will prove a weaker result, namely that
  -- well-kinded hereditary substitutions in well-kinded types
  -- commute, later.  See e.g. `Nf∈-[]-/H-↑⋆` etc. in module
  -- Kinding.Simple.

-- Some commutation lemmas up to βη-equality.

module _ where
  open →β*-Reasoning
  open Kd→β*-Reasoning renaming
    ( begin_  to beginKd_
    ; _∎      to _∎Kd
    ; _⟶⟨_⟩_  to _Kd→⟨_⟩_
    ; _⟶⋆⟨_⟩_ to _Kd→*⟨_⟩_
    ; _≡⟨_⟩_  to _Kd≡⟨_⟩_
    )
  open Substitution hiding (subst)

  mutual

    -- Hereditary substitution commutes with ⌞_⌟ up to β-reduction.
    --
    -- FIXME: remove superfluous parentheses once agda-stdlib issue
    -- #814 has been fixed.

    ⌞⌟-[]-β : ∀ {m} n a k (b : Elim (n + suc m)) →
              ⌞ b ⌟ / sub ⌞ a ⌟ ↑⋆ n  →β*  ⌞ b /H n ← a ∈ k ⌟
    ⌞⌟-[]-β n a k (var x ∙ bs) with compare n x
    ⌞⌟-[]-β n a k (var .(raise n zero) ∙ bs) | yes refl = begin
        ⌞ var z ∙ bs ⌟ / (sub ⌞ a ⌟ ↑⋆ n)
      ⟶⋆⟨ ⌞∙⌟-[]-β n a k (var z / sub ⌞ a ⌟ ↑⋆ n) (var z) bs ε ⟩
        (var z / sub ⌞ a ⌟ ↑⋆ n) ⌞∙⌟ ⌞ bs //H n ← a ∈ k ⌟Sp
      ≡⟨ cong (_⌞∙⌟ ⌞ bs //H n ← a ∈ k ⌟Sp)
              (sym (⌞⌟∘⌜⌝-id (var z / sub ⌞ a ⌟ ↑⋆ n))) ⟩
        ⌞ ⌜ var z / sub ⌞ a ⌟ ↑⋆ n ⌝ ⌟ ⌞∙⌟ ⌞ bs //H n ← a ∈ k ⌟Sp
      ⟶⋆⟨ ⌞⌟-∙∙-β ⌜ var z / sub ⌞ a ⌟ ↑⋆ n ⌝ k (bs //H n ← a ∈ k) ⟩
        ⌞ ⌜ var z / sub ⌞ a ⌟ ↑⋆ n ⌝ ∙∙⟨ k ⟩ (bs //H n ← a ∈ k) ⌟
      ∎
      where z = raise n zero
    ⌞⌟-[]-β n a k (var .(lift n suc y) ∙ bs) | no y refl = begin
        ⌞ var z ∙ bs ⌟ / sub ⌞ a ⌟ ↑⋆ n
      ⟶⋆⟨ ⌞∙⌟-[]-β n a k (var z / sub ⌞ a ⌟ ↑⋆ n) (var z) bs ε ⟩
        (var z / sub ⌞ a ⌟ ↑⋆ n) ⌞∙⌟ ⌞ bs //H n ← a ∈ k ⌟Sp
      ≡⟨ cong (λ c →  c ⌞∙⌟ ⌞ bs //H n ← a ∈ k ⌟Sp) (lookup-sub-↑⋆ n y) ⟩
        ⌞ var y ∙ (bs //H n ← a ∈ k) ⌟
      ∎
      where z = lift n suc y
    ⌞⌟-[]-β n a k (⊥ ∙ bs) = ⌞∙⌟-[]-β n a k ⊥ ⊥ bs ε
    ⌞⌟-[]-β n a k (⊤ ∙ bs) = ⌞∙⌟-[]-β n a k ⊤ ⊤ bs ε
    ⌞⌟-[]-β n a k (Π j b ∙ bs) = ⌞∙⌟-[]-β n a k _ _ bs (begin
        (⌞ Π j b ⌟Hd / sub ⌞ a ⌟ ↑⋆ n)
      ⟶⋆⟨ →β*-Π (⌞⌟Kd-[]-β n a k j) (⌞⌟-[]-β (suc n) a k b) ⟩
        Π ⌞ j Kind/H n ← a ∈ k ⌟Kd ⌞ b /H suc n ← a ∈ k ⌟
      ∎)
    ⌞⌟-[]-β n a k ((b ⇒ c) ∙ bs) = ⌞∙⌟-[]-β n a k _ _ bs (begin
        (⌞ b ⇒ c ⌟Hd / sub ⌞ a ⌟ ↑⋆ n)
      ⟶⋆⟨ →β*-⇒ (⌞⌟-[]-β n a k b) (⌞⌟-[]-β n a k c) ⟩
        ⌞ b /H n ← a ∈ k ⌟ ⇒ ⌞ c /H n ← a ∈ k ⌟
      ∎)
    ⌞⌟-[]-β n a k (Λ j b ∙ bs) = ⌞∙⌟-[]-β n a k _ _ bs (begin
        (⌞ Λ j b ⌟Hd / sub ⌞ a ⌟ ↑⋆ n)
      ⟶⋆⟨ →β*-Λ (⌞⌟Kd-[]-β n a k j) (⌞⌟-[]-β (suc n) a k b) ⟩
        Λ ⌞ j Kind/H n ← a ∈ k ⌟Kd ⌞ b /H suc n ← a ∈ k ⌟
      ∎)
    ⌞⌟-[]-β n a k (ƛ c b ∙ bs) = ⌞∙⌟-[]-β n a k _ _ bs (begin
        (⌞ ƛ c b ⌟Hd / sub ⌞ a ⌟ ↑⋆ n)
      ⟶⋆⟨ →β*-ƛ (⌞⌟-[]-β n a k c) (⌞⌟-[]-β (suc n) a k b) ⟩
        ƛ ⌞ c /H n ← a ∈ k ⌟ ⌞ b /H suc n ← a ∈ k ⌟
      ∎)
    ⌞⌟-[]-β n a k (b ⊡ c ∙ bs) = ⌞∙⌟-[]-β n a k _ _ bs (begin
        (⌞ b ⊡ c ⌟Hd / sub ⌞ a ⌟ ↑⋆ n)
      ⟶⋆⟨ →β*-⊡ (⌞⌟-[]-β n a k b) (⌞⌟-[]-β n a k c) ⟩
        ⌞ b /H n ← a ∈ k ⌟ ⊡ ⌞ c /H n ← a ∈ k ⌟
      ∎)

    ⌞⌟Kd-[]-β : ∀ {m} n a k (j : Kind Elim (n + suc m)) →
                ⌞ j ⌟Kd Kind/ sub ⌞ a ⌟ ↑⋆ n  Kd→β*  ⌞ j Kind/H n ← a ∈ k ⌟Kd
    ⌞⌟Kd-[]-β n a k (b ⋯ c) = beginKd
        (⌞ b ⋯ c ⌟Kd Kind/ sub ⌞ a ⌟ ↑⋆ n)
      Kd→*⟨ Kd→β*-⋯ (⌞⌟-[]-β n a k b) (⌞⌟-[]-β n a k c) ⟩
        ⌞ b /H n ← a ∈ k ⌟ ⋯ ⌞ c /H n ← a ∈ k ⌟
      ∎Kd
    ⌞⌟Kd-[]-β n a k (Π j l) = beginKd
        (⌞ Π j l ⌟Kd Kind/ sub ⌞ a ⌟ ↑⋆ n)
      Kd→*⟨ Kd→β*-Π (⌞⌟Kd-[]-β n a k j) (⌞⌟Kd-[]-β (suc n) a k l) ⟩
        Π ⌞ j Kind/H n ← a ∈ k ⌟Kd ⌞ l Kind/H (suc n) ← a ∈ k ⌟Kd
      ∎Kd

    ⌞∙⌟-[]-β : ∀ {m} n a k b₁ b₂ (bs : Spine (n + suc m)) →
               b₂ / sub ⌞ a ⌟ ↑⋆ n →β* b₁ →
               (b₂ ⌞∙⌟ ⌞ bs ⌟Sp) / sub ⌞ a ⌟ ↑⋆ n  →β*
                 b₁ ⌞∙⌟ ⌞ bs //H n ← a ∈ k ⌟Sp
    ⌞∙⌟-[]-β n a k b₁ b₂ []       hyp = hyp
    ⌞∙⌟-[]-β n a k b₁ b₂ (c ∷ cs) hyp =
      ⌞∙⌟-[]-β n a k (b₁ · ⌞ c /H n ← a ∈ k ⌟) (b₂ · ⌞ c ⌟) cs
               (→β*-· hyp (⌞⌟-[]-β n a k c))

    -- Reducing applications commute with ⌞_⌟ up to β-reduction.

    ⌞⌟-∙∙-β : ∀ {n} (a : Elim n) k bs → ⌞ a ⌟ ⌞∙⌟ ⌞ bs ⌟Sp →β* ⌞ a ∙∙⟨ k ⟩ bs ⌟
    ⌞⌟-∙∙-β a k       []       = ε
    ⌞⌟-∙∙-β a ★       (b ∷ bs) = begin
      ⌞ a ⌟ ⌞∙⌟ (⌞ b ⌟ ∷ ⌞ bs ⌟Sp) ≡⟨ sym (⌞⌟-∙∙ a (b ∷ bs)) ⟩
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
      ⌞ a ⌟ · ⌞ b ⌟              ≡⟨ sym (⌞⌟-· a b) ⟩
      ⌞ a ⌜·⌝ b ⌟                ∎
    ⌞⌟-⌜·⌝-β (a ∙ (c ∷ cs)) (j ⇒ k) b = begin
      ⌞ a ∙ (c ∷ cs) ⌟ · ⌞ b ⌟   ≡⟨ sym (⌞⌟-· (a ∙ (c ∷ cs)) b) ⟩
      ⌞ a ∙ (c ∷ cs) ⌜·⌝ b ⌟     ∎
    ⌞⌟-⌜·⌝-β (var x   ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β (⊥       ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β (⊤       ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β (Π l a   ∙ []) (j ⇒ k) b = ε
    ⌞⌟-⌜·⌝-β ((a ⇒ b) ∙ []) (j ⇒ k) c = ε
    ⌞⌟-⌜·⌝-β (Λ l a ∙ []) (j ⇒ k) b = begin
      Λ ⌞ l ⌟Kd ⌞ a ⌟ · ⌞ b ⌟    ⟶⟨ ⌈ cont-Tp· ⌞ l ⌟Kd ⌞ a ⌟ ⌞ b ⌟ ⌉ ⟩
      (⌞ a ⌟ [ ⌞ b ⌟ ]           ⟶⋆⟨ ⌞⌟-[]-β 0 b j a ⟩
      ⌞ a /H 0 ← b ∈ j ⌟         ∎)
    ⌞⌟-⌜·⌝-β (ƛ a b   ∙ []) (j ⇒ k) c = ε
    ⌞⌟-⌜·⌝-β (a ⊡ b   ∙ []) (j ⇒ k) c = ε

  -- Potentially reducing applications commute with ⌞_⌟ up to β-reduction.
  --
  -- FIXME: remove superfluous parentheses once agda-stdlib issue #814
  -- has been fixed.
  ⌞⌟-↓⌜·⌝-β : ∀ {n} (a : Elim n) b → ⌞ a ⌟ · ⌞ b ⌟ →β* ⌞ a ↓⌜·⌝ b ⌟
  ⌞⌟-↓⌜·⌝-β (a ∙ (c ∷ cs)) b = begin
    ⌞ a ∙ (c ∷ cs) ⌟ · ⌞ b ⌟   ≡⟨ sym (⌞⌟-· (a ∙ (c ∷ cs)) b) ⟩
    ⌞ a ∙ (c ∷ cs) ⌜·⌝ b ⌟     ∎
  ⌞⌟-↓⌜·⌝-β (var x   ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β (⊥       ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β (⊤       ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β (Π l a   ∙ []) b = ε
  ⌞⌟-↓⌜·⌝-β ((a ⇒ b) ∙ []) c = ε
  ⌞⌟-↓⌜·⌝-β (Λ l a ∙ []) b = begin
    Λ ⌞ l ⌟Kd ⌞ a ⌟ · ⌞ b ⌟    ⟶⟨ ⌈ cont-Tp· ⌞ l ⌟Kd ⌞ a ⌟ ⌞ b ⌟ ⌉ ⟩
    (⌞ a ⌟ [ ⌞ b ⌟ ]           ⟶⋆⟨ ⌞⌟-[]-β 0 b ⌊ l ⌋ a ⟩
    ⌞ a /H 0 ← b ∈ ⌊ l ⌋ ⌟     ∎)
  ⌞⌟-↓⌜·⌝-β (ƛ a b   ∙ []) c = ε
  ⌞⌟-↓⌜·⌝-β (a ⊡ b   ∙ []) c = ε
