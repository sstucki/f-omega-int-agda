------------------------------------------------------------------------
-- The untyped SKI combinator calculus
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Undecidable.SK where

open import Data.Bool
open import Data.Product as Prod using (_,_; ∃; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality


------------------------------------------------------------------------
-- The untyped SK(I) combinator calculus

infixl 9 _·_
infixl 4 _≡SK_ _≤SK?_ _⇛[_]_ _⇛[_]*_ _⇛≤_ _⇛≤*_ _⇛≥_ _⇛≥*_ _⇛≤*≤⇚_

-- Terms of the SK combinator calculus.

data SKTerm : Set where
  S   : SKTerm
  K   : SKTerm
  _·_ : SKTerm → SKTerm → SKTerm

-- Equality of SK terms.

data _≡SK_ : SKTerm → SKTerm → Set where
  ≡-refl  : ∀ {t}     → t ≡SK t
  ≡-trans : ∀ {s t u} → s ≡SK t → t ≡SK u → s ≡SK u
  ≡-sym   : ∀ {s t}   → s ≡SK t → t ≡SK s
  ≡-Sred  : ∀ {s t u} → S · s · t · u ≡SK s · u · (t · u)
  ≡-Kred  : ∀ {s t}   →     K · s · t ≡SK s
  ≡-·     : ∀ {s₁ s₂ t₁ t₂} →
            s₁ ≡SK s₂ → t₁ ≡SK t₂ → s₁ · t₁ ≡SK s₂ · t₂

-- A well-known encoding of the I combinator.

I : SKTerm
I = S · K · K

-- Some admissible equality rules.

≡-Ired : ∀ {t} → I · t ≡SK t
≡-Ired = ≡-trans ≡-Sred ≡-Kred

≡-Sexp : ∀ {s t u} → s · u · (t · u) ≡SK S · s · t · u
≡-Sexp = ≡-sym ≡-Sred

≡-Kexp : ∀ {s t} → s ≡SK K · s · t
≡-Kexp = ≡-sym ≡-Kred

≡-Iexp : ∀ {t} → t ≡SK I · t
≡-Iexp = ≡-sym ≡-Ired


------------------------------------------------------------------------
-- A variant of the untyped SK calculus with extra term formers

data SK?Term : Set where
  ⊥   : SK?Term                                 -- degenerate term
  ⊤   : SK?Term                                 -- degenerate term
  S   : SK?Term
  K   : SK?Term
  _·_ : SK?Term → SK?Term → SK?Term

-- An SK? term is pure if it is an SK term.

data Pure : SK?Term → Set where
  S    : Pure S
  K    : Pure K
  _·_  : ∀ {s t} → Pure s → Pure t → Pure (s · t)

-- A partial order on SK? terms that resembles subtyping.

data _≤SK?_ : SK?Term → SK?Term → Set where
  ≤?-refl  : ∀ {t} → t ≤SK? t
  ≤?-trans : ∀ {s t u} → s ≤SK? t → t ≤SK? u → s ≤SK? u
  ≤?-⊥     : ∀ {t} → ⊥ ≤SK? t
  ≤?-⊤     : ∀ {t} → t ≤SK? ⊤
  ≤?-Sred  : ∀ {s t u} →   S · s · t · u ≤SK? s · u · (t · u)
  ≤?-Kred  : ∀ {s t}   →       K · s · t ≤SK? s
  ≤?-Sexp  : ∀ {s t u} → s · u · (t · u) ≤SK? S · s · t · u
  ≤?-Kexp  : ∀ {s t}   →               s ≤SK? K · s · t
  ≤?-·     : ∀ {s₁ s₂ t₁ t₂} →
             s₁ ≤SK? s₂ → t₁ ≤SK? t₂ → s₁ · t₁ ≤SK? s₂ · t₂

-- Parallel one-step and multi-step reduction of SK? terms, possibly
-- containing instances of ⊥-elim and ⊤-intro.
--
-- The `i' index in `_⇛[ i ]_' indicates whether the relation is
-- increasing (true) or decreasing (false).  The increasing
-- single/multi-step relations are (strict) subrelations of _≤SK?_,
-- while the decreasing ones are subrelations of _≥SK?_ (i.e. the
-- inverse of _≤SK?_).

data _⇛[_]_ : SK?Term → Bool → SK?Term → Set where
  ⇛-refl : ∀ {t i} → t ⇛[ i ] t
  ⇛-Sred : ∀ {s₁ s₂ t₁ t₂ u₁ u₂ i} →
           s₁ ⇛[ i ] s₂ → t₁ ⇛[ i ] t₂ → u₁ ⇛[ i ] u₂ →
           S · s₁ · t₁ · u₁ ⇛[ i ] s₂ · u₂ · (t₂ · u₂)
  ⇛-Kred : ∀ {s₁ s₂ t i} → s₁ ⇛[ i ] s₂ → K · s₁ · t ⇛[ i ] s₂
  ⇛-·    : ∀ {s₁ s₂ t₁ t₂ i} →
           s₁ ⇛[ i ] s₂ → t₁ ⇛[ i ] t₂ → s₁ · t₁ ⇛[ i ] s₂ · t₂
  ⇛-⊥    : ∀ {t} → ⊥ ⇛[ true  ] t
  ⇛-⊤    : ∀ {t} → ⊤ ⇛[ false ] t

_⇛[_]*_ : SK?Term → Bool → SK?Term → Set
s ⇛[ i ]* t = (Star _⇛[ i ]_) s t

_⇛≤_ : SK?Term → SK?Term → Set
_⇛≤_ = _⇛[ true ]_

_⇛≤*_ : SK?Term → SK?Term → Set
_⇛≤*_ = _⇛[ true ]*_

_⇛≥_ : SK?Term → SK?Term → Set
_⇛≥_ = _⇛[ false ]_

_⇛≥*_ : SK?Term → SK?Term → Set
_⇛≥*_ = _⇛[ false ]*_

-- A combination of the two multi-step reductions that is equivalent
-- to _≤SK?_ modulo "squashing" of intermediate terms (see ≤SK?--⇛≤*≤⇚
-- below).

_⇛≤*≤⇚_ : SK?Term → SK?Term → Set
s ⇛≤*≤⇚ t = ∃ λ u → s ⇛≤* u × t ⇛≥* u

-- SK terms are SK? terms

inject : SKTerm → SK?Term
inject S       = S
inject K       = K
inject (s · t) = inject s · inject t

inject-Pure : ∀ t → Pure (inject t)
inject-Pure S = S
inject-Pure K = K
inject-Pure (s · t) = inject-Pure s · inject-Pure t

-- The inverse of inject on pure terms.

inject⁻¹ : ∀ {t} → Pure t → SKTerm
inject⁻¹ S       = S
inject⁻¹ K       = K
inject⁻¹ (p · q) = inject⁻¹ p · inject⁻¹ q

inject⁻¹-inject-Pure : ∀ t → inject⁻¹ (inject-Pure t) ≡ t
inject⁻¹-inject-Pure S       = refl
inject⁻¹-inject-Pure K       = refl
inject⁻¹-inject-Pure (s · t) =
  cong₂ _·_ (inject⁻¹-inject-Pure s) (inject⁻¹-inject-Pure t)

inject⁻¹-unique : ∀ {t} → (p q : Pure t) → inject⁻¹ p ≡ inject⁻¹ q
inject⁻¹-unique S         S         = refl
inject⁻¹-unique K         K         = refl
inject⁻¹-unique (p₁ · p₂) (q₁ · q₂) =
  cong₂ _·_ (inject⁻¹-unique p₁ q₁) (inject⁻¹-unique p₂ q₂)

-- Equality of SK terms is a subrelation of the SK? term order and its
-- inverse.

mutual

  ≡SK-≤SK? : ∀ {s t} → s ≡SK t → inject s ≤SK? inject t
  ≡SK-≤SK? ≡-refl            = ≤?-refl
  ≡SK-≤SK? (≡-trans s≡t t≡u) = ≤?-trans (≡SK-≤SK? s≡t) (≡SK-≤SK? t≡u)
  ≡SK-≤SK? (≡-sym s≡t)       = ≡SK-≥SK? s≡t
  ≡SK-≤SK? ≡-Sred            = ≤?-Sred
  ≡SK-≤SK? ≡-Kred            = ≤?-Kred
  ≡SK-≤SK? (≡-· s₁≡t₁ s₂≡t₂) = ≤?-· (≡SK-≤SK? s₁≡t₁) (≡SK-≤SK? s₂≡t₂)

  ≡SK-≥SK? : ∀ {s t} → s ≡SK t → inject t ≤SK? inject s
  ≡SK-≥SK? ≡-refl            = ≤?-refl
  ≡SK-≥SK? (≡-trans s≡t t≡u) = ≤?-trans (≡SK-≥SK? t≡u) (≡SK-≥SK? s≡t)
  ≡SK-≥SK? (≡-sym s≡t)       = ≡SK-≤SK? s≡t
  ≡SK-≥SK? ≡-Sred            = ≤?-Sexp
  ≡SK-≥SK? ≡-Kred            = ≤?-Kexp
  ≡SK-≥SK? (≡-· s₁≡t₁ s₂≡t₂) = ≤?-· (≡SK-≥SK? s₁≡t₁) (≡SK-≥SK? s₂≡t₂)

-- Admissible constructors for multi-step reduction

⇛*-· : ∀ {ab s₁ s₂ t₁ t₂} →
       s₁ ⇛[ ab ]* s₂ → t₁ ⇛[ ab ]* t₂ → s₁ · t₁ ⇛[ ab ]* s₂ · t₂
⇛*-· ε ε                = ε
⇛*-· ε (t₁⇛t₂ ◅ t₂⇛*t₃) = (⇛-· ⇛-refl t₁⇛t₂) ◅ (⇛*-· ε t₂⇛*t₃)
⇛*-· (s₁⇛s₂ ◅ s₂⇛*s₃) ε = (⇛-· s₁⇛s₂ ⇛-refl) ◅ (⇛*-· s₂⇛*s₃ ε)
⇛*-· (s₁⇛s₂ ◅ s₂⇛*s₃) (t₁⇛t₂ ◅ t₂⇛*t₃) = (⇛-· s₁⇛s₂ t₁⇛t₂) ◅ (⇛*-· s₂⇛*s₃ t₂⇛*t₃)

-- A Church-Rosser theorem for SK? reductions.

⇛-CR : ∀ {s t₁ t₂} → s ⇛≤ t₁ → s ⇛≥ t₂ → ∃ λ u → t₁ ⇛≥ u × t₂ ⇛≤ u
⇛-CR ⇛-refl s⇛t₂ = _ , s⇛t₂ , ⇛-refl
⇛-CR (⇛-Sred s₁⇛t₁₁ s₂⇛t₂₁ s₃⇛t₃₁) (⇛-Sred s₁⇛t₁₂ s₂⇛t₂₂ s₃⇛t₃₂) =
  let u₁ , t₁₁⇛u₁ , t₁₂⇛u₁ = ⇛-CR s₁⇛t₁₁ s₁⇛t₁₂
      u₂ , t₂₁⇛u₂ , t₂₂⇛u₂ = ⇛-CR s₂⇛t₂₁ s₂⇛t₂₂
      u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  u₁ · u₃ · (u₂ · u₃) ,
      ⇛-· (⇛-· t₁₁⇛u₁ t₃₁⇛u₃)  (⇛-· t₂₁⇛u₂ t₃₁⇛u₃) ,
      ⇛-· (⇛-· t₁₂⇛u₁  t₃₂⇛u₃) (⇛-· t₂₂⇛u₂ t₃₂⇛u₃)
⇛-CR (⇛-Sred s₁⇛t₁₁ s₂⇛t₂₁ s₃⇛t₃₁) (⇛-· ⇛-refl s₃⇛t₃₂) =
  let u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  _ · u₃ · (_ · u₃) ,
      ⇛-· (⇛-· ⇛-refl t₃₁⇛u₃) (⇛-· ⇛-refl t₃₁⇛u₃) ,
      ⇛-Sred s₁⇛t₁₁ s₂⇛t₂₁ t₃₂⇛u₃
⇛-CR (⇛-Sred s₁⇛t₁₁ s₂⇛t₂₁ s₃⇛t₃₁) (⇛-· (⇛-· ⇛-refl s₂⇛t₂₂) s₃⇛t₃₂) =
  let u₂ , t₂₁⇛u₂ , t₂₂⇛u₂ = ⇛-CR s₂⇛t₂₁ s₂⇛t₂₂
      u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  _ · u₃ · (u₂ · u₃) ,
      ⇛-· (⇛-· ⇛-refl t₃₁⇛u₃) (⇛-· t₂₁⇛u₂ t₃₁⇛u₃) ,
      ⇛-Sred s₁⇛t₁₁ t₂₂⇛u₂ t₃₂⇛u₃
⇛-CR (⇛-Sred s₁⇛t₁₁ s₂⇛t₂₁ s₃⇛t₃₁)
     (⇛-· (⇛-· (⇛-· ⇛-refl s₁⇛t₁₂) s₂⇛t₂₂) s₃⇛t₃₂) =
  let u₁ , t₁₁⇛u₁ , t₁₂⇛u₁ = ⇛-CR s₁⇛t₁₁ s₁⇛t₁₂
      u₂ , t₂₁⇛u₂ , t₂₂⇛u₂ = ⇛-CR s₂⇛t₂₁ s₂⇛t₂₂
      u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  u₁ · u₃ · (u₂ · u₃) ,
      ⇛-· (⇛-· t₁₁⇛u₁ t₃₁⇛u₃)  (⇛-· t₂₁⇛u₂ t₃₁⇛u₃) ,
      ⇛-Sred t₁₂⇛u₁ t₂₂⇛u₂ t₃₂⇛u₃
⇛-CR (⇛-Kred s⇛t₁) (⇛-Kred s⇛t₂) =
  let u , t₁⇛u , t₂⇛u = ⇛-CR s⇛t₁ s⇛t₂
  in  u , t₁⇛u , t₂⇛u
⇛-CR (⇛-Kred s₁⇛t₁₁) (⇛-· ⇛-refl _) = _ , ⇛-refl , ⇛-Kred s₁⇛t₁₁
⇛-CR (⇛-Kred s₁⇛t₁₁) (⇛-· (⇛-· ⇛-refl s₁⇛t₂₁) _) =
  let u₁ , t₁₁⇛u₁ , t₂₁⇛u₁ = ⇛-CR s₁⇛t₁₁ s₁⇛t₂₁
  in  u₁ , t₁₁⇛u₁ , ⇛-Kred t₂₁⇛u₁
⇛-CR (⇛-· ⇛-refl s₃⇛t₃₁) (⇛-Sred s₁⇛t₁₂ s₂⇛t₂₂ s₃⇛t₃₂) =
  let u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  _ · u₃ · (_ · u₃) ,
      ⇛-Sred s₁⇛t₁₂ s₂⇛t₂₂ t₃₁⇛u₃ ,
      ⇛-· (⇛-· ⇛-refl t₃₂⇛u₃) (⇛-· ⇛-refl t₃₂⇛u₃)
⇛-CR (⇛-· (⇛-· ⇛-refl s₂⇛t₂₁) s₃⇛t₃₁) (⇛-Sred s₁⇛t₁₂ s₂⇛t₂₂ s₃⇛t₃₂) =
  let u₂ , t₂₁⇛u₂ , t₂₂⇛u₂ = ⇛-CR s₂⇛t₂₁ s₂⇛t₂₂
      u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  _ · u₃ · (u₂ · u₃) ,
      ⇛-Sred s₁⇛t₁₂ t₂₁⇛u₂ t₃₁⇛u₃ ,
      ⇛-· (⇛-· ⇛-refl t₃₂⇛u₃) (⇛-· t₂₂⇛u₂ t₃₂⇛u₃)
⇛-CR (⇛-· (⇛-· (⇛-· ⇛-refl s₁⇛t₁₁) s₂⇛t₂₁) s₃⇛t₃₁)
     (⇛-Sred s₁⇛t₁₂ s₂⇛t₂₂ s₃⇛t₃₂) =
  let u₁ , t₁₁⇛u₁ , t₁₂⇛u₁ = ⇛-CR s₁⇛t₁₁ s₁⇛t₁₂
      u₂ , t₂₁⇛u₂ , t₂₂⇛u₂ = ⇛-CR s₂⇛t₂₁ s₂⇛t₂₂
      u₃ , t₃₁⇛u₃ , t₃₂⇛u₃ = ⇛-CR s₃⇛t₃₁ s₃⇛t₃₂
  in  u₁ · u₃ · (u₂ · u₃) ,
      ⇛-Sred t₁₁⇛u₁ t₂₁⇛u₂ t₃₁⇛u₃ ,
      ⇛-· (⇛-· t₁₂⇛u₁ t₃₂⇛u₃)  (⇛-· t₂₂⇛u₂ t₃₂⇛u₃)
⇛-CR (⇛-· ⇛-refl _) (⇛-Kred s₁⇛t₂₁) =
  _ , ⇛-Kred s₁⇛t₂₁ , ⇛-refl
⇛-CR (⇛-· (⇛-· ⇛-refl s₁⇛t₁₁) _) (⇛-Kred s₁⇛t₂₁) =
  let u₁ , t₁₁⇛u₁ , t₂₁⇛u₁ = ⇛-CR s₁⇛t₁₁ s₁⇛t₂₁
  in  u₁ , ⇛-Kred t₁₁⇛u₁ , t₂₁⇛u₁
{-# CATCHALL #-}
⇛-CR (⇛-· s₁⇛t₁₁ s₂⇛t₂₁) (⇛-· s₁⇛t₁₂ s₂⇛t₂₂) =
  let u₁ , t₁₁⇛u₁ , t₁₂⇛u₁ = ⇛-CR s₁⇛t₁₁ s₁⇛t₁₂
      u₂ , t₂₁⇛u₂ , t₂₂⇛u₂ = ⇛-CR s₂⇛t₂₁ s₂⇛t₂₂
  in  u₁ · u₂ , ⇛-· t₁₁⇛u₁ t₂₁⇛u₂ , ⇛-· t₁₂⇛u₁ t₂₂⇛u₂
{-# CATCHALL #-}
⇛-CR s⇛t₁ ⇛-refl = _ , ⇛-refl , s⇛t₁

⇛-⇛*-CR : ∀ {s t₁ t₂} → s ⇛≤ t₁ → s ⇛≥* t₂ → ∃ λ u → t₁ ⇛≥* u × t₂ ⇛≤ u
⇛-⇛*-CR s⇛≤t  ε                 = _ , ε , s⇛≤t
⇛-⇛*-CR s⇛≤u₁ (s⇛≥t₁ ◅ t₁⇛≥*t₂) =
  let u₂ , u₁⇛≥u₂  , t₁⇛≤u₂ = ⇛-CR    s⇛≤u₁  s⇛≥t₁
      u₃ , u₂⇛≥*u₃ , t₂⇛≤u₃ = ⇛-⇛*-CR t₁⇛≤u₂ t₁⇛≥*t₂
  in  u₃ , u₁⇛≥u₂ ◅ u₂⇛≥*u₃ , t₂⇛≤u₃

⇛*-CR : ∀ {s t₁ t₂} → s ⇛≤* t₁ → s ⇛≥* t₂ → ∃ λ u → t₁ ⇛≥* u × t₂ ⇛≤* u
⇛*-CR ε                 s⇛≥*t  = _ , s⇛≥*t , ε
⇛*-CR (s⇛≤t₁ ◅ t₁⇛≤*t₂) s⇛≥*u₁ =
  let u₂ , t₁⇛≥*u₂ , u₁⇛≤u₂  = ⇛-⇛*-CR s⇛≤t₁   s⇛≥*u₁
      u₃ , t₂⇛≥*u₃ , u₂⇛≤*u₃ = ⇛*-CR   t₁⇛≤*t₂ t₁⇛≥*u₂
  in  u₃ , t₂⇛≥*u₃ , u₁⇛≤u₂ ◅ u₂⇛≤*u₃

-- Thanks to Church-Rosser, thee combined multi-step reduction is
-- transitive.

⇛≤*≤⇚-trans : ∀ {s t u} → s ⇛≤*≤⇚ t → t ⇛≤*≤⇚ u → s ⇛≤*≤⇚ u
⇛≤*≤⇚-trans (v , s⇛≤*v , t⇛≥*v) (w , t⇛≤*w , u⇛≥*w) =
  let u′ , w⇛≥*u′ , v⇛≤*u′ = ⇛*-CR t⇛≤*w t⇛≥*v
  in u′ , (s⇛≤*v ◅◅ v⇛≤*u′ , u⇛≥*w ◅◅ w⇛≥*u′)

-- The order on SK? terms is a subrelation of the combined multi-step
-- reduction (modulo squashing).
--
-- The two orders are in fact equivalent, but we don't need that
-- result here, so we omit its proof.  Instead we will establish that
-- the two relations are both equivalent to _≡SK_ on pure SK terms
-- (see inject-⇛≤*≤⇚-≡SK below).

≤SK?--⇛≤*≤⇚ : ∀ {s t} → s ≤SK? t → s ⇛≤*≤⇚ t
≤SK?--⇛≤*≤⇚ ≤?-refl = (_ , ε , ε)
≤SK?--⇛≤*≤⇚ (≤?-trans s≤t t≤u) =
  ⇛≤*≤⇚-trans (≤SK?--⇛≤*≤⇚ s≤t) (≤SK?--⇛≤*≤⇚ t≤u)
≤SK?--⇛≤*≤⇚ ≤?-⊥ = (_ , ⇛-⊥ ◅ ε , ε)
≤SK?--⇛≤*≤⇚ ≤?-⊤ = (_ , ε , ⇛-⊤ ◅ ε)
≤SK?--⇛≤*≤⇚ ≤?-Sred = _ , ⇛-Sred ⇛-refl ⇛-refl ⇛-refl ◅ ε , ε
≤SK?--⇛≤*≤⇚ ≤?-Kred = _ , ⇛-Kred ⇛-refl ◅ ε , ε
≤SK?--⇛≤*≤⇚ ≤?-Sexp = _ , ε , ⇛-Sred ⇛-refl ⇛-refl ⇛-refl ◅ ε
≤SK?--⇛≤*≤⇚ ≤?-Kexp = _ , ε , ⇛-Kred ⇛-refl ◅ ε
≤SK?--⇛≤*≤⇚ (≤?-· s₁≤t₁ s₂≤t₂) =
  let u₁ , s₁⇛u₁ , t₁⇛u₁ = ≤SK?--⇛≤*≤⇚ s₁≤t₁
      u₂ , s₂⇛u₂ , t₂⇛u₂ = ≤SK?--⇛≤*≤⇚ s₂≤t₂
  in u₁ · u₂ , ⇛*-· s₁⇛u₁ s₂⇛u₂ , ⇛*-· t₁⇛u₁ t₂⇛u₂

-- Reduction preserves pure terms.

⇛-Pure : ∀ {ab s t} (ps : Pure s) → s ⇛[ ab ] t →
         ∃ λ pt → inject⁻¹ ps ≡SK inject⁻¹ {t} pt
⇛-Pure p ⇛-refl = p , ≡-refl
⇛-Pure (S · ps₁ · pt₁ · pu₁) (⇛-Sred s₁⇛s₂ t₁⇛t₂ u₁⇛u₂) =
  let ps₂ , s₁≡s₂ = ⇛-Pure ps₁ s₁⇛s₂
      pt₂ , t₁≡t₂ = ⇛-Pure pt₁ t₁⇛t₂
      pu₂ , u₁≡u₂ = ⇛-Pure pu₁ u₁⇛u₂
  in ps₂ · pu₂ · (pt₂ · pu₂) ,
     ≡-trans (≡-· (≡-· (≡-· ≡-refl s₁≡s₂) t₁≡t₂) u₁≡u₂) ≡-Sred
⇛-Pure (K · ps₁ · _) (⇛-Kred s₁⇛s₂) =
  let ps₂ , s₁≡s₂ = ⇛-Pure ps₁ s₁⇛s₂
  in ps₂ , ≡-trans ≡-Kred s₁≡s₂
⇛-Pure (ps · pt) (⇛-· s₁⇛s₂ t₁⇛t₂)  =
  Prod.zip _·_ ≡-· (⇛-Pure ps s₁⇛s₂) (⇛-Pure pt t₁⇛t₂)

⇛*-Pure : ∀ {ab s t} (ps : Pure s) → s ⇛[ ab ]* t →
          ∃ λ pt → inject⁻¹ ps ≡SK inject⁻¹ {t} pt
⇛*-Pure p  ε            = p , ≡-refl
⇛*-Pure ps (s⇛t ◅ t⇛*u) =
  let pt , s≡t = ⇛-Pure  ps s⇛t
      pu , t≡u = ⇛*-Pure pt t⇛*u
  in pu , ≡-trans s≡t t≡u

-- The combined multi-step reduction is a subrelation of ≡SK on pure terms.

inject-⇛≤*≤⇚-≡SK : ∀ {s t} → inject s ⇛≤*≤⇚ inject t → s ≡SK t
inject-⇛≤*≤⇚-≡SK {s} {t} (u , s⇛≤*u , t⇛≥*u) =
  let pu  , s≡u = ⇛*-Pure (inject-Pure s) s⇛≤*u
      pu′ , t≡u = ⇛*-Pure (inject-Pure t) t⇛≥*u
  in ≡-trans (subst (_≡SK (inject⁻¹ pu)) (inject⁻¹-inject-Pure s) s≡u)
             (subst₂ (_≡SK_) (inject⁻¹-unique pu′ pu) (inject⁻¹-inject-Pure t)
                     (≡-sym t≡u))

-- The order on SK? terms is a subrelation of the equality on pure SK
-- terms.
--
-- NOTE. This establishes a circular equivalence between the three
-- relations _≡SK_, _⇛≤*≤⇚_ and _≤SK?_ when restricted to pure SK
-- terms:
--
--           _≡SK_  ⊆  _≤SK?_  ⊆  _⇛≤*≤⇚_  ⊆  _≡SK_
--
-- This equivalence will allow us to encode/extract equivalence proofs
-- on (pure) SK terms from typing derivations.

inject-≤SK?-≡SK : ∀ {s t} → inject s ≤SK? inject t → s ≡SK t
inject-≤SK?-≡SK {s} {t} s≤t = inject-⇛≤*≤⇚-≡SK (≤SK?--⇛≤*≤⇚ s≤t)
