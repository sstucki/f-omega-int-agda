------------------------------------------------------------------------
-- Subject reduction for typing in Fω with interval kinds
------------------------------------------------------------------------

-- This module proves a variant of subject reduction (aka the
-- "preservation" theorem) for term reduction in Fω with interval
-- kinds.  The subject reduction property proved here is weaker than
-- the one typically found in the literature on other variants of Fω:
-- subject reduction does not hold in arbitrary typing contexts in Fω
-- with interval types because type variables of interval kind can be
-- used to introduce arbitrary typing (in)equalities into the
-- subtyping relation.  In other words, subject reduction does not
-- hold for full β-reduction as reductions under type abstractions are
-- not safe in general.  Note, however, that subject reduction does
-- hold for arbitrary β-reductions in *types* (see `pres-Tp∈-→β*' in
-- the Kinding.Declarative.Validity module for a proof).
--
-- NOTE.  Here we use the CBV evaluation strategy, but this is
-- unnecessarily restrictive.  Other evaluation strategies work so
-- long as they do not allow reductions under type abstractions.
--
-- Together with the "progress" theorem from Typing.Progress, subject
-- reduction ensures type safety.  For details, see e.g.
--
--  * B. C. Pierce, TAPL (2002), pp. 95.
--
--  * A. Wright and M. Felleisen, "A Syntactic Approach to Type
--    Soundness" (1994).

module FOmegaInt.Typing.Preservation where

open import Data.Product using (_,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Negation using (contradiction)

open import FOmegaInt.Syntax
open import FOmegaInt.Typing
open import FOmegaInt.Typing.Inversion
open import FOmegaInt.Reduction.Cbv
open import FOmegaInt.Reduction.Full

open Syntax
open TermCtx
open Substitution using (_[_]; weaken-sub)
open Typing
open TypedSubstitution using (Tm∈-[]; <:-[])

-- Types of closed terms are preserved under single-step reduction.
pres : ∀ {a b c} → [] ⊢Tm a ∈ c → a →v b → [] ⊢Tm b ∈ c
pres (∈-var () _ _)
pres (∈-∀-i k-kd a∈b)    ()
pres (∈-→-i a∈* b∈c c∈*) ()
pres (∈-∀-e Λja∈Πkc b∈k) (cont-⊡ j a b) with Tm∈-gen Λja∈Πkc
... | ∈-∀-i j-kd a∈d Πjd<:Πkc =
  let k<∷j , d<:c = <:-∀-inv Πjd<:Πkc
  in ∈-⇑ (Tm∈-[] a∈d (∈-tp (∈-⇑ b∈k k<∷j))) (<:-[] d<:c (∈-tp b∈k))
pres (∈-∀-e a∈Πcd b∈c)   (a→e ⊡ b) = ∈-∀-e (pres a∈Πcd a→e) b∈c
pres (∈-→-e ƛea∈c⇒d v∈c) (cont-· e a v) with Tm∈-gen ƛea∈c⇒d
... | ∈-→-i e∈* a∈f e⇒f<:c⇒d =
  let c<:e , f<:d =  <:-→-inv e⇒f<:c⇒d
  in ∈-⇑ (subst (_ ⊢Tm _ ∈_) (weaken-sub _) (Tm∈-[] a∈f (∈-tm (∈-⇑ v∈c c<:e))))
         f<:d
pres (∈-→-e a∈c⇒d b∈c)   (a→e ·₁ b) = ∈-→-e (pres a∈c⇒d a→e) b∈c
pres (∈-→-e a∈c⇒d b∈c)   (v ·₂ b→e) = ∈-→-e a∈c⇒d (pres b∈c b→e)
pres (∈-⇑ a∈c c<:d)      a→b   = ∈-⇑ (pres a∈c a→b) c<:d

-- Weak preservation (aka subject reduction): types of closed terms
-- are preserved under reduction.
pres* : ∀ {a b c} → [] ⊢Tm a ∈ c → a →v* b → [] ⊢Tm b ∈ c
pres* a∈c ε            = a∈c
pres* a∈d (a→b ◅ b→*c) = pres* (pres a∈d a→b) b→*c
