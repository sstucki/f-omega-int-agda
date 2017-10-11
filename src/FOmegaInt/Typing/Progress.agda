------------------------------------------------------------------------
-- Progress of CBV reductions in Fω with interval kinds
------------------------------------------------------------------------

-- This module contains a variant of the "progress" theorem for Fω
-- with interval kinds.  Progress says roughly that well-typed terms
-- do not get stuck.  I.e. a well-typed term is either a value or it
-- can take a call-by-value (CBV) reduction step.  Together with the
-- subject reduction (aka "preservation") theorem from
-- FOmegaInt.Typing.Preservation, progress ensures type safety.  For
-- detials, see e.g.
--
--  * B. C. Pierce, TAPL (2002), pp. 95.
--
--  * A. Wright and M. Felleisen, "A Syntactic Approach to Type
--    Soundness" (1994).

module FOmegaInt.Typing.Progress where

open import Data.Product using (_,_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)

open import FOmegaInt.Syntax
open import FOmegaInt.Typing
open import FOmegaInt.Typing.Inversion
open import FOmegaInt.Reduction.Cbv

open Syntax
open TermCtx
open Substitution using (_[_])
open Typing

-- A canonical forms lemma for universal types: closed values of
-- universal type are type abstractions.
Π-can : ∀ {f k a} → Val f → [] ⊢Tm f ∈ Π k a → ∃ λ k′ →
        ∃ λ a′ → f ≡ Λ k′ a′
Π-can (Λ k a) (∈-∀-i k-kd a∈b)   = k , a , refl
Π-can (Λ k a) (∈-⇑ Λka∈b b<:Πkc) = k , a , refl
Π-can (ƛ a b) (∈-⇑ ƛab∈c c<:Πkd) with Tm∈-gen ƛab∈c
Π-can (ƛ a b) (∈-⇑ ƛab∈c c<:Πkd) | ∈-→-i a∈* b∈e a⇒e<:c =
  contradiction (<:-trans a⇒e<:c c<:Πkd) ⇒-≮:-Π

-- A canonical forms lemma for arrow types: closed values of arrow
-- type are term abstractions.
⇒-can : ∀ {f a b} → Val f → [] ⊢Tm f ∈ a ⇒ b → ∃ λ a′ → ∃ λ b′ → f ≡ ƛ a′ b′
⇒-can (Λ k a) (∈-⇑ Λka∈b b<:c⇒d) with Tm∈-gen Λka∈b
⇒-can (Λ k a) (∈-⇑ Λka∈b b<:c⇒d) | ∈-∀-i k-kd a∈e Πke<:b =
  contradiction (<:-trans Πke<:b b<:c⇒d) Π-≮:-⇒
⇒-can (ƛ a b) (∈-→-i a∈* b∈c c∈*) = a , b , refl
⇒-can (ƛ a b) (∈-⇑ ƛab∈c c<:d⇒e)  = a , b , refl

-- Progress: well-typed terms do not get stuck (under CBV reduction).
prog : ∀ {a b} → [] ⊢Tm a ∈ b → Val a ⊎ (∃ λ a′ → a →v a′)
prog (∈-var () _ _)
prog (∈-∀-i k-kd b∈c)    = inj₁ (Λ _ _)
prog (∈-→-i a∈* b∈c c∈*) = inj₁ (ƛ _ _)
prog (∈-∀-e a∈Πkc b∈k) with prog a∈Πkc
prog (∈-∀-e a∈Πkc b∈k) | inj₁ u with Π-can u a∈Πkc
...| k′ , a′ , refl = inj₂ (_ , cont-⊡ k′ a′ _)
prog (∈-∀-e a∈Πkc b∈k) | inj₂ (a′ , a→a′) = inj₂ (_ , a→a′ ⊡ _)
prog (∈-→-e a∈c⇒d b∈c) with prog a∈c⇒d
prog (∈-→-e a∈c⇒d b∈c) | inj₁ u with prog b∈c
prog (∈-→-e a∈c⇒d b∈c) | inj₁ u | inj₁ v with ⇒-can u a∈c⇒d
...| c′ , a′ , refl = inj₂ (_ , cont-· c′ a′ v)
prog (∈-→-e a∈c⇒d b∈c) | inj₁ u | inj₂ (b′ , b→b′) = inj₂ (_ , u ·₂ b→b′)
prog (∈-→-e a∈c⇒d b∈c) | inj₂ (a′ , a→a′) = inj₂ (_ , a→a′ ·₁ _)
prog (∈-⇑ a∈b b<:c)    = prog a∈b
