------------------------------------------------------------------------
-- Validity of declarative typing and kinding of Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Typing.Validity where

open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Product as Prod using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
open import Function using (_∘_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.TransReasoning
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import FOmegaInt.Syntax
open import FOmegaInt.Typing
open import FOmegaInt.Kinding.Declarative.Equivalence
open import FOmegaInt.Reduction.Full

import FOmegaInt.Kinding.Declarative
import FOmegaInt.Kinding.Declarative.Validity

-- Extended kinding
module E where
  open FOmegaInt.Kinding.Declarative          public
  open FOmegaInt.Kinding.Declarative.Validity public
  open KindedSubstitution                     public


------------------------------------------------------------------------
-- Validity of declarative kinding, typing, subkinding and subtyping

open Syntax
open Substitution hiding (subst)
open TermCtx
open Typing
open TypedSubstitution
open WfCtxOps using (lookup-tp)

-- Validity of kinding: the kinds of well-kinded types are well-formed.
Tp∈-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ k kd
Tp∈-valid = sound-kd ∘ E.Tp∈-valid ∘ complete-Tp∈

-- Validity of subkinding: subkinds are well-formed.
<∷-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ ⊢ j kd × Γ ⊢ k kd
<∷-valid = Prod.map sound-kd sound-kd ∘ E.<∷-valid ∘ complete-<∷

-- Validity of subtyping: subtypes that are related in some kind `k'
-- inhabit `k'.
<:-valid : ∀ {n} {Γ : Ctx n} {a b k} →
           Γ ⊢ a <: b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
<:-valid = Prod.map sound-Tp∈ sound-Tp∈ ∘ E.<:-valid ∘ complete-<:

-- A corollary.
<:-valid-kd : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ∈ k → Γ ⊢ k kd
<:-valid-kd a<:b∈k = Tp∈-valid (proj₁ (<:-valid a<:b∈k))

-- Validity of type equality: types that are equal in some kind `k'
-- inhabit `k'.
≃-valid : ∀ {n} {Γ : Ctx n} {a b k} →
          Γ ⊢ a ≃ b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
≃-valid = Prod.map sound-Tp∈ sound-Tp∈ ∘ E.≃-valid ∘ complete-≃

-- Validity of kind equality: equal kinds are well-formed.
≅-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ j kd × Γ ⊢ k kd
≅-valid (<∷-antisym j<∷k k<∷j) = <∷-valid j<∷k

-- Validity of combined kind and type equality: equal ascriptions are
-- well-formed.
≃wf-valid : ∀ {n} {Γ : Ctx n} {a b} →
            Γ ⊢ a ≃ b wf → Γ ⊢ a wf × Γ ⊢ b wf
≃wf-valid (≃wf-≅ j≅k)   = Prod.map wf-kd wf-kd (≅-valid j≅k)
≃wf-valid (≃wf-≃ a≃b∈k) = Prod.map wf-tp wf-tp (≃-valid a≃b∈k)

-- Validity of typing: the types of well-typed terms are well-kinded.
Tm∈-valid : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢Tm a ∈ b → Γ ⊢Tp b ∈ *
Tm∈-valid (∈-var x Γ-ctx Γ[x]≡tp-a) = lookup-tp x Γ-ctx Γ[x]≡tp-a
Tm∈-valid (∈-∀-i k-kd a∈b)    = ∈-∀-f k-kd (Tm∈-valid a∈b)
Tm∈-valid (∈-→-i a∈* b∈c c∈*) = ∈-→-f a∈* c∈*
Tm∈-valid (∈-∀-e a∈∀kc b∈k)   =
  let k-kd , c∈* = Tp∈-∀-inv (Tm∈-valid a∈∀kc)
  in Tp∈-[] c∈* (∈-tp b∈k)
Tm∈-valid (∈-→-e a∈c⇒d b∈c)   =
  let c∈* , d∈* = Tp∈-→-inv (Tm∈-valid a∈c⇒d)
  in d∈*
Tm∈-valid (∈-⇑ a∈b b<:c)      = proj₂ (<:-valid b<:c)

-- Subtypes inhabiting interval kinds are proper types.
<:-⋯-* : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a <: b ∈ c ⋯ d → Γ ⊢ a <: b ∈ *
<:-⋯-* a<:b∈c⋯d =
  let a∈c⋯d , b∈c⋯d = <:-valid a<:b∈c⋯d
  in <:-⇑ (<:-⋯-i a<:b∈c⋯d) (<∷-⋯ (<:-⊥ a∈c⋯d) (<:-⊤ b∈c⋯d))

-- An admissible rule for kinding η-expanded type operators.
Tp∈-η : ∀ {n} {Γ : Ctx n} {a j k} →
        Γ ⊢Tp a ∈ Π j k → Γ ⊢Tp Λ j (weaken a · var zero) ∈ Π j k
Tp∈-η a∈Πjk with complete-Tp∈ a∈Πjk
Tp∈-η a∈Πjk | a∈Πjk′ with E.Tp∈-valid a∈Πjk′
... | E.Kinding.kd-Π j-kd k-kd = sound-Tp∈ (E.Tp∈-η a∈Πjk′ j-kd k-kd)

-- Operations on well-formed context equality that require weakening
-- and validity of ascription equality.
module CtxEqOps where
  open Pointwise using (Pointwise; []; _∷_; map⁺)
  open TypedRenaming using (≃wf-weaken)

  -- Convert a context equation to its All₂ representation.
  ≃ctx-toAll : ∀ {m} {Γ Δ : Ctx m} → Γ ≃ Δ ctx →
               Pointwise (Γ ⊢_≃_wf) (toVec Γ) (toVec Δ)
  ≃ctx-toAll ≃-[]          = []
  ≃ctx-toAll (≃-∷ a≃b Γ≃Δ) =
    let a-wf , _ = ≃wf-valid a≃b
    in ≃wf-weaken a-wf a≃b ∷ map⁺ (≃wf-weaken a-wf) (≃ctx-toAll Γ≃Δ)

  -- Ascriptions looked up in equal contexts are equal.

  lookup-≃ : ∀ {m} {Γ Δ : Ctx m} x → Γ ≃ Δ ctx →
             Γ ⊢ lookup x Γ ≃ lookup x Δ wf
  lookup-≃ x Γ≃Δ = Pointwise.lookup (≃ctx-toAll Γ≃Δ) x

  lookup-≃-kd : ∀ {m} {Γ Δ : Ctx m} {j k} x → Γ ≃ Δ ctx →
                lookup x Γ ≡ kd j → lookup x Δ ≡ kd k → Γ ⊢ j ≅ k
  lookup-≃-kd x Γ≃Δ Γ[x]≡kd-j Δ[x]≡kd-k =
    ≃wf-kd-inv (subst₂ (_ ⊢_≃_wf) Γ[x]≡kd-j Δ[x]≡kd-k (lookup-≃ x Γ≃Δ))


----------------------------------------------------------------------
-- Context narrowing (strong version)
--
-- NOTE. We could have proven a *weak* variant of context narrowing
-- for the (original) declarative judgments directly in the Typing
-- module (before establishing validity).  But since we did not need
-- (weak or strong) context narrowing of the original judgments until
-- now, it is easier to instead prove the strengthened version here
-- via context narrowing and equivalence of the extended rules.

module TypedNarrowing where

  -- Narrowing the kind of the first type variable preserves
  -- well-formedness of kinds.
  ⇓-kd : ∀ {n} {Γ : Ctx n} {j₁ j₂ k} →
         Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ k kd → kd j₁ ∷ Γ ⊢ k kd
  ⇓-kd j₁<∷j₂ k-kd =
    let j₁<∷j₂′   = complete-<∷ j₁<∷j₂
        j₁-kd , _ = E.<∷-valid j₁<∷j₂′
    in sound-kd (E.⇓-kd j₁-kd j₁<∷j₂′ (complete-kd k-kd))

  -- Narrowing the kind of the first type variable preserves
  -- well-kindedness.
  ⇓-Tp∈ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a k} →
          Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢Tp a ∈ k → kd j₁ ∷ Γ ⊢Tp a ∈ k
  ⇓-Tp∈ j₁<∷j₂ a∈k =
    let j₁<∷j₂′   = complete-<∷ j₁<∷j₂
        j₁-kd , _ = E.<∷-valid j₁<∷j₂′
    in sound-Tp∈ (E.⇓-Tp∈ j₁-kd j₁<∷j₂′ (complete-Tp∈ a∈k))

  -- Narrowing the kind of the first type variable preserves
  -- subkinding and subtyping.

  ⇓-<∷ : ∀ {n} {Γ : Ctx n} {j₁ j₂ k₁ k₂} →
         Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ k₁ <∷ k₂ → kd j₁ ∷ Γ ⊢ k₁ <∷ k₂
  ⇓-<∷ j₁<∷j₂ k₁<∷k₂ =
    let j₁<∷j₂′   = complete-<∷ j₁<∷j₂
        j₁-kd , _ = E.<∷-valid j₁<∷j₂′
    in sound-<∷ (E.⇓-<∷ j₁-kd j₁<∷j₂′ (complete-<∷ k₁<∷k₂))

  ⇓-<: : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂ k} →
         Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ a₁ <: a₂ ∈ k → kd j₁ ∷ Γ ⊢ a₁ <: a₂ ∈ k
  ⇓-<: j₁<∷j₂ a₁<:a₂∈k =
    let j₁<∷j₂′   = complete-<∷ j₁<∷j₂
        j₁-kd , _ = E.<∷-valid j₁<∷j₂′
    in sound-<: (E.⇓-<: j₁-kd j₁<∷j₂′ (complete-<: a₁<:a₂∈k))

open TypedNarrowing

-- Transitivity of subkinding and kind equality.
--
-- NOTE. We could have proven admissibility of these rules directly in
-- the Typing module (before establishing validity) but this would
-- have required a proof of (weak) context narrowing for the
-- (original) declarative rules.  As we do not need these transitivity
-- properties until we prove subject reduction (below), we go with an
-- indirect proof instead.

<∷-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j <∷ k → Γ ⊢ k <∷ l → Γ ⊢ j <∷ l
<∷-trans k₁<∷k₂ k₂<∷k₃ =
  sound-<∷ (E.<∷-trans (complete-<∷ k₁<∷k₂) (complete-<∷ k₂<∷k₃))

≅-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j ≅ k → Γ ⊢ k ≅ l → Γ ⊢ j ≅ l
≅-trans k₁≅k₂ k₂≅k₃ =
  sound-≅ (E.≅-trans (complete-≅ k₁≅k₂) (complete-≅ k₂≅k₃))

-- Relational reasoning for kind and type equality.
--
-- NOTE. Even though the equalities are technically preorders, we have
-- to use the weaker reasoning designed for transitive relations here.
-- This is because reflexivity proofs in typed relations are typically
-- also typed, i.e. given some context `Γ' and some raw kind or term
-- `x` we cannot, in general, conclude that `Γ ⊢ x ∼ x` without an
-- additional well-formedness proof `Γ ⊢ x' of some sort.

module ≅-Reasoning where
  ≅-reasoning : TransCtxTermRelReasoning _⊢_≅_
  ≅-reasoning = record { ∼-trans = ≅-trans }

  open TransCtxTermRelReasoning ≅-reasoning public renaming (_∼⟨_⟩_ to _≅⟨_⟩_)

module ≃-Reasoning where
  ≃-reasoning : TypedTransRelReasoning _⊢_≃_∈_
  ≃-reasoning = record { ∼-trans = ≃-trans }

  open TypedTransRelReasoning ≃-reasoning public renaming (_∼⟨_⟩_ to _≃⟨_⟩_)


----------------------------------------------------------------------
-- Generation lemmas for abstractions

-- A generation lemma for kinding of type operator abstractions.
Tp∈-Λ-inv : ∀ {n} {Γ : Ctx n} {l a j k} → Γ ⊢Tp Λ l a ∈ Π j k →
            Γ ⊢ l kd × kd j ∷ Γ ⊢Tp a ∈ k
Tp∈-Λ-inv (∈-Π-i l-kd a∈k) = l-kd , a∈k
Tp∈-Λ-inv (∈-⇑ Λl∈Πj₁k₁ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd)) =
  let l-kd , a∈k₁ = Tp∈-Λ-inv Λl∈Πj₁k₁
  in l-kd , ∈-⇑ (⇓-Tp∈ j₂<∷j₁ a∈k₁) k₁<∷k₂

-- Term abstractions are not types.
Tp∈-¬λ : ∀ {n} {Γ : Ctx n} {a b k} → ¬ Γ ⊢Tp ƛ a b ∈ k
Tp∈-¬λ (∈-s-i λab∈c⋯d)  = Tp∈-¬λ λab∈c⋯d
Tp∈-¬λ (∈-⇑ λab∈j j<∷k) = Tp∈-¬λ λab∈j


----------------------------------------------------------------------
-- Admissible kind and type equality rules.

-- Functionality of kind formation (strong version).
kd-[≃] : ∀ {n} {Γ : Ctx n} {a b j k} →
         kd j ∷ Γ ⊢ k kd → Γ ⊢ a ≃ b ∈ j → Γ ⊢ k Kind[ a ] ≅ k Kind[ b ]
kd-[≃] k-kd a≃b∈j = sound-≅ (E.kd-[≃] (complete-kd k-kd) (complete-≃ a≃b∈j))

-- Functionality of kinding (strong version).
Tp∈-[≃] : ∀ {n} {Γ : Ctx n} {a b c j k} →
          kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢ b ≃ c ∈ j →
          Γ ⊢ a [ b ] ≃ a [ c ] ∈ k Kind[ b ]
Tp∈-[≃] a∈k b≃c∈j = sound-≃ (E.Tp∈-[≃] (complete-Tp∈ a∈k) (complete-≃ b≃c∈j))

-- An admissible congruence rule for kind equality w.r.t. dependent
-- arrow formation.
≅-Π : ∀ {n} {Γ : Ctx n} {j₁ j₂ k₁ k₂} →
      Γ ⊢ j₁ ≅ j₂ → kd j₁ ∷ Γ ⊢ k₁ ≅ k₂ → Γ ⊢ Π j₁ k₁ ≅ Π j₂ k₂
≅-Π (<∷-antisym j₁<∷j₂ j₂<∷j₁) (<∷-antisym k₁<∷k₂ k₂<∷k₁) =
  let j₁-kd , j₂-kd = <∷-valid j₁<∷j₂
      k₁-kd , k₂-kd = <∷-valid k₁<∷k₂
  in <∷-antisym (<∷-Π j₂<∷j₁ (⇓-<∷ j₂<∷j₁ k₁<∷k₂) (kd-Π j₁-kd k₁-kd))
                (<∷-Π j₁<∷j₂ k₂<∷k₁ (kd-Π j₂-kd (⇓-kd j₂<∷j₁ k₂-kd)))

-- Equal types inhabiting interval kinds are proper types.
≃-⋯-* : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a ≃ b ∈ c ⋯ d → Γ ⊢ a ≃ b ∈ *
≃-⋯-* (<:-antisym a<:b∈c⋯d b<:a∈c⋯d) =
  let a<:b∈* = <:-⋯-* a<:b∈c⋯d
      b<:a∈* = <:-⋯-* b<:a∈c⋯d
  in <:-antisym a<:b∈* b<:a∈*

-- An admissible congruence rule for type equality w.r.t. formation of
-- universal types.
≃-∀ : ∀ {n} {Γ : Ctx n} {k₁ k₂ a₁ a₂} →
      Γ ⊢ k₁ ≅ k₂ → kd k₁ ∷ Γ ⊢ a₁ ≃ a₂ ∈ * → Γ ⊢ Π k₁ a₁ ≃ Π k₂ a₂ ∈ *
≃-∀ (<∷-antisym k₁<∷k₂ k₂<∷k₁) (<:-antisym a₁<:a₂∈* a₂<:a₁∈*) =
  let k₁-kd , k₂-kd = <∷-valid k₁<∷k₂
      a₁∈*  , a₂∈*  = <:-valid a₁<:a₂∈*
  in <:-antisym (<:-∀ k₂<∷k₁ (⇓-<: k₂<∷k₁ a₁<:a₂∈*) (∈-∀-f k₁-kd a₁∈*))
                (<:-∀ k₁<∷k₂ a₂<:a₁∈* (∈-∀-f k₂-kd (⇓-Tp∈ k₂<∷k₁ a₂∈*)))

-- Another, weaker congruence lemma for type equality w.r.t. type
-- operator abstraction.
≃-λ′ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂ k} →
       Γ ⊢ j₁ ≅ j₂ → kd j₁ ∷ Γ ⊢ a₁ ≃ a₂ ∈ k → Γ ⊢ Λ j₁ a₁ ≃ Λ j₂ a₂ ∈ Π j₁ k
≃-λ′ (<∷-antisym j₁<∷j₂ j₂<∷j₁) (<:-antisym a₁<:a₂∈k a₂<:a₁∈k) =
  let j₁-kd , j₂-kd = <∷-valid j₁<∷j₂
      a₁∈k  , a₂∈k  = <:-valid a₁<:a₂∈k
      k-kd          = Tp∈-valid a₁∈k
      k-kd′         = ⇓-kd j₂<∷j₁ k-kd
      Πj₂k<∷j₁k     = <∷-Π j₁<∷j₂ (<∷-refl k-kd) (kd-Π j₂-kd k-kd′)
      Λj₁a₁∈Πj₁k    = ∈-Π-i j₁-kd a₁∈k
      Λj₂a₂∈Πj₁k    = ∈-⇑ (∈-Π-i j₂-kd (⇓-Tp∈ j₂<∷j₁ a₂∈k)) Πj₂k<∷j₁k
  in <:-antisym (<:-λ a₁<:a₂∈k Λj₁a₁∈Πj₁k Λj₂a₂∈Πj₁k)
                (<:-λ a₂<:a₁∈k Λj₂a₂∈Πj₁k Λj₁a₁∈Πj₁k)

-- An admissible congruence rule for type equality w.r.t. type
-- application.
≃-· : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j k} →
      Γ ⊢ a₁ ≃ a₂ ∈ Π j k → Γ ⊢ b₁ ≃ b₂ ∈ j →
      Γ ⊢ a₁ · b₁ ≃ a₂ · b₂ ∈ k Kind[ b₁ ]
≃-· (<:-antisym a₁<:a₂∈Πjk a₂<:a₁∈Πjk) b₁≃b₂∈j with <:-valid-kd a₁<:a₂∈Πjk
... | (kd-Π j-kd k-kd) =
  <:-antisym (<:-· a₁<:a₂∈Πjk b₁≃b₂∈j)
             (<:-⇑ (<:-· a₂<:a₁∈Πjk (≃-sym b₁≃b₂∈j))
                   (≅⇒<∷ (kd-[≃] k-kd (≃-sym b₁≃b₂∈j))))

-- An admissible, more flexible β-rule for type equality.
≃-β′ : ∀ {n} {Γ : Ctx n} {a b j k l} →
       kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j → Γ ⊢Tp Λ l a ∈ Π j k →
       Γ ⊢ (Λ l a) · b ≃ a [ b ] ∈ k Kind[ b ]
≃-β′ a∈k b∈j Λla∈Πjk =
  let j-kd = Tp∈-valid b∈j
  in ≃-trans (≃-· (≃-λ (≃-refl a∈k) Λla∈Πjk (∈-Π-i j-kd a∈k)) (≃-refl b∈j))
             (≃-β a∈k b∈j)

-- An admissible singleton-introduction rule for type equality.
≃-s-i : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a ≃ b ∈ c ⋯ d → Γ ⊢ a ≃ b ∈ a ⋯ a
≃-s-i (<:-antisym a<:b∈c⋯d b<:a∈c⋯d) =
  let a<:b∈*  = <:-⋯-* a<:b∈c⋯d
      b<:a∈*  = <:-⋯-* b<:a∈c⋯d
      a∈* , _ = <:-valid a<:b∈*
      a<:a∈*  = <:-refl a∈*
  in <:-antisym (<:-⇑ (<:-⋯-i a<:b∈c⋯d) (<∷-⋯ a<:a∈* b<:a∈*))
                (<:-⇑ (<:-⋯-i b<:a∈c⋯d) (<∷-⋯ a<:b∈* a<:a∈*))


------------------------------------------------------------------------
-- Subject reduction for kinding.

-- A variant of subject reduction for kinding: untyped β-reduction of
-- kinds and types is included in kind resp. type equality.

mutual

  kd-→β-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j kd → j Kd→β k → Γ ⊢ j ≅ k
  kd-→β-≅ (kd-⋯ a∈* b∈*)   (a→a′ ⋯₁ b) = ≅-⋯ (Tp∈-→β-≃ a∈* a→a′) (≃-refl b∈*)
  kd-→β-≅ (kd-⋯ a∈* b∈*)   (a ⋯₂ b→b′) = ≅-⋯ (≃-refl a∈*) (Tp∈-→β-≃ b∈* b→b′)
  kd-→β-≅ (kd-Π j-kd k-kd) (Π₁ j→j′ k) =
    ≅-Π (kd-→β-≅ j-kd j→j′) (≅-refl k-kd)
  kd-→β-≅ (kd-Π j-kd k-kd) (Π₂ j k→k′) =
    ≅-Π (≅-refl j-kd) (kd-→β-≅ k-kd k→k′)

  Tp∈-→β-≃ : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ∈ k → a →β b → Γ ⊢ a ≃ b ∈ k
  Tp∈-→β-≃ (∈-var x Γ-ctx Γ[x]≡kd-k) ⌈ () ⌉
  Tp∈-→β-≃ (∈-⊥-f Γ-ctx)    ⌈ () ⌉
  Tp∈-→β-≃ (∈-⊤-f Γ-ctx)    ⌈ () ⌉
  Tp∈-→β-≃ (∈-∀-f k-kd a∈*) ⌈ () ⌉
  Tp∈-→β-≃ (∈-∀-f k-kd a∈*) (Π₁ k→k′ a) =
    ≃-∀ (kd-→β-≅ k-kd k→k′) (≃-refl a∈*)
  Tp∈-→β-≃ (∈-∀-f k-kd a∈*) (Π₂ k a→a′) =
    ≃-∀ (≅-refl k-kd) (Tp∈-→β-≃ a∈* a→a′)
  Tp∈-→β-≃ (∈-→-f a∈* b∈*)  ⌈ () ⌉
  Tp∈-→β-≃ (∈-→-f a∈* b∈*)  (a→a′ ⇒₁ b) =
    ≃-→ (Tp∈-→β-≃ a∈* a→a′) (≃-refl b∈*)
  Tp∈-→β-≃ (∈-→-f a∈* b∈*)  (a ⇒₂ b→b′) =
    ≃-→ (≃-refl a∈*) (Tp∈-→β-≃ b∈* b→b′)
  Tp∈-→β-≃ (∈-Π-i j-kd a∈k) ⌈ () ⌉
  Tp∈-→β-≃ (∈-Π-i j-kd a∈k) (Λ₁ j→j′ a) =
    ≃-λ′ (kd-→β-≅ j-kd j→j′) (≃-refl a∈k)
  Tp∈-→β-≃ (∈-Π-i j-kd a∈k) (Λ₂ j a→a′) =
    ≃-λ′ (≅-refl j-kd) (Tp∈-→β-≃ a∈k a→a′)
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j) ⌈ cont-Tp· l a b ⌉ =
    let l-kd , a∈k = Tp∈-Λ-inv a∈Πjk
    in ≃-β′ a∈k b∈j a∈Πjk
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j) ⌈ cont-Tm· a b c ⌉ =
    contradiction a∈Πjk Tp∈-¬λ
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j) (a→a′ ·₁ b) =
    ≃-· (Tp∈-→β-≃ a∈Πjk a→a′) (≃-refl b∈j)
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j) (a ·₂ b→b′) =
    ≃-· (≃-refl a∈Πjk) (Tp∈-→β-≃ b∈j b→b′)
  Tp∈-→β-≃ (∈-s-i a∈k)    a→b = ≃-s-i (Tp∈-→β-≃ a∈k a→b)
  Tp∈-→β-≃ (∈-⇑ a∈j j<∷k) a→b = ≃-⇑ (Tp∈-→β-≃ a∈j a→b) j<∷k

kd-→β*-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j kd → j Kd→β* k → Γ ⊢ j ≅ k
kd-→β*-≅ j-kd ε            = ≅-refl j-kd
kd-→β*-≅ j-kd (j→k ◅ k→*l) =
  let j≅k  = kd-→β-≅ j-kd j→k
      k-kd = proj₂ (≅-valid j≅k)
  in ≅-trans j≅k (kd-→β*-≅ k-kd k→*l)

Tp∈-→β*-≃ : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ∈ k → a →β* b → Γ ⊢ a ≃ b ∈ k
Tp∈-→β*-≃ a∈k ε            = ≃-refl a∈k
Tp∈-→β*-≃ a∈k (a→b ◅ b→*c) =
  let a≃b∈k = Tp∈-→β-≃ a∈k a→b
      b∈k   = proj₂ (≃-valid a≃b∈k)
  in ≃-trans a≃b∈k (Tp∈-→β*-≃ b∈k b→*c)

-- A corollary: subject reduction for kinding, aka preservation of
-- kinding under (full) β-reduction.
pres-Tp∈-→β* : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ∈ k → a →β* b → Γ ⊢Tp b ∈ k
pres-Tp∈-→β* a∈k a→b = proj₂ (≃-valid (Tp∈-→β*-≃ a∈k a→b))
