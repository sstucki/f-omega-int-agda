------------------------------------------------------------------------
-- Canonical kinding of Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module FOmegaInt.Kinding.Canonical where

open import Data.Context.WellFormed
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.Product using (∃; _,_; _×_)
open import Data.Vec as Vec using ([])
open import Level using () renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
import FOmegaInt.Kinding.Simple as SimpleKinding


------------------------------------------------------------------------
-- Canonical kinding derivations.
--
-- NOTE. In the rules below, we use (singleton) kind synthesis
-- judgments of the form `Γ ⊢Nf a ⇉ a ⋯ a' to ensure that `a' is a
-- well-kinded proper type rather than kind checking judgments of the
-- form `Γ ⊢Nf a ⇇ *'.  While the latter may seem more natural, it
-- involves the use of subsumption/subtyping to ensure that `Γ ⊢ a ⋯ a
-- <∷ *'.  As we will show, this is always true (if `a' is indeed a
-- proper type) but the extra use of subsumption complicates the
-- proofs of properties that require (partial) inversion of kinding
-- derivations.  See e.g. the Nf⇉-⋯-* and Nf⇇-⋯-* lemmas.

module Kinding where
  open ElimCtx
  open Syntax

  infix 4 _⊢_wf _ctx _⊢_kd
  infix 4 _⊢Nf_⇉_ _⊢Ne_∈_ _⊢Var_∈_ _⊢_⇉∙_⇉_ _⊢Nf_⇇_
  infix 4 _⊢_<∷_ _⊢_<:_ _⊢_<:_⇇_
  infix 4 _⊢_≅_ _⊢_≃_⇇_ _⊢_⇉∙_≃_⇉_

  mutual

    -- Well-formed type/kind ascriptions in typing contexts.
    --
    -- A raw kind ascriptions is considered well-formed if it
    -- corresponds to a well-formed normal kind.  Raw type ascriptions
    -- are are considered well-formed if they correspond to proper
    -- normal types.
    data _⊢_wf {n} (Γ : Ctx n) : ElimAsc n → Set where
      wf-kd : ∀ {a} → Γ ⊢ a kd        → Γ ⊢ kd a wf
      wf-tp : ∀ {a} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢ tp a wf

    -- Well-formed typing contexts.
    --
    -- Contexts and context extensions are well-formed if all the
    -- ascriptions they contain are well-formed.
    _ctx : ∀ {n} → Ctx n → Set
    Γ ctx = ContextFormation._wf _⊢_wf Γ

    -- Well-formedness checking for η-long β-normal kinds.
    data _⊢_kd {n} (Γ : Ctx n) : Kind Elim n → Set where
      kd-⋯ : ∀ {a b} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢Nf b ⇉ b ⋯ b → Γ ⊢ a ⋯ b kd
      kd-Π : ∀ {j k} → Γ ⊢ j kd → kd j ∷ Γ ⊢ k kd        → Γ ⊢ Π j k kd

    -- Kind synthesis for η-long β-normal types.
    data _⊢Nf_⇉_ {n} (Γ : Ctx n) : Elim n → Kind Elim n → Set where
      ⇉-⊥-f : Γ ctx → Γ ⊢Nf ⊥∙ ⇉ ⊥∙ ⋯ ⊥∙
      ⇉-⊤-f : Γ ctx → Γ ⊢Nf ⊤∙ ⇉ ⊤∙ ⋯ ⊤∙
      ⇉-∀-f : ∀ {k a} → Γ ⊢ k kd → kd k ∷ Γ ⊢Nf a ⇉ a ⋯ a →
              Γ ⊢Nf ∀∙ k a ⇉ ∀∙ k a ⋯ ∀∙ k a
      ⇉-→-f : ∀ {a b} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢Nf b ⇉ b ⋯ b →
              Γ ⊢Nf a ⇒∙ b ⇉ a ⇒∙ b ⋯ a ⇒∙ b
      ⇉-Π-i : ∀ {j a k} → Γ ⊢ j kd → kd j ∷ Γ ⊢Nf a ⇉ k → Γ ⊢Nf Λ∙ j a ⇉ Π j k
      ⇉-s-i : ∀ {a b c} → Γ ⊢Ne a ∈ b ⋯ c → Γ ⊢Nf a ⇉ a ⋯ a

    -- Canonical kinding of neutral types.
    --
    -- NOTE.  This is *not* a kind synthesis judgment!  See the
    -- comment on canonical variable kinding for an explanation.

    data _⊢Ne_∈_ {n} (Γ : Ctx n) : Elim n → Kind Elim n → Set where
      ∈-∙ : ∀ {x j k} {as : Spine n} → Γ ⊢Var x ∈ j →
            Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢Ne var x ∙ as ∈ k

    -- Canonical kinding of variables.
    --
    -- NOTE.  This would be a kind synthesis judgment if it weren't
    -- for the subsumption rule (⇇-⇑).  Thanks to this rule, the proof
    -- of the "context narrowing" property is easy to establish for
    -- canonical typing (see the ContextNarrowing module below).
    -- Without a proof of this property, the various lemmas about
    -- kinded hereditary substitutions become difficult to establish
    -- (see Kinding.HereditarySubstitution).  Unfortunately, proving
    -- that context narrowing is admissible *without* (⇇-⇑) would
    -- require precisely these substitution lemmas, leading to a
    -- cyclic dependency.  Introducing the subsumption rule for
    -- variables thus allows us to break that cycle.  On the other
    -- hand, the subsumption rule breaks functionality of the
    -- canonical kinding relations for variables and neutral types,
    -- i.e. their canonical kinds are no longer unique.  This is
    -- partly remedied by the singleton-introduction rule (⇉-s-i) in
    -- the kind synthesis judgment for normal types: neutrals have
    -- unique (singleton) kinds when viewed as normal forms.  However,
    -- neutral kinding is also used in subtyping, in particular by the
    -- bound projection rules (<:-⟨|) and (<:-|⟩).  Because the kinds
    -- of neutrals are not unique, neither are the bounds projected by
    -- these subtyping rules, and eliminating adjacent instances of
    -- (<:-⟨|) and (<:-|⟩) becomes difficult.  This, in turn,
    -- complicates transitivity elimination (i.e. a proof that
    -- transitivity of subtyping is admissible) in arbitrary contexts.
    -- However, it does not affect elimination of *top-level*
    -- occurrences of the transitivity rule (<:-trans), i.e. those in
    -- the empty contexts, because there are no closed neutral terms,
    -- and therefore no instances of the bound projection rules in
    -- top-level subtyping statements.

    data _⊢Var_∈_ {n} (Γ : Ctx n) : Fin n → Kind Elim n → Set where
      ⇉-var : ∀ {k} x → Γ ctx → lookup Γ x ≡ kd k → Γ ⊢Var x ∈ k
      ⇇-⇑   : ∀ {x j k} → Γ ⊢Var x ∈ j → Γ ⊢ j <∷ k → Γ ⊢ k kd →
              Γ ⊢Var x ∈ k

    -- Kind synthesis for spines: given the kind of the head and a
    -- spine, synthesize the overall kind of the elimination.
    data _⊢_⇉∙_⇉_ {n} (Γ : Ctx n)
      : Kind Elim n → Spine n → Kind Elim n → Set where
      ⇉-[] : ∀ {k} → Γ ⊢ k ⇉∙ [] ⇉ k
      ⇉-∷  : ∀ {a as j k l} → Γ ⊢Nf a ⇇ j → Γ ⊢ j kd →
             Γ ⊢ k Kind[ a ∈ ⌊ j ⌋ ] ⇉∙ as ⇉ l →
             Γ ⊢ Π j k ⇉∙ a ∷ as ⇉ l

    -- Kind checking for η-long β-normal types.
    data _⊢Nf_⇇_ {n} (Γ : Ctx n) : Elim n → Kind Elim n → Set where
      ⇇-⇑  : ∀ {a j k} → Γ ⊢Nf a ⇉ j → Γ ⊢ j <∷ k → Γ ⊢Nf a ⇇ k

    -- Canonical subkinding derivations.
    data _⊢_<∷_ {n} (Γ : Ctx n) : Kind Elim n → Kind Elim n → Set where
      <∷-⋯ : ∀ {a₁ a₂ b₁ b₂} →
             Γ ⊢ a₂ <: a₁ → Γ ⊢ b₁ <: b₂ → Γ ⊢ a₁ ⋯ b₁ <∷ a₂ ⋯ b₂
      <∷-Π : ∀ {j₁ j₂ k₁ k₂} →
             Γ ⊢ j₂ <∷ j₁ → kd j₂ ∷ Γ ⊢ k₁ <∷ k₂ → Γ ⊢ Π j₁ k₁ kd →
             Γ ⊢ Π j₁ k₁ <∷ Π j₂ k₂

    -- Canonical subtyping of proper types.
    data _⊢_<:_ {n} (Γ : Ctx n) : Elim n → Elim n → Set where
      <:-trans : ∀ {a b c} → Γ ⊢ a <: b → Γ ⊢ b <: c → Γ ⊢ a <: c
      <:-⊥     : ∀ {a} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢ ⊥∙ <: a
      <:-⊤     : ∀ {a} → Γ ⊢Nf a ⇉ a ⋯ a → Γ ⊢ a <: ⊤∙
      <:-∀     : ∀ {k₁ k₂ a₁ a₂} →
                 Γ ⊢ k₂ <∷ k₁ → kd k₂ ∷ Γ ⊢ a₁ <: a₂ →
                 Γ ⊢Nf ∀∙ k₁ a₁ ⇉  ∀∙ k₁ a₁ ⋯ ∀∙ k₁ a₁ →
                 Γ ⊢ ∀∙ k₁ a₁ <: ∀∙ k₂ a₂
      <:-→     : ∀ {a₁ a₂ b₁ b₂} →
                 Γ ⊢ a₂ <: a₁ → Γ ⊢ b₁ <: b₂ → Γ ⊢ a₁ ⇒∙ b₁ <: a₂ ⇒∙ b₂
      <:-∙     : ∀ {x as₁ as₂ k b c} →
                 Γ ⊢Var x ∈ k → Γ ⊢ k ⇉∙ as₁ ≃ as₂ ⇉ b ⋯ c →
                 Γ ⊢ var x ∙ as₁ <: var x ∙ as₂
      <:-⟨|    : ∀ {a b c} → Γ ⊢Ne a ∈ b ⋯ c → Γ ⊢ b <: a
      <:-|⟩    : ∀ {a b c} → Γ ⊢Ne a ∈ b ⋯ c → Γ ⊢ a <: c

    -- Checked/kind-driven subtyping.
    data _⊢_<:_⇇_ {n} (Γ : Ctx n) : Elim n → Elim n → Kind Elim n → Set where
      <:-⇇ : ∀ {a b c d} → Γ ⊢Nf a ⇇ c ⋯ d → Γ ⊢Nf b ⇇ c ⋯ d →
             Γ ⊢ a <: b → Γ ⊢ a <: b ⇇ c ⋯ d
      <:-λ : ∀ {j₁ j₂ a₁ a₂ j k} → kd j ∷ Γ ⊢ a₁ <: a₂ ⇇ k →
             Γ ⊢Nf Λ∙ j₁ a₁ ⇇ Π j k → Γ ⊢Nf Λ∙ j₂ a₂ ⇇ Π j k →
             Γ ⊢ Λ∙ j₁ a₁ <: Λ∙ j₂ a₂ ⇇ Π j k

    -- Canonical kind equality.
    data _⊢_≅_ {n} (Γ : Ctx n) : Kind Elim n → Kind Elim n → Set where
      <∷-antisym : ∀ {j k} → Γ ⊢ j kd → Γ ⊢ k kd →
                   Γ ⊢ j <∷ k → Γ ⊢ k <∷ j → Γ ⊢ j ≅ k

    -- Canonical type equality derivations with checked kinds.
    data _⊢_≃_⇇_ {n} (Γ : Ctx n) : Elim n → Elim n → Kind Elim n → Set where
      <:-antisym : ∀ {a b k} →
                   Γ ⊢ k kd → Γ ⊢ a <: b ⇇ k → Γ ⊢ b <: a ⇇ k → Γ ⊢ a ≃ b ⇇ k

    -- Canonical equality of spines.
    data _⊢_⇉∙_≃_⇉_ {n} (Γ : Ctx n)
      : Kind Elim n → Spine n → Spine n → Kind Elim n → Set where
      ≃-[] : ∀ {k} → Γ ⊢ k ⇉∙ [] ≃ [] ⇉ k
      ≃-∷  : ∀ {a as b bs j k l} →
             Γ ⊢ a ≃ b ⇇ j → Γ ⊢ k Kind[ a ∈ ⌊ j ⌋ ] ⇉∙ as ≃ bs ⇉ l →
             Γ ⊢ Π j k ⇉∙ a ∷ as ≃ b ∷ bs ⇉ l

  -- Well-formed context extensions.
  open ContextFormation _⊢_wf public
    hiding (_wf) renaming (_⊢_wfExt to _⊢_ext)

  -- A wrapper for the _⊢Var_∈_ judgment that also provides term
  -- variable bindings.

  infix 4 _⊢Var′_∈_

  data _⊢Var′_∈_ {n} (Γ : Ctx n) : Fin n → ElimAsc n → Set where
    ∈-tp : ∀ {x k} → Γ ⊢Var x ∈ k → Γ ⊢Var′ x ∈ kd k
    ∈-tm : ∀ x {a} → Γ ctx → lookup Γ x ≡ tp a → Γ ⊢Var′ x ∈ tp a

  -- A derived variable rule.

  ∈-var′ : ∀ {n} {Γ : Ctx n} x → Γ ctx → Γ ⊢Var′ x ∈ lookup Γ x
  ∈-var′ {Γ = Γ} x Γ-ctx with lookup Γ x | inspect (lookup Γ) x
  ∈-var′ x Γ-ctx | kd k | [ Γ[x]≡kd-k ] = ∈-tp (⇉-var x Γ-ctx Γ[x]≡kd-k)
  ∈-var′ x Γ-ctx | tp a | [ Γ[x]≡tp-a ] = ∈-tm x Γ-ctx Γ[x]≡tp-a


------------------------------------------------------------------------
-- Simple properties of canonical kindings

open Syntax
open ElimCtx
open SimpleCtx using (kd; tp; ⌊_⌋Asc)
open Kinding
open ContextConversions using (⌊_⌋Ctx; module ⌊⌋Ctx-Lemmas)

-- An inversion lemma for _⊢_wf.

wf-kd-inv : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ kd k wf → Γ ⊢ k kd
wf-kd-inv (wf-kd k-kd) = k-kd

-- Subkinds have the same shape.

<∷-⌊⌋ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → ⌊ j ⌋ ≡ ⌊ k ⌋
<∷-⌊⌋ (<∷-⋯ _ _)             = refl
<∷-⌊⌋ (<∷-Π j₂<∷j₁ k₁<∷k₂ _) = cong₂ _⇒_ (sym (<∷-⌊⌋ j₂<∷j₁)) (<∷-⌊⌋ k₁<∷k₂)

-- Equal kinds have the same shape.

≅-⌊⌋ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → ⌊ j ⌋ ≡ ⌊ k ⌋
≅-⌊⌋ (<∷-antisym j-kd k-kd j<∷k k<∷j) = <∷-⌊⌋ j<∷k

-- Kind and type equality imply subkinding and subtyping, respectively.

≅⇒<∷ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ j <∷ k
≅⇒<∷ (<∷-antisym j-kd k-kd j<∷k k<∷j) = j<∷k

≃⇒<: : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ⇇ k → Γ ⊢ a <: b ⇇ k
≃⇒<: (<:-antisym k-kd a<:b⇇k b<:a⇇k) = a<:b⇇k

≃⇒<:-⋯ : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a ≃ b ⇇ c ⋯ d → Γ ⊢ a <: b
≃⇒<:-⋯ (<:-antisym c⋯d-kd (<:-⇇ a⇇c⋯d b⇇c⋯d a<:b) b<:a⇇c⋯d) = a<:b

-- Symmetry of kind and type equality.

≅-sym : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ k ≅ j
≅-sym (<∷-antisym j-kd k-kd j<:k k<∷j) = <∷-antisym k-kd j-kd k<∷j j<:k

≃-sym : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ⇇ k → Γ ⊢ b ≃ a ⇇ k
≃-sym (<:-antisym k-kd a<:b b<:a) = <:-antisym k-kd b<:a a<:b

-- Transitivity of checked subtyping and type equality are admissible.

<:⇇-trans : ∀ {n} {Γ : Ctx n} {a b c k} →
            Γ ⊢ a <: b ⇇ k → Γ ⊢ b <: c ⇇ k → Γ ⊢ a <: c ⇇ k
<:⇇-trans (<:-⇇ a₁⇇b⋯c _ a₁<:a₂) (<:-⇇ _ a₃⇇b⋯c a₂<:a₃) =
  <:-⇇ a₁⇇b⋯c a₃⇇b⋯c (<:-trans a₁<:a₂ a₂<:a₃)
<:⇇-trans (<:-λ a₁<:a₂ Λj₁a₁⇇Πjk _) (<:-λ a₂<:a₃ _ Λj₃a₃⇇Πjk) =
  <:-λ (<:⇇-trans a₁<:a₂ a₂<:a₃) Λj₁a₁⇇Πjk Λj₃a₃⇇Πjk

≃-trans : ∀ {n} {Γ : Ctx n} {a b c k} →
          Γ ⊢ a ≃ b ⇇ k → Γ ⊢ b ≃ c ⇇ k → Γ ⊢ a ≃ c ⇇ k
≃-trans (<:-antisym k-kd a<:b⇇k b<:a⇇k) (<:-antisym _ b<:c⇇k c<:b⇇k) =
  <:-antisym k-kd (<:⇇-trans a<:b⇇k b<:c⇇k) (<:⇇-trans c<:b⇇k b<:a⇇k)

-- The synthesized kind of a normal proper type is exactly the singleton
-- containing that type.
Nf⇉-≡ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → a ≡ b × a ≡ c
Nf⇉-≡ (⇉-⊥-f Γ-ctx)       = refl , refl
Nf⇉-≡ (⇉-⊤-f Γ-ctx)       = refl , refl
Nf⇉-≡ (⇉-∀-f k-kd  b⇉b⋯b) = refl , refl
Nf⇉-≡ (⇉-→-f a⇉a⋯a b⇉b⋯b) = refl , refl
Nf⇉-≡ (⇉-s-i a∈b⋯c)       = refl , refl

-- Derived singleton introduction rules where the premises are
-- well-kinded normal forms rather than neutrals.

Nf⇉-s-i : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢Nf a ⇉ a ⋯ a
Nf⇉-s-i a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
Nf⇉-s-i a⇉a⋯a | refl , refl = a⇉a⋯a

Nf⇇-s-i : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢Nf a ⇉ a ⋯ a
Nf⇇-s-i (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)) = Nf⇉-s-i a⇉b₁⋯c₁

-- Inhabitants of interval kinds are proper types.

Nf⇉-⋯-* : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢Nf a ⇇ ⌜*⌝
Nf⇉-⋯-* a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
Nf⇉-⋯-* a⇉a⋯a | refl , refl = ⇇-⇑ a⇉a⋯a (<∷-⋯ (<:-⊥ a⇉a⋯a) (<:-⊤ a⇉a⋯a))

Nf⇇-⋯-* : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢Nf a ⇇ ⌜*⌝
Nf⇇-⋯-* (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)) = Nf⇉-⋯-* a⇉b₁⋯c₁

-- Validity of synthesized kinds: synthesized kinds are well-formed.
Nf⇉-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → Γ ⊢ k kd
Nf⇉-valid (⇉-⊥-f Γ-ctx)       = kd-⋯ (⇉-⊥-f Γ-ctx) (⇉-⊥-f Γ-ctx)
Nf⇉-valid (⇉-⊤-f Γ-ctx)       = kd-⋯ (⇉-⊤-f Γ-ctx) (⇉-⊤-f Γ-ctx)
Nf⇉-valid (⇉-∀-f k-kd a⇉a⋯a)  = kd-⋯ (⇉-∀-f k-kd a⇉a⋯a) (⇉-∀-f k-kd a⇉a⋯a)
Nf⇉-valid (⇉-→-f a⇉a⋯a b⇉b⋯b) = kd-⋯ (⇉-→-f a⇉a⋯a b⇉b⋯b) (⇉-→-f a⇉a⋯a b⇉b⋯b)
Nf⇉-valid (⇉-Π-i j-kd a⇉k)    = kd-Π j-kd (Nf⇉-valid a⇉k)
Nf⇉-valid (⇉-s-i a∈b⋯c)       = kd-⋯ (⇉-s-i a∈b⋯c) (⇉-s-i a∈b⋯c)

-- Validity of checked subtyping: the checked subtyping judgment
-- relates well-kinded types.

<:⇇-valid : ∀ {n} {Γ : Ctx n} {a b k} →
            Γ ⊢ a <: b ⇇ k → Γ ⊢Nf a ⇇ k × Γ ⊢Nf b ⇇ k
<:⇇-valid (<:-⇇ a⇇k b⇇k a<:b)               = a⇇k , b⇇k
<:⇇-valid (<:-λ a₁<:a₂ Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) = Λj₁a₁⇇Πjk , Λj₂a₂⇇Πjk

-- Validity of kind and type equality: the equality judgments relate
-- well-formed kinds, resp. well-kinded types.

≅-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ j kd × Γ ⊢ k kd
≅-valid (<∷-antisym j-kd k-kd j<∷k k<∷j) = j-kd , k-kd

≃-valid : ∀ {n} {Γ : Ctx n} {a b k} →
          Γ ⊢ a ≃ b ⇇ k → Γ ⊢Nf a ⇇ k × Γ ⊢Nf b ⇇ k
≃-valid (<:-antisym k-kd a<:b⇇k b<:a⇇k) = <:⇇-valid a<:b⇇k

≃-valid-kd : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ⇇ k → Γ ⊢ k kd
≃-valid-kd (<:-antisym k-kd a<:b b<:a) = k-kd

-- NOTE.  In order to prove validity for the remainder of the kinding,
-- subkinding and subtyping judgments, we first need to prove that
-- hereditary substitutions preserve well-formedness of kinds (see
-- Kinding.Canonical.HereditarySubstitution).  See the definition of
-- `Var∈-valid' below and the module Kinding.Canonical.Validity for
-- the remaining (strong) validity lemmas.

-- The synthesized kinds of neutrals kind-check.
Nf⇇-ne : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Ne a ∈ b ⋯ c → Γ ⊢Nf a ⇇ b ⋯ c
Nf⇇-ne (∈-∙ x∈k k⇉as⇉b⋯c) =
  ⇇-⇑ (⇉-s-i (∈-∙ x∈k k⇉as⇉b⋯c))
      (<∷-⋯ (<:-⟨| (∈-∙ x∈k k⇉as⇉b⋯c)) (<:-|⟩ (∈-∙ x∈k k⇉as⇉b⋯c)))

-- The contexts of (most of) the above judgments are well-formed.
--
-- NOTE. The exceptions are kinding and equality of spines, as the
-- ⇉-[] and ≃-[] rules offer no guarantee that the enclosing context
-- is well-formed.  This is not a problem in practice, since
-- well-kinded spines are used in the kinding of neutral types, the
-- head of which is guaranteed to be kinded in a well-formed context.
mutual

  kd-ctx : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ctx
  kd-ctx (kd-⋯ a⇉a⋯a b⇉b⋯b) = Nf⇉-ctx a⇉a⋯a
  kd-ctx (kd-Π j-kd  k-kd)  = kd-ctx j-kd

  Nf⇉-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → Γ ctx
  Nf⇉-ctx (⇉-⊥-f Γ-ctx)       = Γ-ctx
  Nf⇉-ctx (⇉-⊤-f Γ-ctx)       = Γ-ctx
  Nf⇉-ctx (⇉-∀-f k-kd  a⇉a⋯a) = kd-ctx k-kd
  Nf⇉-ctx (⇉-→-f a⇉a⋯a b⇉b⋯b) = Nf⇉-ctx a⇉a⋯a
  Nf⇉-ctx (⇉-Π-i j-kd  a⇉k)   = kd-ctx j-kd
  Nf⇉-ctx (⇉-s-i a∈b⋯c)       = Ne∈-ctx a∈b⋯c

  Ne∈-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Ne a ∈ k → Γ ctx
  Ne∈-ctx (∈-∙ x∈j j⇉as⇉k) = Var∈-ctx x∈j

  Var∈-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Var a ∈ k → Γ ctx
  Var∈-ctx (⇉-var x Γ-ctx _)   = Γ-ctx
  Var∈-ctx (⇇-⇑ x∈j j<∷k k-kd) = Var∈-ctx x∈j

  Nf⇇-ctx : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇇ k → Γ ctx
  Nf⇇-ctx (⇇-⇑ a⇉j j<∷k) = Nf⇉-ctx a⇉j

mutual

  <∷-ctx : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ ctx
  <∷-ctx (<∷-⋯ b₁<:a₁ a₂<:b₂)          = <:-ctx b₁<:a₁
  <∷-ctx (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) = <∷-ctx j₂<∷j₁

  <:-ctx : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a <: b → Γ ctx
  <:-ctx (<:-trans a<:b b<:c)   = <:-ctx a<:b
  <:-ctx (<:-⊥ a⇉a⋯a)           = Nf⇉-ctx a⇉a⋯a
  <:-ctx (<:-⊤ a⇉a⋯a)           = Nf⇉-ctx a⇉a⋯a
  <:-ctx (<:-∀ k₂<∷k₁ a₁<:a₂ _) = <∷-ctx k₂<∷k₁
  <:-ctx (<:-→ a₂<:a₁ b₁<:b₂)   = <:-ctx a₂<:a₁
  <:-ctx (<:-∙ x∈j as<:bs)      = Var∈-ctx x∈j
  <:-ctx (<:-⟨| a∈b⋯c)          = Ne∈-ctx a∈b⋯c
  <:-ctx (<:-|⟩ a∈b⋯c)          = Ne∈-ctx a∈b⋯c

  ≅-ctx : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ctx
  ≅-ctx (<∷-antisym j-kd k-kd j<∷k k<∷j) = <∷-ctx j<∷k

wf-ctx : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → Γ ctx
wf-ctx (wf-kd k-kd)  = kd-ctx k-kd
wf-ctx (wf-tp a⇉a⋯a) = Nf⇉-ctx a⇉a⋯a

<:⇇-ctx : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ⇇ k → Γ ctx
<:⇇-ctx (<:-⇇ a⇇k b⇇k a<:b)               = Nf⇇-ctx a⇇k
<:⇇-ctx (<:-λ a₁<:a₂ Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) = Nf⇇-ctx Λj₁a₁⇇Πjk

≃-ctx : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ⇇ k → Γ ctx
≃-ctx (<:-antisym k-kd a<:b b<:a) = <:⇇-ctx a<:b

Var′∈-ctx : ∀ {n} {Γ : Ctx n} {x a} → Γ ⊢Var′ x ∈ a → Γ ctx
Var′∈-ctx (∈-tp x∈k)       = Var∈-ctx x∈k
Var′∈-ctx (∈-tm _ Γ-ctx _) = Γ-ctx

-- An admissible formation rule for the kind of proper types.

kd-⌜*⌝ : ∀ {n} {Γ : Ctx n} → Γ ctx → Γ ⊢ ⌜*⌝ kd
kd-⌜*⌝ Γ-ctx = kd-⋯ (⇉-⊥-f Γ-ctx) (⇉-⊤-f Γ-ctx)

-- Admissible formation rules for canonically kinded proper types.

Nf⇇-∀-f : ∀ {n} {Γ : Ctx n} {k a} →
          Γ ⊢ k kd → kd k ∷ Γ ⊢Nf a ⇇ ⌜*⌝ → Γ ⊢Nf ∀∙ k a ⇇ ⌜*⌝
Nf⇇-∀-f k-kd a⇇* =
  let a⇉a⋯a = Nf⇇-s-i a⇇*
  in Nf⇉-⋯-* (⇉-∀-f k-kd a⇉a⋯a)

Nf⇇-→-f : ∀ {n} {Γ : Ctx n} {a b} →
          Γ ⊢Nf a ⇇ ⌜*⌝ → Γ ⊢Nf b ⇇ ⌜*⌝ → Γ ⊢Nf a ⇒∙ b ⇇ ⌜*⌝
Nf⇇-→-f a⇇* b⇇* =
  let a⇉a⋯a = Nf⇇-s-i a⇇*
      b⇉b⋯b = Nf⇇-s-i b⇇*
  in Nf⇉-⋯-* (⇉-→-f a⇉a⋯a b⇉b⋯b)

-- Admissible kinding and equality rules for appending a normal form
-- to a spine.

⇉-∷ʳ : ∀ {n} {Γ : Ctx n} {as : Spine n} {a j k l} →
       Γ ⊢ j ⇉∙ as ⇉ Π k l → Γ ⊢Nf a ⇇ k → Γ ⊢ k kd →
       Γ ⊢ j ⇉∙ as ∷ʳ a ⇉ l Kind[ a ∈ ⌊ k ⌋ ]
⇉-∷ʳ ⇉-[]                       a⇇k k-kd = ⇉-∷ a⇇k k-kd ⇉-[]
⇉-∷ʳ (⇉-∷ a⇇j j-kd k[a]⇉as⇉Πlm) b⇇l l-kd =
  ⇉-∷ a⇇j j-kd (⇉-∷ʳ k[a]⇉as⇉Πlm b⇇l l-kd)

≃-∷ʳ : ∀ {n} {Γ : Ctx n} {as bs : Spine n} {a b j k l} →
       Γ ⊢ j ⇉∙ as ≃ bs ⇉ Π k l → Γ ⊢ a ≃ b ⇇ k →
       Γ ⊢ j ⇉∙ as ∷ʳ a ≃ bs ∷ʳ b ⇉ l Kind[ a ∈ ⌊ k ⌋ ]
≃-∷ʳ ≃-[]            a≃b = ≃-∷ a≃b ≃-[]
≃-∷ʳ (≃-∷ a≃b as≃bs) c≃d = ≃-∷ a≃b (≃-∷ʳ as≃bs c≃d)


----------------------------------------------------------------------
-- Well-kinded variable substitutions in canonically kinded types
--
-- We define two different kinds of well-kinded variable
-- substitutions:
--
--  1. well-kinded renamings, which don't change kinds of variables,
--
--  2. variable substitutions that also allow conversion/subsumption.
--
-- The first kind are used to prove e.g. that weakening preserve
-- (canonical) well-kindedness, while the second kind are used to
-- prove context conversion/narrowing preserves well-kindedness.  The
-- two definitions share a common generic core, which is instantiated
-- to obtain the concrete definitions.  The two separate definitions
-- are necessary because the latter requires the weakening lemma,
-- which in turn depends on the former.

-- Liftings between variable typings

record LiftTo-Var′∈ (_⊢V_∈_ : Typing ElimAsc Fin ElimAsc lzero) : Set₁ where
  open Substitution using (weakenElimAsc; _ElimAsc/Var_)

  typedSub : TypedSub ElimAsc Fin lzero
  typedSub = record
    { _⊢_wf               = _⊢_wf
    ; _⊢_∈_               = _⊢V_∈_
    ; typeExtension       = record { weaken = weakenElimAsc }
    ; typeTermApplication = record { _/_ = _ElimAsc/Var_ }
    ; termSimple          = VarSubst.simple
    }
  open TypedSub typedSub public
    renaming (_⊢/_∈_ to _⊢/Var_∈_) hiding (_⊢_wf; _⊢_∈_; typeExtension)

  -- Simple typed variable substitutions.

  field typedSimple : TypedSimple typedSub
  open TypedSimple typedSimple public renaming (lookup to /∈-lookup)

  -- Lifts well-typed Term₁-terms to well-typed Term₂-terms.

  field ∈-lift : ∀ {n} {Γ : Ctx n} {x a} → Γ ⊢V x ∈ a → Γ ⊢Var′ x ∈ a

module TypedVarSubstApp (_⊢V_∈_ : Typing ElimAsc Fin ElimAsc lzero)
                        (liftTyped : LiftTo-Var′∈ _⊢V_∈_)
                        where

  open LiftTo-Var′∈ liftTyped
  open Substitution hiding (subst; _/Var_) renaming (_Elim/Var_ to _/Var_)
  open RenamingCommutes using (Kind[∈⌊⌋]-/Var)

  -- A helper.

  ∈-↑′ : ∀ {m n} {Δ : Ctx n} {Γ : Ctx m} {k ρ} →
         Δ ⊢ k Kind′/Var ρ kd → Δ ⊢/Var ρ ∈ Γ →
         kd (k Kind′/Var ρ) ∷ Δ ⊢/Var ρ VarSubst.↑ ∈ kd k ∷ Γ
  ∈-↑′ k/ρ-kd ρ∈Γ = ∈-↑ (wf-kd k/ρ-kd) ρ∈Γ

  -- Convert between well-kindedness judgments for variables.

  V∈-Var∈ : ∀ {n} {Γ : Ctx n} {x a k} → a ≡ kd k →
            Γ ⊢V x ∈ a → Γ ⊢Var x ∈ k
  V∈-Var∈ refl xT∈kd-k with ∈-lift xT∈kd-k
  V∈-Var∈ refl xT∈kd-k | ∈-tp x∈k = x∈k

  mutual

    -- Renamings preserve well-formedness of ascriptions.

    wf-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a ρ} →
              Γ ⊢ a wf → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ a ElimAsc/Var ρ wf
    wf-/Var (wf-kd k-kd)  ρ∈Γ = wf-kd (kd-/Var k-kd ρ∈Γ)
    wf-/Var (wf-tp a⇉a⋯a) ρ∈Γ = wf-tp (Nf⇉-/Var a⇉a⋯a ρ∈Γ)

    -- Renamings preserve well-formedness of kinds.

    kd-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k ρ} →
              Γ ⊢ k kd → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ k Kind′/Var ρ kd
    kd-/Var (kd-⋯ a⇉a⋯a b⇉b⋯b) ρ∈Γ =
      kd-⋯ (Nf⇉-/Var a⇉a⋯a ρ∈Γ) (Nf⇉-/Var b⇉b⋯b ρ∈Γ)
    kd-/Var (kd-Π j-kd  k-kd) ρ∈Γ =
      let j/ρ-kd = kd-/Var j-kd ρ∈Γ
      in kd-Π j/ρ-kd (kd-/Var k-kd (∈-↑′ j/ρ-kd ρ∈Γ))

    -- Renamings preserve synthesized kinds of normal types.

    Nf⇉-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k ρ} →
               Γ ⊢Nf a ⇉ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Nf a /Var ρ ⇉ k Kind′/Var ρ
    Nf⇉-/Var (⇉-⊥-f Γ-ctx)       ρ∈Γ = ⇉-⊥-f (/∈-wf ρ∈Γ)
    Nf⇉-/Var (⇉-⊤-f Γ-ctx)       ρ∈Γ = ⇉-⊤-f (/∈-wf ρ∈Γ)
    Nf⇉-/Var (⇉-∀-f k-kd a⇉a⋯a)  ρ∈Γ =
      let k/ρ-kd = kd-/Var k-kd ρ∈Γ
      in ⇉-∀-f k/ρ-kd (Nf⇉-/Var a⇉a⋯a (∈-↑′ k/ρ-kd ρ∈Γ))
    Nf⇉-/Var (⇉-→-f a⇉a⋯a b⇉b⋯b) ρ∈Γ =
      ⇉-→-f (Nf⇉-/Var a⇉a⋯a ρ∈Γ) (Nf⇉-/Var b⇉b⋯b ρ∈Γ)
    Nf⇉-/Var (⇉-Π-i j-kd a⇉k)    ρ∈Γ =
      let j/ρ-kd = kd-/Var j-kd ρ∈Γ
      in ⇉-Π-i j/ρ-kd (Nf⇉-/Var a⇉k (∈-↑′ j/ρ-kd ρ∈Γ))
    Nf⇉-/Var (⇉-s-i a∈b⋯c)       ρ∈Γ = ⇉-s-i (Ne∈-/Var a∈b⋯c ρ∈Γ)

    -- Renamings preserve the kinds of variables.

    Var∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {x k ρ} →
                Γ ⊢Var x ∈ k → Δ ⊢/Var ρ ∈ Γ →
                Δ ⊢Var (Vec.lookup ρ x) ∈ k Kind′/Var ρ
    Var∈-/Var {ρ = ρ} (⇉-var x Γ-ctx Γ[x]≡kd-k) ρ∈Γ =
      V∈-Var∈ (cong (_ElimAsc/Var ρ) Γ[x]≡kd-k) (/∈-lookup ρ∈Γ x)
    Var∈-/Var (⇇-⇑ x∈j j<∷k k-kd) ρ∈Γ =
      ⇇-⇑ (Var∈-/Var x∈j ρ∈Γ) (<∷-/Var j<∷k ρ∈Γ) (kd-/Var k-kd ρ∈Γ)

    -- Renamings preserve synthesized kinds of neutral types.

    Ne∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k ρ} →
               Γ ⊢Ne a ∈ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Ne a /Var ρ ∈ k Kind′/Var ρ
    Ne∈-/Var (∈-∙ x∈j k⇉as⇉l) ρ∈Γ =
      ∈-∙ (Var∈-/Var x∈j ρ∈Γ) (Sp⇉-/Var k⇉as⇉l ρ∈Γ)

    -- Renamings preserve spine kindings.

    Sp⇉-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as j k ρ} →
               Γ ⊢ j ⇉∙ as ⇉ k → Δ ⊢/Var ρ ∈ Γ →
               Δ ⊢ j Kind′/Var ρ ⇉∙ as //Var ρ ⇉ k Kind′/Var ρ
    Sp⇉-/Var ⇉-[]                                ρ∈Γ = ⇉-[]
    Sp⇉-/Var (⇉-∷ {a} {_} {j} {k} a⇇j j-kd k[a]⇉as⇉l) ρ∈Γ =
      ⇉-∷ (Nf⇇-/Var a⇇j ρ∈Γ) (kd-/Var j-kd ρ∈Γ)
          (subst (_ ⊢_⇉∙ _ ⇉ _) (Kind[∈⌊⌋]-/Var k a j)
                 (Sp⇉-/Var k[a]⇉as⇉l ρ∈Γ))

    -- Renamings preserve checked kinds of neutral types.

    Nf⇇-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k ρ} →
               Γ ⊢Nf a ⇇ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Nf a /Var ρ ⇇ k Kind′/Var ρ
    Nf⇇-/Var (⇇-⇑ a⇉j j<∷k) ρ∈Γ = ⇇-⇑ (Nf⇉-/Var a⇉j ρ∈Γ) (<∷-/Var j<∷k ρ∈Γ)

    -- Renamings preserve subkinding.

    <∷-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k ρ} →
              Γ ⊢ j <∷ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ j Kind′/Var ρ <∷ k Kind′/Var ρ
    <∷-/Var (<∷-⋯ a₂<:a₁ b₁<:b₂) ρ∈Γ =
      <∷-⋯ (<:-/Var a₂<:a₁ ρ∈Γ) (<:-/Var b₁<:b₂ ρ∈Γ)
    <∷-/Var (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) ρ∈Γ =
      <∷-Π (<∷-/Var j₂<∷j₁ ρ∈Γ)
           (<∷-/Var k₁<∷k₂ (∈-↑ (<∷-/Var-wf k₁<∷k₂ ρ∈Γ) ρ∈Γ))
           (kd-/Var Πj₁k₁-kd ρ∈Γ)

    -- Renamings preserve subtyping.

    <:-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b ρ} →
              Γ ⊢ a <: b → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ a /Var ρ <: b /Var ρ
    <:-/Var (<:-trans a<:b b<:c) ρ∈Γ =
      <:-trans (<:-/Var a<:b ρ∈Γ) (<:-/Var b<:c ρ∈Γ)
    <:-/Var (<:-⊥ a⇉a⋯a) ρ∈Γ = <:-⊥ (Nf⇉-/Var a⇉a⋯a ρ∈Γ)
    <:-/Var (<:-⊤ a⇉a⋯a) ρ∈Γ = <:-⊤ (Nf⇉-/Var a⇉a⋯a ρ∈Γ)
    <:-/Var (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) ρ∈Γ =
      <:-∀ (<∷-/Var k₂<∷k₁ ρ∈Γ)
           (<:-/Var a₁<:a₂ (∈-↑ (<:-/Var-wf a₁<:a₂ ρ∈Γ) ρ∈Γ))
           (Nf⇉-/Var Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁ ρ∈Γ)
    <:-/Var (<:-→ a₂<:a₁ b₁<:b₂) ρ∈Γ =
      <:-→ (<:-/Var a₂<:a₁ ρ∈Γ) (<:-/Var b₁<:b₂ ρ∈Γ)
    <:-/Var (<:-∙ x∈j j⇉as₁<:as₂⇉k) ρ∈Γ =
      <:-∙ (Var∈-/Var x∈j ρ∈Γ) (Sp≃-/Var j⇉as₁<:as₂⇉k ρ∈Γ)
    <:-/Var (<:-⟨| a∈b⋯c) ρ∈Γ = <:-⟨| (Ne∈-/Var a∈b⋯c ρ∈Γ)
    <:-/Var (<:-|⟩ a∈b⋯c) ρ∈Γ = <:-|⟩ (Ne∈-/Var a∈b⋯c ρ∈Γ)

    <:⇇-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b k ρ} →
               Γ ⊢ a <: b ⇇ k → Δ ⊢/Var ρ ∈ Γ →
               Δ ⊢ a /Var ρ <: b /Var ρ ⇇ k Kind′/Var ρ
    <:⇇-/Var (<:-⇇ a⇇k b⇇k a<:b) ρ∈Γ =
      <:-⇇ (Nf⇇-/Var a⇇k ρ∈Γ) (Nf⇇-/Var b⇇k ρ∈Γ) (<:-/Var a<:b ρ∈Γ)
    <:⇇-/Var (<:-λ a₁<:a₂ Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) ρ∈Γ =
      <:-λ (<:⇇-/Var a₁<:a₂ (∈-↑ (<:⇇-/Var-wf a₁<:a₂ ρ∈Γ) ρ∈Γ))
           (Nf⇇-/Var Λj₁a₁⇇Πjk ρ∈Γ) (Nf⇇-/Var Λj₂a₂⇇Πjk ρ∈Γ)

    -- Renamings preserve type equality.

    ≃-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b k ρ} →
              Γ ⊢ a ≃ b ⇇ k → Δ ⊢/Var ρ ∈ Γ →
              Δ ⊢ a /Var ρ ≃ b /Var ρ ⇇ k Kind′/Var ρ
    ≃-/Var (<:-antisym k-kd a<:b b<:a) ρ∈Γ =
      <:-antisym (kd-/Var k-kd ρ∈Γ) (<:⇇-/Var a<:b ρ∈Γ) (<:⇇-/Var b<:a ρ∈Γ)

    Sp≃-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as bs j k ρ} →
                Γ ⊢ j ⇉∙ as ≃ bs ⇉ k → Δ ⊢/Var ρ ∈ Γ →
                Δ ⊢ j Kind′/Var ρ ⇉∙ as //Var ρ ≃ bs //Var ρ ⇉ k Kind′/Var ρ
    Sp≃-/Var ≃-[] ρ∈Γ = ≃-[]
    Sp≃-/Var (≃-∷ {a} {_} {_} {_} {j} {k} a≃b as≃bs) ρ∈Γ =
      ≃-∷ (≃-/Var a≃b ρ∈Γ)
          (subst (_ ⊢_⇉∙ _ ≃ _ ⇉ _) (Kind[∈⌊⌋]-/Var k a j)
                 (Sp≃-/Var as≃bs ρ∈Γ))

    -- Helpers (to satisfy the termination checker).
    --
    -- These are simply (manual) expansions of the form
    --
    --   XX-/Var-wf x ρ∈Γ  =  wf-/Var (wf-∷₁ (XX-ctx x)) ρ∈Γ
    --
    -- to ensure the above definitions remain structurally recursive
    -- in the various derivations.

    kd-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k ρ} →
                 kd j ∷ Γ ⊢ k kd → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ kd (j Kind′/Var ρ) wf
    kd-/Var-wf (kd-⋯ a∈a⋯a _) ρ∈Γ = Nf⇉-/Var-wf a∈a⋯a ρ∈Γ
    kd-/Var-wf (kd-Π j-kd _)  ρ∈Γ = kd-/Var-wf j-kd ρ∈Γ

    Nf⇉-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k ρ} →
                  kd j ∷ Γ ⊢Nf a ⇉ k → Δ ⊢/Var ρ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var ρ) wf
    Nf⇉-/Var-wf (⇉-⊥-f (j-wf ∷ _)) ρ∈Γ = wf-/Var j-wf ρ∈Γ
    Nf⇉-/Var-wf (⇉-⊤-f (j-wf ∷ _)) ρ∈Γ = wf-/Var j-wf ρ∈Γ
    Nf⇉-/Var-wf (⇉-∀-f k-kd _)     ρ∈Γ = kd-/Var-wf k-kd ρ∈Γ
    Nf⇉-/Var-wf (⇉-→-f a⇉a⋯a _)    ρ∈Γ = Nf⇉-/Var-wf a⇉a⋯a ρ∈Γ
    Nf⇉-/Var-wf (⇉-Π-i j-kd _)     ρ∈Γ = kd-/Var-wf j-kd ρ∈Γ
    Nf⇉-/Var-wf (⇉-s-i a∈b⋯c)      ρ∈Γ = Ne∈-/Var-wf a∈b⋯c ρ∈Γ

    Ne∈-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k ρ} →
                  kd j ∷ Γ ⊢Ne a ∈ k → Δ ⊢/Var ρ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var ρ) wf
    Ne∈-/Var-wf (∈-∙ x∈k _) ρ∈Γ = Var∈-/Var-wf x∈k ρ∈Γ

    Var∈-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k ρ} →
                   kd j ∷ Γ ⊢Var a ∈ k → Δ ⊢/Var ρ ∈ Γ →
                   Δ ⊢ kd (j Kind′/Var ρ) wf
    Var∈-/Var-wf (⇉-var x (j-wf ∷ _) _) ρ∈Γ = wf-/Var j-wf ρ∈Γ
    Var∈-/Var-wf (⇇-⇑ x∈j _ _)          ρ∈Γ = Var∈-/Var-wf x∈j ρ∈Γ

    Nf⇇-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k ρ} →
                  kd j ∷ Γ ⊢Nf a ⇇ k → Δ ⊢/Var ρ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var ρ) wf
    Nf⇇-/Var-wf (⇇-⇑ a⇉j _) ρ∈Γ = Nf⇉-/Var-wf a⇉j ρ∈Γ

    <∷-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k l ρ} →
                 kd j ∷ Γ ⊢ k <∷ l → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ kd (j Kind′/Var ρ) wf
    <∷-/Var-wf (<∷-⋯ a₂<:a₁ _)   ρ∈Γ = <:-/Var-wf a₂<:a₁ ρ∈Γ
    <∷-/Var-wf (<∷-Π j₂<∷j₁ _ _) ρ∈Γ = <∷-/Var-wf j₂<∷j₁ ρ∈Γ

    <:-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j ρ} →
                 kd j ∷ Γ ⊢ a <: b → Δ ⊢/Var ρ ∈ Γ →
                 Δ ⊢ kd (j Kind′/Var ρ) wf
    <:-/Var-wf (<:-trans a<:b _) ρ∈Γ = <:-/Var-wf a<:b ρ∈Γ
    <:-/Var-wf (<:-⊥ a⇉a⋯a)      ρ∈Γ = Nf⇉-/Var-wf a⇉a⋯a ρ∈Γ
    <:-/Var-wf (<:-⊤ a⇉a⋯a)      ρ∈Γ = Nf⇉-/Var-wf a⇉a⋯a ρ∈Γ
    <:-/Var-wf (<:-∀ k₂<∷k₁ _ _) ρ∈Γ = <∷-/Var-wf k₂<∷k₁ ρ∈Γ
    <:-/Var-wf (<:-→ a₂<:a₁ _)   ρ∈Γ = <:-/Var-wf a₂<:a₁ ρ∈Γ
    <:-/Var-wf (<:-∙ x∈j _)      ρ∈Γ = Var∈-/Var-wf x∈j ρ∈Γ
    <:-/Var-wf (<:-⟨| a∈b⋯c)     ρ∈Γ = Ne∈-/Var-wf a∈b⋯c ρ∈Γ
    <:-/Var-wf (<:-|⟩ a∈b⋯c)     ρ∈Γ = Ne∈-/Var-wf a∈b⋯c ρ∈Γ

    <:⇇-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j k ρ} →
                  kd j ∷ Γ ⊢ a <: b ⇇ k → Δ ⊢/Var ρ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var ρ) wf
    <:⇇-/Var-wf (<:-⇇ a⇇k _ _)       ρ∈Γ = Nf⇇-/Var-wf a⇇k ρ∈Γ
    <:⇇-/Var-wf (<:-λ _ Λj₁a₁⇇Πjk _) ρ∈Γ = Nf⇇-/Var-wf Λj₁a₁⇇Πjk ρ∈Γ

    ≅-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k l ρ} →
                kd j ∷ Γ ⊢ k ≅ l → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ kd (j Kind′/Var ρ) wf
    ≅-/Var-wf (<∷-antisym _ _ j<∷k _) ρ∈Γ = <∷-/Var-wf j<∷k ρ∈Γ

  -- Renamings preserve kind equality.

  ≅-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k ρ} →
           Γ ⊢ j ≅ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ j Kind′/Var ρ ≅ k Kind′/Var ρ
  ≅-/Var (<∷-antisym j-kd k-kd j<∷k k<∷j) ρ∈Γ =
    <∷-antisym (kd-/Var j-kd ρ∈Γ) (kd-/Var k-kd ρ∈Γ)
               (<∷-/Var j<∷k ρ∈Γ) (<∷-/Var k<∷j ρ∈Γ)

  -- Renamings preserve wrapped variable typing

  Var′∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {x k ρ} →
               Γ ⊢Var′ x ∈ k → Δ ⊢/Var ρ ∈ Γ →
               Δ ⊢Var′ (Vec.lookup ρ x) ∈ k ElimAsc/Var ρ
  Var′∈-/Var         (∈-tp x∈k)               ρ∈Γ = ∈-tp (Var∈-/Var x∈k ρ∈Γ)
  Var′∈-/Var {ρ = ρ} (∈-tm x Γ-ctx Γ[x]≡tp-t) ρ∈Γ =
    subst (_ ⊢Var′ _ ∈_) (cong (_ElimAsc/Var ρ) Γ[x]≡tp-t)
          (∈-lift (/∈-lookup ρ∈Γ x))

-- Well-kinded renamings in canonically kinded types, i.e. lemmas
-- showing that renaming preserves kinding.
--
-- Note that these are pure renamings that cannot change the kinds of
-- variables (i.e. they cannot be used to implement context conversion
-- or narrowing).

module KindedRenaming where
  open Substitution using (termLikeLemmasElimAsc)

  typedVarSubst : TypedVarSubst ElimAsc lzero
  typedVarSubst = record
    { _⊢_wf              = _⊢_wf
    ; typeExtension      = ElimCtx.weakenOps
    ; typeVarApplication = AppLemmas.application appLemmas
    ; wf-wf              = wf-ctx
    ; /-wk               = refl
    ; id-vanishes        = id-vanishes
    ; /-⊙                 = /-⊙
    }
    where
      open TermLikeLemmas termLikeLemmasElimAsc using (varLiftAppLemmas)
      open LiftAppLemmas  varLiftAppLemmas

  open TypedVarSubst typedVarSubst
    hiding (_⊢_wf) renaming (_⊢Var_∈_ to _⊢GenVar_∈_)

  -- Liftings from generic variable typings to variable kindings.

  liftTyped : LiftTo-Var′∈ _⊢GenVar_∈_
  liftTyped = record
    { typedSimple  = typedSimple
    ; ∈-lift       = ∈-lift
    }
    where
      ∈-lift : ∀ {n} {Γ : Ctx n} {x a} → Γ ⊢GenVar x ∈ a → Γ ⊢Var′ x ∈ a
      ∈-lift (∈-var x Γ-ctx) = ∈-var′ x Γ-ctx

  open TypedVarSubstApp _⊢GenVar_∈_ liftTyped public
  open Substitution hiding (subst)

  -- Weakening preserves well-formedness of kinds.

  kd-weaken : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢ a wf → Γ ⊢ k kd → a ∷ Γ ⊢ weakenKind′ k kd
  kd-weaken a-wf k-kd = kd-/Var k-kd (∈-wk a-wf)

  -- Weakening preserves variable kinding.

  Var∈-weaken : ∀ {n} {Γ : Ctx n} {a x k} → Γ ⊢ a wf →
                Γ ⊢Var x ∈ k →
                a ∷ Γ ⊢Var Vec.lookup VarSubst.wk x ∈ weakenKind′ k
  Var∈-weaken a-wf x∈k = Var∈-/Var x∈k (∈-wk a-wf)

  Var′∈-weaken : ∀ {n} {Γ : Ctx n} {a x b} → Γ ⊢ a wf →
                 Γ ⊢Var′ x ∈ b → a ∷ Γ ⊢Var′ suc x ∈ weakenElimAsc b
  Var′∈-weaken a-wf x∈b =
    subst (_ ⊢Var′_∈ _) VarLemmas./-wk (Var′∈-/Var x∈b (∈-wk a-wf))

  -- Weakening preserves spine kinding.

  Sp⇉-weaken : ∀ {n} {Γ : Ctx n} {a bs j k} → Γ ⊢ a wf → Γ ⊢ j ⇉∙ bs ⇉ k →
               a ∷ Γ ⊢ weakenKind′ j ⇉∙ weakenSpine bs ⇉ weakenKind′ k
  Sp⇉-weaken a-wf j⇉bs⇉k = Sp⇉-/Var j⇉bs⇉k (∈-wk a-wf)

  -- Weakening preserves checked kinding.

  Nf⇇-weaken : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a wf →
               Γ ⊢Nf b ⇇ k → (a ∷ Γ) ⊢Nf weakenElim b ⇇ weakenKind′ k
  Nf⇇-weaken a-wf b⇇k = Nf⇇-/Var b⇇k (∈-wk a-wf)

  -- Weakening preserves subkinding.

  <∷-weaken : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢ a wf →
              Γ ⊢ j <∷ k → (a ∷ Γ) ⊢ weakenKind′ j <∷ weakenKind′ k
  <∷-weaken a-wf j<∷k = <∷-/Var j<∷k (∈-wk a-wf)

  -- Weakening preserves subtyping.

  <:-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b <: c →
              a ∷ Γ ⊢ weakenElim b <: weakenElim c
  <:-weaken a-wf b<:c = <:-/Var b<:c (∈-wk a-wf)

  <:⇇-weaken : ∀ {n} {Γ : Ctx n} {a b c k} → Γ ⊢ a wf → Γ ⊢ b <: c ⇇ k →
               a ∷ Γ ⊢ weakenElim b <: weakenElim c ⇇ weakenKind′ k
  <:⇇-weaken a-wf b<:c = <:⇇-/Var b<:c (∈-wk a-wf)

  -- Weakening preserves well-formedness of ascriptions.

  wf-weaken : ∀ {n} {Γ : Ctx n} {a b} →
              Γ ⊢ a wf → Γ ⊢ b wf → a ∷ Γ ⊢ weakenElimAsc b wf
  wf-weaken a-wf b-wf = wf-/Var b-wf (∈-wk a-wf)

  -- Weakening preserves kind and type equality.

  ≃-weaken : ∀ {n} {Γ : Ctx n} {a b c k} → Γ ⊢ a wf → Γ ⊢ b ≃ c ⇇ k →
              a ∷ Γ ⊢ weakenElim b ≃ weakenElim c ⇇ weakenKind′ k
  ≃-weaken a-wf b≃c = ≃-/Var b≃c (∈-wk a-wf)

  ≅-weaken : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢ a wf → Γ ⊢ j ≅ k →
             a ∷ Γ ⊢ weakenKind′ j ≅ weakenKind′ k
  ≅-weaken a-wf j≅k = ≅-/Var j≅k (∈-wk a-wf)

  Sp≃-weaken : ∀ {n} {Γ : Ctx n} {a bs cs j k} → Γ ⊢ a wf →
               Γ ⊢ j ⇉∙ bs ≃ cs ⇉ k →
               a ∷ Γ ⊢ weakenKind′ j ⇉∙ weakenSpine bs ≃ weakenSpine cs ⇉
                 weakenKind′ k
  Sp≃-weaken a-wf bs≃cs = Sp≃-/Var bs≃cs (∈-wk a-wf)

-- Operations on well-formed contexts that require weakening of
-- well-formedness judgments.

module WfCtxOps where
  open KindedRenaming using (wf-weaken)

  wfWeakenOps : WellFormedWeakenOps weakenOps
  wfWeakenOps = record { wf-weaken = wf-weaken }

  open WellFormedWeakenOps wfWeakenOps public
    hiding (wf-weaken) renaming (lookup to lookup-wf)

  -- Lookup the kind of a type variable in a well-formed context.

  lookup-kd : ∀ {m} {Γ : Ctx m} {k} x →
              Γ ctx → ElimCtx.lookup Γ x ≡ kd k → Γ ⊢ k kd
  lookup-kd x Γ-ctx Γ[x]≡kd-k =
    wf-kd-inv (subst (_ ⊢_wf) Γ[x]≡kd-k (lookup-wf Γ-ctx x))

open WfCtxOps

-- A corollary (validity of variable kinding): the kinds of variables
-- are well-formed.

Var∈-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Var a ∈ k → Γ ⊢ k kd
Var∈-valid (⇉-var x Γ-ctx Γ[x]≡kd-k) = lookup-kd x Γ-ctx Γ[x]≡kd-k
Var∈-valid (⇇-⇑ x∈j j<∷k k-kd)       = k-kd


----------------------------------------------------------------------
-- Context narrowing
--
-- The various judgments are preserved by narrowing of kind
-- ascriptions in their contexts.

module ContextNarrowing where
  open Substitution
    using (termLikeLemmasElim; termLikeLemmasKind′; termLikeLemmasElimAsc)
  open TermLikeLemmas termLikeLemmasElimAsc using (varLiftAppLemmas)
  open LiftAppLemmas varLiftAppLemmas
  open KindedRenaming using (kd-weaken; <∷-weaken; Var′∈-weaken)
  private
    module EL = LiftAppLemmas
                (TermLikeLemmas.varLiftAppLemmas termLikeLemmasElim)
    module KL = LiftAppLemmas
                (TermLikeLemmas.varLiftAppLemmas termLikeLemmasKind′)

  -- NOTE. Rather than proving context narrowing directly by induction
  -- on typing derivations, we instead define a more flexible variant
  -- of well-typed variable substitutions based on the canonical
  -- variable kinding judgment (_⊢Var_∈_).  This judgment features a
  -- subsumption rule (∈-⇑), which is not available in the generic
  -- variable judgment from Data.Fin.Substitutions.Typed that we used
  -- to define basic typed renamings.  With support for subsumption in
  -- typed renamings, we get context narrowing "for free", as it is
  -- just another variable substitution (one that happens to change
  -- the kind rather than the name of a variable).  This way of
  -- proving context narrowing is more convenient since we can reuse
  -- the generic lemmas proven for typed variable substitution and
  -- avoid some explicit fiddling with context.
  --
  -- Note also that we could not have defined typed renamings
  -- directly using the _⊢Var_∈_ judgment since that would have
  -- required a weakening lemma for subkiding, which in turn is
  -- implemented via typed renamings.

  -- The trivial lifting from _⊢Var′_∈_ to itself, and simple typed
  -- variable substitutions.

  liftTyped : LiftTo-Var′∈ _⊢Var′_∈_
  liftTyped = record
    { typedSimple      = record
      { typedWeakenOps = record
        { ∈-weaken     = Var′∈-weaken
        ; ∈-wf         = Var′∈-ctx
        ; /-wk         = refl
        ; /-weaken     = /-weaken
        ; weaken-/-∷   = weaken-/-∷
        }
      ; ∈-var          = ∈-var′
      ; wf-wf          = wf-ctx
      ; id-vanishes    = id-vanishes
      }
    ; ∈-lift           = λ x∈a → x∈a
    }
    where
      weakenLemmas : WeakenLemmas ElimAsc Fin
      weakenLemmas = record { appLemmas = appLemmas ; /-wk = refl }
      open WeakenLemmas weakenLemmas

  open LiftTo-Var′∈ liftTyped
  open TypedVarSubstApp _⊢Var′_∈_ liftTyped

  -- A typed renaming that narrows the kind of the first type
  -- variable.

  ∈-<∷-sub : ∀ {n} {Γ : Ctx n} {j k} →
             Γ ⊢ j kd → Γ ⊢ j <∷ k → (kd k ∷ Γ) ctx →
             kd j ∷ Γ ⊢/Var id ∈ kd k ∷ Γ
  ∈-<∷-sub j-kd j<∷k k∷Γ-ctx =
    ∈-tsub (∈-tp (⇇-⇑ x∈k (<∷-weaken j-wf j<∷k) k-kd))
    where
      j-wf  = wf-kd j-kd
      Γ-ctx = kd-ctx j-kd
      x∈k   = ⇉-var zero (j-wf ∷ Γ-ctx) refl
      k-kd  = kd-weaken j-wf (wf-kd-inv (wf-∷₁ k∷Γ-ctx))

  -- Narrowing the kind of the first type variable preserves
  -- well-formedness of kinds.

  ⇓-kd : ∀ {n} {Γ : Ctx n} {j₁ j₂ k} →
         Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ k kd → kd j₁ ∷ Γ ⊢ k kd
  ⇓-kd j₁-kd j₁<∷j₂ k-kd =
    subst (_ ⊢_kd) (KL.id-vanishes _)
          (kd-/Var k-kd (∈-<∷-sub j₁-kd j₁<∷j₂ (kd-ctx k-kd)))

  -- Narrowing the kind of the first type variable preserves
  -- well-kindedness.

  ⇓-Nf⇉ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a k} →
          Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢Nf a ⇉ k → kd j₁ ∷ Γ ⊢Nf a ⇉ k
  ⇓-Nf⇉ j₁-kd j₁<∷j₂ a⇉k =
    subst₂ (_ ⊢Nf_⇉_) (EL.id-vanishes _) (KL.id-vanishes _)
           (Nf⇉-/Var a⇉k (∈-<∷-sub j₁-kd j₁<∷j₂ (Nf⇉-ctx a⇉k)))

  -- Narrowing the kind of the first type variable preserves
  -- subkinding and subtyping.

  ⇓-<∷ : ∀ {n} {Γ : Ctx n} {j₁ j₂ k₁ k₂} →
         Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ k₁ <∷ k₂ → kd j₁ ∷ Γ ⊢ k₁ <∷ k₂
  ⇓-<∷ j₁-kd j₁<∷j₂ k₁<∷k₂ =
    subst₂ (_ ⊢_<∷_) (KL.id-vanishes _) (KL.id-vanishes _)
           (<∷-/Var k₁<∷k₂ (∈-<∷-sub j₁-kd j₁<∷j₂ (<∷-ctx k₁<∷k₂)))

  ⇓-<: : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂} →
         Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ a₁ <: a₂ → kd j₁ ∷ Γ ⊢ a₁ <: a₂
  ⇓-<: j₁-kd j₁<∷j₂ a₁<:a₂ =
    subst₂ (_ ⊢_<:_) (EL.id-vanishes _) (EL.id-vanishes _)
           (<:-/Var a₁<:a₂ (∈-<∷-sub j₁-kd j₁<∷j₂ (<:-ctx a₁<:a₂)))

  ⇓-<:⇇ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂ k} →
          Γ ⊢ j₁ kd → Γ ⊢ j₁ <∷ j₂ → kd j₂ ∷ Γ ⊢ a₁ <: a₂ ⇇ k →
          kd j₁ ∷ Γ ⊢ a₁ <: a₂ ⇇ k
  ⇓-<:⇇ j₁-kd j₁<∷j₂ a₁<:a₂∈k =
    subst (_ ⊢ _ <: _ ⇇_) (KL.id-vanishes _)
          (subst₂ (_ ⊢_<:_⇇ _) (EL.id-vanishes _) (EL.id-vanishes _)
                  (<:⇇-/Var a₁<:a₂∈k
                            (∈-<∷-sub j₁-kd j₁<∷j₂ (<:⇇-ctx a₁<:a₂∈k))))

open KindedRenaming
open ContextNarrowing
open Substitution hiding (subst)
private module TV = TypedVarSubst typedVarSubst

-- Some corollaries of context narrowing: transitivity of subkinding
-- and kind equality are admissible.

<∷-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j <∷ k → Γ ⊢ k <∷ l → Γ ⊢ j <∷ l
<∷-trans (<∷-⋯ a₂<:a₁ b₁<:b₂) (<∷-⋯ a₃<:a₂ b₂<:b₃) =
  <∷-⋯ (<:-trans a₃<:a₂ a₂<:a₁) (<:-trans b₁<:b₂ b₂<:b₃)
<∷-trans (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) (<∷-Π j₃<∷j₂ k₂<∷k₃ _) =
  let j₃-kd = wf-kd-inv (wf-∷₁ (<∷-ctx k₂<∷k₃))
  in <∷-Π (<∷-trans j₃<∷j₂ j₂<∷j₁)
          (<∷-trans (⇓-<∷ j₃-kd j₃<∷j₂ k₁<∷k₂) k₂<∷k₃) Πj₁k₁-kd

≅-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j ≅ k → Γ ⊢ k ≅ l → Γ ⊢ j ≅ l
≅-trans (<∷-antisym j-kd _ j<∷k k<∷j) (<∷-antisym _ l-kd k<∷l l<∷k) =
  <∷-antisym j-kd l-kd (<∷-trans j<∷k k<∷l) (<∷-trans l<∷k k<∷j)

-- Some more corollaries: subsumption is admissible in canonical kind
-- checking, checked subtyping and kind equality.
--
-- NOTE. The proof of (<:⇇-⇑) is by induction on subkinding
-- derivations (the second hypothesis) rather than kinding derivations
-- (the first hypothesis).

Nf⇇-⇑ : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢Nf a ⇇ j → Γ ⊢ j <∷ k → Γ ⊢Nf a ⇇ k
Nf⇇-⇑ (⇇-⇑ a⇇j₁ j₁<∷j₂) j₂<∷j₃ = ⇇-⇑ a⇇j₁ (<∷-trans j₁<∷j₂ j₂<∷j₃)

<:⇇-⇑ : ∀ {n} {Γ : Ctx n} {a b j k} →
        Γ ⊢ a <: b ⇇ j → Γ ⊢ j <∷ k → Γ ⊢ k kd → Γ ⊢ a <: b ⇇ k
<:⇇-⇑ (<:-⇇ a⇇c₁⋯d₁ b⇇c₁⋯d₁ a<:b) (<∷-⋯ c₂<:c₁ d₁<:d₂) _ =
  <:-⇇ (Nf⇇-⇑ a⇇c₁⋯d₁ (<∷-⋯ c₂<:c₁ d₁<:d₂))
       (Nf⇇-⇑ b⇇c₁⋯d₁ (<∷-⋯ c₂<:c₁ d₁<:d₂)) a<:b
<:⇇-⇑ (<:-λ a₁<:a₂ Λj₁a₁⇇Πk₁l₁ Λj₂a₂⇇Πk₁l₁) (<∷-Π k₂<∷k₁ l₁<∷l₂ Πk₁l₁-kd)
      (kd-Π k₂-kd l₂-kd) =
  <:-λ (<:⇇-⇑ (⇓-<:⇇ k₂-kd k₂<∷k₁ a₁<:a₂) l₁<∷l₂ l₂-kd)
       (Nf⇇-⇑ Λj₁a₁⇇Πk₁l₁ (<∷-Π k₂<∷k₁ l₁<∷l₂ Πk₁l₁-kd))
       (Nf⇇-⇑ Λj₂a₂⇇Πk₁l₁ (<∷-Π k₂<∷k₁ l₁<∷l₂ Πk₁l₁-kd))

≃-⇑ : ∀ {n} {Γ : Ctx n} {a b j k} →
      Γ ⊢ a ≃ b ⇇ j → Γ ⊢ j <∷ k → Γ ⊢ k kd → Γ ⊢ a ≃ b ⇇ k
≃-⇑ (<:-antisym j-kd a<:b b<:a) j<∷k k-kd =
  <:-antisym k-kd (<:⇇-⇑ a<:b j<∷k k-kd) (<:⇇-⇑ b<:a j<∷k k-kd)


------------------------------------------------------------------------
-- Reflexivity of the various relations.
--
-- NOTE. The proof is by mutual induction in the structure of the
-- types and kinds being related to themselves, and then by
-- case-analysis on formation/kinding derivations (rather than
-- induction on the typing/kinding derivations directly).  For
-- example, the proof of (<:⇇-reflNf⇉-⇑) is not decreasing in the
-- kinding derivation of `a' in the type abstraction (Π-intro) case.
-- To avoid clutter, we do not make the corresponding type/kind
-- parameters explicit in the implementations below: thanks to the
-- structure of canonical formation/kinding, every kind/type
-- constructor corresponds to exactly one kinding/typing rule
-- (i.e. the rules are syntax directed).

mutual

  -- Reflexivity of canonical subkinding.
  <∷-refl : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ k <∷ k
  <∷-refl (kd-⋯ a⇉a⋯a b⇉b⋯b) = <∷-⋯ (<:-reflNf⇉ a⇉a⋯a) (<:-reflNf⇉ b⇉b⋯b)
  <∷-refl (kd-Π j-kd k-kd)   =
    <∷-Π (<∷-refl j-kd) (<∷-refl k-kd) (kd-Π j-kd k-kd)

  -- Reflexivity of canonical subtyping.

  <:-reflNf⇉ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢ a <: a
  <:-reflNf⇉ (⇉-⊥-f Γ-ctx)       = <:-⊥ (⇉-⊥-f Γ-ctx)
  <:-reflNf⇉ (⇉-⊤-f Γ-ctx)       = <:-⊤ (⇉-⊤-f Γ-ctx)
  <:-reflNf⇉ (⇉-∀-f k-kd a⇉a⋯a)  =
    <:-∀ (<∷-refl k-kd) (<:-reflNf⇉ a⇉a⋯a) (⇉-∀-f k-kd a⇉a⋯a)
  <:-reflNf⇉ (⇉-→-f a⇉a⋯a b⇉b⋯b) =
    <:-→ (<:-reflNf⇉ a⇉a⋯a) (<:-reflNf⇉ b⇉b⋯b)
  <:-reflNf⇉ (⇉-s-i (∈-∙ x∈j j⇉as⇉k)) = <:-∙ x∈j (≃-reflSp⇉ j⇉as⇉k)

  <:⇇-reflNf⇉-⇑ : ∀ {n} {Γ : Ctx n} {a j k} →
                  Γ ⊢Nf a ⇉ j → Γ ⊢ j <∷ k → Γ ⊢ k kd → Γ ⊢ a <: a ⇇ k
  <:⇇-reflNf⇉-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂) _ =
    let a⇇b₂⋯c₂ = ⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)
    in <:-⇇ a⇇b₂⋯c₂ a⇇b₂⋯c₂ (<:-reflNf⇉ a⇉b₁⋯c₁)
  <:⇇-reflNf⇉-⇑ (⇉-Π-i j₁-kd a⇉k₁) (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd)
                (kd-Π j₂-kd k₂-kd) =
    let a<:a⇇k₂ = <:⇇-reflNf⇉-⇑ (⇓-Nf⇉ j₂-kd j₂<∷j₁ a⇉k₁) k₁<∷k₂ k₂-kd
        Λj₁a⇇Πj₂k₂ = ⇇-⇑ (⇉-Π-i j₁-kd a⇉k₁) (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd)
    in <:-λ a<:a⇇k₂ Λj₁a⇇Πj₂k₂ Λj₁a⇇Πj₂k₂

  <:⇇-reflNf⇇ : ∀ {n} {Γ : Ctx n} {a k} →
                Γ ⊢Nf a ⇇ k → Γ ⊢ k kd → Γ ⊢ a <: a ⇇ k
  <:⇇-reflNf⇇ (⇇-⇑ a⇉k j<∷k) k-kd = <:⇇-reflNf⇉-⇑ a⇉k j<∷k k-kd

  -- Reflexivity of canonical spine equality.
  ≃-reflSp⇉ : ∀ {n} {Γ : Ctx n} {as j k} →
              Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢ j ⇉∙ as ≃ as ⇉ k
  ≃-reflSp⇉ ⇉-[]                     = ≃-[]
  ≃-reflSp⇉ (⇉-∷ a⇇j j-kd k[a]⇉as⇉l) =
    ≃-∷ (≃-reflNf⇇ a⇇j j-kd) (≃-reflSp⇉ k[a]⇉as⇉l)

  -- A checked variant of reflexivity.
  ≃-reflNf⇇ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇇ k → Γ ⊢ k kd → Γ ⊢ a ≃ a ⇇ k
  ≃-reflNf⇇ a⇇k k-kd =
    <:-antisym k-kd (<:⇇-reflNf⇇ a⇇k k-kd) (<:⇇-reflNf⇇ a⇇k k-kd)

-- Reflexivity of canonical kind equality.
≅-refl : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ k ≅ k
≅-refl k-kd = <∷-antisym k-kd k-kd (<∷-refl k-kd) (<∷-refl k-kd)

-- A shorthand.
<:⇇-reflNf⇉ : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢Nf a ⇉ k → Γ ⊢ k kd → Γ ⊢ a <: a ⇇ k
<:⇇-reflNf⇉ a⇉k k-kd = <:⇇-reflNf⇉-⇑ a⇉k (<∷-refl k-kd) k-kd

-- Some corollaryies of reflexivity.

-- The synthesized kinds of normal forms kind-check.
Nf⇉⇒Nf⇇ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → Γ ⊢Nf a ⇇ k
Nf⇉⇒Nf⇇ a⇉k = ⇇-⇑ a⇉k (<∷-refl (Nf⇉-valid a⇉k))

-- An admissible operator introduction rule accepting a checked body.
Nf⇇-Π-i : ∀ {n} {Γ : Ctx n} {j a k} →
          Γ ⊢ j kd → kd j ∷ Γ ⊢Nf a ⇇ k → Γ ⊢Nf Λ∙ j a ⇇ Π j k
Nf⇇-Π-i j-kd (⇇-⇑ a⇉l l<∷k) =
  ⇇-⇑ (⇉-Π-i j-kd a⇉l) (<∷-Π (<∷-refl j-kd) l<∷k (kd-Π j-kd (Nf⇉-valid a⇉l)))

-- Admissible projection rules for canonically kinded proper types.

<:-⟨|-Nf⇉ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢ b <: a
<:-⟨|-Nf⇉ a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
<:-⟨|-Nf⇉ a⇉a⋯a | refl , refl = <:-reflNf⇉ a⇉a⋯a

<:-⟨|-Nf⇇ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢ b <: a
<:-⟨|-Nf⇇ (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)) =
  <:-trans b₂<:b₁ (<:-⟨|-Nf⇉ a⇉b₁⋯c₁)

<:-|⟩-Nf⇉ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇉ b ⋯ c → Γ ⊢ a <: c
<:-|⟩-Nf⇉ a⇉b⋯c with Nf⇉-≡ a⇉b⋯c
<:-|⟩-Nf⇉ a⇉a⋯a | refl , refl = <:-reflNf⇉ a⇉a⋯a

<:-|⟩-Nf⇇ : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢Nf a ⇇ b ⋯ c → Γ ⊢ a <: c
<:-|⟩-Nf⇇ (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)) =
  <:-trans (<:-|⟩-Nf⇉ a⇉b₁⋯c₁) c₁<:c₂

-- An admissible interval rule for checked subtyping.
<:⇇-⋯-i : ∀ {n} {Γ : Ctx n} {a b c d} →
          Γ ⊢ a <: b ⇇ c ⋯ d → Γ ⊢ a <: b ⇇ a ⋯ b
<:⇇-⋯-i (<:-⇇ a⇇c⋯d b⇇c⋯d a<:b) =
  let a⇉a⋯a = Nf⇇-s-i a⇇c⋯d
      b⇉b⋯b = Nf⇇-s-i b⇇c⋯d
  in <:-⇇ (⇇-⇑ a⇉a⋯a (<∷-⋯ (<:-reflNf⇉ a⇉a⋯a) a<:b))
          (⇇-⇑ b⇉b⋯b (<∷-⋯ a<:b (<:-reflNf⇉ b⇉b⋯b))) a<:b

-- An inversion lemma about variable kinding.
Var∈-inv : ∀ {n} {Γ : Ctx n} {x k} → Γ ⊢Var x ∈ k →
           ∃ λ j → lookup Γ x ≡ kd j × Γ ⊢ j <∷ k × Γ ⊢ j kd × Γ ⊢ k kd
Var∈-inv (⇉-var x Γ-ctx Γ[x]≡kd-j) =
  let j-kd = lookup-kd x Γ-ctx Γ[x]≡kd-j
  in _ , Γ[x]≡kd-j , <∷-refl j-kd , j-kd , j-kd
Var∈-inv (⇇-⇑ x∈j j<∷k k-kd) =
  let l , Γ[x]≡kd-l , l<∷j , l-kd , _ = Var∈-inv x∈j
  in l , Γ[x]≡kd-l , <∷-trans l<∷j j<∷k , l-kd , k-kd

-- A "canonical forms" lemma for operator equality.
≃-Π-can : ∀ {n} {Γ : Ctx n} {a₁ a₂ j k} → Γ ⊢ a₁ ≃ a₂ ⇇ Π j k →
          ∃ λ j₁ → ∃ λ b₁ → ∃ λ j₂ → ∃ λ b₂ →
            Γ ⊢Nf Λ∙ j₁ b₁ ⇇ Π j k × Γ ⊢Nf Λ∙ j₂ b₂ ⇇ Π j k × Γ ⊢ Π j k kd ×
              Γ ⊢ j <∷ j₁ × Γ ⊢ j <∷ j₂ ×
              kd j ∷ Γ ⊢ b₁ <: b₂ ⇇ k × kd j ∷ Γ ⊢ b₂ <: b₁ ⇇ k ×
              a₁ ≡ Λ∙ j₁ b₁ × a₂ ≡ Λ∙ j₂ b₂
≃-Π-can (<:-antisym Πjk-kd
          (<:-λ a₁<:a₂
            (⇇-⇑ (⇉-Π-i j₁-kd a₁⇉k₁) (<∷-Π j<∷j₁ k₁<∷k Πj₁k₁-kd))
            (⇇-⇑ (⇉-Π-i j₂-kd a₂⇉k₂) (<∷-Π j<∷j₂ k₂<∷k Πj₂k₂-kd)))
          (<:-λ a₂<:a₁ _ _)) =
  _ , _ , _ , _ ,
  (⇇-⇑ (⇉-Π-i j₁-kd a₁⇉k₁) (<∷-Π j<∷j₁ k₁<∷k Πj₁k₁-kd)) ,
  (⇇-⇑ (⇉-Π-i j₂-kd a₂⇉k₂) (<∷-Π j<∷j₂ k₂<∷k Πj₂k₂-kd)) ,
  Πjk-kd , j<∷j₁ , j<∷j₂ , a₁<:a₂ , a₂<:a₁ , refl , refl


------------------------------------------------------------------------
-- Simplification of well-formed kinding.

module _ where
  open SimpleKinding
  open SimpleKinding.Kinding
    renaming (_⊢Var_∈_ to _⊢sVar_∈_; _⊢Ne_∈_ to _⊢sNe_∈_)
  open KindedHereditarySubstitution
  open ≡-Reasoning

  -- Simplification of well-formedness and kinding: well-formed kinds
  -- resp. well-kinded normal forms, neutrals and spines are also
  -- simply well-formed resp. well-kinded.

  Var∈-sVar∈ : ∀ {n} {Γ : Ctx n} {a k} →
               Γ ⊢Var a ∈ k → ⌊ Γ ⌋Ctx ⊢sVar a ∈ ⌊ k ⌋
  Var∈-sVar∈ {_} {Γ} {_} {k} (⇉-var x Γ-ctx Γ[x]≡kd-k) = ∈-var x (begin
    SimpleCtx.lookup ⌊ Γ ⌋Ctx x   ≡⟨ ⌊⌋Asc-lookup Γ x ⟩
    ⌊ ElimCtx.lookup Γ x ⌋Asc     ≡⟨ cong ⌊_⌋Asc Γ[x]≡kd-k ⟩
    kd ⌊ k ⌋                      ∎)
    where open ContextConversions
  Var∈-sVar∈ (⇇-⇑ x∈j j<∷k k-kd) =
    subst (_ ⊢sVar _ ∈_) (<∷-⌊⌋ j<∷k) (Var∈-sVar∈ x∈j)

  mutual

    kd-kds : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → ⌊ Γ ⌋Ctx ⊢ k kds
    kd-kds (kd-⋯ a∈a⋯a b∈b⋯b) = kds-⋯ (Nf⇉-Nf∈ a∈a⋯a) (Nf⇉-Nf∈ b∈b⋯b)
    kd-kds (kd-Π j-kd k-kd)   = kds-Π (kd-kds j-kd) (kd-kds k-kd)

    Nf⇉-Nf∈ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇉ k → ⌊ Γ ⌋Ctx ⊢Nf a ∈ ⌊ k ⌋
    Nf⇉-Nf∈ (⇉-⊥-f Γ-ctx)       = ∈-⊥-f
    Nf⇉-Nf∈ (⇉-⊤-f Γ-ctx)       = ∈-⊤-f
    Nf⇉-Nf∈ (⇉-∀-f k-kd a⇉a⋯a)  = ∈-∀-f (kd-kds k-kd) (Nf⇉-Nf∈ a⇉a⋯a)
    Nf⇉-Nf∈ (⇉-→-f a∈a⋯a b∈b⋯b) = ∈-→-f (Nf⇉-Nf∈ a∈a⋯a) (Nf⇉-Nf∈ b∈b⋯b)
    Nf⇉-Nf∈ (⇉-Π-i j-kd a⇉k)    = ∈-Π-i (kd-kds j-kd) (Nf⇉-Nf∈ a⇉k)
    Nf⇉-Nf∈ (⇉-s-i a∈b⋯c)       = ∈-ne (Ne∈-sNe∈ a∈b⋯c)

    Ne∈-sNe∈ : ∀ {n} {Γ : Ctx n} {a k} →
               Γ ⊢Ne a ∈ k → ⌊ Γ ⌋Ctx ⊢sNe a ∈ ⌊ k ⌋
    Ne∈-sNe∈ (∈-∙ x∈j j⇉as⇉k) = ∈-∙ (Var∈-sVar∈ x∈j) (Sp⇉-Sp∈ j⇉as⇉k)

    Sp⇉-Sp∈ : ∀ {n} {Γ : Ctx n} {as j k} → Γ ⊢ j ⇉∙ as ⇉ k →
              ⌊ Γ ⌋Ctx ⊢ ⌊ j ⌋ ∋∙ as ∈ ⌊ k ⌋
    Sp⇉-Sp∈ ⇉-[] = ∈-[]
    Sp⇉-Sp∈ (⇉-∷ a⇇j j-kd k[a]⇉as⇉l) =
      ∈-∷ (Nf⇇-Nf∈ a⇇j)
          (subst (_ ⊢_∋∙ _ ∈ _) (⌊⌋-Kind/⟨⟩ _) (Sp⇉-Sp∈ k[a]⇉as⇉l))

    Nf⇇-Nf∈ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇇ k → ⌊ Γ ⌋Ctx ⊢Nf a ∈ ⌊ k ⌋
    Nf⇇-Nf∈ (⇇-⇑ a⇉j j<∷k) = subst (_ ⊢Nf _ ∈_) (<∷-⌊⌋ j<∷k) (Nf⇉-Nf∈ a⇉j)
