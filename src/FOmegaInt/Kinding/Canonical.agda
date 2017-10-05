------------------------------------------------------------------------
-- Canonical kinding of Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Canonical where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Context.Properties
open import Data.Fin.Substitution.Typed
open import Data.List using ([]; _∷_; _∷ʳ_; map)
open import Data.List.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃; _,_; _×_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.All as VecAll using (All₂; []; _∷_)
open import Data.Vec.All.Properties using (gmap₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
import FOmegaInt.Kinding.Simple as SimpleKinding


------------------------------------------------------------------------
-- Canonical kinding derivations.
--
-- TODO: explain the point of this and how "canonical" kinding differs
-- from "algorithmic" kinding.
--
-- NOTE. In the rules below, we use (singleton) kind synthesis
-- judgments of the form `Γ ⊢Nf a ⇉ a ⋯ a' to ensure that `a' is a
-- well-kinded proper type rather than kind checking judgments of the
-- form `Γ ⊢Nf a ⇇ *'.  While the latter may seem more natural, it
-- involves the use of subsumption/subtyping to ensure that `Γ ⊢ a ⋯ a
-- <∷ *'.  As we will show, this is always true (if `a' is indeed a
-- proper type) but the extra use of subsumption complicates the
-- proofs of properties that require (partial) inversion of kinding
-- derivations.

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
    Γ ctx = WellFormedContext._wf _⊢_wf Γ

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
      ∈-∙ : ∀ {x j k} {as : Spine n} → Γ ⊢Var var x ∈ j →
            Γ ⊢ j ⇉∙ as ⇉ k → Γ ⊢Ne var x ∙ as ∈ k

    -- Canonical kinding of variables.
    --
    -- NOTE.  This would be a kind synthesis judgment if it weren't
    -- for the subsumption rule (⇇-⇑).  Thanks to this rule, the proof
    -- of the "context narrowing" property is easy to establish for
    -- canonical typing (see the ContextNarrowing module below).
    -- Without a proof of this property, the various lemmas about
    -- parallel hereditary substitution become difficult to establish
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
    data _⊢Var_∈_ {n} (Γ : Ctx n) : Head n → Kind Elim n → Set where
      ⇉-var : ∀ {k} x → Γ ctx → lookup x Γ ≡ kd k → Γ ⊢Var var x ∈ k
      ⇇-⇑   : ∀ {x j k} → Γ ⊢Var var x ∈ j → Γ ⊢ j <∷ k → Γ ⊢ k kd →
              Γ ⊢Var var x ∈ k

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
                 Γ ⊢Var var x ∈ k → Γ ⊢ k ⇉∙ as₁ ≃ as₂ ⇉ b ⋯ c →
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
  open WellFormedContext (_⊢_wf) public hiding (_wf)
    renaming (_⊢_wfExt to _⊢_ext; _⊢_wfExt′ to _⊢_ext′)


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

-- Subkinds simplify equally.
<∷-⌊⌋ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → ⌊ j ⌋ ≡ ⌊ k ⌋
<∷-⌊⌋ (<∷-⋯ _ _)             = refl
<∷-⌊⌋ (<∷-Π j₂<∷j₁ k₁<∷k₂ _) = cong₂ _⇒_ (sym (<∷-⌊⌋ j₂<∷j₁)) (<∷-⌊⌋ k₁<∷k₂)

-- Equal kinds simplify equally.
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
-- Well-kinded variable substitutions (i.e. renamings) in canonically
-- kinded types
--
-- Or in other words, lemmas showing that renaming preserves kinding.

module KindedRenaming where
  open Substitution        using (termSubst; termLikeLemmasElimAsc)
  open TermSubst termSubst using (varLift)

  typedVarSubst : TypedVarSubst (_⊢_wf)
  typedVarSubst = record
    { application = AppLemmas.application appLemmas
    ; weakenOps   = ElimCtx.weakenOps
    ; /-wk        = refl
    ; id-vanishes = id-vanishes
    ; /-⊙         = /-⊙
    ; wf-wf       = wf-ctx
    }
    where
      open TermLikeLemmas termLikeLemmasElimAsc using (varLiftAppLemmas)
      open LiftAppLemmas  varLiftAppLemmas

  open TypedVarSubst typedVarSubst hiding (∈-weaken)
    renaming (_⊢Var_∈_ to _⊢Var′_∈_)
  open TypedSub typedSub using (_,_) renaming (lookup to ∈-lookup)

  open Substitution hiding (subst; _/Var_) renaming (_Elim/Var_ to _/Var_)
  open RenamingCommutes using (Kind[∈⌊⌋]-/)
  open ≡-Reasoning

  -- A helper.
  ∈-↑′ : ∀ {m n} {Δ : Ctx n} {Γ : Ctx m} {k σ} →
         Δ ⊢ k Kind′/Var σ kd → Δ ⊢/Var σ ∈ Γ →
         kd (k Kind′/Var σ) ∷ Δ ⊢/Var σ VarSubst.↑ ∈ kd k ∷ Γ
  ∈-↑′ k/σ-kd σ∈Γ = ∈-↑ (wf-kd k/σ-kd) σ∈Γ

  -- Convert between well-kindedness judgments for variables.
  Var∈-Var∈ : ∀ {n} {Γ : Ctx n} {x a k} → a ≡ kd k →
              Γ ⊢Var′ x ∈ a → Γ ⊢Var var x ∈ k
  Var∈-Var∈ Γ[x]≡kd-k (var x Γ-ctx) = ⇉-var x Γ-ctx Γ[x]≡kd-k

  mutual

    -- Renamings preserve well-formedness of ascriptions.
    wf-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a σ} →
              Γ ⊢ a wf → Δ ⊢/Var σ ∈ Γ → Δ ⊢ a ElimAsc/Var σ wf
    wf-/Var (wf-kd k-kd)  σ∈Γ = wf-kd (kd-/Var k-kd σ∈Γ)
    wf-/Var (wf-tp a⇉a⋯a) σ∈Γ = wf-tp (Nf⇉-/Var a⇉a⋯a σ∈Γ)

    -- Renamings preserve well-formedness of kinds.
    kd-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k σ} →
              Γ ⊢ k kd → Δ ⊢/Var σ ∈ Γ → Δ ⊢ k Kind′/Var σ kd
    kd-/Var (kd-⋯ a⇉a⋯a b⇉b⋯b) σ∈Γ =
      kd-⋯ (Nf⇉-/Var a⇉a⋯a σ∈Γ) (Nf⇉-/Var b⇉b⋯b σ∈Γ)
    kd-/Var (kd-Π j-kd  k-kd) σ∈Γ =
      let j/σ-kd = kd-/Var j-kd σ∈Γ
      in kd-Π j/σ-kd (kd-/Var k-kd (∈-↑′ j/σ-kd σ∈Γ))

    -- Renamings preserve synthesized kinds of normal types.
    Nf⇉-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Nf a ⇉ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢Nf a /Var σ ⇉ k Kind′/Var σ
    Nf⇉-/Var (⇉-⊥-f Γ-ctx)       (_ , Δ-ctx) = ⇉-⊥-f Δ-ctx
    Nf⇉-/Var (⇉-⊤-f Γ-ctx)       (_ , Δ-ctx) = ⇉-⊤-f Δ-ctx
    Nf⇉-/Var (⇉-∀-f k-kd a⇉a⋯a)  σ∈Γ =
      let k/σ-kd = kd-/Var k-kd σ∈Γ
      in ⇉-∀-f k/σ-kd (Nf⇉-/Var a⇉a⋯a (∈-↑′ k/σ-kd σ∈Γ))
    Nf⇉-/Var (⇉-→-f a⇉a⋯a b⇉b⋯b) σ∈Γ =
      ⇉-→-f (Nf⇉-/Var a⇉a⋯a σ∈Γ) (Nf⇉-/Var b⇉b⋯b σ∈Γ)
    Nf⇉-/Var (⇉-Π-i j-kd a⇉k)    σ∈Γ =
      let j/σ-kd = kd-/Var j-kd σ∈Γ
      in ⇉-Π-i j/σ-kd (Nf⇉-/Var a⇉k (∈-↑′ j/σ-kd σ∈Γ))
    Nf⇉-/Var (⇉-s-i a∈b⋯c)       σ∈Γ = ⇉-s-i (Ne∈-/Var a∈b⋯c σ∈Γ)

    -- Renamings preserve the kinds of variables.
    Var∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
                Γ ⊢Var a ∈ k → Δ ⊢/Var σ ∈ Γ →
                Δ ⊢Var a Head/Var σ ∈ k Kind′/Var σ
    Var∈-/Var {σ = σ} (⇉-var x Γ-ctx Γ[x]≡kd-k) σ∈Γ =
      Var∈-Var∈ (cong (_ElimAsc/Var σ) Γ[x]≡kd-k) (∈-lookup x σ∈Γ)
    Var∈-/Var (⇇-⇑ x∈j j<∷k k-kd) σ∈Γ =
      ⇇-⇑ (Var∈-/Var x∈j σ∈Γ) (<∷-/Var j<∷k σ∈Γ) (kd-/Var k-kd σ∈Γ)

    -- Renamings preserve synthesized kinds of neutral types.
    Ne∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Ne a ∈ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢Ne a /Var σ ∈ k Kind′/Var σ
    Ne∈-/Var (∈-∙ x∈j k⇉as⇉l) σ∈Γ =
      ∈-∙ (Var∈-/Var x∈j σ∈Γ) (Sp⇉-/Var k⇉as⇉l σ∈Γ)

    -- Renamings preserve spine kindings.
    Sp⇉-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as j k σ} →
               Γ ⊢ j ⇉∙ as ⇉ k → Δ ⊢/Var σ ∈ Γ →
               Δ ⊢ j Kind′/Var σ ⇉∙ as //Var σ ⇉ k Kind′/Var σ
    Sp⇉-/Var ⇉-[]                                σ∈Γ = ⇉-[]
    Sp⇉-/Var (⇉-∷ {a} {_} {j} {k} a⇇j j-kd k[a]⇉as⇉l) σ∈Γ =
      ⇉-∷ (Nf⇇-/Var a⇇j σ∈Γ) (kd-/Var j-kd σ∈Γ)
          (subst (_ ⊢_⇉∙ _ ⇉ _) (Kind[∈⌊⌋]-/ k a j) (Sp⇉-/Var k[a]⇉as⇉l σ∈Γ))

    -- Renamings preserve checked kinds of neutral types.
    Nf⇇-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Nf a ⇇ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢Nf a /Var σ ⇇ k Kind′/Var σ
    Nf⇇-/Var (⇇-⇑ a⇉j j<∷k) σ∈Γ = ⇇-⇑ (Nf⇉-/Var a⇉j σ∈Γ) (<∷-/Var j<∷k σ∈Γ)

    -- Renamings preserve subkinding.
    <∷-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
              Γ ⊢ j <∷ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢ j Kind′/Var σ <∷ k Kind′/Var σ
    <∷-/Var (<∷-⋯ a₂<:a₁ b₁<:b₂) σ∈Γ =
      <∷-⋯ (<:-/Var a₂<:a₁ σ∈Γ) (<:-/Var b₁<:b₂ σ∈Γ)
    <∷-/Var (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) σ∈Γ =
      <∷-Π (<∷-/Var j₂<∷j₁ σ∈Γ)
           (<∷-/Var k₁<∷k₂ (∈-↑ (<∷-/Var-wf k₁<∷k₂ σ∈Γ) σ∈Γ))
           (kd-/Var Πj₁k₁-kd σ∈Γ)

    -- Renamings preserve subtyping.

    <:-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b σ} →
              Γ ⊢ a <: b → Δ ⊢/Var σ ∈ Γ → Δ ⊢ a /Var σ <: b /Var σ
    <:-/Var (<:-trans a<:b b<:c) σ∈Γ =
      <:-trans (<:-/Var a<:b σ∈Γ) (<:-/Var b<:c σ∈Γ)
    <:-/Var (<:-⊥ a⇉a⋯a) σ∈Γ = <:-⊥ (Nf⇉-/Var a⇉a⋯a σ∈Γ)
    <:-/Var (<:-⊤ a⇉a⋯a) σ∈Γ = <:-⊤ (Nf⇉-/Var a⇉a⋯a σ∈Γ)
    <:-/Var (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) σ∈Γ =
      <:-∀ (<∷-/Var k₂<∷k₁ σ∈Γ)
           (<:-/Var a₁<:a₂ (∈-↑ (<:-/Var-wf a₁<:a₂ σ∈Γ) σ∈Γ))
           (Nf⇉-/Var Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁ σ∈Γ)
    <:-/Var (<:-→ a₂<:a₁ b₁<:b₂) σ∈Γ =
      <:-→ (<:-/Var a₂<:a₁ σ∈Γ) (<:-/Var b₁<:b₂ σ∈Γ)
    <:-/Var (<:-∙ x∈j j⇉as₁<:as₂⇉k) σ∈Γ =
      <:-∙ (Var∈-/Var x∈j σ∈Γ) (Sp≃-/Var j⇉as₁<:as₂⇉k σ∈Γ)
    <:-/Var (<:-⟨| a∈b⋯c) σ∈Γ = <:-⟨| (Ne∈-/Var a∈b⋯c σ∈Γ)
    <:-/Var (<:-|⟩ a∈b⋯c) σ∈Γ = <:-|⟩ (Ne∈-/Var a∈b⋯c σ∈Γ)

    <:⇇-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b k σ} →
               Γ ⊢ a <: b ⇇ k → Δ ⊢/Var σ ∈ Γ →
               Δ ⊢ a /Var σ <: b /Var σ ⇇ k Kind′/Var σ
    <:⇇-/Var (<:-⇇ a⇇k b⇇k a<:b) σ∈Γ =
      <:-⇇ (Nf⇇-/Var a⇇k σ∈Γ) (Nf⇇-/Var b⇇k σ∈Γ) (<:-/Var a<:b σ∈Γ)
    <:⇇-/Var (<:-λ a₁<:a₂ Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) σ∈Γ =
      <:-λ (<:⇇-/Var a₁<:a₂ (∈-↑ (<:⇇-/Var-wf a₁<:a₂ σ∈Γ) σ∈Γ))
           (Nf⇇-/Var Λj₁a₁⇇Πjk σ∈Γ) (Nf⇇-/Var Λj₂a₂⇇Πjk σ∈Γ)

    -- Renamings preserve type equality.

    ≃-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b k σ} →
              Γ ⊢ a ≃ b ⇇ k → Δ ⊢/Var σ ∈ Γ →
              Δ ⊢ a /Var σ ≃ b /Var σ ⇇ k Kind′/Var σ
    ≃-/Var (<:-antisym k-kd a<:b b<:a) σ∈Γ =
      <:-antisym (kd-/Var k-kd σ∈Γ) (<:⇇-/Var a<:b σ∈Γ) (<:⇇-/Var b<:a σ∈Γ)

    Sp≃-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as bs j k σ} →
                Γ ⊢ j ⇉∙ as ≃ bs ⇉ k → Δ ⊢/Var σ ∈ Γ →
                Δ ⊢ j Kind′/Var σ ⇉∙ as //Var σ ≃ bs //Var σ ⇉ k Kind′/Var σ
    Sp≃-/Var ≃-[] σ∈Γ = ≃-[]
    Sp≃-/Var (≃-∷ {a} {_} {_} {_} {j} {k} a≃b as≃bs) σ∈Γ =
      ≃-∷ (≃-/Var a≃b σ∈Γ)
          (subst (_ ⊢_⇉∙ _ ≃ _ ⇉ _) (Kind[∈⌊⌋]-/ k a j) (Sp≃-/Var as≃bs σ∈Γ))

    -- Helpers (to satisfy the termination checker).
    --
    -- These are simply (manual) expansions of the form
    --
    --   XX-/Var-wf x σ∈Γ  =  wf-/Var (wf-∷₁ (XX-ctx x)) σ∈Γ
    --
    -- to ensure the above definitions remain structurally recursive
    -- in the various derivations.

    kd-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
                 kd j ∷ Γ ⊢ k kd → Δ ⊢/Var σ ∈ Γ → Δ ⊢ kd (j Kind′/Var σ) wf
    kd-/Var-wf (kd-⋯ a∈a⋯a _) σ∈Γ = Nf⇉-/Var-wf a∈a⋯a σ∈Γ
    kd-/Var-wf (kd-Π j-kd _)  σ∈Γ = kd-/Var-wf j-kd σ∈Γ

    Nf⇉-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                  kd j ∷ Γ ⊢Nf a ⇉ k → Δ ⊢/Var σ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var σ) wf
    Nf⇉-/Var-wf (⇉-⊥-f (j-wf ∷ _)) σ∈Γ = wf-/Var j-wf σ∈Γ
    Nf⇉-/Var-wf (⇉-⊤-f (j-wf ∷ _)) σ∈Γ = wf-/Var j-wf σ∈Γ
    Nf⇉-/Var-wf (⇉-∀-f k-kd _)     σ∈Γ = kd-/Var-wf k-kd σ∈Γ
    Nf⇉-/Var-wf (⇉-→-f a⇉a⋯a _)    σ∈Γ = Nf⇉-/Var-wf a⇉a⋯a σ∈Γ
    Nf⇉-/Var-wf (⇉-Π-i j-kd _)     σ∈Γ = kd-/Var-wf j-kd σ∈Γ
    Nf⇉-/Var-wf (⇉-s-i a∈b⋯c)      σ∈Γ = Ne∈-/Var-wf a∈b⋯c σ∈Γ

    Ne∈-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                  kd j ∷ Γ ⊢Ne a ∈ k → Δ ⊢/Var σ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var σ) wf
    Ne∈-/Var-wf (∈-∙ x∈k _) σ∈Γ = Var∈-/Var-wf x∈k σ∈Γ

    Var∈-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                   kd j ∷ Γ ⊢Var a ∈ k → Δ ⊢/Var σ ∈ Γ →
                   Δ ⊢ kd (j Kind′/Var σ) wf
    Var∈-/Var-wf (⇉-var x (j-wf ∷ _) _) σ∈Γ = wf-/Var j-wf σ∈Γ
    Var∈-/Var-wf (⇇-⇑ x∈j _ _)          σ∈Γ = Var∈-/Var-wf x∈j σ∈Γ

    Nf⇇-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a j k σ} →
                  kd j ∷ Γ ⊢Nf a ⇇ k → Δ ⊢/Var σ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var σ) wf
    Nf⇇-/Var-wf (⇇-⇑ a⇉j _) σ∈Γ = Nf⇉-/Var-wf a⇉j σ∈Γ

    <∷-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k l σ} →
                 kd j ∷ Γ ⊢ k <∷ l → Δ ⊢/Var σ ∈ Γ → Δ ⊢ kd (j Kind′/Var σ) wf
    <∷-/Var-wf (<∷-⋯ a₂<:a₁ _)   σ∈Γ = <:-/Var-wf a₂<:a₁ σ∈Γ
    <∷-/Var-wf (<∷-Π j₂<∷j₁ _ _) σ∈Γ = <∷-/Var-wf j₂<∷j₁ σ∈Γ

    <:-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j σ} →
                 kd j ∷ Γ ⊢ a <: b → Δ ⊢/Var σ ∈ Γ →
                 Δ ⊢ kd (j Kind′/Var σ) wf
    <:-/Var-wf (<:-trans a<:b _) σ∈Γ = <:-/Var-wf a<:b σ∈Γ
    <:-/Var-wf (<:-⊥ a⇉a⋯a)      σ∈Γ = Nf⇉-/Var-wf a⇉a⋯a σ∈Γ
    <:-/Var-wf (<:-⊤ a⇉a⋯a)      σ∈Γ = Nf⇉-/Var-wf a⇉a⋯a σ∈Γ
    <:-/Var-wf (<:-∀ k₂<∷k₁ _ _) σ∈Γ = <∷-/Var-wf k₂<∷k₁ σ∈Γ
    <:-/Var-wf (<:-→ a₂<:a₁ _)   σ∈Γ = <:-/Var-wf a₂<:a₁ σ∈Γ
    <:-/Var-wf (<:-∙ x∈j _)      σ∈Γ = Var∈-/Var-wf x∈j σ∈Γ
    <:-/Var-wf (<:-⟨| a∈b⋯c)     σ∈Γ = Ne∈-/Var-wf a∈b⋯c σ∈Γ
    <:-/Var-wf (<:-|⟩ a∈b⋯c)     σ∈Γ = Ne∈-/Var-wf a∈b⋯c σ∈Γ

    <:⇇-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a b j k σ} →
                  kd j ∷ Γ ⊢ a <: b ⇇ k → Δ ⊢/Var σ ∈ Γ →
                  Δ ⊢ kd (j Kind′/Var σ) wf
    <:⇇-/Var-wf (<:-⇇ a⇇k _ _)       σ∈Γ = Nf⇇-/Var-wf a⇇k σ∈Γ
    <:⇇-/Var-wf (<:-λ _ Λj₁a₁⇇Πjk _) σ∈Γ = Nf⇇-/Var-wf Λj₁a₁⇇Πjk σ∈Γ

    ≅-/Var-wf : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k l σ} →
                kd j ∷ Γ ⊢ k ≅ l → Δ ⊢/Var σ ∈ Γ → Δ ⊢ kd (j Kind′/Var σ) wf
    ≅-/Var-wf (<∷-antisym _ _ j<∷k _) σ∈Γ = <∷-/Var-wf j<∷k σ∈Γ

  -- Renamings preserve kind equality.
  ≅-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {j k σ} →
           Γ ⊢ j ≅ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢ j Kind′/Var σ ≅ k Kind′/Var σ
  ≅-/Var (<∷-antisym j-kd k-kd j<∷k k<∷j) σ∈Γ =
    <∷-antisym (kd-/Var j-kd σ∈Γ) (kd-/Var k-kd σ∈Γ)
               (<∷-/Var j<∷k σ∈Γ) (<∷-/Var k<∷j σ∈Γ)


  -- Weakening preserves well-formedness of kinds.

  kd-weaken : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢ a wf → Γ ⊢ k kd → a ∷ Γ ⊢ weakenKind′ k kd
  kd-weaken a-wf k-kd = kd-/Var k-kd (∈-wk a-wf)

  kd-weaken⋆ : ∀ {m n} {Δ′ : CtxExt′ m n} {Γ : Ctx m} {k} →
               Γ ⊢ Δ′ ext′ → Γ ⊢ k kd → Δ′ ′++ Γ ⊢ weakenKind′⋆ n k kd
  kd-weaken⋆ {_} {_} {[]}    []              k-kd = k-kd
  kd-weaken⋆ {_} {_} {_ ∷ _} (a-kd ∷ Δ′-ext) k-kd =
    kd-weaken a-kd (kd-weaken⋆ Δ′-ext k-kd)

  -- Weakening preserves variable kinding of.
  Var∈-weaken : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a wf →
                Γ ⊢Var b ∈ k → a ∷ Γ ⊢Var weakenHead b ∈ weakenKind′ k
  Var∈-weaken a-wf x∈k = Var∈-/Var x∈k (∈-wk a-wf)

  -- Weakening preserves spine kinding.
  Sp⇉-weaken : ∀ {n} {Γ : Ctx n} {a bs j k} → Γ ⊢ a wf → Γ ⊢ j ⇉∙ bs ⇉ k →
               a ∷ Γ ⊢ weakenKind′ j ⇉∙ weakenSpine bs ⇉ weakenKind′ k
  Sp⇉-weaken a-wf j⇉bs⇉k = Sp⇉-/Var j⇉bs⇉k (∈-wk a-wf)

  -- Weakening preserves checked kinding.

  Nf⇇-weaken : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a wf →
               Γ ⊢Nf b ⇇ k → (a ∷ Γ) ⊢Nf weakenElim b ⇇ weakenKind′ k
  Nf⇇-weaken a-wf b⇇k = Nf⇇-/Var b⇇k (∈-wk a-wf)

  Nf⇇-weaken⋆ : ∀ {m n} {Δ′ : CtxExt′ m n} {Γ : Ctx m} {a k} → Γ ⊢ Δ′ ext′ →
                Γ ⊢Nf a ⇇ k → Δ′ ′++ Γ ⊢Nf weakenElim⋆ n a ⇇ weakenKind′⋆ n k
  Nf⇇-weaken⋆ {_} {_} {[]}    []              a⇇k = a⇇k
  Nf⇇-weaken⋆ {_} {_} {_ ∷ _} (a-wf ∷ Δ′-ext) a⇇k =
    Nf⇇-weaken a-wf (Nf⇇-weaken⋆ Δ′-ext a⇇k)

  -- Weakening preserves subkinding.

  <∷-weaken : ∀ {n} {Γ : Ctx n} {a j k} → Γ ⊢ a wf →
              Γ ⊢ j <∷ k → (a ∷ Γ) ⊢ weakenKind′ j <∷ weakenKind′ k
  <∷-weaken a-wf j<∷k = <∷-/Var j<∷k (∈-wk a-wf)

  <∷-weaken⋆ : ∀ {m n} {Δ′ : CtxExt′ m n} {Γ : Ctx m} {j k} → Γ ⊢ Δ′ ext′ →
               Γ ⊢ j <∷ k → Δ′ ′++ Γ ⊢ weakenKind′⋆ n j <∷ weakenKind′⋆ n k
  <∷-weaken⋆ {_} {_} {[]}    []              j<∷k = j<∷k
  <∷-weaken⋆ {_} {_} {_ ∷ _} (a-wf ∷ Δ′-ext) j<∷k =
    <∷-weaken a-wf (<∷-weaken⋆ Δ′-ext j<∷k)

  -- Weakening preserves subtyping.

  <:-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b <: c →
              a ∷ Γ ⊢ weakenElim b <: weakenElim c
  <:-weaken a-wf b<:c = <:-/Var b<:c (∈-wk a-wf)

  <:-weaken⋆ : ∀ {m n} {Δ′ : CtxExt′ m n} {Γ : Ctx m} {b c} →
               Γ ⊢ Δ′ ext′ → Γ ⊢ b <: c →
               Δ′ ′++ Γ ⊢ weakenElim⋆ n b <: weakenElim⋆ n c
  <:-weaken⋆ {_} {_} {[]}    []              b<:c = b<:c
  <:-weaken⋆ {_} {_} {_ ∷ _} (a-wf ∷ Δ′-ext) b<:c =
    <:-weaken a-wf (<:-weaken⋆ Δ′-ext b<:c)

  <:⇇-weaken : ∀ {n} {Γ : Ctx n} {a b c k} → Γ ⊢ a wf → Γ ⊢ b <: c ⇇ k →
               a ∷ Γ ⊢ weakenElim b <: weakenElim c ⇇ weakenKind′ k
  <:⇇-weaken a-wf b<:c = <:⇇-/Var b<:c (∈-wk a-wf)

  <:⇇-weaken⋆ : ∀ {m n} {Δ′ : CtxExt′ m n} {Γ : Ctx m} {b c k} →
                Γ ⊢ Δ′ ext′ → Γ ⊢ b <: c ⇇ k →
                Δ′ ′++ Γ ⊢ weakenElim⋆ n b <: weakenElim⋆ n c ⇇ weakenKind′⋆ n k
  <:⇇-weaken⋆ {_} {_} {[]}    []              b<:c = b<:c
  <:⇇-weaken⋆ {_} {_} {_ ∷ _} (a-wf ∷ Δ′-ext) b<:c =
    <:⇇-weaken a-wf (<:⇇-weaken⋆ Δ′-ext b<:c)


  -- Weakening preserves well-formedness of ascriptions.

  wf-weaken : ∀ {n} {Γ : Ctx n} {a b} →
              Γ ⊢ a wf → Γ ⊢ b wf → a ∷ Γ ⊢ weakenElimAsc b wf
  wf-weaken a-wf b-wf = wf-/Var b-wf (∈-wk a-wf)

  wf-weaken⋆ : ∀ {m n} {Δ′ : CtxExt′ m n} {Γ : Ctx m} {a} →
               Γ ⊢ Δ′ ext′ → Γ ⊢ a wf → Δ′ ′++ Γ ⊢ weakenElimAsc⋆ n a wf
  wf-weaken⋆ {_} {_} {[]}    []              a-wf = a-wf
  wf-weaken⋆ {_} {_} {_ ∷ _} (b-wf ∷ Δ′-ext) a-wf =
    wf-weaken b-wf (wf-weaken⋆ Δ′-ext a-wf)

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

  wfWeakenOps : WfWeakenOps weakenOps
  wfWeakenOps = record { wf-weaken = wf-weaken }

  private module W = WfWeakenOps wfWeakenOps
  open W public hiding (wf-weaken)

  -- Lookup the kind of a type variable in a well-formed context.
  lookup-kd : ∀ {m} {Γ : Ctx m} {a} x →
              Γ ctx → ElimCtx.lookup x Γ ≡ kd a → Γ ⊢ a kd
  lookup-kd x Γ-ctx Γ[x]≡kd-a =
    wf-kd-inv (subst (_ ⊢_wf) Γ[x]≡kd-a (W.lookup x Γ-ctx))

open WfCtxOps hiding (lookup)
open KindedRenaming
open Substitution hiding (subst)

-- A corollary -- validity of variable kinding: the kinds of variables
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
  open ≡-Reasoning
  open WellFormedContextLemmas _⊢_wf

  private
    module KL = TermLikeLemmas termLikeLemmasKind′
    module AL = TermLikeLemmas termLikeLemmasElimAsc

  -- "Lookup" the narrowed type of a variable.
  ⇓-Var∈-Hit : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} {j k₁ k₂} →
               let Γ  = Γ₂ ′++ kd k₂ ∷ Γ₁
                   Δ  = Γ₂ ′++ kd k₁ ∷ Γ₁
                   x  = raise n zero
                   j′ = weakenKind′⋆ n (weakenKind′ k₁)
               in Γ ctx → lookup x Γ ≡ kd j → Γ₁ ⊢ k₁ <∷ k₂ → Δ ctx →
                  Δ ⊢Var var x ∈ j
  ⇓-Var∈-Hit {_} {n} Γ₂ {Γ₁} {j} {k₁} {k₂} Γ-ctx Γ[x]≡kd-j k₁<∷k₂ Δ-ctx =
    let k₂′≡j = kd-inj (begin
            kd (weakenKind′⋆ n (weakenKind′ k₂))
          ≡⟨ cong kd (sym (KL./-wk⋆ n)) ⟩
            weakenElimAsc (kd k₂) ElimAsc/ wk⋆ n
          ≡⟨ AL./-wk⋆ n ⟩
            weakenElimAsc⋆ n (weakenElimAsc (kd k₂))
          ≡⟨ sym (lookup-weaken⋆′ n zero [] Γ₂ (kd k₂ ∷ Γ₁)) ⟩
            lookup (raise n zero) (Γ₂ ′++ kd k₂ ∷ Γ₁)
          ≡⟨ Γ[x]≡kd-j ⟩
            kd j
          ∎)
        Γ₂-ext , k₁∷Γ₁-ctx = wf-split Δ-ctx
        _      , k₂∷Γ₁-ctx = wf-split {Δ = CtxExt′⇒CtxExt Γ₂} Γ-ctx
        k₂-kd              = wf-kd-inv (wf-∷₁ k₂∷Γ₁-ctx)
    in ⇇-⇑ (⇉-var (raise n zero) Δ-ctx (begin
                lookup (raise n zero) (Γ₂ ′++ kd k₁ ∷ Γ₁)
              ≡⟨ lookup-weaken⋆′ n zero [] Γ₂ (kd k₁ ∷ Γ₁) ⟩
                weakenElimAsc⋆ n (weakenElimAsc (kd k₁))
              ≡⟨ sym (AL./-wk⋆ n) ⟩
                weakenElimAsc (kd k₁) ElimAsc/ wk⋆ n
              ≡⟨ cong kd (KL./-wk⋆ n) ⟩
                kd (weakenKind′⋆ n (weakenKind′ k₁))
              ∎))
           (subst (Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ _ <∷_) k₂′≡j
                  (<∷-weaken⋆ {Δ′ = Γ₂} Γ₂-ext
                              (<∷-weaken (wf-∷₁ k₁∷Γ₁-ctx) k₁<∷k₂)))
           (subst (Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢_kd) k₂′≡j
                  (kd-weaken⋆ {Δ′ = Γ₂} Γ₂-ext
                              (kd-weaken (wf-∷₁ k₁∷Γ₁-ctx) k₂-kd)))

  -- "Lookup" the type of a variable not affected by narrowing.
  ⇓-Var∈-Miss : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} y {j k₁ k₂} →
                let Γ = Γ₂ ′++ kd k₂ ∷ Γ₁
                    Δ = Γ₂ ′++ kd k₁ ∷ Γ₁
                    x = lift n suc y
                in Δ ctx → lookup x Γ ≡ kd j → Δ ⊢Var var x ∈ j
  ⇓-Var∈-Miss {_} {n} Γ₂ {Γ₁} y {j} {k₁} {k₂} Δ-ctx Γ[x]≡kd-j =
    ⇉-var (lift n suc y) Δ-ctx (begin
        lookup (lift n suc y) (Γ₂ ′++ kd k₁ ∷ Γ₁)
      ≡⟨ lookup-′++ (lift n suc y) [] Γ₂ (kd k₁ ∷ Γ₁) ⟩
        extLookup′ (lift n suc y) (kd (weakenKind′ k₁) ∷ _) Γ₂
      ≡⟨ sym (lookup′-lift y (kd (weakenKind′ k₁)) _ Γ₂) ⟩
        extLookup′ y _ Γ₂
      ≡⟨ lookup′-lift y (kd (weakenKind′ k₂)) _ Γ₂ ⟩
        extLookup′ (lift n suc y) (kd (weakenKind′ k₂) ∷ _) Γ₂
      ≡⟨ sym (lookup-′++ (lift n suc y) [] Γ₂ (kd k₂ ∷ Γ₁)) ⟩
        lookup (lift n suc y) (Γ₂ ′++ kd k₂ ∷ Γ₁)
      ≡⟨ Γ[x]≡kd-j ⟩
        kd j
      ∎)

  mutual

    -- Context narrowing preserves well-formedness of ascriptions.
    ⇓-wf : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a} →
           Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
           Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ a wf → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ a wf
    ⇓-wf Γ₂ k₁-kd k₁<∷k₂ (wf-kd k-kd)  = wf-kd (⇓-kd Γ₂ k₁-kd k₁<∷k₂ k-kd)
    ⇓-wf Γ₂ k₁-kd k₁<∷k₂ (wf-tp a⇉a⋯a) = wf-tp (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ a⇉a⋯a)

    -- Context narrowing preserves well-formedness of contexts.
    ⇓-ctx : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} →
            Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ctx → Γ₂ ′++ kd k₁ ∷ Γ₁ ctx
    ⇓-ctx []       k₁-kd k₁<∷k₂ (_    ∷ Γ₁-ctx) = wf-kd k₁-kd ∷ Γ₁-ctx
    ⇓-ctx (a ∷ Γ₂) k₁-kd k₁<∷k₂ (a-wf ∷ Γ₁-ctx) =
      ⇓-wf Γ₂ k₁-kd k₁<∷k₂ a-wf ∷ ⇓-ctx Γ₂ k₁-kd k₁<∷k₂ Γ₁-ctx

    -- Context narrowing preserves well-formedness of kinds.
    ⇓-kd : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {j} →
           Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
           Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ j kd → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ j kd
    ⇓-kd Γ₂ k₁-kd k₁<∷k₂ (kd-⋯ a⇉a⋯a b⇉b⋯b) =
      kd-⋯ (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ a⇉a⋯a) (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ b⇉b⋯b)
    ⇓-kd Γ₂ k₁-kd k₁<∷k₂ (kd-Π j₁-kd j₂-kd) =
      kd-Π (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j₁-kd) (⇓-kd (_ ∷ Γ₂) k₁-kd k₁<∷k₂ j₂-kd)

    -- Context narrowing preserves synthesized kinds of normal forms.
    ⇓-Nf⇉ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a j} →
            Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢Nf a ⇉ j → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢Nf a ⇉ j
    ⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-⊥-f Γ-ctx) =
      ⇉-⊥-f (⇓-ctx Γ₂ k₁-kd k₁<∷k₂ Γ-ctx)
    ⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-⊤-f Γ-ctx) =
      ⇉-⊤-f (⇓-ctx Γ₂ k₁-kd k₁<∷k₂ Γ-ctx)
    ⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-∀-f j-kd a⇉a⋯a) =
      ⇉-∀-f (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j-kd) (⇓-Nf⇉ (_ ∷ Γ₂) k₁-kd k₁<∷k₂ a⇉a⋯a)
    ⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-→-f a⇉a⋯a b⇉b⋯b) =
      ⇉-→-f (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ a⇉a⋯a) (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ b⇉b⋯b)
    ⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-Π-i j₁-kd a⇉j₂) =
      ⇉-Π-i (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j₁-kd) (⇓-Nf⇉ (_ ∷ Γ₂) k₁-kd k₁<∷k₂ a⇉j₂)
    ⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-s-i a∈b⋯c) =
      ⇉-s-i (⇓-Ne∈ Γ₂ k₁-kd k₁<∷k₂ a∈b⋯c)

    -- Context narrowing preserves the kinds of variables.
    ⇓-Var∈ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a j} →
             Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
             Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢Var a ∈ j → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢Var a ∈ j
    ⇓-Var∈ {_} {n} Γ₂ k₁-kd k₁<∷k₂ (⇉-var x  Γ-ctx Γ[x]≡kd-j) with compare n x
    ⇓-Var∈ {_} {n} Γ₂ k₁-kd k₁<∷k₂ (⇉-var ._ Γ-ctx Γ[x]≡kd-j) | yes refl =
      let Δ-ctx = ⇓-ctx Γ₂ k₁-kd k₁<∷k₂ Γ-ctx
      in ⇓-Var∈-Hit Γ₂ Γ-ctx Γ[x]≡kd-j k₁<∷k₂ Δ-ctx
    ⇓-Var∈ Γ₂ k₁-kd k₁<∷k₂ (⇉-var ._ Γ-ctx Γ[x]≡kd-j) | no y refl =
      ⇓-Var∈-Miss Γ₂ y (⇓-ctx Γ₂ k₁-kd k₁<∷k₂ Γ-ctx) Γ[x]≡kd-j
    ⇓-Var∈ Γ₂ k₁-kd k₁<∷k₂ (⇇-⇑ x∈j₁ j₁<∷j₂ j₂-kd) =
      ⇇-⇑ (⇓-Var∈ Γ₂ k₁-kd k₁<∷k₂ x∈j₁) (⇓-<∷  Γ₂ k₁-kd k₁<∷k₂ j₁<∷j₂)
          (⇓-kd  Γ₂ k₁-kd k₁<∷k₂ j₂-kd)

    -- Context narrowing preserves the kinds of neutral types.
    ⇓-Ne∈ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a j} →
            Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢Ne a ∈ j → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢Ne a ∈ j
    ⇓-Ne∈ Γ₂ k₁-kd k₁<∷k₂ (∈-∙ x∈j j⇉as⇉b⋯c) =
      ∈-∙ (⇓-Var∈ Γ₂ k₁-kd k₁<∷k₂ x∈j) (⇓-Sp⇉ Γ₂ k₁-kd k₁<∷k₂ j⇉as⇉b⋯c)

    -- Context narrowing preserves spine kindings.
    ⇓-Sp⇉ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {as j₁ j₂} →
            Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ j₁ ⇉∙ as ⇉ j₂ →
            Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ j₁ ⇉∙ as ⇉ j₂
    ⇓-Sp⇉ Γ₂ k₁-kd k₁<∷k₂ ⇉-[] = ⇉-[]
    ⇓-Sp⇉ Γ₂ k₁-kd k₁<∷k₂ (⇉-∷ a⇇j₁ j₁-kd j₂[a]⇉as⇉j₃) =
      ⇉-∷ (⇓-Nf⇇ Γ₂ k₁-kd k₁<∷k₂ a⇇j₁) (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j₁-kd)
          (⇓-Sp⇉ Γ₂ k₁-kd k₁<∷k₂ j₂[a]⇉as⇉j₃)

    -- Context narrowing preserves checked kinds.
    ⇓-Nf⇇ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a j} →
            Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢Nf a ⇇ j → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢Nf a ⇇ j
    ⇓-Nf⇇ Γ₂ k₁-kd k₁<∷k₂ (⇇-⇑ a⇉j₁ j₁<∷j₂) =
      ⇇-⇑ (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ a⇉j₁) (⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ j₁<∷j₂)

    -- Context narrowing preserves subkinding.
    ⇓-<∷ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {j₁ j₂} →
           Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
           Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ j₁ <∷ j₂ → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ j₁ <∷ j₂
    ⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ (<∷-⋯ a₂<:a₁ b₁<:b₂) =
      <∷-⋯ (⇓-<: Γ₂ k₁-kd k₁<∷k₂ a₂<:a₁) (⇓-<: Γ₂ k₁-kd k₁<∷k₂ b₁<:b₂)
    ⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ (<∷-Π j₂<∷j₁ j₁′<∷j₂′ Πj₁j₁′-kd) =
      <∷-Π (⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ j₂<∷j₁) (⇓-<∷ (_ ∷ Γ₂) k₁-kd k₁<∷k₂ j₁′<∷j₂′)
           (⇓-kd Γ₂ k₁-kd k₁<∷k₂ Πj₁j₁′-kd)

    -- Context narrowing preserves subtyping.

    ⇓-<: : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a₁ a₂} →
           Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
           Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ a₁ <: a₂ → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ a₁ <: a₂
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-trans a₁<:a₂ a₂<:a₃) =
      <:-trans (⇓-<: Γ₂ k₁-kd k₁<∷k₂ a₁<:a₂) (⇓-<: Γ₂ k₁-kd k₁<∷k₂ a₂<:a₃)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-⊥ a⇉a⋯a) = <:-⊥ (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ a⇉a⋯a)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-⊤ a⇉a⋯a) = <:-⊤ (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ a⇉a⋯a)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-∀ j₂<∷j₁ a₁<:a₂ Πj₁a₁⇉Πj₁a₁⋯Πj₁a₁) =
      <:-∀ (⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ j₂<∷j₁) (⇓-<: (_ ∷ Γ₂) k₁-kd k₁<∷k₂ a₁<:a₂)
           (⇓-Nf⇉ Γ₂ k₁-kd k₁<∷k₂ Πj₁a₁⇉Πj₁a₁⋯Πj₁a₁)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-→ a₂<:a₁ b₁<:b₂) =
      <:-→ (⇓-<: Γ₂ k₁-kd k₁<∷k₂ a₂<:a₁) (⇓-<: Γ₂ k₁-kd k₁<∷k₂ b₁<:b₂)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-∙ x∈j as≃bs) =
      <:-∙ (⇓-Var∈ Γ₂ k₁-kd k₁<∷k₂ x∈j) (⇓-Sp≃ Γ₂ k₁-kd k₁<∷k₂ as≃bs)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-⟨| a∈b⋯c) = <:-⟨| (⇓-Ne∈ Γ₂ k₁-kd k₁<∷k₂ a∈b⋯c)
    ⇓-<: Γ₂ k₁-kd k₁<∷k₂ (<:-|⟩ a∈b⋯c) = <:-|⟩ (⇓-Ne∈ Γ₂ k₁-kd k₁<∷k₂ a∈b⋯c)

    ⇓-<:⇇ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a₁ a₂ j} →
            Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ a₁ <: a₂ ⇇ j → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ a₁ <: a₂ ⇇ j
    ⇓-<:⇇ Γ₂ k₁-kd k₁<∷k₂ (<:-⇇ a⇇k b⇇k a<:b) =
      <:-⇇ (⇓-Nf⇇ Γ₂ k₁-kd k₁<∷k₂ a⇇k) (⇓-Nf⇇ Γ₂ k₁-kd k₁<∷k₂ b⇇k)
           (⇓-<: Γ₂ k₁-kd k₁<∷k₂ a<:b)
    ⇓-<:⇇ Γ₂ k₁-kd k₁<∷k₂ (<:-λ a₁<:a₂ Λj₁a₁⇇Πjk Λj₂a₂⇇Πjk) =
      <:-λ (⇓-<:⇇ (_ ∷ Γ₂) k₁-kd k₁<∷k₂ a₁<:a₂)
           (⇓-Nf⇇ Γ₂ k₁-kd k₁<∷k₂ Λj₁a₁⇇Πjk) (⇓-Nf⇇ Γ₂ k₁-kd k₁<∷k₂ Λj₂a₂⇇Πjk)

    -- Context narrowing preserves type equality.

    ⇓-≃⇇ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {a₁ a₂ j} →
           Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
           Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ a₁ ≃ a₂ ⇇ j → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ a₁ ≃ a₂ ⇇ j
    ⇓-≃⇇ Γ₂ k₁-kd k₁<∷k₂ (<:-antisym j-kd a<:b b<:a) =
      <:-antisym (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j-kd)
                 (⇓-<:⇇ Γ₂ k₁-kd k₁<∷k₂ a<:b) (⇓-<:⇇ Γ₂ k₁-kd k₁<∷k₂ b<:a)

    ⇓-Sp≃ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m}
            {as bs j₁ j₂} → Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
            Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ j₁ ⇉∙ as ≃ bs ⇉ j₂ →
            Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ j₁ ⇉∙ as ≃ bs ⇉ j₂
    ⇓-Sp≃ Γ₂ k₁-kd k₁<∷k₂ ≃-[] = ≃-[]
    ⇓-Sp≃ Γ₂ k₁-kd k₁<∷k₂ (≃-∷ a≃b as≃bs) =
      ≃-∷ (⇓-≃⇇  Γ₂ k₁-kd k₁<∷k₂ a≃b) (⇓-Sp≃ Γ₂ k₁-kd k₁<∷k₂ as≃bs)

  -- Context narrowing preserves kind equality.
  ⇓-≅ : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {k₁ k₂} {Γ₁ : Ctx m} {j₁ j₂} →
        Γ₁ ⊢ k₁ kd → Γ₁ ⊢ k₁ <∷ k₂ →
        Γ₂ ′++ kd k₂ ∷ Γ₁ ⊢ j₁ ≅ j₂ → Γ₂ ′++ kd k₁ ∷ Γ₁ ⊢ j₁ ≅ j₂
  ⇓-≅ Γ₂ k₁-kd k₁<∷k₂ (<∷-antisym j₁-kd j₂-kd j₁≅j₂ j₂≅j₁) =
    <∷-antisym (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j₁-kd) (⇓-kd Γ₂ k₁-kd k₁<∷k₂ j₂-kd)
               (⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ j₁≅j₂) (⇓-<∷ Γ₂ k₁-kd k₁<∷k₂ j₂≅j₁)

open ContextNarrowing

-- Some corollaries of context narrowing: transitivity of subkinding
-- and kind equality are admissible.

<∷-trans : ∀ {n} {Γ : Ctx n} {j k l} → Γ ⊢ j <∷ k → Γ ⊢ k <∷ l → Γ ⊢ j <∷ l
<∷-trans (<∷-⋯ a₂<:a₁ b₁<:b₂) (<∷-⋯ a₃<:a₂ b₂<:b₃) =
  <∷-⋯ (<:-trans a₃<:a₂ a₂<:a₁) (<:-trans b₁<:b₂ b₂<:b₃)
<∷-trans (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) (<∷-Π j₃<∷j₂ k₂<∷k₃ _) =
  let j₃-kd = wf-kd-inv (wf-∷₁ (<∷-ctx k₂<∷k₃))
  in <∷-Π (<∷-trans j₃<∷j₂ j₂<∷j₁)
          (<∷-trans (⇓-<∷ [] j₃-kd j₃<∷j₂ k₁<∷k₂) k₂<∷k₃) Πj₁k₁-kd

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
  <:-λ (<:⇇-⇑ (⇓-<:⇇ [] k₂-kd k₂<∷k₁ a₁<:a₂) l₁<∷l₂ l₂-kd)
       (Nf⇇-⇑ Λj₁a₁⇇Πk₁l₁ (<∷-Π k₂<∷k₁ l₁<∷l₂ Πk₁l₁-kd))
       (Nf⇇-⇑ Λj₂a₂⇇Πk₁l₁ (<∷-Π k₂<∷k₁ l₁<∷l₂ Πk₁l₁-kd))

≃-⇑ : ∀ {n} {Γ : Ctx n} {a b j k} →
      Γ ⊢ a ≃ b ⇇ j → Γ ⊢ j <∷ k → Γ ⊢ k kd → Γ ⊢ a ≃ b ⇇ k
≃-⇑ (<:-antisym j-kd a<:b b<:a) j<∷k k-kd =
  <:-antisym k-kd (<:⇇-⇑ a<:b j<∷k k-kd) (<:⇇-⇑ b<:a j<∷k k-kd)


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
    let a<:a⇇k₂ = <:⇇-reflNf⇉-⇑ (⇓-Nf⇉ [] j₂-kd j₂<∷j₁ a⇉k₁) k₁<∷k₂ k₂-kd
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
Var∈-inv : ∀ {n} {Γ : Ctx n} {x k} → Γ ⊢Var var x ∈ k →
           ∃ λ j → lookup x Γ ≡ kd j × Γ ⊢ j <∷ k × Γ ⊢ j kd × Γ ⊢ k kd
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
      SimpleCtx.lookup x ⌊ Γ ⌋Ctx
    ≡⟨ ⌊⌋Ctx-Lemmas.lookup-map x ⌊_⌋Asc [] Γ (λ a → sym (⌊⌋Asc-weaken a)) ⟩
      ⌊ ElimCtx.lookup x Γ ⌋Asc
    ≡⟨ cong ⌊_⌋Asc Γ[x]≡kd-k ⟩
      kd ⌊ k ⌋
    ∎)
    where
      ⌊⌋Asc-weaken : ∀ {n} (a : ElimAsc n) → ⌊ weakenElimAsc a ⌋Asc ≡ ⌊ a ⌋Asc
      ⌊⌋Asc-weaken (kd a) = cong kd (⌊⌋-Kind′/Var a)
      ⌊⌋Asc-weaken (tp a) = refl
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
          (subst (_ ⊢_∋∙ _ ∈ _) (⌊⌋-Kind/H _) (Sp⇉-Sp∈ k[a]⇉as⇉l))

    Nf⇇-Nf∈ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Nf a ⇇ k → ⌊ Γ ⌋Ctx ⊢Nf a ∈ ⌊ k ⌋
    Nf⇇-Nf∈ (⇇-⇑ a⇉j j<∷k) = subst (_ ⊢Nf _ ∈_) (<∷-⌊⌋ j<∷k) (Nf⇉-Nf∈ a⇉j)


----------------------------------------------------------------------
-- Context equality
--
-- Properties of kind and type equality extended to kind an type
-- ascriptions as well as contexts.

infix  4 _⊢_≅_wf _⊢_≅_ext
infixr 5 _∷_

-- Equality of type and kind ascriptions.
data _⊢_≅_wf {n} (Γ : Ctx n) : ElimAsc n → ElimAsc n → Set where
  ≅-kd : ∀ {j k}     → Γ ⊢ j ≅ k         → Γ ⊢ kd j ≅ kd k wf
  ≅-tp : ∀ {a b c d} → Γ ⊢ a ≃ b ⇇ c ⋯ d → Γ ⊢ tp a ≅ tp b wf

-- Equality of context extensions.
data _⊢_≅_ext {m} (Γ : Ctx m) : ∀ {n} → CtxExt′ m n → CtxExt′ m n → Set where
  []  : Γ ⊢ [] ≅ [] ext
  _∷_ : ∀ {n a b} {Δ E : CtxExt′ m n} →
        (Δ ′++ Γ) ⊢ a ≅ b wf → Γ ⊢ Δ ≅ E ext → Γ ⊢ a ∷ Δ ≅ b ∷ E ext

-- Reflexivity of ascription equality.
≅wf-refl : ∀ {n} {Γ : Ctx n} {a} → Γ ⊢ a wf → Γ ⊢ a ≅ a wf
≅wf-refl (wf-kd j-kd)  = ≅-kd (≅-refl j-kd)
≅wf-refl (wf-tp a⇉a⋯a) = ≅-tp (≃-reflNf⇇ (Nf⇉⇒Nf⇇ a⇉a⋯a) (kd-⋯ a⇉a⋯a a⇉a⋯a))

-- Right-to-left inversion of kind ascription equality.
≅wf-kd-inv : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢ a ≅ kd k wf →
             ∃ λ j → a ≡ kd j × Γ ⊢ j ≅ k
≅wf-kd-inv (≅-kd j≅k) = _ , refl , j≅k

-- Validity of ascription equality.
≅wf-valid : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ≅ b wf → Γ ⊢ a wf × Γ ⊢ b wf
≅wf-valid (≅-kd (<∷-antisym j-kd  k-kd  _ _)) = wf-kd j-kd , wf-kd k-kd
≅wf-valid (≅-tp (<:-antisym _ a<:b⇇c⋯d _)) =
  let a⇇c⋯d , b⇇c⋯d = <:⇇-valid a<:b⇇c⋯d
  in wf-tp (Nf⇇-s-i a⇇c⋯d) , wf-tp (Nf⇇-s-i b⇇c⋯d)

-- Weakening preserves equality of ascriptions.
≅wf-weaken : ∀ {n} {Γ : Ctx n} {a b c} → Γ ⊢ a wf → Γ ⊢ b ≅ c wf →
             a ∷ Γ ⊢ weakenElimAsc b ≅ weakenElimAsc c wf
≅wf-weaken a-wf (≅-kd j≅k) = ≅-kd (≅-weaken a-wf j≅k)
≅wf-weaken a-wf (≅-tp a≃b) = ≅-tp (≃-weaken a-wf a≃b)

-- Convert a context equality to its All representation.
≅-extToAll : ∀ {m n} {Δ₁ Δ₂ : CtxExt′ m n} {Γ₁ Γ₂ : Ctx m} →
             All₂ (Γ₁ ⊢_≅_wf) (toVec Γ₁) (toVec Γ₂) → Γ₁ ⊢ Δ₁ ≅ Δ₂ ext →
             All₂ (Δ₁ ′++ Γ₁ ⊢_≅_wf) (toVec (Δ₁ ′++ Γ₁)) (toVec (Δ₂ ′++ Γ₂))
≅-extToAll as≅bs []            = as≅bs
≅-extToAll as≅bs (a≅b ∷ Δ₁≅Δ₂) =
  let a-wf , _ = ≅wf-valid a≅b
  in ≅wf-weaken a-wf a≅b ∷ gmap₂ (≅wf-weaken a-wf) (≅-extToAll as≅bs Δ₁≅Δ₂)

-- Ascriptions looked up in equal contexts are equal.

lookup-≅ : ∀ {m n} {Δ E : CtxExt′ m n} {Γ : Ctx m} x →
           Γ ctx → Γ ⊢ Δ ≅ E ext →
           Δ ′++ Γ ⊢ lookup x (Δ ′++ Γ) ≅ lookup x (E ′++ Γ) wf
lookup-≅ x Γ-ctx Δ≅E =
  VecAll.lookup₂ x (≅-extToAll (helper (WfCtxOps.toAll Γ-ctx)) Δ≅E)
  where
    helper : ∀ {m n Γ} {as : Vec (ElimAsc m) n} →
             VecAll.All (Γ ⊢_wf) as → All₂ (Γ ⊢_≅_wf) as as
    helper []             = []
    helper (a-wf ∷ as-wf) = ≅wf-refl a-wf ∷ helper as-wf

lookup-≅-kd : ∀ {m n} {Δ E : CtxExt′ m n} {Γ : Ctx m} {k} x →
              Γ ctx → Γ ⊢ Δ ≅ E ext → lookup x (E ′++ Γ) ≡ kd k →
              ∃ λ j → lookup x (Δ ′++ Γ) ≡ kd j × Δ ′++ Γ ⊢ j ≅ k
lookup-≅-kd x Γ-ctx Δ≅E E++Γ[x]≡kd-k =
  ≅wf-kd-inv (subst (_ ⊢ _ ≅_wf) E++Γ[x]≡kd-k (lookup-≅ x Γ-ctx Δ≅E))

-- Equal ascriptions and context extensions simplify equally.

⌊⌋-≅-wf : ∀ {n} {Γ : Ctx n} {a b} → Γ ⊢ a ≅ b wf → ⌊ a ⌋Asc ≡ ⌊ b ⌋Asc
⌊⌋-≅-wf (≅-kd j≅k) = cong kd (≅-⌊⌋ j≅k)
⌊⌋-≅-wf (≅-tp a≃b) = refl

⌊⌋-≅-ext : ∀ {m n} {E Δ : CtxExt′ m n} {Γ} → Γ ⊢ E ≅ Δ ext →
           _≡_ {A = SimpleCtx.CtxExt′ m n}
             (map′ (λ _ → ⌊_⌋Asc) E) (map′ (λ _ → ⌊_⌋Asc) Δ)
⌊⌋-≅-ext []          = refl
⌊⌋-≅-ext (a≅b ∷ E≅Δ) = cong₂ _∷_ (⌊⌋-≅-wf a≅b) (⌊⌋-≅-ext E≅Δ)
