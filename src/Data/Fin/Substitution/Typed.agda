------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Fin.Substitution.Typed where

open import Data.Context as Ctx hiding (map)
open import Data.Context.WellFormed
open import Data.Context.Properties using (module ContextFormationLemmas)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.Extra
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; map)
open import Data.Vec.Properties using (map-cong; map-∘; lookup-map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)
open import Function as Fun using (_∘_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Unary using (Pred)


------------------------------------------------------------------------
-- Abstract typing
--
-- Well-typed substitutions are defined over an abstract "type
-- system", i.e. a pair of formation and typing judgments and
-- substitution lemmas for raw terms and types.

-- An abtract typing judgment _⊢_∈_ : Typing Bnd Term Type is a
-- ternary relation which, in a given Bnd-context, relates Term-terms
-- to their Type-types.

Typing : ∀ {t₁ t₂ t₃} →
         Pred ℕ t₁ → Pred ℕ t₂ → Pred ℕ t₃ → ∀ ℓ →
         Set (t₁ ⊔ t₂ ⊔ t₃ ⊔ lsuc ℓ)
Typing Bnd Term Type ℓ = ∀ {n} → Ctx Bnd n → Term n → Type n → Set ℓ


------------------------------------------------------------------------
-- Abstract well-typed substitutions (aka context morphisms)

record TypedSub {t}
                (Type : Pred ℕ t)      -- Type syntax
                (Term : Pred ℕ lzero)  -- Term syntax
                ℓ
                : Set (lsuc (t ⊔ ℓ)) where

  -- The underlying type assignment system

  infix 4 _⊢_∈_ _⊢_wf

  field
    _⊢_wf : Wf Type Type ℓ            -- Type formation judgment
    _⊢_∈_ : Typing Type Term Type ℓ   -- Typing judgment

  -- Weakening and term substitutions in types.

  field
    typeExtension       : Extension Type          -- weakening of types
    typeTermApplication : Application Type Term   -- app. of term subst.
    termSimple          : Simple Term             -- simple term subst.

  open ContextFormation _⊢_wf          using (_wf)
  open Application typeTermApplication using (_/_)

  infix  4 _⊢/_∈_
  infixr 5 _∷_

  -- Typed substitutions.
  --
  -- A typed substitution Δ ⊢/ σ ∈ Γ is a substitution σ which, when
  -- applied to a well-typed term Γ ⊢ t ∈ a in a source context Γ,
  -- yields a well-typed term Δ ⊢ t / σ ∈ a / σ in a well-formed
  -- target context Δ.

  data _⊢/_∈_ {n} (Δ : Ctx Type n) :
              ∀ {m} → Sub Term m n → Ctx Type m → Set (t ⊔ ℓ) where
    []  : Δ wf → Δ ⊢/ [] ∈ []
    _∷_ : ∀ {m t} {a : Type m} {σ : Sub Term m n} {Γ} →
          Δ ⊢ t ∈ a / σ → Δ ⊢/ σ ∈ Γ → Δ ⊢/ t ∷ σ ∈ a ∷ Γ

  -- The domains of well-typed substitutions are well-formed.

  /∈-wf : ∀ {m n Δ} {σ : Sub Term m n} {Γ} → Δ ⊢/ σ ∈ Γ → Δ wf
  /∈-wf ([] Δ-wf) = Δ-wf
  /∈-wf (_ ∷ σ∈Γ) = /∈-wf σ∈Γ


------------------------------------------------------------------------
-- Operations on abstract well-typed substitutions

-- Operations on abstract typed substitutions that require weakening
-- of well-typed terms

record TypedWeakenOps {t ℓ} {Type : Pred ℕ t} {Term : Pred ℕ lzero}
                      (typedSub : TypedSub Type Term ℓ)
                      : Set (lsuc (t ⊔ ℓ)) where

  open TypedSub typedSub

  -- Operations on contexts and raw terms that require weakening

  private
    termExtension : Extension Term
    termExtension = record { weaken = Simple.weaken termSimple }

    module E = Extension termExtension
    module C = WeakenOps typeExtension

  open Simple           termSimple          using (wk)
  open Application      typeTermApplication using (_/_; _⊙_)
  open ContextFormation _⊢_wf               using (_wf; _∷_; wf-∷₁)

  field

    -- Weakening preserves well-typed terms.

    ∈-weaken : ∀ {n} {Δ : Ctx Type n} {t a b} → Δ ⊢ a wf → Δ ⊢ t ∈ b →
               (a ∷ Δ) ⊢ E.weaken t ∈ C.weaken b

    -- Well-typedness implies well-formedness of contexts.

    ∈-wf : ∀ {n} {Δ : Ctx Type n} {t a} → Δ ⊢ t ∈ a → Δ wf

    -- Lemmas relating type weakening to term substitutions

    /-wk : ∀ {n} {a : Type n} → a / wk ≡ C.weaken a

    /-weaken : ∀ {m n} {σ : Sub Term m n} a →
               a / map E.weaken σ ≡ a / σ / wk

    weaken-/-∷ : ∀ {n m} {t} {σ : Sub Term m n} (a : Type m) →
                 C.weaken a / (t ∷ σ) ≡ a / σ

  -- Some helper lemmas

  /-map-weaken : ∀ {m n} a (ρ : Sub Term m n) →
                 C.weaken (a / ρ) ≡ a / map E.weaken ρ
  /-map-weaken a ρ = begin
    C.weaken (a / ρ)    ≡⟨ sym /-wk ⟩
    a / ρ / wk          ≡⟨ sym (/-weaken a) ⟩
    a / map E.weaken ρ  ∎

  map-weaken-⊙-∷ : ∀ {m n} (σ : Sub Type m m) t (ρ : Sub Term m n) →
                   σ ⊙ ρ ≡ map C.weaken σ ⊙ (t ∷ ρ)
  map-weaken-⊙-∷ σ t ρ = sym (begin
    map C.weaken σ ⊙ (t ∷ ρ)          ≡⟨ sym (map-∘ _ C.weaken σ) ⟩
    map ((_/ (t ∷ ρ)) ∘ C.weaken) σ   ≡⟨ map-cong weaken-/-∷ σ ⟩
    map (_/ ρ) σ                      ≡⟨⟩
    σ ⊙ ρ                             ∎)

  -- Weakening preserves well-typed substitutions.

  /∈-weaken : ∀ {m n Δ a} {σ : Sub Term m n} {Γ} →
              Δ ⊢ a wf → Δ ⊢/ σ ∈ Γ →
              (a ∷ Δ) ⊢/ map E.weaken σ ∈ Γ
  /∈-weaken                         a-wf ([] Δ-wf)     = [] (a-wf ∷ Δ-wf)
  /∈-weaken {_} {_} {Δ} {a} {t ∷ σ} a-wf (t∈b/σ ∷ σ∈Γ) =
    subst (a ∷ Δ ⊢ _ ∈_) (/-map-weaken _ σ) (∈-weaken a-wf t∈b/σ) ∷
    (/∈-weaken a-wf σ∈Γ)


  -- A typed substitution consists of pointwise-typed terms.

  toPointwise : ∀ {m n Δ} {σ : Sub Term m n} {Γ} →
                Δ ⊢/ σ ∈ Γ → Pointwise (Δ ⊢_∈_) σ (C.toVec Γ ⊙ σ)
  toPointwise                     ([] Δ-wf)     = []
  toPointwise {_} {_} {Δ} {t ∷ σ} (t∈a/σ ∷ σ∈Γ) =
    subst (Δ ⊢ t ∈_) (sym (weaken-/-∷ _)) t∈a/σ ∷
    subst (Pointwise (_⊢_∈_ Δ) σ) (map-weaken-⊙-∷ _ t σ) (toPointwise σ∈Γ)

  -- Look up an entry in a typed substitution.

  lookup : ∀ {m n Δ} {σ : Sub Term m n} {Γ} →
           Δ ⊢/ σ ∈ Γ → (x : Fin m) → Δ ⊢ Vec.lookup σ x ∈ C.lookup Γ x / σ
  lookup {_} {_} {Δ} {σ} {Γ} σ∈Γ x =
    subst (Δ ⊢ _ ∈_) (lookup-map x _ (C.toVec Γ))
          (PW.lookup (toPointwise σ∈Γ) x)

  -- Extension by a typed term.

  ∈-/∷ : ∀ {m n Δ} {σ : Sub Term m n} {Γ t a b} →
         (b ∷ Δ) ⊢ t ∈ C.weaken (a / σ) → Δ ⊢/ σ ∈ Γ →
         b ∷ Δ ⊢/ t E./∷ σ ∈ a ∷ Γ
  ∈-/∷ t∈a/σ σ∈Γ =
    subst (_⊢_∈_ _ _) (/-map-weaken _ _) t∈a/σ ∷ /∈-weaken b-wf σ∈Γ

    where
    b∷Δ-wf = ∈-wf t∈a/σ
    b-wf   = wf-∷₁ b∷Δ-wf

-- Operations on abstract typed substitutions that require simple term
-- substitutions

record TypedSimple {t ℓ} {Type : Pred ℕ t} {Term : Pred ℕ lzero}
                   (typedSub : TypedSub Type Term ℓ)
                   : Set (lsuc (t ⊔ ℓ)) where

  -- Operations on abstract typed substitutions that require weakening
  -- of terms

  field typedWeakenOps : TypedWeakenOps typedSub

  open TypedWeakenOps   typedWeakenOps public
  open TypedSub         typedSub
  open ContextFormation _⊢_wf using (_wf; _⊢_wfExt; []; _∷_; wf-∷₂)
  open Application      typeTermApplication using (_/_)

  private
    module S = Simple    termSimple
    module C = WeakenOps typeExtension
  open S using (_↑; _↑⋆_; id; wk; sub)

  -- Context operations that require term substitutions in types.

  open SubstOps typeTermApplication termSimple using (_E/_)

  field

    -- Takes variables to well-typed Tms.

    ∈-var : ∀ {n} {Γ : Ctx Type n} →
            ∀ x → Γ wf → Γ ⊢ S.var x ∈ C.lookup Γ x

    -- Well-formedness of types implies well-formedness of contexts.

    wf-wf : ∀ {n} {Γ : Ctx Type n} {a} → Γ ⊢ a wf → Γ wf

    -- The identity substitution is an identity

    id-vanishes : ∀ {n} (a : Type n) → a / id ≡ a

  -- Lifting.

  ∈-↑ : ∀ {m n Δ} {σ : Sub Term m n} {a Γ} →
        Δ ⊢ a / σ wf → Δ ⊢/ σ ∈ Γ → a / σ ∷ Δ ⊢/ σ ↑ ∈ a ∷ Γ
  ∈-↑ a/σ-wf σ∈Γ = ∈-/∷ (∈-var zero (a/σ-wf ∷ (wf-wf a/σ-wf))) σ∈Γ

  ∈-↑⋆ : ∀ {k m n Δ} {E : CtxExt Type m k} {σ : Sub Term m n} {Γ} →
         Δ ⊢ (E E/ σ) wfExt → Δ ⊢/ σ ∈ Γ → (E E/ σ) ++ Δ ⊢/ σ ↑⋆ k ∈ (E ++ Γ)
  ∈-↑⋆ {E = []}            []                        σ∈Γ = σ∈Γ
  ∈-↑⋆ {E = a ∷ E} {Δ} {Γ} (a/σ↑⋆1+k-wf ∷ E/σ-wfExt) σ∈Γ =
    ∈-↑ {Γ = E ++ Γ} a/σ↑⋆1+k-wf (∈-↑⋆ {E = E} E/σ-wfExt σ∈Γ)

  -- The identity substitution.

  ∈-id : ∀ {n} {Γ : Ctx Type n} → Γ wf → Γ ⊢/ id ∈ Γ
  ∈-id []            = [] []
  ∈-id (a-wf ∷ Γ-wf) =
    ∈-/∷ (subst (_ ⊢ S.var zero ∈_) (sym (cong C.weaken (id-vanishes _)))
                (∈-var zero (a-wf ∷ Γ-wf)))
         (∈-id Γ-wf)

  -- Weakening.

  ∈-wk : ∀ {n} {Γ : Ctx Type n} {a} → Γ ⊢ a wf → a ∷ Γ ⊢/ wk ∈ Γ
  ∈-wk a-wf = /∈-weaken a-wf (∈-id (wf-wf a-wf))

  -- A substitution which only replaces the first variable.

  ∈-sub : ∀ {n} {Γ : Ctx Type n} {t a} → Γ ⊢ t ∈ a → Γ ⊢/ sub t ∈ a ∷ Γ
  ∈-sub t∈a =
    (subst (_ ⊢ _ ∈_) (sym (id-vanishes _)) t∈a) ∷ (∈-id (∈-wf t∈a))


  -- A substitution which only changes the type of the first variable.

  ∈-tsub : ∀ {n} {Γ : Ctx Type n} {a b} → b ∷ Γ ⊢ S.var zero ∈ C.weaken a →
           b ∷ Γ ⊢/ id ∈ a ∷ Γ
  ∈-tsub z∈a =
    ∈-/∷ (subst (_ ⊢ _ ∈_) (cong C.weaken (sym (id-vanishes _))) z∈a)
         (∈-id (wf-∷₂ (∈-wf z∈a)))

-- Application of typed substitutions to typed terms.

record TypedApplication {t ℓ} {Type : Pred ℕ t} {Term : Pred ℕ lzero}
                        (typedSub : TypedSub Type Term ℓ)
                        : Set (lsuc (t ⊔ ℓ)) where

  open TypedSub    typedSub
  open Application typeTermApplication using (_/_)

  -- Applications of term substitutions to terms

  field termTermApplication : Application Term Term

  private
    module C = WeakenOps typeExtension
    module A = Application termTermApplication
  open A using (_⊙_)

  field

    -- Post-application of substitutions to things.

    ∈-/ : ∀ {m n Δ} {σ : Sub Term m n} {Γ t a} →
          Γ ⊢ t ∈ a → Δ ⊢/ σ ∈ Γ → Δ ⊢ t A./ σ ∈ a / σ

    -- Application of composed substitutions is repeated application.

    /-⊙ : ∀ {m n k} {σ : Sub Term m n} {ρ : Sub Term n k} a →
          a / σ ⊙ ρ ≡ a / σ / ρ

  -- Reverse composition. (Fits well with post-application.)

  ∈-⊙ : ∀ {m n k Δ Γ E} {σ : Sub Term m n} {ρ : Sub Term n k} →
        Δ ⊢/ σ ∈ Γ → E ⊢/ ρ ∈ Δ → E ⊢/ σ ⊙ ρ ∈ Γ
  ∈-⊙ ([] Δ-wf)     ρ∈Δ = [] (/∈-wf ρ∈Δ)
  ∈-⊙ (t∈a/σ ∷ σ∈Γ) ρ∈Δ =
    (subst (_ ⊢ _ ∈_) (sym (/-⊙ _)) (∈-/ t∈a/σ ρ∈Δ)) ∷ (∈-⊙ σ∈Γ ρ∈Δ)


------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Abstract typed liftings from Term₁ to Term₂ terms

record LiftTyped {t ℓ₁ ℓ₂} {Type : Pred ℕ t} {Term₁ Term₂ : Pred ℕ lzero}
                 (typeTermSubst : TermLikeSubst Type Term₂)
                 (_⊢_wf  : Wf Type Type ℓ₁)
                 (_⊢₁_∈_ : Typing Type Term₁ Type ℓ₁)
                 (_⊢₂_∈_ : Typing Type Term₂ Type ℓ₂)
                 : Set (lsuc (t ⊔ ℓ₁ ⊔ ℓ₂)) where

  field rawLift : Lift Term₁ Term₂   -- Lifting between raw terms

  open TermLikeSubst typeTermSubst using (app; weaken; termSubst)
  private module S₂ = TermSubst termSubst

  typedSub : TypedSub Type Term₁ ℓ₁
  typedSub = record
    { _⊢_wf               = _⊢_wf
    ; _⊢_∈_               = _⊢₁_∈_
    ; typeExtension       = record { weaken = weaken }
    ; typeTermApplication = record { _/_    = app rawLift }
    ; termSimple          = Lift.simple rawLift
    }
  open TypedSub typedSub public hiding (_⊢_wf; _⊢_∈_; typeExtension)

  -- Simple typed Term₁ substitutions.

  field typedSimple : TypedSimple typedSub

  open Lift        rawLift             public
  open Application typeTermApplication public
  open TypedSimple typedSimple         public

  field

    -- Lifts well-typed Term₁-terms to well-typed Term₂-terms.

    ∈-lift : ∀ {n} {Γ : Ctx Type n} {t a} → Γ ⊢₁ t ∈ a → Γ ⊢₂ (lift t) ∈ a

    -- A usefule lemma: lifting preserves variables.

    lift-var : ∀ {n} (x : Fin n) → lift (var x) ≡ S₂.var x


-- Abstract variable typings.

module VarTyping {t ℓ} {Type : Pred ℕ t}
                 (_⊢_wf : Wf Type Type (t ⊔ ℓ))
                 (typeExtension : Extension Type) where

  open ContextFormation _⊢_wf
  open WeakenOps        typeExtension

  infix 4 _⊢Var_∈_

  -- Abstract reflexive variable typings.

  data _⊢Var_∈_ {n} (Γ : Ctx Type n) : Fin n → Type n → Set (t ⊔ ℓ) where
    ∈-var : ∀ x → Γ wf → Γ ⊢Var x ∈ lookup Γ x

  -- Variable typing together with type formation forms
  -- a type assignment system.

-- Abstract typed variable substitutions (renamings).

record TypedVarSubst {t} (Type : Pred ℕ t) ℓ : Set (lsuc (t ⊔ ℓ)) where

  infix 4 _⊢_wf

  field
    _⊢_wf : Wf Type Type (t ⊔ ℓ)     -- Type formation judgment

    -- Generic application of renamings to raw types

    typeExtension      : Extension Type
    typeVarApplication : Application Type Fin

  open VarTyping {t} {t ⊔ ℓ} _⊢_wf typeExtension public

  open WeakenOps        typeExtension      using (weaken; toVec)
  open Application      typeVarApplication using (_/_)
  open ContextFormation _⊢_wf              using (_wf; _∷_)
  open VarSubst                            using (id; wk; _⊙_)

  field

    -- Context validity of type formation.

    wf-wf : ∀ {n} {Γ : Ctx Type n} {a}   → Γ ⊢ a wf  → Γ wf

    -- Lemmas about renamings in types

    /-wk        : ∀ {n} {a : Type n} → a / wk ≡ weaken a
    id-vanishes : ∀ {n} (a : Type n) → a / id ≡ a
    /-⊙         : ∀ {m n k} {ρ₁ : Sub Fin m n} {ρ₂ : Sub Fin n k} a →
                  a / ρ₁ ⊙ ρ₂ ≡ a / ρ₁ / ρ₂

  -- Typed renamings and associated lemmas.

  typedRenaming : TypedSub Type Fin (t ⊔ ℓ)
  typedRenaming = record
    { _⊢_wf               = _⊢_wf
    ; _⊢_∈_               = _⊢Var_∈_
    ; typeExtension       = typeExtension
    ; typeTermApplication = typeVarApplication
    ; termSimple          = VarSubst.simple
    }

  appLemmas : AppLemmas Type Fin
  appLemmas = record
    { application = typeVarApplication
    ; lemmas₄     = VarLemmas.lemmas₄
    ; id-vanishes = id-vanishes
    ; /-⊙         = /-⊙
    }

  weakenLemmas : WeakenLemmas Type Fin
  weakenLemmas = record
    { appLemmas = appLemmas
    ; /-wk      = /-wk
    }

  open AppLemmas    appLemmas    using (/-weaken)
  open WeakenLemmas weakenLemmas using (weaken-/-∷)

  -- Simple typed renamings.

  typedSimple : TypedSimple typedRenaming
  typedSimple = record
    { typedWeakenOps = record
      { ∈-weaken     = ∈-weaken
      ; ∈-wf         = ∈-wf
      ; /-wk         = /-wk
      ; /-weaken     = /-weaken
      ; weaken-/-∷   = weaken-/-∷
      }
    ; ∈-var          = ∈-var
    ; wf-wf          = wf-wf
    ; id-vanishes    = id-vanishes
    }
    where

    ∈-weaken : ∀ {n} {Γ : Ctx Type n} {x a b} →
               Γ ⊢ a wf → Γ ⊢Var x ∈ b →
               a ∷ Γ ⊢Var suc x ∈ weaken b
    ∈-weaken {_} {Γ} a-wf (∈-var x Γ-wf) =
      subst (_ ∷ Γ ⊢Var _ ∈_) (lookup-map x weaken (toVec Γ))
            (∈-var (suc x) (a-wf ∷ Γ-wf))

    ∈-wf : ∀ {n} {Γ : Ctx Type n} {x a} → Γ ⊢Var x ∈ a → Γ wf
    ∈-wf (∈-var x Γ-wf) = Γ-wf

  open TypedSub typedRenaming public
    renaming (_⊢/_∈_ to _⊢/Var_∈_) hiding (_⊢_wf)
  open TypedSimple typedSimple public hiding (∈-var; wf-wf; /-wk; id-vanishes)

  -- Applications of typed renamings to typed variables

  typedApplication : TypedApplication typedRenaming
  typedApplication = record
    { termTermApplication = VarSubst.application
    ; ∈-/ = ∈-/
    ; /-⊙ = /-⊙
    }
    where

    ∈-/ : ∀ {m n Δ} {ρ : Sub Fin m n} {Γ x a} →
          Γ ⊢Var x ∈ a → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Var Vec.lookup ρ x ∈ a / ρ
    ∈-/ (∈-var x Γ-wf) ρ∈Γ = lookup ρ∈Γ x

  open TypedApplication typedApplication public using (∈-/; ∈-⊙)

-- Abstract typed term substitutions.

record TypedTermSubst {t h} (Type : Pred ℕ t) (Term : Pred ℕ lzero) ℓ
                      (Helpers : ∀ {T} → Lift T Term → Set h)
                      : Set (lsuc (t ⊔ ℓ) ⊔ h) where

  infix 4 _⊢_∈_ _⊢_wf

  field
    _⊢_wf : Wf Type Type (t ⊔ ℓ)            -- Type formation judgment
    _⊢_∈_ : Typing Type Term Type (t ⊔ ℓ)   -- Typing judgment

    -- Lemmas about term substitutions in Types

    termLikeLemmas : TermLikeLemmas Type Term

  private
    module Tp = TermLikeLemmas termLikeLemmas
    module Tm = TermLemmas Tp.termLemmas
    module S  = TermSubst Tm.termSubst

  typeExtension : Extension Type
  typeExtension = record { weaken = Tp.weaken }

  private module C = WeakenOps typeExtension

  typedSub : TypedSub Type Term (t ⊔ ℓ)
  typedSub = record
    { _⊢_wf               = _⊢_wf
    ; _⊢_∈_               = _⊢_∈_
    ; typeExtension       = typeExtension
    ; termSimple          = S.simple
    ; typeTermApplication = Tp.termApplication
    }

  open ContextFormation _⊢_wf using (_wf)

  field

    -- Custom helper lemmas used to implement application of typed
    -- substitutions

    varHelpers  : Helpers S.varLift   -- lemmas about renamings
    termHelpers : Helpers S.termLift  -- lemmas about substitutions

    -- Context validity of type formation and typing.

    wf-wf : ∀ {n} {Γ : Ctx Type n} {a}   → Γ ⊢ a wf  → Γ wf
    ∈-wf  : ∀ {n} {Γ : Ctx Type n} {t a} → Γ ⊢ t ∈ a → Γ wf

    -- Takes variables to well-typed Tms.

    ∈-var : ∀ {n} {Γ : Ctx Type n} →
            ∀ x → Γ wf → Γ ⊢ S.var x ∈ C.lookup Γ x

    -- Generic application of typed Term′ substitutions to typed Terms.

    typedApp : ∀ {Term′ : Pred ℕ lzero}
               (_⊢′_∈_ : Typing Type Term′ Type (t ⊔ ℓ))
               (liftTyped : LiftTyped Tp.termLikeSubst _⊢_wf _⊢′_∈_ _⊢_∈_) →
               let open LiftTyped liftTyped using (rawLift; _⊢/_∈_; _/_)
               in (helpers : Helpers rawLift) →
                  ∀ {m n Γ Δ t a} {σ : Sub Term′ m n} →
                  Γ ⊢ t ∈ a → Δ ⊢/ σ ∈ Γ → Δ ⊢ S.app rawLift t σ ∈ a / σ

  typedVarSubst : TypedVarSubst Type (t ⊔ ℓ)
  typedVarSubst = record
    { _⊢_wf              = _⊢_wf
    ; typeVarApplication = Tp.varApplication
    ; typeExtension      = typeExtension
    ; wf-wf              = wf-wf
    ; /-wk               = refl
    ; id-vanishes        = id-vanishes
    ; /-⊙                = /-⊙
    }
    where
    open LiftSubLemmas Tp.varLiftSubLemmas using (liftAppLemmas)
    open LiftAppLemmas liftAppLemmas       using (id-vanishes; /-⊙)

  open TypedVarSubst typedVarSubst public
    using (_⊢Var_∈_; _⊢/Var_∈_; typedRenaming)
    renaming
    ( typedSimple    to varTypedSimple
    ; ∈-var          to Var∈-var
    ; ∈-↑            to Var∈-↑
    ; ∈-id           to Var∈-id
    ; ∈-wk           to Var∈-wk
    ; ∈-sub          to Var∈-sub
    ; ∈-tsub         to Var∈-tsub
    )

  varLiftTyped : LiftTyped Tp.termLikeSubst _⊢_wf _⊢Var_∈_ _⊢_∈_
  varLiftTyped = record
    { rawLift     = S.varLift
    ; typedSimple = varTypedSimple
    ; ∈-lift      = ∈-lift
    ; lift-var    = λ _ → refl
    }
    where

    ∈-lift : ∀ {n Γ x} {a : Type n} → Γ ⊢Var x ∈ a → Γ ⊢ S.var x ∈ a
    ∈-lift (Var∈-var x Γ-wf) = ∈-var x Γ-wf

  ∈-/Var : ∀ {m n} {Γ t a} {ρ : Sub Fin m n} {Δ} →
           Δ ⊢ t ∈ a → Γ ⊢/Var ρ ∈ Δ → Γ ⊢ t S./Var ρ ∈ a Tp./Var ρ
  ∈-/Var = typedApp _⊢Var_∈_ varLiftTyped varHelpers

  -- Operations on well-formed contexts that require weakening of
  -- well-formedness judgments.

  -- Simple typed substitutions.

  typedSimple : TypedSimple typedSub
  typedSimple = record
    { typedWeakenOps = record
      { ∈-weaken     = λ a-wf t∈b → ∈-/Var t∈b (Var∈-wk a-wf)
      ; ∈-wf         = ∈-wf
      ; /-wk         = Tp./-wk
      ; /-weaken     = Tp./-weaken
      ; weaken-/-∷   = Tp.weaken-/-∷
      }
    ; ∈-var          = ∈-var
    ; wf-wf          = wf-wf
    ; id-vanishes    = Tp.id-vanishes
    }

  termLiftTyped : LiftTyped Tp.termLikeSubst _⊢_wf _⊢_∈_ _⊢_∈_
  termLiftTyped = record
    { rawLift     = S.termLift
    ; typedSimple = typedSimple
    ; ∈-lift      = Fun.id
    ; lift-var    = λ _ → refl
    }

  -- Applications of typed term substitutions to typed terms

  typedApplication : TypedApplication typedSub
  typedApplication = record
    { termTermApplication = S.application
    ; ∈-/ = typedApp _⊢_∈_ termLiftTyped termHelpers
    ; /-⊙ = Tp./-⊙
    }

  open TypedSub typedSub public hiding (typeExtension)
  open TypedSimple typedSimple public hiding
    (∈-weaken; ∈-wf; ∈-var; wf-wf; /-wk; /-weaken; weaken-/-∷; id-vanishes)
  open TypedApplication typedApplication public hiding (/-⊙)
