------------------------------------------------------------------------
-- Well-typed binary relations lifted to substitutions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Fin.Substitution.TypedRelation where

open import Data.Context hiding (map)
open import Data.Context.WellFormed
open import Data.Fin using (Fin; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.Extra
open import Data.Fin.Substitution.Typed
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Vec as Vec using (_∷_; map; zip; unzip)
open import Data.Vec.Properties
open import Function using (flip)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Unary using (Pred)


------------------------------------------------------------------------
-- Abstract typed binary relations lifted point-wise to substitutions

-- A shorthand.

infixr 2 _⊗_

_⊗_ : ∀ {t₁ t₂ } → Pred ℕ t₁ → Pred ℕ t₂ → Pred ℕ (t₁ ⊔ t₂)
(T₁ ⊗ T₂) n = T₁ n × T₂ n

-- Abstract typed binary relations on terms.
--
-- An abtract typed term relation _⊢_∼_∈_ : TypedRel Bnd Term₁ Term₂
-- Type is a four-place relation which, in a given Bnd-context,
-- relates Term₁ to Term₂-terms and their Type-types.

-- An abtract typing judgment _⊢_∈_ : Typing Bnd Term Type is a
-- ternary relation which, in a given Bnd-context, relates Term-terms
-- to their Type-types.

TypedRel : ∀ {t₁ t₂ t₃ t₄} →
         Pred ℕ t₁ → Pred ℕ t₂ → Pred ℕ t₃ → Pred ℕ t₄ → ∀ ℓ →
         Set (t₁ ⊔ t₂ ⊔ t₃ ⊔ t₄ ⊔ lsuc ℓ)
TypedRel Bnd Term₁ Term₂ Type ℓ =
  ∀ {n} → Ctx Bnd n → Term₁ n → Term₂ n → Type n → Set ℓ

module _ {t₁ t₂ t₃ t₄ ℓ} {Bnd : Pred ℕ t₁}
         {Term₁ : Pred ℕ t₂} {Term₂ : Pred ℕ t₃} {Type : Pred ℕ t₄} where

  -- The following maps witness the obvious correspondence between typed
  -- relations on Term₁ and Term₂ terms and typings of Term₁-Term₂ pairs.

  toTyping : TypedRel Bnd Term₁ Term₂ Type ℓ →
             Typing Bnd (Term₁ ⊗ Term₂) Type ℓ
  toTyping _⊢_∼_∈_ Γ = Prod.uncurry (_⊢_∼_∈_ Γ)

  fromTyping : Typing Bnd (Term₁ ⊗ Term₂) Type ℓ →
               TypedRel Bnd Term₁ Term₂ Type ℓ
  fromTyping _⊢_∈_ Γ = Prod.curry (_⊢_∈_ Γ)

record TypedRelation {t}
                     (Type : Pred ℕ t)      -- Type syntax
                     (Term : Pred ℕ lzero)  -- Term syntax
                     ℓ
                     : Set (lsuc (t ⊔ ℓ)) where

  infix 4 _⊢_∼_∈_ _⊢_wf

  field
    _⊢_wf   : Wf Type Type ℓ                   -- Type formation judgment
    _⊢_∼_∈_ : TypedRel Type Term Term Type ℓ   -- Typed relation judgment


------------------------------------------------------------------------
-- Abstract typed term relations lifted point-wise to substitutions

record TypedSubRel {t}
                   (Type : Pred ℕ t)      -- Type syntax
                   (Term : Pred ℕ lzero)  -- Term syntax
                   ℓ
                   : Set (lsuc (t ⊔ ℓ)) where

  -- The underlying typed relation

  field typedRelation : TypedRelation Type Term ℓ

  open TypedRelation typedRelation public

  -- Weakening and term substitutions in types.

  field
    typeExtension       : Extension Type                  -- type weakening
    typeTermApplication : Application Type (Term ⊗ Term)  -- term subst. app.
    termSimple          : Simple Term                     -- simple term subst.

  open ContextFormation _⊢_wf          using (_wf)
  open Application typeTermApplication using (_/_)

  -- We associate with every typed relation _⊢_∼_∈_ lifted to a pair
  -- of Term-substitutions a single typed substitution of pairs of
  -- Term-terms.

  termPairSimple : Simple (Term ⊗ Term)
  termPairSimple = record
    { var    = Prod.< var , var >
    ; weaken = Prod.map weaken weaken
    }
    where open Simple termSimple

  typedSub : TypedSub Type (Term ⊗ Term) ℓ
  typedSub = record
    { _⊢_wf               = _⊢_wf
    ; _⊢_∈_               = toTyping _⊢_∼_∈_
    ; typeExtension       = typeExtension
    ; typeTermApplication = typeTermApplication
    ; termSimple          = termPairSimple
    }

  open TypedSub typedSub using (_⊢_∈_; _⊢/_∈_; /∈-wf) public

  infix  4 _⊢/_∼_∈_

  -- Typed relations lifted to substitutions.
  --
  -- A typed substitution relation Δ ⊢/ σ ∼ ρ ∈ Γ is a pair σ, ρ of
  -- substitutions which, when applied to related terms Γ ⊢ s ∼ t ∈ a
  -- in a source context Γ, yield related well-typed terms Δ ⊢ s / σ ∼
  -- t / ρ ∈ a / zip σ ρ in a well-formed target context Δ.

  _⊢/_∼_∈_ : ∀ {m n} →
             Ctx Type n → Sub Term m n → Sub Term m n → Ctx Type m →
             Set (t ⊔ ℓ)
  Δ ⊢/ σ ∼ ρ ∈ Γ = Δ ⊢/ zip σ ρ ∈ Γ

------------------------------------------------------------------------
-- Operations on abstract well-typed substitutions

-- Helpers functions for relating extensions of (untyped) zipped
-- substitutions to their projections.

module ZipUnzipExtension {Tm₁ Tm₂ : ℕ → Set}
                         (ext₁ : Extension Tm₁)
                         (ext₂ : Extension Tm₂)
                         where

  private
    module E₁ = Extension ext₁
    module E₂ = Extension ext₂

  -- Extensions of (untyped) Tm⊗Tm substitutions.
  zippedExtension : Extension (Tm₁ ⊗ Tm₂)
  zippedExtension = record { weaken = Prod.map E₁.weaken E₂.weaken }
  open Extension zippedExtension

  -- Some useful shorthands

  π₁ : ∀ {n m} → Sub (Tm₁ ⊗ Tm₂) m n → Sub Tm₁ m n
  π₁ σ = Prod.proj₁ (unzip σ)

  π₂ : ∀ {n m} → Sub (Tm₁ ⊗ Tm₂) m n → Sub Tm₂ m n
  π₂ σ = Prod.proj₂ (unzip σ)

  -- π₁ and π₂ are projections (w.r.t. zipping)

  π₁-zip : ∀ {n m} (σ : Sub Tm₁ m n) (τ : Sub Tm₂ m n) → π₁ (zip σ τ) ≡ σ
  π₁-zip σ τ = cong Prod.proj₁ (unzip∘zip σ τ)

  π₂-zip : ∀ {n m} (σ : Sub Tm₁ m n) (τ : Sub Tm₂ m n) → π₂ (zip σ τ) ≡ τ
  π₂-zip σ τ = cong Prod.proj₂ (unzip∘zip σ τ)

  -- Weakening commutes with zipping and unzipping.

  map-weaken-zip : ∀ {m n} (σ : Sub Tm₁ m n) τ →
                   Vec.map weaken (zip σ τ) ≡
                     zip (Vec.map E₁.weaken σ) (Vec.map E₂.weaken τ)
  map-weaken-zip σ τ = map-zip E₁.weaken E₂.weaken σ τ

  map-weaken-unzip : ∀ {m n} (στ : Sub (Tm₁ ⊗ Tm₂) m n) →
                     (Vec.map E₁.weaken (π₁ στ) , Vec.map E₂.weaken (π₂ στ)) ≡
                       unzip (Vec.map weaken στ)
  map-weaken-unzip στ = map-unzip E₁.weaken E₂.weaken στ

  -- Extension commutes with zipping and unzipping.

  /∷-zip : ∀ {m n s t} (σ : Sub Tm₁ m n) τ →
           (s , t) /∷ zip σ τ ≡ zip (s E₁./∷ σ) (t E₂./∷ τ)
  /∷-zip σ τ = cong (_∷_ _) (map-weaken-zip σ τ)

  /∷-unzip : ∀ {m n s t} (στ : Sub (Tm₁ ⊗ Tm₂) m n) →
             (s E₁./∷ π₁ στ , t E₂./∷ π₂ στ) ≡ unzip ((s , t) /∷ στ)
  /∷-unzip στ = cong (Prod.map (_∷_ _) (_∷_ _)) (map-weaken-unzip στ)

-- Operations on related abstract typed substitutions that require
-- weakening of derivations of the typed relation

record TypedRelWeakenOps {t ℓ} {Type : Pred ℕ t} {Term : Pred ℕ lzero}
                         (typedSubRel : TypedSubRel Type Term ℓ)
                         : Set (lsuc (t ⊔ ℓ)) where

  open TypedSubRel      typedSubRel
  open ContextFormation _⊢_wf               using (_wf)
  open Application      typeTermApplication using (_/_)

  -- Operations on contexts and raw terms that require weakening

  private
    termExtension : Extension Term
    termExtension = record { weaken = Simple.weaken termSimple }

    module E = Extension termExtension
    module C = WeakenOps typeExtension
    module P = Simple    termPairSimple

  field

    -- Weakening preserves well-typed terms.

    ∼∈-weaken : ∀ {n} {Δ : Ctx Type n} {t u a b} →
                Δ ⊢ a wf → Δ ⊢ t ∼ u ∈ b →
                (a ∷ Δ) ⊢ E.weaken t ∼ E.weaken u ∈ C.weaken b

    -- Well-typedness implies well-formedness of contexts.

    ∼∈-wf : ∀ {n} {Δ : Ctx Type n} {t u a} → Δ ⊢ t ∼ u ∈ a → Δ wf

    -- Lemmas relating type weakening to term substitutions

    /-wk : ∀ {n} {a : Type n} → a / P.wk ≡ C.weaken a

    /-weaken : ∀ {m n} {στ : Sub (Term ⊗ Term) m n} a →
               a / Vec.map P.weaken στ ≡ a / στ / P.wk

    weaken-/-∷ : ∀ {n m} {tu} {στ : Sub (Term ⊗ Term) m n} (a : Type m) →
                 C.weaken a / (tu ∷ στ) ≡ a / στ

  -- Operations on the underlying abstract typed substitutions that
  -- require weakening.

  typedWeakenOps : TypedWeakenOps typedSub
  typedWeakenOps = record
    { ∈-weaken   = ∼∈-weaken
    ; ∈-wf       = ∼∈-wf
    ; /-wk       = /-wk
    ; /-weaken   = /-weaken
    ; weaken-/-∷ = weaken-/-∷
    }

  open TypedWeakenOps typedWeakenOps using (∈-/∷)
  open ZipUnzipExtension termExtension termExtension using (/∷-zip)

  -- Look up a pair of related entries in a pair of related
  -- substitutions.

  lookup : ∀ {m n Δ} {σ τ : Sub Term m n} {Γ} →
           Δ ⊢/ σ ∼ τ ∈ Γ → (x : Fin m) →
           Δ ⊢ Vec.lookup σ x ∼ Vec.lookup τ x ∈ C.lookup Γ x / zip σ τ
  lookup {σ = σ} {τ} σ∼τ∈Γ x =
    subst₂ (toTyping _⊢_∼_∈_ _) (lookup-zip x σ τ) refl
           (TypedWeakenOps.lookup typedWeakenOps σ∼τ∈Γ x)

  -- Extension by a pair of related typed terms.

  ∼∈-/∷ : ∀ {m n Γ} {σ τ : Sub Term m n} {Δ t u a b} →
          b ∷ Δ ⊢ t ∼ u ∈ C.weaken (a / zip σ τ) → Δ ⊢/ σ ∼ τ ∈ Γ →
          b ∷ Δ ⊢/ (t E./∷ σ) ∼ (u E./∷ τ) ∈ a ∷ Γ
  ∼∈-/∷ t∼u∈a/στ σ∼τ∈Γ =
    subst (flip (_⊢/_∈_ _) _) (/∷-zip _ _) (∈-/∷ t∼u∈a/στ σ∼τ∈Γ)

-- Helpers functions for relating simple (untyped) zipped
-- substitutions to their projections.

module ZipUnzipSimple {Tm₁ Tm₂ : ℕ → Set}
                      (simple₁ : Simple Tm₁)
                      (simple₂ : Simple Tm₂)
                      where

  private
    module S₁ = SimpleExt simple₁
    module S₂ = SimpleExt simple₂

  open ZipUnzipExtension S₁.extension S₂.extension public

  -- Simple (untyped) Tm⊗Tm substitutions.
  zippedSimple : Simple (Tm₁ ⊗ Tm₂)
  zippedSimple = record
    { weaken = Prod.map S₁.weaken S₂.weaken
    ; var    = λ x → S₁.var x , S₂.var x
    }
  open SimpleExt zippedSimple

  -- Lifting commutes with zipping.

  ↑-zip : ∀ {m n} (σ : Sub Tm₁ m n) τ →
          zip σ τ ↑ ≡ zip (σ S₁.↑) (τ S₂.↑)
  ↑-zip σ τ = /∷-zip σ τ

  ↑⋆-zip : ∀ {m n} (σ : Sub Tm₁ m n) τ k →
           zip σ τ ↑⋆ k ≡ zip (σ S₁.↑⋆ k) (τ S₂.↑⋆ k)
  ↑⋆-zip σ τ zero    = refl
  ↑⋆-zip σ τ (suc k) = cong (var zero ∷_) (begin
      map weaken (zip σ τ ↑⋆ k)
    ≡⟨ cong (map weaken) (↑⋆-zip σ τ k) ⟩  --
      map weaken (zip (σ S₁.↑⋆ k) (τ S₂.↑⋆ k))
    ≡⟨ map-weaken-zip (σ S₁.↑⋆ k) (τ S₂.↑⋆ k) ⟩
      zip (map S₁.weaken (σ S₁.↑⋆ k)) (map S₂.weaken (τ S₂.↑⋆ k))
    ∎)

  -- Lifting commutes with unzipping.
  ↑-unzip : ∀ {m n} (σ : Sub (Tm₁ ⊗ Tm₂) m n) →
            (π₁ σ S₁.↑ , π₂ σ S₂.↑) ≡ unzip (σ ↑)
  ↑-unzip σ = /∷-unzip σ

  -- Zipping preserves identity substitutions.
  id-zip : ∀ {n} → id {n} ≡ zip S₁.id S₂.id
  id-zip {zero}  = refl
  id-zip {suc n} = begin
    id {n} ↑                         ≡⟨ cong _↑ id-zip ⟩
    (zip S₁.id S₂.id) ↑              ≡⟨ ↑-zip S₁.id S₂.id ⟩
    zip (S₁.id S₁.↑) (S₂.id S₂.↑)    ∎

  -- Unzipping preserves identity substitutions.
  id-unzip : ∀ {n} → (S₁.id , S₂.id) ≡ unzip (id {n})
  id-unzip {zero}  = refl
  id-unzip {suc n} = begin
    (S₁.id S₁.↑ , S₂.id S₂.↑)   ≡⟨ cong (Prod.map S₁._↑ S₂._↑) id-unzip ⟩
    (π₁ id S₁.↑ , π₂ id S₂.↑)   ≡⟨ ↑-unzip id ⟩
    unzip (id {n} ↑)            ∎

  -- Zipping preserves weakening substitutions.
  wk-zip : ∀ {n} → wk {n} ≡ zip S₁.wk S₂.wk
  wk-zip {n} = begin
      map weaken id
    ≡⟨ cong (map weaken) id-zip ⟩
      map weaken (zip S₁.id S₂.id)
    ≡⟨ map-zip S₁.weaken S₂.weaken _ _ ⟩
      zip (map S₁.weaken S₁.id) (map S₂.weaken S₂.id)
    ∎

  -- Unzipping preserves weakening substitutions.
  wk-unzip : ∀ {n} → (S₁.wk , S₂.wk) ≡ unzip (wk {n})
  wk-unzip {n} = begin
      (map S₁.weaken S₁.id , map S₂.weaken S₂.id)
    ≡⟨ cong (Prod.map (map S₁.weaken) (map S₂.weaken)) id-unzip ⟩
      (map S₁.weaken (π₁ id) , map S₂.weaken (π₂ id))
    ≡⟨ map-unzip S₁.weaken S₂.weaken id ⟩
      unzip (map weaken id)
    ∎

  -- Zipping preserves sigle-variable substitutions.
  sub-zip : ∀ {n} (s : Tm₁ n) t → sub (s , t) ≡ zip (S₁.sub s) (S₂.sub t)
  sub-zip s t = cong (_∷_ (s , t)) id-zip

  -- Unzipping preserves sigle-variable substitutions.
  sub-unzip : ∀ {n} (s : Tm₁ n) t → (S₁.sub s , S₂.sub t) ≡ unzip (sub (s , t))
  sub-unzip s t = cong (Prod.map (_∷_ s) (_∷_ t)) id-unzip

-- Operations on abstract typed substitutions that require simple term
-- substitutions

record TypedRelSimple {t ℓ} {Type : Pred ℕ t} {Term : Pred ℕ lzero}
                      (typedSubRel : TypedSubRel Type Term ℓ)
                      : Set (lsuc (t ⊔ ℓ)) where

  -- Operations on related abstract typed substitutions that require
  -- weakening.

  field typedRelWeakenOps : TypedRelWeakenOps typedSubRel

  open TypedRelWeakenOps typedRelWeakenOps public
  open TypedSubRel       typedSubRel
  open ContextFormation  _⊢_wf               using (_wf; _⊢_wfExt)
  open Application       typeTermApplication using (_/_)

  private
    module S = Simple    termSimple
    module C = WeakenOps typeExtension
    module P = Simple    termPairSimple
  open S using (_↑; _↑⋆_; id; wk; sub)

  -- Context operations that require term substitutions in types.

  open SubstOps typeTermApplication termPairSimple using (_E/_)

  field

    -- Takes equal variables to well-typed related terms.

    ∼∈-var : ∀ {n} {Γ : Ctx Type n} →
             ∀ x → Γ wf → Γ ⊢ S.var x ∼ S.var x ∈ C.lookup Γ x

    -- Well-formedness of related types implies well-formedness of
    -- contexts.

    wf-wf : ∀ {n} {Γ : Ctx Type n} {a} → Γ ⊢ a wf → Γ wf

    -- The identity substitution in types is an identity

    id-vanishes : ∀ {n} (a : Type n) → a / P.id ≡ a

  -- Operations on the underlying abstract typed substitutions that
  -- require simple typed term substitutions.

  typedSimple : TypedSimple typedSub
  typedSimple = record
    { typedWeakenOps = typedWeakenOps
    ; ∈-var          = ∼∈-var
    ; wf-wf          = wf-wf
    ; id-vanishes    = id-vanishes
    }

  open TypedSimple typedSimple using (∈-↑; ∈-↑⋆; ∈-id; ∈-wk; ∈-sub; ∈-tsub)
  open ZipUnzipSimple termSimple termSimple

  -- Lifting.

  ∼∈-↑ : ∀ {m n Δ} {σ τ : Sub Term m n} {a Γ} →
         Δ ⊢ a / zip σ τ wf → Δ ⊢/ σ ∼ τ ∈ Γ →
         a / zip σ τ ∷ Δ ⊢/ σ ↑ ∼ τ ↑ ∈ a ∷ Γ
  ∼∈-↑ a/στ-wf σ∼τΓ =
    subst (flip (_⊢/_∈_ _) _) (↑-zip _ _) (∈-↑ a/στ-wf σ∼τΓ)

  ∼∈-↑⋆ : ∀ {k m n Δ} {E : CtxExt Type m k} {σ τ : Sub Term m n} {Γ} →
          Δ ⊢ (E E/ zip σ τ) wfExt → Δ ⊢/ σ ∼ τ ∈ Γ →
          (E E/ zip σ τ) ++ Δ ⊢/ σ ↑⋆ k ∼ τ ↑⋆ k ∈ (E ++ Γ)
  ∼∈-↑⋆ {k} E/στ-wfExt σ∼τ∈Γ =
    subst (flip (_⊢/_∈_ _) _) (↑⋆-zip _ _ k) (∈-↑⋆ E/στ-wfExt σ∼τ∈Γ)

  -- The identity substitution.

  ∼∈-id : ∀ {n} {Γ : Ctx Type n} → Γ wf → Γ ⊢/ id ∼ id ∈ Γ
  ∼∈-id Γ-wf = subst (flip (_⊢/_∈_ _) _) id-zip (∈-id Γ-wf)

  -- Weakening.

  ∼∈-wk : ∀ {n} {Γ : Ctx Type n} {a} → Γ ⊢ a wf → a ∷ Γ ⊢/ wk ∼ wk ∈ Γ
  ∼∈-wk a-wf = subst (flip (_⊢/_∈_ _) _) wk-zip (∈-wk a-wf)

  -- A substitution which only replaces the first variable.

  ∼∈-sub : ∀ {n} {Γ : Ctx Type n} {t u a} → Γ ⊢ t ∼ u ∈ a →
           Γ ⊢/ sub t ∼ sub u ∈ a ∷ Γ
  ∼∈-sub s∼t∈a =
    subst (flip (_⊢/_∈_ _) _) (sub-zip _ _) (∈-sub s∼t∈a)


  -- A substitution which only changes the type of the first variable.

  ∼∈-tsub : ∀ {n} {Γ : Ctx Type n} {a b} →
            b ∷ Γ ⊢ S.var zero ∼ S.var zero ∈ C.weaken a →
            b ∷ Γ ⊢/ id ∼ id ∈ a ∷ Γ
  ∼∈-tsub z∈a = subst (flip (_⊢/_∈_ _) _) id-zip (∈-tsub z∈a)
