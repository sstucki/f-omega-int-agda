------------------------------------------------------------------------
-- Well-typed binary relations lifted to substitutions
------------------------------------------------------------------------

module Data.Fin.Substitution.TypedRelation where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Context hiding (map)
open import Data.Fin.Substitution.Typed
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Vec as Vec using (_∷_; map; zip; unzip)
open import Data.Vec.Properties
open import Function using (flip; _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixr 2 _⊗_

------------------------------------------------------------------------
-- Abstract typed binary relations lifted point-wise to substitutions

-- A shorthand.
_⊗_ : (ℕ → Set) → (ℕ → Set) → ℕ → Set
(T₁ ⊗ T₂) n = T₁ n × T₂ n

-- Abstract typed binary relations on terms.
--
-- An abtract typed term relation _⊢_∼_∈_ : TypedRel Tp₁ Tm₁ Tm₂ Tp₂
-- is a four-place relation which, in a given Tp₁-context, relates Tm₁
-- to Tm₂-terms and their Tp₂-types.
TypedRel : (ℕ → Set) → (ℕ → Set) → (ℕ → Set) → (ℕ → Set) → Set₁
TypedRel Tp₁ Tm₁ Tm₂ Tp₂ = ∀ {n} → Ctx Tp₁ n → Tm₁ n → Tm₂ n → Tp₂ n → Set

-- The following maps witness the obvious correspondence between typed
-- relations on Tm₁ and Tm₂ terms and typings of Tm₁-Tm₂ pairs.

toTyping : ∀ {Tp₁ Tm₁ Tm₂ Tp₂} →
           TypedRel Tp₁ Tm₁ Tm₂ Tp₂ → Typing Tp₁ (Tm₁ ⊗ Tm₂) Tp₂
toTyping _⊢_∼_∈_ Γ = Prod.uncurry (_⊢_∼_∈_ Γ)

fromTyping : ∀ {Tp₁ Tm₁ Tm₂ Tp₂} →
             Typing Tp₁ (Tm₁ ⊗ Tm₂) Tp₂ → TypedRel Tp₁ Tm₁ Tm₂ Tp₂
fromTyping _⊢_∈_ Γ = Prod.curry (_⊢_∈_ Γ)

-- A handy helper.

subst₃ : ∀ {a b c p} {A : Set a} {B : Set b} {C : Set c}
         (P : A → B → C → Set p) {x₁ x₂ y₁ y₂ z₁ z₂} →
         x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
subst₃ P refl refl refl p = p

-- Abstract typed term relations lifted point-wise to substitutions
record TypedSubRel (Tp₁ Tm₁ Tm₂ Tp₂ : ℕ → Set) : Set₁ where

  infix 4 _⊢_∼_∈_ _⊢_wf

  field
    _⊢_∼_∈_ : TypedRel Tp₂ Tm₁ Tm₂ Tp₁   -- the associated typed relation
    _⊢_wf   : Wf Tp₂                     -- (traget) Tp₂-well-formedness

    -- Application of Tm₁⊗Tm₂-substitutions to (source) Tp₁-types
    application : Application Tp₁ (Tm₁ ⊗ Tm₂)

    -- Weakening of Tp₁-types.
    weakenOps : Extension Tp₁

  open WellFormedContext _⊢_wf public
  private module C = WeakenOps weakenOps

  -- We associate with every typed relation _⊢_∼_∈_ lifted to a pair
  -- of Tm₁- and Tm₂-substitutions a _⊢_∈_-typed (simple) substitution
  -- of pairs of Tm₁- and Tm₂-terms.
  typedSub : TypedSub Tp₁ (Tm₁ ⊗ Tm₂) Tp₂
  typedSub = record
    { _⊢_∈_       = toTyping _⊢_∼_∈_
    ; _⊢_wf       = _⊢_wf
    ; application = application
    ; weakenOps   = weakenOps
    }

  open TypedSub typedSub using (_⊢_∈_; _⊢/_∈_; _/_; _⊙_; _,_) public

  infix  4 _⊢/_∼_∈_

  -- Typed relations lifted to substitutions.
  --
  -- A typed substitution relation Δ ⊢/ σ ∼ ρ ∈ Γ is a pair σ, ρ of
  -- substitutions which, when applied to related terms Γ ⊢ s ∼ t ∈ a
  -- in a source context Γ, yield related well-typed terms Δ ⊢ s / σ ∼
  -- t / ρ ∈ a / zip σ ρ in a well-formed target context Δ.
  _⊢/_∼_∈_ : ∀ {m n} → Ctx Tp₂ n → Sub Tm₁ m n → Sub Tm₂ m n → Ctx Tp₁ m → Set
  Δ ⊢/ σ ∼ ρ ∈ Γ = Δ ⊢/ zip σ ρ ∈ Γ

  -- Look up a pair of related entries in a pair of related
  -- substitutions.
  lookup : ∀ {m n} {Δ : Ctx Tp₂ n} {Γ : Ctx Tp₁ m} (x : Fin m) {σ ρ} →
           Δ ⊢/ σ ∼ ρ ∈ Γ →
           Δ ⊢ Vec.lookup σ x ∼ Vec.lookup ρ x ∈ C.lookup x Γ / zip σ ρ
  lookup x {σ} {ρ} σ∼ρ∈Γ =
    subst₂ (toTyping _⊢_∼_∈_ _) (lookup-zip x σ ρ) refl
           (TypedSub.lookup typedSub x σ∼ρ∈Γ)


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

  π₁-zip : ∀ {n m} (σ : Sub Tm₁ m n) (ρ : Sub Tm₂ m n) → π₁ (zip σ ρ) ≡ σ
  π₁-zip σ ρ = cong Prod.proj₁ (unzip∘zip σ ρ)

  π₂-zip : ∀ {n m} (σ : Sub Tm₁ m n) (ρ : Sub Tm₂ m n) → π₂ (zip σ ρ) ≡ ρ
  π₂-zip σ ρ = cong Prod.proj₂ (unzip∘zip σ ρ)

  -- Extension commutes with zipping.
  /∷-zip : ∀ {m n s t} (σ : Sub Tm₁ m n) ρ →
           (s , t) /∷ zip σ ρ ≡ zip (s E₁./∷ σ) (t E₂./∷ ρ)
  /∷-zip σ ρ = cong (_∷_ _) (map-zip E₁.weaken E₂.weaken σ ρ)

  -- Extension commutes with unzipping.
  /∷-unzip : ∀ {m n s t} (σ : Sub (Tm₁ ⊗ Tm₂) m n) →
             (s E₁./∷ π₁ σ , t E₂./∷ π₂ σ) ≡ unzip ((s , t) /∷ σ)
  /∷-unzip σ = cong (Prod.map (_∷_ _) (_∷_ _)) (map-unzip _ _ σ)


-- Extensions of abstract typed relations lifted to substitutions.

record TypedRelExtension {Tp₁ Tm₁ Tm₂ Tp₂ : ℕ → Set}
                         (ext₁ : Extension Tm₁)
                         (ext₂ : Extension Tm₂)
                         (typedSubRel : TypedSubRel Tp₁ Tm₁ Tm₂ Tp₂)
                         : Set where

  open TypedSubRel typedSubRel
  private
    module E₁ = Extension ext₁
    module E₂ = Extension ext₂

  open ZipUnzipExtension ext₁ ext₂ renaming (zippedExtension to ext)

  field rawTypedExtension : RawTypedExtension _⊢_wf _⊢_∈_ application
                                              weakenOps ext ext

  -- Extension of the associated typed Tm₁⊗Tm₂-substitutions.
  typedExtension : TypedExtension ext typedSub
  typedExtension = record { rawTypedExtension = rawTypedExtension }

  private module TE = TypedExtension typedExtension
  open TE public hiding (rawTypedExtension; ∈-/∷) renaming
    ( ∈-weaken to ∼∈-weaken
    ; ∈-wf     to ∼∈-wf
    )
  open Extension ext hiding (weaken)
  open WeakenOps weakenOps

  -- Extension by typed related terms.
  ∼∈-/∷ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {s t a b σ ρ} →
          b ∷ Δ ⊢ s ∼ t ∈ weaken (a / zip σ ρ) → Δ ⊢/ σ ∼ ρ ∈ Γ →
          b ∷ Δ ⊢/ (s E₁./∷ σ) ∼ (t E₂./∷ ρ) ∈ a ∷ Γ
  ∼∈-/∷ s∼t∈a/σρ σ∼ρ∈Γ =
    subst (flip (_⊢/_∈_ _) _) (/∷-zip _ _) (TE.∈-/∷ s∼t∈a/σρ σ∼ρ∈Γ)


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
  ↑-zip : ∀ {m n} (σ : Sub Tm₁ m n) ρ →
          zip σ ρ ↑ ≡ zip (σ S₁.↑) (ρ S₂.↑)
  ↑-zip σ ρ = /∷-zip σ ρ

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


-- Abstract typed relations lifted to some simple substitutions.

record TypedRelSimple {Tp Tm₁ Tm₂ : ℕ → Set}
                      (simple₁ : Simple Tm₁)
                      (simple₂ : Simple Tm₂)
                      (typedSubRel : TypedSubRel Tp Tm₁ Tm₂ Tp)
                      : Set where

  open TypedSubRel typedSubRel
  private
    module S₁ = SimpleExt simple₁
    module S₂ = SimpleExt simple₂
    module L₀ = Lemmas₀   (record { simple = simple₁ })
    module C  = WeakenOps weakenOps

    -- Extension of the underlying substitutions.

    ext₁ : Extension Tm₁
    ext₁ = record { weaken = S₁.weaken }

    ext₂ : Extension Tm₂
    ext₂ = record { weaken = S₂.weaken }

  open ZipUnzipSimple simple₁ simple₂ renaming (zippedSimple to simple)

  field rawTypedSimple : RawTypedSimple _⊢_wf _⊢_∈_ application
                                        weakenOps simple simple

  -- The associated simple typed Tm₁⊗Tm₂-substitutions.
  typedSimple : TypedSimple simple typedSub
  typedSimple = record { rawTypedSimple = rawTypedSimple }

  private module TS = TypedSimple typedSimple
  open TS public hiding (rawTypedSimple; ∈-/∷; ∈-↑; ∈-id; ∈-wk; ∈-sub; ∈-tsub)
    renaming
    ( ∈-weaken to ∼∈-weaken
    ; ∈-wf     to ∼∈-wf
    ; ∈-var    to ∼∈-var
    )
  open Simple simple

  typedRelExtension : TypedRelExtension ext₁ ext₂ typedSubRel
  typedRelExtension = record { rawTypedExtension = rawTypedExtension }
    where open RawTypedSimple TS.rawTypedSimple
  open TypedRelExtension typedRelExtension public using (∼∈-/∷)

  -- Lifting.
  ∼∈-↑ : ∀ {m n} {Δ : Ctx Tp n} {Γ : Ctx Tp m} {a σ ρ} →
         Δ ⊢ a / zip σ ρ wf → Δ ⊢/ σ ∼ ρ ∈ Γ →
         a / zip σ ρ ∷ Δ ⊢/ σ S₁.↑ ∼ ρ S₂.↑ ∈ a ∷ Γ
  ∼∈-↑ a/σρ-wf σ∼ρΓ =
    subst (flip (_⊢/_∈_ _) _) (↑-zip _ _) (TS.∈-↑ a/σρ-wf σ∼ρΓ)

  -- Identity substitutions in typed related terms.
  ∼∈-id  : ∀ {n} {Γ : Ctx Tp n} → Γ wf → Γ ⊢/ S₁.id ∼ S₂.id ∈ Γ
  ∼∈-id Γ-wf = subst (flip (_⊢/_∈_ _) _) id-zip (TS.∈-id Γ-wf)

  -- Weakening of typed related terms.
  ∼∈-wk : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → a ∷ Γ ⊢/ S₁.wk ∼ S₂.wk ∈ Γ
  ∼∈-wk a-wf = subst (flip (_⊢/_∈_ _) _) wk-zip (TS.∈-wk a-wf)

  -- Related substitutions which only replace the first variable.
  ∼∈-sub : ∀ {n} {Γ : Ctx Tp n} {s t a} → Γ ⊢ s ∼ t ∈ a →
           Γ ⊢/ S₁.sub s ∼ S₂.sub t ∈ a ∷ Γ
  ∼∈-sub s∼t∈a =
    subst (flip (_⊢/_∈_ _) _) (sub-zip _ _) (TS.∈-sub s∼t∈a)

  -- Related substitutions which only change the type of the first
  -- variable in the context.
  ∼∈-tsub : ∀ {n} {Γ : Ctx Tp n} {a b} →
            b ∷ Γ ⊢ S₁.var zero ∼ S₂.var zero ∈ C.weaken a →
            b ∷ Γ ⊢/ S₁.id ∼ S₂.id ∈ a ∷ Γ
  ∼∈-tsub z∈a = subst (flip (_⊢/_∈_ _) _) id-zip (TS.∈-tsub z∈a)


-- Abstract typed liftings from Tm₁/Tm₂ to Tm₁′/Tm₂′.

record LiftTypedRel {Tp Tm₁ Tm₂ Tm₁′ Tm₂′}
                    (l₁ : Lift Tm₁ Tm₁′)
                    (l₂ : Lift Tm₂ Tm₂′)
                    (typedSubRel : TypedSubRel Tp Tm₁ Tm₂ Tp)
                    (_⊢₂_∼_∈_ : TypedRel Tp Tm₁′ Tm₂′ Tp)
                    : Set where

  open TypedSubRel typedSubRel renaming (_⊢_∼_∈_ to _⊢₁_∼_∈_)
  private
    module L₁ = Lift l₁
    module L₂ = Lift l₂

  -- The underlying well-typed related simple Tm₁-Tm₂-substitutions.
  field
    typedRelSimple : TypedRelSimple L₁.simple L₂.simple typedSubRel

  open TypedRelSimple typedRelSimple public

  -- Lifts well-typed Tm₁-terms to well-typed Tm₂-terms.
  field lift : ∀ {n} {Γ : Ctx Tp n} {s t a} →
               Γ ⊢₁ s ∼ t ∈ a → Γ ⊢₂ (L₁.lift s) ∼ (L₂.lift t) ∈ a


-- Abstract typed variable equality.

module VarEquality {Tp} (weakenOps : Extension Tp) (_⊢_wf : Wf Tp) where
  open WeakenOps weakenOps
  open WellFormedContext _⊢_wf

  infix 4 _⊢Var_≡_∈_

  -- Abstract variable equality.
  data _⊢Var_≡_∈_ {n} (Γ : Ctx Tp n) : Fin n → Fin n → Tp n → Set where
    refl : ∀ x → Γ wf → Γ ⊢Var x ≡ x ∈ lookup x Γ


-- Helpers lemmas for relating (untyped) zipped substitutions to their
-- first projection.

record ProjLemmas (Tp Tm : ℕ → Set) : Set where

  field
    weakenOps   : Extension Tp
    appLemmas   : AppLemmas Tp Tm

  private
    module C = WeakenOps      weakenOps
    module L = ExtAppLemmas   appLemmas
    module H = ZipUnzipSimple L.simple L.simple
    module S = SimpleExt      H.zippedSimple
  open SimpleExt   L.simple
  open Application L.application
  open H public

  field
    /-wk : ∀ {n} {a : Tp n} → a / wk ≡ C.weaken a

  open Prod using (proj₁)

  -- Weakening commutes with unzipped substitution.
  weaken-/ : ∀ {m n} {σ : Sub (Tm ⊗ Tm) m n} {st} a →
             C.weaken (a / π₁ σ) ≡ C.weaken a / π₁ (st S./∷ σ)
  weaken-/ {σ = σ} {s , t} a = begin
      C.weaken (a / π₁ σ)
    ≡⟨ sym /-wk ⟩
      a / π₁ σ / wk
    ≡⟨ L.wk-commutes a ⟩
      a / wk / (s /∷ π₁ σ)
    ≡⟨ cong₂ _/_ /-wk refl ⟩
      C.weaken a / (s /∷ π₁ σ)
    ≡⟨ cong (_/_ (C.weaken a) ∘ proj₁) (H./∷-unzip {t = t} σ) ⟩
      C.weaken a / π₁ ((s , t) S./∷ σ)
    ∎

  id-vanishes : ∀ {n} (a : Tp n) → a / π₁ S.id ≡ a
  id-vanishes a = begin
    a / π₁ S.id   ≡⟨ cong (_/_ _ ∘ proj₁) (sym (H.id-unzip)) ⟩
    a / id        ≡⟨ L.id-vanishes a ⟩
    a             ∎

  /-proj₁-wk : ∀ {n} {a : Tp n} → a / π₁ S.wk ≡ C.weaken a
  /-proj₁-wk {a = a} = begin
    a / π₁ S.wk   ≡⟨ cong (_/_ _ ∘ proj₁) (sym H.wk-unzip) ⟩
    a / wk        ≡⟨ /-wk ⟩
    C.weaken a    ∎

  wk-sub-vanishes : ∀ {n} {xy} (a : Tp n) →
                    a / π₁ S.wk / π₁ (S.sub xy) ≡ a
  wk-sub-vanishes {xy = x , y} a = begin
      a / π₁ S.wk / π₁ (S.sub (x , y))
    ≡⟨ cong (_/_ (a / π₁ S.wk) ∘ proj₁) (sym (H.sub-unzip x y)) ⟩
      a / π₁ S.wk / sub x
    ≡⟨ cong (λ σ → a / proj₁ σ / sub x) (sym H.wk-unzip) ⟩
      a / wk / sub x
    ≡⟨ L.wk-sub-vanishes a ⟩
      a
    ∎

-- Abstract typed variable equality substitutions (renamings).

record TypedVarEqSubst {Tp} (_⊢_wf : Wf Tp) : Set where

  field
    application : Application Tp Fin
    weakenOps   : Extension Tp

  open WellFormedContext     _⊢_wf
  open VarEquality weakenOps _⊢_wf public
  open Application application     using (_/_)
  open VarLemmas                   using (simple; lemmas₄)
  open Lemmas₄     lemmas₄         using (_↑; id; wk; sub; _⊙_)
  open SimpleExt   simple          using (extension)
  private module C = WeakenOps weakenOps

  field
    /-wk        : ∀ {n} {a : Tp n} → a / wk ≡ C.weaken a
    id-vanishes : ∀ {n} (a : Tp n) → a / id ≡ a
    /-⊙         : ∀ {m n k} {σ₁ : Sub Fin m n} {σ₂ : Sub Fin n k} a →
                  a / σ₁ ⊙ σ₂ ≡ a / σ₁ / σ₂
    wf-wf       : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → Γ wf

  projLemmas : ProjLemmas Tp Fin
  projLemmas = record
    { weakenOps = weakenOps
    ; appLemmas = record
      { application = application
      ; lemmas₄     = lemmas₄
      ; id-vanishes = id-vanishes
      ; /-⊙         = /-⊙
      }
    ; /-wk      = /-wk
    }

  private module H = ProjLemmas projLemmas

  typedSubRel : TypedSubRel Tp Fin Fin Tp
  typedSubRel = record
    { _⊢_∼_∈_     = _⊢Var_≡_∈_
    ; _⊢_wf       = _⊢_wf
    ; application = record { _/_ = λ a σ → a / H.π₁ σ }
    ; weakenOps   = weakenOps
    }

  open TypedSubRel typedSubRel public
    using () renaming (_⊢/_∼_∈_ to _⊢/Var_≡_∈_)

  -- Extensions of renamings in related terms.
  typedRelExtension : TypedRelExtension extension extension typedSubRel
  typedRelExtension = record
    { rawTypedExtension = record
      { ∈-weaken = ≡∈-weaken
      ; weaken-/ = λ {_} {_} {ρ} {xy} a → H.weaken-/ {σ = ρ} {xy} a
      ; ∈-wf     = ≡∈-wf
      }
    }
    where
      ≡∈-weaken : ∀ {n} {Γ : Ctx Tp n} {x y a b} → Γ ⊢ a wf →
                  Γ ⊢Var x ≡ y ∈ b → a ∷ Γ ⊢Var suc x ≡ suc y ∈ C.weaken b
      ≡∈-weaken {_} {Γ} a-wf (refl x Γ-wf) =
        subst (_⊢Var_≡_∈_ _ _ _) (lookup-map x C.weaken (C.toVec Γ))
              (refl (suc x) (a-wf ∷ Γ-wf))

      ≡∈-wf : ∀ {n} {Γ : Ctx Tp n} {x y a} → Γ ⊢Var x ≡ y ∈ a → Γ wf
      ≡∈-wf (refl x Γ-wf) = Γ-wf

  open TypedRelExtension typedRelExtension using (rawTypedExtension)

  -- Typed simple renamings in related terms.
  typedRelSimple : TypedRelSimple simple simple typedSubRel
  typedRelSimple = record
    { rawTypedSimple = record
      { rawTypedExtension = rawTypedExtension
      ; ∈-var             = refl
      ; id-vanishes       = H.id-vanishes
      ; /-wk              = H./-proj₁-wk
      ; wk-sub-vanishes   = λ {_} {xy} a → H.wk-sub-vanishes {xy = xy} a
      ; wf-wf             = wf-wf
      }
    }

  open TypedRelSimple typedRelSimple public
    hiding (typedRelExtension; /-wk; id-vanishes; wk-sub-vanishes; wf-wf)
