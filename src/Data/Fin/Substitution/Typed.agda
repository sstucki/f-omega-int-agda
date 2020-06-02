------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Data.Fin.Substitution.Typed where

open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Context
open import Data.Fin.Substitution.Context.Properties
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Properties using (map-cong; map-id; map-∘; lookup-map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_; map; map⁺)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function as Fun using (_∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq hiding (trans)
open PropEq.≡-Reasoning


------------------------------------------------------------------------
-- Abstract well-typed substitutions (i.e. substitution lemmas)

-- Abstract term relations in a context.
--
-- An abtract term relation _⊢_∼_ : CtxTermRel Tp Tm₁ Tm₂ is a ternary
-- relation which, in a given Tp-context, relates Tm₁-terms to
-- Tm₂-terms.
CtxTermRel : (ℕ → Set) → (ℕ → Set) → (ℕ → Set) → Set₁
CtxTermRel Tp₁ Tm Tp₂ = ∀ {n} → Ctx Tp₁ n → Tm n → Tp₂ n → Set

module _ {Tp Tm₁ Tm₂ : ℕ → Set} where

  -- Term relations lifted pointwise to corresponding substitutions.
  --
  -- Given a relation R on Tm₁ and Tm₂ terms in a Tp context, the
  -- family of relations (LiftCtxTermRel R) relates Tm₁ and Tm₂
  -- substitutions pointwise.
  LiftCtxTermRel : ∀ {m} → CtxTermRel Tp Tm₁ Tm₂ →
                   CtxTermRel Tp (Sub Tm₁ m) (Sub Tm₂ m)
  LiftCtxTermRel P Γ σ₁ σ₂ = Pointwise (P Γ) σ₁ σ₂

  infix 4 _⊢_⟨_⟩_

  -- Syntactic sugar: and infix version of lifting.
  _⊢_⟨_⟩_ : ∀ {m n} → Ctx Tp n → Sub Tm₁ m n → CtxTermRel Tp Tm₁ Tm₂ →
            Sub Tm₂ m n → Set
  Γ ⊢ σ₁ ⟨ R ⟩ σ₂ = LiftCtxTermRel R Γ σ₁ σ₂

-- Abstract typings
--
-- An abtract typing relation _⊢_∈_ : Typing Tp₁ Tm Tp₂ is a ternary
-- relation which, in a given Tp₁-context, relates Tm-terms to their
-- Tp₂-types.
Typing = CtxTermRel

-- Abstract typed substitutions (aka context morphisms).
record TypedSub (Tp₁ Tm Tp₂ : ℕ → Set) : Set₁ where

  infix 4 _⊢_∈_ _⊢_wf

  field
    _⊢_∈_ : Typing Tp₂ Tm Tp₁   -- the associated typing
    _⊢_wf : Wf Tp₂              -- (target) Tp₂-well-formedness

    -- Application of Tm₂-substitutions to (source) Tp₁-types
    application : Application Tp₁ Tm

    -- Weakening of Tp₁-types.
    weakenOps : Extension Tp₁

  open Application       application       public using (_/_; _⊙_)
  open WellFormedContext _⊢_wf             public
  private module C = WeakenOps weakenOps

  infix  4 _⊢/_∈_
  infixr 4 _,_

  -- Typed substitutions.
  --
  -- A typed substitution Δ ⊢/ σ ∈ Γ is a substitution σ which, when
  -- applied to a well-typed term Γ ⊢ t ∈ a in a source context Γ,
  -- yield a well-typed term Δ ⊢ t / σ ∈ a / σ in a well-formed target
  -- context Δ.
  data _⊢/_∈_ {m n} (Δ : Ctx Tp₂ n) (σ : Sub Tm m n) (Γ : Ctx Tp₁ m) : Set where
     _,_ : (Δ ⊢ σ ⟨ _⊢_∈_ ⟩ C.toVec Γ ⊙ σ) → Δ wf → Δ ⊢/ σ ∈ Γ

  -- Look up an entry in a typed substitution.
  lookup : ∀ {m n} {Δ : Ctx Tp₂ n} {Γ : Ctx Tp₁ m} {σ}
           (x : Fin m) → Δ ⊢/ σ ∈ Γ → Δ ⊢ Vec.lookup σ x ∈ C.lookup x Γ / σ
  lookup {_} {_} {Δ} {Γ} x (σ⟨∈⟩Γ⊙σ , _) =
    subst (Δ ⊢ _ ∈_) (lookup-map x _ (C.toVec Γ)) (PW.lookup σ⟨∈⟩Γ⊙σ x)

  -- Context validity of typed substitutions.
  /∈-wf : ∀ {m n Δ Γ} {σ : Sub Tm m n} → Δ ⊢/ σ ∈ Γ → Δ wf
  /∈-wf (_ , Δ-wf) = Δ-wf


------------------------------------------------------------------------
-- Operations on abstract well-typed substitutions.

-- Extensions of abstract typed substitutions.

record RawTypedExtension {Tp₁ Tm₁ Tp₂ Tm₂}
                         (_⊢_wf : Wf Tp₂) (_⊢_∈_ : CtxTermRel Tp₂ Tm₁ Tp₁)
                         (application : Application Tp₁ Tm₂)
                         (weakenOps   : Extension Tp₁)
                         (extension₁  : Extension Tm₁)
                         (extension₂  : Extension Tm₂)
                         : Set where

  open WellFormedContext _⊢_wf
  open Application application
  private
    module E₁ = Extension extension₁
    module E₂ = Extension extension₂
    module C  = WeakenOps weakenOps

  field

    -- Weakens well-typed Tm-terms.
    ∈-weaken : ∀ {n} {Δ : Ctx Tp₂ n} {t a b} → Δ ⊢ a wf → Δ ⊢ t ∈ b →
               (a ∷ Δ) ⊢ E₁.weaken t ∈ C.weaken b

    -- Weakening commutes with substitutions.
    weaken-/ : ∀ {m n} {ρ : Sub Tm₂ m n} {t} a →
               C.weaken (a / ρ) ≡ C.weaken a / (t E₂./∷ ρ)

    -- Well-typedness implies well-formedness of contexts.
    ∈-wf : ∀ {n} {Δ : Ctx Tp₂ n} {t a} → Δ ⊢ t ∈ a → Δ wf

  -- A helper lemma.

  map-weaken-/ : ∀ {m n} (σ : Sub Tp₁ m m) (ρ : Sub Tm₂ m n) t →
                 Vec.map C.weaken (σ ⊙ ρ) ≡ Vec.map C.weaken σ ⊙ (t E₂./∷ ρ)
  map-weaken-/ σ ρ t = begin
      Vec.map C.weaken (σ ⊙ ρ)                  ≡⟨ sym (map-∘ C.weaken _ σ) ⟩
      Vec.map (C.weaken ∘ (_/ ρ)) σ             ≡⟨ map-cong weaken-/ σ ⟩
      Vec.map ((_/ (t E₂./∷ ρ)) ∘ C.weaken) σ   ≡⟨ map-∘ _ C.weaken σ ⟩
      Vec.map C.weaken σ ⊙ (t E₂./∷ ρ)          ∎

  -- Extension by a typed term.
  ∈-/∷ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {t u a b σ ρ} →
         (b ∷ Δ) ⊢ t ∈ C.weaken (a / ρ) → Δ ⊢ σ ⟨ _⊢_∈_ ⟩ C.toVec Γ ⊙ ρ →
         b ∷ Δ ⊢ t E₁./∷ σ ⟨ _⊢_∈_ ⟩ C.toVec (a ∷ Γ) ⊙ (u E₂./∷ ρ)
  ∈-/∷ t∈a/ρ σ⟨∈⟩Γ⊙ρ = σ⟨∈⟩Γ⊙ρ′
    where
      b∷Δ-wf   = ∈-wf t∈a/ρ
      b-wf     = wf-∷₁ b∷Δ-wf
      t∈a/ρ′   = subst (_⊢_∈_ _ _) (weaken-/ _) t∈a/ρ
      σ⟨∈⟩Γ⊙ρ′ =
        t∈a/ρ′ ∷ (subst ((LiftCtxTermRel _⊢_∈_) _ _) (map-weaken-/ _ _ _)
                        (map⁺ (∈-weaken b-wf) σ⟨∈⟩Γ⊙ρ))

record TypedExtension {Tp₁ Tm Tp₂}
                      (ext : Extension Tm)
                      (typedSub : TypedSub Tp₁ Tm Tp₂)
                      : Set where

  open TypedSub typedSub

  field rawTypedExtension : RawTypedExtension _⊢_wf _⊢_∈_ application
                                              weakenOps ext ext

  private module R = RawTypedExtension rawTypedExtension
  open R public hiding (∈-/∷)
  open Extension ext hiding (weaken)
  open WeakenOps weakenOps hiding (_/∷_)

  -- Extension by a typed term.
  ∈-/∷ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {t a b σ} →
         b ∷ Δ ⊢ t ∈ weaken (a / σ) → Δ ⊢/ σ ∈ Γ →
         b ∷ Δ ⊢/ (t /∷ σ) ∈ a ∷ Γ
  ∈-/∷ {Γ = Γ} t∈a/σ (σ⟨∈⟩Γ⊙σ , _) = R.∈-/∷ {Γ = Γ} t∈a/σ σ⟨∈⟩Γ⊙σ , ∈-wf t∈a/σ

-- Abstract typed simple substitutions.

record RawTypedSimple {Tp Tm₁ Tm₂}
                      (_⊢_wf : Wf Tp) (_⊢_∈_ : CtxTermRel Tp Tm₁ Tp)
                      (application : Application Tp Tm₂)
                      (weakenOps   : Extension Tp)
                      (simple₁ : Simple Tm₁) (simple₂ : Simple Tm₂)
                      : Set where

  open WellFormedContext _⊢_wf
  open Application application
  private
    module S₁ = SimpleExt simple₁
    module S₂ = SimpleExt simple₂
    module L₀ = Lemmas₀   (record { simple = simple₁ })
    module C  = WeakenOps weakenOps

    ext₁ : Extension Tm₁
    ext₁ = record { weaken = S₁.weaken }
    ext₂ : Extension Tm₂
    ext₂ = record { weaken = S₂.weaken }

  field
    rawTypedExtension : RawTypedExtension _⊢_wf _⊢_∈_ application
                                          weakenOps ext₁ ext₂

    -- Takes variables to well-typed Tms.
    ∈-var : ∀ {n} {Γ : Ctx Tp n} (x : Fin n) →
            Γ wf → Γ ⊢ S₁.var x ∈ C.lookup x Γ

    -- Types are invariant under the identity substitution.
    id-vanishes : ∀ {n} (a : Tp n) → a / S₂.id ≡ a

    -- Relates weakening of types to weakening of Tms.
    /-wk : ∀ {n} {a : Tp n} → a / S₂.wk ≡ C.weaken a

    -- Single-variable substitution is a left-inverse of weakening.
    wk-sub-vanishes : ∀ {n t} (a : Tp n) → a / S₂.wk / S₂.sub t ≡ a

    -- Well-formedness of types implies well-formedness of contexts.
    wf-wf : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → Γ wf

  open RawTypedExtension rawTypedExtension public

  -- Context operations that require Tm₂ substitutions in Tp-types.
  open SubstOps application simple₂ using (_E′/_)

  -- Some useful helper lemmas.

  ⊙-id : ∀ {m n} {ρ : Sub Tp m n} → ρ ⊙ S₂.id ≡ ρ
  ⊙-id {ρ = ρ} = begin
    Vec.map (_/ S₂.id) ρ  ≡⟨ map-cong id-vanishes ρ ⟩
    Vec.map Fun.id     ρ  ≡⟨ map-id ρ ⟩
    ρ                     ∎

  weaken-sub-vanishes : ∀ {n t} (a : Tp n) → C.weaken a / S₂.sub t ≡ a
  weaken-sub-vanishes {t = t} a = begin
    C.weaken a / S₂.sub t   ≡⟨ cong (flip _/_ _) (sym /-wk) ⟩
    a / S₂.wk / S₂.sub t    ≡⟨ wk-sub-vanishes a ⟩
    a                       ∎

  map-weaken-⊙-sub : ∀ {m n} {ρ : Sub Tp m n} {t} →
                     Vec.map C.weaken ρ ⊙ S₂.sub t ≡ ρ
  map-weaken-⊙-sub {ρ = ρ} {t} = begin
    Vec.map C.weaken ρ ⊙ S₂.sub t          ≡⟨ sym (map-∘ _ C.weaken ρ) ⟩
    Vec.map ((_/ S₂.sub t) ∘ C.weaken) ρ   ≡⟨ map-cong weaken-sub-vanishes ρ ⟩
    Vec.map Fun.id ρ                       ≡⟨ map-id ρ ⟩
    ρ                                  ∎

  -- Lifting.

  ∈-↑ : ∀ {m n} {Δ : Ctx Tp n} {Γ : Ctx Tp m} {a σ ρ} →
        Δ ⊢ a / ρ wf → Δ ⊢ σ ⟨ _⊢_∈_ ⟩ C.toVec Γ ⊙ ρ →
        a / ρ ∷ Δ ⊢ σ S₁.↑ ⟨ _⊢_∈_ ⟩ C.toVec (a ∷ Γ) ⊙ ρ S₂.↑
  ∈-↑ {Γ = Γ} a/ρ-wf σ⟨∈⟩Γ⊙ρ =
    ∈-/∷ {Γ = Γ} (∈-var zero (a/ρ-wf ∷ wf-wf a/ρ-wf)) σ⟨∈⟩Γ⊙ρ

  ∈-↑⋆ : ∀ {k m n} {E : CtxExt′ Tp m k} {Δ : Ctx Tp n} {Γ : Ctx Tp m}
         {σ ρ} → Δ ⊢ (E E′/ ρ) wfExt′ → Δ ⊢ σ ⟨ _⊢_∈_ ⟩ C.toVec Γ ⊙ ρ →
         (E E′/ ρ) ′++ Δ ⊢ σ S₁.↑⋆ k ⟨ _⊢_∈_ ⟩ C.toVec (E ′++ Γ) ⊙ ρ S₂.↑⋆ k
  ∈-↑⋆ {E = []}            []                        σ⟨∈⟩Γ⊙ρ = σ⟨∈⟩Γ⊙ρ
  ∈-↑⋆ {E = a ∷ E} {Δ} {Γ} (a/ρ↑⋆1+k-wf ∷ E/ρ-wfExt) σ⟨∈⟩Γ⊙ρ =
    ∈-↑ {Γ = E ′++ Γ} a/ρ↑⋆1+k-wf (∈-↑⋆ {E = E} E/ρ-wfExt σ⟨∈⟩Γ⊙ρ)

  -- The identity substitution.
  ∈-id : ∀ {n} {Γ : Ctx Tp n} → Γ wf → Γ ⊢ S₁.id ⟨ _⊢_∈_ ⟩ C.toVec Γ ⊙ S₂.id
  ∈-id             []            = []
  ∈-id {Γ = a ∷ Γ} (a-wf ∷ Γ-wf) =
    subst₂ (_⊢_⟨ _⊢_∈_ ⟩ C.toVec (a ∷ Γ) ⊙ S₂.id)
           (cong (flip _∷_ Γ) (id-vanishes a)) (L₀.id-↑⋆ 1)
           (∈-↑ {Γ = Γ} (subst (_⊢_wf Γ) (sym (id-vanishes a)) a-wf)
                (∈-id Γ-wf))

  private
    ∈-id′ : ∀ {n} {Γ : Ctx Tp n} → Γ wf → Γ ⊢ S₁.id ⟨ _⊢_∈_ ⟩ C.toVec Γ
    ∈-id′ Γ-wf = subst (_ ⊢ _ ⟨ _⊢_∈_ ⟩_) ⊙-id (∈-id Γ-wf)

  -- Weakening.
  ∈-wk : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf →
         a ∷ Γ ⊢ S₁.wk ⟨ _⊢_∈_ ⟩ C.toVec Γ ⊙ S₂.wk
  ∈-wk a-wf = map⁺ (weaken′ a-wf) (∈-id′ (wf-wf a-wf))
    where
      weaken′ : ∀ {n} {Γ : Ctx Tp n} {t a b} → Γ ⊢ a wf → Γ ⊢ t ∈ b →
                (a ∷ Γ) ⊢ S₁.weaken t ∈ (b / S₂.wk)
      weaken′ a-wf = subst (_⊢_∈_ _ _) (sym /-wk) ∘ ∈-weaken a-wf

  -- A substitution which only replaces the first variable.
  ∈-sub : ∀ {n} {Γ : Ctx Tp n} {t u a} →
          Γ ⊢ t ∈ a → Γ ⊢ S₁.sub t ⟨ _⊢_∈_ ⟩ C.toVec (a ∷ Γ) ⊙ S₂.sub u
  ∈-sub t∈a =
    t∈a′ ∷ subst₂ (_ ⊢_⟨ _⊢_∈_ ⟩_) (map-id _) (map-∘ (_/ S₂.sub _) C.weaken _)
                  (map⁺ (subst (_⊢_∈_ _ _) (sym (weaken-sub-vanishes _)))
                        (∈-id′ Γ-wf))
    where
      Γ-wf = ∈-wf t∈a
      t∈a′ = subst (_⊢_∈_ _ _) (sym (weaken-sub-vanishes _)) t∈a

  -- A substitution which only changes the type of the first variable.
  ∈-tsub : ∀ {n} {Γ : Ctx Tp n} {a b} → (b ∷ Γ) ⊢ S₁.var zero ∈ C.weaken a →
           b ∷ Γ ⊢ S₁.id ⟨ _⊢_∈_ ⟩ C.toVec (a ∷ Γ) ⊙ S₂.id
  ∈-tsub {Γ = Γ} z∈a = ∈-/∷ {Γ = Γ} z∈a′ (∈-id (wf-∷₂ (∈-wf z∈a)))
    where
      z∈a′ = subst (_⊢_∈_ _ _) (cong C.weaken (sym (id-vanishes _))) z∈a

record TypedSimple {Tp Tm}
                   (simple : Simple Tm)
                   (typedSub : TypedSub Tp Tm Tp)
                   : Set where

  open TypedSub typedSub

  field rawTypedSimple : RawTypedSimple _⊢_wf _⊢_∈_ application
                                        weakenOps simple simple

  private module R = RawTypedSimple rawTypedSimple
  open R public
    hiding (rawTypedExtension; ∈-/∷; ∈-↑; ∈-↑⋆; ∈-id; ∈-wk; ∈-sub; ∈-tsub)
  open Simple    simple             hiding (weaken)
  open WeakenOps weakenOps
  open SubstOps  application simple using (_E′/_)
  open WellFormedContextLemmas _⊢_wf

  typedExtension : TypedExtension _ _
  typedExtension = record { rawTypedExtension = R.rawTypedExtension }
  open TypedExtension typedExtension public using (∈-/∷)

  -- Lifting.

  ∈-↑ : ∀ {m n} {Δ : Ctx Tp n} {Γ : Ctx Tp m} {a σ} →
        Δ ⊢ a / σ wf → Δ ⊢/ σ ∈ Γ → a / σ ∷ Δ ⊢/ σ ↑ ∈ a ∷ Γ
  ∈-↑ {Γ = Γ} a/σ-wf (σ⟨∈⟩Γ⊙σ , Δ-wf) =
    R.∈-↑ {Γ = Γ} a/σ-wf σ⟨∈⟩Γ⊙σ , a/σ-wf ∷ wf-wf a/σ-wf

  ∈-↑⋆ : ∀ {k m n} {E : CtxExt′ Tp m k} {Δ : Ctx Tp n} {Γ : Ctx Tp m} {σ} →
         Δ ⊢ (E E′/ σ) wfExt′ → Δ ⊢/ σ ∈ Γ →
         (E E′/ σ) ′++ Δ ⊢/ σ ↑⋆ k ∈ E ′++ Γ
  ∈-↑⋆ {E = E} {Δ} {Γ} E/σ-wfExt (σ⟨∈⟩Γ⊙σ , Δ-wf) =
    R.∈-↑⋆ E/σ-wfExt σ⟨∈⟩Γ⊙σ , wf-++-wfExt E/σ-wfExt Δ-wf

  -- The identity substitution.
  ∈-id : ∀ {n} {Γ : Ctx Tp n} → Γ wf → Γ ⊢/ id ∈ Γ
  ∈-id Γ-wf = R.∈-id Γ-wf , Γ-wf

  -- Weakening.
  ∈-wk : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → a ∷ Γ ⊢/ wk ∈ Γ
  ∈-wk a-wf = R.∈-wk a-wf , a-wf ∷ wf-wf a-wf

  -- A substitution which only replaces the first variable.
  ∈-sub : ∀ {n} {Γ : Ctx Tp n} {t a} →
          Γ ⊢ t ∈ a → Γ ⊢/ sub t ∈ a ∷ Γ
  ∈-sub t∈a = R.∈-sub t∈a , ∈-wf t∈a

  -- A substitution which only replaces the m-th variable.
  ∈-sub-↑⋆ : ∀ {m n} {Δ : CtxExt′ Tp (suc n) m} {Γ : Ctx Tp n} {t a} →
             Γ ⊢ Δ E′/ sub t wfExt′ → Γ ⊢ t ∈ a →
             (Δ E′/ sub t) ′++ Γ ⊢/ sub t ↑⋆ m ∈ Δ ′++ a ∷ Γ
  ∈-sub-↑⋆ Δ-wfExt t∈a = ∈-↑⋆ Δ-wfExt (∈-sub t∈a)

  -- A substitution which only changes the type of the first variable.
  ∈-tsub : ∀ {n} {Γ : Ctx Tp n} {a b} → b ∷ Γ ⊢ var zero ∈ weaken a →
           b ∷ Γ ⊢/ id ∈ a ∷ Γ
  ∈-tsub z∈a = R.∈-tsub z∈a , ∈-wf z∈a

  -- Helper lemmas.

  id-↑⋆ : ∀ {n} k → id ↑⋆ k ≡ id {k + n}
  id-↑⋆ zero    = refl
  id-↑⋆ (suc k) = begin
    (id ↑⋆ k) ↑   ≡⟨ cong _↑ (id-↑⋆ k) ⟩
    id        ↑   ∎

  E′/-id-vanishes : ∀ {m n} (Δ : CtxExt′ Tp m n) → Δ E′/ id ≡ Δ
  E′/-id-vanishes             []      = refl
  E′/-id-vanishes {n = suc n} (a ∷ Δ) = cong₂ _∷_ (begin
    a / id ↑⋆ n   ≡⟨ cong (a /_) (id-↑⋆ n) ⟩
    a / id        ≡⟨ id-vanishes a ⟩
    a             ∎) (E′/-id-vanishes Δ)

  -- A substitution which only changes the type of the m-th variable.
  ∈-tsub-↑⋆ : ∀ {m n} {Δ : CtxExt′ Tp (suc n) m} {Γ : Ctx Tp n} {a b} →
              b ∷ Γ ⊢ Δ wfExt′ → b ∷ Γ ⊢ var zero ∈ weaken a →
              Δ ′++ b ∷ Γ ⊢/ id ∈ Δ ′++ a ∷ Γ
  ∈-tsub-↑⋆ {m} {n} {Δ} Δ-wfExt z∈a =
    subst₂ (_⊢/_∈ _) (cong (_′++ _) (E′/-id-vanishes Δ)) (id-↑⋆ m)
           (∈-↑⋆ {E = Δ} (subst (_ ⊢_wfExt′) (sym (E′/-id-vanishes Δ)) Δ-wfExt)
                 (∈-tsub z∈a))

-- TODO: applications of well-typed substitutions to well-typed terms.


------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Abstract typed liftings from Tm₁ to Tm₁′.
record LiftTyped {Tp Tm₁ Tm₂}
                 (l : Lift Tm₁ Tm₂)
                 (typedSub : TypedSub Tp Tm₁ Tp)
                 (_⊢₂_∈_   : Typing Tp Tm₂ Tp) : Set where

  open TypedSub typedSub renaming (_⊢_∈_ to _⊢₁_∈_)
  private module L = Lift l

  -- The underlying well-typed simple substitutions.
  field typedSimple : TypedSimple L.simple typedSub

  open TypedSimple typedSimple public

  -- Lifts well-typed Tm₁-terms to well-typed Tm₂-terms.
  field lift : ∀ {n} {Γ : Ctx Tp n} {t a} → Γ ⊢₁ t ∈ a → Γ ⊢₂ (L.lift t) ∈ a

-- Abstract variable typings.
module VarTyping {Tp} (weakenOps : Extension Tp) (_⊢_wf : Wf Tp) where
  open WeakenOps weakenOps
  open WellFormedContext _⊢_wf

  infix 4 _⊢Var_∈_

  -- Abstract reflexive variable typings.
  data _⊢Var_∈_ {n} (Γ : Ctx Tp n) : Fin n → Tp n → Set where
    var : ∀ x → Γ wf → Γ ⊢Var x ∈ lookup x Γ

-- Abstract typed variable substitutions (renamings).
record TypedVarSubst {Tp} (_⊢_wf : Wf Tp) : Set where
  field
    application : Application Tp Fin
    weakenOps   : Extension Tp

  open WellFormedContext   _⊢_wf
  open VarTyping weakenOps _⊢_wf public

  typedSub : TypedSub Tp Fin Tp
  typedSub = record
    { _⊢_∈_       = _⊢Var_∈_
    ; _⊢_wf       = _⊢_wf
    ; application = application
    ; weakenOps   = weakenOps
    }

  open TypedSub typedSub public using () renaming (_⊢/_∈_ to _⊢/Var_∈_)

  open Application application       using (_/_)
  open Lemmas₄     VarLemmas.lemmas₄ using (id; wk; _⊙_)
  private module C = WeakenOps weakenOps

  field
    /-wk        : ∀ {n} {a : Tp n} → a / wk ≡ C.weaken a
    id-vanishes : ∀ {n} (a : Tp n) → a / id ≡ a
    /-⊙         : ∀ {m n k} {σ₁ : Sub Fin m n} {σ₂ : Sub Fin n k} a →
                  a / σ₁ ⊙ σ₂ ≡ a / σ₁ / σ₂
    wf-wf       : ∀ {n} {Γ : Ctx Tp n} {a} → Γ ⊢ a wf → Γ wf

  appLemmas : AppLemmas Tp Fin
  appLemmas = record
    { application = application
    ; lemmas₄     = VarLemmas.lemmas₄
    ; id-vanishes = id-vanishes
    ; /-⊙         = /-⊙
    }

  open ExtAppLemmas appLemmas using (wk-commutes; wk-sub-vanishes)
  open SimpleExt VarLemmas.simple using (extension; _/∷_)

  -- Simple typed renamings.
  typedSimple : TypedSimple VarLemmas.simple typedSub
  typedSimple = record
    { rawTypedSimple = record
        { rawTypedExtension = record
            { ∈-weaken = ∈-weaken
            ; weaken-/ = weaken-/
            ; ∈-wf     = ∈-wf
            }
        ; ∈-var             = var
        ; id-vanishes       = id-vanishes
        ; /-wk              = /-wk
        ; wk-sub-vanishes   = wk-sub-vanishes
        ; wf-wf             = wf-wf
        }
    }
    where
      ∈-weaken : ∀ {n} {Γ : Ctx Tp n} {x a b} → Γ ⊢ a wf → Γ ⊢Var x ∈ b →
                 a ∷ Γ ⊢Var suc x ∈ C.weaken b
      ∈-weaken {_} {Γ} a-wf (var x Γ-wf) =
        subst (_ ∷ Γ ⊢Var _ ∈_) (lookup-map x C.weaken (C.toVec Γ))
              (var (suc x) (a-wf ∷ Γ-wf))

      weaken-/ : ∀ {m n} {σ : Sub Fin m n} {t} a →
                 C.weaken (a / σ) ≡ C.weaken a / (t /∷ σ)
      weaken-/ {σ = σ} {t} a = begin
        C.weaken (a / σ)        ≡⟨ sym /-wk ⟩
        a / σ / wk              ≡⟨ wk-commutes a ⟩
        a / wk / (t /∷ σ)       ≡⟨ cong₂ _/_ /-wk refl ⟩
        C.weaken a / (t /∷ σ)   ∎

      ∈-wf : ∀ {n} {Γ : Ctx Tp n} {x a} → Γ ⊢Var x ∈ a → Γ wf
      ∈-wf (var x Γ-wf) = Γ-wf

  open TypedSimple typedSimple public
    hiding (/-wk; id-vanishes; wk-sub-vanishes; wf-wf)
