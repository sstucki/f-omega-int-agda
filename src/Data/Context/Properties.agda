------------------------------------------------------------------------
-- Propierties of abstract typing contexts
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Context.Properties where

open import Data.Fin using (Fin; zero; suc; lift; raise)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as VecProps
open import Function as Fun using (_∘_; flip)
open import Relation.Binary.PropositionalEquality hiding (subst-∘)
open ≡-Reasoning
open import Relation.Unary using (Pred)

open import Data.Context
open import Data.Context.WellFormed


------------------------------------------------------------------------
-- Properties of abstract contexts and context extensions.

-- Properties of the `map' functions.

module _ {ℓ₁ ℓ₂} {T₁ : Pred ℕ ℓ₁} {T₂ : Pred ℕ ℓ₂} where

  -- pointwise equality is a congruence w.r.t. map and mapExt.

  map-cong : ∀ {n} {f g : ∀ {k} → T₁ k → T₂ k} → (∀ {k} → f {k} ≗ g {k}) →
             _≗_ {A = Ctx T₁ n} (map f) (map g)
  map-cong f≗g []        = refl
  map-cong f≗g (_∷_ t Γ) = cong₂ _∷_ (f≗g t) (map-cong f≗g Γ)

  mapExt-cong : ∀ {k m n} {f g : ∀ i → T₁ (i + m) → T₂ (i + n)} →
                (∀ {i} → f i ≗ g i) →
                _≗_ {A = CtxExt T₁ m k} (mapExt {T₂ = T₂} f) (mapExt g)
  mapExt-cong f≗g []            = refl
  mapExt-cong f≗g (_∷_ {l} t Γ) = cong₂ _∷_ (f≗g {l} t) (mapExt-cong f≗g Γ)

module _ {ℓ} {T : Pred ℕ ℓ} where

  -- map and mapExt are functorial.

  map-id : ∀ {n} → _≗_ {A = Ctx T n} (map Fun.id) Fun.id
  map-id []      = refl
  map-id (t ∷ Γ) = cong (t ∷_) (map-id Γ)

  mapExt-id : ∀ {m n} → _≗_ {A = CtxExt T m n} (mapExt λ _ t → t) Fun.id
  mapExt-id []      = refl
  mapExt-id (t ∷ Γ) = cong (t ∷_) (mapExt-id Γ)

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Pred ℕ ℓ₁} {T₂ : Pred ℕ ℓ₂} {T₃ : Pred ℕ ℓ₃} where

  map-∘ : ∀ {n} (f : ∀ {k} → T₂ k → T₃ k) (g : ∀ {k} → T₁ k → T₂ k)
          (Γ : Ctx T₁ n) → map {T₂ = T₃} (f ∘ g) Γ ≡ map {T₁ = T₂} f (map g Γ)
  map-∘ f g []      = refl
  map-∘ f g (t ∷ Γ) = cong (_ ∷_) (map-∘ f g Γ)

  mapExt-∘ : ∀ {k l m n}
             (f : ∀ i → T₂ (i + m) → T₃ (i + n))
             (g : ∀ i → T₁ (i + l) → T₂ (i + m)) →
             (Γ : CtxExt T₁ l k) →
             mapExt {T₂ = T₃} (λ i t → f i (g i t)) Γ ≡
               mapExt {T₁ = T₂} f (mapExt g Γ)
  mapExt-∘ f g []      = refl
  mapExt-∘ f g (t ∷ Γ) = cong (_ ∷_) (mapExt-∘ f g Γ)

-- Lemmas about operations on contexts that require weakening of
-- types.

module WeakenOpsLemmas {ℓ} {T : Pred ℕ ℓ} (extension : Extension T) where

  -- The underlyig operations.
  open WeakenOps extension

  -- Conversion to vector representation commutes with
  -- concatenation.

  toVec-++ : ∀ {m n} (Δ : CtxExt T m n) (Γ : Ctx T m) →
             toVec (Δ ++ Γ) ≡ extToVec Δ (toVec Γ)
  toVec-++ []      Γ = refl
  toVec-++ (t ∷ Δ) Γ =
    cong ((_ ∷_) ∘ Vec.map weaken) (toVec-++ Δ Γ)

  -- Lookup commutes with concatenation.

  lookup-++ : ∀ {m n} (Δ : CtxExt T m n) (Γ : Ctx T m) x →
              lookup (Δ ++ Γ) x ≡ extLookup Δ (toVec Γ) x
  lookup-++ Δ Γ x = cong (flip Vec.lookup x) (toVec-++ Δ Γ)

  -- We can skip the first element when looking up others.

  lookup-suc : ∀ {n} t (Γ : Ctx T n) x →
               lookup (t ∷ Γ) (suc x) ≡ weaken (lookup Γ x)
  lookup-suc t Γ x = VecProps.lookup-map x weaken (toVec Γ)

  extLookup-suc : ∀ {k m n} t (Γ : CtxExt T m n) (ts : Vec (T m) k) x →
                  extLookup (t ∷ Γ) ts (suc x) ≡ weaken (extLookup Γ ts x)
  extLookup-suc t Γ ts x = VecProps.lookup-map x weaken (extToVec Γ ts)

  -- We can skip a spliced-in element when looking up others.

  lookup-lift : ∀ {k m n} (Γ : CtxExt T m n) t (ts : Vec (T m) k) x →
                extLookup Γ ts x ≡ extLookup Γ (t ∷ ts) (lift n suc x)
  lookup-lift             []      t ts x       = refl
  lookup-lift             (u ∷ Δ) t ts zero    = refl
  lookup-lift {n = suc n} (u ∷ Δ) t ts (suc x) = begin
      extLookup (u ∷ Δ) ts (suc x)
    ≡⟨ extLookup-suc u Δ ts x ⟩
      weaken (extLookup Δ ts x)
    ≡⟨ cong weaken (lookup-lift Δ t ts x) ⟩
      weaken (extLookup Δ (t ∷ ts) (lift n suc x))
    ≡⟨ sym (extLookup-suc u Δ (t ∷ ts) (lift n suc x)) ⟩
      extLookup (u ∷ Δ) (t ∷ ts) (suc (lift n suc x))
    ∎

  -- Lookup in the prefix of a concatenation results in weakening.

  lookup-weaken⋆ : ∀ {m} n (Δ : CtxExt T m n) (Γ : Ctx T m) x →
                   lookup (Δ ++ Γ) (raise n x) ≡ weaken⋆ n (lookup Γ x)
  lookup-weaken⋆ zero    []      Γ x = refl
  lookup-weaken⋆ (suc n) (t ∷ Δ) Γ x = begin
      lookup (t ∷ Δ ++ Γ) (suc (raise n x))
    ≡⟨ VecProps.lookup-map (raise n x) weaken (toVec (Δ ++ Γ)) ⟩
      weaken (lookup (Δ ++ Γ) (raise n x))
    ≡⟨ cong weaken (lookup-weaken⋆ n Δ Γ x) ⟩
      weaken (weaken⋆ n (lookup Γ x))
    ∎

-- Lemmas relating conversions of context extensions to vector
-- representation with conversions of the underling entries.

module ConversionLemmas {T₁ T₂ : ℕ → Set}
                        (extension₁ : Extension T₁)
                        (extension₂ : Extension T₂) where
  private
    module W₁ = WeakenOps extension₁
    module W₂ = WeakenOps extension₂

  toVec-map : ∀ {n} (f : ∀ {k} → T₁ k → T₂ k) (Γ : Ctx T₁ n) →
              (∀ {k} (t : T₁ k) → W₂.weaken (f t) ≡ f (W₁.weaken t)) →
              W₂.toVec (map f Γ) ≡ Vec.map f (W₁.toVec Γ)
  toVec-map f []        _   = refl
  toVec-map f (_∷_ t Γ) hyp = cong₂ _∷_ (hyp t) (begin
      Vec.map W₂.weaken (W₂.toVec (map f Γ))
    ≡⟨ cong (Vec.map W₂.weaken) (toVec-map f Γ hyp) ⟩
      (Vec.map W₂.weaken (Vec.map f (W₁.toVec Γ)))
    ≡⟨ sym (VecProps.map-∘ W₂.weaken f (W₁.toVec Γ)) ⟩
      (Vec.map (W₂.weaken ∘ f) (W₁.toVec Γ))
    ≡⟨ VecProps.map-cong hyp (W₁.toVec Γ) ⟩
      (Vec.map (f ∘ W₁.weaken) (W₁.toVec Γ))
    ≡⟨ VecProps.map-∘ f W₁.weaken (W₁.toVec Γ) ⟩
      (Vec.map f (Vec.map W₁.weaken (W₁.toVec Γ)))
    ∎)

  -- Lookup commutes with re-indexing, provided that the reindexing
  -- function commutes with weakening.

  lookup-map : ∀ {n} (f : ∀ {k} → T₁ k → T₂ k) (Γ : Ctx T₁ n) x →
               (∀ {k} (t : T₁ k) → W₂.weaken (f t) ≡ f (W₁.weaken t)) →
               W₂.lookup (map f Γ) x ≡ f (W₁.lookup Γ x)
  lookup-map f Γ x hyp = begin
      W₂.lookup (map f Γ) x
    ≡⟨ cong (flip Vec.lookup x) (toVec-map f Γ hyp) ⟩
      Vec.lookup (Vec.map f (W₁.toVec Γ)) x
    ≡⟨ VecProps.lookup-map x f (W₁.toVec Γ) ⟩
      f (W₁.lookup Γ x)
    ∎

-- Lemmas about well-formed contexts and context extensions.

module ContextFormationLemmas {t ℓ} {T : Pred ℕ t}
                              (_⊢_wf : Wf T T ℓ) where
  open ContextFormation _⊢_wf

  -- Concatenation preserves well-formedness of contexts.

  wf-++-wfExt : ∀ {m n} {Δ : CtxExt T m n} {Γ : Ctx T m} →
                Γ ⊢ Δ wfExt → Γ wf → Δ ++ Γ wf
  wf-++-wfExt []               Γ-wf = Γ-wf
  wf-++-wfExt (t-wf ∷ Δ-wfExt) Γ-wf = t-wf ∷ wf-++-wfExt Δ-wfExt Γ-wf

  -- Splitting of well-formed contexts.
  wf-split : ∀ {m n} {Δ : CtxExt T m n} {Γ : Ctx T m} →
             Δ ++ Γ wf → Γ ⊢ Δ wfExt × Γ wf
  wf-split {Δ = []}    Γ-wf             = [] , Γ-wf
  wf-split {Δ = t ∷ Δ} (t-wf ∷ Δ++Γ-wf) =
    let Δ-wfExt , Γ-wf = wf-split Δ++Γ-wf
    in t-wf ∷ Δ-wfExt , Γ-wf
