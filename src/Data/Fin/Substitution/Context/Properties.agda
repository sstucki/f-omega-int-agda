------------------------------------------------------------------------
-- Propierties of abstract typing contexts
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

-- FIXME: some lemmas in this file use UIP (aka axiom K) so we cannot
-- use the --without-K option globally. This use of UIP should not be
-- necessary!

module Data.Fin.Substitution.Context.Properties where

open import Data.Fin using (Fin; zero; suc; lift; raise)
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as VecProp
open import Function as Fun using (_∘_; flip)
open import Relation.Binary.PropositionalEquality hiding (subst-∘)
open ≡-Reasoning

open import Data.Fin.Substitution.Context


------------------------------------------------------------------------
-- Properties of abstract contexts and context extensions.

-- Some reusable lemmas about subst.
--
-- FIXME: These currently use UIP, this should not be necessary!

subst-shift : ∀ {a} {A : Set a} (P Q : A → Set) {x y : A}
              {f g : A → A} (F : ∀ {z} → P (f z) → Q (g z))
              (b : x ≡ y) (p : f x ≡ f y) (q : g x ≡ g y) {a : P (f x)} →
              F (subst P p a) ≡ subst Q q (F a)
subst-shift P Q F refl refl refl = refl

subst-shift₂ : ∀ {a} {A : Set a} (P Q R : A → Set) {x y : A}
               {f g h : A → A} (F : ∀ {z} → P (f z) → Q (g z) → R (h z))
               (b : x ≡ y) (p : f x ≡ f y) (q : g x ≡ g y) (r : h x ≡ h y)
               {a : P (f x)} {b : Q (g x)} →
               F (subst P p a) (subst Q q b) ≡ subst R r (F a b)
subst-shift₂ P Q R F refl refl refl refl = refl

subst-∘ : ∀ {a} {A : Set a} (P : A → Set) {x y z : A} {a : P x}
          (p : x ≡ y) (q : y ≡ z) →
          subst P q (subst P p a) ≡ subst P (trans p q) a
subst-∘ P refl refl = refl

subst-id : ∀ {a} {A : Set a} (P : A → Set) {x : A} {a : P x}
           (p : x ≡ x) → subst P p a ≡ a
subst-id P refl = refl

-- The two representations of context extensions are isomorphic.

CtxExt⇒CtxExt′⇒CtxExt-id : ∀ {T m n} (Γ : CtxExt T m (n + m)) →
                           CtxExt′⇒CtxExt {l = n} (CtxExt⇒CtxExt′ Γ) ≡ Γ
CtxExt⇒CtxExt′⇒CtxExt-id {T} {m} {n} Γ =
  let l≡n     = length-idx′ {n = n} Γ
      l+m≡n+m = length-idx Γ
  in begin
    CtxExt′⇒CtxExt (CtxExt⇒CtxExt′ Γ)
  ≡⟨ subst-shift (CtxExt′ T m) (CtxExt T m) {f = λ n → n}
                 (CtxExt′⇒CtxExt {T} {m}) l≡n l≡n l+m≡n+m ⟩
    subst (CtxExt T m) l+m≡n+m (CtxExt′⇒CtxExt (CtxExt⇒CtxExt′-helper Γ))
  ≡⟨ cong (subst (CtxExt T m) l+m≡n+m) (helper Γ) ⟩
    subst (CtxExt T m) l+m≡n+m (subst (CtxExt T m) (sym l+m≡n+m) Γ)
  ≡⟨ subst-∘ (CtxExt T m) (sym l+m≡n+m) l+m≡n+m ⟩
    subst (CtxExt T m) (trans (sym l+m≡n+m) l+m≡n+m) Γ
  ≡⟨ subst-id (CtxExt T m) (trans (sym l+m≡n+m) l+m≡n+m) ⟩
    Γ
  ∎
  where
    open ConversionHelper

    helper : ∀ {T m n} (Γ : CtxExt T m n) →
             CtxExt′⇒CtxExt (CtxExt⇒CtxExt′-helper Γ) ≡
               subst (CtxExt T m) (sym (length-idx Γ)) Γ
    helper         []      = refl
    helper {T} {m} (t ∷ Γ) = let n≡l+m = sym (length-idx Γ) in begin
        subst T n≡l+m t ∷ CtxExt′⇒CtxExt (CtxExt⇒CtxExt′-helper Γ)
      ≡⟨ cong ((subst T n≡l+m t) ∷_) (helper Γ) ⟩
        subst T n≡l+m t ∷ subst (CtxExt T m) n≡l+m Γ
      ≡⟨ subst-shift₂ T (CtxExt T m) (CtxExt T m) {f = λ n → n} _∷_
                      n≡l+m n≡l+m n≡l+m (sym (length-idx (t ∷ Γ))) ⟩
        subst (CtxExt T m) (sym (length-idx (t ∷ Γ))) (t ∷ Γ)
      ∎

CtxExt′⇒CtxExt⇒CtxExt′-id : ∀ {T m n} (Γ′ : CtxExt′ T m n) →
                            CtxExt⇒CtxExt′ (CtxExt′⇒CtxExt Γ′) ≡ Γ′
CtxExt′⇒CtxExt⇒CtxExt′-id {T} {m} Γ′ =
  let Γ   = CtxExt′⇒CtxExt Γ′
      l≡n = length-idx′ Γ
  in begin
    CtxExt⇒CtxExt′ Γ
  ≡⟨ cong (subst (CtxExt′ T m) l≡n) (helper Γ′) ⟩
    subst (CtxExt′ T m) l≡n (subst (CtxExt′ T m) (sym l≡n) Γ′)
  ≡⟨ subst-∘ (CtxExt′ T m) (sym l≡n) l≡n ⟩
    subst (CtxExt′ T m) (trans (sym l≡n) l≡n) Γ′
  ≡⟨ subst-id (CtxExt′ T m) (trans (sym l≡n) l≡n) ⟩
    Γ′
  ∎
  where
    open ConversionHelper

    helper : ∀ {T m n} (Γ′ : CtxExt′ T m n) →
             CtxExt⇒CtxExt′-helper (CtxExt′⇒CtxExt Γ′) ≡
               subst (CtxExt′ T m) (sym (length-idx′ (CtxExt′⇒CtxExt Γ′))) Γ′
    helper {T} {m} []       =
      sym (subst-id (CtxExt′ T m) (sym (length-idx′ {T} {m} [])))
    helper {T} {m} (t ∷ Γ′) =
      let Γ       = CtxExt′⇒CtxExt Γ′
          n≡l     = sym (length-idx′ Γ)
          n+m≡l+m = sym (length-idx Γ)
      in begin
        subst T n+m≡l+m t ∷ CtxExt⇒CtxExt′-helper Γ
      ≡⟨ cong (subst T n+m≡l+m t ∷_) (helper Γ′) ⟩
        subst T n+m≡l+m t ∷ subst (CtxExt′ T m) n≡l Γ′
      ≡⟨ subst-shift₂ T (CtxExt′ T m) (CtxExt′ T m) {g = λ n → n} _∷_
                      n≡l n+m≡l+m n≡l (sym (length-idx′ (t ∷ Γ))) ⟩
        subst (CtxExt′ T m) (sym (length-idx′ (t ∷ Γ))) (t ∷ Γ′)
      ∎

-- Properties of the `map' functions.

-- map′ is a congruence.

map′-cong : ∀ {T₁ T₂ : ℕ → Set} {k m n}
            {f g : ∀ i → T₁ (i + m) → T₂ (i + n)} → (∀ {i} → f i ≗ g i) →
            _≗_ {A = CtxExt′ T₁ m k} (map′ {T₂ = T₂} f) (map′ g)
map′-cong f≗g []            = refl
map′-cong f≗g (_∷_ {l} t Γ) = cong₂ _∷_ (f≗g {l} t) (map′-cong f≗g Γ)

-- map′ is functorial.

map′-id : ∀ {T m n} → _≗_ {A = CtxExt T m n} (map Fun.id) Fun.id
map′-id []      = refl
map′-id (t ∷ Γ) = cong (t ∷_) (map′-id Γ)

map′-∘ : ∀ {T₁ T₂ T₃ : ℕ → Set} {k l m n}
         (f : ∀ i → T₂ (i + m) → T₃ (i + n))
         (g : ∀ i → T₁ (i + l) → T₂ (i + m)) →
         (Γ : CtxExt′ T₁ l k) →
         map′ {T₂ = T₃} (λ i t → f i (g i t)) Γ ≡ map′ {T₁ = T₂} f (map′ g Γ)
map′-∘ f g []      = refl
map′-∘ f g (t ∷ Γ) = cong (_ ∷_) (map′-∘ f g Γ)

-- Properties of context concatenations.

-- The empty context [] is a right-unit of concatenation.
++-[] : ∀ {T m n} (Γ : CtxExt T m n) → Γ ++ [] ≡ Γ
++-[] []      = refl
++-[] (t ∷ Γ) = cong (_ ∷_) (++-[] Γ)

-- Concatenations commute.
++-comm : ∀ {T k l m n}
          (E : CtxExt T m n) (Δ : CtxExt T l m) (Γ : CtxExt T k l) →
          (E ++ Δ) ++ Γ ≡ E ++ (Δ ++ Γ)
++-comm []      Δ Γ = refl
++-comm (t ∷ E) Δ Γ = cong (_ ∷_) (++-comm E Δ Γ)

-- Mapping commutes with concatenation.
++-map : ∀ {T₁ T₂ : ℕ → Set} {k m n} (f : ∀ {l} → T₁ l → T₂ l)
         (Δ : CtxExt T₁ m n) (Γ : CtxExt T₁ k m) →
         (map f Δ) ++ (map f Γ) ≡ map f (Δ ++ Γ)
++-map f []      Γ = refl
++-map f (t ∷ Δ) Γ = cong (f t ∷_) (++-map f Δ Γ)

-- Mapping commutes with the above variant of concatenation.
′++-map : ∀ {T₁ T₂ : ℕ → Set} {k m n} (f : ∀ {l} → T₁ l → T₂ l)
          (Δ′ : CtxExt′ T₁ m n) (Γ : CtxExt T₁ k m) →
          (map′ (λ l t → f t) Δ′) ′++ (map f Γ) ≡ map f (Δ′ ′++ Γ)
′++-map f []       Γ = refl
′++-map f (t ∷ Δ′) Γ = cong (f t ∷_) (′++-map f Δ′ Γ)

-- Lemmas relating the two variants of concatenation.

++-′++ : ∀ {T l m n} (Δ′ : CtxExt′ T m n) (Γ : CtxExt T l m) →
         CtxExt′⇒CtxExt Δ′ ++ Γ ≡ Δ′ ′++ Γ
++-′++ Δ′ Γ = refl

′++-++ : ∀ {T l m n} (Δ : CtxExt T m (n + m)) (Γ : CtxExt T l m) →
         CtxExt⇒CtxExt′ {l = n} Δ ′++ Γ ≡ Δ ++ Γ
′++-++ Δ Γ = begin
    CtxExt⇒CtxExt′ Δ ′++ Γ
  ≡⟨ sym (++-′++ (CtxExt⇒CtxExt′ Δ) Γ) ⟩
    CtxExt′⇒CtxExt (CtxExt⇒CtxExt′ Δ) ++ Γ
  ≡⟨ cong (_++ Γ) (CtxExt⇒CtxExt′⇒CtxExt-id Δ) ⟩
    Δ ++ Γ
  ∎

-- Lemmas about operations on contexts that require weakening of
-- types.
module WeakenOpsLemmas {T : ℕ → Set} (extension : Extension T) where

  -- The underlyig operations.
  open WeakenOps extension

  -- Conversion to vector representation commutes with
  -- concatenation.

  extToVec-++ : ∀ {k m n} ts (Δ : CtxExt T m n) (Γ : CtxExt T k m) →
                extToVec ts (Δ ++ Γ) ≡ extToVec (extToVec ts Γ) Δ
  extToVec-++ ts []      Γ = refl
  extToVec-++ ts (t ∷ Δ) Γ =
    cong ((_ ∷_) ∘ Vec.map weaken) (extToVec-++ ts Δ Γ)

  extToVec-′++ : ∀ {k m n} ts (Δ′ : CtxExt′ T m n) (Γ : CtxExt T k m) →
                 extToVec ts (Δ′ ′++ Γ) ≡ extToVec′ (extToVec ts Γ) Δ′
  extToVec-′++ ts []       Γ = refl
  extToVec-′++ ts (t ∷ Δ′) Γ =
    cong ((_ ∷_) ∘ Vec.map weaken) (extToVec-′++ ts Δ′ Γ)

  -- Lookup commutes with concatenation.

  lookup-++ : ∀ {k m n} x ts (Δ : CtxExt T m n) (Γ : CtxExt T k m) →
              extLookup x ts (Δ ++ Γ) ≡ extLookup x (extToVec ts Γ) Δ
  lookup-++ x ts Δ Γ = cong (flip Vec.lookup x) (extToVec-++ ts Δ Γ)

  lookup-′++ : ∀ {k m n} x ts (Δ′ : CtxExt′ T m n) (Γ : CtxExt T k m) →
               extLookup x ts (Δ′ ′++ Γ) ≡ extLookup′ x (extToVec ts Γ) Δ′
  lookup-′++ x ts Δ′ Γ = cong (flip Vec.lookup x) (extToVec-′++ ts Δ′ Γ)

  -- We can skip the first element when looking up others.

  lookup-suc : ∀ {m n} x t (ts : Vec (T m) m) (Γ : CtxExt T m n) →
               extLookup (suc x) ts (t ∷ Γ) ≡ weaken (extLookup x ts Γ)
  lookup-suc x t ts Γ = VecProp.lookup-map x weaken (extToVec ts Γ)

  lookup′-suc : ∀ {k m n} x t (ts : Vec (T m) k) (Γ′ : CtxExt′ T m n) →
                extLookup′ (suc x) ts (t ∷ Γ′) ≡ weaken (extLookup′ x ts Γ′)
  lookup′-suc x t ts Γ′ = VecProp.lookup-map x weaken (extToVec′ ts Γ′)

  -- We can skip a spliced-in element when looking up others.

  lookup′-lift : ∀ {k m n} x t (ts : Vec (T m) k) (Γ′ : CtxExt′ T m n) →
                 extLookup′ x ts Γ′ ≡ extLookup′ (lift n suc x) (t ∷ ts) Γ′
  lookup′-lift             x       t ts []       = refl
  lookup′-lift             zero    t ts (u ∷ Δ′) = refl
  lookup′-lift {n = suc n} (suc x) t ts (u ∷ Δ′) = begin
      extLookup′ (suc x) ts (u ∷ Δ′)
    ≡⟨ lookup′-suc x u ts Δ′ ⟩
      weaken (extLookup′ x ts Δ′)
    ≡⟨ cong weaken (lookup′-lift x t ts Δ′) ⟩
      weaken (extLookup′ (lift n suc x) (t ∷ ts) Δ′)
    ≡⟨ sym (lookup′-suc (lift n suc x) u (t ∷ ts) Δ′) ⟩
      extLookup′ (suc (lift n suc x)) (t ∷ ts) (u ∷ Δ′)
    ∎

  -- Lookup in the prefix of a concatenation results in weakening.

  lookup-weaken⋆′ : ∀ {k m} l x ts (Δ′ : CtxExt′ T m l) (Γ : CtxExt T k m) →
                    extLookup (raise l x) ts (Δ′ ′++ Γ) ≡
                      weaken⋆ l (extLookup x ts Γ)
  lookup-weaken⋆′ zero    x ts []       Γ = refl
  lookup-weaken⋆′ (suc l) x ts (t ∷ Δ′) Γ = begin
      extLookup (suc (raise l x)) ts (t ∷ Δ′ ′++ Γ)
    ≡⟨ VecProp.lookup-map (raise l x) weaken (extToVec ts (Δ′ ′++ Γ)) ⟩
      weaken (extLookup (raise l x) ts (Δ′ ′++ Γ))
    ≡⟨ cong weaken (lookup-weaken⋆′ l x ts Δ′ Γ) ⟩
      weaken (weaken⋆ l (extLookup x ts Γ))
    ∎

  lookup-weaken⋆ : ∀ {k m} l x ts (Δ : CtxExt T m (l + m))
                   (Γ : CtxExt T k m) →
                   extLookup (raise l x) ts (Δ ++ Γ) ≡
                     weaken⋆ l (extLookup x ts Γ)
  lookup-weaken⋆ l x ts Δ Γ = begin
      extLookup (raise l x) ts (Δ ++ Γ)
    ≡⟨ sym (cong (extLookup (raise l x) ts) (′++-++ Δ Γ)) ⟩
      extLookup (raise l x) ts ((CtxExt⇒CtxExt′ {l = l} Δ) ′++ Γ)
    ≡⟨ lookup-weaken⋆′ l x ts (CtxExt⇒CtxExt′ Δ) Γ ⟩
      weaken⋆ l (extLookup x ts Γ)
    ∎

-- Lemmas relating conversions of context extensions to vector
-- representation with conversions of the underling entries.
module ConversionLemmas {T₁ T₂ : ℕ → Set}
                        (extension₁ : Extension T₁)
                        (extension₂ : Extension T₂) where
  open VecProp using (map-cong; map-∘)
  private
    module W₁ = WeakenOps extension₁
    module W₂ = WeakenOps extension₂

  -- Conversion to vector representation commutes with mapping,
  -- provided that the mapped function commutes with weakening.
  extToVec-map : ∀ {m n} (f : ∀ {l} → T₁ l → T₂ l) ts (Γ : CtxExt T₁ m n) →
                 (∀ {j} (t : T₁ j) → W₂.weaken (f t) ≡ f (W₁.weaken t)) →
                 W₂.extToVec (Vec.map f ts) (map f Γ) ≡
                   Vec.map f (W₁.extToVec ts Γ)
  extToVec-map f ts []      hyp = refl
  extToVec-map f ts (t ∷ Γ) hyp = cong₂ _∷_ (hyp t) (begin
      Vec.map W₂.weaken (W₂.extToVec (Vec.map f ts) (map f Γ))
    ≡⟨ cong (Vec.map W₂.weaken) (extToVec-map f ts Γ hyp) ⟩
      (Vec.map W₂.weaken (Vec.map f (W₁.extToVec ts Γ)))
    ≡⟨ sym (map-∘ W₂.weaken f (W₁.extToVec ts Γ)) ⟩
      (Vec.map (W₂.weaken ∘ f) (W₁.extToVec ts Γ))
    ≡⟨ map-cong hyp (W₁.extToVec ts Γ) ⟩
      (Vec.map (f ∘ W₁.weaken) (W₁.extToVec ts Γ))
    ≡⟨ map-∘ f W₁.weaken (W₁.extToVec ts Γ) ⟩
      (Vec.map f (Vec.map W₁.weaken (W₁.extToVec ts Γ)))
    ∎)

  -- Conversion to vector representation commutes with re-indexing,
  -- provided that the reindexing function commutes with weakening.
  extToVec′-map′ : ∀ {k l m n} (f : ∀ j → T₁ (j + m) → T₂ (j + n))
                   (ts : Vec (T₁ m) k) (Γ′ : CtxExt′ T₁ m l) →
                   (∀ {j} (t : T₁ (j + m)) →
                     W₂.weaken (f j t) ≡ f (suc j) (W₁.weaken t)) →
                   W₂.extToVec′ (Vec.map (f 0) ts) (map′ f Γ′) ≡
                     Vec.map (f l) (W₁.extToVec′ ts Γ′)
  extToVec′-map′ f ts []             _   = refl
  extToVec′-map′ f ts (_∷_ {l} t Γ′) hyp = cong₂ _∷_ (hyp {l} t) (begin
      Vec.map W₂.weaken (W₂.extToVec′ (Vec.map (f 0) ts) (map′ f Γ′))
    ≡⟨ cong (Vec.map W₂.weaken) (extToVec′-map′ f ts Γ′ hyp) ⟩
      (Vec.map W₂.weaken (Vec.map (f _) (W₁.extToVec′ ts Γ′)))
    ≡⟨ sym (map-∘ W₂.weaken (f l) (W₁.extToVec′ ts Γ′)) ⟩
      (Vec.map (W₂.weaken ∘ f l) (W₁.extToVec′ ts Γ′))
    ≡⟨ map-cong (hyp {l}) (W₁.extToVec′ ts Γ′) ⟩
      (Vec.map (f (suc l) ∘ W₁.weaken) (W₁.extToVec′ ts Γ′))
    ≡⟨ map-∘ (f (suc l)) W₁.weaken (W₁.extToVec′ ts Γ′) ⟩
      (Vec.map (f (suc l)) (Vec.map W₁.weaken (W₁.extToVec′ ts Γ′)))
    ∎)

  -- Lookup commutes with mapping, provided that the mapped function
  -- commutes with weakening.
  lookup-map : ∀ {m n} x (f : ∀ {j} → T₁ j → T₂ j) ts (Γ : CtxExt T₁ m n) →
               (∀ {j} (t : T₁ j) → W₂.weaken (f t) ≡ f (W₁.weaken t)) →
               W₂.extLookup x (Vec.map f ts) (map f Γ) ≡
                 f (W₁.extLookup x ts Γ)
  lookup-map x f ts Γ hyp = begin
      W₂.extLookup x (Vec.map f ts) (map f Γ)
    ≡⟨ cong (flip Vec.lookup x) (extToVec-map f ts Γ hyp) ⟩
      Vec.lookup (Vec.map f (W₁.extToVec ts Γ)) x
    ≡⟨ VecProp.lookup-map x f (W₁.extToVec ts Γ) ⟩
      f (W₁.extLookup x ts Γ)
    ∎

  -- Lookup commutes with re-indexing, provided that the reindexing
  -- function commutes with weakening.
  lookup′-map′ : ∀ {k l m n} x (f : ∀ j → T₁ (j + m) → T₂ (j + n))
                 (ts : Vec (T₁ m) k) (Γ′ : CtxExt′ T₁ m l) →
                 (∀ {j} (t : T₁ (j + m)) →
                   W₂.weaken (f j t) ≡ f (suc j) (W₁.weaken t)) →
                 W₂.extLookup′ x (Vec.map (f 0) ts) (map′ f Γ′) ≡
                   f l (W₁.extLookup′ x ts Γ′)
  lookup′-map′ {l = l} x f ts Γ′ hyp = begin
      W₂.extLookup′ x (Vec.map (f 0) ts) (map′ f Γ′)
    ≡⟨ cong (flip Vec.lookup x) (extToVec′-map′ f ts Γ′ hyp) ⟩
      Vec.lookup (Vec.map (f l) (W₁.extToVec′ ts Γ′)) x
    ≡⟨ VecProp.lookup-map x (f l) (W₁.extToVec′ ts Γ′) ⟩
      f l (W₁.extLookup′ x ts Γ′)
    ∎

-- Lemmas about well-formed contexts and context extensions.
module WellFormedContextLemmas {T} (_⊢_wf : Wf T) where

  open WellFormedContext _⊢_wf

  -- Conversions between well-formed extensions of the empty context
  -- are well-formed contexts.

  ⊢wfExt⇒wf : ∀ {n} {Γ : Ctx T n} → [] ⊢ Γ wfExt → Γ wf
  ⊢wfExt⇒wf []               = []
  ⊢wfExt⇒wf (t-wf ∷ Γ-wfExt) =
    subst (_⊢ _ wf) (++-[] _) t-wf ∷ ⊢wfExt⇒wf Γ-wfExt

  wf⇒⊢wfExt : ∀ {n} {Γ : Ctx T n} → Γ wf → [] ⊢ Γ wfExt
  wf⇒⊢wfExt []            = []
  wf⇒⊢wfExt (t-wf ∷ Γ-wf) =
    subst (_⊢ _ wf) (sym (++-[] _)) t-wf ∷ wf⇒⊢wfExt Γ-wf

  -- Well-formed extensions of the empty context are isomorphic to
  -- well-formed contexts.

  ⊢wfExt⇒wf⇒⊢wfExt-id : ∀ {n} {Γ : Ctx T n} (Γ-wfExt : [] ⊢ Γ wfExt) →
                        wf⇒⊢wfExt (⊢wfExt⇒wf Γ-wfExt) ≡ Γ-wfExt
  ⊢wfExt⇒wf⇒⊢wfExt-id []                             = refl
  ⊢wfExt⇒wf⇒⊢wfExt-id (_∷_ {t = t} {Δ} t-wf Γ-wfExt) =
    cong₂ _∷_ (begin
      subst (_⊢ t wf) (sym (++-[] Δ)) (subst (_⊢ t wf) (++-[] Δ) t-wf)
    ≡⟨ subst-∘ (_⊢ t wf) (++-[] Δ) (sym (++-[] Δ)) ⟩
      subst (_⊢ t wf) (trans (++-[] Δ) (sym (++-[] Δ))) t-wf
    ≡⟨ subst-id (_⊢ t wf) (trans (++-[] Δ) (sym (++-[] Δ))) ⟩
      t-wf
    ∎) (⊢wfExt⇒wf⇒⊢wfExt-id Γ-wfExt)

  wf⇒⊢wfExt⇒wf-id : ∀ {n} {Γ : Ctx T n} (Γ-wf : Γ wf) →
                    ⊢wfExt⇒wf (wf⇒⊢wfExt Γ-wf) ≡ Γ-wf
  wf⇒⊢wfExt⇒wf-id []                          = refl
  wf⇒⊢wfExt⇒wf-id (_∷_ {t = t} {Γ} t-wf Γ-wf) =
    cong₂ _∷_ (begin
      subst (_⊢ t wf) (++-[] Γ) (subst (_⊢ t wf) (sym (++-[] Γ)) t-wf)
    ≡⟨ subst-∘ (_⊢ t wf) (sym (++-[] Γ)) (++-[] Γ) ⟩
      subst (_⊢ t wf) (trans (sym (++-[] Γ)) (++-[] Γ)) t-wf
    ≡⟨ subst-id (_⊢ t wf) (trans (sym (++-[] Γ)) (++-[] Γ)) ⟩
      t-wf
    ∎) (wf⇒⊢wfExt⇒wf-id Γ-wf)

  -- Concatenation preserves well-formedness of contexts.
  wf-++-wfExt : ∀ {m n} {Δ : CtxExt T m n} {Γ : Ctx T m} →
                Γ ⊢ Δ wfExt → Γ wf → Δ ++ Γ wf
  wf-++-wfExt []               Γ-wf = Γ-wf
  wf-++-wfExt (t-wf ∷ Δ-wfExt) Γ-wf = t-wf ∷ wf-++-wfExt Δ-wfExt Γ-wf

  -- Concatenation preserves well-formedness of context extensions.
  wfExt-++-wfExt : ∀ {k m n} {E : CtxExt T m n} {Δ : CtxExt T k m}
                   {Γ : Ctx T k} →
                   Δ ++ Γ ⊢ E wfExt → Γ ⊢ Δ wfExt → Γ ⊢ E ++ Δ wfExt
  wfExt-++-wfExt []                             Δ-wfExt = Δ-wfExt
  wfExt-++-wfExt (_∷_ {t = t} {E} t-wf E-wfExt) Δ-wfExt =
    subst (_⊢ t wf) (sym (++-comm E _ _)) t-wf ∷ wfExt-++-wfExt E-wfExt Δ-wfExt

  -- Splitting of well-formed contexts.
  wf-split : ∀ {m n} {Δ : CtxExt T m n} {Γ : Ctx T m} →
             Δ ++ Γ wf → Γ ⊢ Δ wfExt × Γ wf
  wf-split {Δ = []}    Γ-wf             = [] , Γ-wf
  wf-split {Δ = t ∷ Δ} (t-wf ∷ Δ++Γ-wf) =
    let Δ-wfExt , Γ-wf = wf-split Δ++Γ-wf
    in t-wf ∷ Δ-wfExt , Γ-wf

  -- Splitting of well-formed context extensions.
  wfExt-split : ∀ {k m n} {E : CtxExt T m n} {Δ : CtxExt T k m} {Γ : Ctx T k} →
                Γ ⊢ E ++ Δ wfExt → Δ ++ Γ ⊢ E wfExt × Γ ⊢ Δ wfExt
  wfExt-split {E = []}    Δ-wfExt             = [] , Δ-wfExt
  wfExt-split {E = t ∷ E} (t-wf ∷ E++Δ-wfExt) =
    let E-wfExt , Δ-wfExt = wfExt-split E++Δ-wfExt
    in subst (_⊢ _ wf) (++-comm E _ _) t-wf ∷ E-wfExt , Δ-wfExt
