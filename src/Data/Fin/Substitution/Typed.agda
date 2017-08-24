------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

module Data.Fin.Substitution.Typed where

import Category.Applicative.Indexed as Applicative
open Applicative.Morphism using (op-<$>)
open import Data.Fin using (Fin; zero; suc; raise)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as NatProp
import Data.Nat.Properties.Simple as SimpleNatProp
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.All as All using (All; All₂; []; _∷_; map₂)
open import Data.Vec.All.Properties using (gmap; gmap₂; gmap₂₁; gmap₂₂)
import Data.Vec.Properties as VecProp
open import Function as Fun using (_∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq hiding (trans)
open PropEq.≡-Reasoning


------------------------------------------------------------------------
-- Abstract typing contexts and well-typedness relations

-- Abstract typing contexts over T-types.
--
-- A typing context Ctx T n maps n variables to T-types containing up
-- to n free variables each.
module Context where

  infixr 5 _∷_

  -- Extensions of typing contexts.
  --
  -- Context extensions are indexed sequences that can be concatenated
  -- together to form typing contexts.  A CtxExt m n is an extension
  -- mapping (n - m) variables to T-types with m to n free variables
  -- each.  I.e. the i-th type (for m ≤ i < n) may refer to any of the
  -- previous (i - 1) free variables xₘ, ..., xᵢ₋₁.
  data CtxExt (T : ℕ → Set) (m : ℕ) : ℕ → Set where
    []  :                              CtxExt T m m
    _∷_ : ∀ {n} → T n → CtxExt T m n → CtxExt T m (suc n)

  -- Typing contexts.
  --
  -- Typing contexts are just initial context extensions, i.e. the
  -- innermost type must not contain any free variables at all.
  Ctx : (ℕ → Set) → ℕ → Set
  Ctx T = CtxExt T 0

  -- Drop the m innermost elements of a context Γ.
  drop : ∀ {T n} m → Ctx T (m + n) → Ctx T n
  drop zero         Γ  = Γ
  drop (suc m) (_ ∷ Γ) = drop m Γ

  -- A map function that point-wise changes the entries of a context
  -- extension.
  map : ∀ {T₁ T₂ m n} → (∀ {l} → T₁ l → T₂ l) → CtxExt T₁ m n → CtxExt T₂ m n
  map f []      = []
  map f (t ∷ Γ) = f t ∷ map f Γ

  infixr 5 _++_

  -- Concatenate two context extensions.
  _++_ : ∀ {T k m n} → CtxExt T m n → CtxExt T k m → CtxExt T k n
  []      ++ Γ = Γ
  (t ∷ Δ) ++ Γ = t ∷ (Δ ++ Γ)

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

  -- The length of a context extension.
  length : ∀ {T m n} → CtxExt T m n → ℕ
  length []      = 0
  length (_ ∷ Γ) = suc (length Γ)

  -- Lemmas relating the length of a context extension to its
  -- indices/bounds.

  length-bds : ∀ {T m n} (Γ : CtxExt T m n) → length Γ + m ≡ n
  length-bds []      = refl
  length-bds (t ∷ Γ) = cong suc (length-bds Γ)

  length-bds′ : ∀ {T m n} (Γ : CtxExt T m (n + m)) → length Γ ≡ n
  length-bds′ {T} {m} {n} Γ = cancel-+-left m (begin
    m + length Γ    ≡⟨ +-comm m _ ⟩
    length Γ + m    ≡⟨ length-bds Γ ⟩
    n + m           ≡⟨ +-comm n m ⟩
    m + n           ∎)
    where
      open SimpleNatProp using (+-comm)
      open NatProp       using (cancel-+-left)

  -- An alternative representation of context extension using
  -- relative-indexing.
  data CtxExt′ (T : ℕ → Set) (m : ℕ) : ℕ → Set where
    []  :                                     CtxExt′ T m 0
    _∷_ : ∀ {l} → T (l + m) → CtxExt′ T m l → CtxExt′ T m (suc l)

  head′ : ∀ {T m l} → CtxExt′ T m (suc l) → T (l + m)
  head′ (t ∷ ts) = t

  tail′ : ∀ {T m l} → CtxExt′ T m (suc l) → CtxExt′ T m l
  tail′ (t ∷ ts) = ts

  -- A map function that point-wise re-indexes and changes the entries
  -- in a context.
  map′ : ∀ {T₁ T₂ k m n} → (∀ l → T₁ (l + m) → T₂ (l + n)) →
         CtxExt′ T₁ m k → CtxExt′ T₂ n k
  map′ f []            = []
  map′ f (_∷_ {l} t Γ) = f l t ∷ map′ (λ l → f l) Γ

  -- map′ is a congruence.

  map′-cong : ∀ {T₁ T₂ : ℕ → Set} {k m n}
              {f g : ∀ i → T₁ (i + m) → T₂ (i + n)} → (∀ {i} → f i ≗ g i) →
              _≗_ {A = CtxExt′ T₁ m k} (map′ {T₂ = T₂} f) (map′ g)
  map′-cong f≗g []      = refl
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

  -- Conversions between the two representations.

  private

    CtxExt⇒CtxExt′-helper : ∀ {T m n} → (Γ : CtxExt T m n) →
                            CtxExt′ T m (length Γ)
    CtxExt⇒CtxExt′-helper     []      = []
    CtxExt⇒CtxExt′-helper {T} (t ∷ Γ) =
      subst T (sym (length-bds Γ)) t ∷ CtxExt⇒CtxExt′-helper Γ

  CtxExt⇒CtxExt′ : ∀ {T m l} → CtxExt T m (l + m) → CtxExt′ T m l
  CtxExt⇒CtxExt′ Γ =
    subst (CtxExt′ _ _) (length-bds′ Γ) (CtxExt⇒CtxExt′-helper Γ)

  CtxExt′⇒CtxExt : ∀ {T m l} → CtxExt′ T m l → CtxExt T m (l + m)
  CtxExt′⇒CtxExt []       = []
  CtxExt′⇒CtxExt (t ∷ Γ′) = t ∷ CtxExt′⇒CtxExt Γ′

  -- Some reusable lemmas about subst.
  --
  -- FIXME: These should probably go into
  -- Relation.Binary.PropositionalEquality.

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
            subst P q (subst P p a) ≡ subst P (PropEq.trans p q) a
  subst-∘ P refl refl = refl

  subst-id : ∀ {a} {A : Set a} (P : A → Set) {x : A} {a : P x}
             (p : x ≡ x) → subst P p a ≡ a
  subst-id P refl = refl

  -- The two representations of context extensions are isomorphic.

  CtxExt⇒CtxExt′⇒CtxExt-id : ∀ {T m n} (Γ : CtxExt T m (n + m)) →
                             CtxExt′⇒CtxExt {l = n} (CtxExt⇒CtxExt′ Γ) ≡ Γ
  CtxExt⇒CtxExt′⇒CtxExt-id {T} {m} {n} Γ =
    let l≡n     = length-bds′ {n = n} Γ
        l+m≡n+m = length-bds Γ
    in begin
      CtxExt′⇒CtxExt (CtxExt⇒CtxExt′ Γ)
    ≡⟨ subst-shift (CtxExt′ T m) (CtxExt T m) {f = λ n → n}
                   (CtxExt′⇒CtxExt {T} {m}) l≡n l≡n l+m≡n+m ⟩
      subst (CtxExt T m) l+m≡n+m (CtxExt′⇒CtxExt (CtxExt⇒CtxExt′-helper Γ))
    ≡⟨ cong (subst (CtxExt T m) l+m≡n+m) (helper Γ) ⟩
      subst (CtxExt T m) l+m≡n+m (subst (CtxExt T m) (sym l+m≡n+m) Γ)
    ≡⟨ subst-∘ (CtxExt T m) (sym l+m≡n+m) l+m≡n+m ⟩
      subst (CtxExt T m) (PropEq.trans (sym l+m≡n+m) l+m≡n+m) Γ
    ≡⟨ subst-id (CtxExt T m) (PropEq.trans (sym l+m≡n+m) l+m≡n+m) ⟩
      Γ
    ∎
    where
      helper : ∀ {T m n} (Γ : CtxExt T m n) →
               CtxExt′⇒CtxExt (CtxExt⇒CtxExt′-helper Γ) ≡
                 subst (CtxExt T m) (sym (length-bds Γ)) Γ
      helper         []      = refl
      helper {T} {m} (t ∷ Γ) = let n≡l+m = sym (length-bds Γ) in begin
          subst T n≡l+m t ∷ CtxExt′⇒CtxExt (CtxExt⇒CtxExt′-helper Γ)
        ≡⟨ cong ((subst T n≡l+m t) ∷_) (helper Γ) ⟩
          subst T n≡l+m t ∷ subst (CtxExt T m) n≡l+m Γ
        ≡⟨ subst-shift₂ T (CtxExt T m) (CtxExt T m) {f = λ n → n} _∷_
                        n≡l+m n≡l+m n≡l+m (sym (length-bds (t ∷ Γ))) ⟩
          subst (CtxExt T m) (sym (length-bds (t ∷ Γ))) (t ∷ Γ)
        ∎

  CtxExt′⇒CtxExt⇒CtxExt′-id : ∀ {T m n} (Γ′ : CtxExt′ T m n) →
                              CtxExt⇒CtxExt′ (CtxExt′⇒CtxExt Γ′) ≡ Γ′
  CtxExt′⇒CtxExt⇒CtxExt′-id {T} {m} Γ′ =
    let Γ   = CtxExt′⇒CtxExt Γ′
        l≡n = length-bds′ Γ
    in begin
      CtxExt⇒CtxExt′ Γ
    ≡⟨ cong (subst (CtxExt′ T m) l≡n) (helper Γ′) ⟩
      subst (CtxExt′ T m) l≡n (subst (CtxExt′ T m) (sym l≡n) Γ′)
    ≡⟨ subst-∘ (CtxExt′ T m) (sym l≡n) l≡n ⟩
      subst (CtxExt′ T m) (PropEq.trans (sym l≡n) l≡n) Γ′
    ≡⟨ subst-id (CtxExt′ T m) (PropEq.trans (sym l≡n) l≡n) ⟩
      Γ′
    ∎
    where
      helper : ∀ {T m n} (Γ′ : CtxExt′ T m n) →
               CtxExt⇒CtxExt′-helper (CtxExt′⇒CtxExt Γ′) ≡
                 subst (CtxExt′ T m) (sym (length-bds′ (CtxExt′⇒CtxExt Γ′))) Γ′
      helper {T} {m} []       =
        sym (subst-id (CtxExt′ T m) (sym (length-bds′ {T} {m} [])))
      helper {T} {m} (t ∷ Γ′) =
        let Γ       = CtxExt′⇒CtxExt Γ′
            n≡l     = sym (length-bds′ Γ)
            n+m≡l+m = sym (length-bds Γ)
        in begin
          subst T n+m≡l+m t ∷ CtxExt⇒CtxExt′-helper Γ
        ≡⟨ cong (subst T n+m≡l+m t ∷_) (helper Γ′) ⟩
          subst T n+m≡l+m t ∷ subst (CtxExt′ T m) n≡l Γ′
        ≡⟨ subst-shift₂ T (CtxExt′ T m) (CtxExt′ T m) {g = λ n → n} _∷_
                        n≡l n+m≡l+m n≡l (sym (length-bds′ (t ∷ Γ))) ⟩
          subst (CtxExt′ T m) (sym (length-bds′ (t ∷ Γ))) (t ∷ Γ′)
        ∎

  infixr 5 _′++_

  -- A variant of concatenation where the suffix is given in the
  -- alternative representation.
  _′++_ : ∀ {T k m n} → CtxExt′ T m n → CtxExt T k m → CtxExt T k (n + m)
  Δ′ ′++ Γ = CtxExt′⇒CtxExt Δ′ ++ Γ

  -- Mapping commutes with the above variant of concatenation.
  ′++-map : ∀ {T₁ T₂ : ℕ → Set} {k m n} (f : ∀ {l} → T₁ l → T₂ l)
            (Δ′ : CtxExt′ T₁ m n) (Γ : CtxExt T₁ k m) →
            (map′ (λ l t → f t) Δ′) ′++ (map f Γ) ≡ map f (Δ′ ′++ Γ)
  ′++-map f []       Γ = refl
  ′++-map f (t ∷ Δ′) Γ = cong (f t ∷_) (′++-map f Δ′ Γ)

  -- Operations on contexts that require weakening of types.
  record WeakenOps (T : ℕ → Set) : Set where

    -- Weakening of types.
    field weaken : ∀ {n} → T n → T (1 + n)

    extension : Extension T
    extension = record { weaken = weaken }
    open Extension extension hiding (weaken)

    -- Convert a context extension to its vector representation.

    extToVec : ∀ {m n} → Vec (T m) m → CtxExt T m n → Vec (T n) n
    extToVec ts []      = ts
    extToVec ts (t ∷ Γ) = weaken t /∷ extToVec ts Γ

    extToVec′ : ∀ {k m n} → Vec (T m) k → CtxExt′ T m n →
                Vec (T (n + m)) (n + k)
    extToVec′ ts []      = ts
    extToVec′ ts (t ∷ Γ) = weaken t /∷ extToVec′ ts Γ

    -- Convert a context to its vector representation.
    toVec : ∀ {n} → Ctx T n → Vec (T n) n
    toVec = extToVec []

    -- Lookup the type of a variable in a context extension.

    extLookup : ∀ {m n} → Fin n → Vec (T m) m → CtxExt T m n → T n
    extLookup x ts Γ = Vec.lookup x (extToVec ts Γ)

    extLookup′ : ∀ {k m n} → Fin (n + k) → Vec (T m) k →
                 CtxExt′ T m n → T (n + m)
    extLookup′ x ts Γ = Vec.lookup x (extToVec′ ts Γ)

    -- Lookup the type of a variable in a context.
    lookup : ∀ {n} → Fin n → Ctx T n → T n
    lookup x = extLookup x []

    -- Some helful lemmas about context extensions.

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
    lookup-++ x ts Δ Γ = cong (Vec.lookup x) (extToVec-++ ts Δ Γ)

    lookup-′++ : ∀ {k m n} x ts (Δ′ : CtxExt′ T m n) (Γ : CtxExt T k m) →
                 extLookup x ts (Δ′ ′++ Γ) ≡ extLookup′ x (extToVec ts Γ) Δ′
    lookup-′++ x ts Δ′ Γ = cong (Vec.lookup x) (extToVec-′++ ts Δ′ Γ)

    open Data.Fin using (lift; raise)

    -- We can skip the first element when looking up others.

    lookup-suc : ∀ {m n} x t (ts : Vec (T m) m) (Γ : CtxExt T m n) →
                 extLookup (suc x) ts (t ∷ Γ) ≡ weaken (extLookup x ts Γ)
    lookup-suc x t ts Γ = op-<$> (lookup-morphism x) _ _
      where open VecProp using (lookup-morphism)

    lookup′-suc : ∀ {k m n} x t (ts : Vec (T m) k) (Γ′ : CtxExt′ T m n) →
                  extLookup′ (suc x) ts (t ∷ Γ′) ≡ weaken (extLookup′ x ts Γ′)
    lookup′-suc x t ts Γ′ = op-<$> (lookup-morphism x) _ _
      where open VecProp using (lookup-morphism)

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
      where open VecProp using (lookup-morphism)

    -- Lookup in the prefix of a concatenation results in weakening.

    lookup-weaken⋆′ : ∀ {k m} l x ts (Δ′ : CtxExt′ T m l) (Γ : CtxExt T k m) →
                      extLookup (raise l x) ts (Δ′ ′++ Γ) ≡
                        weaken⋆ l (extLookup x ts Γ)
    lookup-weaken⋆′ zero    x ts []       Γ = refl
    lookup-weaken⋆′ (suc l) x ts (t ∷ Δ′) Γ = begin
        extLookup (suc (raise l x)) ts (t ∷ Δ′ ′++ Γ)
      ≡⟨ op-<$> (VecProp.lookup-morphism (raise l x)) _ _ ⟩
        weaken (extLookup (raise l x) ts (Δ′ ′++ Γ))
      ≡⟨ cong weaken (lookup-weaken⋆′ l x ts Δ′ Γ) ⟩
        weaken (weaken⋆ l (extLookup x ts Γ))
      ∎

    lookup-weaken⋆ : ∀ {k m} l x ts (Δ : CtxExt T m (l + m))
                     (Γ : CtxExt T k m) →
                     extLookup (raise l x) ts (Δ ++ Γ) ≡
                       weaken⋆ l (extLookup x ts Γ)
    lookup-weaken⋆ l x ts Δ Γ =
      subst (_≡ _) (cong (λ Δ → extLookup (raise l x) ts (Δ ++ Γ))
                         (CtxExt⇒CtxExt′⇒CtxExt-id Δ))
            (lookup-weaken⋆′ l x ts (CtxExt⇒CtxExt′ Δ) Γ)

  -- Lemmas relating conversions of context extensions to vector
  -- representation with conversions of the underling entries.
  module ConversionLemmas {T₁ T₂}
                          (weakenOps₁ : WeakenOps T₁)
                          (weakenOps₂ : WeakenOps T₂) where
    open VecProp using (map-cong; map-∘)
    private
      module W₁ = WeakenOps weakenOps₁
      module W₂ = WeakenOps weakenOps₂

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
      ≡⟨ cong (Vec.lookup x) (extToVec-map f ts Γ hyp) ⟩
        Vec.lookup x (Vec.map f (W₁.extToVec ts Γ))
      ≡⟨ op-<$> (VecProp.lookup-morphism x) _ _ ⟩
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
      ≡⟨ cong (Vec.lookup x) (extToVec′-map′ f ts Γ′ hyp) ⟩
        Vec.lookup x (Vec.map (f l) (W₁.extToVec′ ts Γ′))
      ≡⟨ op-<$> (VecProp.lookup-morphism x) _ _ ⟩
        f l (W₁.extLookup′ x ts Γ′)
      ∎

  -- Operations on contexts that require substitutions in types.
  record SubstOps (T T′ : ℕ → Set) : Set where

    field
      application : Application T T′ -- Application of T′ substitutions to Ts.
      simple      : Simple T′        -- Simple T′ substitutions.

    open Application application public
    open Simple      simple      public

    -- Application of substitutions to context extensions.

    _E′/_ : ∀ {k m n} → CtxExt′ T m k → Sub T′ m n → CtxExt′ T n k
    Γ′ E′/ σ = map′ (λ l t → t / σ ↑⋆ l) Γ′

    _E/_ : ∀ {k m n} → CtxExt T m (k + m) → Sub T′ m n → CtxExt T n (k + n)
    _E/_ {k} Γ σ = CtxExt′⇒CtxExt (CtxExt⇒CtxExt′ {l = k} Γ E′/ σ)


open Context

-- Abstract well-formedness.
--
-- An abtract well-formedness relation _⊢_wf : Wf Tp is a binary
-- relation which, in a given Tp-context, asserts the well-formedness
-- of Tp-types.
Wf : (ℕ → Set) → Set₁
Wf Tp = ∀ {n} → Ctx Tp n → Tp n → Set

-- Well-formed contexts.
--
-- A well-formed typing context (Γ wf) is a context Γ in which every
-- participating T-type is well-formed.
module WellFormedContext {T} (_⊢_wf : Wf T) where
  infix  4 _wf _⊢_wfExt _⊢_wfExt′
  infixr 5 _∷_

  -- Well-formed typing contexts.
  data _wf : ∀ {n} → Ctx T n → Set where
    []  :                                              [] wf
    _∷_ : ∀ {n t} {Γ : Ctx T n} → Γ ⊢ t wf → Γ wf → t ∷ Γ wf

  -- Well-formed context extensions.

  data _⊢_wfExt {m} (Γ : Ctx T m) : ∀ {n} → CtxExt T m n → Set where
    []  : Γ ⊢ [] wfExt
    _∷_ : ∀ {n t} {Δ : CtxExt T m n} →
          (Δ ++ Γ) ⊢ t wf → Γ ⊢ Δ wfExt → Γ ⊢ t ∷ Δ wfExt

  _⊢_wfExt′ : ∀ {m n} → Ctx T m → CtxExt′ T m n → Set
  Γ ⊢ Δ′ wfExt′ = Γ ⊢ (CtxExt′⇒CtxExt Δ′) wfExt

  -- Inversions.

  wf-∷₁ : ∀ {n} {Γ : Ctx T n} {a} → a ∷ Γ wf → Γ ⊢ a wf
  wf-∷₁ (a-wf ∷ _) = a-wf

  wf-∷₂ : ∀ {n} {Γ : Ctx T n} {a} → a ∷ Γ wf → Γ wf
  wf-∷₂ (_ ∷ Γ-wf) = Γ-wf

  wfExt-∷₁ : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} {a} →
             Γ ⊢ a ∷ Δ wfExt → (Δ ++ Γ) ⊢ a wf
  wfExt-∷₁ (a-wf ∷ _) = a-wf

  wfExt-∷₂ : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} {a} →
             Γ ⊢ a ∷ Δ wfExt → Γ ⊢ Δ wfExt
  wfExt-∷₂ (_ ∷ Γ-wf) = Γ-wf

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
      subst (_⊢ t wf) (PropEq.trans (++-[] Δ) (sym (++-[] Δ))) t-wf
    ≡⟨ subst-id (_⊢ t wf) (PropEq.trans (++-[] Δ) (sym (++-[] Δ))) ⟩
      t-wf
    ∎) (⊢wfExt⇒wf⇒⊢wfExt-id Γ-wfExt)

  wf⇒⊢wfExt⇒wf-id : ∀ {n} {Γ : Ctx T n} (Γ-wf : Γ wf) →
                    ⊢wfExt⇒wf (wf⇒⊢wfExt Γ-wf) ≡ Γ-wf
  wf⇒⊢wfExt⇒wf-id []                          = refl
  wf⇒⊢wfExt⇒wf-id (_∷_ {t = t} {Γ} t-wf Γ-wf) =
    cong₂ _∷_ (begin
      subst (_⊢ t wf) (++-[] Γ) (subst (_⊢ t wf) (sym (++-[] Γ)) t-wf)
    ≡⟨ subst-∘ (_⊢ t wf) (sym (++-[] Γ)) (++-[] Γ) ⟩
      subst (_⊢ t wf) (PropEq.trans (sym (++-[] Γ)) (++-[] Γ)) t-wf
    ≡⟨ subst-id (_⊢ t wf) (PropEq.trans (sym (++-[] Γ)) (++-[] Γ)) ⟩
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

  -- Operations on well-formed contexts that require weakening of
  -- well-formedness judgments.
  record WfWeakenOps (weakenOps : WeakenOps T) : Set where
    private module W = WeakenOps weakenOps

    -- Weakening of well-formedness judgments.
    field wf-weaken : ∀ {n} {Γ : Ctx T n} {a b} → Γ ⊢ a wf → Γ ⊢ b wf →
                      (a ∷ Γ) ⊢ W.weaken b wf

    -- Convert a well-formed context to its All representation.
    toAll : ∀ {n} {Γ : Ctx T n} → Γ wf → All (λ t → Γ ⊢ t wf) (W.toVec Γ)
    toAll []            = []
    toAll (t-wf ∷ Γ-wf) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (toAll Γ-wf)

    -- Convert a well-formed context extension to its All representation.
    extToAll : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} →
               All (λ t → Γ ⊢ t wf) (W.toVec Γ) → Γ ⊢ Δ wfExt →
               All (λ a → (Δ ++ Γ) ⊢ a wf) (W.toVec (Δ ++ Γ))
    extToAll ts-wf []               = ts-wf
    extToAll ts-wf (t-wf ∷ Δ-wfExt) =
      wf-weaken t-wf t-wf ∷ gmap (wf-weaken t-wf) (extToAll ts-wf Δ-wfExt)

    -- Lookup the well-formedness proof of a variable in a context.
    lookup : ∀ {n} {Γ : Ctx T n} (x : Fin n) → Γ wf → Γ ⊢ (W.lookup x Γ) wf
    lookup x = All.lookup x ∘ toAll

    -- Lookup the well-formedness proof of a variable in a context extension.
    extLookup : ∀ {m n} {Γ : Ctx T m} {Δ : CtxExt T m n} (x : Fin n) →
                All (λ t → Γ ⊢ t wf) (W.toVec Γ) → Γ ⊢ Δ wfExt →
                (Δ ++ Γ) ⊢ (W.lookup x (Δ ++ Γ)) wf
    extLookup x ts-wf = All.lookup x ∘ (extToAll ts-wf)

-- Trivial well-formedness.
--
-- This module provides a trivial well-formedness relation and the
-- corresponding trivially well-formed contexts.  This is useful when
-- implmenting typed substitutions on types that either lack or do not
-- necessitate a notion of well-formedness.
module ⊤-WellFormed {T} (weakenOps : WeakenOps T) where

  infix  4 _⊢_wf

  -- Trivial well-formedness.
  _⊢_wf : Wf T
  _ ⊢ _ wf = ⊤

  open WellFormedContext _⊢_wf public

  -- Trivial well-formedness of contexts.
  ctx-wf : ∀ {n} (Γ : Ctx T n) → Γ wf
  ctx-wf []      = []
  ctx-wf (a ∷ Γ) = tt ∷ ctx-wf Γ

  -- Trivial well-formedness of context extensions.

  ctx-wfExt : ∀ {m n} (Δ : CtxExt T m n) {Γ : Ctx T m} → Γ ⊢ Δ wfExt
  ctx-wfExt []      = []
  ctx-wfExt (a ∷ Δ) = tt ∷ ctx-wfExt Δ

  ctx-wfExt′ : ∀ {m n} (Δ′ : CtxExt′ T m n) {Γ : Ctx T m} → Γ ⊢ Δ′ wfExt′
  ctx-wfExt′ Δ′ = ctx-wfExt (CtxExt′⇒CtxExt Δ′)

  module ⊤-WfWeakenOps where

    wfWeakenOps : WfWeakenOps weakenOps
    wfWeakenOps = record { wf-weaken = λ _ _ → tt }

    open WfWeakenOps public


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

  -- Term relations lifted point-wise to corresponding substitutions.
  --
  -- Given a relation R on Tm₁ and Tm₂ terms in a Tp context, the
  -- family of relations (LiftCtxTermRel R) relates Tm₁ and Tm₂
  -- substitutions point-wise.
  LiftCtxTermRel : ∀ {m} → CtxTermRel Tp Tm₁ Tm₂ →
                   CtxTermRel Tp (Sub Tm₁ m) (Sub Tm₂ m)
  LiftCtxTermRel P Γ σ₁ σ₂ = All₂ (P Γ) σ₁ σ₂

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

    -- Operations on (source) Tp₁ contexts.
    weakenOps : WeakenOps Tp₁

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
           (x : Fin m) → Δ ⊢/ σ ∈ Γ → Δ ⊢ Vec.lookup x σ ∈ C.lookup x Γ / σ
  lookup x (σ⟨∈⟩Γ⊙σ , _) =
    subst (_⊢_∈_ _ _) (op-<$> (VecProp.lookup-morphism x) _ _)
          (All.lookup₂ x σ⟨∈⟩Γ⊙σ)


------------------------------------------------------------------------
-- Operations on abstract well-typed substitutions.

-- Extensions of abstract typed substitutions.

record RawTypedExtension {Tp₁ Tm₁ Tp₂ Tm₂}
                         (_⊢_wf : Wf Tp₂) (_⊢_∈_ : CtxTermRel Tp₂ Tm₁ Tp₁)
                         (application : Application Tp₁ Tm₂)
                         (weakenOps   : WeakenOps Tp₁)
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

  open VecProp using (map-cong; map-∘)

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
                        (gmap₂ (∈-weaken b-wf) σ⟨∈⟩Γ⊙ρ))

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
  open WeakenOps weakenOps

  -- Extension by a typed term.
  ∈-/∷ : ∀ {m n} {Γ : Ctx Tp₁ m} {Δ : Ctx Tp₂ n} {t a b σ} →
         b ∷ Δ ⊢ t ∈ weaken (a / σ) → Δ ⊢/ σ ∈ Γ →
         b ∷ Δ ⊢/ (t /∷ σ) ∈ a ∷ Γ
  ∈-/∷ {Γ = Γ} t∈a/σ (σ⟨∈⟩Γ⊙σ , _) = R.∈-/∷ {Γ = Γ} t∈a/σ σ⟨∈⟩Γ⊙σ , ∈-wf t∈a/σ

-- Abstract typed simple substitutions.

record RawTypedSimple {Tp Tm₁ Tm₂}
                      (_⊢_wf : Wf Tp) (_⊢_∈_ : CtxTermRel Tp Tm₁ Tp)
                      (application : Application Tp Tm₂)
                      (weakenOps   : WeakenOps Tp)
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
  open VecProp using (map-cong; map-id; map-∘)

  -- Context operations that require Tm₂ substitutions in Tp-types.
  substOps : SubstOps Tp Tm₂
  substOps = record { application = application; simple = simple₂ }

  open SubstOps substOps using (_E′/_)

  -- Some useful helper lemmas.

  ⊙-id : ∀ {m n} {ρ : Sub Tp m n} → ρ ⊙ S₂.id ≡ ρ
  ⊙-id {ρ = ρ} = begin
    Vec.map (_/ S₂.id) ρ  ≡⟨ VecProp.map-cong id-vanishes ρ ⟩
    Vec.map Fun.id     ρ  ≡⟨ VecProp.map-id ρ ⟩
    ρ                 ∎

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
  ∈-wk a-wf = gmap₂ (weaken′ a-wf) (∈-id′ (wf-wf a-wf))
    where
      weaken′ : ∀ {n} {Γ : Ctx Tp n} {t a b} → Γ ⊢ a wf → Γ ⊢ t ∈ b →
                (a ∷ Γ) ⊢ S₁.weaken t ∈ (b / S₂.wk)
      weaken′ a-wf = subst (_⊢_∈_ _ _) (sym /-wk) ∘ ∈-weaken a-wf

  -- A substitution which only replaces the first variable.
  ∈-sub : ∀ {n} {Γ : Ctx Tp n} {t u a} →
          Γ ⊢ t ∈ a → Γ ⊢ S₁.sub t ⟨ _⊢_∈_ ⟩ C.toVec (a ∷ Γ) ⊙ S₂.sub u
  ∈-sub t∈a =
    t∈a′ ∷ subst (_ ⊢ _ ⟨ _⊢_∈_ ⟩_) (VecProp.map-∘ (_/ S₂.sub _) C.weaken _)
                 (gmap₂₂ (subst (_⊢_∈_ _ _) (sym (weaken-sub-vanishes _)))
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
    hiding (rawTypedExtension; ∈-/∷; ∈-↑; ∈-id; ∈-wk; ∈-sub; ∈-tsub; ∈-↑⋆)
  open Simple simple hiding (weaken)
  open WeakenOps weakenOps
  open SubstOps  substOps  using (_E′/_)

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
module VarTyping {Tp} (weakenOps : WeakenOps Tp) (_⊢_wf : Wf Tp) where
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
    weakenOps   : WeakenOps Tp

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
      ∈-weaken a-wf (var x Γ-wf) =
        subst (_⊢Var_∈_ _ _) (op-<$> (VecProp.lookup-morphism x) _ _)
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


------------------------------------------------------------------------
-- Abstract context substitutions (i.e. context conversions)

-- Context-replacing substitutions.
record ContextSub (Tp₁ Tm Tp₂ : ℕ → Set) : Set₁ where
  infix 4 _⊢_∈_ _⊢_wf

  field
    _⊢_∈_ : Typing Tp₂ Tm Tp₁   -- the associated typing
    _⊢_wf : Wf Tp₂              -- (target) Tp₂-well-formedness

    -- Simple Tm-substitutions (e.g. id).
    simple : Simple Tm

    -- Operations on the (source) Tp₁-context.
    weakenOps : WeakenOps Tp₁

  open Simple    simple        using (id)
  open WeakenOps weakenOps     using (toVec)
  open WellFormedContext _⊢_wf using (_wf)

  infix  4 _⊢/id-∈_
  infixr 4 _,_

  -- Context-replacing substitutions.
  --
  -- An alternative representation for substitutions that only change
  -- the context of a well-typed Tm-term, i.e. where the underlying
  -- untyped substitution is the identity.
  data _⊢/id-∈_ {n} (Δ : Ctx Tp₂ n) (Γ : Ctx Tp₁ n) : Set where
    _,_ : All₂ (λ t a → Δ ⊢ t ∈ a) id (toVec Γ) → Δ wf → Δ ⊢/id-∈ Γ

  -- Project out the first component of a context substitution.
  proj₁ : ∀ {n} {Γ : Ctx Tp₁ n} {Δ : Ctx Tp₂ n} →
          Δ ⊢/id-∈ Γ → All₂ (λ t a → Δ ⊢ t ∈ a) id (toVec Γ)
  proj₁ (∈-id , _) = ∈-id

-- Equivalences between (simple) typed substitutions and their
-- context-replacing counterparts.
record Equivalence {Tp₁ Tm Tp₂}
                   (simple : Simple Tm)
                   (typedSub : TypedSub Tp₁ Tm Tp₂)
                   : Set where

  open TypedSub typedSub
  open Simple   simple

  -- The type of context substitutions participating in this
  -- equivalence.
  contextSub : ContextSub Tp₁ Tm Tp₂
  contextSub = record
    { _⊢_∈_     = _⊢_∈_
    ; _⊢_wf     = _⊢_wf
    ; simple    = simple
    ; weakenOps = weakenOps
    }

  open ContextSub contextSub hiding (_⊢_∈_)

  -- Types are invariant under the identity substitution.
  field id-vanishes : ∀ {n} (a : Tp₁ n) → a / id ≡ a

  -- The identity substitution is the right-identity of _⊙_.
  ⊙-id : ∀ {m n} {σ : Sub Tp₁ m n} → σ ⊙ id ≡ σ
  ⊙-id {σ = σ} = begin
    Vec.map (_/ id) σ   ≡⟨ VecProp.map-cong id-vanishes σ ⟩
    Vec.map Fun.id  σ   ≡⟨ VecProp.map-id σ ⟩
    σ               ∎

  -- There is a context substitution for every typed identity
  -- substitution.
  sound : ∀ {n} {Γ : Ctx Tp₁ n} {Δ : Ctx Tp₂ n} → Δ ⊢/id-∈ Γ → Δ ⊢/ id ∈ Γ
  sound (id∈Γ , Δ-wf) =
    subst (_⊢_⟨ _⊢_∈_ ⟩_ _ _) (sym ⊙-id) id∈Γ , Δ-wf

  -- There is a context substitution for every typed identity
  -- substitution.
  complete : ∀ {n} {Γ : Ctx Tp₁ n} {Δ : Ctx Tp₂ n} → Δ ⊢/ id ∈ Γ → Δ ⊢/id-∈ Γ
  complete (id∈Γ , Δ-wf) =
    subst (_⊢_⟨ _⊢_∈_ ⟩_ _ _) ⊙-id id∈Γ , Δ-wf

-- Variants of some simple typed substitutions.
record ContextSimple {Tp Tm}
                     (simple : Simple Tm)
                     (typedSub : TypedSub Tp Tm Tp)
                     : Set where

  field typedSimple : TypedSimple simple typedSub

  open TypedSub typedSub hiding (_⊢_∈_; _⊢_wf)
  open TypedSimple typedSimple
  private
    module U = SimpleExt simple
    module C = WeakenOps weakenOps

  equivalence : Equivalence simple typedSub
  equivalence = record { id-vanishes = id-vanishes }

  open Equivalence equivalence public
  open ContextSub  contextSub  public

  -- Extension.
  ctx-/∷ : ∀ {n} {Γ : Ctx Tp n} {Δ : Ctx Tp n} {a b} →
           b ∷ Δ ⊢ U.var zero ∈ C.weaken a → Δ ⊢/id-∈ Γ → b ∷ Δ ⊢/id-∈ a ∷ Γ
  ctx-/∷ z∈a (∈-id , Δ-wf) =
    z∈a ∷ gmap₂ (∈-weaken (wf-∷₁ b∷Δ-wf)) ∈-id , b∷Δ-wf
    where b∷Δ-wf = ∈-wf z∈a

  -- Lifting.
  ctx-↑ : ∀ {n} {Γ : Ctx Tp n} {Δ : Ctx Tp n} → Δ ⊢/id-∈ Γ →
          ∀ {a} → Δ ⊢ a wf → a ∷ Δ ⊢/id-∈ a ∷ Γ
  ctx-↑ id∈Γ a-wf = ctx-/∷ (∈-var zero (a-wf ∷ wf-wf a-wf)) id∈Γ

  -- The identity substitution.
  ctx-id : ∀ {n} {Γ : Ctx Tp n} → Γ wf → Γ ⊢/id-∈ Γ
  ctx-id Γ-wf = complete (∈-id Γ-wf)
