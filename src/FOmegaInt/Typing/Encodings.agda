------------------------------------------------------------------------
-- Encodings and properties of higher-order extrema and intervals in
-- Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Typing.Encodings where

open import Data.Fin using (zero)
open import Data.Nat using (suc)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality

open import FOmegaInt.Syntax
open import FOmegaInt.Kinding.Declarative
open import FOmegaInt.Kinding.Declarative.Validity

open Syntax       hiding (⌈_⌉)
open TermCtx
open Substitution hiding (subst)
open Kinding
open KindedSubstitution


----------------------------------------------------------------------
-- Injection of simple kinds into kinds.

-- For every simple kind `k' there is a kind `⌈ k ⌉' that simplifies
-- back to `k', i.e. `⌈_⌉' is a right inverse for `⌊_⌋'.
--
-- NOTE. The definition of the injection `⌈_⌉' is rather intuitive,
-- but it is neither the only right inverse of `⌊_⌋', nor even the
-- "most canonical" one.  Below we define two alternatives `⌈_⌉↓' and
-- `⌈_⌉↑' which, in addition to being right-inverse to `⌊_⌋', have
-- some appealing order-theoretic properties.

⌈_⌉ : ∀ {n} → SKind → Kind Term n
⌈ ★     ⌉ = *
⌈ j ⇒ k ⌉ = Π ⌈ j ⌉ ⌈ k ⌉

⌊⌋∘⌈⌉-id : ∀ {n} k → ⌊ ⌈_⌉ {n} k ⌋ ≡ k
⌊⌋∘⌈⌉-id ★       = refl
⌊⌋∘⌈⌉-id (j ⇒ k) = cong₂ _⇒_ (⌊⌋∘⌈⌉-id j) (⌊⌋∘⌈⌉-id k)

-- The kind `⌈ k ⌉' is well-formed (in any well-formed context).

⌈⌉-kd : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉ kd
⌈⌉-kd ★       Γ-ctx = *-kd Γ-ctx
⌈⌉-kd (j ⇒ k) Γ-ctx =
  let ⌈j⌉-kd = ⌈⌉-kd j Γ-ctx
  in kd-Π ⌈j⌉-kd (⌈⌉-kd k (wf-kd ⌈j⌉-kd ∷ Γ-ctx))


----------------------------------------------------------------------
-- Encodings and properties of extremal kinds.

-- The empty interval (note the use of absurd bounds).
∅ : ∀ {n} → Kind Term n
∅ = ⊤ ⋯ ⊥

-- Well-formedness of the empty interval kind.
∅-kd : ∀ {n} {Γ : Ctx n} → Γ ctx → Γ ⊢ ∅ kd
∅-kd Γ-ctx = kd-⋯ (∈-⊤-f Γ-ctx) (∈-⊥-f Γ-ctx)

-- Right-inverses of kind simplification: for every simple kind `k'
-- there are two canonical kinds `⌈ k ⌉↓' and `⌈ k ⌉↑', such that
--
--  1. `⌈_⌉↓' and `⌈_⌉↑' are right-inverses for `⌊_⌋', i.e. `⌈ k ⌉↓'
--     and `⌈ k ⌉↑' both simplify to `k',
--
--  2. `⌈ k ⌉↓' and `⌈ k ⌉↑' are limits, i.e. they are the least
--     resp. greatest kinds for which 1 holds.
--
-- NOTE. Rather than thinking of `⌈_⌉↓' and `⌈_⌉↑' as right-inverses
-- of kind simplifications, one may instead think of `⌊_⌋' as defining
-- a "kind space" `S(k, Γ) = { j | ⌊ j ⌋ ≡ k, Γ ⊢ j kd }' ordered by
-- subkinding, and interpret `⌈ k ⌉↓' and `⌈ k ⌉↑' as the extrema of
-- the space `S(k, Γ)' associated with `k'.
mutual

  ⌈_⌉↓ : ∀ {n} → SKind → Kind Term n
  ⌈ ★     ⌉↓ = ∅
  ⌈ j ⇒ k ⌉↓ = Π ⌈ j ⌉↑ ⌈ k ⌉↓

  ⌈_⌉↑ : ∀ {n} → SKind → Kind Term n
  ⌈ ★     ⌉↑ = *
  ⌈ j ⇒ k ⌉↑ = Π ⌈ j ⌉↓ ⌈ k ⌉↑


mutual

  -- Proof of point 1 above: `⌈_⌉↓' and `⌈_⌉↑' are right-inverses of
  -- `⌊_⌋'.

  ⌊⌋∘⌈⌉↓-id : ∀ {n} k → ⌊ ⌈_⌉↓ {n} k ⌋ ≡ k
  ⌊⌋∘⌈⌉↓-id ★       = refl
  ⌊⌋∘⌈⌉↓-id (j ⇒ k) = cong₂ _⇒_ (⌊⌋∘⌈⌉↑-id j) (⌊⌋∘⌈⌉↓-id k)

  ⌊⌋∘⌈⌉↑-id : ∀ {n} k → ⌊ ⌈_⌉↑ {n} k ⌋ ≡ k
  ⌊⌋∘⌈⌉↑-id ★       = refl
  ⌊⌋∘⌈⌉↑-id (j ⇒ k) = cong₂ _⇒_ (⌊⌋∘⌈⌉↓-id j) (⌊⌋∘⌈⌉↑-id k)

mutual

  -- `⌈ k ⌉↓' and `⌈ k ⌉↑' are well-formed (in any well-formed
  -- context).

  ⌈⌉↓-kd : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉↓ kd
  ⌈⌉↓-kd ★       Γ-ctx = ∅-kd Γ-ctx
  ⌈⌉↓-kd (j ⇒ k) Γ-ctx =
    let ⌈j⌉↑-kd = ⌈⌉↑-kd j Γ-ctx
    in kd-Π ⌈j⌉↑-kd (⌈⌉↓-kd k (wf-kd ⌈j⌉↑-kd ∷ Γ-ctx))

  ⌈⌉↑-kd : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉↑ kd
  ⌈⌉↑-kd ★       Γ-ctx = *-kd Γ-ctx
  ⌈⌉↑-kd (j ⇒ k) Γ-ctx =
    let ⌈j⌉↓-kd = ⌈⌉↓-kd j Γ-ctx
    in kd-Π ⌈j⌉↓-kd (⌈⌉↑-kd k (wf-kd ⌈j⌉↓-kd ∷ Γ-ctx))

mutual

  -- Proof of point 2 above: `⌈ k ⌉↓' and `⌈ k ⌉↑' are the least
  -- resp. greatest (well-formed) kinds that simplify to `k'.

  ⌈⌉↑-maximum : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ k <∷ ⌈ ⌊ k ⌋ ⌉↑
  ⌈⌉↑-maximum (kd-⋯ a∈* b∈*)       = <∷-⋯ (<:-⊥ a∈*) (<:-⊤ b∈*)
  ⌈⌉↑-maximum (kd-Π {j} j-kd k-kd) =
    let ⌈⌊j⌋⌉↓-kd = ⌈⌉↓-kd ⌊ j ⌋ (kd-ctx j-kd)
        ⌈⌊j⌋⌉↓<∷j = ⌈⌉↓-minimum j-kd
    in <∷-Π ⌈⌊j⌋⌉↓<∷j (⌈⌉↑-maximum (⇓-kd ⌈⌊j⌋⌉↓-kd ⌈⌊j⌋⌉↓<∷j k-kd))
            (kd-Π j-kd k-kd)

  ⌈⌉↓-minimum : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ k kd → Γ ⊢ ⌈ ⌊ k ⌋ ⌉↓ <∷ k
  ⌈⌉↓-minimum (kd-⋯ a∈* b∈*)   = <∷-⋯ (<:-⊤ a∈*) (<:-⊥ b∈*)
  ⌈⌉↓-minimum (kd-Π {j} {k} j-kd k-kd) =
    <∷-Π (⌈⌉↑-maximum j-kd) (⌈⌉↓-minimum k-kd) (⌈⌉↓-kd ⌊ Π j k ⌋ (kd-ctx j-kd))

-- Some corollaries.

-- Minima are subkinds of maxima.
⌈⌉↓<∷⌈⌉↑ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉↓ <∷ ⌈ k ⌉↑
⌈⌉↓<∷⌈⌉↑ k Γ-ctx =
  subst (_ ⊢ ⌈ k ⌉↓ <∷_) (cong ⌈_⌉↑ (⌊⌋∘⌈⌉↓-id k))
        (⌈⌉↑-maximum (⌈⌉↓-kd k Γ-ctx))

-- Minima are subkinds of the "intuitively" injected simple kinds.
⌈⌉↓<∷⌈⌉ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉↓ <∷ ⌈ k ⌉
⌈⌉↓<∷⌈⌉ k Γ-ctx =
  subst (_ ⊢_<∷ ⌈ k ⌉) (cong ⌈_⌉↓ (⌊⌋∘⌈⌉-id k))
        (⌈⌉↓-minimum (⌈⌉-kd k Γ-ctx))

-- Maxima are superkinds of the "intuitively" injected simple kinds.
⌈⌉<∷⌈⌉↑ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢ ⌈ k ⌉ <∷ ⌈ k ⌉↑
⌈⌉<∷⌈⌉↑ k Γ-ctx =
  subst (_ ⊢ ⌈ k ⌉ <∷_) (cong ⌈_⌉↑ (⌊⌋∘⌈⌉-id k))
        (⌈⌉↑-maximum (⌈⌉-kd k Γ-ctx))

-- Every well-kinded type inhabits the maximum kind associated with
-- its simple kind.
∈-⇑-⌈⌉↑ : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢Tp a ∈ ⌈ ⌊ k ⌋ ⌉↑
∈-⇑-⌈⌉↑ a∈k = ∈-⇑ a∈k (⌈⌉↑-maximum (Tp∈-valid a∈k))


----------------------------------------------------------------------
-- Encodings and properties of higher-order extrema

-- Higher order extremal types.

⊥⟨_⟩ : ∀ {n} → SKind → Term n
⊥⟨ ★ ⟩     = ⊥
⊥⟨ j ⇒ k ⟩ = Λ ⌈ j ⌉ ⊥⟨ k ⟩

⊤⟨_⟩ : ∀ {n} → SKind → Term n
⊤⟨ ★ ⟩     = ⊤
⊤⟨ j ⇒ k ⟩ = Λ ⌈ j ⌉ ⊤⟨ k ⟩

-- ⊥⟨ k ⟩ and ⊤⟨ k ⟩ inhabit ⌈ k ⌉.

∈-⊥⟨⟩ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢Tp ⊥⟨ k ⟩ ∈ ⌈ k ⌉
∈-⊥⟨⟩ ★       Γ-ctx = ∈-⊥-f Γ-ctx
∈-⊥⟨⟩ (j ⇒ k) Γ-ctx =
  let ⌈j⌉-kd = ⌈⌉-kd j Γ-ctx
      ⌈j⌉∷Γ  = wf-kd ⌈j⌉-kd ∷ Γ-ctx
      ⌈k⌉-kd = ⌈⌉-kd k ⌈j⌉∷Γ
  in ∈-Π-i ⌈j⌉-kd (∈-⊥⟨⟩ k ⌈j⌉∷Γ) ⌈k⌉-kd

∈-⊤⟨⟩ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢Tp ⊤⟨ k ⟩ ∈ ⌈ k ⌉
∈-⊤⟨⟩ ★       Γ-ctx = ∈-⊤-f Γ-ctx
∈-⊤⟨⟩ (j ⇒ k) Γ-ctx =
  let ⌈j⌉-kd = ⌈⌉-kd j Γ-ctx
      ⌈j⌉∷Γ  = wf-kd ⌈j⌉-kd ∷ Γ-ctx
      ⌈k⌉-kd = ⌈⌉-kd k ⌈j⌉∷Γ
  in ∈-Π-i ⌈j⌉-kd (∈-⊤⟨⟩ k ⌈j⌉∷Γ) ⌈k⌉-kd

-- ⊥⟨ k ⟩ and ⊤⟨ k ⟩ are extremal types in ⌈ k ⌉.

⊥⟨⟩-minimum : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢Tp a ∈ ⌈ k ⌉ → Γ ⊢ ⊥⟨ k ⟩ <: a ∈ ⌈ k ⌉
⊥⟨⟩-minimum {k = ★    } a∈*     = <:-⊥ a∈*
⊥⟨⟩-minimum {k = j ⇒ k} a∈⌈j⇒k⌉ =
  <:-trans (<:-λ (⊥⟨⟩-minimum a·z∈⌈k⌉) (∈-⊥⟨⟩ (j ⇒ k) Γ-ctx) Λa·z∈⌈j⇒k⌉)
           (<:-η₁ a∈⌈j⇒k⌉)
  where
    Γ-ctx  = Tp∈-ctx a∈⌈j⇒k⌉
    ⌈j⌉-kd = ⌈⌉-kd j Γ-ctx
    ⌈k⌉-kd = ⌈⌉-kd k (wf-kd ⌈j⌉-kd ∷ Γ-ctx)
    Λa·z∈⌈j⇒k⌉ = Tp∈-η a∈⌈j⇒k⌉ ⌈j⌉-kd ⌈k⌉-kd
    a·z∈⌈k⌉    = proj₂ (Tp∈-Λ-inv Λa·z∈⌈j⇒k⌉)

⊤⟨⟩-maximum : ∀ {n} {Γ : Ctx n} {a k} →
              Γ ⊢Tp a ∈ ⌈ k ⌉ → Γ ⊢ a <: ⊤⟨ k ⟩ ∈ ⌈ k ⌉
⊤⟨⟩-maximum {k = ★    } a∈*     = <:-⊤ a∈*
⊤⟨⟩-maximum {k = j ⇒ k} a∈⌈j⇒k⌉ =
  <:-trans (<:-η₂ a∈⌈j⇒k⌉)
           (<:-λ (⊤⟨⟩-maximum a·z∈⌈k⌉) Λa·z∈⌈j⇒k⌉ (∈-⊤⟨⟩ (j ⇒ k) Γ-ctx))
  where
    Γ-ctx  = Tp∈-ctx a∈⌈j⇒k⌉
    ⌈j⌉-kd = ⌈⌉-kd j Γ-ctx
    ⌈k⌉-kd = ⌈⌉-kd k (wf-kd ⌈j⌉-kd ∷ Γ-ctx)
    Λa·z∈⌈j⇒k⌉ = Tp∈-η a∈⌈j⇒k⌉ ⌈j⌉-kd ⌈k⌉-kd
    a·z∈⌈k⌉    = proj₂ (Tp∈-Λ-inv Λa·z∈⌈j⇒k⌉)

-- An alternate pair of higher-order extremal types inhabiting the
-- family of kinds ⌈ k ⌉↑, rather than ⌈ k ⌉.

⊥↑⟨_⟩ : ∀ {n} → SKind → Term n
⊥↑⟨ ★ ⟩     = ⊥
⊥↑⟨ j ⇒ k ⟩ = Λ ⌈ j ⌉↑ ⊥↑⟨ k ⟩

⊤↑⟨_⟩ : ∀ {n} → SKind → Term n
⊤↑⟨ ★ ⟩     = ⊤
⊤↑⟨ j ⇒ k ⟩ = Λ ⌈ j ⌉↑ ⊤↑⟨ k ⟩

-- ⊥↑⟨ k ⟩ and ⊤↑⟨ k ⟩ inhabit ⌈ k ⌉↑.

∈-⊥↑⟨⟩ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢Tp ⊥↑⟨ k ⟩ ∈ ⌈ k ⌉↑
∈-⊥↑⟨⟩ ★       Γ-ctx = ∈-⊥-f Γ-ctx
∈-⊥↑⟨⟩ (j ⇒ k) Γ-ctx =
  let ⌈j⌉↑-kd = ⌈⌉↑-kd j Γ-ctx
      ⌈j⌉↑∷Γ  = wf-kd ⌈j⌉↑-kd ∷ Γ-ctx
      ⌈k⌉↑-kd = ⌈⌉↑-kd k ⌈j⌉↑∷Γ
  in ∈-⇑ (∈-Π-i ⌈j⌉↑-kd (∈-⊥↑⟨⟩ k ⌈j⌉↑∷Γ) ⌈k⌉↑-kd)
         (<∷-Π (⌈⌉↓<∷⌈⌉↑ j Γ-ctx)
               (<∷-refl (⌈⌉↑-kd k ((wf-kd (⌈⌉↓-kd j Γ-ctx)) ∷ Γ-ctx)))
               (kd-Π ⌈j⌉↑-kd ⌈k⌉↑-kd))

∈-⊤↑⟨⟩ : ∀ {n} {Γ : Ctx n} k → Γ ctx → Γ ⊢Tp ⊤↑⟨ k ⟩ ∈ ⌈ k ⌉↑
∈-⊤↑⟨⟩ ★       Γ-ctx = ∈-⊤-f Γ-ctx
∈-⊤↑⟨⟩ (j ⇒ k) Γ-ctx =
  let ⌈j⌉↑-kd = ⌈⌉↑-kd j Γ-ctx
      ⌈j⌉↑∷Γ  = wf-kd ⌈j⌉↑-kd ∷ Γ-ctx
      ⌈k⌉↑-kd = ⌈⌉↑-kd k ⌈j⌉↑∷Γ
  in ∈-⇑ (∈-Π-i ⌈j⌉↑-kd (∈-⊤↑⟨⟩ k ⌈j⌉↑∷Γ) ⌈k⌉↑-kd)
         (<∷-Π (⌈⌉↓<∷⌈⌉↑ j Γ-ctx)
               (<∷-refl (⌈⌉↑-kd k ((wf-kd (⌈⌉↓-kd j Γ-ctx)) ∷ Γ-ctx)))
               (kd-Π ⌈j⌉↑-kd ⌈k⌉↑-kd))

-- ⊥↑⟨ k ⟩ and ⊤↑⟨ k ⟩ are extremal types in ⌈ k ⌉↑.

⊥↑⟨⟩-minimum : ∀ {n} {Γ : Ctx n} {a k} →
               Γ ⊢Tp a ∈ k → Γ ⊢ ⊥↑⟨ ⌊ k ⌋ ⟩ <: a ∈ ⌈ ⌊ k ⌋ ⌉↑
⊥↑⟨⟩-minimum {k = b ⋯ c} a∈b⋯c = <:-⊥ a∈b⋯c
⊥↑⟨⟩-minimum {k = Π j k} a∈Πjk with Tp∈-valid a∈Πjk
... | kd-Π j-kd k-kd =
  <:-trans (<:-λ (⊥↑⟨⟩-minimum a·z∈k′) (∈-⊥↑⟨⟩ ⌊ Π j k ⌋ Γ-ctx)
                 (∈-⇑ Λa·z∈Πjk Πjk<∷⌈Πjk⌉↑))
           (<:-⇑ (<:-η₁ a∈Πjk) Πjk<∷⌈Πjk⌉↑)
  where
    Πjk<∷⌈Πjk⌉↑ = ⌈⌉↑-maximum (kd-Π j-kd k-kd)
    Γ-ctx       = Tp∈-ctx a∈Πjk
    ⌈⌊j⌋⌉↓-kd   = ⌈⌉↓-kd ⌊ j ⌋ Γ-ctx
    ⌈⌊j⌋⌉↓<∷j   = ⌈⌉↓-minimum j-kd
    Λa·z∈Πjk    = Tp∈-η a∈Πjk j-kd k-kd
    a·z∈k       = proj₂ (Tp∈-Λ-inv Λa·z∈Πjk)
    a·z∈k′      = ⇓-Tp∈ ⌈⌊j⌋⌉↓-kd ⌈⌊j⌋⌉↓<∷j a·z∈k

⊤↑⟨⟩-maximum : ∀ {n} {Γ : Ctx n} {a k} →
               Γ ⊢Tp a ∈ k → Γ ⊢ a <: ⊤↑⟨ ⌊ k ⌋ ⟩ ∈ ⌈ ⌊ k ⌋ ⌉↑
⊤↑⟨⟩-maximum {k = b ⋯ c} a∈b⋯c = <:-⊤ a∈b⋯c
⊤↑⟨⟩-maximum {k = Π j k} a∈Πjk with Tp∈-valid a∈Πjk
... | kd-Π j-kd k-kd =
  <:-trans (<:-⇑ (<:-η₂ a∈Πjk) Πjk<∷⌈Πjk⌉↑)
           (<:-λ (⊤↑⟨⟩-maximum a·z∈k′) (∈-⇑ Λa·z∈Πjk Πjk<∷⌈Πjk⌉↑)
                 (∈-⊤↑⟨⟩ ⌊ Π j k ⌋ Γ-ctx))
  where
    Πjk<∷⌈Πjk⌉↑ = ⌈⌉↑-maximum (kd-Π j-kd k-kd)
    Γ-ctx       = Tp∈-ctx a∈Πjk
    ⌈⌊j⌋⌉↓-kd   = ⌈⌉↓-kd ⌊ j ⌋ Γ-ctx
    ⌈⌊j⌋⌉↓<∷j   = ⌈⌉↓-minimum j-kd
    Λa·z∈Πjk    = Tp∈-η a∈Πjk j-kd k-kd
    a·z∈k       = proj₂ (Tp∈-Λ-inv Λa·z∈Πjk)
    a·z∈k′      = ⇓-Tp∈ ⌈⌊j⌋⌉↓-kd ⌈⌊j⌋⌉↓<∷j a·z∈k


----------------------------------------------------------------------
-- Encodings and properties of higher-order intervals

infix 6 _⋯⟨_⟩_

-- Higher-order interval kinds.
_⋯⟨_⟩_ : ∀ {n} → Term n → Kind Term n → Term n → Kind Term n
a ⋯⟨ c ⋯ d ⟩ b = a ⋯ b
a ⋯⟨ Π j k ⟩ b = Π j (weaken a · var zero ⋯⟨ k ⟩ weaken b · var zero)

-- Higher order interval kinds simplify as their kind-indices.

⌊⌋-⋯⟨⟩ : ∀ {n} {a b : Term n} k → ⌊ a ⋯⟨ k ⟩ b ⌋ ≡ ⌊ k ⌋
⌊⌋-⋯⟨⟩ (a ⋯ b) = refl
⌊⌋-⋯⟨⟩ (Π j k) = cong (⌊ j ⌋ ⇒_) (⌊⌋-⋯⟨⟩ k)

-- "Idempotence" of higher order interval kinds.

⋯⟨⟩-idempotent : ∀ {n} {a b : Term n} k → a ⋯⟨ a ⋯⟨ k ⟩ b ⟩ b ≡ a ⋯⟨ k ⟩ b
⋯⟨⟩-idempotent (a ⋯ b) = refl
⋯⟨⟩-idempotent (Π j k) = cong (Π j) (⋯⟨⟩-idempotent k)

-- Well-formedness of higher-order interval kinds.
kd-⋯⟨⟩ : ∀ {n} {Γ : Ctx n} {a b k} →
         Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ k → Γ ⊢ a ⋯⟨ k ⟩ b kd
kd-⋯⟨⟩ a∈k   b∈k   with Tp∈-valid a∈k
kd-⋯⟨⟩ a∈c⋯d b∈c⋯d | kd-⋯ _ _       = kd-⋯ (Tp∈-⋯-* a∈c⋯d) (Tp∈-⋯-* b∈c⋯d)
kd-⋯⟨⟩ a∈Πjk b∈Πjk | kd-Π j-kd k-kd =
  kd-Π j-kd (kd-⋯⟨⟩ a·z∈k b·z∈k)
  where
    a·z∈k = proj₂ (Tp∈-Λ-inv (Tp∈-η a∈Πjk j-kd k-kd))
    b·z∈k = proj₂ (Tp∈-Λ-inv (Tp∈-η b∈Πjk j-kd k-kd))

-- NOTE.  We would like to show that the inverse of the above also
-- holds, i.e. that given a well-formed higher-order interval kind `a
-- ⋯⟨ k ⟩ b', we have `a ∈ k' and `b ∈ k'.  Unfortunately this is not
-- true because the definition of `a ⋯⟨ k ⟩ b' is a bit too forgetful
-- when the kind-index `k' is itself an interval `k = c ⋯ d', that is,
-- when `a' and `b' are proper types.  E.g. the kind `⊥ ⋯⟨ ∅ ⟩ ⊤' is
-- well-formed, but clearly `⊥ , ⊤ ∉ ø'.
--
-- However, as following lemma illustrates, we can invert some
-- judgments about higher-order intervals with "sensible"
-- kind-indices, such as those resulting from simple kinds via ⌈_⌉.
-- Still, a proper inversion lemma would require more work, in
-- particular one has to contract the kinding derivations of the
-- η-expanded bounds `a' and `b' back into their non-expanded form.

-- Higher-order interval kinds indexed by `⌈ k ⌉' for some `k' are
-- subkinds of `⌈ k ⌉'.
⋯⟨⌈⌉⟩-<∷-⌈⌉ : ∀ {n} {Γ : Ctx n} {a b k} →
              Γ ⊢ a ⋯⟨ ⌈ k ⌉ ⟩ b kd → Γ ⊢ a ⋯⟨ ⌈ k ⌉ ⟩ b <∷ ⌈ k ⌉
⋯⟨⌈⌉⟩-<∷-⌈⌉ {k = ★    } (kd-⋯ a∈* b∈*) = <∷-⋯ (<:-⊥ a∈*) (<:-⊤ b∈*)
⋯⟨⌈⌉⟩-<∷-⌈⌉ {k = j ⇒ k} (kd-Π ⌈j⌉-kd a·z⋯⟨⌈k⌉⟩b·z-kd) =
  <∷-Π (<∷-refl ⌈j⌉-kd) (⋯⟨⌈⌉⟩-<∷-⌈⌉ a·z⋯⟨⌈k⌉⟩b·z-kd)
       (kd-Π ⌈j⌉-kd a·z⋯⟨⌈k⌉⟩b·z-kd)

-- Two corollaries.

-- Types inhabiting a type interval indexed by a simple kind `k' also
-- inhabit `⌈ k ⌉`.
Tp∈-⋯⟨⌈⌉⟩-inv : ∀ {n} {Γ : Ctx n} {a b c k} →
                Γ ⊢Tp a ∈ b ⋯⟨ ⌈ k ⌉ ⟩ c → Γ ⊢Tp a ∈ ⌈ k ⌉
Tp∈-⋯⟨⌈⌉⟩-inv a∈b⋯⟨⌈k⌉⟩c =
  ∈-⇑ a∈b⋯⟨⌈k⌉⟩c (⋯⟨⌈⌉⟩-<∷-⌈⌉ (Tp∈-valid a∈b⋯⟨⌈k⌉⟩c))

-- Types related in a type interval indexed by a simple kind `k' are
-- also related in `⌈ k ⌉`.
<:-⋯⟨⌈⌉⟩-inv : ∀ {n} {Γ : Ctx n} {a b c d k} →
               Γ ⊢ a <: b ∈ c ⋯⟨ ⌈ k ⌉ ⟩ d → Γ ⊢ a <: b ∈ ⌈ k ⌉
<:-⋯⟨⌈⌉⟩-inv a<:b∈c⋯⟨⌈k⌉⟩d =
  <:-⇑ a<:b∈c⋯⟨⌈k⌉⟩d (⋯⟨⌈⌉⟩-<∷-⌈⌉ (<:-valid-kd a<:b∈c⋯⟨⌈k⌉⟩d))

-- Subkinding of higher-order interval kinds.
<∷-⋯⟨⟩ : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ k} →
         Γ ⊢ a₂ <: a₁ ∈ k → Γ ⊢ b₁ <: b₂ ∈ k → Γ ⊢ a₁ ⋯⟨ k ⟩ b₁ <∷ a₂ ⋯⟨ k ⟩ b₂
<∷-⋯⟨⟩ a₂<:a₁∈k   b₁<:b₂∈k   with <:-valid-kd a₂<:a₁∈k
<∷-⋯⟨⟩ a₂<:a₁∈c⋯d b₁<:b₂∈c⋯d | kd-⋯ _ _ =
  <∷-⋯ (<:-⋯-* a₂<:a₁∈c⋯d) (<:-⋯-* b₁<:b₂∈c⋯d)
<∷-⋯⟨⟩ a₂<:a₁∈Πjk b₁<:b₂∈Πjk | kd-Π j-kd k-kd =
  let module TR = KindedRenaming

      a₂∈Πjk , a₁∈Πjk = <:-valid a₂<:a₁∈Πjk
      b₁∈Πjk , b₂∈Πjk = <:-valid b₁<:b₂∈Πjk
      Γ-ctx   = kd-ctx j-kd
      j-wf    = wf-kd j-kd
      j∷Γ-ctx = j-wf ∷ Γ-ctx
      j-kd′   = kd-weaken j-wf j-kd
      k-kd′   = TR.kd-/ k-kd (TR.∈-↑ (wf-kd j-kd′) (TR.∈-wk j-wf))
      z∈k     = ∈-var zero j∷Γ-ctx refl
      z≃z∈k   = ≃-refl z∈k
      a₂<:a₁∈Πjk′ = <:-weaken j-wf a₂<:a₁∈Πjk
      b₁<:b₂∈Πjk′ = <:-weaken j-wf b₁<:b₂∈Πjk
      k[z]-kd     = kd-[] k-kd′ (∈-tp z∈k)
      k[z]≡k      = Kind-wk↑-sub-zero-vanishes _
      a₂·z<:a₁·z∈k[z] = <:-· a₂<:a₁∈Πjk′ z≃z∈k z∈k k-kd′ k[z]-kd
      b₁·z<:b₂·z∈k[z] = <:-· b₁<:b₂∈Πjk′ z≃z∈k z∈k k-kd′ k[z]-kd
      a₂·z<:a₁·z∈k = subst (_ ⊢ _ <: _ ∈_) k[z]≡k a₂·z<:a₁·z∈k[z]
      b₁·z<:b₂·z∈k = subst (_ ⊢ _ <: _ ∈_) k[z]≡k b₁·z<:b₂·z∈k[z]
  in <∷-Π (<∷-refl j-kd)
          (<∷-⋯⟨⟩ a₂·z<:a₁·z∈k b₁·z<:b₂·z∈k)
          (kd-⋯⟨⟩ a₁∈Πjk b₁∈Πjk)

-- A variant of kind-driven η-expansion that only expands the head.
η-exp : ∀ {n} → Kind Term n → Term n → Term n
η-exp (_ ⋯ _) a = a
η-exp (Π j k) a = Λ j (η-exp k (weaken a · var zero))

-- Soundness of η-expansion.
≃-η-exp : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ a ≃ η-exp k a ∈ k
≃-η-exp {_} {_} {_} {b ⋯ c} a∈b⋯c = ≃-refl a∈b⋯c
≃-η-exp {_} {_} {a} {Π j k} a∈Πjk with Tp∈-valid a∈Πjk
... | kd-Π j-kd k-kd = begin
  a                                     ≃⟨ ≃-sym (≃-η a∈Πjk) ⟩
  Λ j (weaken a · var zero)             ≃⟨ ≃-λ′ (≅-refl j-kd) (≃-η-exp a·z∈k) ⟩
  Λ j (η-exp k (weaken a · var zero))   ∎
  where
    open ≃-Reasoning
    a·z∈k = proj₂ (Tp∈-Λ-inv (Tp∈-η a∈Πjk j-kd k-kd))

-- A singleton introduction rule for higher-order interval kinds.
∈-s⟨⟩-i : ∀ {n} {Γ : Ctx n} {a k} →
          Γ ⊢Tp a ∈ k → Γ ⊢Tp η-exp k a ∈ a ⋯⟨ k ⟩ a
∈-s⟨⟩-i a∈k   with Tp∈-valid a∈k
∈-s⟨⟩-i a∈b⋯c | kd-⋯ _ _       = ∈-s-i a∈b⋯c
∈-s⟨⟩-i a∈Πjk | kd-Π j-kd k-kd =
  ∈-Π-i j-kd (∈-s⟨⟩-i a·z∈k) (kd-⋯⟨⟩ a·z∈k a·z∈k)
  where
    a·z∈k = proj₂ (Tp∈-Λ-inv (Tp∈-η a∈Πjk j-kd k-kd))

-- A corollary: we can kind (the η-expansion of) a type with explicit
-- lower and uper bounds in the interval defined by these bounds.
Tp∈-<:-⋯ : ∀ {n} {Γ : Ctx n} {a b c k} →
           Γ ⊢Tp a ∈ k → Γ ⊢ b <: a ∈ k → Γ ⊢ a <: c ∈ k →
           Γ ⊢Tp η-exp k a ∈ b ⋯⟨ k ⟩ c
Tp∈-<:-⋯ a∈k b<:a∈k a<:c∈k = ∈-⇑ (∈-s⟨⟩-i a∈k) (<∷-⋯⟨⟩ b<:a∈k a<:c∈k)

-- Bound projection rules for higher-order intervals.
--
-- NOTE.  These lemmas are a bit weaker than one might like.  In
-- particular, the addtional presmise `Γ ⊢ a , b , c ∈ k' might seem
-- redundant.  But recall that we cannot, in general, invert
-- well-formed higher-order intervals, i.e. `Γ ⊢ b ⋯⟨ k ⟩ c kd' does
-- *not* imply `Γ ⊢ b ∈ k' and `Γ ⊢ c ∈ k'.  Similarly, `Γ ⊢ a ∈ b ⋯⟨
-- k ⟩ c' does *not* imply `Γ ⊢ a ∈ k'.  To see this, consider again
-- the kind `⊥ ⋯⟨ ∅ ⟩ ⊤', which is well-formed and inhabited by both
-- `⊥' and `⊤', yet clearly `⊥ , ⊤ ∉ ø'.

<:-⋯⟨⟩-⟨|⟩ : ∀ {n} {Γ : Ctx n} {a b c k} →
             Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ k → Γ ⊢Tp c ∈ k →
             Γ ⊢Tp a ∈ b ⋯⟨ k ⟩ c → Γ ⊢ b <: a ∈ k × Γ ⊢ a <: c ∈ k
<:-⋯⟨⟩-⟨|⟩ a∈k   b∈k   c∈k   a∈b⋯⟨k⟩c       with Tp∈-valid a∈k
<:-⋯⟨⟩-⟨|⟩ a∈d⋯e b∈d⋯e c∈d⋯e a∈b⋯c          | kd-⋯ _ _ =
  <:-⇑ (<:-⋯-i (<:-⟨| a∈b⋯c)) (<∷-⋯ (<:-⟨| b∈d⋯e) (<:-|⟩ a∈d⋯e)) ,
  <:-⇑ (<:-⋯-i (<:-|⟩ a∈b⋯c)) (<∷-⋯ (<:-⟨| a∈d⋯e) (<:-|⟩ c∈d⋯e))
<:-⋯⟨⟩-⟨|⟩ a∈Πjk b∈Πjk c∈Πjk a∈Πjb·z⋯⟨k⟩c·z | kd-Π j-kd k-kd =
  let Λa·z∈Πjk  = Tp∈-η a∈Πjk j-kd k-kd
      Λb·z∈Πjk  = Tp∈-η b∈Πjk j-kd k-kd
      Λc·z∈Πjk  = Tp∈-η c∈Πjk j-kd k-kd
      _ , a·z∈k = Tp∈-Λ-inv Λa·z∈Πjk
      _ , b·z∈k = Tp∈-Λ-inv Λb·z∈Πjk
      _ , c·z∈k = Tp∈-Λ-inv Λc·z∈Πjk
      Λa·z∈Πjb·z⋯⟨k⟩c·z  = Tp∈-η a∈Πjb·z⋯⟨k⟩c·z j-kd (kd-⋯⟨⟩ b·z∈k c·z∈k)
      _ , a·z∈b·z⋯⟨k⟩c·z = Tp∈-Λ-inv Λa·z∈Πjb·z⋯⟨k⟩c·z
      b·z<:a·z∈k , a·z<:c·z∈k = <:-⋯⟨⟩-⟨|⟩ a·z∈k b·z∈k c·z∈k a·z∈b·z⋯⟨k⟩c·z
      Λjb·z<:Λja·z∈Πjk = <:-λ b·z<:a·z∈k Λb·z∈Πjk Λa·z∈Πjk
      Λja·z<:Λjc·z∈Πjk = <:-λ a·z<:c·z∈k Λa·z∈Πjk Λc·z∈Πjk
      Λja·z<:a∈kΠjk    = <:-η₁ a∈Πjk
      a<:Λja·z∈kΠjk    = <:-η₂ a∈Πjk
      Λjc·z<:c∈kΠjk    = <:-η₁ c∈Πjk
      b<:Λjb·z∈kΠjk    = <:-η₂ b∈Πjk
  in <:-trans (<:-trans b<:Λjb·z∈kΠjk Λjb·z<:Λja·z∈Πjk) Λja·z<:a∈kΠjk ,
     <:-trans (<:-trans a<:Λja·z∈kΠjk Λja·z<:Λjc·z∈Πjk) Λjc·z<:c∈kΠjk

<:-⋯⟨⟩-⟨| : ∀ {n} {Γ : Ctx n} {a b c k} →
            Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ k → Γ ⊢Tp c ∈ k →
            Γ ⊢Tp a ∈ b ⋯⟨ k ⟩ c → Γ ⊢ b <: a ∈ k
<:-⋯⟨⟩-⟨| a∈k b∈k c∈k a∈b⋯⟨k⟩c = proj₁ (<:-⋯⟨⟩-⟨|⟩ a∈k b∈k c∈k a∈b⋯⟨k⟩c)

<:-⋯⟨⟩-|⟩ : ∀ {n} {Γ : Ctx n} {a b c k} →
            Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ k → Γ ⊢Tp c ∈ k →
            Γ ⊢Tp a ∈ b ⋯⟨ k ⟩ c → Γ ⊢ a <: c ∈ k
<:-⋯⟨⟩-|⟩ a∈k b∈k c∈k a∈b⋯⟨k⟩c = proj₂ (<:-⋯⟨⟩-⟨|⟩ a∈k b∈k c∈k a∈b⋯⟨k⟩c)


----------------------------------------------------------------------
-- Encodings and admissible kinding rules of bounded quantifiers

-- Bounded universal quantifiers.
∀′ : ∀ {n} → Term n → Term n → Kind Term n → Term (suc n) → Term n
∀′ a b k c = Π (a ⋯⟨ k ⟩ b) c

-- Bounded universal quantifier abstraction.
Λ′ : ∀ {n} → Term n → Term n → Kind Term n → Term (suc n) → Term n
Λ′ a b k c = Λ (a ⋯⟨ k ⟩ b) c

-- A formation rule for bounded universal quantifiers.
∈-∀′-f : ∀ {n} {Γ : Ctx n} {a b k c} →
         Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ k → kd (a ⋯⟨ k ⟩ b) ∷ Γ ⊢Tp c ∈ * →
         Γ ⊢Tp ∀′ a b k c ∈ *
∈-∀′-f a∈k b∈k c∈* = ∈-∀-f (kd-⋯⟨⟩ a∈k b∈k) c∈*

-- TODO.  We also want to show that there are admissible introduction
-- and elimination rules for bounded quantifiers.  To do so, we need
-- to first re-write the above development so it uses the kinding
-- rules defined in FOmegaInt.Typing rather than those from
-- FOmegaInt.Kinding.Declarative.  This will require "transporting"
-- some lemmas about declarative kinding (in particular validity
-- lemmas) via the equivalence of the two presentations.
