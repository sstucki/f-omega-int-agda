------------------------------------------------------------------------
-- Validity of declarative kinding of Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Declarative.Validity where

open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Product as Prod using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Vec as Vec using ([]; _∷_)
open import Data.Vec.All as VecAll using (All₂; []; _∷_)
open import Data.Vec.All.Properties using (gmap; gmap₂)
open import Data.Star using (ε; _◅_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Relation.Nullary.Negation using (contradiction)

open import FOmegaInt.Syntax
open import FOmegaInt.Kinding.Declarative
open import FOmegaInt.Reduction.Full


------------------------------------------------------------------------
-- Validity of declarative kinding, subkinding and subtyping

open Syntax
open Substitution hiding (subst)
open TermCtx
open Kinding
open WfCtxOps using (lookup-kd)
open KindedSubstitution
open KindedParallelSubstitution

-- An admissible rule for kinding η-expanded type operators.
Tp∈-η : ∀ {n} {Γ : Ctx n} {a j k} →
        Γ ⊢Tp a ∈ Π j k → Γ ⊢ j kd → kd j ∷ Γ ⊢ k kd →
        Γ ⊢Tp Λ j (weaken a · var zero) ∈ Π j k
Tp∈-η {k = k} a∈Πjk j-kd k-kd =
  ∈-Π-i j-kd (subst (_ ⊢Tp _ ∈_) k′[z]≡k (∈-Π-e a∈Πjk′ z∈k k-kd′ k[z]-kd)) k-kd
  where
    open ≡-Reasoning
    module TR = KindedRenaming
    module KL = TermLikeLemmas termLikeLemmasKind

    j-wf    = wf-kd j-kd
    j-kd′   = kd-weaken j-wf j-kd
    k-kd′   = TR.kd-/ k-kd (TR.∈-↑ (wf-kd j-kd′) (TR.∈-wk j-wf))
    z∈k     = ∈-var zero (j-wf ∷ kd-ctx j-kd) refl
    a∈Πjk′  = Tp∈-weaken j-wf a∈Πjk
    k[z]-kd = kd-[] k-kd′ (∈-tp z∈k)
    k′[z]≡k = Kind-wk↑-sub-zero-vanishes k

mutual

  -- Validity of kinding: the kinds of well-kinded types are well-formed.
  Tp∈-valid : ∀ {n} {Γ : Ctx n} {a k} → Γ ⊢Tp a ∈ k → Γ ⊢ k kd
  Tp∈-valid (∈-var x Γ-ctx Γ[x]≡kd-k) = lookup-kd x Γ-ctx Γ[x]≡kd-k
  Tp∈-valid (∈-⊥-f Γ-ctx)             = *-kd Γ-ctx
  Tp∈-valid (∈-⊤-f Γ-ctx)             = *-kd Γ-ctx
  Tp∈-valid (∈-∀-f k-kd a∈*)          = *-kd (kd-ctx k-kd)
  Tp∈-valid (∈-→-f a∈* b∈*)           = *-kd (Tp∈-ctx a∈*)
  Tp∈-valid (∈-Π-i j-kd a∈k k-kd)     = kd-Π j-kd (Tp∈-valid a∈k)
  Tp∈-valid (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) = k[b]-kd
  Tp∈-valid (∈-s-i a∈b⋯c)             = let a∈* = Tp∈-⋯-* a∈b⋯c in kd-⋯ a∈* a∈*
  Tp∈-valid (∈-⇑ a∈j j<∷k)            = proj₂ (<∷-valid j<∷k)

  -- Validity of subkinding: subkinds are well-formed.
  <∷-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j <∷ k → Γ ⊢ j kd × Γ ⊢ k kd
  <∷-valid (<∷-⋯ a₂<:a₁∈* b₁<:b₂∈*)      =
    let a₂∈* , a₁∈* = <:-valid a₂<:a₁∈*
        b₁∈* , b₂∈* = <:-valid b₁<:b₂∈*
    in kd-⋯ a₁∈* b₁∈* , kd-⋯ a₂∈* b₂∈*
  <∷-valid (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) =
    Πj₁k₁-kd ,
    kd-Π (proj₁ (<∷-valid j₂<∷j₁)) (proj₂ (<∷-valid k₁<∷k₂))

  -- Validity of subtyping: subtypes that are related in some kind `k'
  -- inhabit `k'.
  <:-valid : ∀ {n} {Γ : Ctx n} {a b k} →
             Γ ⊢ a <: b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
  <:-valid (<:-refl a∈k)            = a∈k , a∈k
  <:-valid (<:-trans a<:b∈k b<:c∈k) =
    proj₁ (<:-valid a<:b∈k) , proj₂ (<:-valid b<:c∈k)
  <:-valid (<:-β₁ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    ∈-Π-e (∈-Π-i j-kd a∈k k-kd) b∈j k-kd k[b]-kd , a[b]∈k[b]
    where j-kd = wf-kd-inv (wf-∷₁ (Tp∈-ctx a∈k))
  <:-valid (<:-β₂ a∈k b∈j a[b]∈k[b] k-kd k[b]-kd) =
    a[b]∈k[b] , ∈-Π-e (∈-Π-i j-kd a∈k k-kd) b∈j k-kd k[b]-kd
    where j-kd = wf-kd-inv (wf-∷₁ (Tp∈-ctx a∈k))
  <:-valid (<:-η₁ a∈Πjk) with Tp∈-valid a∈Πjk
  ... | (kd-Π j-kd k-kd) = Tp∈-η a∈Πjk j-kd k-kd , a∈Πjk
  <:-valid (<:-η₂ a∈Πjk) with Tp∈-valid a∈Πjk
  ... | (kd-Π j-kd k-kd) = a∈Πjk , Tp∈-η a∈Πjk j-kd k-kd
  <:-valid (<:-⊥ b∈c⋯d) = ∈-⊥-f (Tp∈-ctx b∈c⋯d) , Tp∈-⋯-* b∈c⋯d
  <:-valid (<:-⊤ b∈c⋯d) = Tp∈-⋯-* b∈c⋯d , ∈-⊤-f (Tp∈-ctx b∈c⋯d)
  <:-valid (<:-∀ k₂<∷k₁ a₁<:a₂∈* ∀k₁a₁∈*) =
    ∀k₁a₁∈* ,
    ∈-∀-f (proj₁ (<∷-valid k₂<∷k₁)) (proj₂ (<:-valid a₁<:a₂∈*))
  <:-valid (<:-→ a₂<:a₁∈* b₁<:b₂∈*) =
    let a₂∈* , a₁∈* = <:-valid a₂<:a₁∈*
        b₁∈* , b₂∈* = <:-valid b₁<:b₂∈*
    in ∈-→-f a₁∈* b₁∈* , ∈-→-f a₂∈* b₂∈*
  <:-valid (<:-λ a₁<:a₂∈k Λj₁a₁∈Πjk Λj₂a₂∈Πjk) = Λj₁a₁∈Πjk , Λj₂a₂∈Πjk
  <:-valid (<:-· a₁<:a₂∈Πjk b₁≃b₂∈j b₁∈j k-kd k[b₁]-kd) =
    let a₁∈Πjk , a₂∈Πjk = <:-valid a₁<:a₂∈Πjk
        b₁∈j   , b₂∈j   = ≃-valid  b₁≃b₂∈j
    in ∈-Π-e a₁∈Πjk b₁∈j k-kd k[b₁]-kd ,
       ∈-⇑ (∈-Π-e a₂∈Πjk b₂∈j k-kd (kd-[] k-kd (∈-tp b₂∈j)))
           (≅⇒<∷ (kd-[≃′] k-kd b₂∈j b₁∈j (≃-sym b₁≃b₂∈j)))
  <:-valid (<:-⟨| a∈b⋯c) with Tp∈-valid a∈b⋯c
  ... | (kd-⋯ b∈* c∈*) = b∈* , Tp∈-⋯-* a∈b⋯c
  <:-valid (<:-|⟩ a∈b⋯c) with Tp∈-valid a∈b⋯c
  ... | (kd-⋯ b∈* c∈*) = Tp∈-⋯-* a∈b⋯c , c∈*
  <:-valid (<:-⋯-i a<:b∈c⋯d) =
    let a∈c⋯d , b∈c⋯d = <:-valid a<:b∈c⋯d
        a<:b∈*        = <:-⋯-*   a<:b∈c⋯d
    in ∈-⇑ (∈-s-i a∈c⋯d) (<∷-⋯ (<:-refl (Tp∈-⋯-* a∈c⋯d)) a<:b∈*) ,
       ∈-⇑ (∈-s-i b∈c⋯d) (<∷-⋯ a<:b∈* (<:-refl (Tp∈-⋯-* b∈c⋯d)))
  <:-valid (<:-⇑ a<:b∈j j<∷k) =
    let a∈j , b∈j = <:-valid a<:b∈j
    in ∈-⇑ a∈j j<∷k , ∈-⇑ b∈j j<∷k

  -- Validity of type equality: types that are equal in some kind `k'
  -- inhabit `k'.
  ≃-valid : ∀ {n} {Γ : Ctx n} {a b k} →
            Γ ⊢ a ≃ b ∈ k → Γ ⊢Tp a ∈ k × Γ ⊢Tp b ∈ k
  ≃-valid (<:-antisym a<:b∈k b<:a∈k) = <:-valid a<:b∈k

  -- Subtypes inhabiting interval kinds are proper types.
  <:-⋯-* : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a <: b ∈ c ⋯ d → Γ ⊢ a <: b ∈ *
  <:-⋯-* a<:b∈c⋯d =
    let a∈c⋯d , b∈c⋯d = <:-valid a<:b∈c⋯d
    in <:-⇑ (<:-⋯-i a<:b∈c⋯d) (<∷-⋯ (<:-⊥ a∈c⋯d) (<:-⊤ b∈c⋯d))

-- Validity of kind equality: equal kinds are well-formed.
≅-valid : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j ≅ k → Γ ⊢ j kd × Γ ⊢ k kd
≅-valid (<∷-antisym j<∷k k<∷j) = <∷-valid j<∷k

-- Validity of combined kind and type equality: equal ascriptions are
-- well-formed.
≃wf-valid : ∀ {n} {Γ : Ctx n} {a b} →
            Γ ⊢ a ≃ b wf → Γ ⊢ a wf × Γ ⊢ b wf
≃wf-valid (≃wf-≅ j≅k)   = Prod.map wf-kd wf-kd (≅-valid j≅k)
≃wf-valid (≃wf-≃ a≃b∈k) = Prod.map wf-tp wf-tp (≃-valid a≃b∈k)

-- Some corollaries.

<:-valid-kd : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a <: b ∈ k → Γ ⊢ k kd
<:-valid-kd a<:b∈k = Tp∈-valid (proj₁ (<:-valid a<:b∈k))

≃-valid-kd : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢ a ≃ b ∈ k → Γ ⊢ k kd
≃-valid-kd (<:-antisym a<:b∈k _) = <:-valid-kd a<:b∈k


----------------------------------------------------------------------
-- Admissible kind and type equality rules.

-- Single-variable substitutions map well-formed kinds to kind
-- equations (strong version).
kd-[≃] : ∀ {n} {Γ : Ctx n} {a b j k} →
         kd j ∷ Γ ⊢ k kd → Γ ⊢ a ≃ b ∈ j → Γ ⊢ k Kind[ a ] ≅ k Kind[ b ]
kd-[≃] k-kd a≃b∈j = let a∈j , b∈j = ≃-valid a≃b∈j in kd-[≃′] k-kd a∈j b∈j a≃b∈j

-- Single-variable substitutions map well-kinded types to type
-- equations (strong version).
Tp∈-[≃] : ∀ {n} {Γ : Ctx n} {a b c j k} →
          kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢ b ≃ c ∈ j →
          Γ ⊢ a [ b ] ≃ a [ c ] ∈ k Kind[ b ]
Tp∈-[≃] a∈k b≃c∈j = let b∈j , c∈j = ≃-valid b≃c∈j in Tp∈-[≃′] a∈k b∈j c∈j b≃c∈j

-- An admissible congruence rule for kind equality w.r.t. dependent
-- arrow formation.
≅-Π : ∀ {n} {Γ : Ctx n} {j₁ j₂ k₁ k₂} →
      Γ ⊢ j₁ ≅ j₂ → kd j₁ ∷ Γ ⊢ k₁ ≅ k₂ → Γ ⊢ Π j₁ k₁ ≅ Π j₂ k₂
≅-Π (<∷-antisym j₁<∷j₂ j₂<∷j₁) (<∷-antisym k₁<∷k₂ k₂<∷k₁) =
  let j₁-kd , j₂-kd = <∷-valid j₁<∷j₂
      k₁-kd , k₂-kd = <∷-valid k₁<∷k₂
  in <∷-antisym (<∷-Π j₂<∷j₁ (⇓-<∷ j₂-kd j₂<∷j₁ k₁<∷k₂) (kd-Π j₁-kd k₁-kd))
                (<∷-Π j₁<∷j₂ k₂<∷k₁ (kd-Π j₂-kd (⇓-kd j₂-kd j₂<∷j₁ k₂-kd)))

-- Equal types inhabiting interval kinds are proper types.
≃-⋯-* : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a ≃ b ∈ c ⋯ d → Γ ⊢ a ≃ b ∈ *
≃-⋯-* (<:-antisym a<:b∈c⋯d b<:a∈c⋯d) =
  let a<:b∈* = <:-⋯-* a<:b∈c⋯d
      b<:a∈* = <:-⋯-* b<:a∈c⋯d
  in <:-antisym a<:b∈* b<:a∈*

-- An admissible congruence rule for type equality w.r.t. formation of
-- universal types.
≃-∀ : ∀ {n} {Γ : Ctx n} {k₁ k₂ a₁ a₂} →
      Γ ⊢ k₁ ≅ k₂ → kd k₁ ∷ Γ ⊢ a₁ ≃ a₂ ∈ * → Γ ⊢ Π k₁ a₁ ≃ Π k₂ a₂ ∈ *
≃-∀ (<∷-antisym k₁<∷k₂ k₂<∷k₁) (<:-antisym a₁<:a₂∈* a₂<:a₁∈*) =
  let k₁-kd , k₂-kd = <∷-valid k₁<∷k₂
      a₁∈*  , a₂∈*  = <:-valid a₁<:a₂∈*
  in <:-antisym (<:-∀ k₂<∷k₁ (⇓-<: k₂-kd k₂<∷k₁ a₁<:a₂∈*) (∈-∀-f k₁-kd a₁∈*))
                (<:-∀ k₁<∷k₂ a₂<:a₁∈* (∈-∀-f k₂-kd (⇓-Tp∈ k₂-kd k₂<∷k₁ a₂∈*)))

-- Another, weaker congruence lemma for type equality w.r.t. type
-- operator abstraction.
≃-λ′ : ∀ {n} {Γ : Ctx n} {j₁ j₂ a₁ a₂ k} →
       Γ ⊢ j₁ ≅ j₂ → kd j₁ ∷ Γ ⊢ a₁ ≃ a₂ ∈ k → Γ ⊢ Λ j₁ a₁ ≃ Λ j₂ a₂ ∈ Π j₁ k
≃-λ′ (<∷-antisym j₁<∷j₂ j₂<∷j₁) (<:-antisym a₁<:a₂∈k a₂<:a₁∈k) =
  let j₁-kd , j₂-kd = <∷-valid j₁<∷j₂
      a₁∈k  , a₂∈k  = <:-valid a₁<:a₂∈k
      k-kd          = Tp∈-valid a₁∈k
      k-kd′         = ⇓-kd j₂-kd j₂<∷j₁ k-kd
      Πj₂k<∷j₁k     = <∷-Π j₁<∷j₂ (<∷-refl k-kd) (kd-Π j₂-kd k-kd′)
      Λj₁a₁∈Πj₁k    = ∈-Π-i j₁-kd a₁∈k k-kd
      Λj₂a₂∈Πj₁k    = ∈-⇑ (∈-Π-i j₂-kd (⇓-Tp∈ j₂-kd j₂<∷j₁ a₂∈k) k-kd′)
                          Πj₂k<∷j₁k
  in <:-antisym (<:-λ a₁<:a₂∈k Λj₁a₁∈Πj₁k Λj₂a₂∈Πj₁k)
                (<:-λ a₂<:a₁∈k Λj₂a₂∈Πj₁k Λj₁a₁∈Πj₁k)

-- An admissible congruence rule for type equality w.r.t. type
-- application.
≃-· : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j k} →
      Γ ⊢ a₁ ≃ a₂ ∈ Π j k → Γ ⊢ b₁ ≃ b₂ ∈ j →
      Γ ⊢ a₁ · b₁ ≃ a₂ · b₂ ∈ k Kind[ b₁ ]
≃-· (<:-antisym a₁<:a₂∈Πjk a₂<:a₁∈Πjk) b₁≃b₂∈j with <:-valid-kd a₁<:a₂∈Πjk
... | (kd-Π j-kd k-kd) =
  let b₁∈j , b₂∈j = ≃-valid b₁≃b₂∈j
      k[b₁]-kd    = kd-[] k-kd (∈-tp b₁∈j)
      k[b₂]-kd    = kd-[] k-kd (∈-tp b₂∈j)
  in <:-antisym (<:-· a₁<:a₂∈Πjk b₁≃b₂∈j b₁∈j k-kd k[b₁]-kd)
                (<:-⇑ (<:-· a₂<:a₁∈Πjk (≃-sym b₁≃b₂∈j) b₂∈j k-kd k[b₂]-kd)
                      (≅⇒<∷ (kd-[≃] k-kd (≃-sym b₁≃b₂∈j))))

-- An admissible, more flexible β-rule for type equality.
≃-β′ : ∀ {n} {Γ : Ctx n} {a b j k l} →
       kd j ∷ Γ ⊢Tp a ∈ k → Γ ⊢Tp b ∈ j → Γ ⊢Tp Λ l a ∈ Π j k →
       Γ ⊢ (Λ l a) · b ≃ a [ b ] ∈ k Kind[ b ]
≃-β′ a∈k b∈j Λla∈Πjk =
  let j-kd      = Tp∈-valid b∈j
      k-kd      = Tp∈-valid a∈k
      k[b]-kd   = kd-[] k-kd (∈-tp b∈j)
      a[b]∈k[b] = Tp∈-[] a∈k (∈-tp b∈j)
  in ≃-trans (≃-· (≃-λ (≃-refl a∈k) Λla∈Πjk (∈-Π-i j-kd a∈k k-kd)) (≃-refl b∈j))
             (≃-β a∈k b∈j a[b]∈k[b] k-kd k[b]-kd)

-- An admissible singleton-introduction rule for type equality.
≃-s-i : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ⊢ a ≃ b ∈ c ⋯ d → Γ ⊢ a ≃ b ∈ a ⋯ a
≃-s-i (<:-antisym a<:b∈c⋯d b<:a∈c⋯d) =
  let a<:b∈*  = <:-⋯-* a<:b∈c⋯d
      b<:a∈*  = <:-⋯-* b<:a∈c⋯d
      a∈* , _ = <:-valid a<:b∈*
      a<:a∈*  = <:-refl a∈*
  in <:-antisym (<:-⇑ (<:-⋯-i a<:b∈c⋯d) (<∷-⋯ a<:a∈* b<:a∈*))
                (<:-⇑ (<:-⋯-i b<:a∈c⋯d) (<∷-⋯ a<:b∈* a<:a∈*))

-- Operations on well-formed context reductions that require weakening
-- and validity of well-formed reductions.
module CtxReductionOps where
  open KindedRenaming using (≃wf-weaken)

  -- Convert a context equation to its All₂ representation.
  ≃ctx-toAll : ∀ {m} {Γ Δ : Ctx m} → Γ ≃ Δ ctx →
               All₂ (Γ ⊢_≃_wf) (toVec Γ) (toVec Δ)
  ≃ctx-toAll ≃-[]          = []
  ≃ctx-toAll (≃-∷ a≃b Γ≃Δ) =
    let a-wf , _ = ≃wf-valid a≃b
    in ≃wf-weaken a-wf a≃b ∷ gmap₂ (≃wf-weaken a-wf) (≃ctx-toAll Γ≃Δ)

  -- Ascriptions looked up in equal contexts are equal.

  lookup-≃ : ∀ {m} {Γ Δ : Ctx m} x → Γ ≃ Δ ctx →
             Γ ⊢ lookup x Γ ≃ lookup x Δ wf
  lookup-≃ x Γ≃Δ = VecAll.lookup₂ x (≃ctx-toAll Γ≃Δ)

  lookup-≃-kd : ∀ {m} {Γ Δ : Ctx m} {j k} x → Γ ≃ Δ ctx →
                lookup x Γ ≡ kd j → lookup x Δ ≡ kd k → Γ ⊢ j ≅ k
  lookup-≃-kd x Γ≃Δ Γ[x]≡kd-j Δ[x]≡kd-k =
    ≃wf-kd-inv (PropEq.subst₂ (_ ⊢_≃_wf) Γ[x]≡kd-j Δ[x]≡kd-k (lookup-≃ x Γ≃Δ))

-- A variant of subject reduction for kinding: untyped β-reduction of
-- kinds and types is included in kind resp. type equality.

mutual

  kd-→β-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j kd → j Kd→β k → Γ ⊢ j ≅ k
  kd-→β-≅ (kd-⋯ a∈* b∈*)   (a→a′ ⋯₁ b) = ≅-⋯ (Tp∈-→β-≃ a∈* a→a′) (≃-refl b∈*)
  kd-→β-≅ (kd-⋯ a∈* b∈*)   (a ⋯₂ b→b′) = ≅-⋯ (≃-refl a∈*) (Tp∈-→β-≃ b∈* b→b′)
  kd-→β-≅ (kd-Π j-kd k-kd) (Π₁ j→j′ k) =
    ≅-Π (kd-→β-≅ j-kd j→j′) (≅-refl k-kd)
  kd-→β-≅ (kd-Π j-kd k-kd) (Π₂ j k→k′) =
    ≅-Π (≅-refl j-kd) (kd-→β-≅ k-kd k→k′)

  Tp∈-→β-≃ : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ∈ k → a →β b → Γ ⊢ a ≃ b ∈ k
  Tp∈-→β-≃ (∈-var x Γ-ctx Γ[x]≡kd-k) ⌈ () ⌉
  Tp∈-→β-≃ (∈-⊥-f Γ-ctx)    ⌈ () ⌉
  Tp∈-→β-≃ (∈-⊤-f Γ-ctx)    ⌈ () ⌉
  Tp∈-→β-≃ (∈-∀-f k-kd a∈*) ⌈ () ⌉
  Tp∈-→β-≃ (∈-∀-f k-kd a∈*) (Π₁ k→k′ a) =
    ≃-∀ (kd-→β-≅ k-kd k→k′) (≃-refl a∈*)
  Tp∈-→β-≃ (∈-∀-f k-kd a∈*) (Π₂ k a→a′) =
    ≃-∀ (≅-refl k-kd) (Tp∈-→β-≃ a∈* a→a′)
  Tp∈-→β-≃ (∈-→-f a∈* b∈*)  ⌈ () ⌉
  Tp∈-→β-≃ (∈-→-f a∈* b∈*)  (a→a′ ⇒₁ b) =
    ≃-→ (Tp∈-→β-≃ a∈* a→a′) (≃-refl b∈*)
  Tp∈-→β-≃ (∈-→-f a∈* b∈*)  (a ⇒₂ b→b′) =
    ≃-→ (≃-refl a∈*) (Tp∈-→β-≃ b∈* b→b′)
  Tp∈-→β-≃ (∈-Π-i j-kd a∈k k-kd) ⌈ () ⌉
  Tp∈-→β-≃ (∈-Π-i j-kd a∈k k-kd) (Λ₁ j→j′ a) =
    ≃-λ′ (kd-→β-≅ j-kd j→j′) (≃-refl a∈k)
  Tp∈-→β-≃ (∈-Π-i j-kd a∈k k-kd) (Λ₂ j a→a′) =
    ≃-λ′ (≅-refl j-kd) (Tp∈-→β-≃ a∈k a→a′)
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) ⌈ cont-Tp· l a b ⌉ =
    let l-kd , a∈k = Tp∈-Λ-inv a∈Πjk
    in ≃-β′ a∈k b∈j a∈Πjk
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) ⌈ cont-Tm· a b c ⌉ =
    contradiction a∈Πjk Tp∈-¬λ
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) (a→a′ ·₁ b) =
    ≃-· (Tp∈-→β-≃ a∈Πjk a→a′) (≃-refl b∈j)
  Tp∈-→β-≃ (∈-Π-e a∈Πjk b∈j k-kd k[b]-kd) (a ·₂ b→b′) =
    ≃-· (≃-refl a∈Πjk) (Tp∈-→β-≃ b∈j b→b′)
  Tp∈-→β-≃ (∈-s-i a∈k)    a→b = ≃-s-i (Tp∈-→β-≃ a∈k a→b)
  Tp∈-→β-≃ (∈-⇑ a∈j j<∷k) a→b = ≃-⇑ (Tp∈-→β-≃ a∈j a→b) j<∷k

kd-→β*-≅ : ∀ {n} {Γ : Ctx n} {j k} → Γ ⊢ j kd → j Kd→β* k → Γ ⊢ j ≅ k
kd-→β*-≅ j-kd ε            = ≅-refl j-kd
kd-→β*-≅ j-kd (j→k ◅ k→*l) =
  let j≅k  = kd-→β-≅ j-kd j→k
      k-kd = proj₂ (≅-valid j≅k)
  in ≅-trans j≅k (kd-→β*-≅ k-kd k→*l)

Tp∈-→β*-≃ : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ∈ k → a →β* b → Γ ⊢ a ≃ b ∈ k
Tp∈-→β*-≃ a∈k ε            = ≃-refl a∈k
Tp∈-→β*-≃ a∈k (a→b ◅ b→*c) =
  let a≃b∈k = Tp∈-→β-≃ a∈k a→b
      b∈k   = proj₂ (≃-valid a≃b∈k)
  in ≃-trans a≃b∈k (Tp∈-→β*-≃ b∈k b→*c)

-- A corollary: subject reduction for kinding, aka preservation of
-- kinding under (full) β-reduction.
pres-Tp∈-→β* : ∀ {n} {Γ : Ctx n} {a b k} → Γ ⊢Tp a ∈ k → a →β* b → Γ ⊢Tp b ∈ k
pres-Tp∈-→β* a∈k a→b = proj₂ (≃-valid (Tp∈-→β*-≃ a∈k a→b))
