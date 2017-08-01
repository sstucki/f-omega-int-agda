------------------------------------------------------------------------
-- Canonically kinded hereditary substitutions in Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Canonical.HereditarySubstitution where

open import Data.Fin using (Fin; zero; suc; raise; lift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.List using ([]; _∷_; _∷ʳ_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProp
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization
open import FOmegaInt.Kinding.Canonical as CanonicalKinding
open import FOmegaInt.Kinding.Simple    as SimpleKinding

open Syntax
open ElimCtx            hiding (extension)
open SimpleCtx          using (⌊_⌋Asc; kd; tp)
open ContextConversions using (⌊_⌋Ctx)
open Substitution       hiding (subst)
open RenamingCommutes
open SimpHSubstLemmas
open SimpleKinding.Kinding
  renaming (_⊢Var_∈_ to _⊢sVar_∈_; _⊢Ne_∈_ to _⊢sNe_∈_)
open CanonicalKinding.Kinding
open KindedHereditarySubstitution
  using (_⊢/H_∈_; ∈-hsub; kds-/H; kds-[]-/H-↑⋆)
open CanonicalKinding.KindedRenaming
  using (kd-weaken⋆; Nf⇇-weaken⋆; <:⇇-weaken⋆)
open ContextNarrowing


----------------------------------------------------------------------
-- Well-kinded hereditary substitutions (i.e. substitution lemmas) in
-- canonical types

infix 4 _⊢/H_⇇_ _⊢/H_≃_⇇_

-- Well-kinded suspended parallel hereditary substations.
data _⊢/H_≃_⇇_ : ∀ {k m n} → Ctx n → HSub k m n → HSub k m n → Ctx m → Set where
  ≃-hsub : ∀ {k m n} {Δ₂ : CtxExt′ m n} {Γ₂ Γ₁} {a b j} →
            Γ₁ ⊢ Δ₂ ≅ Γ₂ E[ a ∈ k ] ext → Γ₁ ⊢ Δ₂ ≅ Γ₂ E[ b ∈ k ] ext →
            Γ₁ ⊢ a ≃ b ⇇ j → ⌊ j ⌋≡ k →
            Δ₂ ′++ Γ₁ ⊢/H (n ← a ∈ k) ≃ (n ← b ∈ k) ⇇ Γ₂ ′++ kd j ∷ Γ₁

-- Lift a kinded hereditary substitution over an additional type variable.
≃-H↑ : ∀ {k m n Δ Γ} {ρ σ : HSub k m n} {a b} →
        Δ ⊢ a ≅ b Asc/H ρ wf → Δ ⊢ a ≅ b Asc/H σ wf → Δ ⊢/H ρ ≃ σ ⇇ Γ →
        a ∷ Δ ⊢/H ρ H↑ ≃ σ H↑ ⇇ b ∷ Γ
≃-H↑ d≅e[a] d≅e[b] (≃-hsub Δ≅Γ[a] Δ≅Γ[b] a≃b⇇j ⌊j⌋≡k) =
  ≃-hsub (d≅e[a] ∷ Δ≅Γ[a]) (d≅e[b] ∷ Δ≅Γ[b]) a≃b⇇j ⌊j⌋≡k

-- Lift a kinded hereditary substitution over multiple additional
-- variables.
≃-H↑⋆ : ∀ {k m n i} {E : CtxExt′ n i} {Φ Δ Γ} {ρ σ : HSub k m n} →
         Δ ⊢ E ≅ Φ E/H ρ ext → Δ ⊢ E ≅ Φ E/H σ ext → Δ ⊢/H ρ ≃ σ ⇇ Γ →
         E ′++ Δ ⊢/H ρ H↑⋆ i ≃ σ H↑⋆ i ⇇ Φ ′++ Γ
≃-H↑⋆ {Φ = []}    []            []            ρ≃σ⇇Γ = ρ≃σ⇇Γ
≃-H↑⋆ {Φ = _ ∷ _} (a≅b ∷ E≅Φ/ρ) (a≅c ∷ E≅Φ/σ) ρ≃σ⇇Γ =
  ≃-H↑ a≅b a≅c (≃-H↑⋆ E≅Φ/ρ E≅Φ/σ ρ≃σ⇇Γ)

-- Well-kinded suspended hereditary substations are just well-kinded
-- parallel hereditary substitutions where the underlying
-- substitutions coincide.

_⊢/H_⇇_ : ∀ {k m n} → Ctx n → HSub k m n → Ctx m → Set
Δ ⊢/H ρ ⇇ Γ = Δ ⊢/H ρ ≃ ρ ⇇ Γ

⇇-hsub : ∀ {k m n} {Δ₂ : CtxExt′ m n} {Γ₂ Γ₁} {a j} →
         Γ₁ ⊢ Δ₂ ≅ Γ₂ E[ a ∈ k ] ext → Γ₁ ⊢Nf a ⇇ j → Γ₁ ⊢ j kd → ⌊ j ⌋≡ k →
         Δ₂ ′++ Γ₁ ⊢/H (n ← a ∈ k) ⇇ Γ₂ ′++ kd j ∷ Γ₁
⇇-hsub Δ≅Γ[a] a⇇j j-kd ⌊j⌋≡k = ≃-hsub Δ≅Γ[a] Δ≅Γ[a] (≃-reflNf⇇ a⇇j j-kd) ⌊j⌋≡k

-- Lift a kinded hereditary substitution over an additional variable.
⇇-H↑ : ∀ {k m n Δ Γ} {ρ : HSub k m n} {a b} →
       Δ ⊢ a ≅ b Asc/H ρ wf → Δ ⊢/H ρ ⇇ Γ → a ∷ Δ ⊢/H ρ H↑ ⇇ b ∷ Γ
⇇-H↑ a≅b ρ⇇Γ = ≃-H↑ a≅b a≅b ρ⇇Γ

-- Lift a kinded hereditary substitution over multiple additional
-- variables.
⇇-H↑⋆ : ∀ {k m n i} {E : CtxExt′ n i} {Φ Δ Γ} {ρ : HSub k m n} →
        Δ ⊢ E ≅ Φ E/H ρ ext → Δ ⊢/H ρ ⇇ Γ → E ′++ Δ ⊢/H ρ H↑⋆ i ⇇ Φ ′++ Γ
⇇-H↑⋆ E≅Φ/ρ ρ⇇Γ = ≃-H↑⋆ E≅Φ/ρ E≅Φ/ρ ρ⇇Γ

-- Left and right-hand "validity" of parallel hereditary substitutions.

/H≃-valid₁ : ∀ {k m n Δ Γ} {ρ σ : HSub k m n} → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢/H ρ ⇇ Γ
/H≃-valid₁ (≃-hsub Δ≅Γ[a] _ a≃b⇇j ⌊j⌋≡k) =
  ⇇-hsub Δ≅Γ[a] (proj₁ (≃-valid a≃b⇇j)) (≃-valid-kd a≃b⇇j) ⌊j⌋≡k

/H≃-valid₂ : ∀ {k m n Δ Γ} {ρ σ : HSub k m n} → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢/H σ ⇇ Γ
/H≃-valid₂ (≃-hsub _ Δ≅Γ[b] a≃b⇇j ⌊j⌋≡k) =
  ⇇-hsub Δ≅Γ[b] (proj₂ (≃-valid a≃b⇇j)) (≃-valid-kd a≃b⇇j) ⌊j⌋≡k

-- "Symmetry" of parallel hereditary substitutions.
/H≃-sym : ∀ {k m n Δ Γ} {ρ σ : HSub k m n} → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢/H σ ≃ ρ ⇇ Γ
/H≃-sym (≃-hsub Δ≅Γ[a] Δ≅Γ[b] a≃b⇇j ⌊j⌋≡k) =
  ≃-hsub Δ≅Γ[b] Δ≅Γ[a] (≃-sym a≃b⇇j) ⌊j⌋≡k

-- Hits in the left of a parallel substitution also hit in the right.
/H≃-Hit : ∀ {k m n Δ Γ} {ρ σ : HSub k m n} {x} →
           Δ ⊢/H ρ ≃ σ ⇇ Γ → Hit ρ x → Hit σ x
/H≃-Hit (≃-hsub Δ≅Γ[a] Δ≅Γ[b] a≃b⇇j ⌊j⌋≡k) refl = refl

-- Misses in the left of a parallel substitution also miss in the right.
/H≃-Miss : ∀ {k m n Δ Γ} {ρ σ : HSub k m n} {x y} →
            Δ ⊢/H ρ ≃ σ ⇇ Γ → Miss ρ x y → Miss σ x y
/H≃-Miss (≃-hsub Δ≅Γ[a] Δ≅Γ[b] a≃b⇇j ⌊j⌋≡k) refl = refl

private
  module KL = TermLikeLemmas termLikeLemmasKind′
  module EL = TermLikeLemmas termLikeLemmasElim
  module AL = TermLikeLemmas termLikeLemmasElimAsc

-- Simplification of kinded substitutions.
/H⇇-/H∈ : ∀ {k m n Δ Γ} {ρ : HSub k m n} →
          Δ ⊢/H ρ ⇇ Γ → ⌊ Δ ⌋Ctx ⊢/H ρ ∈ ⌊ Γ ⌋Ctx
/H⇇-/H∈ (≃-hsub {Δ₂ = Δ₂} {Γ₂} {Γ₁} {a} {_} {j} Δ₂≅Γ₁[a] _ a≃a⇇j ⌊j⌋≡k)
  rewrite sym (⌊⌋≡⇒⌊⌋-≡ ⌊j⌋≡k) =
  subst₂ (_⊢/H _ ∈_) (begin
      map′ (λ _ k → k) (map′ (λ _ → ⌊_⌋Asc) Γ₂) ′++ ⌊ Γ₁ ⌋Ctx
    ≡⟨ cong (_′++ _) (sym (map′-∘ (λ _ k → k) (λ _ → ⌊_⌋Asc) Γ₂)) ⟩
      map′ (λ _ → ⌊_⌋Asc) Γ₂ ′++ ⌊ Γ₁ ⌋Ctx
    ≡⟨ cong (_′++ _) (map′-cong (λ a → sym (⌊⌋-Asc/H a)) Γ₂) ⟩
      map′ (λ i b → ⌊ b Asc/H i ← a ∈ ⌊ j ⌋ ⌋Asc) Γ₂ ′++ ⌊ Γ₁ ⌋Ctx
    ≡⟨ cong (_′++ _)
            (map′-∘ (λ _ → ⌊_⌋Asc) (λ i b → b Asc/H i ← a ∈ ⌊ j ⌋) Γ₂)  ⟩
      map′ (λ _ → ⌊_⌋Asc) (Γ₂ E[ a ∈ ⌊ j ⌋ ]) ′++ ⌊ Γ₁ ⌋Ctx
    ≡⟨ cong (_′++ _) (sym (⌊⌋-≅-ext Δ₂≅Γ₁[a]))  ⟩
      map′ (λ _ → ⌊_⌋Asc) Δ₂ ′++ ⌊ Γ₁ ⌋Ctx
    ≡⟨ ′++-map ⌊_⌋Asc Δ₂ Γ₁ ⟩
      ElimCtx.map ⌊_⌋Asc (Δ₂ ′++ Γ₁)
    ∎) (′++-map ⌊_⌋Asc Γ₂ (kd j ∷ Γ₁))
         (∈-hsub (map′ (λ _ → ⌊_⌋Asc) Γ₂) (Nf⇇-Nf∈ a⇇j))
    where a⇇j = proj₁ (≃-valid a≃a⇇j)

-- Lookup a hit in a well-kinded hereditary substitution.
Var∈-Hit-/H≃ : ∀ {m n} {E : CtxExt′ m n} {Γ₂ Γ₁ a b j k l} →
               let Γ = Γ₂ ′++ kd k ∷ Γ₁
                   Δ = E ′++ Γ₁
                   ρ = n ← a ∈ l
                   σ = n ← b ∈ l
                   x = raise n zero
               in Δ ctx → lookup x Γ ≡ kd j →
                  Γ₁ ⊢ E ≅ Γ₂ E[ a ∈ l ] ext → Γ₁ ⊢ a ≃ b ⇇ k → ⌊ k ⌋≡ l →
                  Δ ⊢ var∙ x /H ρ ≃ var∙ x /H σ ⇇ j Kind/H ρ × ⌊ j Kind/H ρ ⌋≡ l
Var∈-Hit-/H≃ {_} {n} {E} {Γ₂} {Γ₁} {a} {b} {j} {k} {l} Δ-ctx Γ[x]≡kd-j
             E≅Γ₂[a] (<:-antisym k-kd a<:b b<:a) ⌊k⌋≡l =
  <:-antisym (subst  (E ′++ Γ₁ ⊢_kd) k′≡j/ρ (kd-weaken⋆ {Δ′ = E} E-ext k-kd))
             (subst₂ (E ′++ Γ₁ ⊢_<:_⇇ j Kind/H n ← a ∈ l)
                     (helper n a) (helper n b)
                     (subst (E ′++ Γ₁ ⊢ _ <: _ ⇇_) k′≡j/ρ
                            (<:⇇-weaken⋆ {Δ′ = E} E-ext a<:b)))
             (subst₂ (E ′++ Γ₁ ⊢_<:_⇇ j Kind/H n ← a ∈ l)
                     (helper n b) (helper n a)
                     (subst (E ′++ Γ₁ ⊢ _ <: _ ⇇_) k′≡j/ρ
                            (<:⇇-weaken⋆ {Δ′ = E} E-ext b<:a))) ,
  ⌊⌋≡-trans (cong ⌊_⌋ (sym k′≡j/ρ)) (⌊⌋≡-weaken⋆ n ⌊k⌋≡l)
  where
    E-ext = proj₁ (wf-split Δ-ctx)

    k′≡j/ρ = begin
        weakenKind′⋆ n k
      ≡⟨ sym (KL./-wk⋆ n) ⟩
        k Kind′/ wk⋆ n
      ≡⟨ cong (_Kind′/ wk⋆ n) (sym (Kind/-wk-↑⋆-hsub-vanishes 0 k)) ⟩
        (weakenKind′ k) Kind/H 0 ← a ∈ l Kind′/ wk⋆ n
      ≡⟨ sym (wk⋆-Kind/H-↑⋆ n (weakenKind′ k)) ⟩
        (weakenKind′ k) Kind′/ wk⋆ n Kind/H (0 ← a ∈ l) H↑⋆ n
      ≡⟨ cong ((weakenKind′ k) Kind′/ wk⋆ n Kind/H_) (zero-←-↑⋆ n) ⟩
        (weakenKind′ k) Kind′/ wk⋆ n Kind/H n ← a ∈ l
      ≡⟨ kd-inj (cong (_Asc/H n ← a ∈ l) (begin
            kd (weakenKind′ k Kind′/ wk⋆ n)
          ≡⟨ AL./-wk⋆ n ⟩
            weakenElimAsc⋆ n (weakenElimAsc (kd k))
          ≡⟨ sym (lookup-weaken⋆′ n zero [] Γ₂ (kd k ∷ Γ₁)) ⟩
            lookup (raise n zero) (Γ₂ ′++ kd k ∷ Γ₁)
          ≡⟨ Γ[x]≡kd-j ⟩
            kd j
          ∎)) ⟩
        j Kind/H (n ← a ∈ l)
      ∎

    helper : ∀ n {m} (a : Elim m) →
             weakenElim⋆ n a ≡ var∙ (raise n zero) /H n ← a ∈ l
    helper n a = begin
        weakenElim⋆ n a
      ≡⟨ sym (EL./-wk⋆ n) ⟩
        a Elim/ wk⋆ n
      ≡⟨ cong (_Elim/ wk⋆ n) (sym (⌜⌝∘⌞⌟-id a)) ⟩
        ⌜ ⌞ a ⌟ ⌝ Elim/ wk⋆ n
      ≡⟨ sym (⌜⌝-/ ⌞ a ⌟) ⟩
        ⌜ ⌞ a ⌟ / wk⋆ n ⌝
      ≡⟨ cong ⌜_⌝ (sym (ExtLemmas₄.raise-/-↑⋆ lemmas₄ n zero)) ⟩
        ⌜ Vec.lookup (raise n zero) (sub ⌞ a ⌟ ↑⋆ n) ⌝
      ≡⟨ sym (var∙-/H-/ (n ← a ∈ l) (raise n zero)) ⟩
        var∙ (raise n zero) /H n ← a ∈ l
      ∎

-- Lookup a miss in a well-kinded hereditary substitution.
Var∈-Miss-/H : ∀ {m n} {E : CtxExt′ m n} {Γ₂ Γ₁} {x a j k l} →
               let Γ = Γ₂ ′++ kd k ∷ Γ₁
                   Δ = E ′++ Γ₁
               in Δ ctx → lookup (lift n suc x) Γ ≡ kd j →
                  Γ₁ ⊢ E ≅ Γ₂ E[ a ∈ l ] ext → ⌊ k ⌋≡ l →
                  Δ ⊢Var var x ∈ j Kind/H (n ← a ∈ l)
Var∈-Miss-/H {_} {n} {E} {Γ₂} {Γ₁} {x} {a} {j} {k} {l}
             Δ-ctx Γ[x]≡kd-j E≅Γ₂[a] ⌊k⌋≡l =
  let open VecProp using (map-cong; map-id; map-∘)

      Γ₁-ctx = proj₂ (wf-split {Δ = CtxExt′⇒CtxExt E} Δ-ctx)

      Γ₂/ρ++Γ₁[x]≡kd-j/σ = begin
          lookup x (Γ₂ E[ a ∈ l ] ′++ Γ₁)
        ≡⟨ cong (λ l → lookup x (Γ₂ E[ a ∈ l ] ′++ Γ₁)) (sym (⌊⌋≡⇒⌊⌋-≡ ⌊k⌋≡l)) ⟩
          lookup x (Γ₂ E[ a ∈ ⌊ k ⌋ ] ′++ Γ₁)
        ≡⟨ lookup-E[] Γ₂ a k x ⟩
          lookup (lift n suc x) (Γ₂ ′++ kd k ∷ Γ₁) Asc/H n ← a ∈ ⌊ k ⌋
        ≡⟨ cong₂ (λ b l → b Asc/H n ← a ∈ l) Γ[x]≡kd-j (⌊⌋≡⇒⌊⌋-≡ ⌊k⌋≡l) ⟩
          kd (j Kind/H n ← a ∈ l)
        ∎

      k , Δ[x]≡kd-k , k≅j/ρ = lookup-≅-kd x Γ₁-ctx E≅Γ₂[a] Γ₂/ρ++Γ₁[x]≡kd-j/σ

  in ⇇-⇑ (⇉-var x Δ-ctx Δ[x]≡kd-k) (≅⇒<∷ k≅j/ρ) (proj₂ (≅-valid k≅j/ρ))

-- TODO: explain why we need to track simple kinds explicitly.
module TrackSimpleKindsSubst where

  -- TODO: explain how/why preservation of (sub)kinding/subtyping
  -- under reducing applications, hereditary substitution and parallel
  -- hereditary substitutions circularly depend on each other
  -- (including a description of the critical path).

  mutual

    -- Hereditary substitutions preserve well-formedness of ascriptions.
    wf-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {a} →
            Γ ⊢ a wf → Δ ⊢/H ρ ⇇ Γ → Δ ⊢ a Asc/H ρ wf
    wf-/H (wf-kd k-kd)  ρ⇇Γ = wf-kd (kd-/H k-kd ρ⇇Γ)
    wf-/H (wf-tp a⇉a⋯a) ρ⇇Γ = wf-tp (Nf⇉-/H a⇉a⋯a ρ⇇Γ)

    -- Hereditary substitutions preserve well-formedness of contexts.
    ctx-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} → Γ ctx → Δ ⊢/H ρ ⇇ Γ → Δ ctx
    ctx-/H Γ-ctx (≃-hsub E≅Γ₂[a] _ a≃a⇇j ⌊j⌋≡k) = ctx-/H′ _ E≅Γ₂[a] Γ-ctx
      where
        a⇇j  = proj₁ (≃-valid a≃a⇇j)
        j-kd = ≃-valid-kd a≃a⇇j

        ctx-/H′ : ∀ {k m n} {E : CtxExt′ m n} Γ₂ {Γ₁ a j} →
                  Γ₁ ⊢ E ≅ Γ₂ E[ a ∈ k ] ext →
                  Γ₂ ′++ kd j ∷ Γ₁ ctx → E ′++ Γ₁ ctx
        ctx-/H′ []      []                (_    ∷ Γ-ctx) = Γ-ctx
        ctx-/H′ (c ∷ Γ) (b≅c[a] ∷ E≅Γ[a]) (c-wf ∷ Γ-ctx) =
          proj₁ (≅wf-valid b≅c[a]) ∷ ctx-/H′ Γ E≅Γ[a] Γ-ctx

    -- Hereditary substitutions preserve well-formedness of kinds.
    kd-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {j} →
            Γ ⊢ j kd → Δ ⊢/H ρ ⇇ Γ → Δ ⊢ j Kind/H ρ kd
    kd-/H (kd-⋯ a⇉a⋯a b⇉b⋯b) ρ⇇Γ =
      kd-⋯ (Nf⇉-/H a⇉a⋯a ρ⇇Γ) (Nf⇉-/H b⇉b⋯b ρ⇇Γ)
    kd-/H (kd-Π j-kd k-kd)   ρ⇇Γ =
      let j/ρ-kd = kd-/H j-kd ρ⇇Γ
      in kd-Π j/ρ-kd (kd-/H k-kd (⇇-H↑ (≅-kd (≅-refl j/ρ-kd)) ρ⇇Γ))

    -- Hereditary substitutions preserve synthesized kinds of normal
    -- types.
    Nf⇉-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {a j} →
             Γ ⊢Nf a ⇉ j → Δ ⊢/H ρ ⇇ Γ → Δ ⊢Nf a /H ρ ⇉ j Kind/H ρ
    Nf⇉-/H (⇉-⊥-f Γ-ctx) ρ⇇Γ = ⇉-⊥-f (ctx-/H Γ-ctx ρ⇇Γ)
    Nf⇉-/H (⇉-⊤-f Γ-ctx) ρ⇇Γ = ⇉-⊤-f (ctx-/H Γ-ctx ρ⇇Γ)
    Nf⇉-/H (⇉-∀-f k-kd a⇉a⋯a)  ρ⇇Γ =
      let k/ρ-kd = kd-/H k-kd ρ⇇Γ
      in ⇉-∀-f k/ρ-kd (Nf⇉-/H a⇉a⋯a (⇇-H↑ (≅wf-refl (wf-kd k/ρ-kd)) ρ⇇Γ))
    Nf⇉-/H (⇉-→-f a⇉a⋯a b⇉b⋯b) ρ⇇Γ =
      ⇉-→-f (Nf⇉-/H a⇉a⋯a ρ⇇Γ) (Nf⇉-/H b⇉b⋯b ρ⇇Γ)
    Nf⇉-/H (⇉-Π-i k-kd a⇉a⋯a)  ρ⇇Γ =
      let k/ρ-kd = kd-/H k-kd ρ⇇Γ
      in ⇉-Π-i k/ρ-kd (Nf⇉-/H a⇉a⋯a (⇇-H↑ (≅-kd (≅-refl k/ρ-kd)) ρ⇇Γ))
    Nf⇉-/H (⇉-s-i a∈b⋯c) ρ⇇Γ = Nf⇇-s-i (Ne∈-/H a∈b⋯c ρ⇇Γ)

    -- Neutral proper types kind-check against their synthesized kinds
    -- after substitution.
    Ne∈-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {a b c} →
             Γ ⊢Ne a ∈ b ⋯ c → Δ ⊢/H ρ ⇇ Γ → Δ ⊢Nf a /H ρ ⇇ b /H ρ ⋯ c /H ρ
    Ne∈-/H {ρ = ρ} (∈-∙ {x} x∈j j⇉as⇉l) ρ⇇Γ with hit? ρ x
    Ne∈-/H (∈-∙ x∈j j⇉as⇉l) ρ⇇Γ | yes hit =
      let x/ρ⇇j/ρ , ⌊j/ρ⌋≡k , j-kd = Var⇇-Hit-/H hit x∈j ρ⇇Γ
      in subst (_ ⊢Nf_⇇ _) (sym (ne-/H-Hit _ hit))
               (Nf⇇-∙∙ x/ρ⇇j/ρ (Sp⇉-/H (kd-kds j-kd) j⇉as⇉l ρ⇇Γ) ⌊j/ρ⌋≡k)
    Ne∈-/H (∈-∙ x∈j j⇉as⇉l) ρ⇇Γ | no y miss =
      let y∈j/ρ , j-kd = Var⇇-Miss-/H y miss x∈j ρ⇇Γ
      in subst (_ ⊢Nf_⇇ _) (sym (ne-/H-Miss _ y miss))
               (Nf⇇-ne (∈-∙ y∈j/ρ (Sp⇉-/H (kd-kds j-kd) j⇉as⇉l ρ⇇Γ)))

    Var⇇-Hit-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {x j} → Hit ρ x →
                  Γ ⊢Var var x ∈ j → Δ ⊢/H ρ ⇇ Γ →
                  Δ ⊢Nf var∙ x /H ρ ⇇ j Kind/H ρ × ⌊ j Kind/H ρ ⌋≡ k × Γ ⊢ j kd
    Var⇇-Hit-/H refl (⇉-var _ Γ-ctx Γ[x]≡kd-j)
                (≃-hsub {_} {_} {n} E≅Γ₂[a] _ a≃a⇇k ⌊k⌋≡l) =
      let Δ-ctx = ctx-/H Γ-ctx (≃-hsub E≅Γ₂[a] E≅Γ₂[a] a≃a⇇k ⌊k⌋≡l)
          a≃a⇇j/ρ , ⌊j/ρ⌋≡k = Var∈-Hit-/H≃ Δ-ctx Γ[x]≡kd-j E≅Γ₂[a] a≃a⇇k ⌊k⌋≡l
          a⇇j/ρ   , _ = ≃-valid a≃a⇇j/ρ
          j-kd        = Var∈-valid (⇉-var (raise n zero) Γ-ctx Γ[x]≡kd-j)
      in a⇇j/ρ , ⌊j/ρ⌋≡k , j-kd
    Var⇇-Hit-/H hit (⇇-⇑ x∈j₁ j₁<∷j₂ j₂-kd) ρ⇇Γ =
      let x/ρ⇇j₁/ρ , ⌊j₁/ρ⌋≡k , _ = Var⇇-Hit-/H hit x∈j₁ ρ⇇Γ
          j₁/ρ<:j₂/ρ = <∷-/H≃ j₁<∷j₂ ρ⇇Γ
      in Nf⇇-⇑ x/ρ⇇j₁/ρ j₁/ρ<:j₂/ρ ,
         ⌊⌋≡-trans (sym (<∷-⌊⌋ j₁/ρ<:j₂/ρ)) ⌊j₁/ρ⌋≡k ,
         j₂-kd

    Var⇇-Miss-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {x j} y → Miss ρ x y →
                   Γ ⊢Var var x ∈ j → Δ ⊢/H ρ ⇇ Γ →
                   Δ ⊢Var var y ∈ j Kind/H ρ × Γ ⊢ j kd
    Var⇇-Miss-/H y refl (⇉-var _ Γ-ctx Γ[x]≡kd-j)
                 (≃-hsub {_} {_} {n} E≅Γ₂[a] _ a≃a⇇k ⌊k⌋≡l) =
      let Δ-ctx = ctx-/H Γ-ctx (≃-hsub E≅Γ₂[a] E≅Γ₂[a] a≃a⇇k ⌊k⌋≡l)
          x/ρ⇇j/ρ = Var∈-Miss-/H Δ-ctx Γ[x]≡kd-j E≅Γ₂[a] ⌊k⌋≡l
          j-kd = Var∈-valid (⇉-var (lift n suc y) Γ-ctx Γ[x]≡kd-j)
      in x/ρ⇇j/ρ , j-kd
    Var⇇-Miss-/H y miss (⇇-⇑ x∈j₁ j₁<∷j₂ j₂-kd) ρ⇇Γ =
      let y∈j₁/ρ , _ = Var⇇-Miss-/H y miss x∈j₁ ρ⇇Γ
          j₁/ρ<:j₂/ρ = <∷-/H≃ j₁<∷j₂ ρ⇇Γ
      in ⇇-⇑ y∈j₁/ρ j₁/ρ<:j₂/ρ (kd-/H j₂-kd ρ⇇Γ) , j₂-kd

    -- Hereditary substitutions preserve synthesized kinds of spines.
    Sp⇉-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {as j₁ j₂} →
             ⌊ Γ ⌋Ctx ⊢ j₁ kds → Γ ⊢ j₁ ⇉∙ as ⇉ j₂ → Δ ⊢/H ρ ⇇ Γ →
             Δ ⊢ j₁ Kind/H ρ ⇉∙ as //H ρ ⇉ j₂ Kind/H ρ
    Sp⇉-/H _ ⇉-[] ρ⇇Γ = ⇉-[]
    Sp⇉-/H {k} (kds-Π j₁-kds j₂-kds)
           (⇉-∷ {a} {_} {j₁} {j₂} a⇇j₁ j₁-kd j₂[a]⇉as⇉j₃) ρ⇇Γ =
      ⇉-∷ (Nf⇇-/H a⇇j₁ ρ⇇Γ) (kd-/H j₁-kd ρ⇇Γ)
          (subst (_ ⊢_⇉∙ _ ⇉ _) j₂[a]/ρ≡j₂/ρ[a/ρ]
                 (Sp⇉-/H (kds-/H j₂-kds (∈-hsub [] a∈⌊j₁⌋)) j₂[a]⇉as⇉j₃ ρ⇇Γ))
      where
        a∈⌊j₁⌋ = Nf⇇-Nf∈ a⇇j₁

        j₂[a]/ρ≡j₂/ρ[a/ρ] = begin
            j₂ Kind[ a ∈ ⌊ j₁ ⌋ ] Kind/H _
          ≡⟨ kds-[]-/H-↑⋆ [] j₂-kds a∈⌊j₁⌋ (/H⇇-/H∈ ρ⇇Γ) ⟩
            j₂ Kind/H _ H↑ Kind/H 0 ← (a /H _) ∈ ⌊ j₁ ⌋
          ≡⟨ cong (_ Kind[ a /H _ ∈_]) (sym (⌊⌋-Kind/H j₁)) ⟩
            (j₂ Kind/H _ H↑) Kind[ a /H _ ∈ ⌊ j₁ Kind/H _ ⌋ ]
          ∎

    -- Hereditary substitutions preserve checked kinds of normal
    -- types.
    Nf⇇-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {a j} →
             Γ ⊢Nf a ⇇ j → Δ ⊢/H ρ ⇇ Γ → Δ ⊢Nf a /H ρ ⇇ j Kind/H ρ
    Nf⇇-/H (⇇-⇑ a⇉j j<∷k) ρ⇇Γ = ⇇-⇑ (Nf⇉-/H a⇉j ρ⇇Γ) (<∷-/H≃ j<∷k ρ⇇Γ)

    -- Parallel hereditary substitutions map well-formed ascriptions
    -- to identities.
    wf-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a} →
             Γ ⊢ a wf → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ a Asc/H ρ ≅ a Asc/H σ wf
    wf-/H≃ (wf-kd k-kd)  ρ≃σ⇇Γ = ≅-kd (kd-/H≃-≅ k-kd ρ≃σ⇇Γ)
    wf-/H≃ (wf-tp a⇉a⋯a) ρ≃σ⇇Γ =
      let a/ρ⇉a/ρ⋯a/ρ = Nf⇉-/H a⇉a⋯a (/H≃-valid₁ ρ≃σ⇇Γ)
          a/σ⇉a/σ⋯a/σ = Nf⇉-/H a⇉a⋯a (/H≃-valid₂ ρ≃σ⇇Γ)
          a/ρ⋯a/ρ-kd  = kd-⋯ a/ρ⇉a/ρ⋯a/ρ a/ρ⇉a/ρ⋯a/ρ
          a/ρ<:a/σ    = Nf⇉-⋯-/H≃ a⇉a⋯a ρ≃σ⇇Γ
          a/σ<:a/ρ    = Nf⇉-⋯-/H≃ a⇉a⋯a (/H≃-sym ρ≃σ⇇Γ)
          a/ρ⇇a/ρ⋯a/ρ = Nf⇉⇒Nf⇇ a/ρ⇉a/ρ⋯a/ρ
          a/σ⇇a/ρ⋯a/ρ = ⇇-⇑ a/σ⇉a/σ⋯a/σ (<∷-⋯ a/ρ<:a/σ a/σ<:a/ρ)
      in ≅-tp (<:-antisym a/ρ⋯a/ρ-kd
                          (<:-⇇ a/ρ⇇a/ρ⋯a/ρ a/σ⇇a/ρ⋯a/ρ a/ρ<:a/σ)
                          (<:-⇇ a/σ⇇a/ρ⋯a/ρ a/ρ⇇a/ρ⋯a/ρ a/σ<:a/ρ))

    -- Parallel hereditary substitutions well-formed kinds to
    -- subkinds.
    kd-/H≃-<∷ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {k} →
                Γ ⊢ k kd → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                Δ ⊢ k Kind/H ρ <∷ k Kind/H σ
    kd-/H≃-<∷ (kd-⋯ a⇉a⋯a b⇉b⋯b) ρ≃σ⇇Γ =
      <∷-⋯ (Nf⇉-⋯-/H≃ a⇉a⋯a (/H≃-sym ρ≃σ⇇Γ)) (Nf⇉-⋯-/H≃ b⇉b⋯b ρ≃σ⇇Γ)
    kd-/H≃-<∷ (kd-Π j-kd k-kd)   ρ≃σ⇇Γ =
      let ρ⇇Γ     = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ     = /H≃-valid₂ ρ≃σ⇇Γ
          σ≃ρ⇇Γ   = /H≃-sym ρ≃σ⇇Γ
          j/ρ≅j/ρ = kd-/H≃-≅ j-kd ρ⇇Γ
          j/σ≅j/σ = kd-/H≃-≅ j-kd σ⇇Γ
          j/σ≅j/ρ = kd-/H≃-≅ j-kd σ≃ρ⇇Γ
      in <∷-Π (kd-/H≃-<∷ j-kd σ≃ρ⇇Γ)
              (kd-/H≃-<∷ k-kd (≃-H↑ (≅-kd j/σ≅j/ρ) (≅-kd j/σ≅j/σ) ρ≃σ⇇Γ))
              (kd-Π (kd-/H j-kd ρ⇇Γ) (kd-/H k-kd (⇇-H↑ (≅-kd j/ρ≅j/ρ) ρ⇇Γ)))

    -- Parallel hereditary substitutions map well-formed kinds to kind
    -- identities.
    kd-/H≃-≅ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {k} →
               Γ ⊢ k kd → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ k Kind/H ρ ≅ k Kind/H σ
    kd-/H≃-≅ k-kd ρ≃σ⇇Γ =
      <∷-antisym (kd-/H k-kd (/H≃-valid₁ ρ≃σ⇇Γ))
                 (kd-/H k-kd (/H≃-valid₂ ρ≃σ⇇Γ))
                 (kd-/H≃-<∷ k-kd ρ≃σ⇇Γ) (kd-/H≃-<∷ k-kd (/H≃-sym ρ≃σ⇇Γ))

    -- Parallel hereditary substitutions map normal forms to subtypes.

    Nf⇉-⋯-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a b c} →
                Γ ⊢Nf a ⇉ b ⋯ c → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ a /H ρ <: a /H σ
    Nf⇉-⋯-/H≃ (⇉-⊥-f Γ-ctx) ρ≃σ⇇Γ =
      <:-⊥ (⇉-⊥-f (ctx-/H Γ-ctx (/H≃-valid₁ ρ≃σ⇇Γ)))
    Nf⇉-⋯-/H≃ (⇉-⊤-f Γ-ctx) ρ≃σ⇇Γ =
      <:-⊤ (⇉-⊤-f (ctx-/H Γ-ctx (/H≃-valid₂ ρ≃σ⇇Γ)))
    Nf⇉-⋯-/H≃ (⇉-∀-f k-kd a⇉a⋯a) ρ≃σ⇇Γ =
      let ρ⇇Γ       = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ       = /H≃-valid₂ ρ≃σ⇇Γ
          σ≃ρ⇇Γ     = /H≃-sym  ρ≃σ⇇Γ
          k/σ≅k/σ   = kd-/H≃-≅ k-kd σ⇇Γ
          k/ρ≅k/ρ   = kd-/H≃-≅ k-kd ρ⇇Γ
          k/σ≅k/ρ   = kd-/H≃-≅ k-kd σ≃ρ⇇Γ
          ρ≃σ⇇j/σ∷Γ = ≃-H↑ (≅-kd k/σ≅k/ρ) (≅-kd k/σ≅k/σ) ρ≃σ⇇Γ
      in <:-∀ (≅⇒<∷ k/σ≅k/ρ) (Nf⇉-⋯-/H≃ a⇉a⋯a ρ≃σ⇇j/σ∷Γ)
              (⇉-∀-f (kd-/H k-kd ρ⇇Γ)
                     (Nf⇉-/H a⇉a⋯a (⇇-H↑ (≅-kd k/ρ≅k/ρ) ρ⇇Γ)))
    Nf⇉-⋯-/H≃ (⇉-→-f a⇉a⋯a b⇉b⋯b) ρ≃σ⇇Γ =
      <:-→ (Nf⇉-⋯-/H≃ a⇉a⋯a (/H≃-sym ρ≃σ⇇Γ)) (Nf⇉-⋯-/H≃ b⇉b⋯b ρ≃σ⇇Γ)
    Nf⇉-⋯-/H≃ (⇉-s-i a∈b⋯c) ρ≃σ⇇Γ = Ne∈-/H≃ a∈b⋯c ρ≃σ⇇Γ

    Nf⇉-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a j} →
              Γ ⊢Nf a ⇉ j → Γ ⊢ j kd → Δ ⊢/H ρ ≃ σ ⇇ Γ →
              Δ ⊢ a /H ρ <: a /H σ ⇇ j Kind/H ρ
    Nf⇉-/H≃ a⇉b⋯c (kd-⋯ b⇉b⋯b c⇉c⋯c) ρ≃σ⇇Γ =
      let ρ⇇Γ   = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ   = /H≃-valid₂ ρ≃σ⇇Γ
          σ≃ρ⇇Γ = /H≃-sym ρ≃σ⇇Γ
      in <:-⇇ (Nf⇉⇒Nf⇇ (Nf⇉-/H a⇉b⋯c ρ⇇Γ))
              (⇇-⇑ (Nf⇉-/H a⇉b⋯c σ⇇Γ)
                   (<∷-⋯ (Nf⇉-⋯-/H≃ b⇉b⋯b ρ≃σ⇇Γ) (Nf⇉-⋯-/H≃ c⇉c⋯c σ≃ρ⇇Γ)))
              (Nf⇉-⋯-/H≃ a⇉b⋯c ρ≃σ⇇Γ)
    Nf⇉-/H≃ (⇉-Π-i _ a⇉l) (kd-Π j-kd l-kd) ρ≃σ⇇Γ =
      let σ≃ρ⇇Γ = /H≃-sym ρ≃σ⇇Γ
          ρ⇇Γ   = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ   = /H≃-valid₂ ρ≃σ⇇Γ
          j/ρ-kd  = kd-/H j-kd ρ⇇Γ
          j/σ-kd  = kd-/H j-kd σ⇇Γ
          j/ρ≅j/ρ = kd-/H≃-≅ j-kd ρ⇇Γ
          j/σ≅j/σ = kd-/H≃-≅ j-kd σ⇇Γ
          j/ρ≅j/σ = kd-/H≃-≅ j-kd ρ≃σ⇇Γ
          a/ρ⇉l/ρ = Nf⇉-/H a⇉l (⇇-H↑ (≅-kd j/ρ≅j/ρ) ρ⇇Γ)
          a/σ⇉l/σ = Nf⇉-/H a⇉l (⇇-H↑ (≅-kd j/σ≅j/σ) σ⇇Γ)
          a/ρ<:a/σ⇇l/ρ = Nf⇉-/H≃ a⇉l l-kd (≃-H↑ (≅-kd j/ρ≅j/ρ) (≅-kd j/ρ≅j/σ)
                                                ρ≃σ⇇Γ)
          Πjl/σ<∷Πjl/ρ = kd-/H≃-<∷ (kd-Π j-kd l-kd) σ≃ρ⇇Γ
          Λja/ρ⇇Πjl/ρ = Nf⇉⇒Nf⇇ (⇉-Π-i j/ρ-kd a/ρ⇉l/ρ)
          Λja/σ⇇Πjl/ρ = ⇇-⇑ (⇉-Π-i j/σ-kd a/σ⇉l/σ) Πjl/σ<∷Πjl/ρ
      in <:-λ a/ρ<:a/σ⇇l/ρ Λja/ρ⇇Πjl/ρ Λja/σ⇇Πjl/ρ

    -- Parallel hereditary substitutions map proper neutrals to subtypes.
    Ne∈-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a b c} →
              Γ ⊢Ne a ∈ b ⋯ c → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ a /H ρ <: a /H σ
    Ne∈-/H≃ {ρ = ρ} (∈-∙ {x} x∈j j⇉as⇉k) ρ≃σ⇇Γ with hit? ρ x
    Ne∈-/H≃ (∈-∙ x∈j j⇉as⇉l) ρ≃σ⇇Γ | yes ρ-hit =
      let σ-hit = /H≃-Hit ρ≃σ⇇Γ ρ-hit
          x/ρ≃x/σ⇇j/ρ , ⌊j/ρ⌋≡k , j-kd = Var⇇-Hit-/H≃ ρ-hit x∈j ρ≃σ⇇Γ
      in subst₂ (_ ⊢_<:_)
                (sym (ne-/H-Hit _ ρ-hit)) (sym (ne-/H-Hit _ σ-hit))
                (≃⇒<:-⋯ (≃-∙∙ x/ρ≃x/σ⇇j/ρ
                              (Sp⇉-/H≃ (kd-kds j-kd) j⇉as⇉l ρ≃σ⇇Γ) ⌊j/ρ⌋≡k))
    Ne∈-/H≃ (∈-∙ x∈j j⇉as⇉l) ρ≃σ⇇Γ | no y ρ-miss =
      let σ-miss = /H≃-Miss ρ≃σ⇇Γ ρ-miss
          y∈j/ρ , j-kds = Var⇇-Miss-/H y ρ-miss x∈j (/H≃-valid₁ ρ≃σ⇇Γ)
      in subst₂ (_ ⊢_<:_)
                (sym (ne-/H-Miss _ y ρ-miss)) (sym (ne-/H-Miss _ y σ-miss))
                (<:-∙ y∈j/ρ (Sp⇉-/H≃ (kd-kds j-kds) j⇉as⇉l ρ≃σ⇇Γ))

    Var⇇-Hit-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {x j} → Hit ρ x →
                   Γ ⊢Var var x ∈ j → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                   Δ ⊢ var∙ x /H ρ ≃ var∙ x /H σ ⇇ j Kind/H ρ ×
                     ⌊ j Kind/H ρ ⌋≡ k × Γ ⊢ j kd
    Var⇇-Hit-/H≃ refl (⇉-var _ Γ-ctx Γ[x]≡kd-j)
                (≃-hsub {_} {_} {n} E≅Γ₂[a] E≅Γ₂[b] a≃b⇇k ⌊k⌋≡l) =
      let a⇇k , b⇇k = ≃-valid    a≃b⇇k
          k-kd      = ≃-valid-kd a≃b⇇k
          Δ-ctx     = ctx-/H Γ-ctx (⇇-hsub E≅Γ₂[a] a⇇k k-kd ⌊k⌋≡l)
          a≃b⇇j/ρ , ⌊j/ρ⌋≡k = Var∈-Hit-/H≃ Δ-ctx Γ[x]≡kd-j E≅Γ₂[a] a≃b⇇k ⌊k⌋≡l
          j-kd = Var∈-valid (⇉-var (raise n zero) Γ-ctx Γ[x]≡kd-j)
      in a≃b⇇j/ρ , ⌊j/ρ⌋≡k , j-kd
    Var⇇-Hit-/H≃ hit (⇇-⇑ x∈j₁ j₁<∷j₂ j₂-kd) ρ≃σ⇇Γ =
      let x/ρ≃x/ρ⇇j₁/ρ , ⌊j₁/ρ⌋≡k , _ = Var⇇-Hit-/H≃ hit x∈j₁ ρ≃σ⇇Γ
          j₁/ρ<:j₂/ρ = <∷-/H≃ j₁<∷j₂ (/H≃-valid₁ ρ≃σ⇇Γ)
          j₂/ρ-kd = kd-/H j₂-kd (/H≃-valid₁ ρ≃σ⇇Γ)
      in ≃-⇑ x/ρ≃x/ρ⇇j₁/ρ j₁/ρ<:j₂/ρ j₂/ρ-kd ,
         ⌊⌋≡-trans (sym (<∷-⌊⌋ j₁/ρ<:j₂/ρ)) ⌊j₁/ρ⌋≡k ,
         j₂-kd

    -- Parallel hereditary substitutions map spines to spine identities.
    Sp⇉-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {as j₁ j₂} →
              ⌊ Γ ⌋Ctx ⊢ j₁ kds → Γ ⊢ j₁ ⇉∙ as ⇉ j₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ →
              Δ ⊢ j₁ Kind/H ρ ⇉∙ as //H ρ ≃ as //H σ ⇉ j₂ Kind/H ρ
    Sp⇉-/H≃ _ ⇉-[] ρ⇇Γ = ≃-[]
    Sp⇉-/H≃ {k} (kds-Π j₁-kds j₂-kds)
            (⇉-∷ {a} {_} {j₁} {j₂} a⇇j₁ j₁-kd j₂[a]⇉as⇉j₃) ρ⇇Γ =
      ≃-∷ (Nf⇇-/H≃-≃ a⇇j₁ j₁-kd ρ⇇Γ)
          (subst (_ ⊢_⇉∙ _ ≃ _ ⇉ _) j₂[a]/ρ≡j₂/ρ[a/ρ]
                 (Sp⇉-/H≃ (kds-/H j₂-kds (∈-hsub [] a∈⌊j₁⌋)) j₂[a]⇉as⇉j₃ ρ⇇Γ))
      where
        a∈⌊j₁⌋ = Nf⇇-Nf∈ a⇇j₁

        j₂[a]/ρ≡j₂/ρ[a/ρ] = begin
            j₂ Kind[ a ∈ ⌊ j₁ ⌋ ] Kind/H _
          ≡⟨ kds-[]-/H-↑⋆ [] j₂-kds a∈⌊j₁⌋ (/H⇇-/H∈ (/H≃-valid₁ ρ⇇Γ)) ⟩
            j₂ Kind/H _ H↑ Kind/H 0 ← (a /H _) ∈ ⌊ j₁ ⌋
          ≡⟨ cong (_ Kind[ a /H _ ∈_]) (sym (⌊⌋-Kind/H j₁)) ⟩
            (j₂ Kind/H _ H↑) Kind[ a /H _ ∈ ⌊ j₁ Kind/H _ ⌋ ]
          ∎

    -- Parallel hereditary substitutions map checked normal forms to
    -- subtypes.
    Nf⇇-/H≃-<: : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a j} →
                 Γ ⊢Nf a ⇇ j → Γ ⊢ j kd → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                 Δ ⊢ a /H ρ <: a /H σ ⇇ j Kind/H ρ
    Nf⇇-/H≃-<: (⇇-⇑ a⇉b₁⋯c₁ (<∷-⋯ b₂<:b₁ c₁<:c₂)) _ ρ≃σ⇇Γ =
      let ρ⇇Γ   = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ   = /H≃-valid₂ ρ≃σ⇇Γ
          σ≃ρ⇇Γ = /H≃-sym ρ≃σ⇇Γ
      in <:-⇇ (⇇-⇑ (Nf⇉-/H a⇉b₁⋯c₁ ρ⇇Γ) (<∷-/H≃ (<∷-⋯ b₂<:b₁ c₁<:c₂) ρ⇇Γ))
              (⇇-⇑ (Nf⇉-/H a⇉b₁⋯c₁ σ⇇Γ) (<∷-/H≃ (<∷-⋯ b₂<:b₁ c₁<:c₂) σ≃ρ⇇Γ))
              (Nf⇉-⋯-/H≃ a⇉b₁⋯c₁ ρ≃σ⇇Γ)
    Nf⇇-/H≃-<: (⇇-⇑ a⇉Πj₁l₁ (<∷-Π j₂<∷j₁ l₁<∷l₂ Πj₁l₁-kd)) Πj₂k₂-kd ρ≃σ⇇Γ =
      let ρ⇇Γ = /H≃-valid₁ ρ≃σ⇇Γ
          Πj₁l₁/ρ<∷Πj₂l₂/ρ = <∷-/H≃ (<∷-Π j₂<∷j₁ l₁<∷l₂ Πj₁l₁-kd) ρ⇇Γ
          Πj₂l₂/ρ-kd       = kd-/H Πj₂k₂-kd ρ⇇Γ
      in <:⇇-⇑ (Nf⇉-/H≃ a⇉Πj₁l₁ Πj₁l₁-kd ρ≃σ⇇Γ) Πj₁l₁/ρ<∷Πj₂l₂/ρ Πj₂l₂/ρ-kd

    -- Parallel hereditary substitutions map checked normal forms to
    -- type identities.
    Nf⇇-/H≃-≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a k} →
                Γ ⊢Nf a ⇇ k → Γ ⊢ k kd → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                Δ ⊢ a /H ρ ≃ a /H σ ⇇ k Kind/H ρ
    Nf⇇-/H≃-≃ a⇇k k-kd ρ≃σ⇇Γ =
      let σ≃ρ⇇Γ  = /H≃-sym ρ≃σ⇇Γ
          k/ρ-kd = kd-/H k-kd (/H≃-valid₁ ρ≃σ⇇Γ)
      in <:-antisym k/ρ-kd (Nf⇇-/H≃-<: a⇇k k-kd ρ≃σ⇇Γ)
                    (<:⇇-⇑ (Nf⇇-/H≃-<: a⇇k k-kd σ≃ρ⇇Γ)
                    (kd-/H≃-<∷ k-kd σ≃ρ⇇Γ) k/ρ-kd)

    -- Parallel hereditary substitutions preserve subkinding.
    <∷-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {j₁ j₂} →
             Γ ⊢ j₁ <∷ j₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ j₁ Kind/H ρ <∷ j₂ Kind/H σ
    <∷-/H≃ (<∷-⋯ a₂<:a₁ b₁<:b₂) ρ≃σ⇇Γ =
      <∷-⋯ (<:-/H≃ a₂<:a₁ (/H≃-sym ρ≃σ⇇Γ)) (<:-/H≃ b₁<:b₂ ρ≃σ⇇Γ)
    <∷-/H≃ (<∷-Π j₂<∷j₁ k₁<∷k₂ Πj₁k₁-kd) ρ≃σ⇇Γ =
      let σ≃ρ⇇Γ = /H≃-sym ρ≃σ⇇Γ
          σ≃σ⇇Γ = /H≃-valid₂ ρ≃σ⇇Γ
      in <∷-Π (<∷-/H≃ j₂<∷j₁ (/H≃-sym ρ≃σ⇇Γ))
              (<∷-/H≃ k₁<∷k₂ (≃-H↑ (<∷-/H≃-wf k₁<∷k₂ σ≃ρ⇇Γ)
                             (<∷-/H≃-wf k₁<∷k₂ σ≃σ⇇Γ) ρ≃σ⇇Γ))
              (kd-/H Πj₁k₁-kd (/H≃-valid₁ ρ≃σ⇇Γ))

    -- Parallel hereditary substitutions preserve subtyping.

    <:-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a₁ a₂} →
             Γ ⊢ a₁ <: a₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ a₁ /H ρ <: a₂ /H σ
    <:-/H≃ (<:-trans a<:b b<:c) ρ≃σ⇇Γ =
      <:-trans (<:-/H≃ a<:b (/H≃-valid₁ ρ≃σ⇇Γ)) (<:-/H≃ b<:c ρ≃σ⇇Γ)
    <:-/H≃ (<:-⊥ a⇉a⋯a) ρ≃σ⇇Γ = <:-⊥ (Nf⇉-/H a⇉a⋯a (/H≃-valid₂ ρ≃σ⇇Γ))
    <:-/H≃ (<:-⊤ a⇉a⋯a) ρ≃σ⇇Γ = <:-⊤ (Nf⇉-/H a⇉a⋯a (/H≃-valid₁ ρ≃σ⇇Γ))
    <:-/H≃ (<:-∀ k₂<∷k₁ a₁<:a₂ Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁) ρ≃σ⇇Γ =
      let σ≃ρ⇇Γ = /H≃-sym ρ≃σ⇇Γ
          σ≃σ⇇Γ = /H≃-valid₂ ρ≃σ⇇Γ
      in <:-∀ (<∷-/H≃ k₂<∷k₁ σ≃ρ⇇Γ)
              (<:-/H≃ a₁<:a₂ (≃-H↑ (<:-/H≃-wf a₁<:a₂ σ≃ρ⇇Γ)
                                   (<:-/H≃-wf a₁<:a₂ σ≃σ⇇Γ) ρ≃σ⇇Γ))
         (Nf⇉-/H Πk₁a₁⇉Πk₁a₁⋯Πk₁a₁ (/H≃-valid₁ ρ≃σ⇇Γ))
    <:-/H≃ (<:-→ a₂<:a₁ b₁<:b₂) ρ≃σ⇇Γ =
      <:-→ (<:-/H≃ a₂<:a₁ (/H≃-sym ρ≃σ⇇Γ)) (<:-/H≃ b₁<:b₂ ρ≃σ⇇Γ)
    <:-/H≃ {ρ = ρ} (<:-∙ {x} x∈j j⇉as≃bs⇉l) ρ≃σ⇇Γ with hit? ρ x
    <:-/H≃ (<:-∙ x∈j j⇉as≃bs⇉l) ρ≃σ⇇Γ | yes ρ-hit =
      let σ-hit = /H≃-Hit ρ≃σ⇇Γ ρ-hit
          x/ρ≃x/σ⇇j/ρ , ⌊j/ρ⌋≡k , j-kd = Var⇇-Hit-/H≃ ρ-hit x∈j ρ≃σ⇇Γ
      in subst₂ (_ ⊢_<:_)
                (sym (ne-/H-Hit _ ρ-hit)) (sym (ne-/H-Hit _ σ-hit))
                (≃⇒<:-⋯ (≃-∙∙ x/ρ≃x/σ⇇j/ρ
                              (Sp≃-/H≃ (kd-kds j-kd) j⇉as≃bs⇉l ρ≃σ⇇Γ) ⌊j/ρ⌋≡k))
    <:-/H≃ (<:-∙ x∈j j⇉as≃bs⇉l) ρ≃σ⇇Γ | no y ρ-miss =
      let σ-miss = /H≃-Miss ρ≃σ⇇Γ ρ-miss
          y∈j/ρ , j-kd = Var⇇-Miss-/H y ρ-miss x∈j (/H≃-valid₁ ρ≃σ⇇Γ)
      in subst₂ (_ ⊢_<:_)
                (sym (ne-/H-Miss _ y ρ-miss)) (sym (ne-/H-Miss _ y σ-miss))
                (<:-∙ y∈j/ρ (Sp≃-/H≃ (kd-kds j-kd) j⇉as≃bs⇉l ρ≃σ⇇Γ))
    <:-/H≃ (<:-⟨| a∈b⋯c) ρ≃σ⇇Γ =
      let a/ρ⇉b/ρ⋯c/ρ = Ne∈-/H a∈b⋯c (/H≃-valid₁ ρ≃σ⇇Γ)
      in <:-trans (<:-⟨|-Nf⇇ a/ρ⇉b/ρ⋯c/ρ) (Ne∈-/H≃ a∈b⋯c ρ≃σ⇇Γ)
    <:-/H≃ (<:-|⟩ a∈b⋯c) ρ≃σ⇇Γ =
      let a/σ⇉b/σ⋯c/σ = Ne∈-/H a∈b⋯c (/H≃-valid₂ ρ≃σ⇇Γ)
      in <:-trans (Ne∈-/H≃ a∈b⋯c ρ≃σ⇇Γ) (<:-|⟩-Nf⇇ a/σ⇉b/σ⋯c/σ)

    <:⇇-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a₁ a₂ j} →
              Γ ⊢ a₁ <: a₂ ⇇ j → Γ ⊢ j kd → Δ ⊢/H ρ ≃ σ ⇇ Γ →
              Δ ⊢ a₁ /H ρ <: a₂ /H σ ⇇ j Kind/H ρ
    <:⇇-/H≃ (<:-⇇ a₁⇇b⋯c a₂⇇b⋯c a₁<:a₂) b⋯c-kd ρ≃σ⇇Γ =
      let ρ⇇Γ     = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ     = /H≃-valid₂ ρ≃σ⇇Γ
          σ≃ρ⇇Γ   = /H≃-sym ρ≃σ⇇Γ
      in <:-⇇ (Nf⇇-/H a₁⇇b⋯c ρ⇇Γ)
              (Nf⇇-⇑ (Nf⇇-/H a₂⇇b⋯c σ⇇Γ) (kd-/H≃-<∷ b⋯c-kd σ≃ρ⇇Γ))
              (<:-/H≃ a₁<:a₂ ρ≃σ⇇Γ)
    <:⇇-/H≃ (<:-λ a₁<:a₂⇇l Λj₁a₁⇇Πjl Λj₂a₂⇇Πjl) (kd-Π j-kd l-kd) ρ≃σ⇇Γ =
      let ρ⇇Γ     = /H≃-valid₁ ρ≃σ⇇Γ
          σ⇇Γ     = /H≃-valid₂ ρ≃σ⇇Γ
          σ≃ρ⇇Γ   = /H≃-sym ρ≃σ⇇Γ
          j/ρ≅j/ρ = kd-/H≃-≅ j-kd ρ⇇Γ
          j/ρ≅j/σ = kd-/H≃-≅ j-kd ρ≃σ⇇Γ
      in <:-λ (<:⇇-/H≃ a₁<:a₂⇇l l-kd (≃-H↑ (≅-kd j/ρ≅j/ρ) (≅-kd j/ρ≅j/σ) ρ≃σ⇇Γ))
              (Nf⇇-/H Λj₁a₁⇇Πjl ρ⇇Γ)
              (Nf⇇-⇑ (Nf⇇-/H Λj₂a₂⇇Πjl σ⇇Γ) (kd-/H≃-<∷ (kd-Π j-kd l-kd) σ≃ρ⇇Γ))

    -- Parallel hereditary substitutions preserve spine equality.
    Sp≃-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {as₁ as₂ j₁ j₂} →
              ⌊ Γ ⌋Ctx ⊢ j₁ kds → Γ ⊢ j₁ ⇉∙ as₁ ≃ as₂ ⇉ j₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ →
              Δ ⊢ j₁ Kind/H ρ ⇉∙ as₁ //H ρ ≃ as₂ //H σ ⇉ j₂ Kind/H ρ
    Sp≃-/H≃ _ ≃-[] ρ≃σ⇇Γ = ≃-[]
    Sp≃-/H≃ {k} (kds-Π j₁-kds j₂-kds)
            (≃-∷ {a} {j = j₁} {j₂} a≃b as≃bs) ρ≃σ⇇Γ =
      let a∈⌊j₁⌋            = Nf⇇-Nf∈ (proj₁ (≃-valid a≃b))
          j₂[a]/ρ≡j₂/ρ[a/ρ] = begin
              j₂ Kind[ a ∈ ⌊ j₁ ⌋ ] Kind/H _
            ≡⟨ kds-[]-/H-↑⋆ [] j₂-kds a∈⌊j₁⌋ (/H⇇-/H∈ (/H≃-valid₁ ρ≃σ⇇Γ)) ⟩
              j₂ Kind/H _ H↑ Kind/H 0 ← (a /H _) ∈ ⌊ j₁ ⌋
            ≡⟨ cong (_ Kind[ a /H _ ∈_]) (sym (⌊⌋-Kind/H j₁)) ⟩
              (j₂ Kind/H _ H↑) Kind[ a /H _ ∈ ⌊ j₁ Kind/H _ ⌋ ]
            ∎
      in ≃-∷ (≃-/H≃ a≃b ρ≃σ⇇Γ)
             (subst (_ ⊢_⇉∙ _ ≃ _ ⇉ _) j₂[a]/ρ≡j₂/ρ[a/ρ]
                    (Sp≃-/H≃ (kds-/H j₂-kds (∈-hsub [] a∈⌊j₁⌋)) as≃bs ρ≃σ⇇Γ))

    -- Parallel hereditary substitutions preserve type equality.
    ≃-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {a₁ a₂ j} →
            Γ ⊢ a₁ ≃ a₂ ⇇ j → Δ ⊢/H ρ ≃ σ ⇇ Γ →
            Δ ⊢ a₁ /H ρ ≃ a₂ /H σ ⇇ j Kind/H ρ
    ≃-/H≃ (<:-antisym k-kd a<:b⇇k b<:a⇇k) ρ≃σ⇇Γ =
      let σ≃ρ⇇Γ = /H≃-sym ρ≃σ⇇Γ
          k/ρ-kd = kd-/H k-kd (/H≃-valid₁ ρ≃σ⇇Γ)
      in <:-antisym k/ρ-kd (<:⇇-/H≃ a<:b⇇k k-kd ρ≃σ⇇Γ)
                    (<:⇇-⇑ (<:⇇-/H≃ b<:a⇇k k-kd σ≃ρ⇇Γ)
                           (kd-/H≃-<∷ k-kd σ≃ρ⇇Γ) k/ρ-kd)

    -- Applications in canonical kind checking are admissible.

    Nf⇇-∙∙ : ∀ {n} {Γ : Ctx n} {a as j₁ j₂ k} →
             Γ ⊢Nf a ⇇ j₁ → Γ ⊢ j₁ ⇉∙ as ⇉ j₂ → ⌊ j₁ ⌋≡ k →
             Γ ⊢Nf a ∙∙⟨ k ⟩ as ⇇ j₂
    Nf⇇-∙∙ a⇇j₁ ⇉-[] ⌊j₁⌋≡k = a⇇j₁
    Nf⇇-∙∙ a⇇Πj₁j₂ (⇉-∷ b⇇j₁ j₁-kd j₂[b]⇉as⇉j₃) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) =
      Nf⇇-∙∙ (Nf⇇-Π-e a⇇Πj₁j₂ b⇇j₁ j₁-kd (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂))
             j₂[b]⇉as⇉j₃ (⌊⌋≡-/H ⌊j₂⌋≡k₂)

    Nf⇇-Π-e : ∀ {n} {Γ : Ctx n} {a b j₁ j₂ k} →
              Γ ⊢Nf a ⇇ Π j₁ j₂ → Γ ⊢Nf b ⇇ j₁ → Γ ⊢ j₁ kd →
              ⌊ Π j₁ j₂ ⌋≡ k → Γ ⊢Nf a ⌜·⌝⟨ k ⟩ b ⇇ j₂ Kind[ b ∈ ⌊ j₁ ⌋ ]
    Nf⇇-Π-e {_} {Γ} {_} {b}
            (⇇-⇑ (⇉-Π-i j₁-kd a⇉l₁)
            (<∷-Π {j₁} {j₂} {l₁} {l₂} j₂<∷j₁ l₁<∷l₂ Πj₁l₁-kd))
            b⇇j₂ j₂-kd (is-⇒ {_} {_} {k₁} ⌊j₂⌋≡k₁ ⌊l₂⌋≡k₂) =
      let ρ⇇j₂∷Γ = ⇇-hsub [] b⇇j₂ j₂-kd ⌊j₂⌋≡k₁
      in ⇇-⇑ (Nf⇉-/H (⇓-Nf⇉ [] j₂-kd j₂<∷j₁ a⇉l₁) ρ⇇j₂∷Γ)
             (subst (λ k → Γ ⊢ l₁ Kind/H _ <∷ l₂ Kind/H 0 ← b ∈ k)
                    (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₂⌋≡k₁))
                    (<∷-/H≃ l₁<∷l₂ ρ⇇j₂∷Γ))

    -- Applications in checked type equality are admissible.

    ≃-∙∙ : ∀ {n} {Γ : Ctx n} {a b as bs j₁ j₂ k} →
           Γ ⊢ a ≃ b ⇇ j₁ → Γ ⊢ j₁ ⇉∙ as ≃ bs ⇉ j₂ → ⌊ j₁ ⌋≡ k →
           Γ ⊢ a ∙∙⟨ k ⟩ as ≃ b ∙∙⟨ k ⟩ bs ⇇ j₂
    ≃-∙∙ a≃b⇇j₁ ≃-[] ⌊j₁⌋≡k = a≃b⇇j₁
    ≃-∙∙ a≃b⇇Πj₁j₂ (≃-∷ c≃d⇇j₁ j₂[b]⇉cs≃ds⇉j₃) (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂) =
      ≃-∙∙ (≃-Π-e a≃b⇇Πj₁j₂ c≃d⇇j₁ (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂))
           j₂[b]⇉cs≃ds⇉j₃ (⌊⌋≡-/H ⌊j₂⌋≡k₂)

    ≃-Π-e : ∀ {n} {Γ : Ctx n} {a₁ a₂ b₁ b₂ j₁ j₂ k} →
            Γ ⊢ a₁ ≃ a₂ ⇇ Π j₁ j₂ → Γ ⊢ b₁ ≃ b₂ ⇇ j₁ → ⌊ Π j₁ j₂ ⌋≡ k →
            Γ ⊢ a₁ ⌜·⌝⟨ k ⟩ b₁ ≃ a₂ ⌜·⌝⟨ k ⟩ b₂ ⇇ j₂ Kind[ b₁ ∈ ⌊ j₁ ⌋ ]
    ≃-Π-e a₁≃a₂⇇Πj₁j₂ b₁≃b₂⇇j₂ (is-⇒ ⌊j₂⌋≡k₁ ⌊j₂⌋≡k₂) with ≃-Π-can a₁≃a₂⇇Πj₁j₂
    ≃-Π-e {_} {Γ} {_} {_} {b₁} {b₂} Λl₁a₁≃Λl₂a₂⇇Πj₁j₂ b₁≃b₂⇇j₁
          (is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂)
      | l₁ , a₁ , l₂ , a₂ , Λl₁a₁⇇Πj₁j₂ , Λl₂a₂⇇Πj₁j₂ , kd-Π j₁-kd j₂-kd ,
        j₁<∷l₁ , l₁≅l₂ , a₁<:a₂⇇j₂ , a₂<:a₁⇇j₂ , refl , refl =
        let ⌊Πj₁j₂⌋≡k     = is-⇒ ⌊j₁⌋≡k₁ ⌊j₂⌋≡k₂
            k₁≡⌊j₁⌋       = sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁)
            b₁⇇j₁ , b₂⇇j₁ = ≃-valid b₁≃b₂⇇j₁
            ρ≃σ⇇j₁∷Γ      = ≃-hsub [] [] b₁≃b₂⇇j₁ ⌊j₁⌋≡k₁
            σ≃ρ⇇j₁∷Γ      = /H≃-sym ρ≃σ⇇j₁∷Γ
            ρ⇇j₁∷Γ        = /H≃-valid₁ ρ≃σ⇇j₁∷Γ
        in <:-antisym (subst (λ k → _ ⊢ _ Kind[ _ ∈ k ] kd)
                             (sym (⌊⌋≡⇒⌊⌋-≡ ⌊j₁⌋≡k₁))
                             (kd-/H j₂-kd (/H≃-valid₁ ρ≃σ⇇j₁∷Γ)))
                      (subst (λ k → _ ⊢ _ <: _ ⇇ _ Kind[ _ ∈ k ]) k₁≡⌊j₁⌋
                             (<:⇇-/H≃ a₁<:a₂⇇j₂ j₂-kd ρ≃σ⇇j₁∷Γ))
                      (<:⇇-⇑ (<:⇇-/H≃ a₂<:a₁⇇j₂ j₂-kd σ≃ρ⇇j₁∷Γ)
                             (subst (λ k → Γ ⊢ _ <∷ _ Kind[ _ ∈ k ]) k₁≡⌊j₁⌋
                                    (kd-/H≃-<∷ j₂-kd σ≃ρ⇇j₁∷Γ))
                             (subst (λ k → Γ ⊢ _ Kind[ _ ∈ k ] kd) k₁≡⌊j₁⌋
                                    (kd-/H j₂-kd ρ⇇j₁∷Γ)))

    -- Helpers (to satisfy the termination checker).
    --
    -- These are simply (manual) expansions of the form
    --
    --   XX-/H≃-wf x ρ≃σ⇇Γ  =  wf-/H≃ (wf-∷₁ (XX-ctx x)) ρ≃σ⇇Γ
    --
    -- to ensure the above definitions remain structurally recursive
    -- in the various derivations.

    kd-/H≃-wf : ∀ {l m n Γ Δ} {ρ σ : HSub l m n} {j k} →
                kd j ∷ Γ ⊢ k kd → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                Δ ⊢ kd (j Kind/H ρ) ≅ kd (j Kind/H σ) wf
    kd-/H≃-wf (kd-⋯ a⇉a⋯a _) ρ≃σ⇇Γ = Nf⇉-/H≃-wf a⇉a⋯a ρ≃σ⇇Γ
    kd-/H≃-wf (kd-Π j-kd _)  ρ≃σ⇇Γ = kd-/H≃-wf j-kd ρ≃σ⇇Γ

    Nf⇉-/H≃-wf : ∀ {l m n Γ Δ} {ρ σ : HSub l m n} {j a k} →
                 kd j ∷ Γ ⊢Nf a ⇉ k → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                 Δ ⊢ kd (j Kind/H ρ) ≅ kd (j Kind/H σ) wf
    Nf⇉-/H≃-wf (⇉-⊥-f (j-wf ∷ Γ-ctx)) ρ≃σ⇇Γ = wf-/H≃ j-wf ρ≃σ⇇Γ
    Nf⇉-/H≃-wf (⇉-⊤-f (j-wf ∷ Γ-ctx)) ρ≃σ⇇Γ = wf-/H≃ j-wf ρ≃σ⇇Γ
    Nf⇉-/H≃-wf (⇉-∀-f k-kd _)         ρ≃σ⇇Γ = kd-/H≃-wf k-kd ρ≃σ⇇Γ
    Nf⇉-/H≃-wf (⇉-→-f a⇉a⋯a _)        ρ≃σ⇇Γ = Nf⇉-/H≃-wf a⇉a⋯a ρ≃σ⇇Γ
    Nf⇉-/H≃-wf (⇉-Π-i j-kd _)         ρ≃σ⇇Γ = kd-/H≃-wf j-kd ρ≃σ⇇Γ
    Nf⇉-/H≃-wf (⇉-s-i a∈b⋯c)          ρ≃σ⇇Γ = Ne∈-/H≃-wf a∈b⋯c ρ≃σ⇇Γ

    Ne∈-/H≃-wf : ∀ {l m n Γ Δ} {ρ σ : HSub l m n} {j a k} →
                 kd j ∷ Γ ⊢Ne a ∈ k → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                 Δ ⊢ kd (j Kind/H ρ) ≅ kd (j Kind/H σ) wf
    Ne∈-/H≃-wf (∈-∙ x∈k _) ρ≃σ⇇Γ = Var∈-/H≃-wf x∈k ρ≃σ⇇Γ

    Var∈-/H≃-wf : ∀ {l m n Γ Δ} {ρ σ : HSub l m n} {j a k} →
                  kd j ∷ Γ ⊢Var a ∈ k → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                  Δ ⊢ kd (j Kind/H ρ) ≅ kd (j Kind/H σ) wf
    Var∈-/H≃-wf (⇉-var x (j-wf ∷ Γ-ctx) _) ρ≃σ⇇Γ = wf-/H≃ j-wf ρ≃σ⇇Γ
    Var∈-/H≃-wf (⇇-⇑ x∈k _ _)              ρ≃σ⇇Γ = Var∈-/H≃-wf x∈k ρ≃σ⇇Γ

    <∷-/H≃-wf : ∀ {l m n Γ Δ} {ρ σ : HSub l m n} {j k₁ k₂} →
                kd j ∷ Γ ⊢ k₁ <∷ k₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                Δ ⊢ kd (j Kind/H ρ) ≅ kd (j Kind/H σ) wf
    <∷-/H≃-wf (<∷-⋯ a₂<:a₁ _)   ρ≃σ⇇Γ = <:-/H≃-wf a₂<:a₁ ρ≃σ⇇Γ
    <∷-/H≃-wf (<∷-Π j₁<∷j₂ _ _) ρ≃σ⇇Γ = <∷-/H≃-wf j₁<∷j₂ ρ≃σ⇇Γ

    <:-/H≃-wf : ∀ {l m n Γ Δ} {ρ σ : HSub l m n} {j a₁ a₂} →
                kd j ∷ Γ ⊢ a₁ <: a₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ →
                Δ ⊢ kd (j Kind/H ρ) ≅ kd (j Kind/H σ) wf
    <:-/H≃-wf (<:-trans a<:b _) ρ≃σ⇇Γ = <:-/H≃-wf a<:b ρ≃σ⇇Γ
    <:-/H≃-wf (<:-⊥ a⇉a⋯a)      ρ≃σ⇇Γ = Nf⇉-/H≃-wf a⇉a⋯a ρ≃σ⇇Γ
    <:-/H≃-wf (<:-⊤ a⇉a⋯a)      ρ≃σ⇇Γ = Nf⇉-/H≃-wf a⇉a⋯a ρ≃σ⇇Γ
    <:-/H≃-wf (<:-∀ k₂<∷k₁ _ _) ρ≃σ⇇Γ = <∷-/H≃-wf k₂<∷k₁ ρ≃σ⇇Γ
    <:-/H≃-wf (<:-→ a₂<:a₁ _)   ρ≃σ⇇Γ = <:-/H≃-wf a₂<:a₁ ρ≃σ⇇Γ
    <:-/H≃-wf (<:-∙ x∈j _)      ρ≃σ⇇Γ = Var∈-/H≃-wf x∈j ρ≃σ⇇Γ
    <:-/H≃-wf (<:-⟨| a∈b⋯c)     ρ≃σ⇇Γ = Ne∈-/H≃-wf a∈b⋯c ρ≃σ⇇Γ
    <:-/H≃-wf (<:-|⟩ a∈b⋯c)     ρ≃σ⇇Γ = Ne∈-/H≃-wf a∈b⋯c ρ≃σ⇇Γ

  -- Parallel hereditary substitutions preserve kind equality.
  ≅-/H≃ : ∀ {k m n Γ Δ} {ρ σ : HSub k m n} {k₁ k₂} →
          Γ ⊢ k₁ ≅ k₂ → Δ ⊢/H ρ ≃ σ ⇇ Γ → Δ ⊢ k₁ Kind/H ρ ≅ k₂ Kind/H σ
  ≅-/H≃ (<∷-antisym j-kd k-kd j<∷k k<∷j) ρ≃σ⇇Γ =
    <∷-antisym (kd-/H j-kd (/H≃-valid₁ ρ≃σ⇇Γ))
               (kd-/H k-kd (/H≃-valid₂ ρ≃σ⇇Γ))
               (<∷-/H≃ j<∷k ρ≃σ⇇Γ) (<∷-/H≃ k<∷j (/H≃-sym ρ≃σ⇇Γ))
