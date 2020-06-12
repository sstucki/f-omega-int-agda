------------------------------------------------------------------------
-- Simple kinding of Fω with interval kinds
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FOmegaInt.Kinding.Simple where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.List as List using ([]; _∷_; _∷ʳ_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (∃; _,_; _×_)
open import Data.Unit using (tt)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProps
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; _≡_)
open import Relation.Nullary.Negation

open import FOmegaInt.Syntax
open import FOmegaInt.Syntax.SingleVariableSubstitution
open import FOmegaInt.Syntax.HereditarySubstitution
open import FOmegaInt.Syntax.Normalization


------------------------------------------------------------------------
-- Simple kinding derivations.
--
-- TODO: explain the point of this and how "simple" kinding differs
-- from "canonical" kinding.

module Kinding where
  open SimpleCtx
  open Syntax

  infix 4 _⊢Var_∈_ _⊢_kds _⊢Nf_∈_ _⊢Ne_∈_ _⊢_∋∙_∈_ _⊢_wfs

  -- Simple kinding of variables.
  data _⊢Var_∈_ {n} (Γ : Ctx n) : Fin n → SKind → Set where
    ∈-var : ∀ {k} x → lookup Γ x ≡ kd k → Γ ⊢Var x ∈ k

  mutual

    -- Simplified well-formedness of kinds: a variant of
    -- well-formedness for η-long β-normal kinds based on simple
    -- kinding.
    data _⊢_kds {n} (Γ : Ctx n) : Kind Elim n → Set where
      kds-⋯ : ∀ {a b} → Γ ⊢Nf a ∈ ★ → Γ ⊢Nf b ∈ ★           → Γ ⊢ a ⋯ b kds
      kds-Π : ∀ {j k} → Γ ⊢ j kds   → kd ⌊ j ⌋ ∷ Γ ⊢ k kds  → Γ ⊢ Π j k kds

    -- Simple kinding of η-long β-normal types.
    data _⊢Nf_∈_ {n} (Γ : Ctx n) : Elim n → SKind → Set where
      ∈-⊥-f : Γ ⊢Nf ⊥∙ ∈ ★
      ∈-⊤-f : Γ ⊢Nf ⊤∙ ∈ ★
      ∈-∀-f : ∀ {k a} → Γ ⊢ k kds → kd ⌊ k ⌋ ∷ Γ ⊢Nf a ∈ ★ →
              Γ ⊢Nf ∀∙ k a ∈ ★
      ∈-→-f : ∀ {a b} → Γ ⊢Nf a ∈ ★ → Γ ⊢Nf b ∈ ★ → Γ ⊢Nf a ⇒∙ b ∈ ★
      ∈-Π-i : ∀ {j a k} → Γ ⊢ j kds → kd ⌊ j ⌋ ∷ Γ ⊢Nf a ∈ k →
              Γ ⊢Nf Λ∙ j a ∈ ⌊ j ⌋ ⇒ k
      ∈-ne  : ∀ {a} → Γ ⊢Ne a ∈ ★ → Γ ⊢Nf a ∈ ★

    -- Simple kinding of neutral types.
    data _⊢Ne_∈_ {n} (Γ : Ctx n) : Elim n → SKind → Set where
      ∈-∙ : ∀ {x j k} {as : Spine n} → Γ ⊢Var x ∈ j →
            Γ ⊢ j ∋∙ as ∈ k → Γ ⊢Ne var x ∙ as ∈ k

    -- Simple spine kinding.
    data _⊢_∋∙_∈_ {n} (Γ : Ctx n) : SKind → Spine n → SKind → Set where
      ∈-[] : ∀ {k} → Γ ⊢ k ∋∙ [] ∈ k
      ∈-∷  : ∀ {a as j k l} → Γ ⊢Nf a ∈ j → Γ ⊢ k ∋∙ as ∈ l →
             Γ ⊢ j ⇒ k ∋∙ a ∷ as ∈ l

  open ContextConversions using (⌊_⌋Ctx)

  -- Simple well-formedness of ascriptions
  data _⊢_wfs {n} (Γ : Ctx n) : ElimAsc n → Set where
    wfs-kd : ∀ {a} → Γ ⊢ a kds   → Γ ⊢ kd a wfs
    wfs-tp : ∀ {a} → Γ ⊢Nf a ∈ ★ → Γ ⊢ tp a wfs

  -- Simply well-formed context extensions.
  module SimplyWfCtx = WellFormedContext (λ Γ a → ⌊ Γ ⌋Ctx ⊢ a wfs)
  open SimplyWfCtx public using () renaming (_wf to _ctxs; _⊢_wfExt to _⊢_exts)

open Syntax
open SimpleCtx
open Kinding
open PropEq

-- An admissible kinding rule for spine concatenation.
∈-++ : ∀ {n} {Γ : Ctx n} {as bs j k l} →
       Γ ⊢ j ∋∙ as ∈ k → Γ ⊢ k ∋∙ bs ∈ l →
       Γ ⊢ j ∋∙ as List.++ bs ∈ l
∈-++ ∈-[]               k∋as∈l = k∋as∈l
∈-++ (∈-∷ b∈j₁ j₂∋as∈k) k∋as∈l = ∈-∷ b∈j₁ (∈-++ j₂∋as∈k k∋as∈l)

-- An admissible kinding rule for appending a normal form to a spine.
∈-∷ʳ : ∀ {n} {Γ : Ctx n} {as a j k l} →
       Γ ⊢ j ∋∙ as ∈ k ⇒ l → Γ ⊢Nf a ∈ k →
       Γ ⊢ j ∋∙ as ∷ʳ a ∈ l
∈-∷ʳ j∋as∈k⇒k a∈k = ∈-++ j∋as∈k⇒k (∈-∷ a∈k ∈-[])

-- An admissible kinding rule for post-application to neutral types.
Ne∈-Π-e : ∀ {n} {Γ : Ctx n} {a b j k} →
          Γ ⊢Ne a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Γ ⊢Ne a ⌜·⌝ b ∈ k
Ne∈-Π-e (∈-∙ x∈j j∋as∈k) b∈k = ∈-∙ x∈j (∈-∷ʳ j∋as∈k b∈k)

-- An inversion lemma for _⊢_wf.
wfs-kd-inv : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ kd k wfs → Γ ⊢ k kds
wfs-kd-inv (wfs-kd k-kds) = k-kds

-- An inversion lemma for type operators.
Nf∈-⇒-inv : ∀ {n} {Γ : Ctx n} {a k₁ k₂} → Γ ⊢Nf a ∈ k₁ ⇒ k₂ →
            ∃ λ j → ∃ λ b →
              Γ ⊢ j kds × kd k₁ ∷ Γ ⊢Nf b ∈ k₂ × ⌊ j ⌋ ≡ k₁ × a ≡ Λ∙ j b
Nf∈-⇒-inv (∈-Π-i j-kds b∈k₂) = _ , _ , j-kds , b∈k₂ , refl , refl


----------------------------------------------------------------------
-- Well-kinded substitutions (i.e. substitution lemmas) in canonical
-- types

-- Well-kinded variable substitutions (renamings).
module KindedRenaming where

  open ⊤-WellFormed SimpleCtx.weakenOps

  typedVarSubst : TypedVarSubst (_⊢_wf)
  typedVarSubst = record
    { application = record { _/_ = λ k _ → k }
    ; weakenOps   = SimpleCtx.weakenOps
    ; /-wk        = refl
    ; id-vanishes = λ _ → refl
    ; /-⊙         = λ _ → refl
    ; wf-wf       = λ _ → ctx-wf _
    }

  open TypedVarSubst typedVarSubst public
    hiding (∈-weaken; ∈-var) renaming (_⊢Var_∈_ to _⊢Var′_∈_)
  open TypedSub typedSub using () renaming (lookup to ∈-lookup)

  open Substitution hiding (subst; _/Var_) renaming (_Elim/Var_ to _/Var_)
  open RenamingCommutes using (Kind[∈⌊⌋]-/Var)
  open PropEq
  open ≡-Reasoning

  -- A helper.
  ∈-↑′ : ∀ {m n} {Δ : Ctx n} {Γ : Ctx m} {k ρ} →
         Δ ⊢/Var ρ ∈ Γ →
         kd ⌊ k Kind′/Var ρ ⌋ ∷ Δ ⊢/Var ρ VarSubst.↑ ∈ kd ⌊ k ⌋ ∷ Γ
  ∈-↑′ {Δ = Δ} {_} {k} ρ∈Γ =
    subst (λ j → kd j ∷ Δ ⊢/Var _ ∈ _) (sym (⌊⌋-Kind′/Var k)) (∈-↑ tt ρ∈Γ)

  -- Convert between well-kindedness judgments for variables.
  Var∈′-Var∈ : ∀ {n} {Γ : Ctx n} {x a k} → a ≡ kd k →
               Γ ⊢Var′ x ∈ a → Γ ⊢Var x ∈ k
  Var∈′-Var∈ Γ[x]≡kd-k (var x Γ-ctx) = ∈-var x Γ[x]≡kd-k

  -- Renamings preserve synthesized kinds of variables.
  Var∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {x k ρ} →
              Γ ⊢Var x ∈ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Var Vec.lookup ρ x ∈ k
  Var∈-/Var (∈-var x Γ[x]≡kd-k) ρ∈Γ = Var∈′-Var∈ Γ[x]≡kd-k (∈-lookup ρ∈Γ x)

  mutual

    -- Renamings preserve well-formedness of kinds.
    kds-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k ρ} →
               Γ ⊢ k kds → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ k Kind′/Var ρ kds
    kds-/Var (kds-⋯ a∈★ b∈★) ρ∈Γ = kds-⋯ (Nf∈-/Var a∈★ ρ∈Γ) (Nf∈-/Var b∈★ ρ∈Γ)
    kds-/Var (kds-Π j-kds  k-kds) ρ∈Γ =
      kds-Π (kds-/Var j-kds ρ∈Γ) (kds-/Var k-kds (∈-↑′ ρ∈Γ))

    -- Renamings preserve synthesized kinds of normal types.
    Nf∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k ρ} →
               Γ ⊢Nf a ∈ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Nf a /Var ρ ∈ k
    Nf∈-/Var ∈-⊥-f              ρ∈Γ = ∈-⊥-f
    Nf∈-/Var ∈-⊤-f              ρ∈Γ = ∈-⊤-f
    Nf∈-/Var (∈-∀-f k-kds a∈★)  ρ∈Γ =
      ∈-∀-f (kds-/Var k-kds ρ∈Γ) (Nf∈-/Var a∈★ (∈-↑′ ρ∈Γ))
    Nf∈-/Var (∈-→-f a∈★ b∈★)    ρ∈Γ =
      ∈-→-f (Nf∈-/Var a∈★ ρ∈Γ) (Nf∈-/Var b∈★ ρ∈Γ)
    Nf∈-/Var (∈-Π-i {j} {a} {k} j-kds a∈k) ρ∈Γ =
      subst (λ l → _ ⊢Nf Λ∙ j a /Var _ ∈ l ⇒ k) (⌊⌋-Kind′/Var j)
            (∈-Π-i (kds-/Var j-kds ρ∈Γ) (Nf∈-/Var a∈k (∈-↑′ ρ∈Γ)))
    Nf∈-/Var (∈-ne a∈★)         ρ∈Γ = ∈-ne (Ne∈-/Var a∈★ ρ∈Γ)

    -- Renamings preserve synthesized kinds of neutral types.
    Ne∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k ρ} →
               Γ ⊢Ne a ∈ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢Ne a /Var ρ ∈ k
    Ne∈-/Var (∈-∙ x∈j k∈as∈l) ρ∈Γ =
      ∈-∙ (Var∈-/Var x∈j ρ∈Γ) (Sp∈-/Var k∈as∈l ρ∈Γ)

    Sp∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as j k ρ} →
               Γ ⊢ j ∋∙ as ∈ k → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ j ∋∙ as //Var ρ  ∈ k
    Sp∈-/Var ∈-[]                ρ∈Γ = ∈-[]
    Sp∈-/Var (∈-∷ a∈j k[a]∈as∈l) ρ∈Γ =
      ∈-∷ (Nf∈-/Var a∈j ρ∈Γ) (Sp∈-/Var k[a]∈as∈l ρ∈Γ)

  -- Renamings preserve well-formedness of ascriptions.
  wfs-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a ρ} →
             Γ ⊢ a wfs → Δ ⊢/Var ρ ∈ Γ → Δ ⊢ a ElimAsc/Var ρ wfs
  wfs-/Var (wfs-kd k-kds) ρ∈Γ = wfs-kd (kds-/Var k-kds ρ∈Γ)
  wfs-/Var (wfs-tp a∈★)   ρ∈Γ = wfs-tp (Nf∈-/Var a∈★ ρ∈Γ)

  -- Weakening preserves simple well-formedness of kinds.

  kds-weaken : ∀ {n} {Γ : Ctx n} {k a} →
               Γ ⊢ k kds → a ∷ Γ ⊢ weakenKind′ k kds
  kds-weaken k-kds = kds-/Var k-kds (∈-wk tt)

  kds-weaken⋆ : ∀ {m n} (Δ : CtxExt m n) {Γ : Ctx m} {k} →
                Γ ⊢ k kds → Δ ++ Γ ⊢ weakenKind′⋆ n k kds
  kds-weaken⋆ []       k-kds = k-kds
  kds-weaken⋆ (_ ∷ Δ′) k-kds = kds-weaken (kds-weaken⋆ Δ′ k-kds)

  -- Weakening preserves kinding of normal forms.

  Nf∈-weaken : ∀ {n} {Γ : Ctx n} {a b k} →
               Γ ⊢Nf b ∈ k → (a ∷ Γ) ⊢Nf weakenElim b ∈ k
  Nf∈-weaken b∈k = Nf∈-/Var b∈k (∈-wk tt)

  Nf∈-weaken⋆ : ∀ {m n} (Δ : CtxExt m n) {Γ : Ctx m} {a k} →
                Γ ⊢Nf a ∈ k → Δ ++ Γ ⊢Nf weakenElim⋆ n a ∈ k
  Nf∈-weaken⋆ []       a∈k = a∈k
  Nf∈-weaken⋆ (_ ∷ Δ′) a∈k = Nf∈-weaken (Nf∈-weaken⋆ Δ′ a∈k)

  -- Weakening preserves kinding of neutral forms.
  Ne∈-weaken : ∀ {n} {Γ : Ctx n} {a b k} →
               Γ ⊢Ne b ∈ k → (a ∷ Γ) ⊢Ne weakenElim b ∈ k
  Ne∈-weaken b∈k = Ne∈-/Var b∈k (∈-wk tt)

  -- Weakening preserves spine kinding.
  Sp∈-weaken : ∀ {n} {Γ : Ctx n} {a bs j k} →
               Γ ⊢ j ∋∙ bs ∈ k → (a ∷ Γ) ⊢ j ∋∙ weakenSpine bs ∈ k
  Sp∈-weaken j∋bs∈k = Sp∈-/Var j∋bs∈k (∈-wk tt)

  -- Weakening preserves simple well-formedness of ascriptions.
  wfs-weaken : ∀ {n} {Γ : Ctx n} {a b} →
               Γ ⊢ b wfs → a ∷ Γ ⊢ weakenElimAsc b wfs
  wfs-weaken b-wfs = wfs-/Var b-wfs (∈-wk tt)

-- Operations on simply well-formed contexts that require weakening of
-- well-formedness judgments.
module WfsCtxOps where
  open SimplyWfCtx
  open ContextConversions using (⌊_⌋Ctx)
  open KindedRenaming using (wfs-weaken)

  wfsWeakenOps : WfWeakenOps ElimCtx.weakenOps
  wfsWeakenOps = record { wf-weaken = λ _ → wfs-weaken }

  private module W = WfWeakenOps wfsWeakenOps
  open W public hiding (wf-weaken)

  -- Lookup the kind of a type variable in a well-formed context.
  lookup-kd : ∀ {m} {Γ : ElimCtx.Ctx m} {a} x →
              Γ ctxs → ElimCtx.lookup Γ x ≡ kd a → ⌊ Γ ⌋Ctx ⊢ a kds
  lookup-kd x Γ-ctxs Γ[x]≡kd-a =
    wfs-kd-inv (subst (_ ⊢_wfs) Γ[x]≡kd-a (W.lookup Γ-ctxs x))

module KindedHereditarySubstitution where
  open Data.Fin         using (zero; raise; lift)
  open Substitution     hiding (subst; sub; _↑; _↑⋆_)
  open KindedRenaming   using (_⊢/Var_∈_; Nf∈-/Var; Nf∈-weaken⋆; ∈-wk; ∈-↑⋆)
  open RenamingCommutes using (wk-/⟨⟩-↑⋆; /Var-wk-↑⋆-hsub-vanishes)
  open PropEq
  open ≡-Reasoning
  private module V = VarSubst

  infix 4 _⊢/⟨_⟩_∈_ _⊢?⟨_⟩_∈_

  -- Simply well-kinded hereditary substitions and lookup results.

  data _⊢/⟨_⟩_∈_ : ∀ {m n} → Ctx n → SKind → SVSub m n → Ctx m → Set where
    ∈-hsub : ∀ {n} {Γ : Ctx n} {k a} →
             Γ ⊢Nf a ∈ k → Γ ⊢/⟨ k ⟩ sub a ∈ kd k ∷ Γ
    ∈-H↑   : ∀ {m n Δ k Γ} {σ : SVSub m n} {a} →
             Δ ⊢/⟨ k ⟩ σ ∈ Γ → a ∷ Δ ⊢/⟨ k ⟩ σ ↑ ∈ a ∷ Γ

  data _⊢?⟨_⟩_∈_ {n} (Γ : Ctx n) (k : SKind) : SVRes n → SAsc n → Set where
    ∈-hit  : ∀ {a}   → Γ ⊢Nf a ∈ k    → Γ ⊢?⟨ k ⟩ hit a ∈ kd k
    ∈-miss : ∀ y {a} → lookup Γ y ≡ a → Γ ⊢?⟨ k ⟩ miss y ∈ a

  -- A variant of `∈-H↑' that applies `σ' in the target context

  ∈-H↑′ : ∀ {m n Δ k Γ} {σ : SVSub m n} {j} →
          Δ ⊢/⟨ k ⟩ σ ∈ Γ →
          kd ⌊ j Kind/⟨ k ⟩ σ ⌋ ∷ Δ ⊢/⟨ k ⟩ σ ↑ ∈ kd ⌊ j ⌋ ∷ Γ
  ∈-H↑′ σ∈Γ =
    subst (λ k → kd k ∷ _ ⊢/⟨ _ ⟩ _ ↑ ∈ kd _ ∷ _)
          (sym (⌊⌋-Kind/⟨⟩ _)) (∈-H↑ σ∈Γ)

  -- Lift a kinded hereditary substitution over multiple additional
  -- variables.

  ∈-H↑⋆ : ∀ {m n i} (E : CtxExt m i) {Δ k Γ} {σ : SVSub m n} →
          Δ ⊢/⟨ k ⟩ σ ∈ Γ → re-idx E ++ Δ ⊢/⟨ k ⟩ σ ↑⋆ i ∈ E ++ Γ
  ∈-H↑⋆ []      σ∈Γ = σ∈Γ
  ∈-H↑⋆ (a ∷ E) σ∈Γ = ∈-H↑ (∈-H↑⋆ E σ∈Γ)

  -- Renamings preserve well-kinded SV results.

  ?∈-/Var : ∀ {m n Γ k Δ r a} {ρ : Sub Fin m n} →
            Γ ⊢?⟨ k ⟩ r ∈ a → Δ ⊢/Var ρ ∈ Γ → Δ ⊢?⟨ k ⟩ r ?/Var ρ ∈ a
  ?∈-/Var                 (∈-hit a∈k)     ρ∈Γ = ∈-hit (Nf∈-/Var a∈k ρ∈Γ)
  ?∈-/Var {Γ = Γ} {k} {Δ} (∈-miss y refl) ρ∈Γ = helper refl (TS.lookup ρ∈Γ y)
    where
      module TS = TypedSub KindedRenaming.typedSub
      module TV = TypedVarSubst KindedRenaming.typedVarSubst

      helper : ∀ {x a} → a ≡ lookup Γ y → Δ TV.⊢Var x ∈ a →
               Δ ⊢?⟨ k ⟩ miss x ∈ lookup Γ y
      helper Δ[x]≡Γ[y] (TV.var x _) = ∈-miss x Δ[x]≡Γ[y]

  ?∈-weaken : ∀ {n} {Γ : Ctx n} {k r a b} →
              Γ ⊢?⟨ k ⟩ r ∈ a → (b ∷ Γ) ⊢?⟨ k ⟩ weakenSVRes r ∈ a
  ?∈-weaken r∈a = ?∈-/Var r∈a (KindedRenaming.∈-wk tt)

  -- Look up a variable in a well-kinded hereditary substitution.

  lookup-/⟨⟩∈ : ∀ {m n Δ k Γ} {σ : SVSub m n} →
                Δ ⊢/⟨ k ⟩ σ ∈ Γ → (x : Fin m) →
                Δ ⊢?⟨ k ⟩ lookupSV σ x ∈ lookup Γ x
  lookup-/⟨⟩∈                (∈-hsub a∈k) zero    = ∈-hit a∈k
  lookup-/⟨⟩∈ {Γ = kd k ∷ Γ} (∈-hsub a∈k) (suc x) =
    ∈-miss x (cong (λ Γ → Vec.lookup Γ x) (sym (VecProps.map-id (toVec Γ))))
  lookup-/⟨⟩∈ (∈-H↑                     σ∈Γ) zero    = ∈-miss zero refl
  lookup-/⟨⟩∈ (∈-H↑ {Δ = Δ} {_} {Γ} {σ} σ∈Γ) (suc x) =
    ?∈-weaken (subst (λ as → Δ ⊢?⟨ _ ⟩ lookupSV σ x ∈ Vec.lookup as x)
                     (sym (VecProps.map-id (toVec Γ))) (lookup-/⟨⟩∈ σ∈Γ x))

  -- Lookup a hit in a well-kinded hereditary substitution.
  --
  -- NOTE. Since `j ≡ k', we could have formulated this lemma
  -- differently.  In particular, given the premise `Γ ⊢Var x ∈ j', it
  -- would have been more intuitive for the kinding judgment in the
  -- conclusion to use the simple kind `j' rather than `k' (preserving
  -- the kind of the variable, as usual for substitution lemmas).
  -- However, it is important that the simple kind `k' of the normal
  -- type returned by this function is syntactically equal to the kind
  -- annotation of the hereditary substitution `Δ ⊢/⟨ k ⟩ σ ∈ Γ'
  -- because it serves as the termination measure for the (hereditary)
  -- substitution lemmas below.

  lookup-/⟨⟩∈-Hit : ∀ {m n Δ k} {σ : SVSub m n} {Γ x j a} →
                    Δ ⊢/⟨ k ⟩ σ ∈ Γ → Γ ⊢Var x ∈ j → Hit σ x a →
                    Δ ⊢Nf a ∈ k × j ≡ k
  lookup-/⟨⟩∈-Hit σ∈Γ (∈-var {j} x Γ[x]≡kd-j) hitP =
    let a∈k , Γ[x]≡kd-k = helper (lookup-Hit hitP) (lookup-/⟨⟩∈ σ∈Γ x)
    in  a∈k , kd-inj′ (trans (sym Γ[x]≡kd-j) Γ[x]≡kd-k)
    where
      helper : ∀ {n} {Δ : Ctx n} {r a b k} →
               r ≡ hit a → Δ ⊢?⟨ k ⟩ r ∈ b → Δ ⊢Nf a ∈ k × b ≡ kd k
      helper refl (∈-hit a∈k) = a∈k , refl

  lookup-/⟨⟩∈-Miss : ∀ {m n Δ k} {σ : SVSub m n} {Γ x y j} →
                     Δ ⊢/⟨ k ⟩ σ ∈ Γ → Γ ⊢Var x ∈ j → Miss σ x y →
                     lookup Δ y ≡ lookup Γ x
  lookup-/⟨⟩∈-Miss σ∈Γ (∈-var {j} x Γ[x]≡kd-j) missP =
    helper (lookup-Miss missP) (lookup-/⟨⟩∈ σ∈Γ x)
    where
      helper : ∀ {n} {Δ : Ctx n} {r y b k} →
               r ≡ miss y → Δ ⊢?⟨ k ⟩ r ∈ b → lookup Δ y ≡ b
      helper refl (∈-miss y Δ[y]≡b) = Δ[y]≡b

  open KindSimpLemmas simpLemmasKind′

  -- TODO: explain why this terminates.
  mutual

    -- Hereditary substitutions preserve simple well-formedness and
    -- kinding (of kinds, normal types and spines).

    kds-/⟨⟩ : ∀ {m n Γ k Δ} {σ : SVSub m n} {j} →
              Γ ⊢ j kds → Δ ⊢/⟨ k ⟩ σ ∈ Γ → Δ ⊢ j Kind/⟨ k ⟩ σ kds
    kds-/⟨⟩ (kds-⋯ a∈★ b∈★)     σ∈Γ = kds-⋯ (Nf∈-/⟨⟩ a∈★ σ∈Γ) (Nf∈-/⟨⟩ b∈★ σ∈Γ)
    kds-/⟨⟩ (kds-Π j-kds k-kds) σ∈Γ =
      kds-Π (kds-/⟨⟩ j-kds σ∈Γ) (kds-/⟨⟩ k-kds (∈-H↑′ σ∈Γ))

    Nf∈-/⟨⟩ : ∀ {m n Γ k Δ} {σ : SVSub m n} {a j} →
              Γ ⊢Nf a ∈ j → Δ ⊢/⟨ k ⟩ σ ∈ Γ → Δ ⊢Nf a /⟨ k ⟩ σ ∈ j
    Nf∈-/⟨⟩ ∈-⊥-f             σ∈Γ = ∈-⊥-f
    Nf∈-/⟨⟩ ∈-⊤-f             σ∈Γ = ∈-⊤-f
    Nf∈-/⟨⟩ (∈-∀-f k-kds a∈★) σ∈Γ =
      ∈-∀-f (kds-/⟨⟩ k-kds σ∈Γ) (Nf∈-/⟨⟩ a∈★ (∈-H↑′ σ∈Γ))
    Nf∈-/⟨⟩ (∈-→-f a∈★ b∈★)   σ∈Γ =
      ∈-→-f (Nf∈-/⟨⟩ a∈★ σ∈Γ) (Nf∈-/⟨⟩ b∈★ σ∈Γ)
    Nf∈-/⟨⟩ (∈-Π-i {j} {a} {k} j-kds a∈k) σ∈Γ =
      subst (λ l → _ ⊢Nf Λ∙ j a /⟨ _ ⟩ _ ∈ l ⇒ k) (⌊⌋-Kind/⟨⟩ j)
            (∈-Π-i (kds-/⟨⟩ j-kds σ∈Γ) (Nf∈-/⟨⟩ a∈k (∈-H↑′ σ∈Γ)))
    Nf∈-/⟨⟩ (∈-ne a∈★)        σ∈Γ = Ne∈-/⟨⟩ a∈★ σ∈Γ

    Sp∈-/⟨⟩ : ∀ {m n Γ k Δ} {σ : SVSub m n} {as j₁ j₂} →
              Γ ⊢ j₁ ∋∙ as ∈ j₂ → Δ ⊢/⟨ k ⟩ σ ∈ Γ → Δ ⊢ j₁ ∋∙ as //⟨ k ⟩ σ ∈ j₂
    Sp∈-/⟨⟩ ∈-[]                   σ∈Γ = ∈-[]
    Sp∈-/⟨⟩ (∈-∷ a∈j₁ j₂[a]∈as∈j₃) σ∈Γ =
      ∈-∷ (Nf∈-/⟨⟩ a∈j₁ σ∈Γ) (Sp∈-/⟨⟩ j₂[a]∈as∈j₃ σ∈Γ)

    -- Hereditary substitutions preserve simple kinds of neutral
    -- types (but not neutrality itself).
    Ne∈-/⟨⟩ : ∀ {m n Γ k Δ} {σ : SVSub m n} {a} →
              Γ ⊢Ne a ∈ ★ → Δ ⊢/⟨ k ⟩ σ ∈ Γ → Δ ⊢Nf a /⟨ k ⟩ σ ∈ ★
    Ne∈-/⟨⟩ (∈-∙ (∈-var x Γ[x]≡kd-j) j∈as∈l) σ∈Γ =
      ?⟨⟩∈-?∙∙ (subst (_ ⊢?⟨ _ ⟩ _ ∈_) Γ[x]≡kd-j (lookup-/⟨⟩∈ σ∈Γ x))
               (Sp∈-/⟨⟩ j∈as∈l σ∈Γ)

    -- Applications in simple kinding are admissible.

    ?⟨⟩∈-?∙∙ : ∀ {n} {Γ : Ctx n} {r as k j} →
               Γ ⊢?⟨ k ⟩ r ∈ kd j → Γ ⊢ j ∋∙ as ∈ ★ → Γ ⊢Nf r ?∙∙⟨ k ⟩ as ∈ ★
    ?⟨⟩∈-?∙∙ (∈-hit a∈j)          j∋as∈★ = Nf∈-∙∙ a∈j j∋as∈★
    ?⟨⟩∈-?∙∙ (∈-miss y Γ[y]≡kd-j) j∋as∈★ = ∈-ne (∈-∙ (∈-var y Γ[y]≡kd-j) j∋as∈★)

    Nf∈-∙∙ : ∀ {n} {Γ : Ctx n} {a as j k} →
             Γ ⊢Nf a ∈ j → Γ ⊢ j ∋∙ as ∈ k → Γ ⊢Nf a ∙∙⟨ j ⟩ as ∈ k
    Nf∈-∙∙ a∈j   ∈-[]             = a∈j
    Nf∈-∙∙ a∈j⇒k (∈-∷ b∈j k∋as∈l) = Nf∈-∙∙ (Nf∈-Π-e a∈j⇒k b∈j) k∋as∈l

    Nf∈-Π-e : ∀ {n} {Γ : Ctx n} {a b j k} →
              Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Γ ⊢Nf a ⌜·⌝⟨ j ⇒ k ⟩ b ∈ k
    Nf∈-Π-e (∈-Π-i j-kds a∈k) b∈⌊j⌋ = Nf∈-/⟨⟩ a∈k (∈-hsub b∈⌊j⌋)

  -- Concatenation of simply well-formed spines results in application.
  Nf∈-++-∙∙⟨⟩ : ∀ {n} {Γ : Ctx n} {a bs cs j k l} →
                Γ ⊢Nf a ∈ j → Γ ⊢ j ∋∙ bs ∈ k → Γ ⊢ k ∋∙ cs ∈ l →
                a ∙∙⟨ j ⟩ (bs List.++ cs) ≡ a ∙∙⟨ j ⟩ bs ∙∙⟨ k ⟩ cs
  Nf∈-++-∙∙⟨⟩ a∈j     ∈-[]                  k∋cs∈l = refl
  Nf∈-++-∙∙⟨⟩ a∈j₁⇒j₂ (∈-∷ b∈j₁ j₂[b]∋bs∈k) k∋cs∈l =
    Nf∈-++-∙∙⟨⟩ (Nf∈-Π-e a∈j₁⇒j₂ b∈j₁) j₂[b]∋bs∈k k∋cs∈l

  -- Another admissible kinding rule for applications.
  Nf∈-Π-e′ : ∀ {n} {Γ : Ctx n} {a b j k} →
             Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Γ ⊢Nf a ↓⌜·⌝ b ∈ k
  Nf∈-Π-e′ (∈-Π-i j-kds a∈k) b∈⌊j⌋ = Nf∈-/⟨⟩ a∈k (∈-hsub b∈⌊j⌋)

  mutual

    -- Simply well-kinded hereditary substitutions in simply
    -- well-formed kinds and simply well-kinded types commute.
    --
    -- NOTE: this is a variant of the `sub-commutes' lemma from
    -- Data.Fin.Substitution.Lemmas adapted to hereditary
    -- substitutions.

    kds-[]-/⟨⟩-↑⋆ : ∀ {i m n} (E : CtxExt (suc m) i) {Γ Δ}
                    {j b k l} {σ : SVSub m n} →
                    E ++ kd k ∷ Γ ⊢ j kds → Γ ⊢Nf b ∈ k → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                    j Kind/⟨ k ⟩ (sub b ↑⋆ i) Kind/⟨ l ⟩ σ ↑⋆ i ≡
                      j Kind/⟨ l ⟩ (σ ↑) ↑⋆ i Kind/⟨ k ⟩ sub (b /⟨ l ⟩ σ) ↑⋆ i
    kds-[]-/⟨⟩-↑⋆ E (kds-⋯ a∈★ b∈★)     c∈k σ∈Γ =
      cong₂ _⋯_ (Nf∈-[]-/⟨⟩-↑⋆ E a∈★ c∈k σ∈Γ) (Nf∈-[]-/⟨⟩-↑⋆ E b∈★ c∈k σ∈Γ)
    kds-[]-/⟨⟩-↑⋆ E (kds-Π j-kds k-kds) b∈k σ∈Γ =
      cong₂ Π (kds-[]-/⟨⟩-↑⋆ E j-kds b∈k σ∈Γ)
              (kds-[]-/⟨⟩-↑⋆ (_ ∷ E) k-kds b∈k σ∈Γ)

    Nf∈-[]-/⟨⟩-↑⋆ : ∀ {i m n} (E : CtxExt (suc m) i) {Γ Δ}
                    {a b j k l} {σ : SVSub m n} →
                    E ++ kd k ∷ Γ ⊢Nf a ∈ j → Γ ⊢Nf b ∈ k → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                    a /⟨ k ⟩ (sub b ↑⋆ i) /⟨ l ⟩ σ ↑⋆ i ≡
                      a /⟨ l ⟩ (σ ↑) ↑⋆ i /⟨ k ⟩ sub (b /⟨ l ⟩ σ) ↑⋆ i
    Nf∈-[]-/⟨⟩-↑⋆ E ∈-⊥-f b∈k σ∈Γ = refl
    Nf∈-[]-/⟨⟩-↑⋆ E ∈-⊤-f b∈k σ∈Γ = refl
    Nf∈-[]-/⟨⟩-↑⋆ E (∈-∀-f k-kds a∈★) b∈k σ∈Γ =
      cong (_∙ []) (cong₂ Π (kds-[]-/⟨⟩-↑⋆ E k-kds b∈k σ∈Γ)
                            (Nf∈-[]-/⟨⟩-↑⋆ (_ ∷ E) a∈★ b∈k σ∈Γ))
    Nf∈-[]-/⟨⟩-↑⋆ E (∈-→-f a∈★ b∈★)   c∈k σ∈Γ =
      cong (_∙ []) (cong₂ _⇒_ (Nf∈-[]-/⟨⟩-↑⋆ E a∈★ c∈k σ∈Γ)
                              (Nf∈-[]-/⟨⟩-↑⋆ E b∈★ c∈k σ∈Γ))
    Nf∈-[]-/⟨⟩-↑⋆ E (∈-Π-i j-kds a∈l) b∈k σ∈Γ =
      cong (_∙ []) (cong₂ Λ (kds-[]-/⟨⟩-↑⋆ E j-kds b∈k σ∈Γ)
                            (Nf∈-[]-/⟨⟩-↑⋆ (_ ∷ E) a∈l b∈k σ∈Γ))
    Nf∈-[]-/⟨⟩-↑⋆ E (∈-ne a∈★)        b∈k σ∈Γ = Ne∈-[]-/⟨⟩-↑⋆ E a∈★ b∈k σ∈Γ

    Ne∈-[]-/⟨⟩-↑⋆ : ∀ {i m n} (E : CtxExt (suc m) i) {Γ Δ}
                    {a b j k l} {σ : SVSub m n} →
                    E ++ kd k ∷ Γ ⊢Ne a ∈ j → Γ ⊢Nf b ∈ k → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                    a /⟨ k ⟩ (sub b ↑⋆ i) /⟨ l ⟩ σ ↑⋆ i ≡
                      a /⟨ l ⟩ (σ ↑) ↑⋆ i /⟨ k ⟩ sub (b /⟨ l ⟩ σ) ↑⋆ i
    Ne∈-[]-/⟨⟩-↑⋆ {i} E {b = b} (∈-∙ (∈-var x _) j∋as∈l) b∈k σ∈Γ
      with hit? (sub b ↑⋆ i) x
    Ne∈-[]-/⟨⟩-↑⋆ {i} E {_} {_} {var x ∙ as} {b} {_} {k} {l} {σ}
                  (∈-∙ (∈-var x Γ[x]=kd-j) j∋as∈l) b∈k σ∈Γ
      | hit a hitP =
      let σ₁′ = sub b ↑⋆ i
          σ₂′ = sub (b /⟨ l ⟩ σ) ↑⋆ i
          as₁ = as //⟨ k ⟩ σ₁′
          as₂ = as //⟨ l ⟩ ((σ ↑) ↑⋆ i)
          [b/i]∈E++k∷Γ = ∈-H↑⋆ E (∈-hsub b∈k)
          _ , j≡k   = lookup-/⟨⟩∈-Hit [b/i]∈E++k∷Γ (∈-var x Γ[x]=kd-j) hitP
          k∋as∈l    = subst (_ ⊢_∋∙ as ∈ _) j≡k j∋as∈l
          σ↑⋆i∈E++Γ = ∈-H↑⋆ (re-idx E) σ∈Γ
      in begin
        lookupSV σ₁′ x ?∙∙⟨ k ⟩ as₁ /⟨ l ⟩ σ ↑⋆ i
      ≡⟨ cong (λ r → r ?∙∙⟨ k ⟩ as₁ /⟨ l ⟩ _)
              (trans (lookup-Hit hitP) (cong hit (Hit-sub-↑⋆₂ i hitP))) ⟩
        weakenElim⋆ i b ∙∙⟨ k ⟩ as₁ /⟨ l ⟩ σ ↑⋆ i
      ≡⟨ Nf∈-∙∙-/⟨⟩ (Nf∈-weaken⋆ (re-idx E) b∈k)
                    (Sp∈-/⟨⟩ k∋as∈l [b/i]∈E++k∷Γ) σ↑⋆i∈E++Γ ⟩
        (weakenElim⋆ i b /⟨ l ⟩ σ ↑⋆ i) ∙∙⟨ k ⟩ (as₁ //⟨ l ⟩ σ ↑⋆ i)
      ≡⟨ cong₂ (_∙∙⟨ k ⟩_) (sym (weaken⋆-/⟨⟩-↑⋆ i b))
               (Sp∈-[]-/⟨⟩-↑⋆ E j∋as∈l b∈k σ∈Γ) ⟩
        weakenElim⋆ i (b /⟨ l ⟩ σ) ∙∙⟨ k ⟩ (as₂ //⟨ k ⟩ σ₂′)
      ≡˘⟨ cong (_?∙∙⟨ k ⟩ (as₂ //⟨ k ⟩ σ₂′)) (lookup-Hit (Hit-sub-↑⋆ i)) ⟩
        lookupSV σ₂′ (raise i zero) ?∙∙⟨ k ⟩ (as₂ //⟨ k ⟩ σ₂′)
      ≡⟨⟩
        miss (raise i zero) ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ≡˘⟨ cong (λ r → r ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′)
               (lookup-Miss (Miss-↑⋆ i under)) ⟩
        lookupSV ((σ ↑) ↑⋆ i) (raise i zero) ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ≡˘⟨ cong (λ y → lookupSV ((σ ↑) ↑⋆ i) y ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′)
               (Hit-sub-↑⋆₁ i hitP) ⟩
        lookupSV ((σ ↑) ↑⋆ i) x ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ∎
    Ne∈-[]-/⟨⟩-↑⋆ {i} E {_} {_} {var x ∙ as} {b} {_} {k} {l} {σ}
                  (∈-∙ (∈-var x Γ[x]=kd-j) j∋as∈l) b∈k σ∈Γ
      | miss y missP-[a/i] with hit? (σ ↑⋆ i) y
    ... | hit a hitP =
      let σ₁′ = sub b ↑⋆ i
          σ₂′ = sub (b /⟨ l ⟩ σ) ↑⋆ i
          as₁ = as //⟨ k ⟩ σ₁′
          as₂ = as //⟨ l ⟩ ((σ ↑) ↑⋆ i)
          hitP-σ↑↑⋆ = Hit-↑-↑⋆ i hitP
          σ₂′∈E++Γ  = ∈-H↑⋆ (re-idx E) (∈-hsub (Nf∈-/⟨⟩ b∈k σ∈Γ))
          σ∈E++k∷Γ  = ∈-H↑⋆ E (∈-H↑ σ∈Γ)
          x≡i+1+y   = Miss-sub-↑⋆′ i y missP-[a/i]
          i+1+y∈j   = subst (_ ⊢Var_∈ _) x≡i+1+y (∈-var x Γ[x]=kd-j)
          a∈l , j≡l = lookup-/⟨⟩∈-Hit σ∈E++k∷Γ i+1+y∈j hitP-σ↑↑⋆
          l∋as₂∈l   = subst (_ ⊢_∋∙ as₂ ∈ _) j≡l (Sp∈-/⟨⟩ j∋as∈l σ∈E++k∷Γ)
      in begin
        lookupSV σ₁′ x ?∙∙⟨ k ⟩ as₁ /⟨ l ⟩ σ ↑⋆ i
      ≡⟨ cong (λ r → r ?∙∙⟨ k ⟩ as₁ /⟨ l ⟩ σ ↑⋆ i) (lookup-Miss missP-[a/i]) ⟩
        var y ∙ as₁ /⟨ l ⟩ σ ↑⋆ i
      ≡⟨⟩
        lookupSV (σ ↑⋆ i) y ?∙∙⟨ l ⟩ (as₁ //⟨ l ⟩ σ ↑⋆ i)
      ≡⟨ cong₂ (_?∙∙⟨ l ⟩_) (lookup-Hit hitP) (Sp∈-[]-/⟨⟩-↑⋆ E j∋as∈l b∈k σ∈Γ) ⟩
        a ∙∙⟨ l ⟩ (as₂ //⟨ k ⟩ σ₂′)
      ≡˘⟨ cong (_∙∙⟨ l ⟩ (as₂ //⟨ k ⟩ σ₂′)) (/Var-wk-↑⋆-hsub-vanishes i a) ⟩
        (a Elim/Var V.wk V.↑⋆ i /⟨ k ⟩ σ₂′) ∙∙⟨ l ⟩ (as₂ //⟨ k ⟩ σ₂′)
      ≡˘⟨ Nf∈-∙∙-/⟨⟩ a∈l l∋as₂∈l σ₂′∈E++Γ ⟩
        (a Elim/Var V.wk V.↑⋆ i) ∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ≡˘⟨ cong (λ r → r ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′) (lookup-Hit hitP-σ↑↑⋆) ⟩
        lookupSV ((σ ↑) ↑⋆ i) (lift i suc y) ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ≡˘⟨ cong (λ z → lookupSV ((σ ↑) ↑⋆ i) z ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′) x≡i+1+y ⟩
        lookupSV ((σ ↑) ↑⋆ i) x ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ∎
    ... | miss z missP =
      let σ₁′ = sub b ↑⋆ i
          σ₂′ = sub (b /⟨ l ⟩ σ) ↑⋆ i
          as₁ = as //⟨ k ⟩ σ₁′
          as₂ = as //⟨ l ⟩ ((σ ↑) ↑⋆ i)
          missP-σ↑↑⋆ = Miss-↑-↑⋆ i missP
          x≡i+1+y    = Miss-sub-↑⋆′ i y missP-[a/i]
      in begin
        lookupSV σ₁′ x ?∙∙⟨ k ⟩ as₁ /⟨ l ⟩ σ ↑⋆ i
      ≡⟨ cong (λ r → r ?∙∙⟨ k ⟩ as₁ /⟨ l ⟩ σ ↑⋆ i) (lookup-Miss missP-[a/i]) ⟩
        var y ∙ as₁ /⟨ l ⟩ σ ↑⋆ i
      ≡⟨⟩
        lookupSV (σ ↑⋆ i) y ?∙∙⟨ l ⟩ (as₁ //⟨ l ⟩ σ ↑⋆ i)
      ≡⟨ cong₂ (_?∙∙⟨ l ⟩_) (lookup-Miss missP)
               (Sp∈-[]-/⟨⟩-↑⋆ E j∋as∈l b∈k σ∈Γ) ⟩
        var z ∙ (as₂ //⟨ k ⟩ σ₂′)
      ≡˘⟨ cong (_?∙∙⟨ k ⟩ (as₂ //⟨ k ⟩ σ₂′)) (lookup-Miss (Miss-sub-↑⋆ i z)) ⟩
        lookupSV σ₂′ (lift i suc z) ?∙∙⟨ k ⟩ (as₂ //⟨ k ⟩ σ₂′)
      ≡⟨⟩
        var (lift i suc z) ∙ as₂ /⟨ k ⟩ σ₂′
      ≡˘⟨ cong (λ r → r ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′) (lookup-Miss missP-σ↑↑⋆) ⟩
        lookupSV ((σ ↑) ↑⋆ i) (lift i suc y) ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ≡˘⟨ cong (λ z → lookupSV ((σ ↑) ↑⋆ i) z ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′) x≡i+1+y ⟩
        lookupSV ((σ ↑) ↑⋆ i) x ?∙∙⟨ l ⟩ as₂ /⟨ k ⟩ σ₂′
      ∎

    Sp∈-[]-/⟨⟩-↑⋆ : ∀ {i m n} (E : CtxExt (suc m) i) {Γ Δ}
                    {as b j₁ j₂ k l} {σ : SVSub m n} →
                    E ++ kd k ∷ Γ ⊢ j₁ ∋∙ as ∈ j₂ →
                    Γ ⊢Nf b ∈ k → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                    as //⟨ k ⟩ (sub b ↑⋆ i) //⟨ l ⟩ σ ↑⋆ i ≡
                      as //⟨ l ⟩ (σ ↑) ↑⋆ i //⟨ k ⟩ sub (b /⟨ l ⟩ σ) ↑⋆ i
    Sp∈-[]-/⟨⟩-↑⋆ E ∈-[]                b∈k σ∈Γ = refl
    Sp∈-[]-/⟨⟩-↑⋆ E (∈-∷ a∈j₁ j₂∋as∈j₃) b∈k σ∈Γ =
      cong₂ _∷_ (Nf∈-[]-/⟨⟩-↑⋆ E a∈j₁ b∈k σ∈Γ) (Sp∈-[]-/⟨⟩-↑⋆ E j₂∋as∈j₃ b∈k σ∈Γ)

    -- Reducing applications commute with hereditary substitution.

    Nf∈-∙∙-/⟨⟩ : ∀ {l m n Γ Δ} {σ : SVSub m n} {a as j k} →
                 Γ ⊢Nf a ∈ j → Γ ⊢ j ∋∙ as ∈ k → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                 a ∙∙⟨ j ⟩ as /⟨ l ⟩ σ ≡ (a /⟨ l ⟩ σ) ∙∙⟨ j ⟩ (as //⟨ l ⟩ σ)
    Nf∈-∙∙-/⟨⟩ a∈j ∈-[] σ∈Γ = refl
    Nf∈-∙∙-/⟨⟩ {l} {σ = σ} {a} {b ∷ bs} {j ⇒ k} a∈j⇒k (∈-∷ b∈j k∋bs∈l) σ∈Γ =
      begin
        a ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs /⟨ l ⟩ σ
      ≡⟨ Nf∈-∙∙-/⟨⟩ (Nf∈-Π-e a∈j⇒k b∈j) k∋bs∈l σ∈Γ ⟩
        (a ⌜·⌝⟨ j ⇒ k ⟩ b /⟨ l ⟩ σ) ∙∙⟨ _ ⟩ (bs //⟨ l ⟩ σ)
      ≡⟨ cong (_∙∙⟨ k ⟩ (bs //⟨ l ⟩ σ)) (Nf∈-Π-e-/⟨⟩ a∈j⇒k b∈j σ∈Γ) ⟩
        (a /⟨ l ⟩ σ) ⌜·⌝⟨ j ⇒ k ⟩ (b /⟨ l ⟩ σ) ∙∙⟨ k ⟩ (bs //⟨ l ⟩ σ)
      ∎

    Nf∈-Π-e-/⟨⟩ : ∀ {l m n Γ Δ} {σ : SVSub m n} {a b j k} →
                  Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                  a ⌜·⌝⟨ j ⇒ k ⟩ b /⟨ l ⟩ σ ≡
                    (a /⟨ l ⟩ σ) ⌜·⌝⟨ j ⇒ k ⟩ (b /⟨ l ⟩ σ)
    Nf∈-Π-e-/⟨⟩ (∈-Π-i j-kds a∈k) b∈⌊j⌋ σ∈Γ = Nf∈-[]-/⟨⟩-↑⋆ [] a∈k b∈⌊j⌋ σ∈Γ

  -- Potentially reducing applications commute with hereditary
  -- substitution.

  Nf∈-Π-e-/⟨⟩′ : ∀ {l m n Γ Δ} {σ : SVSub m n} {a b j k} →
                Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Δ ⊢/⟨ l ⟩ σ ∈ Γ →
                a ↓⌜·⌝ b /⟨ l ⟩ σ ≡ (a /⟨ l ⟩ σ) ↓⌜·⌝ (b /⟨ l ⟩ σ)
  Nf∈-Π-e-/⟨⟩′ {l} {σ = σ} {_} {b} (∈-Π-i {j} {a} j-kds a∈k) b∈⌊j⌋ σ∈Γ =
    begin
      (a [ b ∈ ⌊ j ⌋ ]) /⟨ l ⟩ σ
    ≡⟨ Nf∈-[]-/⟨⟩-↑⋆ [] a∈k b∈⌊j⌋ σ∈Γ ⟩
      (a /⟨ l ⟩ σ ↑) [ b /⟨ l ⟩ σ ∈ ⌊ j ⌋ ]
    ≡⟨ cong ((a /⟨ l ⟩ σ ↑) [ b /⟨ l ⟩ σ ∈_]) (sym (⌊⌋-Kind/⟨⟩ j)) ⟩
      (a /⟨ l ⟩ σ ↑) [ b /⟨ l ⟩ σ ∈ ⌊ j Kind/⟨ l ⟩ σ ⌋ ]
    ∎
