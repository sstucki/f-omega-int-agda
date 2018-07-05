------------------------------------------------------------------------
-- Simple kinding of Fω with interval kinds
------------------------------------------------------------------------

module FOmegaInt.Kinding.Simple where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.ExtraLemmas
open import Data.Fin.Substitution.Typed
open import Data.List using ([]; _∷_; _++_; _∷ʳ_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (∃; _,_; _×_)
open import Data.Unit using (tt)
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as VecProp
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; _≡_)
open import Relation.Nullary.Negation

open import FOmegaInt.Syntax
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
  data _⊢Var_∈_ {n} (Γ : Ctx n) : Head n → SKind → Set where
    ∈-var : ∀ {k} x → lookup x Γ ≡ kd k → Γ ⊢Var var x ∈ k

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
      ∈-∙ : ∀ {x j k} {as : Spine n} → Γ ⊢Var var x ∈ j →
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
  open SimplyWfCtx public using ()
    renaming (_wf to _ctxs; _⊢_wfExt to _⊢_exts; _⊢_wfExt′ to _⊢_exts′)

open Syntax
open SimpleCtx hiding (_++_)
open Kinding
open PropEq

-- An admissible kinding rule for spine concatenation.
∈-++ : ∀ {n} {Γ : Ctx n} {as bs j k l} →
       Γ ⊢ j ∋∙ as ∈ k → Γ ⊢ k ∋∙ bs ∈ l →
       Γ ⊢ j ∋∙ as ++ bs ∈ l
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
  open TypedSub typedSub using (_,_) renaming (lookup to ∈-lookup)

  open Substitution hiding (subst; _/Var_) renaming (_Elim/Var_ to _/Var_)
  open RenamingCommutes using (Kind[∈⌊⌋]-/)
  open PropEq
  open ≡-Reasoning

  -- A helper.
  ∈-↑′ : ∀ {m n} {Δ : Ctx n} {Γ : Ctx m} {k σ} →
         Δ ⊢/Var σ ∈ Γ →
         kd ⌊ k Kind′/Var σ ⌋ ∷ Δ ⊢/Var σ VarSubst.↑ ∈ kd ⌊ k ⌋ ∷ Γ
  ∈-↑′ {Δ = Δ} {_} {k} σ∈Γ =
    subst (λ j → kd j ∷ Δ ⊢/Var _ ∈ _) (sym (⌊⌋-Kind′/Var k)) (∈-↑ tt σ∈Γ)

  -- Convert between well-kindedness judgments for variables.
  Var∈′-Var∈ : ∀ {n} {Γ : Ctx n} {x a k} → a ≡ kd k →
               Γ ⊢Var′ x ∈ a → Γ ⊢Var var x ∈ k
  Var∈′-Var∈ Γ[x]≡kd-k (var x Γ-ctx) = ∈-var x Γ[x]≡kd-k

  -- Renamings preserve synthesized kinds of variables.
  Var∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
              Γ ⊢Var a ∈ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢Var a Head/Var σ ∈ k
  Var∈-/Var (∈-var x Γ[x]≡kd-k) σ∈Γ = Var∈′-Var∈ Γ[x]≡kd-k (∈-lookup x σ∈Γ)

  mutual

    -- Renamings preserve well-formedness of kinds.
    kds-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {k σ} →
               Γ ⊢ k kds → Δ ⊢/Var σ ∈ Γ → Δ ⊢ k Kind′/Var σ kds
    kds-/Var (kds-⋯ a∈★ b∈★) σ∈Γ = kds-⋯ (Nf∈-/Var a∈★ σ∈Γ) (Nf∈-/Var b∈★ σ∈Γ)
    kds-/Var (kds-Π j-kds  k-kds) σ∈Γ =
      kds-Π (kds-/Var j-kds σ∈Γ) (kds-/Var k-kds (∈-↑′ σ∈Γ))

    -- Renamings preserve synthesized kinds of normal types.
    Nf∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Nf a ∈ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢Nf a /Var σ ∈ k
    Nf∈-/Var ∈-⊥-f              σ∈Γ = ∈-⊥-f
    Nf∈-/Var ∈-⊤-f              σ∈Γ = ∈-⊤-f
    Nf∈-/Var (∈-∀-f k-kds a∈★)  σ∈Γ =
      ∈-∀-f (kds-/Var k-kds σ∈Γ) (Nf∈-/Var a∈★ (∈-↑′ σ∈Γ))
    Nf∈-/Var (∈-→-f a∈★ b∈★)    σ∈Γ =
      ∈-→-f (Nf∈-/Var a∈★ σ∈Γ) (Nf∈-/Var b∈★ σ∈Γ)
    Nf∈-/Var (∈-Π-i {j} {a} {k} j-kds a∈k) σ∈Γ =
      subst (λ l → _ ⊢Nf Λ∙ j a /Var _ ∈ l ⇒ k) (⌊⌋-Kind′/Var j)
            (∈-Π-i (kds-/Var j-kds σ∈Γ) (Nf∈-/Var a∈k (∈-↑′ σ∈Γ)))
    Nf∈-/Var (∈-ne a∈★)         σ∈Γ = ∈-ne (Ne∈-/Var a∈★ σ∈Γ)

    -- Renamings preserve synthesized kinds of neutral types.
    Ne∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a k σ} →
               Γ ⊢Ne a ∈ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢Ne a /Var σ ∈ k
    Ne∈-/Var (∈-∙ x∈j k∈as∈l) σ∈Γ =
      ∈-∙ (Var∈-/Var x∈j σ∈Γ) (Sp∈-/Var k∈as∈l σ∈Γ)

    Sp∈-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {as j k σ} →
               Γ ⊢ j ∋∙ as ∈ k → Δ ⊢/Var σ ∈ Γ → Δ ⊢ j ∋∙ as //Var σ  ∈ k
    Sp∈-/Var ∈-[]                σ∈Γ = ∈-[]
    Sp∈-/Var (∈-∷ a∈j k[a]∈as∈l) σ∈Γ =
      ∈-∷ (Nf∈-/Var a∈j σ∈Γ) (Sp∈-/Var k[a]∈as∈l σ∈Γ)

  -- Renamings preserve well-formedness of ascriptions.
  wfs-/Var : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {a σ} →
             Γ ⊢ a wfs → Δ ⊢/Var σ ∈ Γ → Δ ⊢ a ElimAsc/Var σ wfs
  wfs-/Var (wfs-kd k-kds) σ∈Γ = wfs-kd (kds-/Var k-kds σ∈Γ)
  wfs-/Var (wfs-tp a∈★)   σ∈Γ = wfs-tp (Nf∈-/Var a∈★ σ∈Γ)

  -- Weakening preserves simple well-formedness of kinds.

  kds-weaken : ∀ {n} {Γ : Ctx n} {k a} →
               Γ ⊢ k kds → a ∷ Γ ⊢ weakenKind′ k kds
  kds-weaken k-kds = kds-/Var k-kds (∈-wk tt)

  kds-weaken⋆ : ∀ {m n} (Δ′ : CtxExt′ m n) {Γ : Ctx m} {k} →
                Γ ⊢ k kds → Δ′ ′++ Γ ⊢ weakenKind′⋆ n k kds
  kds-weaken⋆ []       k-kds = k-kds
  kds-weaken⋆ (_ ∷ Δ′) k-kds = kds-weaken (kds-weaken⋆ Δ′ k-kds)

  -- Weakening preserves kinding of normal forms.

  Nf∈-weaken : ∀ {n} {Γ : Ctx n} {a b k} →
               Γ ⊢Nf b ∈ k → (a ∷ Γ) ⊢Nf weakenElim b ∈ k
  Nf∈-weaken b∈k = Nf∈-/Var b∈k (∈-wk tt)

  Nf∈-weaken⋆ : ∀ {m n} (Δ′ : CtxExt′ m n) {Γ : Ctx m} {a k} →
                Γ ⊢Nf a ∈ k → Δ′ ′++ Γ ⊢Nf weakenElim⋆ n a ∈ k
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
              Γ ctxs → ElimCtx.lookup x Γ ≡ kd a → ⌊ Γ ⌋Ctx ⊢ a kds
  lookup-kd x Γ-ctxs Γ[x]≡kd-a =
    wfs-kd-inv (subst (_ ⊢_wfs) Γ[x]≡kd-a (W.lookup x Γ-ctxs))

module KindedHereditarySubstitution where
  open Data.Fin         using (zero; raise; lift)
  open Substitution     hiding (subst)
  open KindedRenaming   using (Nf∈-weaken⋆)
  open RenamingCommutes using (wk-/H-↑⋆; /-wk-↑⋆-hsub-vanishes)
  open PropEq
  open ≡-Reasoning

  infix 4 _⊢/H_∈_

  -- Well-kinded suspended hereditary substitions.
  data _⊢/H_∈_ : ∀ {k m n} (Δ : Ctx n) (ρ : HSub k m n) (Γ : Ctx m) → Set where
    ∈-hsub : ∀ {k m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} {a} →
             Γ₁ ⊢Nf a ∈ k →
             re-idx Γ₂ ′++ Γ₁ ⊢/H (n ← a ∈ k) ∈ Γ₂ ′++ kd k ∷ Γ₁

  -- Lift a kinded hereditary substitution over an additional variable.
  ∈-H↑ : ∀ {k m n Δ Γ} {ρ : HSub k m n} {a} →
         Δ ⊢/H ρ ∈ Γ → a ∷ Δ ⊢/H ρ H↑ ∈ a ∷ Γ
  ∈-H↑ (∈-hsub Γ a∈j) = ∈-hsub (_ ∷ Γ) a∈j

  ∈-H↑′ : ∀ {k m n Δ Γ} {ρ : HSub k m n} {j} →
          Δ ⊢/H ρ ∈ Γ → kd ⌊ j Kind/H ρ ⌋ ∷ Δ ⊢/H ρ H↑ ∈ kd ⌊ j ⌋ ∷ Γ
  ∈-H↑′ ρ∈Γ =
    subst (λ k → kd k ∷ _ ⊢/H _ H↑ ∈ kd _ ∷ _) (sym (⌊⌋-Kind/H _)) (∈-H↑ ρ∈Γ)

  -- Lift a kinded hereditary substitution over multiple additional
  -- variables.
  ∈-H↑⋆ : ∀ {k m n i} (E : CtxExt′ m i) {Δ Γ} {ρ : HSub k m n} →
          Δ ⊢/H ρ ∈ Γ → re-idx E ′++ Δ ⊢/H ρ H↑⋆ i ∈ E ′++ Γ
  ∈-H↑⋆ []      ρ∈Γ = ρ∈Γ
  ∈-H↑⋆ (a ∷ E) ρ∈Γ = ∈-H↑ (∈-H↑⋆ E ρ∈Γ)

  -- TODO: explain.
  Var∈-Hit : ∀ {k m n Γ Δ} {ρ : HSub k m n} {x j} →
             Γ ⊢Var var x ∈ j → Δ ⊢/H ρ ∈ Γ → Hit ρ x → j ≡ k
  Var∈-Hit (∈-var {j} _ Γ[x]≡kd-j) (∈-hsub {k} {_} {n} Γ₂ {Γ₁} a∈k) refl =
    kd-inj′ (begin
        kd j
      ≡⟨ sym Γ[x]≡kd-j ⟩
        lookup (raise n zero) (Γ₂ ′++ kd k ∷ Γ₁)
      ≡⟨ lookup-weaken⋆′ n zero [] Γ₂ (kd k ∷ Γ₁) ⟩
        weakenSAsc⋆ n (kd k)
      ≡⟨ weakenSAsc⋆-id n ⟩
        kd k
      ∎)

  -- Lookup a hit in a well-kinded hereditary substitution.
  --
  -- NOTE. Since `j ≡ k', we could have formulated this lemma
  -- differently.  In particular, given the premise `lookup x Γ ≡ kd
  -- j', it would have been more intuitive for the kinding judgment in
  -- the conclusion to use the simple kind `j' rather than `k'
  -- (mirroring the structure of the variable rule).  However, it is
  -- important that the simple kind `k' of the normal type returned by
  -- this function is syntactically equal to the kind annotation of
  -- the hereditary substitution `n ← a ∈ k' because it serves as the
  -- termination measure for the (hereditary) substitution lemmas
  -- below.
  Var∈-Hit-/H : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} {a j k} →
                let Γ = Γ₂ ′++ kd k ∷ Γ₁
                    Δ = re-idx Γ₂ ′++ Γ₁
                    ρ = n ← a ∈ k
                    x = raise n zero
                in lookup x Γ ≡ kd j → Γ₁ ⊢Nf a ∈ k →
                   Δ ⊢Nf ⌜ Vec.lookup (sub ⌞ a ⌟ ↑⋆ n) x ⌝ ∈ k × j ≡ k
  Var∈-Hit-/H {_} {n} Γ₂ {Γ₁} {a} {j} {k} Γ[x]≡kd-j a∈k =
    subst (re-idx Γ₂ ′++ Γ₁ ⊢Nf_∈ _) (begin
          weakenElim⋆ n a
        ≡⟨ sym (Elim/-wk⋆ n) ⟩
          a Elim/ wk⋆ n
        ≡⟨ cong (_Elim/ wk⋆ n) (sym (⌜⌝∘⌞⌟-id a)) ⟩
          ⌜ ⌞ a ⌟ ⌝ Elim/ wk⋆ n
        ≡⟨ sym (⌜⌝-/ ⌞ a ⌟) ⟩
          ⌜ ⌞ a ⌟ / wk⋆ n ⌝
        ≡⟨ cong ⌜_⌝ (sym (ExtLemmas₄.raise-/-↑⋆ lemmas₄ n zero)) ⟩
          ⌜ Vec.lookup (sub ⌞ a ⌟ ↑⋆ n) (raise n zero) ⌝
        ∎)
      (Nf∈-weaken⋆ (re-idx Γ₂) a∈k) ,
      (Var∈-Hit (∈-var (raise n zero) Γ[x]≡kd-j) (∈-hsub Γ₂ a∈k) refl)

  -- TODO: Could this be refactored to replace the above?
  Var∈-Hit-/H′ : ∀ {k m n Γ Δ} {ρ : HSub k m n} {x j} →
                 Γ ⊢Var var x ∈ j → Δ ⊢/H ρ ∈ Γ → Hit ρ x →
                 Δ ⊢Nf var∙ x /H ρ ∈ k × j ≡ k
  Var∈-Hit-/H′ (∈-var {j} _ Γ[x]≡kd-j) (∈-hsub {k} {_} {n} Γ₂ {Γ₁} a∈k) refl =
    let x/ρ∈k , j≡k = Var∈-Hit-/H Γ₂ Γ[x]≡kd-j a∈k
    in subst (_ ⊢Nf_∈ _) (sym (var∙-/H-/ (n ← _ ∈ k) ((raise n zero)))) x/ρ∈k ,
       j≡k

  -- Lookup a miss in a well-kinded hereditary substitution.
  Var∈-Miss-/H : ∀ {m n} (Γ₂ : CtxExt′ (suc m) n) {Γ₁ : Ctx m} {x j k} →
                 let Γ = Γ₂ ′++ kd k ∷ Γ₁
                     Δ = re-idx Γ₂ ′++ Γ₁
                 in lookup (lift n suc x) Γ ≡ kd j → Δ ⊢Var var x ∈ j
  Var∈-Miss-/H {m} {n} Γ₂ {Γ₁} {x} {j} {k} Γ[x]≡kd-j =
    ∈-var x (begin
        lookup x ((re-idx Γ₂) ′++ Γ₁)
      ≡⟨ lookup-′++ x [] (re-idx Γ₂) Γ₁ ⟩
        extLookup′ x (toVec Γ₁) (re-idx Γ₂)
      ≡⟨ lookup′-lift x (kd k) (toVec Γ₁) (re-idx Γ₂) ⟩
        extLookup′ (lift n suc x) (kd k ∷ toVec Γ₁) (re-idx Γ₂)
      ≡⟨ cong (λ ts → extLookup′ (lift n suc x) ts (re-idx {m = m} Γ₂)) (begin
            kd k ∷ toVec Γ₁
          ≡⟨ sym (map-id (kd k ∷ toVec Γ₁)) ⟩
            Vec.map Function.id (kd k ∷ toVec Γ₁)
          ≡⟨ map-∘ Function.id Function.id (kd k ∷ toVec Γ₁) ⟩
            Vec.map Function.id (toVec (kd k ∷ Γ₁))
          ∎) ⟩
        extLookup′ (lift n suc x) (Vec.map Function.id (toVec (kd k ∷ Γ₁)))
                   (re-idx Γ₂)
      ≡⟨ lookup′-map′ (lift n suc x) (λ _ k → k) (toVec (kd k ∷ Γ₁)) Γ₂
                      (λ _ → refl) ⟩
        extLookup′ (lift n suc x) (toVec (kd k ∷ Γ₁)) Γ₂
      ≡⟨ (sym (lookup-′++ (lift n suc x) [] Γ₂ (kd k ∷ Γ₁))) ⟩
        lookup (lift n suc x) (Γ₂ ′++ kd k ∷ Γ₁)
      ≡⟨ Γ[x]≡kd-j ⟩
        kd j
      ∎)
    where open VecProp using (map-id; map-∘)

  open KindSimpLemmas simpLemmasKind′

  -- TODO: explain why this terminates.
  mutual

    -- Hereditary substitutions preserve simple well-formedness of kinds.
    kds-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {j} →
             Γ ⊢ j kds → Δ ⊢/H ρ ∈ Γ → Δ ⊢ j Kind/H ρ kds
    kds-/H (kds-⋯ a∈★ b∈★)     ρ∈Γ = kds-⋯ (Nf∈-/H a∈★ ρ∈Γ) (Nf∈-/H b∈★ ρ∈Γ)
    kds-/H (kds-Π j-kds k-kds) ρ∈Γ =
      kds-Π (kds-/H j-kds ρ∈Γ) (kds-/H k-kds (∈-H↑′ ρ∈Γ))

    -- Hereditary substitutions preserve simple kinding of normal types.
    Nf∈-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {a j} →
             Γ ⊢Nf a ∈ j → Δ ⊢/H ρ ∈ Γ → Δ ⊢Nf a /H ρ ∈ j
    Nf∈-/H ∈-⊥-f             ρ∈Γ = ∈-⊥-f
    Nf∈-/H ∈-⊤-f             ρ∈Γ = ∈-⊤-f
    Nf∈-/H (∈-∀-f k-kds a∈★) ρ∈Γ =
      ∈-∀-f (kds-/H k-kds ρ∈Γ) (Nf∈-/H a∈★ (∈-H↑′ ρ∈Γ))
    Nf∈-/H (∈-→-f a∈★ b∈★)   ρ∈Γ =
      ∈-→-f (Nf∈-/H a∈★ ρ∈Γ) (Nf∈-/H b∈★ ρ∈Γ)
    Nf∈-/H (∈-Π-i {j} {a} {k} j-kds a∈k) ρ∈Γ =
      subst (λ l → _ ⊢Nf Λ∙ j a /H _ ∈ l ⇒ k) (⌊⌋-Kind/H j)
            (∈-Π-i (kds-/H j-kds ρ∈Γ) (Nf∈-/H a∈k (∈-H↑′ ρ∈Γ)))
    Nf∈-/H (∈-ne a∈★)        ρ∈Γ = Ne∈-/H a∈★ ρ∈Γ

    -- Hereditary substitutions preserve simple kinds of neutral
    -- types (but not neutrality itself).
    Ne∈-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {a} →
             Γ ⊢Ne a ∈ ★ → Δ ⊢/H ρ ∈ Γ → Δ ⊢Nf a /H ρ ∈ ★
    Ne∈-/H (∈-∙ (∈-var x Γ[x]≡kd-j) j∈as∈l)
           (∈-hsub {_} {_} {n} Γ₂ a∈k) with compare n x
    Ne∈-/H (∈-∙ {_} {_} {_} {as} (∈-var _ Γ[x]≡kd-j) j∋as∈l) (∈-hsub Γ₂ a∈k)
      | yes refl =
      let a/ρ∈k , j≡k = Var∈-Hit-/H Γ₂ Γ[x]≡kd-j a∈k
          k∋as∈l      = subst (_ ⊢_∋∙ as ∈ _) j≡k j∋as∈l
      in Nf∈-∙∙ a/ρ∈k (Sp∈-/H k∋as∈l (∈-hsub Γ₂ a∈k))
    Ne∈-/H (∈-∙ (∈-var _ Γ[x]≡kd-j) j∋as∈l) (∈-hsub Γ₂ a∈k) | no y refl =
      ∈-ne (∈-∙ (Var∈-Miss-/H Γ₂ Γ[x]≡kd-j) (Sp∈-/H j∋as∈l (∈-hsub Γ₂ a∈k)))

    -- Hereditary substitutions preserve simple kinding of spines.
    Sp∈-/H : ∀ {k m n Γ Δ} {ρ : HSub k m n} {as j₁ j₂} →
             Γ ⊢ j₁ ∋∙ as ∈ j₂ → Δ ⊢/H ρ ∈ Γ → Δ ⊢ j₁ ∋∙ as //H ρ ∈ j₂
    Sp∈-/H ∈-[]                   ρ∈Γ = ∈-[]
    Sp∈-/H (∈-∷ a∈j₁ j₂[a]∈as∈j₃) ρ∈Γ =
      ∈-∷ (Nf∈-/H a∈j₁ ρ∈Γ) (Sp∈-/H j₂[a]∈as∈j₃ ρ∈Γ)

    -- Applications in simple kinding are admissible.

    Nf∈-∙∙ : ∀ {n} {Γ : Ctx n} {a as j k} →
             Γ ⊢Nf a ∈ j → Γ ⊢ j ∋∙ as ∈ k → Γ ⊢Nf a ∙∙⟨ j ⟩ as ∈ k
    Nf∈-∙∙ a∈j   ∈-[]             = a∈j
    Nf∈-∙∙ a∈j⇒k (∈-∷ b∈j k∋as∈l) = Nf∈-∙∙ (Nf∈-Π-e a∈j⇒k b∈j) k∋as∈l

    Nf∈-Π-e : ∀ {n} {Γ : Ctx n} {a b j k} →
              Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Γ ⊢Nf a ⌜·⌝⟨ j ⇒ k ⟩ b ∈ k
    Nf∈-Π-e (∈-Π-i j-kds a∈k) b∈⌊j⌋ = Nf∈-/H a∈k (∈-hsub [] b∈⌊j⌋)

  -- Concatenation of simply well-formed spines results in application.
  Nf∈-++-∙∙⟨⟩ : ∀ {n} {Γ : Ctx n} {a bs cs j k l} →
                Γ ⊢Nf a ∈ j → Γ ⊢ j ∋∙ bs ∈ k → Γ ⊢ k ∋∙ cs ∈ l →
                a ∙∙⟨ j ⟩ (bs ++ cs) ≡ a ∙∙⟨ j ⟩ bs ∙∙⟨ k ⟩ cs
  Nf∈-++-∙∙⟨⟩ a∈j     ∈-[]                  k∋cs∈l = refl
  Nf∈-++-∙∙⟨⟩ a∈j₁⇒j₂ (∈-∷ b∈j₁ j₂[b]∋bs∈k) k∋cs∈l =
    Nf∈-++-∙∙⟨⟩ (Nf∈-Π-e a∈j₁⇒j₂ b∈j₁) j₂[b]∋bs∈k k∋cs∈l

  -- Another admissible kinding rule for applications.
  Nf∈-Π-e′ : ∀ {n} {Γ : Ctx n} {a b j k} →
             Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Γ ⊢Nf a ↓⌜·⌝ b ∈ k
  Nf∈-Π-e′ (∈-Π-i j-kds a∈k) b∈⌊j⌋ = Nf∈-/H a∈k (∈-hsub [] b∈⌊j⌋)

  mutual

    -- Simply well-kinded hereditary substitutions in simply
    -- well-formed kinds commute.
    kds-[]-/H-↑⋆ : ∀ {i m n} (E : CtxExt′ (suc m) i) {Γ Δ}
                   {j b k l} {ρ : HSub l m n} →
                   E ′++ kd k ∷ Γ ⊢ j kds → Γ ⊢Nf b ∈ k → Δ ⊢/H ρ ∈ Γ →
                   j Kind/H (i ← b ∈ k) Kind/H ρ H↑⋆ i ≡
                     j Kind/H (ρ H↑) H↑⋆ i Kind/H (i ← b /H ρ ∈ k)
    kds-[]-/H-↑⋆ E (kds-⋯ a∈★ b∈★)     c∈k ρ∈Γ =
      cong₂ _⋯_ (Nf∈-[]-/H-↑⋆ E a∈★ c∈k ρ∈Γ) (Nf∈-[]-/H-↑⋆ E b∈★ c∈k ρ∈Γ)
    kds-[]-/H-↑⋆ E (kds-Π j-kds k-kds) b∈k ρ∈Γ =
      cong₂ Π (kds-[]-/H-↑⋆ E j-kds b∈k ρ∈Γ)
              (kds-[]-/H-↑⋆ (_ ∷ E) k-kds b∈k ρ∈Γ)

    -- Simply well-kinded hereditary substitutions in simply
    -- well-kinded types commute.

    Nf∈-[]-/H-↑⋆ : ∀ {i m n} (E : CtxExt′ (suc m) i) {Γ Δ}
                   {a b j k l} {ρ : HSub l m n} →
                   E ′++ kd k ∷ Γ ⊢Nf a ∈ j → Γ ⊢Nf b ∈ k → Δ ⊢/H ρ ∈ Γ →
                   a /H (i ← b ∈ k) /H ρ H↑⋆ i ≡
                     a /H (ρ H↑) H↑⋆ i /H (i ← b /H ρ ∈ k)
    Nf∈-[]-/H-↑⋆ E ∈-⊥-f b∈k ρ∈Γ = refl
    Nf∈-[]-/H-↑⋆ E ∈-⊤-f b∈k ρ∈Γ = refl
    Nf∈-[]-/H-↑⋆ E (∈-∀-f k-kds a∈★) b∈k ρ∈Γ =
      cong (_∙ []) (cong₂ Π (kds-[]-/H-↑⋆ E k-kds b∈k ρ∈Γ)
                            (Nf∈-[]-/H-↑⋆ (_ ∷ E) a∈★ b∈k ρ∈Γ))
    Nf∈-[]-/H-↑⋆ E (∈-→-f a∈★ b∈★)   c∈k ρ∈Γ =
      cong (_∙ []) (cong₂ _⇒_ (Nf∈-[]-/H-↑⋆ E a∈★ c∈k ρ∈Γ)
                              (Nf∈-[]-/H-↑⋆ E b∈★ c∈k ρ∈Γ))
    Nf∈-[]-/H-↑⋆ E (∈-Π-i j-kds a∈l) b∈k ρ∈Γ =
      cong (_∙ []) (cong₂ Λ (kds-[]-/H-↑⋆ E j-kds b∈k ρ∈Γ)
                            (Nf∈-[]-/H-↑⋆ (_ ∷ E) a∈l b∈k ρ∈Γ))
    Nf∈-[]-/H-↑⋆ E (∈-ne a∈★)        b∈k ρ∈Γ = Ne∈-[]-/H-↑⋆ E a∈★ b∈k ρ∈Γ

    Ne∈-[]-/H-↑⋆ : ∀ {i m n} (E : CtxExt′ (suc m) i) {Γ Δ}
                   {a b j k l} {ρ : HSub l m n} →
                   E ′++ kd k ∷ Γ ⊢Ne a ∈ j → Γ ⊢Nf b ∈ k → Δ ⊢/H ρ ∈ Γ →
                   a /H (i ← b ∈ k) /H ρ H↑⋆ i ≡
                     a /H (ρ H↑) H↑⋆ i /H (i ← b /H ρ ∈ k)
    Ne∈-[]-/H-↑⋆ {i} E (∈-∙ (∈-var x _) j∋as∈l) b∈k ρ∈Γ with compare i x
    Ne∈-[]-/H-↑⋆ {i} E {b = b} {_} {k} {_} {ρ}
                 (∈-∙ {as = as} (∈-var _ Γ[x]≡kd-j) j∋as∈l) b∈k ρ∈Γ
      | yes refl = begin
        ⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩
          (as //H i ← b ∈ k) /H ρ H↑⋆ i
      ≡⟨ helper i E (raise i zero) as b k ρ refl Γ[x]≡kd-j j∋as∈l b∈k ρ∈Γ ⟩
        var (raise i zero) ∙ (as //H (ρ H↑) H↑⋆ i) /H (i ← b /H ρ ∈ k)
      ≡⟨ cong (_/H (i ← b /H ρ ∈ k))
              (sym (ne-/H-↑⋆-Miss i zero zero (↑-zero-Miss ρ))) ⟩
        var (raise i zero) ∙ as /H (ρ H↑) H↑⋆ i /H (i ← b /H ρ ∈ k)
      ∎
      where
        open ExtLemmas₄ lemmas₄ using (raise-/-↑⋆)

        helper : ∀ i {m n} (E : CtxExt′ (suc m) i) {Γ Δ}
                 x as b k {j₁ j₂ l} (ρ : HSub l m n) → raise i zero ≡ x →
                 lookup (raise i zero) (E ′++ kd k ∷ Γ) ≡ kd j₁ →
                 E ′++ kd k ∷ Γ ⊢ j₁ ∋∙ as ∈ j₂ → Γ ⊢Nf b ∈ k → Δ ⊢/H ρ ∈ Γ →
                 ⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩
                   (as //H i ← b ∈ k) /H ρ H↑⋆ i ≡
                     (var x ∙ (as //H (ρ H↑) H↑⋆ i) /H (i ← b /H ρ ∈ k))
        helper i E x  as b k ρ hyp Γ[i]≡kd-j j∋as∈l b∈k ρ∈Γ with compare i x
        helper i E ._ as b k ρ hyp Γ[i]≡kd-j j∋as∈l b∈k ρ∈Γ | yes refl =
          let b/ρ∈k , j≡k = Var∈-Hit-/H E Γ[i]≡kd-j b∈k
              k∋as∈l      = subst (_ ⊢_∋∙ as ∈ _) j≡k j∋as∈l
              ρ↑⋆i∈E++Γ   = ∈-H↑⋆ (re-idx E) ρ∈Γ
          in begin
            ⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩ (as //H i ← b ∈ k)
              /H ρ H↑⋆ i
          ≡⟨ Nf∈-∙∙-/H b/ρ∈k (Sp∈-/H k∋as∈l (∈-hsub E b∈k)) ρ↑⋆i∈E++Γ ⟩
            (⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ /H ρ H↑⋆ i) ∙∙⟨ k ⟩
              (as //H (i ← b ∈ k) //H ρ H↑⋆ i)
          ≡⟨ cong₂ (_∙∙⟨ k ⟩_) (begin
                 ⌜ var (raise i zero) / sub ⌞ b ⌟ ↑⋆ i ⌝ /H ρ H↑⋆ i
               ≡⟨ cong ((_/H ρ H↑⋆ i) ∘ ⌜_⌝) (raise-/-↑⋆ i zero) ⟩
                 ⌜ ⌞ b ⌟ / wk⋆ i ⌝ /H ρ H↑⋆ i
               ≡⟨ cong (_/H ρ H↑⋆ i) (⌜⌝-/ ⌞ b ⌟) ⟩
                 ⌜ ⌞ b ⌟ ⌝ Elim/ wk⋆ i /H ρ H↑⋆ i
               ≡⟨ wk⋆-/H-↑⋆ i ⌜ ⌞ b ⌟ ⌝ ⟩
                 ⌜ ⌞ b ⌟ ⌝ /H ρ Elim/ wk⋆ i
               ≡⟨ cong ((_Elim/ wk⋆ i) ∘ (_/H ρ)) (⌜⌝∘⌞⌟-id b) ⟩
                 b /H ρ Elim/ wk⋆ i
               ≡⟨ cong (_Elim/ wk⋆ i) (sym (⌜⌝∘⌞⌟-id (b /H ρ))) ⟩
                 ⌜ ⌞ b /H ρ ⌟ ⌝ Elim/ wk⋆ i
               ≡⟨ sym (⌜⌝-/ ⌞ b /H ρ ⌟) ⟩
                 ⌜ ⌞ b /H ρ ⌟ / wk⋆ i ⌝
               ≡⟨ cong ⌜_⌝ (sym (raise-/-↑⋆ i zero)) ⟩
                 ⌜ var (raise i zero) / sub ⌞ b /H ρ ⌟ ↑⋆ i ⌝
               ∎) (Sp∈-[]-/H-↑⋆ E j∋as∈l b∈k ρ∈Γ) ⟩
            ⌜ var (raise i zero) / sub ⌞ b /H ρ ⌟ ↑⋆ i ⌝ ∙∙⟨ k ⟩
              (as //H (ρ H↑) H↑⋆ i //H i ← b /H ρ ∈ k)
          ∎
        helper i E ._ as b k ρ hyp Γ[x]≡kd-j₁ j₁∋as∈j₂ b∈k ρ∈Γ | no z refl =
          contradiction hyp (yes-≠-no i z)
    Ne∈-[]-/H-↑⋆ {i} E {ρ = ρ} (∈-∙ (∈-var _ Γ[x]≡kd-j) j∋as∈l) b∈k ρ∈Γ
      | no y refl with hit? (ρ H↑⋆ i) y
    Ne∈-[]-/H-↑⋆ {i} E {b = b} {_} {k₁} {k₂} {ρ}
                 (∈-∙ {as = as} (∈-var _ Γ[x]≡kd-j) j∋as∈l) b∈k₁ ρ∈Γ
      | no y refl | yes hit =
      let module V = VarSubst
          ρ∈E++k∷Γ      = ∈-H↑⋆ E (∈-H↑ ρ∈Γ)
          lift-hit      = lift-↑⋆-Hit ρ i y hit
          y/ρ↑⋆∈k , j≡k = Var∈-Hit-/H′ (∈-var _ Γ[x]≡kd-j) ρ∈E++k∷Γ lift-hit
          k∋as∈l        = subst (_ ⊢_∋∙ as ∈ _) j≡k j∋as∈l
      in begin
        var y ∙ (as //H (i ← b ∈ k₁)) /H ρ H↑⋆ i
      ≡⟨ ne-/H-Hit y hit ⟩
        (var∙ y /H ρ H↑⋆ i) ∙∙⟨ k₂ ⟩ (as //H i ← b ∈ k₁ //H ρ H↑⋆ i)
      ≡⟨ cong₂ (_∙∙⟨ k₂ ⟩_) (begin
            var∙ y /H ρ H↑⋆ i
          ≡⟨ cong (_/H ρ H↑⋆ i) (sym (ne-no-/H i y))  ⟩
            var∙ (lift i suc y) /H i ← b ∈ k₁ /H ρ H↑⋆ i
          ≡⟨ cong (λ z → var∙ z /H i ← b ∈ k₁ /H ρ H↑⋆ i)
                  (sym (VarLemmas.lookup-wk-↑⋆ i y)) ⟩
            var∙ y Elim/Var V.wk V.↑⋆ i /H i ← b ∈ k₁ /H ρ H↑⋆ i
          ≡⟨ cong (_/H ρ H↑⋆ i) (/-wk-↑⋆-hsub-vanishes i (var∙ y)) ⟩
            var∙ y /H ρ H↑⋆ i
          ≡⟨ sym (/-wk-↑⋆-hsub-vanishes i (var∙ y /H ρ H↑⋆ i)) ⟩
            var∙ y /H ρ H↑⋆ i Elim/Var V.wk V.↑⋆ i /H i ← b /H ρ ∈ k₁
          ≡⟨ cong (_/H i ← b /H ρ ∈ k₁) (sym (wk-/H-↑⋆ i (var∙ y))) ⟩
            var∙ y Elim/Var V.wk V.↑⋆ i /H (ρ H↑) H↑⋆ i /H i ← b /H ρ ∈ k₁
          ≡⟨ cong (λ z → var∙ z /H (ρ H↑) H↑⋆ i /H i ← b /H ρ ∈ k₁)
                  (VarLemmas.lookup-wk-↑⋆ i y) ⟩
            var∙ (lift i suc y) /H (ρ H↑) H↑⋆ i /H i ← b /H ρ ∈ k₁
          ∎) (Sp∈-[]-/H-↑⋆ E j∋as∈l b∈k₁ ρ∈Γ) ⟩
        (var∙ (lift i suc y) /H (ρ H↑) H↑⋆ i /H i ← b /H ρ ∈ k₁) ∙∙⟨ k₂ ⟩
          (as //H (ρ H↑) H↑⋆ i //H i ← b /H ρ ∈ k₁)
      ≡⟨ sym (Nf∈-∙∙-/H y/ρ↑⋆∈k (Sp∈-/H k∋as∈l ρ∈E++k∷Γ)
                        (∈-hsub (re-idx E) (Nf∈-/H b∈k₁ ρ∈Γ))) ⟩
        (var∙ (lift i suc y) /H (ρ H↑) H↑⋆ i) ∙∙⟨ k₂ ⟩ (as //H (ρ H↑) H↑⋆ i) /H
          (i ← b /H ρ ∈ k₁)
      ≡⟨ cong (_/H (i ← b /H ρ ∈ k₁))
              (sym (ne-/H-Hit (lift i suc y) (lift-↑⋆-Hit ρ i y hit))) ⟩
        var (lift i suc y) ∙ as /H (ρ H↑) H↑⋆ i /H (i ← b /H ρ ∈ k₁)
      ∎
    Ne∈-[]-/H-↑⋆ {i} E {b = b} {_} {k} {_} {ρ}
                 (∈-∙ {as = as} (∈-var _ Γ[x]≡kd-j) j∋as∈l) b∈k ρ∈Γ
      | no y refl | no z miss = begin
        var y ∙ (as //H (i ← b ∈ k)) /H ρ H↑⋆ i
      ≡⟨ ne-/H-Miss y z miss ⟩
        var z ∙ (as //H (i ← b ∈ k) //H ρ H↑⋆ i)
      ≡⟨ cong (var z ∙_) (Sp∈-[]-/H-↑⋆ E j∋as∈l b∈k ρ∈Γ) ⟩
        var z ∙ (as //H (ρ H↑) H↑⋆ i //H (i ← b /H ρ ∈ k))
      ≡⟨ sym (ne-no-/H i z) ⟩
        var (lift i suc z) ∙ (as //H (ρ H↑) H↑⋆ i) /H (i ← b /H ρ ∈ k)
      ≡⟨ cong (_/H (i ← b /H ρ ∈ k))
              (sym (ne-/H-Miss (lift i suc y) (lift i suc z)
                               (lift-↑⋆-Miss ρ i y z miss))) ⟩
        var (lift i suc y) ∙ as /H (ρ H↑) H↑⋆ i /H (i ← b /H ρ ∈ k)
      ∎

    Sp∈-[]-/H-↑⋆ : ∀ {i m n} (E : CtxExt′ (suc m) i) {Γ Δ}
                   {as b j₁ j₂ k l} {ρ : HSub l m n} →
                   E ′++ kd k ∷ Γ ⊢ j₁ ∋∙ as ∈ j₂ → Γ ⊢Nf b ∈ k → Δ ⊢/H ρ ∈ Γ →
                   as //H (i ← b ∈ k) //H ρ H↑⋆ i ≡
                     as //H (ρ H↑) H↑⋆ i //H (i ← b /H ρ ∈ k)
    Sp∈-[]-/H-↑⋆ E ∈-[]                b∈k ρ∈Γ = refl
    Sp∈-[]-/H-↑⋆ E (∈-∷ a∈j₁ j₂∋as∈j₃) b∈k ρ∈Γ =
      cong₂ _∷_ (Nf∈-[]-/H-↑⋆ E a∈j₁ b∈k ρ∈Γ) (Sp∈-[]-/H-↑⋆ E j₂∋as∈j₃ b∈k ρ∈Γ)

    -- Reducing applications commute with hereditary substitution.

    Nf∈-∙∙-/H : ∀ {l m n Γ Δ} {ρ : HSub l m n} {a as j k} →
                Γ ⊢Nf a ∈ j → Γ ⊢ j ∋∙ as ∈ k → Δ ⊢/H ρ ∈ Γ →
                a ∙∙⟨ j ⟩ as /H ρ ≡ (a /H ρ) ∙∙⟨ j ⟩ (as //H ρ)
    Nf∈-∙∙-/H a∈j ∈-[] ρ∈Γ = refl
    Nf∈-∙∙-/H {ρ = ρ} {a} {b ∷ bs} {j ⇒ k} a∈j⇒k (∈-∷ b∈j k∋bs∈l) ρ∈Γ = begin
        a ⌜·⌝⟨ j ⇒ k ⟩ b ∙∙⟨ k ⟩ bs /H ρ
      ≡⟨ Nf∈-∙∙-/H (Nf∈-Π-e a∈j⇒k b∈j) k∋bs∈l ρ∈Γ ⟩
        (a ⌜·⌝⟨ j ⇒ k ⟩ b /H ρ) ∙∙⟨ _ ⟩ (bs //H ρ)
      ≡⟨ cong (_∙∙⟨ k ⟩ (bs //H ρ)) (Nf∈-Π-e-/H a∈j⇒k b∈j ρ∈Γ) ⟩
        (a /H ρ) ⌜·⌝⟨ j ⇒ k ⟩ (b /H ρ) ∙∙⟨ k ⟩ (bs //H ρ)
      ∎

    Nf∈-Π-e-/H : ∀ {l m n Γ Δ} {ρ : HSub l m n} {a b j k} →
                 Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Δ ⊢/H ρ ∈ Γ →
                 a ⌜·⌝⟨ j ⇒ k ⟩ b /H ρ ≡ (a /H ρ) ⌜·⌝⟨ j ⇒ k ⟩ (b /H ρ)
    Nf∈-Π-e-/H (∈-Π-i j-kds a∈k) b∈⌊j⌋ ρ∈Γ = Nf∈-[]-/H-↑⋆ [] a∈k b∈⌊j⌋ ρ∈Γ

  -- Potentially reducing applications commute with hereditary
  -- substitution.
  Nf∈-Π-e-/H′ : ∀ {l m n Γ Δ} {ρ : HSub l m n} {a b j k} →
                Γ ⊢Nf a ∈ j ⇒ k → Γ ⊢Nf b ∈ j → Δ ⊢/H ρ ∈ Γ →
                a ↓⌜·⌝ b /H ρ ≡ (a /H ρ) ↓⌜·⌝ (b /H ρ)
  Nf∈-Π-e-/H′ {ρ = ρ} {_} {b} (∈-Π-i {j} {a} j-kds a∈k) b∈⌊j⌋ ρ∈Γ =
    begin
      (a [ b ∈ ⌊ j ⌋ ]) /H ρ
    ≡⟨ Nf∈-[]-/H-↑⋆ [] a∈k b∈⌊j⌋ ρ∈Γ ⟩
      (a /H ρ H↑) [ b /H ρ ∈ ⌊ j ⌋ ]
    ≡⟨ cong ((a /H ρ H↑) [ b /H ρ ∈_]) (sym (⌊⌋-Kind/H j)) ⟩
      (a /H ρ H↑) [ b /H ρ ∈ ⌊ j Kind/H ρ ⌋ ]
    ∎
