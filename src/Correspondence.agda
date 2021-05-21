------------------------------------------------------------------------
-- Correspondence between paper and Agda development
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Correspondence where

------------------------------------------------------------------------
-- Main results
--
-- To confirm that we have mechanized all of the metatheoretic results
-- outlined in the introduction of our paper, it is sufficient to
-- check the language definitions of Fω.. (syntax, type system,
-- operational semantics) and the proofs of our main lemmas and
-- theorems. Concretely, these are:
--
--  * The declarative presentation of Fω.. (Sec. 3)
--  * Subject reduction for types and kinds (Theorem 3.3)
--  * Weak normalization of types and kinds (Lemma 4.3)
--  * Type safety (Theorem 5.5)
--  * Undecidability of subtyping (Theorem. 6.1)
--
-- In Detail:
--
-- ** The declarative presentation of Fω.. (Sec. 3) **
--
--  * Syntax (Fig. 1), including substitution.
--
--    NOTE 1. This module also contains the definition of the
--    alternative syntax described in Sec. 4.1 and a proof that the
--    two versions of the syntax are isomorphic.
--
--    NOTE 2. The syntax of values is not defined in this module.
--    Instead, it is defined as a predicate on terms in the module
--    FOmegaInt.Reduction.Cbv (see below).

import FOmegaInt.Syntax
module Syn = FOmegaInt.Syntax

--  * Structural operational semantics (Sec. 3.1.2)

import FOmegaInt.Reduction.Full
import FOmegaInt.Reduction.Cbv
module β-reduction   = FOmegaInt.Reduction.Full
module CBV-reduction = FOmegaInt.Reduction.Cbv

--  * The declarative judgments (Fig. 3-4)

import FOmegaInt.Typing
module Decl = FOmegaInt.Typing

-- ** Subject reduction for types and kinds (Theorem 3.3) **
--
--    NOTE. Subject reduction for types and kinds is proven with
--    respect to full full β-reduction.

import FOmegaInt.Typing.Validity as DeclValid
thm-3-3-1 = DeclValid.kd-→β*-≅
thm-3-3-2 = DeclValid.Tp∈-→β*-≃

--  * The more common statement of subject reduction (Corollary 3.4)

cor-3-4-1 = DeclValid.pres-kd-→β*
cor-3-4-2 = DeclValid.pres-Tp∈-→β*

-- ** Weak normalization of types and kinds (Sec. 4) **

--  * Alternative syntax, aka spine form (Sec. 4.1)

sec-4-1-Eliminations     = Syn.Syntax.Elim
sec-4-1-Heads            = Syn.Syntax.Head
sec-4-1-Spines           = Syn.Syntax.Spine
sec-4-1-KindsInSpineForm = Syn.Syntax.Kind

--  * Hereditary substitution and reducing application (Fig. 5)

import FOmegaInt.Syntax.HereditarySubstitution
module HSubst = FOmegaInt.Syntax.HereditarySubstitution
fig-5-HSubstInElims  = HSubst._/⟨_⟩_
fig-5-HSubstInSpines = HSubst._//⟨_⟩_
fig-5-HSubstInKinds  = HSubst._Kind/⟨_⟩_
fig-5-RedAppInElims  = HSubst._⌜·⌝⟨_⟩_
fig-5-RedAppInSpines = HSubst._∙∙⟨_⟩_

--  * Normalization (Fig. 6):

import FOmegaInt.Syntax.Normalization
module Norm = FOmegaInt.Syntax.Normalization
fig-6-η-Expansion = Norm.η-exp
fig-6-NfTypes     = Norm.nf
fig-6-NfKinds     = Norm.nfKind

--  * Soundness of hereditary substitution (Corollary 4.2)

import FOmegaInt.Kinding.Declarative.Normalization as DeclNorm
cor-4-2-1 = DeclNorm.kd-⌞⌟-[]-≅
cor-4-2-2 = DeclNorm.Tp∈-⌞⌟-[]-≃

--  * Soundness of normalization (Lemma 4.3)

lem-4-3-1 = DeclNorm.kd-≅-⌞⌟-nf
lem-4-3-2 = DeclNorm.Tp∈-≃-⌞⌟-nf

-- ** Type safety (Theorem 5.5) **
--
--    Part 1: progress

import FOmegaInt.Typing.Progress
thm-5-5a = FOmegaInt.Typing.Progress.prog

--    Part 2: weak preservation

import FOmegaInt.Typing.Preservation
thm-5-5b = FOmegaInt.Typing.Preservation.pres

-- ** Undecidability of subtyping (Sec. 6) **
--
--  * Syntax and equality of SK terms (Sec. 6) **

import FOmegaInt.Undecidable.SK
module SK = FOmegaInt.Undecidable.SK

--  * Undecidability of subtyping (Theorem. 6.1) **

import FOmegaInt.Undecidable
thm-6-1 = FOmegaInt.Undecidable.declarativeEquivalence


------------------------------------------------------------------------
-- Other definitions and proofs
--
-- For completeness, we list here the other definitions and lemmas
-- given in the paper that are not covered under 'Main results' above.
--
-- ** Sec. 3 -- The Declarative System **
--
--  * Encodings (Fig. 2)

import FOmegaInt.Typing.Encodings as Enc
fig-2-*       = Syn.Syntax.*    -- kind constants
fig-2-∅       = Enc.∅
fig-2-HO-intv = Enc._⋯⟨_⟩_      -- higher-order intervals
fig-2-HO-*    = Enc.*⟨_⟩
fig-2-HO-⊤    = Enc.⊤⟨_⟩        -- higher-order extrema
fig-2-HO-⊥    = Enc.⊥⟨_⟩
fig-2-erase   = Syn.Syntax.⌊_⌋  -- type erasure
fig-2-bnd-∀   = Enc.∀′          -- bounded universals type
fig-2-bnd-Π   = Enc.Π′          -- bounded operator kind
fig-2-bnd-λ   = Enc.Λ′          -- bounded lambda (same for terms and types)

--  * Lemma 3.1 (validity)

lem-3-1-kinding-validity₁        = Decl.kd-ctx
lem-3-1-kinding-validity₂        = DeclValid.Tp∈-valid
lem-3-1-typing-validity₁         = Decl.Tp∈-ctx
lem-3-1-typing-validity₂         = DeclValid.Tm∈-valid
lem-3-1-kind-equation-validity   = DeclValid.≅-valid
lem-3-1-kind-inequation-validity = DeclValid.≅-valid
lem-3-1-type-equation-validity   = DeclValid.<∷-valid
lem-3-1-type-inequation-validity = DeclValid.<:-valid

--  * Lemma 3.2 (functionality)

lem-3-2-1 = DeclValid.kd-[≃]
lem-3-2-2 = DeclValid.Tp∈-[≃]

-- ** Sec. 4 -- Normalization of Types **

--  * Lemma 4.1 (ordinary substs. β-reduce to hereditary substs.)

lem-4-1-1 = HSubst.⌞⌟Kd-/⟨⟩-β
lem-4-1-2 = HSubst.⌞⌟-/⟨⟩-β
lem-4-1-3 = HSubst.⌞⌟-⌜·⌝-β
lem-4-1-4 = HSubst.⌞⌟-∙∙-β

--  * Lemma 4.4 (substitution weakly commutes with normalization):

import FOmegaInt.Kinding.Simple.Normalization as SimpleNorm
lem-4-4-1 = SimpleNorm.nfKind-/⟨⟩
lem-4-4-2 = SimpleNorm.nf-/⟨⟩

--    NOTE. The Agda version of Lemma 4.4 referenced above uses a
--    representation of (well-kinded) single-variable substitutions
--    that is well-suited to the intrinsically well-scoped de Bruijn
--    representation used throughout the mechanization.  However, this
--    changes (and somewhat obscures) the statement of the lemma in
--    that the kinding premise shared by both parts of the lemma is
--    replaced by a well-typed substitution judgment.
--
--    A more familiar version of the statement, for the special case
--    where the last variable in the context is substituted, is stated
--    explicitly as a pair of corollaries in the Agda mechanization.

cor-lem-4-4-1 = SimpleNorm.nfKind-[]
cor-lem-4-4-2 = SimpleNorm.nf-[]

-- ** Sec. 5 -- The Canonical System **

--  * The canonical system (Fig. 7 and 8)

import FOmegaInt.Kinding.Canonical
module Canon = FOmegaInt.Kinding.Canonical

--  * Lemma 5.1 (soundness of the canonical rules -- excerpt)

import FOmegaInt.Kinding.Canonical.Equivalence as CanonEquiv
lemma-5-1-1a = CanonEquiv.sound-Nf⇉
lemma-5-1-1b = CanonEquiv.sound-Nf⇇
lemma-5-1-2  = CanonEquiv.sound-<:
lemma-5-1-3  = CanonEquiv.sound-<:⇇

--  * Lemma 5.2 (hereditary substitution -- excerpt)
--
--    NOTE. The Agda version of Lemma 5.2 again uses a representation
--    of (canonically well-kinded) single-variable substitutions
--    similar to that discussed in the comment of Lemma 4.4 above.  As
--    a consequence, the (canonical) kinding premise shared by all
--    four parts is replaced by a (canonically) well-kinded single
--    variable substitution.

import FOmegaInt.Kinding.Canonical.HereditarySubstitution as CanonHSubst
lemma-5-2-1 = CanonHSubst.Nf⇇-/⟨⟩
lemma-5-2-2 = CanonHSubst.Nf⇇-/⟨⟩≃-<:
lemma-5-2-3 = CanonHSubst.<:⇇-/⟨⟩≃
lemma-5-2-4 = CanonHSubst.≃-Π-e

--  * Lemma 5.3 (completeness of the canonical rules -- excerpt)

lemma-5-3-1 = CanonEquiv.CompletenessExtended.complete-Tp∈
lemma-5-3-2 = CanonEquiv.CompletenessExtended.complete-<:

--  * Lemma 5.4 (inversion of top-level subtyping)

import FOmegaInt.Typing.Inversion as Inv
lemma-5-4-1  = Inv.<:-∀-inv
lemma-5-4-2  = Inv.<:-→-inv
lemma-5-4-3a = Inv.⇒-≮:-Π
lemma-5-4-3b = Inv.Π-≮:-⇒


------------------------------------------------------------------------
-- Full list of Agda modules
--
-- For an exhaustive list of all the modules contained in the
-- mechanization, see:

import README
