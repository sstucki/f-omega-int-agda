------------------------------------------------------------------------
-- Correspondence between paper and Agda development
------------------------------------------------------------------------

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
-- # Proofs
-- ### Sec. 3
-- - Encodings (Fig. 2): ?
-- - Lemma 3.1 (validity):
-- - Lemma 3.2 (functionality):
-- - Sec. 3.4: Subject reduction for well-kinded types (Thm. 3.3, Corollary 3.4):
-- - Sec. 3.5: Prop. 3.1 (???): preservation. Not a theorem. Prop. 3.2 is proven in Thm. 5.5, listed above.

------------------------------------------------------------------------
-- ### Sec. 4
-- - Lemma 4.1 (results of substitution beta-reduce to results of het. subst.):
-- - Lemma 4.4 (substitution weakly commutes with normalization):

------------------------------------------------------------------------
-- ### Sec. 5
-- - Canonical system: syntax (Fig. 7, 8):
-- - Lemmas 5.1, 5.2, 5.3 (just to show the full statement)
-- - Lemma 5.4

{-
------------------------------------------------------------------------
** Differences between our paper (and technical appendix) and our Agda development
------------------------------------------------------------------------

There are a number of small differences between the paper presentation
of Fω.. and the formalization in Agda. We briefly discuss them here.

- In Agda, we use well-scoped de Bruijn indexes and parallel substitutions, and
  this choice affects some statements, especially for auxiliary lemmas.

- In our paper, we have inlined a few auxiliary definitions for clarity.

------------------------------------------------------------------------
** Typing lemma naming conventions
------------------------------------------------------------------------
-}

------------------------------------------------------------------------
-- Full list of Agda modules
------------------------------------------------------------------------

-- For an exhaustive list of all the modules contained in the
-- mechanization, see:

import README
