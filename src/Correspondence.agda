------------------------------------------------------------------------
-- Correspondence between paper and Agda development
------------------------------------------------------------------------

-- All file paths in this file are relative to the [`src/`](src/) folder.

module Correspondence where


------------------------------------------------------------------------
-- ## Definitions and top-level claims

-- To confirm that we have proved type soundness for Fω.., and that our examples
-- are well-typed, it is sufficient to check the statement of our top-level theorems,
-- and the definition of the language with its operational semantics and
-- type system. In more detail:


-- - Declarative System (Sec. 3):
-- -- Syntax (Fig. 1), including substitution: [FOmegaInt/Syntax.agda](FOmegaInt/Syntax.agda)

-- FIXME: not sure what to make clickable here...
import FOmegaInt.Syntax
module Syn = FOmegaInt.Syntax.Syntax
fig-1-kind = Syn.Kind
fig-1-term-type = Syn.Term

-- -- Declarative presentation (Fig. 3-4):
import FOmegaInt.Typing
module fig-3&4 = FOmegaInt.Typing

-- - Normalization (Sec. 4):
-- -- Syntax (Sec. 4.1), hereditary substitution (Fig. 5):
sec-4-1-term-type = Syn.Elim
import FOmegaInt.Syntax.HereditarySubstitution as HS
fig-5-term-type-subst = HS._/⟨_⟩_
fig-5-kind-subst = HS._Kind/⟨_⟩_

-- Is there such a thing?
-- sec-4-1-kind = Syn.Kind

-- - Theorem 5.5 (type safety):
--   * Part 1: progress

-- Sandro: not including the type signature as this requires importing
-- tons of other stuff (including from the stdlib) and possibly will
-- cause name clashes.  The important thing is the clickable link?
--
import FOmegaInt.Typing.Progress
--thm-5-5a : ∀ {a b} → [] ⊢Tm a ∈ b → Val a ⊎ (∃ λ a′ → a →v a′)
thm-5-5a = FOmegaInt.Typing.Progress.prog

--   * Part 2: weak preservation

import FOmegaInt.Typing.Preservation
thm-5-5b = FOmegaInt.Typing.Preservation.pres

-- - Sec. 6 (undecidability):
import FOmegaInt.Undecidable

------------------------------------------------------------------------
-- ## Proofs
-- - Encodings (Fig. 2): ?
-- - Lemma 3.1 (validity):
-- - Lemma 3.2 (functionality):
-- - Sec. 3.4: Subject reduction for well-kinded types (Thm. 3.3, Corollary 3.4):
-- - Sec. 3.5: Prop. 3.1 (???): preservation. Not a theorem. Prop. 3.2 is proven in Thm. 5.5, listed above.

------------------------------------------------------------------------
-- ### Sec. 4
-- - Het. subst: (Fig. 5):
-- - Lemma 4.1, Corollary 4.2:
-- - Auxiliary syntax (Fig. 6):
-- - Lemma 4.3 (soundness of normalization)
-- - Lemma 4.4:

------------------------------------------------------------------------
-- 5## Sec. 4
-- - Canonical system: syntax (Fig. 7, 8):

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

------------------------------------------------------------------------
* Directory Layout
------------------------------------------------------------------------

FIXME (P.): do we need this here, Sandro?
-}
