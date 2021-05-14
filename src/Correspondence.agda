------------------------------------------------------------------------
-- Correspondence between paper and Agda development
------------------------------------------------------------------------

-- All file paths in this file are relative to the [`src/`](src/) folder.

module Correspondence where


------------------------------------------------------------------------
-- ## Trusted base
-- To confirm that we have proved type soundness for Fω.., and that our examples
-- are well-typed, it is sufficient to check the statement of our top-level theorems,
-- and the definition of the language with its operational semantics and
-- type system. In more detail:


-- Sec. 3:
-- - Syntax (Fig. 1): [FOmegaInt/Syntax.agda](FOmegaInt/Syntax.agda)

-- FIXME: not sure what to make clickable here...
import FOmegaInt.Syntax
module fig-1 = FOmegaInt.Syntax

-- - Declarative presentation (Fig. 3-4):
import FOmegaInt.Typing
module fig-3&4 = FOmegaInt.Typing

-- - Normalization:

-- - Theorem 5.5 (type safety):
--   * Part 1: progress

-- - Sec. 6 (undecidability):

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

------------------------------------------------------------------------
-- ## Proofs
-- - Encodings (Fig. 2): ?
-- - Lemma 3.1 (validity):
-- - Lemma 3.2 (functionality):
-- - Sec. 3.4: Subject reduction for well-kinded types (Thm. 3.3, Corollary 3.4):
-- - Sec. 3.5: Prop. 3.1 (???): preservation (this might not belong here)?

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
