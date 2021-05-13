# Correspondence between paper and Agda development

All file paths in this file are relative to the [`src/`](src/) folder.

## Trusted base
To confirm that we have proved type soundness for Fω.., and that our examples
are well-typed, it is sufficient to check our type soundness
theorem, and the definition of the language with its operational semantics and
type system. In more detail:

Sec. 3:
- Syntax (Fig. 1): [FOmegaInt/Syntax.agda](FOmegaInt/Syntax.agda)
- Encodings (Fig. 2): ?
- Declarative presentation (Fig. 3-4):
- Theorem 5.5 (type safety):

## Proofs
- Lemma 3.1 (validity):
- Lemma 3.2 (functionality):
- Sec. 3.4: Subject reduction for well-kinded types (Thm. 3.3, Corollary 3.4):
- Sec. 3.5: Prop. 3.1 (???): preservation (this might not belong here)?

### Sec. 4
- Het. subst: (Fig. 5):
- Lemma 4.1, Corollary 4.2:
- Auxiliary syntax (Fig. 6):
- Lemma 4.3 (soundness of normalization)
- Lemma 4.4:

5## Sec. 4
- Canonical system: syntax (Fig. 7, 8):
