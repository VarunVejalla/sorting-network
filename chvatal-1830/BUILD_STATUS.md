# Repaired simplification checkpoint

Verified 2026-10-08 with Lean 4.29.0-rc4:

- Full `lake build`: successful (3009 jobs).
- `lake build AKS.Bounds.Chvatal1830Axioms`: successful (3008 jobs).
- The full build freshly compiled `Chvatal1830Final` and `Chvatal1830Axioms`.
- Both headline axiom guards accept exactly `propext`, `Classical.choice`,
  and `Quot.sound`.

The results remain `D(n) ≤ 1830 log₂(n) - 58657` for `n ≥ 2^42` and
`limsup D(n)/log₂(n) ≤ 1830`.

This checkpoint preserves the interrupted simplification, with targeted repairs
to imports, embedding unfolding, dependent rewriting, deleted wrapper references,
and shortened arithmetic/counting proofs. Some proof sections were restored from
the previously building commit. The package now has 88 Lean modules and 14,008
physical source lines under `AKS/`, excluding dependencies and build artifacts.

The saved declaration graph and older README/ledger module lists have not been
refreshed. Regenerate the graph before further declaration pruning.

Environment: Lake warns about the manifest's package-directory setting. The
installed toolchain was invoked directly; no dependency update was performed.
