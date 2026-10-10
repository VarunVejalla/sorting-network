# Verified pruning checkpoint

## Relocation check

Verified 2026-10-10 with the installed Lean 4.29.0-rc4 toolchain after moving
the package to `upper-bound/best` and changing its shared package directory to
`../../.lake/packages`:

- Full quiet `lake build`: successful (2982 jobs).
- Quiet `lake build AKS.Bounds.Chvatal1830Axioms`: successful (2981 jobs).
- The 61 checked-in Lean modules have the same aggregate path-and-content
  SHA-256 before and after the move:
  `0015E439CCCBC40D956DCEC6E606B1AAD9EE8E822B9FFE9F05856A7CAED9C04D`.

Both builds reused cached artifacts and reported only existing linter warnings.
No dependency update was run.

Verified 2026-10-09 with Lean 4.29.0-rc4 after promoting the deletion loop's
verified fixed point into this checkout:

- Full `lake build`: successful (3009 jobs), freshly compiling both headline
  theorem and axiom-guard modules.
- Explicit `lake build AKS.Bounds.Chvatal1830Axioms`: successful (3008 jobs).
- Both guards accept exactly `propext`, `Classical.choice`, and `Quot.sound`.
- The headline theorem files and minimum-depth definition are unchanged.

The promotion removes 20 written declarations and 136 physical lines across six
source files. The package has 88 Lean files, 834 written declarations, and 13,872
physical source lines. The regenerated graph contains 1,060 compiled declarations:
943 reachable and 117 unreachable from the two headline theorems. Remaining
unreachable declarations are not automatically safe to delete; source tactics
and elaboration can depend on declarations absent from the final proof terms.

See [the inventory](../../docs/chvatal-proof-inventory.md) for the counting method
and breakdown. Build logs and local pruning helpers remain gitignored.

## Previous repair checkpoint

Verified 2026-10-08 with Lean 4.29.0-rc4:

- Full `lake build`: successful (3009 jobs).
- `lake build AKS.Bounds.Chvatal1830Axioms`: successful (3008 jobs).
- The full build freshly compiled `Chvatal1830Final` and `Chvatal1830Axioms`.
- Both headline axiom guards accept exactly `propext`, `Classical.choice`,
  and `Quot.sound`.

The results remain `D(n) ≤ 1770 log₂(n) - 56497` for `n ≥ 2^42` and
`limsup D(n)/log₂(n) ≤ 1770`.

This checkpoint preserves the interrupted simplification, with targeted repairs
to imports, embedding unfolding, dependent rewriting, deleted wrapper references,
and shortened arithmetic/counting proofs. Some proof sections were restored from
the previously building commit. The package now has 88 Lean modules and 14,008
physical source lines under `AKS/`, excluding dependencies and build artifacts.

At that checkpoint, the saved declaration graph and older module lists had not
been refreshed. The graph and README inventory were subsequently regenerated.

Environment: Lake warns about the manifest's package-directory setting. The
installed toolchain was invoked directly; no dependency update was performed.
