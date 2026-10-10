# Reorganization verification

Status on 2026-10-10 after splitting the repository into independent workstream
packages. Each package has its own Lake configuration because the packages use
overlapping `AKS.*` module names.

## Verified

- `upper-bound/best` contains the relocated Chvátal proof package. Its 61 Lean
  source files are byte-identical before and after the move. The aggregate
  path-and-content SHA-256 is
  `0015E439CCCBC40D956DCEC6E606B1AAD9EE8E822B9FFE9F05856A7CAED9C04D`.
- The installed Lean 4.29.0-rc4 toolchain completed the relocated package's
  full build (2982 jobs).
- The explicit `AKS.Bounds.Chvatal1830Axioms` guard target also passed
  (2981 jobs). It permits only `propext`, `Classical.choice`, and `Quot.sound`.
- The package and manifest use the repository's shared dependency checkout at
  `../../.lake/packages`. No dependency update was performed.
- A repository-wide normalized-line-ending audit matched 394 of the 398 moved
  tracked Lean files byte for byte. The four reviewed differences are the
  intended `ConditionalLimit` import change from `Upper` to `Minimum`, the
  relocated `Random/Cert/ReadFFI` documentation path, the upper package's shared
  package-directory setting, and the relocated graph export paths in
  `upper-bound/best/scripts/usage.lean`.
- A static import audit found no missing local import names across 345 unique
  source modules. The repository-wide source marker gate also passed.
- `upper-bound/alternatives/legacy` uses the `LegacyAKS` library with 212
  explicit roots and excludes the old `AKS` umbrella, avoiding package ownership
  ambiguity. `lower-bound/best` uses the separate `LowerBest` library.

## Additional completed checks

- `lower-bound/best`: full build passed (3430 jobs); focused
  `AKS.Bounds.KahaleAxioms` passed (3428 jobs). The four guards permit only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lower-bound/experiments`: full build passed (3489 jobs), including all 60
  retained modules. Duplicate foundations and the duplicate asymptotic module
  were removed; declared dependencies provide their original definitions.
- `upper-bound/alternatives/legacy`: focused
  `AKS.Bounds.PatersonTightAxioms` passed (3555 jobs). This checks the retained
  rounded construction and its all-n and asymptotic endpoints; it is not a
  full build of every historical module in the package.
- `research/limit-existence`: `AKS.Bounds.AmplificationAxioms` passed
  (3424 jobs), checking the conditional research results and their axiom guards.
  These theorems do not assert unconditional existence of the depth limit.
- The optional expander package's five AKS foundation modules passed
  `lake build AKS` (3341 jobs). Certificate, native evaluation, FFI, benchmark,
  and data-generation targets were not built.
- The package-specific import audit found no missing local imports, including
  imports resolved through declared dependencies. Python source syntax checks
  passed, including the five updated root source utilities.
- The staged marker gate checked renamed as well as added/modified Lean files.
  Moved executable scripts retain their original Git permissions. Build logs,
  private scratch archives, and local helper notes remain gitignored.

Both upper best checks were repeated successfully after restoring the shared
Mathlib cache: full build 2982 jobs and headline guards 2981 jobs. No dependency
revision update was performed. A failed intermediate lower check identified
an ambiguous duplicate module; removing that copy restored the green build.

Historical build claims in older notes describe their original layouts unless a
post-move check is listed here or in the relevant package's build-status file.
