# Optional expander certificate experiments

This directory is an isolated Lake package for the optional random-regular-graph
certificate and spectral experiments. Its five `AKS/` files are the minimal
source closure needed by the bridge (`AKS.Misc.List`, `AKS.Misc.Fin`,
`AKS.Graph.Regular`, `AKS.ZigZag.RVWBound`, and
`AKS.ZigZag.RVWInequality`). The package does not depend on the root AKS
library. Mathlib is referenced from the repository checkout at
`../../../.lake/packages/mathlib`.

No library or executable is a default target. Build an optional component only
when needed, from this directory, for example `lake build RandomBridge` or
`lake build cert-bench`. Building `RandomConcrete` may compile large embedded
certificate data and run expensive native computation; do not include it in
the ordinary root build. The `Random.Bench` modules are development utilities.

Certificate data are read from `data/{n}/` relative to this package. The helper
scripts and Rust programs are also package-relative: `scripts/` and `rust/`.
The certificate bench wrapper is `scripts/bench`; the deprecated one-sided PSD
experiment is also retained in that scripts directory for historical context.
`Random.Cert.ReadFFI` calls native C through Lean `@[extern]` declarations in
`Random/Cert/mmap_string.c`; this code bypasses the Lean kernel and is part of
the trusted computing base. The concrete certificate checks use `native_decide`,
which introduces native-decision axioms as recorded in
`Random/Concrete/Axioms.lean`. These are executable experimental certificates,
not kernel-only proofs.

The root directory `Random/`, its certificate Rust helpers, and their selected
scripts were relocated here. Generated certificate files remain untracked under
`data/` and are not copied into this source package.
