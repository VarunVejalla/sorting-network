# Best proved lower bound

This standalone Lean package contains the dependency closure of the checked
Kahale endpoint
`SortingDepth.liminf_minimum_div_logb_ge_kahale`:

```text
liminf (D(n) / log₂ n) ≥ 1 / (1 - log₂ φ).
```

`AKS.Bounds.Minimum` exposes `D(n)` from the local legacy upper-bound package.
This dependency is mathematically relevant to the chosen real-valued `liminf`:
Mathlib requires a boundedness premise, discharged here by the existing
logarithmic-depth sorting construction.  The Kahale finite inequality itself does
not use that upper construction.

Build and audit the headline result with:

```sh
lake build AKS.Bounds.KahaleAxioms
```

The copied Kahale proof sources are unchanged from the repository root.  The
shared legacy package supplies the generic asymptotic lemma and its logarithmic
upper-bound corollary; this package owns the Kahale finite and liminf endpoints.
