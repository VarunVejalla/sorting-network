# Global upper-bound contributions

This package accepts any closed Lean proof of
`limsup D(n)/log_2 n <= C`, where the canonical model and `D(n)` come from
[`../best/AKS/Bounds/Minimum.lean`](../best/AKS/Bounds/Minimum.lean). A submission
may use a construction, a nonconstructive argument, or any other proof strategy.
It does not have to use `SortingDepth.UpperBoundCertificate`.

## Submission entry point

Put the candidate theorem in `UpperBoundContrib/Candidate.lean`, in namespace
`UpperBoundContrib`, with this shape (replace `1419` with the claimed constant
and provide its proof):

```lean
import AKS.Bounds.Chvatal1830Final

namespace UpperBoundContrib

theorem candidate_bound :
    Filter.limsup
      (fun n : ℕ => (SortingDepth.minimum n : ℝ) / Real.logb 2 n)
      Filter.atTop ≤ (1419 : ℝ) := by
  exact SortingDepth.limsup_minimum_div_logb_le_1419

end UpperBoundContrib
```

The sample is a working baseline, not an improvement. Keep its declaration
name and module path so the automated check can find it. The theorem must be
closed: no extra hypotheses, project axioms, `sorry`, or altered definitions
of networks, sorting, depth, or `D(n)`.

## Checks

The `upper-bound-contributions` GitHub Actions workflow runs on pull requests
and builds this package, then compiles `UpperBoundContrib.Axioms`. That guard
requires the candidate theorem to depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms. A successful build and
guard establish that the named theorem typechecks against the canonical
minimum-depth definition and meets the accepted axiom boundary.

Locally, from this directory, run:

```sh
lake build
lake build UpperBoundContrib.Axioms
```

`AKS.Bounds.Certificate` remains available as an optional adapter for proofs
that establish an eventual `C * log_2 n + K` family of sorting networks. A
submission proving the limsup statement directly need not use it.
