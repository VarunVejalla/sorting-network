# Global upper-bound contributions

This package accepts any closed Lean proof of an upper bound on `limsup D(n)/log₂ n`, where the canonical
model and `D(n)` (`SortingDepth.minimum`) come from [`../best/AKS/Bounds/Minimum.lean`](../best/AKS/Bounds/Minimum.lean).
A submission may use a construction, a nonconstructive argument, or any other strategy. What a verified
result means, what must be trusted and what the checks do not cover is in
[`../TRUSTED.md`](../TRUSTED.md); read it before reviewing a claim.

## The statement

```lean
def BoundSpec (C : ℝ) : Prop :=          -- UpperBoundContrib/Spec.lean (trusted, fingerprinted)
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (SortingDepth.minimum n : ℝ) ≤ (C + ε) * Real.logb 2 (n : ℝ)
```

`BoundSpec.limsup_le : BoundSpec C → limsup D(n)/log₂ n ≤ C`. The eventual pointwise form is used because in
`ℝ` a `limsup` of an unbounded sequence is the junk value `0`. `NetSpec C` is the equivalent network form
(`BoundSpec.netSpec`, `NetSpec.boundSpec`); `FromCertificate.boundSpec_of_certificate` adapts the optional
`AKS.Bounds.Certificate` API (an eventual `C * log₂ n + K` family of sorting networks).

## Submission entry point

Edit `UpperBoundContrib/Candidate.lean` (keep the module path and the names `claimed`, `candidate_bound`):

```lean
namespace UpperBoundContrib
def claimed : ℝ := 1419                       -- your claimed constant
theorem candidate_bound : BoundSpec claimed := currentBest_spec   -- replace by your proof
end UpperBoundContrib
```

The theorem must be closed: no extra hypotheses, project axioms, `sorry`, `native_decide`, or altered
definitions of networks, sorting, depth or `D(n)` (the last is enforced by the fingerprint of the trusted base).
The sample is a baseline, not an improvement.

## Checks

```sh
python3 scripts/check-contribution      # from the repository root: everything below, in order
```

1. `scripts/trusted-fingerprint --check`: the trusted base (definitions, spec, guards, lakefiles, scripts, CI) is unchanged.
2. `scripts/check-status`: `upper-bound/STATUS.json`, `Best.lean` and the headline file agree on the accepted constant.
3. `lake build` and `lake build UpperBoundContrib.Axioms` here: the candidate builds; `Axioms.lean` pins the exact type
   (`example : BoundSpec claimed := candidate_bound`) and allows only `propext, Classical.choice, Quot.sound`.
4. `lake build UpperBoundGate` (informational): compiles iff `claimed < currentBest`, i.e. the claim strictly improves the
   accepted best (it fails for the baseline by design).

The GitHub workflow `upper-bound-contributions` runs 1–3 as blocking jobs and 4 as informational. A manual, draft
workflow `upper-bound-comparator` replays the proof with an independent kernel in a sandbox (not yet run here).

## Comparator Challenge (draft)

`Challenge.lean` (Mathlib-only copies of the definitions, one `sorry`ed theorem `upper_bound_certified`) and
`challenge.json` follow the legacy package's layout; `UpperBoundSolution.lean` proves the same statement from the
candidate (`lake build UpperBoundSolution`). Their pretty-printed types were checked identical; the comparator itself has
not been run. `scripts/make-limsup-challenge C` rewrites the constant in both files. The definitions in `Challenge.lean`
must stay textually identical to `../best/AKS/Sort/{Defs,Depth,Monotone}.lean`.

## Accepting an improvement

(1) PR changes `Candidate.lean` (+ any new modules under `UpperBoundContrib/` or a package it requires) and, for a new
constant, `UpperBoundSolution.lean`/`Challenge.lean` via `scripts/make-limsup-challenge`; (2) CI green and the improvement gate
shows strict improvement; (3) owner promotes: moves the package under `../best` (previous best to `../alternatives`), updates
`Best.lean`, `STATUS.json`, runs `scripts/trusted-fingerprint --update`, rebuilds from scratch. See `../TRUSTED.md`.
