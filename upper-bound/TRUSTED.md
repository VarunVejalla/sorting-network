# Trust model of the upper-bound results

What does "limsup D(n)/log₂ n ≤ C is verified" mean here, and what must a reviewer read to believe it?

## The claim

`UpperBoundContrib.BoundSpec C` (`contributions/UpperBoundContrib/Spec.lean`):

```lean
def BoundSpec (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (SortingDepth.minimum n : ℝ) ≤ (C + ε) * Real.logb 2 (n : ℝ)
```

`BoundSpec.limsup_le` derives `limsup D(n)/log₂ n ≤ C` from it. The eventual pointwise form is the primary
statement because in `ℝ` the `limsup` of a sequence that is not bounded above is the junk value `0`
(`sInf ∅ = 0`): `limsup ≤ C` alone, without a boundedness argument, would be vacuous for an unbounded
sequence. `D(n)` is genuinely O(log n), so the limsup form is also true, but only the pointwise form certifies it.

## What a reader must trust (the trusted base)

These files fix the *meaning* of the statement; a proof of `BoundSpec C` is meaningful iff they are
the intended definitions. They are fingerprinted (`TRUSTED_FILES`, `TRUSTED.sha256`, checked by
`scripts/trusted-fingerprint --check` in CI), and covered by `.github/CODEOWNERS`.

| file | what it defines |
|---|---|
| `best/AKS/Sort/Defs.lean` | `Comparator` (i < j, min goes to i), `Comparator.apply`, `ComparatorNetwork`, `exec` |
| `best/AKS/Sort/Depth.lean` | `depthStep`, `ComparatorNetwork.depth` (critical-path depth) |
| `best/AKS/Sort/Monotone.lean` | `ComparatorNetwork.Sorts` (sorts every input; definition at line ~43; the rest of the file is lemmas) |
| `best/AKS/Bounds/Minimum.lean` | `SortingDepth.minimum` = least depth of a sorting network on `n` wires |
| `contributions/UpperBoundContrib/Spec.lean` | `BoundSpec` and `BoundSpec.limsup_le` |
| `contributions/UpperBoundContrib/Best.lean` | the accepted best constant `currentBest` |
| `contributions/UpperBoundContrib/Axioms.lean` | the pin `example : BoundSpec claimed := candidate_bound` and the axiom guards |
| `contributions/UpperBoundGate/Improvement.lean` | the strict-improvement gate |
| lakefiles, `lake-manifest.json`, `lean-toolchain` | toolchain and dependency pins (Mathlib revision) |
| `scripts/trusted-fingerprint`, `scripts/check-*`, `.github/workflows/upper-bound-contributions.yml` | the checks themselves |

Beyond these files you trust Lean's kernel and Mathlib's definitions of `Fin`, `LinearOrder`, `Real.logb`,
`Filter.atTop`. Nothing else in `best/AKS/**` needs to be read: any proof of `BoundSpec C` that type-checks
against these definitions with only the standard axioms is a proof of the stated mathematical claim.

## What the checks establish

For a contribution `UpperBoundContrib/Candidate.lean`:

1. `scripts/trusted-fingerprint --check`: the files above are byte-identical (modulo line endings) to the
   recorded fingerprint. A contribution cannot silently redefine "sorts", "depth" or "minimum".
2. `scripts/check-status`: `STATUS.json`, `Best.lean` and the headline theorem file agree on the accepted constant.
3. `lake build` and `lake build UpperBoundContrib.Axioms` in `contributions/`: the candidate type-checks;
   the pin `example : UpperBoundContrib.BoundSpec UpperBoundContrib.claimed := UpperBoundContrib.candidate_bound`
   forces the *exact* trusted type; `#guard_msgs` forces the dependency set to be
   `propext, Classical.choice, Quot.sound` (no `sorry`, `native_decide`, new axioms).
4. Informational: `lake build UpperBoundGate` compiles iff `claimed < currentBest` (strict improvement).

Negative tests that were run when this was added: a candidate of the wrong type, and a `sorry` candidate
claiming `1000`, are both rejected by step 3.

## What the checks do NOT establish (residual risks)

* **The workflow can be edited by a pull request.** CI cannot defend itself: enable branch protection with
  "Require review from Code Owners" so edits to the trusted base need the owner. Without that, the
  fingerprint is only a tripwire for honest mistakes.
* **Elaboration-time tricks.** Lean macros, elaborators, `initialize` or `#eval` in a candidate run during the
  build and can in principle interfere with `#print axioms`/`#guard_msgs` or the environment. The robust tool is
  `leanprover/comparator` (export the environment with `lean4export`, replay it with an independent kernel
  such as `nanoda`, in a `landrun` sandbox, against a Mathlib-only Challenge file). It is used for the
  legacy package (`.github/workflows/comparator.yml`). A draft limsup Challenge is in
  `contributions/Challenge.lean` + `challenge.json` (see `contributions/README.md`); it has not been run with comparator in this repository.
* **Mathlib/Lean soundness bugs** are out of scope.
* **Fidelity of the definitions.** A reviewer must still read the ~100 lines in the table above and confirm they
  match "comparator network", "depth" and "sorting network" as intended.

## Promotion (owner procedure)

When a better package is promoted to `upper-bound/best`: (1) rebuild from scratch and run the package guard;
(2) update `currentBest` in `Best.lean` and `STATUS.json` together; (3) `python3 scripts/trusted-fingerprint --update`
and review the diff of `TRUSTED.sha256`; (4) `python3 scripts/check-status`; (5) move the previous best to
`alternatives/` and keep it building.
