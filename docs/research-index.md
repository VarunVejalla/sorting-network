# Sorting-network research index

Local review: 2026-10-03. This index describes the checked-out sources, including
the local Paterson work, rather than just the upstream clone or September handoff.

## Objective and current result

The active target is a smaller upper bound on
`limsup_{n -> infinity} D(n)/log_2 n`, where `D(n)` is minimum binary-comparator
sorting-network depth. A constant for natural logarithms is the base-two constant
divided by `ln 2`.

The best complete bound currently formalized in this repository is
[`SortingDepth.minimum_depth_le`](../AKS/Bounds/Upper.lean):

```text
SortingDepth.minimum n <= 102 * 10^62 * Nat.clog 2 n.
```

`SortingDepth.minimum` defines `D(n)` as the minimum over sorting networks.
[`SortingDepth.limsup_minimum_div_logb_le`](../AKS/Bounds/Asymptotic.lean)
formally derives `limsup D(n)/log_2 n <= 102 * 10^62`, accounting for the
ceiling logarithm. The new executable `SortingDepth.upperNetwork` uses the
existing Seiferas correctness proof with `A = 8`, `gamma = 1/64`,
`epsilon = 1/57`, `nu = 41/50`. This improves the repository's previous
`141 * 10^62` coefficient by about 28%; it is a conservative parameter
improvement, not an improvement over published sorting bounds.

The original `network` and its old bound remain in `AKS/Seiferas.lean`.
No Paterson result is used in the new complete theorem's dependency chain. The smaller
numbers below are proved local bounds and arithmetic certificates; they do not
yet establish a new bound for `D(n)`.

## Proved milestones

| Component | Endpoint and source | Precise scope |
| --- | --- | --- |
| Restricted halvers | `Paterson.exists_paterson_halver_all_arities` in [PatersonTail](../AKS/Halver/PatersonTail.lean) | Every side arity, including zero; entropy-formula ceiling depth; existential and selected noncomputably. |
| Shared first-level network | `Paterson.exists_paterson_first_level_all_arities` in [PatersonJointTail](../AKS/Halver/PatersonJointTail.lean) | One network satisfies both required contracts with depth at most 263. Separate existence theorems would not suffice. |
| Five-level network depth | `Paterson.separatorNetwork_depth_le` in [PatersonConstruction](../AKS/Separator/PatersonConstruction.lean) | Depth at most 989 for every arity; correctness has a narrower domain. |
| Supported separator | `Paterson.separatorNetwork_certificate_of_dvd32` in [PatersonCertificate](../AKS/Separator/PatersonCertificate.lean) | For `32 ∣ n`: both extreme cohorts of size `k <= n/50` reach fringes of size `n/32`, with error at most `patersonTailError * k`, and the same network has depth at most 989. |
| Odd-block gadgets | `Paterson.oddInitialHalver_injective` and `Paterson.oddFinalHalver_injective` in [PatersonOdd](../AKS/Separator/PatersonOdd.lean) and [PatersonOddFinal](../AKS/Separator/PatersonOddFinal.lean) | Separate directional virtual-maximum and virtual-minimum constructions. They are not yet an arbitrary-arity five-level separator. |
| Numerical budgets | [PatersonNumerics](../AKS/Bags/PatersonNumerics.lean) | Six entropy bounds: 262, 263, 155, 167, 187, 217; first level shares the maximum, so total depth is 989. |
| Parameter repair | [PatersonParams](../AKS/Bags/PatersonParams.lean) | Literal reported choices fail two interior inequalities. `nu = 693/1000` repairs them with strict slack; ideal stage ratio is below `123/20`. These are scalar inequalities, not a bag invariant proof. |
| Trust audit | [PatersonAxioms](../AKS/Halver/PatersonAxioms.lean) | Compile-time axiom checks for the main local results: only `propext`, `Classical.choice`, `Quot.sound`. |

The supported contract is intentionally weaker than the existing
[`IsSeparator`](../AKS/Separator/Defs.lean): its cohort support `1/50` is smaller
than its fringe fraction `1/32`. The first-level large-cohort contract remains
available in `firstLevelNetwork_good`; it must be used by the future bag proof.

## Proof files by role

Read the endpoint for a milestone first, then follow its imports. The files
already separate the main arguments; there is no need to merge them into one
large proof or build optional certificate libraries to work on them.

| Layer | Files under `AKS/` |
| --- | --- |
| Interfaces and matching networks | `Halver/Paterson.lean` |
| Counting and trap correctness | `Halver/MatchingCount.lean`, `Halver/PatersonCorrectness.lean`, `Halver/PatersonExistence.lean` |
| Entropy and depth accounting | `Halver/PatersonEntropy.lean`, `Halver/PatersonMonotonicity.lean`, `Halver/PatersonDepthBridge.lean` |
| Witness reduction and uniform tail | `Halver/PatersonWitnesses.lean`, `Halver/PatersonCollapsedWitnesses.lean`, `Halver/PatersonTail.lean` |
| Simultaneous first-level guarantee | `Halver/PatersonSimultaneous.lean`, `Halver/PatersonJointTail.lean` |
| Ambient input and separator interface | `Separator/PatersonInjective.lean`, `Separator/PatersonDefs.lean`, `Separator/PatersonFamily.lean` |
| Network assembly and even-chunk induction | `Separator/PatersonConstruction.lean`, `Separator/PatersonNear.lean`, `Separator/PatersonStep.lean`, `Separator/PatersonPrefix.lean`, `Separator/PatersonCertificate.lean` |
| Odd-size directional bridges | `Separator/PatersonOdd.lean`, `Separator/PatersonFlip.lean`, `Separator/PatersonOddFinal.lean` |
| Scalar parameters and numerical certificates | `Bags/PatersonParams.lean`, `Bags/PatersonNumerics.lean` |
| Axiom assertions | `Halver/PatersonAxioms.lean` |

## Rounded Paterson implementation in progress

The first modular interior preservation theorem is implemented and checked:
[`Paterson.Bags.interior_step`](../AKS/Paterson/Interior.lean). It derives the
destination invariant from the old invariant, bag-local comparisons, child
subset routing, a parent-cohort filtering bound, and a parent first-stranger
bound. The two parent bounds are explicit hypotheses. This is not yet a
verified scheduler transition or a global sorting theorem.

New reusable pieces:

- [BagParams](../AKS/Paterson/BagParams.lean): rational interior constraints,
  capacity recurrence, and a working rounded instance with `mu = 199/10000`,
  `nu = 18/25`, minimum capacity `10^6`, and explicit rounding allowance.
  `roundedParams_fresh_source` checks that the rank-balance source estimate
  fits its fresh-error budget, allowing a floor loss of one in the selected
  cohort and a half-size rounding gain of one.
- [Rounding](../AKS/Paterson/Rounding.lean): even subtree totals, exact bag
  subtraction, `b - 8 < actual size < b + 2`, rounded fringe error below one,
  support slack, and coverage of the `n/32` fringe.
- [PatersonGood](../AKS/Separator/PatersonGood.lean): later comparator layers
  preserve the jointly selected first halver's large-cohort guarantee at
  every even whole-bag arity. This does not remove the divisibility restriction
  of the separate small-cohort five-level contract.
- [RankTransfer](../AKS/Paterson/RankTransfer.lean): both supported separator
  directions for injective selections of ambient ranks.
- [GoodRouting](../AKS/Paterson/GoodRouting.lean): both half-complement and
  middle first-stranger bounds under explicit input-rank balance.
  The estimate retains residual old strangers after imperfect fringe filtering.
- [Axiom assertions](../AKS/Bounds/Axioms.lean): the new global bound and
  modular Paterson endpoints.

Next obligations: derive input balance from actual placements and cold
storage, construct the rounded local
separator at all required even sizes, and discharge the two parent hypotheses
for the scheduler. Root/partial-level rules, root splitting, and global depth
accounting remain open. The looser working instance above does not certify
the older conditional `<6100` numerical target.

## Further conservative improvement via full-support Paterson halvers

There is also a route that does not require completing Paterson's refined bag
argument. The proved `exists_paterson_halver_all_arities` permits `alpha = 1`.
At full support its two-sided contract matches the ordinary halver interface,
after a rank/count conversion. Such halvers could replace the enormous-degree
MGG halvers while retaining the current Seiferas parameters and invariant.

This is not a drop-in change today: [`separatorNet`](../AKS/Separator/General.lean)
selects `halvers` directly, and [`separate`](../AKS/Bags/Network.lean) selects
`separatorNet` directly. A useful next refactor would parameterize those
constructions and the consuming proofs over a separator provider with explicit
correctness and depth fields. Then certify a full-support Paterson provider's
depth and assemble a new existential sorting theorem. Noncomputable selection
is sufficient for a bound on minimum depth, although it would not preserve the
existing executable construction without a separate search implementation.

This route sacrifices the level-dependent depth advantage behind the 989
budget. It offers a potentially much larger completed improvement over the MGG
baseline; its final numerical coefficient still needs to be proved. The
refined `<6100` target requires the additional work below.

## Remaining path to the refined Paterson bound

1. **Rounded local separator.** Specify and assemble the five-level network
   for the local sizes actually used by the bag scheduler. Prove the exact
   rounded fringes and supported-cohort bounds. The two odd-block lemmas provide
   ingredients, but merely composing them does not preserve the existing
   989-depth budget automatically.
2. **Bag transition and invariant.** Define the scheduler and prove capacity,
   higher-order stranger decay, and fresh first-order stranger control, using
   the small-cohort and large-cohort contracts where appropriate. Include cold
   storage, partial levels, root transitions, and integer rounding. The current
   Seiferas `Params` cannot be instantiated with these Paterson choices:
   `patersonNu_fails_current_hC3` records one concrete obstruction. The adjusted
   fringe parameter also needs an actual rounded implementation.
3. **Sorting and finishing.** Prove that the invariant implies rank-pure small
   subproblems and that cleanup sorts. Reuse generic network, scattering,
   monotonicity, restriction, and depth lemmas where their hypotheses match.
4. **Asymptotic stage accounting.** Prove a bound of the form
   `T(k) <= (123/20) * k + O(1)` with `k = log_2 N`, rather than rounding the
   stage coefficient itself to 7. With the 989 local budget, that rounding
   would cost 6923 instead of the candidate coefficient 6082.35.
5. **All n and limsup.** Combine sorting, stage depth, and boundary costs to
   obtain `D(n) <= C * log_2 n + o(log n)`. Proving this first on powers of two
   is enough if the existing wire-restriction theorem is used correctly:
   `ceil(log_2 n) = log_2 n + O(1)`. This does not remove the need to handle
   odd *local bag* sizes.

The verified arithmetic `989 * (123/20) = 6082.35 < 6100` motivates a completion
target. It is conditional on the missing global proof and its actual cost
accounting. For the limsup objective, finite small sizes and constant boundary
costs do not alter `C`; any nonconstant extra work must be bounded explicitly.

The minimum-depth and limsup infrastructure is now in `Bounds/Upper.lean` and
`Bounds/Asymptotic.lean`. A completed refined family can reuse that infrastructure.

For the refined track, the next mathematical task should be the rounded
separator interface consumed by one precise bag transition. Validate that
interface before building the entire scheduler, so the existing local proof
and the global invariant agree. For a further complete improvement, consider
the full-support provider refactor above.

## Build and audit

Pinned toolchain: `leanprover/lean4:v4.29.0-rc4`. Use the checked-in
`lake-manifest.json`; an audit does not require updating Mathlib.

```sh
# Independent milestone checks (each builds its own dependency closure).
lake build AKS.Halver.PatersonTail
lake build AKS.Halver.PatersonJointTail
lake build AKS.Separator.PatersonCertificate
lake build AKS.Separator.PatersonOddFinal
lake build AKS.Halver.PatersonAxioms
lake build AKS.Paterson.Interior
lake build AKS.Paterson.GoodRouting
lake build AKS.Bounds.Axioms

# Full core, including the existing sorting theorem and local research.
lake build AKS

# Portable source audits; run from the repository root.
python scripts/sorry-gate
python scripts/sorries
```

The full `lake build AKS` passed with the new minimum-depth/limsup theorem
and rounded Paterson modules included in the root build.
The new endpoint axiom assertions permit only `propext`, `Classical.choice`,
and `Quot.sound`. Source audits found no `sorry`, `#exit`,
or declared `axiom` in the protected files. The `Random/` native-evaluation
path is separate from the AKS and Paterson proofs. The audit now reads UTF-8 on
Windows and permits the classical minimum-depth definition in the exact
`Bounds/Upper.lean` file, alongside the two named analytic Paterson files in
`Bags/`. Both `network` and `SortingDepth.upperNetwork` are computable definitions.

## Documents and history

- [Paterson interface audit](paterson-interface.md): detailed local theorem
  contracts, corrected parameter arithmetic, and remaining mathematical issues.
- [Local Paterson paper](paterson.pdf): primary mathematical source for this
  track; verify claims against the relevant sections before extending the proof.
- [September handoff entry point](../AKS_CODEX_HANDOFF_2026-09-27/README_START_HERE.md)
  and [historical proof ledger](../AKS_CODEX_HANDOFF_2026-09-27/PROOF_STATUS_LEDGER.md):
  preserved background. Their claim that Paterson is not formalized predates
  the current local partial formalization; the final sorting result is still open.
- [Current research state from the handoff](../AKS_CODEX_HANDOFF_2026-09-27/CURRENT_RESEARCH_STATE.md):
  Avenue 2 and `GoodSplitter` ideas remain research leads; candidate constants
  from older handoffs are not proved.
- [Bag-tree notes](bags.md), [module guide](modules.md), and the remaining
  upstream `docs/` describe inherited infrastructure. Some progress/trust
  descriptions are historical; use Lean declarations and current axiom checks
  as the evidence for proof status. `docs/old/` is historical planning material.
