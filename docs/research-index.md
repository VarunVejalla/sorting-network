# Sorting-network research index

Local review: 2026-10-03. This index describes the checked-out sources, including
the local Paterson work, rather than just the upstream clone or September handoff.

## Objective and current result

The active target is a smaller upper bound on
`limsup_{n -> infinity} D(n)/log_2 n`, where `D(n)` is minimum binary-comparator
sorting-network depth. A constant for natural logarithms is the base-two constant
divided by `ln 2`.

The best complete endpoints are in
[Bounds/PatersonTight](../AKS/Bounds/PatersonTight.lean):

```text
minimum_depth_le_6991: D(n) <= 6991 * Nat.clog 2 n (every n).
minimum_depth_double_le: 2*D(n) <= 13981 * Nat.clog 2 n + 13979.
limsup_minimum_div_logb_le_6990_5: limsup D(n)/log_2 n <= 13981/2.
eventually_minimum_depth_le_7000_logb: eventually D(n) <= 7000 * log_2 n.
```

`minimum_depth_le_7000_logb` gives the explicit sufficient condition
`n >= 2` and `log_2 n >= 1472`. The networks are selected classically.
All correctness and depth proofs are kernel checked. The older complete
million-coefficient theorem remains in [Bounds/Paterson](../AKS/Bounds/Paterson.lean).
The inherited executable networks remain available. This is an improvement to
this repository's formal bound, not to the best published sorting bound.

## Lower-bound endpoint

The independent Kahale formalization proves
`liminf D(n)/log_2 n >= 1/(1-log_2(phi))`, approximately `3.270559454`,
with `phi = (1+sqrt(5))/2`. It includes the actual comparator execution,
greedy depth scheduling, and analytic limit. The finite inequality is
`n * fib(D(n)+1) <= 2^(D(n)+1) * (D(n)+1)^2`.

Entry point: `lake build AKS.Kahale`. See
[the detailed proof map](kahale-lower-bound.md) and
[the asymptotic endpoints](../AKS/Bounds/KahaleAsymptotic.lean).
This reproduces the published lower bound; stronger constants remain research.

## Proved milestones

| Component | Endpoint and source | Precise scope |
| --- | --- | --- |
| Restricted halvers | `Paterson.exists_paterson_halver_all_arities` in [PatersonTail](../AKS/Halver/PatersonTail.lean) | Every side arity, including zero; entropy-formula ceiling depth; existential and selected noncomputably. |
| Full-support provider and complete sorting bound | [PatersonFull](../AKS/Halver/PatersonFull.lean), [PatersonProvider](../AKS/Separator/PatersonProvider.lean), [Bounds/Paterson](../AKS/Bounds/Paterson.lean) | Full halvers at every even arity, the complete scheduler, all-n restriction, and a limsup coefficient at most `10^6`. |
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

## Completed rounded Paterson implementation

The active candidate uses `A = 19/4`, `mu = 199/10000`, `delta = 1/57`,
`nu = 707/1000`, minimum capacity `300000`, and rounding allowance `10`.
[FastParams](../AKS/Paterson/FastParams.lean) checks every interior parameter
constraint and `(2*A)^2 * nu^13 < 1`.
The older `roundedParams` and ideal approximately-6100 certificates are
historical candidate arithmetic; the current budget includes root sorting.

### Checked concrete components

| Component | Files | What is proved |
| --- | --- | --- |
| Parallel separator stage | [BagSeparator](../AKS/Paterson/BagSeparator.lean), [Stage](../AKS/Paterson/Stage.lean) | Actual scattered bag networks, depth at most 989, local execution identities, supported old-stranger filtering, and a routed placement for specified fringes. |
| Fresh-stranger source | [Fresh](../AKS/Paterson/Fresh.lean), [Balance](../AKS/Paterson/Balance.lean) | Actual first-halver execution estimates, finite disjoint-cohort counting, rounded fresh-cost arithmetic, and a capacity-based sufficient condition for rank balance. |
| Concrete interior preservation | [Transition](../AKS/Paterson/Transition.lean) | `interior_parallel_step` discharges the former abstract separator-filter and first-stranger hypotheses. Actual size, capacity, fringe, parity, and `ChildBalance` hypotheses remain explicit. |
| Descendant contamination | [Subtree](../AKS/Paterson/Subtree.lean) | Geometric subtree intrusion bound for the new Paterson parameters, conditional on the old invariant and parity emptiness. |
| Rounded size recipe | [Schedule](../AKS/Paterson/Schedule.lean), [BoundarySchedule](../AKS/Paterson/BoundarySchedule.lean), [ClippedRouting](../AKS/Paterson/ClippedRouting.lean) | 32-lattice subtree totals, size bounds, fringe coverage, and exact routing counts at full, clipped, and empty levels. |
| Explicit cold storage and one-tree allocation | [ColdStorage](../AKS/Paterson/ColdStorage.lean), [ColdAllocation](../AKS/Paterson/ColdAllocation.lean), [AllocationSchedule](../AKS/Paterson/AllocationSchedule.lean), [AllocationPreservation](../AKS/Paterson/AllocationPreservation.lean), [AllocationInitial](../AKS/Paterson/AllocationInitial.lean) | Computable ownership including cold storage, centered initialization and feeds, actual routing, and `allocationRun_invariant`. Every bag and cold-storage cardinality is checked while the root capacity stays above the threshold. This is positional allocation, not sorting correctness. |
| Storage-aware comparison and routing | [StoredStage](../AKS/Paterson/StoredStage.lean), [StoredRouting](../AKS/Paterson/StoredRouting.lean), [StoredSizes](../AKS/Paterson/StoredSizes.lean) | Parallel execution for arbitrary bag-local networks, depth bounds, unchanged cold inputs, nonroot register flow, root returns, and actual output cardinalities. |
| Actual full-bag rank balance | [AllocatedSubtree](../AKS/Paterson/AllocatedSubtree.lean), [RankCohorts](../AKS/Paterson/RankCohorts.lean), [AllocationBounds](../AKS/Paterson/AllocationBounds.lean), [AllocatedBalance](../AKS/Paterson/AllocatedBalance.lean) | Actual subtree totals and parent/sibling conservation, native rank counts, and `allocated_full_cohort_balance` from the old stranger invariant. Coherent rounding cancels in the sibling deficit. |
| Actual partial-bag rank budgets | [PartialBoundary](../AKS/Paterson/PartialBoundary.lean), [AllocatedPartialBalance](../AKS/Paterson/AllocatedPartialBalance.lean) | Available cohort counts, actual half-size upper bounds, `allocated_partial_fresh_budget`, and separator support when the outgoing middle is nonempty. These estimates are now assembled by `ScheduledPartialTransition`. |
| Root purity and sort cost | [Root](../AKS/Paterson/Root.lean), [TightDepth](../AKS/Bitonic/TightDepth.lean) | At a sufficiently small root capacity, the invariant implies zero deepest strangers from level six. Given explicit region size bounds, the top region has fewer than `2^33` wires and its scattered bitonic sort costs at most 561. No forest splitting correctness theorem yet. |
| Arbitrary virtual padding | [Padding](../AKS/Paterson/Padding.lean) | Both directional supported contracts survive restriction with virtual maxima/minima, without additive error. |
| Concrete partial-bag gadget | [PatersonRefinement](../AKS/Separator/PatersonRefinement.lean), [PatersonPartial](../AKS/Separator/PatersonPartial.lean), [PatersonHalfCounting](../AKS/Separator/PatersonHalfCounting.lean), [PatersonPartialCertificate](../AKS/Separator/PatersonPartialCertificate.lean) | Four refinement levels cost 726; the actual-size first split and padded half refinements cost 989. `partialNetwork_supported` proves both whole-network directional supported contracts with explicit actual-size and virtual-size support budgets. The first split retains its large-cohort guarantee. The mixed boundary invariant is checked in `ScheduledInvariant`. |
| Proposed operation counts | [Accounting](../AKS/Paterson/Accounting.lean) | `T(k) = 13*ceil(k/2)` overcomes initial capacity growth. The proposed cost `989*T(k) + 561*k` is at most `7000*k` for `k >= 613`. These are arithmetic theorems, not sorting theorems. |
| Kernel audit | [Axioms](../AKS/Paterson/Axioms.lean), [StorageAxioms](../AKS/Paterson/StorageAxioms.lean) | Guarded axiom checks on transition, padding, partial certificates, allocation runs, actual rank balance, root bounds, and accounting. Only `propext`, `Classical.choice`, and `Quot.sound` appear. |

### Remaining global obligations

The comparison-stage obligation is now closed: `scheduledCompare_preserves`
in [ScheduledInvariant](../AKS/Paterson/ScheduledInvariant.lean) handles full,
partial, root, inactive, and empty-middle cases. The selected local networks and
actual stage have depth at most 989.
[PatersonRun](../AKS/Separator/PatersonRun.lean) constructs the repeated network
and proves its invariant and depth at most `989*t` within the root window.

Root split groundwork is also checked:

- [RootAllocationBudget](../AKS/Paterson/RootAllocationBudget.lean): the actual
  upper region has fewer than `2^33` registers in the root split window.
- [UpperRegionCounts](../AKS/Paterson/UpperRegionCounts.lean) and
  [DescendantRegisters](../AKS/Paterson/DescendantRegisters.lean): the upper
  and deep regions partition all registers, with upper size `N - 64*T6`.
- [DeepErrors](../AKS/Paterson/DeepErrors.lean),
  [DeepPurity](../AKS/Paterson/DeepPurity.lean), and
  [DeepPrefixAgreement](../AKS/Paterson/DeepPrefixAgreement.lean): global deep
  error bounds, exact half purity, and actual/assigned prefix agreement outside errors.
- [DeepPrefix](../AKS/Paterson/DeepPrefix.lean): exact assigned deep prefix counts.
- [PrefixDiscrepancy](../AKS/Paterson/PrefixDiscrepancy.lean): generic remaining
  prefix discrepancy and sorted-bin wrong-rank bounds.

### Completed global proof chain

| Obligation | Checked endpoint |
| --- | --- |
| Exact sorted-bin coordinates and errors | [RootPrefixCoordinates](../AKS/Paterson/RootPrefixCoordinates.lean), [RootSortedBins](../AKS/Paterson/RootSortedBins.lean) |
| Actual root rebuild, cardinalities and stranger budgets | `allocatedRebuild_preserves` in [RootRebuildInvariant](../AKS/Paterson/RootRebuildInvariant.lean) |
| Independent halves, actual child allocation and invariant | `scheduledChild_allocation`, `scheduledChild_invariant` in [ChildInvariant](../AKS/Paterson/ChildInvariant.lean) |
| Phase windows, fuel and well-founded recursion | [ForestPhase](../AKS/Paterson/ForestPhase.lean), [PatersonForest](../AKS/Separator/PatersonForest.lean) |
| Actual recursive network depth | `forestNetwork_depth_le` in [PatersonForestDepth](../AKS/Separator/PatersonForestDepth.lean) |
| Input-independent final rank arrangement | `preliminaryNetwork_independent` in [PatersonForestRanks](../AKS/Separator/PatersonForestRanks.lean) |
| Fixed permutation correction in depth k | `exists_known_permutation_correction` in [KnownPermutation](../AKS/Sort/KnownPermutation.lean) |
| Full sorting correctness and doubled depth bound | `correctedForest_sorts`, `correctedForest_depth_double` in [PatersonForestSorts](../AKS/Separator/PatersonForestSorts.lean) |
| All-n minimum depth and limsup | [PatersonTight](../AKS/Bounds/PatersonTight.lean) |
| Complete theorem axiom audit | [PatersonTightAxioms](../AKS/Bounds/PatersonTightAxioms.lean) |

The final coefficient is `989*(13/2) + 561 + 1 = 6990.5`. The doubled
finite-size budget is `13981*k + 13979`. All global obligations needed for
the 7000 target are discharged; reducing the coefficient further is new work.
The older proposed-count arithmetic above is retained as historical context.

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
lake build AKS.Paterson.Transition
lake build AKS.Separator.PatersonPartial
lake build AKS.Paterson.Axioms
lake build AKS.Paterson.GoodRouting
lake build AKS.Paterson.AllocatedPartialBalance
lake build AKS.Paterson.StorageAxioms
lake build AKS.Separator.PatersonRun
lake build AKS.Paterson.CoarsePrefixCount
lake build AKS.Paterson.ForestAxioms
lake build AKS.Bounds.Axioms
lake build AKS.Bounds.PatersonAxioms
lake build AKS.Bounds.PatersonTightAxioms

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
Windows and permits the selected refined network in `Bounds/PatersonTight.lean`,
the classical minimum-depth definition in the exact
`Bounds/Upper.lean` file and selected Paterson network in `Bounds/Paterson.lean`,
alongside the two named analytic Paterson files in `Bags/`. Both `network`
and `SortingDepth.upperNetwork` remain computable definitions.

## Current research directions (2026-10-03, unverified unless noted)

- Paterson tuning is exhausted in-family. A full-floor grid search over
  `(A,μ,δ,δᵢ,ν,mincap)` encoding every known floor (bag parameters, lattice
  fringe, cohort corners, rebuild lock, `νA ≥ 1`, ceiling margins) found 775
  fully-feasible points, none with stage ratio `m ≤ 12`; the checked-in
  parameters are the in-family optimum at `6990.5`. Scripts
  (`scripts/paterson_search.py`, `scripts/paterson_fullfloor_search.py`) are
  untracked experiment tooling, not proof. Earlier sub-6990 search hits
  (`6463`, `6894.5`) were retracted as infeasible mirages missing hidden
  floors; the `tune-6463` branch was deleted and `main` rebuilt green.
- Chvátal 1830 track (Phase 0 + Phase 1 §3 kernel-checked). Reference
  `docs/dcs-tr-294.pdf` (untracked; Rutgers DCS-TR-294). [Chvatal/DepthSkeleton](../AKS/Chvatal/DepthSkeleton.lean)
  proves the §7 depth accounting (`totalDepth_eq`: `6320 + (3d-21)·3660 + 903`
  at `d = clog₂ N - 66`) and the §7 numeric checks (4.1), (4.3), (4.4),
  (4.5), (7.1), (7.2), `δF ≤ 1/25`, driven by one sharp bound `ln 2 < 0.7`
  from the checked-in dyadic enclosure. [Chvatal/SkeletonAxioms](../AKS/Chvatal/SkeletonAxioms.lean)
  audits the axiom footprint (standard axioms only). Phase 1 §3 scaffolding
  is kernel-checked: [Chvatal/Tree](../AKS/Chvatal/Tree.lean) (`br`-ary bags,
  Native/Strange), [Chvatal/Scheduler](../AKS/Chvatal/Scheduler.lean)
  (capacity / `LevelSchedule` / allocation), and
  [Chvatal/SchedulerLemmas](../AKS/Chvatal/SchedulerLemmas.lean) (Lemma 3.1
  under the global mass identity; Lemma 3.2 under an explicit snap hypothesis).
  [Chvatal/OutsiderInvariant](../AKS/Chvatal/OutsiderInvariant.lean) states
  proposition `P`, separator-quality hypotheses (4.1)–(4.5), and Lemma 4.5
  purity.   [Chvatal/SeparatorContract](../AKS/Chvatal/SeparatorContract.lean)
  packages `StageCounts` / `StageModel` and the Lemma 4.3–4.4 source
  interfaces. [Chvatal/OutsiderLemmas](../AKS/Chvatal/OutsiderLemmas.lean)
  gives the algebraic cores of Lemmas 4.1–4.4 under those hypotheses
  (kernel-checked).   [Chvatal/OutsiderInduction](../AKS/Chvatal/OutsiderInduction.lean)
  closes the §4 inductive algebra: `OutsiderBoundLe` at `t` + `SeparatorConds`
  + `StageModel` ⇒ `OutsiderBoundLe` at `t+1`, with trajectory induction and
  purity under a strict capacity envelope (kernel-checked).
  [Chvatal/StageDynamics](../AKS/Chvatal/StageDynamics.lean) discharges
  `StageModel` from a thinner combinatorial `StageDynamics` contract (Lemma
  4.2 parts, source splits, fringe/child routing; kernel-checked via
  `stageModel_of_dynamics` / `outsiderBound_step_of_dynamics`).
  [Chvatal/PlacementStep](../AKS/Chvatal/PlacementStep.lean) fills the
  stranger source-split from a concrete parent-send ∪ children-send Finset
  cover and assembles `StageDynamics` from `StageRouting` (kernel-checked).
  [Chvatal/RoutingFromP](../AKS/Chvatal/RoutingFromP.lean) discharges
  parent-outsider, intrusion, and fringe bounds from `OutsiderBoundLe` +
  `LocalSeparatorQuality`. [Chvatal/StageKernel](../AKS/Chvatal/StageKernel.lean)
  collapses sibling mass to its Lemma 4.2 closed form and closes the §4
  inductive chain under a minimal `StageKernel`
  (`outsiderBound_step_of_kernel` / `outsiderBound_induction_of_kernel`;
  kernel-checked). [Chvatal/ChildSend](../AKS/Chvatal/ChildSend.lean) covers
  `fromChildren` by the concrete send-up `fromChildren ∩ child.regs`
  (`childSendCover_of_support`). Order-0 size bounds discharge from schedule
  card (`|sendUp| ≤ |regs|/Q`) plus fair density / perm-mono
  (`childSendSize_of_card_fair`) then `P`; order-`r` (`r+1 ≤ d`) from `P` +
  bridge (`StageKernel.ofChildSend`; kernel-checked); top order `r = d`
  remains a one-line residual. Remaining kernel obligations: schedule slack,
  Lemma 4.1 count identities, bad-send/fringe Finset routing, level-0,
  schedule card / fair-density / perm-bridge from the placement networks, and
  concrete separators. Remaining Phase 1: discharge those from the scheduler /
  placement networks, and Lemma 3.2 snap-from-envelope. Then Phase 2 (§5–6
  scramble existence, Thm 5.1), Phase 3 (§7 instantiation +
  `D(N) ≤ 1830·lg N − 58657` endpoints). The (4.2) numeric assembly remains
  deferred to the separator/outsider proofs.

## Documents and history

- [Paterson interface audit](paterson-interface.md): detailed local theorem
  contracts, corrected parameter arithmetic, and remaining mathematical issues.
- [Local Paterson paper](paterson.pdf): primary mathematical source for this
  track; verify claims against the relevant sections before extending the proof.
- [September handoff entry point](../AKS_CODEX_HANDOFF_2026-09-27/README_START_HERE.md)
  and [historical proof ledger](../AKS_CODEX_HANDOFF_2026-09-27/PROOF_STATUS_LEDGER.md):
  preserved background. Their claim that Paterson is not formalized predates
  the completed rounded forest formalization and its final sorting theorem.
- [Current research state from the handoff](../AKS_CODEX_HANDOFF_2026-09-27/CURRENT_RESEARCH_STATE.md):
  Avenue 2 and `GoodSplitter` ideas remain research leads; candidate constants
  from older handoffs are not proved.
- [Bag-tree notes](bags.md), [module guide](modules.md), and the remaining
  upstream `docs/` describe inherited infrastructure. Some progress/trust
  descriptions are historical; use Lean declarations and current axiom checks
  as the evidence for proof status. `docs/old/` is historical planning material.
