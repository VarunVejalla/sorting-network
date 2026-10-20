# Sorting-network research index

## Current package layout (2026-10-19)

- `upper-bound/best`: current endpoint, coefficient 789.75 (UB-31; `D(n) ≤ 789.75 lg n + 3159`
  for `n ≥ 16^12`, `limsup ≤ 789.75`; headline `AKS/Bounds/Sub800Final.lean`, modules
  `AKS/Sub800/`, paper proof `upper-bound/best/notes/sub800/R1-PROOF.md`). It keeps the 1419
  Chvátal modules it builds on (math notes in `upper-bound/best/notes/two-round/`).
  The previous endpoint (1419) is `upper-bound/alternatives/chvatal-1419`, the one before (1770)
  `upper-bound/alternatives/chvatal-1770`; parked and ruled-out ideas are in `upper-bound/backlog/`.
- `lower-bound/best`: Kahale endpoint, coefficient approximately 3.270559454.
  Its real-valued liminf boundedness premise uses the legacy upper package;
  the finite Kahale inequality itself is independent of that construction.
- `upper-bound/alternatives/legacy`: Paterson all-n 6991 / limsup 6990.5 and
  older Seiferas/MGG infrastructure.
- `upper-bound/experiments`: candidate Chvátal improvements and optional
  certificate/expander research.
- `lower-bound/experiments`: retained research beyond the Kahale endpoint.
- `research/limit-existence`: conditional convergence and repair research.
- `archive/handoffs`: preserved historical handoffs; these are not current status.

Build packages separately; their AKS module names overlap. See the root README
and each package README. The completed migration checks are summarized in
[the reorganization verification](reorganization-verification.md). The older proof map below remains historical context;
its dated constants and inline command paths may describe earlier layouts.

### Active upper research

The earlier Chvatal fringe-repair experiments below are historical context for
the 1770-era design; the promoted endpoint is now 789.75 (UB-31, previously 1419). The current high-upside
structural lead is multiway partitioning and its missing global composition
argument, tracked below.

The older global-cost audit contains an 86-layer fringe-funnel candidate and
a 107-layer central bulk-repair target, but neither has its universal proof.
These remain experimental context, not the route underlying 1419; see the
[global cost audit](../upper-bound/experiments/global-cost-audit/README.md) and
[the verified endpoint](../upper-bound/best/README.md).

The latest audit adds a joint-column fringe exponential-tail argument and
explicit bulk localization with a 631-layer band-cut repair baseline. The
universal fringe profile count and the reduction of bulk repair to 107 layers
remain open. See [central bulk feasibility](../upper-bound/experiments/global-cost-audit/central-bulk-feasibility.md)
and [the joint fringe tail](../upper-bound/experiments/global-cost-audit/funnel-joint-tail.md).

The active structural route is now a direct jointly designed multiway
partitioner with all-cut and fringe guarantees, tracked in the [direct
multiway research sequence](../upper-bound/experiments/direct-multiway/RESEARCH-SEQUENCE.md).
Its first gate is an explicit contract-to-invariant table and a priced finite
construction. The older Ajtai–Komlós–Szemerédi row-scramble branch has
all-cuts aggregate screens, but no composable repair; its exceptional-column
tail audit is parked at [the backlog note](../upper-bound/backlog/ajtai-row-scramble-tail.md).

The [1419 cost audit](upper-bound-1419-cost-audit.md) identifies the 2838-layer
ordinary node as the repeated leading cost and the hand-certified two-tail
Variant B as a possible route to 1354.5; its lower window and exact-mass
first-round proof are not yet formalized. It also compares the AKS core against
the promoted node interface.

The tapered branch now has an initialized count/ownership schedule in
[`FrontierIntegerSchedule.lean`](../upper-bound/experiments/tapered/FrontierIntegerSchedule.lean).
For every `d >= 14`, its actual register partitions preserve even counts,
active-band support and the shape-specific 69-wire discrepancy through every
six-stage segment and the terminal meeting at `3*d - 23`. Its bootstrap
preserves static address debt instead of using the old uniform reset. See the
[UB-23 checkpoint](../upper-bound/experiments/tapered/UB-23-FLOW-FAMILY.md)
for verification and the remaining provider/rank obligations. This is not a
new sorting-depth bound.

UB-24 now has an exact threshold recurrence on that actual execution in
`RaggedPrefixRoute.lean`, shared endpoint-deficit identities, threshold cohort
conservation, and a retirement capacity gate. Cumulative rounding now connects
to a local top-advance construction: exact native complements of even stored
subtree masses form an allowed retiring split when they conserve the source
count. The global schedule still does not supply those coordinated subtree
masses. See the [UB-24 checkpoint](../upper-bound/experiments/tapered/UB-24-RANK-PROFILE.md).
The global signed rank invariant remains open.

## Historical proof map

Local review: 2026-10-09. This index describes the checked-out sources, including
the local Paterson work, rather than just the upstream clone or September handoff.

## Objective and current result

The active target is a smaller upper bound on
`limsup_{n -> infinity} D(n)/log_2 n`, where `D(n)` is minimum binary-comparator
sorting-network depth. A constant for natural logarithms is the base-two constant
divided by `ln 2`.

The completed all-input-size Paterson endpoints are in
[Bounds/PatersonTight](../upper-bound/alternatives/legacy/AKS/Bounds/PatersonTight.lean):

```text
minimum_depth_le_6991: D(n) <= 6991 * Nat.clog 2 n (every n).
minimum_depth_double_le: 2*D(n) <= 13981 * Nat.clog 2 n + 13979.
limsup_minimum_div_logb_le_6990_5: limsup D(n)/log_2 n <= 13981/2.
eventually_minimum_depth_le_7000_logb: eventually D(n) <= 7000 * log_2 n.
```

`minimum_depth_le_7000_logb` gives the explicit sufficient condition
`n >= 2` and `log_2 n >= 1472`. The networks are selected classically.
All correctness and depth proofs are kernel checked. The older complete
million-coefficient theorem remains in [Bounds/Paterson](../upper-bound/alternatives/legacy/AKS/Bounds/Paterson.lean).
The inherited executable networks remain available. This is an improvement to
this repository's formal bound, not to the best published sorting bound.

**Chvátal-form 1830 endpoint (complete, 2026-10-07).** The folder
[`chvatal-1830/`](../upper-bound/best/README.md) is a self-contained Lean package proving, with only
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

```text
SortingDepth.minimum_depth_le_1830_logb:  for n ≥ 64^7,
  D(n) ≤ 1830 * log₂ n − 58657
SortingDepth.limsup_minimum_div_logb_le_1830:
  limsup D(n)/log₂ n ≤ 1830
```

(`chvatal-1830/AKS/Bounds/Chvatal1830Final.lean`). The witness networks are full-wire Batcher for
`7 ≤ ⌈log₆₄ n⌉ ≤ 13` and Chvátal's network `Chvatal.chvatal_sorter_exists` beyond (depth
`≤ totalDepth d = 6320 + (3d−21)·3660 + 903` on `64^d` wires, `d ≥ 14`), restricted to `n` wires. It
follows DCS-TR-294 (`dcs-tr-294.pdf`). The Chvátal code is no longer part of the main `AKS`
library; its shared basics (`Sort`, `Bitonic`, `Halver`, `Misc`) are copied into the folder.
The repaired simplification passed its full build and headline axiom guards on 2026-10-08;
see [BUILD_STATUS](../upper-bound/best/BUILD_STATUS.md). Before
this, the best complete upper bound was Paterson's `6991·⌈log₂ n⌉` (above).

## Lower-bound endpoint

The independent Kahale formalization proves
`liminf D(n)/log_2 n >= 1/(1-log_2(phi))`, approximately `3.270559454`,
with `phi = (1+sqrt(5))/2`. It includes the actual comparator execution,
greedy depth scheduling, and analytic limit. The finite inequality is
`n * fib(D(n)+1) <= 2^(D(n)+1) * (D(n)+1)^2`.

Entry point: `lake build AKS.Kahale`. See
[the detailed proof map](kahale-lower-bound.md) and
[the asymptotic endpoints](../lower-bound/best/AKS/Bounds/KahaleAsymptotic.lean).
This reproduces the published lower bound; stronger constants remain research.

## Proved milestones

| Component | Endpoint and source | Precise scope |
| --- | --- | --- |
| Restricted halvers | `Paterson.exists_paterson_halver_all_arities` in [PatersonTail](../upper-bound/alternatives/legacy/AKS/Halver/PatersonTail.lean) | Every side arity, including zero; entropy-formula ceiling depth; existential and selected noncomputably. |
| Full-support provider and complete sorting bound | [PatersonFull](../upper-bound/alternatives/legacy/AKS/Halver/PatersonFull.lean), [PatersonProvider](../upper-bound/alternatives/legacy/AKS/Separator/PatersonProvider.lean), [Bounds/Paterson](../upper-bound/alternatives/legacy/AKS/Bounds/Paterson.lean) | Full halvers at every even arity, the complete scheduler, all-n restriction, and a limsup coefficient at most `10^6`. |
| Shared first-level network | `Paterson.exists_paterson_first_level_all_arities` in [PatersonJointTail](../upper-bound/alternatives/legacy/AKS/Halver/PatersonJointTail.lean) | One network satisfies both required contracts with depth at most 263. Separate existence theorems would not suffice. |
| Five-level network depth | `Paterson.separatorNetwork_depth_le` in [PatersonConstruction](../upper-bound/alternatives/legacy/AKS/Separator/PatersonConstruction.lean) | Depth at most 989 for every arity; correctness has a narrower domain. |
| Supported separator | `Paterson.separatorNetwork_certificate_of_dvd32` in [PatersonCertificate](../upper-bound/alternatives/legacy/AKS/Separator/PatersonCertificate.lean) | For `32 ∣ n`: both extreme cohorts of size `k <= n/50` reach fringes of size `n/32`, with error at most `patersonTailError * k`, and the same network has depth at most 989. |
| Odd-block gadgets | `Paterson.oddInitialHalver_injective` and `Paterson.oddFinalHalver_injective` in [PatersonOdd](../upper-bound/alternatives/legacy/AKS/Separator/PatersonOdd.lean) and [PatersonOddFinal](../upper-bound/alternatives/legacy/AKS/Separator/PatersonOddFinal.lean) | Separate directional virtual-maximum and virtual-minimum constructions. They are not yet an arbitrary-arity five-level separator. |
| Numerical budgets | [PatersonNumerics](../upper-bound/alternatives/legacy/AKS/Bags/PatersonNumerics.lean) | Six entropy bounds: 262, 263, 155, 167, 187, 217; first level shares the maximum, so total depth is 989. |
| Parameter repair | [PatersonParams](../upper-bound/alternatives/legacy/AKS/Bags/PatersonParams.lean) | Literal reported choices fail two interior inequalities. `nu = 693/1000` repairs them with strict slack; ideal stage ratio is below `123/20`. These are scalar inequalities, not a bag invariant proof. |
| Trust audit | [PatersonAxioms](../upper-bound/alternatives/legacy/AKS/Halver/PatersonAxioms.lean) | Compile-time axiom checks for the main local results: only `propext`, `Classical.choice`, `Quot.sound`. |

The supported contract is intentionally weaker than the existing
[`IsSeparator`](../lower-bound/experiments/AKS/Separator/Defs.lean): its cohort support `1/50` is smaller
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
[FastParams](../upper-bound/alternatives/legacy/AKS/Paterson/FastParams.lean) checks every interior parameter
constraint and `(2*A)^2 * nu^13 < 1`.
The older `roundedParams` and ideal approximately-6100 certificates are
historical candidate arithmetic; the current budget includes root sorting.

### Checked concrete components

| Component | Files | What is proved |
| --- | --- | --- |
| Parallel separator stage | [BagSeparator](../upper-bound/alternatives/legacy/AKS/Paterson/BagSeparator.lean), [Stage](../upper-bound/alternatives/legacy/AKS/Paterson/Stage.lean) | Actual scattered bag networks, depth at most 989, local execution identities, supported old-stranger filtering, and a routed placement for specified fringes. |
| Fresh-stranger source | [Fresh](../upper-bound/alternatives/legacy/AKS/Paterson/Fresh.lean), [Balance](../upper-bound/alternatives/legacy/AKS/Paterson/Balance.lean) | Actual first-halver execution estimates, finite disjoint-cohort counting, rounded fresh-cost arithmetic, and a capacity-based sufficient condition for rank balance. |
| Concrete interior preservation | [Transition](../upper-bound/alternatives/legacy/AKS/Paterson/Transition.lean) | `interior_parallel_step` discharges the former abstract separator-filter and first-stranger hypotheses. Actual size, capacity, fringe, parity, and `ChildBalance` hypotheses remain explicit. |
| Descendant contamination | [Subtree](../upper-bound/alternatives/legacy/AKS/Paterson/Subtree.lean) | Geometric subtree intrusion bound for the new Paterson parameters, conditional on the old invariant and parity emptiness. |
| Rounded size recipe | [Schedule](../upper-bound/alternatives/legacy/AKS/Paterson/Schedule.lean), [BoundarySchedule](../upper-bound/alternatives/legacy/AKS/Paterson/BoundarySchedule.lean), [ClippedRouting](../upper-bound/alternatives/legacy/AKS/Paterson/ClippedRouting.lean) | 32-lattice subtree totals, size bounds, fringe coverage, and exact routing counts at full, clipped, and empty levels. |
| Explicit cold storage and one-tree allocation | [ColdStorage](../upper-bound/alternatives/legacy/AKS/Paterson/ColdStorage.lean), [ColdAllocation](../upper-bound/alternatives/legacy/AKS/Paterson/ColdAllocation.lean), [AllocationSchedule](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationSchedule.lean), [AllocationPreservation](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationPreservation.lean), [AllocationInitial](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationInitial.lean) | Computable ownership including cold storage, centered initialization and feeds, actual routing, and `allocationRun_invariant`. Every bag and cold-storage cardinality is checked while the root capacity stays above the threshold. This is positional allocation, not sorting correctness. |
| Storage-aware comparison and routing | [StoredStage](../upper-bound/alternatives/legacy/AKS/Paterson/StoredStage.lean), [StoredRouting](../upper-bound/alternatives/legacy/AKS/Paterson/StoredRouting.lean), [StoredSizes](../upper-bound/alternatives/legacy/AKS/Paterson/StoredSizes.lean) | Parallel execution for arbitrary bag-local networks, depth bounds, unchanged cold inputs, nonroot register flow, root returns, and actual output cardinalities. |
| Actual full-bag rank balance | [AllocatedSubtree](../upper-bound/alternatives/legacy/AKS/Paterson/AllocatedSubtree.lean), [RankCohorts](../upper-bound/alternatives/legacy/AKS/Paterson/RankCohorts.lean), [AllocationBounds](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationBounds.lean), [AllocatedBalance](../upper-bound/alternatives/legacy/AKS/Paterson/AllocatedBalance.lean) | Actual subtree totals and parent/sibling conservation, native rank counts, and `allocated_full_cohort_balance` from the old stranger invariant. Coherent rounding cancels in the sibling deficit. |
| Actual partial-bag rank budgets | [PartialBoundary](../upper-bound/alternatives/legacy/AKS/Paterson/PartialBoundary.lean), [AllocatedPartialBalance](../upper-bound/alternatives/legacy/AKS/Paterson/AllocatedPartialBalance.lean) | Available cohort counts, actual half-size upper bounds, `allocated_partial_fresh_budget`, and separator support when the outgoing middle is nonempty. These estimates are now assembled by `ScheduledPartialTransition`. |
| Root purity and sort cost | [Root](../upper-bound/alternatives/legacy/AKS/Paterson/Root.lean), [TightDepth](../upper-bound/alternatives/legacy/AKS/Bitonic/TightDepth.lean) | At a sufficiently small root capacity, the invariant implies zero deepest strangers from level six. Given explicit region size bounds, the top region has fewer than `2^33` wires and its scattered bitonic sort costs at most 561. No forest splitting correctness theorem yet. |
| Arbitrary virtual padding | [Padding](../upper-bound/alternatives/legacy/AKS/Paterson/Padding.lean) | Both directional supported contracts survive restriction with virtual maxima/minima, without additive error. |
| Concrete partial-bag gadget | [PatersonRefinement](../upper-bound/alternatives/legacy/AKS/Separator/PatersonRefinement.lean), [PatersonPartial](../upper-bound/alternatives/legacy/AKS/Separator/PatersonPartial.lean), [PatersonHalfCounting](../upper-bound/alternatives/legacy/AKS/Separator/PatersonHalfCounting.lean), [PatersonPartialCertificate](../upper-bound/alternatives/legacy/AKS/Separator/PatersonPartialCertificate.lean) | Four refinement levels cost 726; the actual-size first split and padded half refinements cost 989. `partialNetwork_supported` proves both whole-network directional supported contracts with explicit actual-size and virtual-size support budgets. The first split retains its large-cohort guarantee. The mixed boundary invariant is checked in `ScheduledInvariant`. |
| Proposed operation counts | [Accounting](../upper-bound/alternatives/legacy/AKS/Paterson/Accounting.lean) | `T(k) = 13*ceil(k/2)` overcomes initial capacity growth. The proposed cost `989*T(k) + 561*k` is at most `7000*k` for `k >= 613`. These are arithmetic theorems, not sorting theorems. |
| Kernel audit | [Axioms](../upper-bound/alternatives/legacy/AKS/Paterson/Axioms.lean), [StorageAxioms](../upper-bound/alternatives/legacy/AKS/Paterson/StorageAxioms.lean) | Guarded axiom checks on transition, padding, partial certificates, allocation runs, actual rank balance, root bounds, and accounting. Only `propext`, `Classical.choice`, and `Quot.sound` appear. |

### Remaining global obligations

The comparison-stage obligation is now closed: `scheduledCompare_preserves`
in [ScheduledInvariant](../upper-bound/alternatives/legacy/AKS/Paterson/ScheduledInvariant.lean) handles full,
partial, root, inactive, and empty-middle cases. The selected local networks and
actual stage have depth at most 989.
[PatersonRun](../upper-bound/alternatives/legacy/AKS/Separator/PatersonRun.lean) constructs the repeated network
and proves its invariant and depth at most `989*t` within the root window.

Root split groundwork is also checked:

- [RootAllocationBudget](../upper-bound/alternatives/legacy/AKS/Paterson/RootAllocationBudget.lean): the actual
  upper region has fewer than `2^33` registers in the root split window.
- [UpperRegionCounts](../upper-bound/alternatives/legacy/AKS/Paterson/UpperRegionCounts.lean) and
  [DescendantRegisters](../upper-bound/alternatives/legacy/AKS/Paterson/DescendantRegisters.lean): the upper
  and deep regions partition all registers, with upper size `N - 64*T6`.
- [DeepErrors](../upper-bound/alternatives/legacy/AKS/Paterson/DeepErrors.lean),
  [DeepPurity](../upper-bound/alternatives/legacy/AKS/Paterson/DeepPurity.lean), and
  [DeepPrefixAgreement](../upper-bound/alternatives/legacy/AKS/Paterson/DeepPrefixAgreement.lean): global deep
  error bounds, exact half purity, and actual/assigned prefix agreement outside errors.
- [DeepPrefix](../upper-bound/alternatives/legacy/AKS/Paterson/DeepPrefix.lean): exact assigned deep prefix counts.
- [PrefixDiscrepancy](../upper-bound/alternatives/legacy/AKS/Paterson/PrefixDiscrepancy.lean): generic remaining
  prefix discrepancy and sorted-bin wrong-rank bounds.

### Completed global proof chain

| Obligation | Checked endpoint |
| --- | --- |
| Exact sorted-bin coordinates and errors | [RootPrefixCoordinates](../upper-bound/alternatives/legacy/AKS/Paterson/RootPrefixCoordinates.lean), [RootSortedBins](../upper-bound/alternatives/legacy/AKS/Paterson/RootSortedBins.lean) |
| Actual root rebuild, cardinalities and stranger budgets | `allocatedRebuild_preserves` in [RootRebuildInvariant](../upper-bound/alternatives/legacy/AKS/Paterson/RootRebuildInvariant.lean) |
| Independent halves, actual child allocation and invariant | `scheduledChild_allocation`, `scheduledChild_invariant` in [ChildInvariant](../upper-bound/alternatives/legacy/AKS/Paterson/ChildInvariant.lean) |
| Phase windows, fuel and well-founded recursion | [ForestPhase](../upper-bound/alternatives/legacy/AKS/Paterson/ForestPhase.lean), [PatersonForest](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForest.lean) |
| Actual recursive network depth | `forestNetwork_depth_le` in [PatersonForestDepth](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForestDepth.lean) |
| Input-independent final rank arrangement | `preliminaryNetwork_independent` in [PatersonForestRanks](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForestRanks.lean) |
| Fixed permutation correction in depth k | `exists_known_permutation_correction` in [KnownPermutation](../upper-bound/alternatives/legacy/AKS/Sort/KnownPermutation.lean) |
| Full sorting correctness and doubled depth bound | `correctedForest_sorts`, `correctedForest_depth_double` in [PatersonForestSorts](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForestSorts.lean) |
| All-n minimum depth and limsup | [PatersonTight](../upper-bound/alternatives/legacy/AKS/Bounds/PatersonTight.lean) |
| Complete theorem axiom audit | [PatersonTightAxioms](../upper-bound/alternatives/legacy/AKS/Bounds/PatersonTightAxioms.lean) |

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
or declared `axiom` in the protected files. The optional
`upper-bound/experiments/expanders/Random/` native-evaluation path is separate
from the AKS and Paterson proofs. The audit now reads UTF-8 on
Windows and permits the selected refined network in `Bounds/PatersonTight.lean`,
the classical minimum-depth definition in the exact
`Bounds/Upper.lean` file and selected Paterson network in `Bounds/Paterson.lean`,
alongside the two named analytic Paterson files in `Bags/`. Both `network`
and `SortingDepth.upperNetwork` remain computable definitions.

## Current research directions (2026-10-05, unverified unless noted)

- Paterson tuning is exhausted in-family. A full-floor grid search over
  `(A,μ,δ,δᵢ,ν,mincap)` encoding every known floor (bag parameters, lattice
  fringe, cohort corners, rebuild lock, `νA ≥ 1`, ceiling margins) found 775
  fully-feasible points, none with stage ratio `m ≤ 12`; the checked-in
  parameters are the in-family optimum at `6990.5`. Scripts
  (`scripts/paterson_search.py`, `scripts/paterson_fullfloor_search.py`) are
  untracked experiment tooling, not proof. Earlier sub-6990 search hits
  (`6463`, `6894.5`) were retracted as infeasible mirages missing hidden
  floors; the `tune-6463` branch was deleted and `main` rebuilt green.
- Chvátal 1830 track: **complete**. See the headline section above and
  [chvatal-1830/](../upper-bound/best/README.md); the scaffolding-era notes are in
  [old/chvatal-1830-scaffolding-history.md](old/chvatal-1830-scaffolding-history.md).

## Chvátal 1830

The self-contained proof is in [`chvatal-1830/`](../upper-bound/best/README.md) (proof map and build
instructions) with its modular ledger in [`chvatal-1830/LEDGER.md`](../upper-bound/best/LEDGER.md).
Unused earlier scaffolding is archived, unbuilt, in
[`archive/chvatal-scaffolding/`](../archive/chvatal-scaffolding/README.md).

## Documents and history

- [Sorting-depth limit and repair-interface investigation](sorter-repair-barrier.md)
  (2026-10-07): checked prefix-locality, dependency, and cut lemmas; a derived
  obstruction to staged local-module amplification with vanishing repair
  overhead; finite lifted-prefix probes. `Bounds/DyadicLimit` proves full
  convergence **conditional on** a uniform additive composition defect.
  The defect is unproved; existence of the limit and improved coefficients
  are not claimed. See the note's verification and status map.

- [Paterson interface audit](paterson-interface.md): detailed local theorem
  contracts, corrected parameter arithmetic, and remaining mathematical issues.
- [Local Paterson paper](paterson.pdf): primary mathematical source for this
  track; verify claims against the relevant sections before extending the proof.
- [September handoff entry point](../archive/handoffs/AKS_CODEX_HANDOFF_2026-09-27/README_START_HERE.md)
  and [historical proof ledger](../archive/handoffs/AKS_CODEX_HANDOFF_2026-09-27/PROOF_STATUS_LEDGER.md):
  preserved background. Their claim that Paterson is not formalized predates
  the completed rounded forest formalization and its final sorting theorem.
- [Current research state from the handoff](../archive/handoffs/AKS_CODEX_HANDOFF_2026-09-27/CURRENT_RESEARCH_STATE.md):
  Avenue 2 and `GoodSplitter` ideas remain research leads; candidate constants
  from older handoffs are not proved.
- [Bag-tree notes](bags.md), [module guide](modules.md), and the remaining
  upstream `docs/` describe inherited infrastructure. Some progress/trust
  descriptions are historical; use Lean declarations and current axiom checks
  as the evidence for proof status. `docs/old/` is historical planning material.

The latest profile-budgeted funnel recurrence couples exterior mass and root blockers and finds substantial fixed-profile expectation slack numerically. It still does not handle the common-witness profile union. The 107-layer bulk target has no construction; the next candidate is a shared multiway approximate separator checked against the exact central contract. See [profile-budgeted funnels](../upper-bound/experiments/global-cost-audit/profile-budgeted-funnels.md).

A candidate screen confirms that the cited two-round k-halver is not itself the central 107-layer repair: it handles one cut, has percent-scale error, and a direct Batcher simulation costs 156�182 layers for k=4096�8192. The proposed p-way composition needs an explicit finite analysis before expander work is justified. See [the 107-layer screen](../upper-bound/experiments/global-cost-audit/central-107-screen.md).

A finite Batcher-priced check narrows the 107-layer AKS route: k=512 costs 90 layers for the two sorter rounds and leaves 17 for the unquantified p-way combination; the stated arbitrary-input halver error is still about 0.22�0.27. The published sketch gives no finite combination bound, so this does not yet define a candidate network.

A row-scramble-specific two-height profile shows the two-round k=512 core leaves expected leakage at least delta/4 for every fixed row permutation. Under the candidate geometry this is about 110x the central allowance, so the final 17 layers need a localized multiscale repair or a stronger first-scramble promise. This is conditional on the L1 profile class; reachability under the first scramble remains open. See [the central 107-layer screen](../upper-bound/experiments/global-cost-audit/central-107-screen.md).

A further screen of the 17-layer finisher finds simple candidates insufficient on the same two-height profile: random cross-boundary matchings leave about 0.0418 delta expected leakage and exact Batcher sorting of 32-wire blocks about ~0.06998 delta, versus the conditional ~0.0022 delta stress threshold. The later common localization promise excludes this profile on its good event (mass beyond the band about 8 million per column versus A=4,096--8,192), so it is not necessary for the revised reachable class if that informal promise holds. These are model-specific diagnostics, not lower bounds on arbitrary finishers.


The localized 17-layer repair target now has a matching-graph criterion: on the aligned iid boundary profile, degree 17 already contributes about `0.001879*delta` isolated highs, leaving `0.000321*delta` under the conditional `0.0022*delta` stress threshold. Sampled cyclic-shift schedules leave about `0.044*delta`; this is a limited simulation screen, not a lower bound on general networks. See [the central 107-layer screen](../upper-bound/experiments/global-cost-audit/central-107-screen.md).

A finite matching-schedule diagnostic trains each layer to maximize expected immediate repairs: validation residual was `0.047394` at 64 positions, against `0.051465` for five random schedules, still over 21x target. The next check is graph capacity via per-input maximum matching versus the fixed edge order. See [the script and central screen](../upper-bound/experiments/global-cost-audit/central-107-screen.md).

Four bipartite multigraphs formed from 17 random perfect matchings (4,096 positions, 500 balanced samples each) left `0.0436` residual under fixed edge order but only `0.00250`--`0.00261` under per-input maximum matching. The graph has near-target capacity; realizing it with one fixed 17-layer schedule is the bottleneck in this model. This is a finite diagnostic only. See [the capacity screen](../upper-bound/experiments/global-cost-audit/matching_capacity_screen.py) and [analysis](../upper-bound/experiments/global-cost-audit/central-107-screen.md).

A two-row within-row butterfly compactor was screened by exact four-state distribution propagation. Exhaustively placing the 17 layers within the family of butterfly dimensions plus pointwise cross-row cancellation gives best leakage `0.007162` on `2^16` positions, still 3.25x above the conditional `0.0022` stress threshold. Ideal block compaction would leave about `0.001102` from count imbalance alone, so a substantial gain requires changing the compactor structure, not just layer placement. This remains an iid local diagnostic. See [the script](../upper-bound/experiments/global-cost-audit/butterfly_compaction_screen.py) and [analysis](../upper-bound/experiments/global-cost-audit/central-107-screen.md).
A first Monte Carlo screen of random perfect-matching compaction layers on 256 wires is substantially worse than butterfly schedules: three sampled 16-layer networks per orientation leave 0.047-0.051 leakage, versus 0.029449 for the best 17-layer butterfly/cancellation schedule. This is an initial rejection of unstructured random topologies, not a limitation on designed networks. See [the screen](../upper-bound/experiments/global-cost-audit/random_compaction_screen.py) and [central analysis](../upper-bound/experiments/global-cost-audit/central-107-screen.md).
A truncated 16-layer bitonic network also leaves about 0.0495 leakage on 64, 256, and 1,024 wires, sampled iid, worse than the best 17-layer butterfly/cancellation schedule on 256 wires. Random and generic sorting-network prefixes fail this screen; investigate a distribution-tailored coarse-to-fine compactor. See [the screen](../upper-bound/experiments/global-cost-audit/bitonic_prefix_screen.py) and [analysis](../upper-bound/experiments/global-cost-audit/central-107-screen.md). Finite sorter searches such as [SorterHunter](https://github.com/bertdobbelaere/SorterHunter) can seed local gadget search but optimize exact sorting and cover at most 64 wires; the exact 64-position iid compaction imbalance floor is still 0.03519. Thus use finite gadgets only within a recursively composed profile-combining design. The `0.0022` threshold is conditional on an L1-admissible two-height profile not yet shown reachable; the actual repair contract is cut- and input-dependent. See [the repair contract](../upper-bound/experiments/global-cost-audit/repair-contract.md). A cut-sensitive retuning also appears to close the 631-layer band baseline reserve: lowering protected-window error from 2048 to 896 and adjusting beta leaves at least 128 counts per column under the conservative allowance, with sampled worst probability margins 1.695 (window) and 3.397 (bulk tail). This is still informal and does not supply the desired 107-layer network. See [calculation](../upper-bound/experiments/global-cost-audit/central_slack_envelope.py) and [derivation](../upper-bound/experiments/global-cost-audit/central-bulk-feasibility.md).

A fixed-matching search on 64-position iid quarter-density inputs found a 17-layer schedule with validation leakage 0.02138, versus 0.04525 for repeated butterfly and 0.03637 for a random schedule. This is only a finite iid topology screen, not a bound for the scheduler-reachable localized band states. See [search code](../upper-bound/experiments/global-cost-audit/finite_repair_search.py) and [central screen](../upper-bound/experiments/global-cost-audit/central-107-screen.md). The current next step is to align the evaluator with the cut-dependent repair contract before spending effort on broader finite searches.

A small exact contract-search loop now enumerates height profiles under L1/tail constraints, applies one fixed row-wise scramble and repair, and computes Q_*, Q_R, and per-cut integer slack. On an 8x4 toy geometry, a 4-layer unrestricted matching network passed 781 profiles; the same shallow random search under a central-row confinement did not. The toy cap is synthetic and the envelope is not an upstream reachability theorem. See [evaluator](../upper-bound/experiments/global-cost-audit/cut_contract_screen.py) and [results/analysis](../upper-bound/experiments/global-cost-audit/central-107-screen.md). The scheduler-shaped toy 66x2 search also failed under central confinement, but that is not a lower bound. The unrestricted 8x4 schedule touched protected rows in 46 of its 64 comparators. Details are in the [central repair screen](../upper-bound/experiments/global-cost-audit/central-107-screen.md).
