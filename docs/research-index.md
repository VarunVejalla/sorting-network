# Sorting-network research index

Local review: 2026-10-06. This index describes the checked-out sources, including
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

**Chvátal-form 1830 endpoint (finite Batcher range, 2026-10-06).**
[Bounds/Chvatal1830Batcher](../AKS/Bounds/Chvatal1830Batcher.lean) proves
kernel-checked

```text
minimum_depth_le_1830_logb_of_batcher_range:
  for 1 < n with 7 ≤ Nat.clog 64 n ≤ 603,
  D(n) ≤ 1830 * log₂ n − 58657
```

via full-wire Batcher on `64^d` (depth ≤ §7 `totalDepth d`). This is **not**
the paper scramble schedule and does **not** give unconditional
`limsup D(n)/log₂ n ≤ 1830` (Batcher exceeds `totalDepth` for every `d > 603`;
see `Limsup1830Residual` / paper depth-shell `PaperDepthShellSortResidual`).
See the Chvátal section below for the local proof map.

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
- Chvátal 1830 track (Phase 0 + Phase 1 §3 + §4 algebra + §5–§6 scaffolding;
  reference `docs/dcs-tr-294.pdf`, untracked Rutgers DCS-TR-294). **Kernel-checked
  unless noted.** [DepthSkeleton](../AKS/Chvatal/DepthSkeleton.lean): §7 depth
  accounting (`totalDepth`, padded `1830 log₂ n − 58657`), numeric (4.1)–(4.5),
  (7.1)–(7.2), `δF ≤ 1/25`; [SkeletonAxioms](../AKS/Chvatal/SkeletonAxioms.lean)
  standard axioms only. §3–§4 bag/scheduler/outsider chain through
  [ChildSend](../AKS/Chvatal/ChildSend.lean),
  [AbstractPlacement](../AKS/Chvatal/AbstractPlacement.lean) (`preferNon`
  children-send, **`ChildRegisterCapacityLower`** when child regs nonempty,
  `PreferNonStageChildrenData.fromParent_empty` / `rootStage_fromParent_empty`,
  support=abstract cover, `StageKernelWithChildren.ofAbstractChildSend`,
  root init `P`), [Schedule7](../AKS/Chvatal/Schedule7.lean) (`levelSchedule7`,
  purity envelope, Lemma 3.2 without snap), [Params](../AKS/Chvatal/Params.lean)
  `SeparatorConds` at `params7`. §5–§6: [PropertyBF](../AKS/Chvatal/PropertyBF.lean),
  [Theorem51](../AKS/Chvatal/Theorem51.lean) (statement + routing bridge),
  [Lemma61](../AKS/Chvatal/Lemma61.lean) / [Lemma63](../AKS/Chvatal/Lemma63.lean)
  (Chernoff cores; **paper** combinatorial B is `HasCombinatorialPropertyB` ∀ monotone `c`;
  **pipeline** B is `HasCombinatorialPropertyBOnPipeline` with `TotalColumnOnesLeLevel m n i c`
  (`totalColumnOnes c ≤ n·i`). Module A fail-bound for B uses
  `DecodeMatrixClassObligation` / `lemma61FailBound_onPipeline_of_decodeClass`, not global
  `TotalColumnOnesLeN`),
  [Lemma62](../AKS/Chvatal/Lemma62.lean) / [Lemma62Chernoff](../AKS/Chvatal/Lemma62Chernoff.lean):
  fringe MGF/Chernoff, `Lemma62FringeCellBound.of_hyp`; **cell counting for F is
  kernel-checked under** `FringeOnesDensityLeHalfWidth` (hence under global
  `TotalColumnOnesLeN` / `AvgRowOnesLeOne` via `FringeOnesDensityLeHalfWidth_of_totalColumnOnesLeN`) plus
  per-cell `hepsCell` and numeric `hclose` in
  `Lemma62CellCountingObligation` / `ModuleACombinatorialObligation`.
  [ModuleA](../AKS/Chvatal/ModuleA.lean) packages combinatorial B/F; at **`m = 100`, `n = 16`**
  kernel-checked **`ExistsCombinatorialPropertyBOnPipeline_of_decodeClass_m100`** /
  **`exists_combinatorialScrambleBF_onPipeline_of_ModuleA_m100`** (no `AvgRowOnesLeOne` on B).
  F-side cell counting still uses **`AvgRowOnesLeOne`** (fringe density).   [MatrixBridge](../AKS/Chvatal/MatrixBridge.lean): sort–scramble–sort
  skeleton, wire layout, combinatorial→matrix wiring into `Theorem51Obligation`;
  **B-side (kernel-checked, general `m`,`n`):** Thm 5.1 witnesses use
  `SemanticSeparator` / `ScrambleSeparatorWitness` with **semantic** matrix
  properties (`HasPackSemanticPropertyB` / `HasMatrixPropertyB_exec` on
  `pack.semanticExec`; `pack.net` still ignores `wirePerm`). Kernel-checked:
  `MiddleStageDecodeHyp.of_idealColumnSort_rowScramble`,
  `packSemanticIntrusionCountB_eq_onesAboveBottom` /
  `matrixIntrusionCountB_semantic_eq_onesAboveBottom` in
  [SortedColumnDecode](../AKS/Chvatal/SortedColumnDecode.lean); canonical pack
  `canonicalSortScrambleSortPack` (`columnSortNetwork` + `rowScrambleNetwork`) via
  `HasPackSemanticPropertyB_canonical_of_combinatorial` /
  `HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline` /
  `combinatorialPropertyB_onPipeline_implies_matrixB_exec_canonical`;
  `CombinatorialToMatrixObligationB.of_columnSortNetwork_rowScramble` when universal
  `IdealColumnSort` + `RowScrambleCorrect` hold;
  `MatrixBridgeBResidual.of_columnSortNetwork_rowScramble_discharged` packages the B-bridge.
  **F-side (kernel-checked, 2026-10-05):** `MiddleStageFringeDecodeHyp.of_idealColumnSort_rowScramble`,
  `packSemanticIntrusionCountF_eq_onesAboveBottom`,
  **`FringePropertyFClosingHyp.of_idealColumnSort_rowScramble`** (semantic `< ε_F·j` via top-`j`
  column totals and `j < f` from **`δ_F·n < 1`**, not a direct combinatorial-F Chernoff step),
  **`CombinatorialToMatrixObligationF.of_columnSortNetwork_rowScramble`**, and full
  **`CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble`** (B + F) when universal
  `IdealColumnSort` + `RowScrambleCorrect`, `0 < f`, `0 < ε_F`, and `δ_F·n < 1` hold
  (`deltaF_mul_n_lt_one_params7_n16` for §7 at `n = 16`).
  `ModuleACombinatorialObligation.of_params7_m100_n16` / **`of_params7Geometry_m100_n16`**
  (B/F counting bundle given `hepsB`, `havg`, `hepsWorst`; **`hf2` / `hmF` / `hjMax48`**
  discharged on any `params7Geometry` shape via [ModuleANumerics](../AKS/Chvatal/ModuleANumerics.lean);
  §7 `hclose` at `m=100`,`n=16` still via
  `lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16` when `jMax ≤ 48`).
  §7 endpoint
  [Bound1830](../AKS/Chvatal/Bound1830.lean): `AbstractChildSendTrajectory` +
  outsider induction, `params7_purity_of_abstract`, `Sorting1830Obligation`
  bundle, **`network_depth_le_1830_of_sorting1830Obligation`** (hypothesis-dependent).
  **`FinalSorterDepthBudget.of_batcher42` discharged** (`bitonicSort 42`, depth
  `≤ 903`).   **`NetworkDepthAssemblyObligation`**: root++ordinary×`(tf−1)`++final
  with **`depth_le_totalDepth` kernel-checked** from append-depth lemmas +
  `StageDepthBudget`; **`assembledChvatalNetwork_sorts` /
  `of_stage_sorts`** discharge assembled `Sorts` once each stage net sorts.
  **[StageAssembly](../AKS/Chvatal/StageAssembly.lean) (2026-10-05):** executable
  `chvatalEmptyStageNet` / `chvatalFinalBatcherNet` on `64^d`; empty root+ordinary
  assembly lemmas; **`NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7`**
  — kernel-checked **`Sorts`**, **`StageDepthBudget.ofPaper`**, and
  **`composed = chvatalFinalBatcherNet 7`** (honest separator placeholders; real
  **6320 / 3660** stage nets still open). Trajectory
  packaging: **`PreferNonStageChildrenData`** (kernel-checked preferNon
  children-send; **`fromParent_empty`**) + **`AbstractParentResidueRouting`**
  (Thm 5.1 bad-send/fringe Finset bounds; **`AbstractParentResidueRouting.of_residue`**
  / **`of_stageRoutingResidue`**, **`AbstractParentResidueRouting.of_emptyFromParent`**
  for zero parent send-up with explicit budget nonnegativity, **`PreferNonStageObligation.routing_of_residue`**) ⇒
  **`PreferNonStageObligation`** / **`Params7AbstractTrajectoryRoutingObligation`** /
  **`Params7AbstractTrajectory.of_routingObligation`** (with **`outsiderBoundLe_tf`**
  / **`purity_at_meet`** corollaries).
  **[Schedule7Trajectory](../AKS/Chvatal/Schedule7Trajectory.lean) (2026-10-06):**
  `capacity_le_nativeCard_params7`, `ChildRegisterCapacityLower.of_ladderNative_params7`,
  **`Params7PreferNonStageRoutingObligation.rootStage`** (any `d`; stationary empty
  `fromParent`) / **`rootStage7`**, **`Params7AbstractTrajectoryRoutingObligation.stationaryRoot`**
  for all `d ≥ 7`,
  **`AbstractParentResidueRouting.of_zeroStrangersFromParent`** (generalizes empty send-up),
  **`level1NativePlacement`** / **`nativeLevel1FromParent`** (nonempty for level-1 bags),
  **`Params7PreferNonStageRoutingObligation.nativeRootSplit`** (root→level-1 evolving stage;
  zero-stranger sends meet Thm 5.1 / paper-ordinary quality budgets),
  **`nativeLevel1Stay`**, full evolving
  **`Params7AbstractTrajectoryRoutingObligation.nativeLevel1`** for `d ≥ 7`
  (`d = 7` has `tf = 1`, so the split alone completes the schedule;
  **`nativeLevel1_d7`**),
  `ScrambleSeparatorBagLink` / `parentSeparatorQuality_params7` (hypothesis-level
  `ExistsScrambleSeparator` → bag `LocalSeparatorQuality`, not wire `fromParent` yet).
  **Schedule split:** `moduleA_invariantF16`, `ScrambleSeparatorModuleABagLink`,
  `not_scrambleSeparatorBagLink_invariant7_of_moduleA_f16` (Module A `P` cannot use
  `invariant7` scalars in `ScrambleSeparatorBagLink`).
  Open: wire-level separator→`fromParent` Finsets from scramble nets (native/identity
  sends are quality-compatible but not separator-net-derived); deeper ladder capacity
  on nonempty child bags beyond level 1; real root/ordinary separator nets (not only
  **`Sorting1830Obligation.of_routingAssembly_d7`**
  in [StageAssembly](../AKS/Chvatal/StageAssembly.lean): empty root/ordinary + Batcher,
  net **`= chvatalFinalBatcherNet 7`**, depth still hypothesis-dependent on trajectory).
  **`Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1`**: Batcher assembly +
  evolving native PreferNon + paper-ordinary residual (kernel-checked).
  **`Sorting1830Obligation.of_routingAssembly`** bundles routing trajectory + separator + assembly.
  Matrix bridge progress:
  wire/count lemmas, `RowScrambleCorrect`, Bool column-local region counts
  (`ColumnOnesRegion`), marking under `KeysAreWireIndices`; kernel-checked
  `IdealColumnSort` for `columnSortNetwork` and column wire/bitonic bridge in
  `MatrixBridge`.   **`SortedColumnDecode.lean`:** kernel-checked semantic B/F decode, F closing, and
  `CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble` (see F-side above).
  **`RowScramble.lean`:** `RowScrambleCorrect` kernel-checked for general `n` via
  `of_rowScrambleNetwork` (wired middle stage + ideal column sort).
  **§7 separator instantiation (2026-10-06):** [Theorem51Core](../AKS/Chvatal/Theorem51Core.lean)
  `params7Geometry` / `params7Geometry_f16` / `theorem51Params7`; [Lemma62](../AKS/Chvatal/Lemma62.lean)
  `fringeRowCount_eq`, **`fringeRowCount_m100_f16`** (`m−f/2 = 92`), **`lemma62_jMax_params7_f16_le_48`**;
  [ModuleANumerics](../AKS/Chvatal/ModuleANumerics.lean) shape lemmas and residual bundle
  **`ModuleAParams7_f16Residual`**. [ModuleA](../AKS/Chvatal/ModuleA.lean):
  **`ExistsScrambleSeparator_params7Geometry_m100_n16`** — same conclusion as
  **`ExistsScrambleSeparator_params7_m100_n16`** but **`hPeps`**, **`hf2`**, **`hmF`**,
  **`hjMax48`**, **`hfm`**, **`hfpos`** kernel-discharged when `P = theorem51Params7 …`;
  **`ExistsScrambleSeparator_params7Geometry_f16_residual`** packages the fixed `f = 16`
  witness. Legacy entry points **`ExistsScrambleSeparator_params7_m100_n16`** /
  **`ExistsScrambleSeparator_params7Geometry_f16`** / **`Theorem51Obligation_params7_m100_n16`**
  still list the full hypothesis list for callers that do not use the geometry lemma.
  All combine `ModuleACombinatorialObligation`, universal `rowScrambleNetwork_all`, and
  **`CombinatorialToMatrixObligation.of_params7_m100_n16_bridge`**
  ([SortedColumnDecode](../AKS/Chvatal/SortedColumnDecode.lean); **`deltaF_mul_n_lt_one_params7_n16`**
  kernel-checked).   Pipeline (decode class): combinatorial→matrix lemmas in **`MatrixBridge`** /
  **`SortedColumnDecode`**; §7 separator entry points in **`ModuleABridge`** (needs **`g.m = 100`**, **`g.n = 16`**).
  Global **`ExistsCombinatorialPropertyB`** still needs **`HasCombinatorialPropertyB.imp_onPipeline`**
  plus unrestricted B (legacy **`Lemma61FailBoundObligation`** + **`havg`**) if one insists on paper ∀`c`.

  **§7 paper-scale scramble (DCS-TR-294 §7, not `m = 100` minima):** [Theorem51Core](../AKS/Chvatal/Theorem51Core.lean)
  **`paperOrdinaryGeometry`** (`m = 2^60`, `n = 16`, `f = 2^58`, `k = 1`, `b = 2^59`), **`paperOrdinaryGeometry_m2p59p1`**
  (`m = 2^59+1`, `b = 1`), **`paperRootGeometry`** (`m = 2^79`, `f = 2^78`); paper **`ε_B`**
  via **`paperOrdinaryEpsB`** / **`paperRootEpsB`** (not **`invariant7.epsB`**). [PaperScrambleNumerics](../AKS/Chvatal/PaperScrambleNumerics.lean)
  (kernel-checked): Chernoff **`chernoff_hepsB paperOrdinaryM ≤ paperOrdinaryEpsB`**, root analogue,
  **`not_chernoff_hepsB_le_invariant7_at_paperOrdinaryM`**, **`paperOrdinary_hepsF_ge_4e`** at `f = 2^58`,
  **`paperRoot_hepsF_ge_4e`** at `f = 2^78`,
  **`PaperOrdinary_epsF_lemma62_Certificate`** / **`paperOrdinary_epsF_lemma62_lb_le_invariant7`**,
  **`PaperRoot_epsF_lemma62_Certificate`** / **`paperRoot_epsF_lemma62_lb_le_invariant7`**, and
  **`theorem51Params_paperOrdinaryGeometry_discharged`** / **`theorem51Params_paperRootGeometry_discharged`**
  (full Thm 5.1 `P` at paper ordinary/root geometry with `invariant7` `δ_F`/`ε_F`). Fringe Chernoff **`hepsWorst`**: **kernel-checked impossible** at
  `invariant7.epsF` — **`not_paperOrdinary_hepsWorst_le_invariant7_epsF`** (scale **`≳ 10^10 × epsF`**, i.e.
  **`paperOrdinary_hepsWorst > 125`** vs **`epsF = 1/80000000`**; numeric order **`≈ 7×10^10` vs `1.25×10^-8`**).
  **`paperOrdinary_lemma62_jMax_gt_48`**: `jMax` at `(f,n) = (2^58,16)` is **`≫ 48`** (not the `m=100` regime).
  **`PaperOrdinary_hclose_residual`**: cell-union **`hclose`** packaged as an open Prop (numerically false at paper scale).
  **`SortedColumnDecode`**: **`CombinatorialToMatrixObligation.of_invariant7_geometry_bridge`** for any
  **`ScrambleGeometry`** with `δ_F = invariant7.deltaF`; at paper ordinary geometry see
  **`paperOrdinary_combinatorialToMatrix_bridge`** in [ModuleABridge](../AKS/Chvatal/ModuleABridge.lean).
  **Module A** (partial): **`of_scrambleGeometry`** / **`Lemma62CellCountingObligation.of_geometry_jMax`** needs
  **`hepsWorst`** + **`hclose`** at paper `(m,jMax)`; **`not_TotalColumnOnesLeN_paperOrdinaryM`**.
  **Not closed at paper `m`:** pipeline B∧F existence / **`ModuleACombinedFailFraction`** at paper numerics,
  global **`AvgRowOnesLeOne`**, and **`ExistsScrambleSeparator`** (packaged residual
  **`PaperOrdinaryScrambleSeparatorResidual`** / **`ExistsScrambleSeparator_paperOrdinaryGeometry_residual`**).
  **`theorem51Params7`** is the wrong `P` at paper `m` (Chernoff ≫ **`invariant7.epsB`**).
  **Unconditional Thm 5.1 separators (pipeline B + `δ_F·n < 1` semantic F):**
  - **`ExistsScrambleSeparator_params7Geometry_f16_moduleA`** — Module A `P` (`ε_B = 1/2`, `ε_F = 300`); not §4-compatible.
  - **`ExistsScrambleSeparator_paperOrdinaryGeometry`** — paper ordinary `m = 2^60`, paper `ε_B`, **`invariant7` `δ_F`/`ε_F`** (DCS-TR-294 §7 ordinary).
  - **`ExistsScrambleSeparator_paperRootGeometry`** — paper root `m = 2^79`, paper root `ε_B`, **`invariant7` `δ_F`/`ε_F`**; Lemma 6.2 floor discharged by **`paperRoot_epsF_lemma62_lb_le_invariant7`** / **`PaperRoot_epsF_lemma62_Certificate`** (value ≪ `1/80000000`).
  - Generic: **`ExistsScrambleSeparator_of_pipelineB_deltaFn`**; B from **`ExistsCombinatorialPropertyBOnPipeline_of_decodeClass`**.
  Semantic F uses **`HasPackSemanticPropertyF.of_idealColumnSort_rowScramble_deltaFn`** (combinatorial F unused when `δ_F·n < 1`).
  **Pack depth (kernel-checked):** ordinary **`ExistsScrambleSeparator_paperOrdinaryGeometry_depth_le_ordinaryStage`** ≤ `3660`; root **`ExistsScrambleSeparator_paperRootGeometry_depth_le_rootSeparator`** ≤ `6320`.
  **§4 paper-ordinary invariants:** **`invariant7_paperOrdinary`** (`ε_B = ε_F = 1/8·10⁷`) with
  **`separatorConds_params7_paperOrdinary`** kernel-checked. Bag link:
  **`ScrambleSeparatorBagLinkPaperOrdinary`** / **`scrambleSeparatorBagLinkPaperOrdinary`**
  (unconditional nonempty) in [Schedule7Trajectory](../AKS/Chvatal/Schedule7Trajectory.lean).
  **`Sorting1830Obligation.d7_batcher_paperOrdinary`** ([StageAssembly](../AKS/Chvatal/StageAssembly.lean)):
  unconditional — stationary PreferNon + **`ScrambleSeparatorResidual.paperOrdinary`** +
  Batcher root/ordinary/final (sorts; `ordinaryRounds 7 = 0`).
  **`Sorting1830Obligation.d7_batcher_paperRoot`**: same assembly with
  **`ScrambleSeparatorResidual.paperRoot`** (unconditional; `ExistsScrambleSeparator_paperRootGeometry`
  discharged). **`network_depth_le_1830_of_d7_batcher_paperOrdinary`** /
  **`_paperRoot`**: for `Nat.clog 64 n = 7`, net depth `≤ 1830 log₂ n − 58657`
  (kernel-checked). Stages are full-wire Batcher, not paper scramble separators; still a
  true depth bound in the §7 padded form at this `d`.
  **Finite Batcher range (strongest unconditional 1830-form endpoint, 2026-10-06):**
  [BatcherAssembly](../AKS/Chvatal/BatcherAssembly.lean) /
  [DepthSkeleton](../AKS/Chvatal/DepthSkeleton.lean) **`batcherFitsTotalDepthMax = 603`**;
  **`bitonicDepthBudget_6d_le_totalDepth`** / **`chvatalFinalBatcherNet_depth_le_totalDepth`**
  for `7 ≤ d ≤ 603`; **`bitonicDepthBudget_6d_gt_totalDepth`** for `d > 603` (Batcher
  method fails past this cutoff). Stage-budget packaging in
  [StageAssembly](../AKS/Chvatal/StageAssembly.lean):
  Batcher all stages for `d ≤ 7`; Batcher-as-root for `d ≤ 18`
  (`batcherRoot_paperOrdinary` / `batcherRoot_paperRoot`); direct totalDepth compare
  for `d ≤ 603`. [Bounds/Chvatal1830Batcher](../AKS/Bounds/Chvatal1830Batcher.lean):
  **`minimum_depth_le_1830_logb_of_batcher_range`** — `D(n) ≤ 1830 log₂ n − 58657`
  for every `1 < n` with `7 ≤ clog 64 n ≤ 603`;
  **`eventually_minimum_depth_le_1830_logb_of_batcher_window`** (windowed, not all large `n`);
  **`limsup_minimum_div_logb_le_1830_of_forall_totalDepth`** (conditional);
  **`Limsup1830Residual`** + **`limsup_…_of_batcher_and_residual`** (honest limsup package;
  residual open for `d > 603`).
  **Paper depth shells (kernel-checked depth, 2026-10-06):**
  **`paperDepthShellNetwork`** in [StageAssembly](../AKS/Chvatal/StageAssembly.lean) —
  tiled root/ordinary packs + parallel final; **`paperDepthShellNetwork_depth_le`**
  `≤ totalDepth d` for every `d ≥ 14`. **`PaperDepthShellSortResidual`** packages
  the open `Sorts` obligation; **`exists_totalDepth_of_paperDepthShellSorts`** and
  **`limsup_minimum_div_logb_le_1830_of_paperDepthShellSorts`** reduce limsup `≤ 1830`
  to those residuals (not discharged).
  Budget lemmas: **`chvatalFinalBatcherNet_depth_le_ordinary`** (`d ≤ 14`),
  **`_le_root`** (`d ≤ 18`). Full-wire Batcher finals meet `903` only for `d ≤ 7`;
  for `d ≥ 7` parallel block finals meet paper final depth (depth only; see below).
  **Pack depth (kernel-checked, 2026-10-06):** [SeparatorDepth](../AKS/Chvatal/SeparatorDepth.lean)
  — columns are wire-disjoint, so `columnSortNetwork_depth_le` ≤ bitonic depth via
  `depth_flatMap_disjoint`; canonical packs (empty scramble comparators) satisfy
  `SortScrambleSortPack_canonical_depth_le_budget` ≤ `2 · bitonicDepthBudget(clog₂ m)`.
  Paper ordinary: `SortScrambleSortPack_paperOrdinary_depth_le_ordinaryStage` ≤ `3660`;
  paper root: `SortScrambleSortPack_paperRoot_depth_le_rootSeparator` ≤ `6320`.
  Also `ExistsScrambleSeparator_paperOrdinaryGeometry_depth_le_ordinaryStage` and
  `ExistsScrambleSeparator_paperRootGeometry_depth_le_rootSeparator` (witnesses with
  those pack-depth bounds). Pack accounting only until bag-routed `64^d` stages.
  **Parallel finals (kernel-checked depth only, 2026-10-06):**
  [ParallelFinalDepth](../AKS/Chvatal/ParallelFinalDepth.lean) /
  [ParallelFinal](../AKS/Chvatal/ParallelFinal.lean) (re-export) —
  `finalBlockSize_dvd_pow64`, `finalBlockEmbed_disjoint`,
  `chvatalParallelFinalNet` = wire-disjoint `flatMap` of `scatterEmbed`
  (`bitonicNetwork finalBlockSize` on contiguous `2^42` blocks),
  **`chvatalParallelFinalNet_depth_le` / `_paper` / `_budget`** ≤ `903` =
  `finalSorterPaperDepth` = `bitonicDepthBudget 42` for every `d ≥ 7`.
  Depth-only shell: **`ParallelFinalDepthObligation.of_parallelBlocks`**
  (also `parallelFinalDepth_ofPaper` in StageAssembly).
  **Does not claim `Sorts`** for `d > 7`; residual **`ParallelFinalPuritySortResidual`**.
  **Pack tiling into `64^d` (kernel-checked depth, 2026-10-06):**
  [StagePackEmbed](../AKS/Chvatal/StagePackEmbed.lean) — abstract
  `BagWireLayout` (`Fin numBags → (Fin bagSize ↪o Fin N)`, pairwise disjoint);
  `parallelScatterBags_depth_le` (packs of depth ≤ `D` ⇒ stage depth ≤ `D`);
  contiguous specialization `parallelPackStageNet_depth_le`. Preferred
  depth-only obligations (no `Sorts`, mirroring `ParallelFinalDepthObligation`):
  **`OrdinarySeparatorDepthObligation`** /
  **`RootSeparatorDepthObligation`**, with
  `of_paperOrdinaryCanonical` (`d ≥ 11`, pack `2^64`, ≤ `3660`) and
  `of_paperRootCanonical` (`d ≥ 14`, pack `2^83`, ≤ `6320`).
  [PackEmbed](../AKS/Chvatal/PackEmbed.lean) re-exports `StagePackEmbed`.
  [StageAssembly](../AKS/Chvatal/StageAssembly.lean):
  `ordinaryPackStage_of_canonical` / `rootPackStage_of_canonical` /
  `parallelFinalDepth_ofPaper`. Tree/Scheduler expose only abstract
  `Placement.regs` (Finsets), not paper-size bag layouts for these tilings.
  `OrdinarySeparatorStageObligation` / `RootSeparatorStageObligation` still
  require `Sorts` (overstrong for separators); prefer the depth-only shells.
  **Open for limsup / all large `n`:** wire depth shells into the §7 outsider
  schedule (not global `Sorts`); discharge purity⇒sort for parallel finals when
  `d > 7`. Root Lemma 6.2 / Thm 5.1 separator and pack depth ≤ `6320` are discharged.
  Unconditional `limsup D(n)/log₂ n ≤ 1830` remains open (`Limsup1830Residual` for
  `d > 603`); Batcher covers only `7 ≤ clog 64 n ≤ 603`.
  **Kernel-checked 1830-form (finite range, 2026-10-06):**
  `minimum_depth_le_1830_logb_of_batcher_range` — for every `1 < n` with
  `7 ≤ clog 64 n ≤ 603`, `D(n) ≤ 1830 log₂ n − 58657` (axioms: propext /
  Classical.choice / Quot.sound only; see `Chvatal1830Axioms`). Not limsup;
  stages are Batcher, not paper separators.

  **Build (2026-10-06):** **`lake build AKS`** green including **`PaperScrambleNumerics`** and **`ModuleABridge`**.
  Counting / decode-class track: **`AKS.Chvatal.ModuleA`**
  (pipeline Lemma 6.1 fail bound **`lemma61FailBound_onPipeline_of_decodeClass`**, Lemma 6.2 cell counting,
  **`ModuleACombinatorialObligation`**). Bridge / §7 API: **`AKS.Chvatal.ModuleABridge`**.
  **Fail-fraction / existence (2026-10-06, kernel-checked where noted):**
  **`not_ModuleACombinedFailFraction_m100_crude`**: nested-level pipeline factor **`lemma61_failFactor_pipeline`**
  plus F **`β`** at `(100,16,x=3/10)` is **not** `< 1` (proved lower bound **`α ≳ 4/5`**, **`β ≳ 43/100`**).
  **`ModuleACombinedFailFraction_m100`** is **kernel-checked** via **`moduleACombinedFailFraction_m100`**: pigeonhole
  uses **`lemma61_failFactor`** (one **`matrixOnesLevel`** cell per monotone matrix in
  **`lemma61FailBound_onPipeline_of_decodeClass`**, not **`m · lemma61_failFactor`**).
  **`moduleA_global_failFraction_add_lt_one`**: **`lemma61_failFactor + lemma62_failFactor` `< 1`** for all
  **`m ≥ 100`**, **`n ≥ 16`**; still needed for unrestricted global Lemma 6.1 with **`AvgRowOnesLeOne`** (false at
  **`m = 100`**).
  **`ExistsCombinatorialScrambleBF_onPipeline_of_ModuleA_m100`**: **unconditional** from
  **`ModuleACombinatorialObligation`** + **`hinner : F.inner = thirty`** (no separate **`hαβ`**).
  **`ModuleAPipelineBFImpliesScrambleSeparator_m100_discharged`**: given combinatorial pipeline B/F on one `σ` and
  **`CombinatorialToMatrixObligation`**, **`ExistsScrambleSeparator`** is kernel-checked (no separate `hRes`); compose
  with **`exists_combinatorialScrambleBF_onPipeline_of_ModuleA_m100`** at `(100,16)` when `g.m = 100` and `g.n = 16`.
  Legacy alias **`ModuleAPipelineBFImpliesScrambleSeparator_m100`** is still the Prop **`ExistsScrambleSeparator`**
  for older entry points that pass **`hRes`** explicitly.
  **Paper `m`:** crude **`lemma61_failFactor_pipeline (2^60) 16 < 1`** is false; F **`hclose`** at huge `jMax` remains
  open (**`PaperOrdinary_hclose_residual`**; see **`paperOrdinary_lemma62_jMax_gt_48`**).

  **Hypothesis ledger at `m = 100`, `n = 16`** (see [Params](../AKS/Chvatal/Params.lean),
  [ModuleANumerics](../AKS/Chvatal/ModuleANumerics.lean), [Lemma61](../AKS/Chvatal/Lemma61.lean)):

  | Item | Lean status |
  |------|-------------|
  | `hPeps` / geometry side (`hf2`, `hmF`, `hjMax48`, …) | **Discharged** on `params7Geometry` (`ModuleANumerics`, `ModuleA`) |
  | `invariant7` vs Lemma 6.1 Chernoff `hepsB` | **Impossible at `m=100`** — `not_invariant7_hepsB_m100`; **log-scale `m`** — `chernoff_loose_floor_le_eps`, `invariant7_chernoff_loose_m_gt_100` (`m ≳ 2·10^30` for loose `√(2/m) ≤ epsB`) |
  | `invariant7` vs worst-case fringe `hepsWorst` | **Impossible** — `not_invariant7_hepsWorst_f16` |
  | `invariant7` vs `(4e)/f`, `epsF_lemma62_lb` | **Impossible** — `not_invariant7_hepsF_ge_4e_f16` (+ numeric gap for `hepsF_ge_lemma62`) |
  | §4 `(4.2)` / `(4.5)` vs Chernoff-scale `ε` | **Incompatible** — `not_cond42_epsB_half_at_params7`, `not_cond45_epsF_three_hundred_at_params7` |
  | `htotal` / `havg` (global ∀ monotone `c`) | **Equivalent** and **false** — `not_TotalColumnOnesLeN_100_16`. **Not used** for pipeline B: **`DecodeMatrixClassObligation.standard`** + per-level `totalColumnOnesLeLevel_decodeColumnSums_atLevel` (`SortedColumnDecode`) |
  | Pipeline B at `(100,16)` | **`DecodeMatrixClassObligation`** → **`lemma61FailBound_onPipeline_of_decodeClass`** (union at **`matrixOnesLevel`**, factor **`lemma61_failFactor`**) → **`ExistsCombinatorialPropertyBOnPipeline`** |
  | `havg` for F | Still required for fringe cell Chernoff unless a narrower F-side class is packaged |
  | **Viable Thm 5.1 `P`** | **`theorem51Params_moduleA_f16`** — `εB = 1/2`, `εF = 300`, `δF = invariant7.deltaF`; Chernoff floors kernel-checked except **`ModuleA_epsF_lemma62_Certificate`** (`epsF_lemma62_lb ≤ 300`, value ≈ 3.81) |
  | `ExistsScrambleSeparator` at Module A `P` | **`ExistsScrambleSeparator_of_moduleA_and_bridge`** / **`_m100`** — needs **`hRes`** (residual separator) plus **`hExist`** (residual B∧F scramble) and **`hαβ`** (residual `α+β`); B-side counting is kernel-checked on decode class. **`ExistsScrambleSeparator_params7Geometry_f16_*`** updated accordingly |

  **1830 depth budget:** `SeparatorConds params7 invariant7` and `totalDepth` / `network_depth_le_1830_of_sorting1830Obligation` remain tied to **tiny** `invariant7` scalars (`chvatal71`-scale). Module A Chernoff `P` does **not** satisfy those §4 inequalities; plugging `theorem51Params_moduleA_f16` into `LocalSeparatorQuality.ofTheorem51 invariant7` would break outsider induction. Closing `Sorting1830Obligation` still needs either reconciled constants or a split between matrix-existence `P` and schedule `InvariantParams`.
  **Remaining for unconditional `D(n) ≤ 1830 log₂ n`:** (1) optional link `HasMatrixPropertyB pack.net` when
  `wirePerm = 1` (semantic = comparator exec),
  (2) per-stage `PreferNonStageObligation` / `Params7AbstractTrajectoryObligation` from
  Thm 5.1 routing, (3) real root/ordinary separator nets at paper depths for general
  `d ≥ 7` (partial: **`of_batcher903_emptySeparators_d7`** at `StageDepthBudget.ofPaper`).
  **Unconditional 1830 is still open** (`network_depth_le_1830_of_sorting1830Obligation`
  remains hypothesis-dependent).


## Chvátal 1830: modular remaining-work ledger (2026-10-06)

Reference: `docs/dcs-tr-294.pdf` (text extraction is garbled; decode `/NN` tokens as
ASCII, low codes are cmmi Greek: 11 α, 14 δ, 15 ε, 22 ν, 25 π, 27 σ, 31 τ, 33 ω).
**Rule: follow the paper's proof structure.** Kernel-checked = ✔. `[me]` needs
careful analysis; `[delegate]` is mechanical once statements are fixed. Delegated
(Haiku) output has repeatedly contained `sorry`s or `rfl` tautologies reported as
success: always rebuild, `grep sorry`, and `#print axioms` before trusting it.

**Audit of the abstract model vs. the paper.** The `Placement`/`perm` model is
faithful if a Lean "register" is a *key* identified by its initial index, `perm` is
its address (the input rank map), and the placement is data-dependent; then
`perms (t+1) = perms t` is correct. The paper's wire sets of nodes are
input-independent (wires stay put, keys move). The final 2^42 blocks are made
contiguous by one global relabeling of the wires (inputs are arbitrary). The
constant `58657` matches the paper's Theorem 1.1 (`N ≥ 2^78`).

### A. Separators for every bag size (paper §5–6)

| # | Piece | Status |
| --- | --- | --- |
| A1 | Property B for general `n`: **✔** `DecodeMatrixClassObligation.standard` is already general in `(m,n)`; used in `ExistsScrambleSeparator_general` | ✔ |
| A2 | Claim (ii): tops counting + binomial estimates ([Lemma62TopsCount](../AKS/Chvatal/Lemma62TopsCount.lean), [Lemma62TopsAnalytic](../AKS/Chvatal/Lemma62TopsAnalytic.lean)) | ✔ |
| A3 | Two-sided geometric tail sum ([GeomTail](../AKS/Chvatal/GeomTail.lean)) | ✔ |
| A4 | Per-`s` tail and ratio bounds: **✔** `p(s) ≤ C(n,s)(e j s/(nT))^T` ([Lemma62Tail](../AKS/Chvatal/Lemma62Tail.lean)); `key_right`, `ratio_left/right`, `gfun_sum_le_G1` (`Σ_{s≤n} g(s) ≤ (1+e^-5)/(1-e^-5) G1(b)`) and `pbound_le_gfun` ([Lemma62Ratio](../AKS/Chvatal/Lemma62Ratio.lean)), for `n ≥ 16`, `f ≥ 1.7e10`, `j ≤ (128/4095) f n`; integrality of `ε_F j` and evenness of `f` not needed | ✔ |
| A5 | Event-E bound per `E`: **✔** `fail_prob_at_E` (`|badSetF j| ≤ 1.025 (3/10)^E |Scramble|`, [Lemma62FailE](../AKS/Chvatal/Lemma62FailE.lean)) from the tops reduction ([Lemma62FailReduce](../AKS/Chvatal/Lemma62FailReduce.lean)), the closed tops count, the tail sum (incl. `⌊2εj/f⌋ = 0`) and `x ≤ 3/10` | ✔ |
| A6 | Rigorous `x ≤ 1/4 ≤ 3/10` for all `j` (`xval_le_three_tenths`, [Lemma62Numerics](../AKS/Chvatal/Lemma62Numerics.lean); `n` cancels via `u = j/(fn)`) | ✔ |
| A7 | Assembly: **✔** (2026-10-07). Corrected `HasPaperPropertyF` (tie `totalColumnOnes c = j`; the old `HasCombinatorialPropertyF` was false for every `σ` once `m ≥ f+1`), rounding to multiples of `1/ε` and summing `E ≥ 1` (fail fraction `≤ 0.44`, [Lemma62Round](../AKS/Chvatal/Lemma62Round.lean)), corrected F-bridge to the pack ([Lemma62Bridge](../AKS/Chvatal/Lemma62Bridge.lean)), pigeonhole with pipeline B (`< 1/100`): `ExistsScrambleSeparator_general` ([GeneralSeparator](../AKS/Chvatal/GeneralSeparator.lean)) for every `ScrambleGeometry` with `f ≥ 1.7e10`, `δ_F ≤ 128/4095`, `ε_F ≥ 1/(8e7)`. Still needed to *use* it: build `Theorem51Params g` for each `g` (A8: `ε_F` floors, `4e/f`, `ε_B` bound) | ✔ |
| A8 | `Theorem51Params g` for every geometry: **✔** ([GeneralParams](../AKS/Chvatal/GeneralParams.lean)): `epsF_floor_general`, `four_e_div_le`, `epsB_general` (`m ≥ 2^59`), `epsB_root_general` (`m ≥ 2^79`), `theorem51Params_general`, `ExistsScrambleSeparator_ordinary/_root` | ✔ |
| A9 | Scaling a template into `m ∈ (2^59, 2^60]` with `f > 1.7e10`, even ([GeometryScale](../AKS/Chvatal/GeometryScale.lean)) | ✔ |
| A10 | The four paper templates (§5) satisfy `m' < 2^37`, `f0 ≥ 4095` (needs the flow table B1) | open `[delegate]` |
| A11 | Small bags (≤ `2^64` wires): node network `bitonicNetwork a`; it sorts fully so the separator guarantees are trivial. Needs the node-separator interface (B7) | open `[me]` |
| A13 | **Two-sided Property B/F.** Lean's semantic B/F count only the largest keys; a block can be polluted from both sides. Choose `σ` with B, F for both `σ` and its flip `r ↦ m−1−r` (failure fractions `2·(0.01+0.44) = 0.90 < 1`) and prove flip-symmetry of `semanticExec` | open `[me]` |
| A12 | Root separator (`m = 2^79`, root `ε_B`) for general `n`: **✔** `ExistsScrambleSeparator_root` | ✔ |

### B. The actual network (paper §3, §4)

| # | Piece | Status |
| --- | --- | --- |
| B1 | Integer flow table `flowUp`/`flowDown` over the rational scheduler, with the send identity `a = π + kτ` (`allocation_eq_flowUp_add_flowDown`, [FlowTable](../AKS/Chvatal/FlowTable.lean)); table confirmed against the paper by the author (pp. 7–9) and by exact Python checks for `d = 14, 15, 20, 30` | ✔ |
| B2 | Flow table: send identity (`t+1 ≤ t_f`), conservation, instantiation for `levelSchedule7`, and natural-number sizes `flowSizes7 d hd : FlowSizes d (tf7 d)` ([FlowSizes7](../AKS/Chvatal/FlowSizes7.lean); integrality, evenness of `up`, the `t = 0, 1` special steps). Corrections found while proving: rising-top exponent is `e ≥ 6` (not 8), `τ` interior is `c(2^24−1)/2^30` | ✔ |
| M2′ | **Resolved (2026-10-07).** Paper (4.2) ends with `μδAk/ν` (author-confirmed; (4.5) matches Lean). Lean's `Cond42` had `μδ/(Akν)`, assuming a fair-density send-up. Fixed: `Cond42`, `cond42_coeff_form`, `cond42_scaled`, `lemma43_of_sources` and the order-0 children bound in `StageKernel`/`PlacementStep`/`RoutingFromP`/`StageDynamics`/`SeparatorContract` now use the worst case `μ δ k A² c(l−1,t)`; the old fair-density derivation (`fromChildren0_of_cover`) is weakened to it. `cond42_params7` and the paper-ordinary version still hold (exact check: `LHS/μ = 0.960` at `ε_B = 1.25e-8`). Consequence: the real network only has to supply `fromChildren ⊆ ⋃ child registers` (children part) and the parent-side Property B/F bounds (B7) — no goods-first rule or `c/Q` send budget | ✔ |
| B3 | Wire sets over time: **✔** ([WireFlow](../AKS/Chvatal/WireFlow.lean)). `wireSets F t` from any `FlowSizes F` (sorted-order splitting: first/last `up/2` positions go up, middle cut into 64 blocks), with `wireSets_card`, `wireSets_disjoint`, `wireSets_complete`, `wirePlacement`, and the destination characterisation `mem_wireSets_succ` | ✔ |
| B4 | Wire sets need not be contiguous at `t_f`: use generalized comparators and **✔ `Untangle.untangle`** ([Untangle](../AKS/Sort/Untangle.lean): a generalized network sorting into any fixed output order τ yields a standard network of equal greedy depth that sorts; supersedes the depth-`k` `KnownPermutation` correction). Remaining: generalized-network versions of the stage nets (embedding packs along arbitrary bijections) | partly ✔ `[me]` |
| B5a | `physicalPackNet`: standard network realizing the sort–scramble–sort pack on a node's wires (second column sort relabeled through the scramble); `physicalPackNet_exec` (= semantic output ∘ `wirePerm`), row-region counts agree, depth `≤ 2·bitonicDepthBudget` ([PhysicalPack](../AKS/Chvatal/PhysicalPack.lean)) | ✔ |
| B5b | `stageNet`: heterogeneous node networks on sorted wire lists, `stageNet_exec_inside`, `stageNet_outside`, `stageNet_depth_le` ([StageNet](../AKS/Chvatal/StageNet.lean)) | ✔ |
| B5c | Assembly: `nodeNet` per node (physical pack with scaled-template geometry and `σ` from `ExistsScrambleSeparator_*`, or `bitonicNetwork` for small bags); the full network `stages 0..t_f−1 ++ final sorters`; depth `≤ totalDepth d` | open `[me]` |
| B6 | Execution-defined placement: for an input `v` (perm), the keys on each node's wires after `t` stages; `perm` = `v`; `fromParent`/`fromChildren` = keys on the down/up wire blocks | open, core `[me]` |
| B7a | Lemma 4.2's sorted-window counting: in the sorted order of a node's keys those addressed below child `j` form a contiguous run, so a block of the sorted order has few keys not addressed below child `j` | open, core `[me]` |
| B7b | Property B/F (two-sided, A13) on the real output give `hBadSend0` and `hFringeSend`; children part from `fromChildren ⊆ ⋃ child regs` + P at the children | open, core, main research risk `[me]` |
| B8 | Induction to `t_f`, with the exceptional root separator `ε_*` at `t = 0` | open `[me]` |

### C. Assembly

| # | Piece | Status |
| --- | --- | --- |
| C1 | Monotone parallel final on block-separated / rank-pure input ([FinalPurity](../AKS/Chvatal/FinalPurity.lean)) | ✔ |
| C2 | Zero order-2 strangers at `t_f` ⇒ rank-pure level-(d−7) blocks | open `[me]` |
| C3 | Assemble `Sorting1830Obligation` and `Sorts` for the real network | open `[me]` |
| C4 | From `64^d` to all `n`, and the `d > 603` limsup | conditional versions exist; routine |

Critical path: `A4 → A5 → A6/A8 → A7 → A12` and `B1 → B2 → B3 → B4 → B5` are
independent; `B6 → B7 → B8 → C2 → C3 → C4` needs both. The two real research risks
are B7 (Property B/F ⇒ send bounds) and B6 (placement from execution).
Already done: depth accounting, abstract scheduler/outsider induction, pack depths,
parallel-final depth.

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
