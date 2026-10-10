# Sorting-network research index

## Current package layout (2026-10-10)

- `upper-bound/best`: current Chvátal endpoint, coefficient 1770. Its relocated
  full build and both headline guards passed on 2026-10-10.
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

The proposed smaller **one-round** fringe target is ruled out by a deterministic
adversary. The current route is a joint two-round fringe guarantee, paired with
a variance-sensitive bulk lemma. These are research arguments, not improved
kernel-checked endpoints. See [the obstruction](chvatal-fringe-obstruction.md)
and [the small-rank branch](chvatal-two-round-small-ranks.md).

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
