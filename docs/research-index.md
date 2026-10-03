# Sorting-network research index

Local review: 2026-10-03. This index describes the checked-out sources, including
the local Paterson work, rather than just the upstream clone or September handoff.

## Objective and current result

The active target is a smaller upper bound on
`limsup_{n -> infinity} D(n)/log_2 n`, where `D(n)` is minimum binary-comparator
sorting-network depth. A constant for natural logarithms is the base-two constant
divided by `ln 2`.

The best complete bound currently formalized in this repository is
[`SortingDepth.minimum_depth_le_million`](../AKS/Bounds/Paterson.lean):

```text
SortingDepth.minimum n <= 10^6 * Nat.clog 2 n.
```

`SortingDepth.minimum` defines `D(n)` as the minimum over sorting networks.
[`SortingDepth.limsup_minimum_div_logb_le_million`](../AKS/Bounds/Paterson.lean)
formally derives `limsup D(n)/log_2 n <= 10^6`, accounting for the ceiling
logarithm. This combines the proved full-support Paterson halver with the
prefix-doubling separator and the established Seiferas bag scheduler. It is
a complete first Paterson-based bound, not the refined Paterson bag theorem
or an improvement over published sorting bounds. The matching family and
network are selected classically; this is an existence bound, not an
executable search algorithm.

The coefficient certificate is `999189 = 14 * 71370 + 9 < 10^6`.
Parameters: `A = 397/50`, `gamma = 1/63`, `epsilon = 89/5000`,
`nu = 8203/10000`. The underlying full-support halver has error `89/35000`
and depth at most 5490. Every finite-size and cleanup contribution in the
million bound is covered by the complete existing scheduler proof.

The original `network` and its old bound remain in `AKS/Seiferas.lean`.
The previous executable `upperNetwork` with coefficient `102 * 10^62`
remains in `Bounds/Upper.lean`. The smaller five-level numbers below are local
bounds and arithmetic certificates; they do not yet establish the refined
7000 target for `D(n)`.

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

## Rounded Paterson implementation in progress

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
| Rounded size recipe | [Schedule](../AKS/Paterson/Schedule.lean) | 32-lattice subtree totals, full-bag size bounds, fringe coverage, and routing cardinality identities. These are arithmetic identities; the global allocation is not constructed yet. |
| Root purity and sort cost | [Root](../AKS/Paterson/Root.lean), [TightDepth](../AKS/Bitonic/TightDepth.lean) | At a sufficiently small root capacity, the invariant implies zero deepest strangers from level six. Given explicit region size bounds, the top region has fewer than `2^33` wires and its scattered bitonic sort costs at most 561. No forest splitting correctness theorem yet. |
| Arbitrary virtual padding | [Padding](../AKS/Paterson/Padding.lean) | Both directional supported contracts survive restriction with virtual maxima/minima, without additive error. |
| Concrete partial-bag gadget | [PatersonRefinement](../AKS/Separator/PatersonRefinement.lean), [PatersonPartial](../AKS/Separator/PatersonPartial.lean) | Four refinement levels cost 726; the actual-size first split and two padded half refinements cost 989, retain the large-cohort first contract, and satisfy both directional half refinement estimates. The larger partial-tail error fits the bottom-level arithmetic budget. Whole partial-bag preservation remains open. |
| Proposed operation counts | [Accounting](../AKS/Paterson/Accounting.lean) | `T(k) = 13*ceil(k/2)` overcomes initial capacity growth. The proposed cost `989*T(k) + 561*k` is at most `7000*k` for `k >= 613`. These are arithmetic theorems, not sorting theorems. |
| Kernel audit | [Axioms](../AKS/Paterson/Axioms.lean) | Guarded axiom checks on concrete transition, padding, partial gadget, root bounds, and accounting. Only the standard Lean/Mathlib axioms appear. |

### Remaining global obligations

1. **Cold storage and allocation.** Construct the complete rounded placement
   with explicit cold storage, parity, full levels, partial levels, and root
   flow. Prove its actual cardinalities match `scheduledSubtree` and the
   routing identities. `Stage.route` alone does not implement this scheduler.
2. **Rank balance.** Instantiate the checked disjoint-cohort and subtree
   estimates with the scheduler's actual native intervals and cold-storage
   deficits to obtain `ChildBalance` at every interior transition.
3. **Partial-level invariant.** Combine the actual first split with the two
   padded refinement estimates into whole-bag filtering, then prove the
   boundary transition where no descendants contribute.
4. **Root/forest transition.** Prove the sorted top region can be split into
   independent smaller trees while retaining the required invariant and
   storage constraints. Deep rank purity alone does not prove this.
5. **Termination and final sorting.** Build the recursive network, establish
   sortedness, and justify its actual stage and root-sort counts. Include
   startup, terminal cleanup, and all extra costs in the accounting.
6. **Minimum depth and limsup.** Apply the existing restriction and asymptotic
   infrastructure to the completed family, with all boundary costs covered.

The candidate coefficient is `989*(13/2) + 561 = 6989.5`. This is a
**conditional construction budget**, not a theorem about `D(n)` or its limsup.
Even the proved eventual inequality in `Accounting.lean` bounds only the
proposed operation count. The best complete sorting bound remains `10^6`.

The next proof should implement cold storage and global allocation, while
finishing the whole partial-bag contract in parallel with that mathematical
work. The old Seiferas parameter interface cannot simply be instantiated with
these parameters; `patersonNu_fails_current_hC3` records an obstruction.

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
lake build AKS.Bounds.Axioms
lake build AKS.Bounds.PatersonAxioms

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
`Bounds/Upper.lean` file and selected Paterson network in `Bounds/Paterson.lean`,
alongside the two named analytic Paterson files in `Bags/`. Both `network`
and `SortingDepth.upperNetwork` remain computable definitions.

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
