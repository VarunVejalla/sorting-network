# Best checked upper bound

A self-contained Lean 4 / Mathlib formalization of

* `SortingDepth.minimum_depth_le_1419_logb` — for every `n ≥ 64^7`,
  `D(n) ≤ 1419 · log₂ n − 43861`;
* `SortingDepth.limsup_minimum_div_logb_le_1419` — `limsup D(n)/log₂ n ≤ 1419`,

where `D(n)` (`SortingDepth.minimum n`) is the minimum depth of a comparator network sorting
`n` wires. Both are in `AKS/Bounds/Chvatal1830Final.lean` and depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

The proof follows V. Chvátal, *Lecture Notes on the New AKS Sorting Network*, DCS-TR-294 (1992)
(`../../docs/dcs-tr-294.pdf`), §3–§7; `LEDGER.md` records how it was assembled. The central object is `Chvatal.chvatal_sorter_exists`
(`AKS/Chvatal/RealSorter.lean`): for every `d ≥ 14` a sorting network on `64^d` wires of depth at
most `totalDepth d` (window `2^42 < m ≤ 2^43`, node depth 2838; `D(n) ≤ 1419 lg n − 43861`). For `7 ≤ d ≤ 13`
full-wire bitonic sorting is used instead; both are restricted to `n` wires with
`d = ⌈log₆₄ n⌉`, which gives the padded form `1419 log₂ n − 43861`.

## Two-round separator (new in this package)

The 1419 bound replaces the one-round separator by the two-round one
(sort, scramble `σ1`, sort, scramble `σ2`, sort; `PhysicalPack2`, `PackSpec2`, `PackNodeSpec2`).
The probabilistic existence `Chvatal.twoRoundSeparatorExists : TwoRoundSeparatorExists`
(`AKS/Chvatal/TwoRoundProof.lean`) is proved with three cases:
`f = 0` (`Bulk2Exists`, B2 only); `131040 ≤ f < 8.5·10⁹` (`F2Exists.exists_twoRound_mid`:
round-1 bulk B1, `F2SmallRank`/`F2R1` for `σ1`, bulk B2 and `F2R2n` for `σ2`, via the deterministic
reduction `F2Det.F2_both_orientations` and the parameters `F2Params.ofF`); `f ≥ 8.5·10⁹`
(old one-round Property F, `ExistsScrambleSeparator_twoSided_two`). New modules:
`Bulk2*`, `F2Defs`, `F2Det`, `F2SR`, `F2R1Fail`, `F2R2*`, `F2ParamsOf`, `F2Exists`, `TwoRoundHyp`, `TwoRoundProof`.

## Building

```
cd upper-bound/experiments/tworound-final
lake build
lake build AKS.Bounds.Chvatal1830Axioms
```

The package shares the Mathlib checkout of the repository root. Both targets succeed (3003 jobs);
the guard accepts only `propext`, `Classical.choice`, `Quot.sound` for the two headlines and
`Chvatal.twoRoundSeparatorExists`. See [BUILD_STATUS.md](BUILD_STATUS.md).

## Layout

`AKS/` holds the modules (names kept identical to the main repository). Besides `Chvatal/`, it contains
only the shared basics the proof needs: `Sort/` (comparator networks, depth, 0-1 and permutation
principles, untangling), `Bitonic/` (Batcher sorter and its depth), `Halver/` (two shared modules), `Bounds/` (the minimum-depth definition,
headline results, and guards), and `Misc/Fin.lean`.

### Proof map (`AKS/Chvatal/`)

**A. Separators (paper §5–§6).** `Params`, `Theorem51Core`, `GeneralParams`,
`Lemma61`, `Lemma62*` (tops counting, tails, ratios, failure reduction, rounding),
`Lemma63`, `MatrixBridge`, `SortedColumnDecode`, `PhysicalPack` (the physical sort–scramble–sort network),
`PackSpec`, `FlipSpec`, `NodeSpec` (two-sided node guarantee), `NodeGeom` (geometry per node type),
`SeparatorDepth`.

**B. The tree network (paper §3–§4).** `Tree` (bags, outsiders), `FlowTable(7)`, `FlowSizes(7)`
(integer flow table), `Schedule7`, `Scheduler*`, `WireFlow`, `StageNet`,
`ExecPlacement` (execution-defined placement), `NodeKeys`, `StrangerBounds`,
`Wires31`, `Lemma41Real`, `BadSendReal`, `FringeSendReal`, `OutsiderInvariant/Lemmas/Induction`,
`StageKernel`, `RoutingFromP`, `SeparatorContract`,
`ChildSend`, `StageCountsFill`.

**C. Assembly (paper §7).** `KernelSetup` (the numeric instance `invMu` etc.),
`BadSendField`, `FringeSendField`, `RealKernel`, `RealNets` (per-node networks, `RealSpecs`),
`RealInduction` (root step, induction, purity at level `d − 6`), `RealBlocks` (also holds `realNets_purity`)
(rank-pure level-`(d − 7)` blocks), `FinalSorts` (final block sorters + untangling to a
standard network), `RealNetwork` (stage concatenation, depth), `RealSorter`, `DepthSkeleton`
(`totalDepth`, the padded inequality).

## Provenance

These files were developed in the surrounding repository's `AKS/Chvatal/` and `AKS/Bounds/`
(see `../../docs/research-index.md` for history); this folder is the cleaned extraction. Older,
no-longer-needed scaffolding (abstract trajectories, finite-range Batcher assembly, the
`Sorting1830Obligation` bundle) is kept, unbuilt, under `../../archive/chvatal-scaffolding/`.
