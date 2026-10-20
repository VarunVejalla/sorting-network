# Best checked upper bound

A self-contained Lean 4 / Mathlib formalization of

* `SortingDepth.minimum_depth_le_78975_logb` — for every `n ≥ 16^12`,
  `D(n) ≤ 789.75 · log₂ n + 3159`;
* `SortingDepth.limsup_minimum_div_logb_le_78975` — `limsup D(n)/log₂ n ≤ 789.75`
  (and `limsup_minimum_div_logb_le_800`),

where `D(n)` (`SortingDepth.minimum n`) is the minimum depth of a comparator network sorting
`n` wires. They are in `AKS/Bounds/Sub800Final.lean` and depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound` (guard: `AKS/Bounds/Sub800Axioms.lean`).

## The 789.75 construction (UB-31, `AKS/Sub800/`)

Paper proof: [`notes/sub800/R1-PROOF.md`](notes/sub800/R1-PROOF.md); module map:
[`notes/sub800/LEAN-PLAN.md`](notes/sub800/LEAN-PLAN.md); parameters and certificates:
[`notes/sub800/README.md`](notes/sub800/README.md). It keeps Chvátal's invariant and tree
(paper DCS-TR-294, `../../docs/dcs-tr-294.pdf`) at `(k, A, ν) = (16, 32, 1/8)` and changes three things:

* **Flow table, design P.** Each node sends `π/2 + G − r*c` to its end children and spreads
  `2r*c − G` over the interior children, where `G` is the node's deficit
  (`R1Design`, `R1Table`, `R1Inv*`, occupancy `R1Occ`).
* **Bulk: the walk bound.** Property B of the two-round separator without Lemma 6.1's union
  over inputs, proved by negative association and Ville's inequality (`NegAssoc`, `Ville`,
  `Round2*`, `Round1*`, cells `R1Cells`/`R2Cells` as kernel-checked data via `ExpCert`,
  `CellCheck1`, `CellCheck2`); this admits rows `< 2^26`.
* **Fringe: padded separator at `δ_F = 1/8`.** The two-round separator on an `(m+1) × n`
  rectangle with one partial dummy row (`PaddedSeparator`, `PaddedFringe`, `BaselineFringeD`,
  copied from `../experiments/tapered`) and the per-E fringe route (`F2D*`) for the two
  classes `f = 7934`, `f = 406109` (`Fringe7934`, `Fringe406109`).

The tree induction (`R1Sched` … `R1Final`, `R1Subtree`) follows the package's Chvátal kernel
(`AKS/Chvatal/`); node networks and their specifications are in `R1Sep`, `R1Geom`, `R1Nets`.
`R1T.r1_sorter` gives, for `d ≥ 12`, a sorter on `16^d` wires of depth
`2709 + 1053 (3d − 15) + 136 = 3159 d − 12950` (root separator 3·S(42), ordinary nodes 3·S(26),
final layer 136); restricting to `n` wires with `d = ⌈log₁₆ n⌉` gives the headline
(`R1Main.lean`).

## The underlying Chvátal 1419 modules

The previous best, `limsup ≤ 1419` (`SortingDepth.limsup_minimum_div_logb_le_1419` in
`AKS/Bounds/Chvatal1830Final.lean`, guard `AKS.Bounds.Chvatal1830Axioms`), still builds here because
the 789.75 proof reuses its modules; the standalone package is `../alternatives/chvatal-1419`. The
rest of this README describes those modules.

## Two-round separator

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
cd upper-bound/best
lake build
lake build AKS.Bounds.Sub800Axioms
lake build AKS.Bounds.Chvatal1830Axioms
```

The package shares the Mathlib checkout of the repository root. All targets succeed (3584 jobs, 2026-10-19). `Sub800Axioms` accepts only `propext`, `Classical.choice`, `Quot.sound` for the
789.75 headlines and `R1T.r1_sorter`; `Chvatal1830Axioms` does the same for the 1419 headlines and
`Chvatal.twoRoundSeparatorExists`. Import targeted Mathlib modules, never bare `import Mathlib`: loading all of
Mathlib costs about 60 s per file (against about 15 s for `Mathlib.Tactic`) and multiplies memory in parallel builds. See [BUILD_STATUS.md](BUILD_STATUS.md).

## Layout

`AKS/` holds the modules (names kept identical to the main repository). Besides `Chvatal/`, it contains
only the shared basics the proof needs: `Sort/` (comparator networks, depth, 0-1 and permutation
principles, untangling), `Sub800/` (the 789.75 construction), `Bitonic/` (Batcher sorter and its depth), `Halver/` (two shared modules), `Bounds/` (the minimum-depth definition,
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

The generic closed-certificate interface for independent global upper bounds is
[`AKS/Bounds/Certificate.lean`](AKS/Bounds/Certificate.lean). The separate
[`../contributions/README.md`](../contributions/README.md) package demonstrates how to submit a
different construction against the same comparator-network model and minimum-depth definition.
