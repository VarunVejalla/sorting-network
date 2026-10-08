# chvatal-1830

A self-contained Lean 4 / Mathlib formalization of

* `SortingDepth.minimum_depth_le_1830_logb` — for every `n ≥ 64^7`,
  `D(n) ≤ 1830 · log₂ n − 58657`;
* `SortingDepth.limsup_minimum_div_logb_le_1830` — `limsup D(n)/log₂ n ≤ 1830`,

where `D(n)` (`SortingDepth.minimum n`) is the minimum depth of a comparator network sorting
`n` wires. Both are in `AKS/Bounds/Chvatal1830Final.lean` and depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

The proof follows V. Chvátal, *Lecture Notes on the New AKS Sorting Network*, DCS-TR-294 (1992)
(`../docs/dcs-tr-294.pdf`), §3–§7; `LEDGER.md` records how it was assembled. The central object is `Chvatal.chvatal_sorter_exists`
(`AKS/Chvatal/RealSorter.lean`): for every `d ≥ 14` a sorting network on `64^d` wires of depth at
most `totalDepth d = 6320 + (3d − 21)·3660 + 903` (`= 10980 d − 69637`). For `7 ≤ d ≤ 13`
full-wire bitonic sorting is used instead; both are restricted to `n` wires with
`d = ⌈log₆₄ n⌉`, which gives the padded form `1830 log₂ n − 58657`.

## Building

```
cd chvatal-1830
lake build
```

The package shares the Mathlib checkout of the enclosing repository (`packagesDir := "../.lake/packages"`).
Its own modules were verified to build with `lake build` (3025 jobs), which includes
`AKS/Bounds/Chvatal1830Axioms.lean`: `#guard_msgs` checks that both headline theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`. A first build compiles the ~100 modules (about 30k lines).

## Layout

`AKS/` holds the modules (names kept identical to the main repository). Besides `Chvatal/`, it contains
only the shared basics the proof needs: `Sort/` (comparator networks, depth, 0-1 and permutation
principles, untangling), `Bitonic/` (Batcher sorter and its depth), `Halver/` and `Bags/` (a few
definitions/numerics), `Misc/Fin.lean`.

### Proof map (`AKS/Chvatal/`)

**A. Separators (paper §5–§6).** `Params`, `Theorem51(Core)`, `GeneralParams`, `GeneralSeparator`,
`Lemma61`, `Lemma62*` (Chernoff, tops counting, tails, ratios, failure reduction, rounding),
`Lemma63`, `PropertyBF`, `RowScramble`, `MatrixBridge`, `SortedColumnDecode`, `ModuleA*`,
`PaperScrambleNumerics`, `PhysicalPack` (the physical sort–scramble–sort network),
`PackSpec`, `FlipSpec`, `NodeSpec` (two-sided node guarantee), `NodeGeom` (geometry per node type),
`SeparatorDepth`.

**B. The tree network (paper §3–§4).** `Tree` (bags, outsiders), `FlowTable(7)`, `FlowSizes(7)`
(integer flow table), `Schedule7`, `Scheduler*`, `SendSchedule`, `WireFlow`, `StageNet`,
`ExecPlacement` (execution-defined placement), `NodeKeys`, `StrangerBounds`,
`Wires31`, `Lemma41Real`, `BadSendReal`, `FringeSendReal`, `OutsiderInvariant/Lemmas/Induction`,
`StageKernel`, `StageDynamics`, `PlacementStep`, `RoutingFromP`, `SeparatorContract`,
`ChildSend`, `StageCountsFill`, `AbstractPlacement`.

**C. Assembly (paper §7).** `KernelSetup` (the invariant parameters `invariantReal`),
`BadSendField`, `FringeSendField`, `RealKernel`, `RealNets` (per-node networks, `RealSpecs`),
`RealInduction` (root step, induction, purity at level `d − 6`), `RealPurity`, `RealBlocks`
(rank-pure level-`(d − 7)` blocks), `FinalSorts` (final block sorters + untangling to a
standard network), `RealNetwork` (stage concatenation, depth), `RealSorter`, `DepthSkeleton`
(`totalDepth`, the padded inequality).

## Provenance

These files were developed in the surrounding repository's `AKS/Chvatal/` and `AKS/Bounds/`
(see `../docs/research-index.md` for history); this folder is the cleaned extraction. Older,
no-longer-needed scaffolding (abstract trajectories, finite-range Batcher assembly, the
`Sorting1830Obligation` bundle) is kept, unbuilt, under `../archive/chvatal-scaffolding/`.
