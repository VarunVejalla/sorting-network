# chvatal-1830

A self-contained Lean 4 / Mathlib formalization of

* `SortingDepth.minimum_depth_le_1770_logb` — for every `n ≥ 64^7`,
  `D(n) ≤ 1770 · log₂ n − 56497`;
* `SortingDepth.limsup_minimum_div_logb_le_1770` — `limsup D(n)/log₂ n ≤ 1770`,

where `D(n)` (`SortingDepth.minimum n`) is the minimum depth of a comparator network sorting
`n` wires. Both are in `AKS/Bounds/Chvatal1830Final.lean` and depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

The proof follows V. Chvátal, *Lecture Notes on the New AKS Sorting Network*, DCS-TR-294 (1992)
(`../docs/dcs-tr-294.pdf`), §3–§7; `LEDGER.md` records how it was assembled. The central object is `Chvatal.chvatal_sorter_exists`
(`AKS/Chvatal/RealSorter.lean`): for every `d ≥ 14` a sorting network on `64^d` wires of depth at
most `totalDepth d = 6320 + (3d − 21)·3540 + 903` (`= 10620 d − 67117`). For `7 ≤ d ≤ 13`
full-wire bitonic sorting is used instead; both are restricted to `n` wires with
`d = ⌈log₆₄ n⌉`, which gives the padded form `1770 log₂ n − 56497`.

## Building

```
cd chvatal-1830
lake build
```

The package shares the Mathlib checkout of the enclosing repository (`packagesDir := "../.lake/packages"`).
The promoted pruning checkpoint passed `lake build` (3009 jobs) and the explicit
`AKS.Bounds.Chvatal1830Axioms` target (3008 jobs) on 2026-10-09. Both headline
modules freshly compiled; their guarded axiom checks allow only `propext`,
`Classical.choice`, and `Quot.sound`. See [BUILD_STATUS.md](BUILD_STATUS.md).

The package contains **88 Lean files, 834 source declarations, and 13,872 physical
lines**, including comments and whitespace. See
[the source inventory](../docs/chvatal-proof-inventory.md) for the breakdown and
further consolidation opportunities. The converged declaration graph contains 1,060 compiled declarations
(943 reachable, 117 unreachable) and 8,603 distinct dependency
edges. Generated helpers make this declaration count larger than the written
source count. The deletion loop removed 20 written declarations and 136 lines;
remaining candidates require proof changes rather than straightforward deletion.

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
(see `../docs/research-index.md` for history); this folder is the cleaned extraction. Older,
no-longer-needed scaffolding (abstract trajectories, finite-range Batcher assembly, the
`Sorting1830Obligation` bundle) is kept, unbuilt, under `../archive/chvatal-scaffolding/`.
