# Roadmap for `experiments/runaware` (current best: 1770)

Updated after the generic-parameter scoping. See `DESIGN.md` for the run-aware first sort and
`../../backlog/` for ideas that are parked.

## What is worth doing (honest numbers)

| step | gain | status |
|---|---|---|
| run-aware first sort, uniform `s = 29` | 1770 → ~1553 (−12%) | design done; block sorter proved in scratch (`scratch/runaware/Block5.lean`); divisibility + `GenNetwork` composition in progress |
| smaller-fringe lemma, one round only | ≈ 0 | at (6,12,6) the bulk condition (4.2) pins `L ≈ 58` (margin 1.18) whatever F allows |
| re-parameterize to (5,10,4) / (6,11,5) / (6,10,4) | ≈ −1% (1692 / 1683 / 1700 vs 1711 in script accounting) | **dropped**: needs a generic flow table / schedule / `NodeShape` (1500+ lines, high risk) |
| two-round separator (3 sorts, `m ≈ 2^42`) + F at `f ≈ 2^17` | → ~1354 (conditional); ~1300 with run-aware | blocked on the two-round F contract (open joint-witness problem), plus a formal Bernstein second-scramble lemma |

`(5,10,4)`: stage count per level (x+y)/z = 15/4 (not an integer, so the 3-stages-per-level scheduler,
`tf7 = 3d−20`, `omega = (t+2)/3`, does not carry over); `(6,11,5)`: 17/5; only `(6,10,4)` has an
integer count (4). The current instance is special: `k = 64`, `A = 4096 = k²`, `ν = 1/k`, so every
capacity is a power of 64 and `NodeShape` (`64^(g+1)`, `16777215·64^(1+f)`, `capacityRatio = 64^6`)
depends on it.

## Where the numbers are baked in (from the scoping read)

* Flow table / schedule: `Schedule7` (capacity, `capacityRatio`, `tf7 = 3d−20`, `meetLevel7 = d−6`),
  `FlowTable` (literals `1/64`, `4096·64`, `4095`), `FlowSizes7` (`NodeShape`, `flowA7/flowUp7/flowDown7`).
* Geometry: `NodeGeom` (window `2^58 < m ≤ 2^59`, `n ≥ 16`, `f ≥ 8.5·10⁹`, small cutoff `2^63`,
  templates `(64,0,1)`, `(2^30,32,2^24−1)`, `(137438953470,4095,2147483520)`, `(8192R+8190,4095,128R)`),
  `GeometryScale` (`exists_pow_scale`, `scaled_fringe_big_ratio`).
* Numerics: `StageKernel` (`invMu = 1023/2^40`, `invDelta = 1/5.3e9`, `invEpsB = 1/5.9e7`, `invEpsF = 1/8.6e7`),
  `KernelSetup`, `GeneralParams`, `Theorem51Core`, `Lemma62*` (`8.5e9`, `86e6`), `BadSendField`, `FringeSendField`.
* Assembly: `RealNets` (`depthBound = 6320 / 3540`, `2^63 → 2016`), `RealNetwork`/`RealSorter`/`DepthSkeleton`
  (`3d−21`, `903`, `10620d − 67117`), `Chvatal1830Final`.
* Already generic: `Tree`, `WireFlow`, `RealBlocks`, `RealInduction`, `ExecPlacement`, `StageNet`,
  `BadSendReal`, and nearly `FinalSorts`.

The L = 58 change (commit 82d8387, 22 files, +200/−188) touched only the window/threshold, the
Property-F constants and the depth constants; not the flow table, schedule or `NodeShape`.

## Work order

1. Run-aware (this package): divisibility `2^s ∣ f, b` and `2^s' ∣ up/2, down`; `GenNetwork` stage
   composition + `Untangle`; then `X` with inter-stage permutations, chunk invariant,
   `Π_t` construction, switch `RealNets` to `physicalPackNetBlock`, depth skeleton `3540 → 3105`.
2. Two-round: wait for the F-contract analysis (`../fringe-single-round/NOTES.md`); only if a route
   at `f ≈ 2^17` is credible, formalize bulk (hypergeometric MGF comparison + Bernstein, second
   scramble lemma at exact mass) and the F contract, then redo scaling and small-node cutoffs.
3. Promotion rule: nothing moves to `upper-bound/best` until the full package builds, the axioms
   guard passes and the headline theorem is restated with the new constant.
