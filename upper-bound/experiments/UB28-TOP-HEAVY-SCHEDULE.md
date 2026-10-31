# UB-28 top-heavy schedule screen

Status: **exact annealed count-process diagnostic; not an all-size bound.**
For a uniform random input and independent uniform matching schedule, the law
is invariant under independent slot permutations within each block. Matching
layers preserve this symmetry, and block splits preserve the child-block
subgroup. Thus the block-count matching and split kernels are exact for the
first-moment ensemble. The fixed-input width-2 singleton example does not
invalidate this annealed recurrence.

This replaces the constant
round count with a schedule that spends more random-matching rounds at the
largest scales, where the local first-moment exponent is most sensitive.

For `n=2^L`, use the same two offset passes at every dyadic scale `h` from 8
through `n/2`. At `h=8,16`, use 150 independent uniform matchings per offset.
For `h>=32`, let

```text
j = log2(n/2) - log2(h)   # distance from this scale to the top
r(h) = 260 if j is even, 20 if j is odd.
```

Below width 8, use the existing exact cyclic tail. The mean of `260,20` is
140 rounds per scale and there are two offsets, so the depth is
`280 log2(n) + O(1)`. Thus a proof of the probability gate would give
coefficient 280, below the target 300. The less aggressive `240,20` schedule
has coefficient 260 but a much smaller screened margin.

## Max-path screen

For a fixed final bad edge, the local first moment sums probabilities of
count trajectories. With fixed maximum round count, the number of local
count trajectories is `exp(O(log^2 n))`; its exponential-in-`n` rate is
therefore governed by the most likely trajectory. The exact finite max-plus
transfer in [`ub28-local-edge-maxpath.py`](ub28-local-edge-maxpath.py) uses all
count values at each supported block, but is currently practical only through
`n=128` for a central edge. For the `260,20` top-relative schedule at `n=128`,
the max-path rates `-log(P_path)/n` are 2.0033 at edge 14, 1.5751 at edge 30,
and 0.7996 at edge 62. The central edge is the hardest of these samples.

[`ub28-rate-grid.py`](ub28-rate-grid.py) continues from the exact width-16
table using only counts that are multiples of `h/16` at each larger width.
The coarse-lattice transfer retains only counts that are multiples of `h/16`
at each larger width, so every included feasible trajectory is realizable in
the exact count process. A rate below `ln 2` would therefore witness a
first-moment obstruction; a rate above `ln 2` is only a screen, since other
count paths are omitted. On the
central edge at `n=2^22`, the `260,20` schedule gives rate 0.81658, and at
`n=2^24` it gives 0.81651. These runs use 150 rounds for both anchor scales
`h=8,16`; for example, the `n=2^22` value is reproduced by:

```text
python upper-bound/experiments/ub28-rate-grid.py --log-n 22 --anchor-edge 126 \
  --anchor-rounds 150 --top-alternating-149-151 --top-high 260 --top-low 20
```

The CLI exposes `--anchor-rounds` separately because the later schedule's
`--rounds` value does not describe the finite `h=8,16` anchor. For the stronger
`280,20` schedule, the `n=2^22` rate is 0.87217. The `280,20` screen across
the four even edge residues
modulo 8 near the center ranges from 0.87217 to 0.87233; odd edges are sorted
for the sampled representatives by the final fixed odd-offset pass. At the
left boundary, sampled even edges have higher rates (edge 2: 6.78; edge 14:
1.54). This does not exhaust all dyadic phase histories.

The schedule sweep gives a depth/rate tradeoff on the same central edge at
`n=2^24`. Grid-16 rates are 0.64972 for `(200,20)`, 0.70531 for `(220,20)`,
0.76091 for `(240,20)`, 0.81651 for `(260,20)`, and 0.87217 for `(280,20)`.
The corresponding depth coefficients are 220, 240, 260, 280, and 300. Since
each grid path is feasible, the first value is evidence that `(200,20)` misses
the first-moment gate; values above `ln 2` do not prove the gate because
omitted paths may be more likely. Full-count max-path screens at
`n=128`, edge 62, give rates 0.78947, 0.79461, and 0.80454 for `(220,20)`,
`(240,20)`, and `(280,20)` respectively. These finite-width numerical rates
are not asymptotic bounds.

A uniform 70-round schedule has a misleadingly strong finite screen: at
`n=128`, the full-count max-path rate at edge 62 is 1.34223. The grid-16
asymptotic screen nevertheless has a feasible central path of rate 0.35783
for that schedule. This shows why the finite `n=128` rate cannot stand in for
the all-size gate. These screens use binary64 and remain diagnostic.

Implementation note: `ub28-count-process.expected_failures` accepts one
scalar round count, so it computes exact finite distributions only for a
constant-round schedule. The top-relative schedules above are implemented in
the max-path transfer; extending the exact probability recurrence to
scale-dependent rounds is straightforward but is not needed for these
max-path screens.

These values use binary64 log-binomial evaluations. They are not certified
rate bounds, and the fixed density lattice does not maximize over all count
trajectories. They support pursuing this schedule but cannot establish that
the full bad-edge rate exceeds `ln 2`.

### Edge-position smoke test (2026-10-24)

I ran the same grid-16 transfer at `n=2^20` for a few translated anchor
positions with the `(280,20)` top-relative schedule (`150` anchor rounds).
The rates were: left placement, edges `2,14,30`: `6.77461, 1.53955,
1.19704`; centered placement, edges `62,126`: `0.87357, 0.87243`; right
placement, edge `242`: `2.06413`. Every sampled feasible path remains above
`ln 2`, with the smallest margin about `0.1793` at centered edge126. The
left-edge results agree with the earlier `n=2^22` screen. This does not close
the proof gate: it samples only six edge/placement pairs and a subset of
count paths, so it gives no upper bound on the worst edge rate. The next
decisive step remains a certified outer Bellman bound over all profiles,
phases, and boundaries.

### Cell-Bellman refinement (2026-10-24)

In `ub28-pinsker-cell-bellman.py`, density-cell compression now retains the
maximum exact width-16 anchor log-weight in each cell instead of replacing
every feasible cell by zero. I also tested a proposed sharper generic
TV-to-relative-entropy bound and rejected it: for Bernoulli probabilities
`0.65` and `0.45`, `TV=0.2` but the relative entropy is about `0.0798`, below
the proposed `2*TV*atanh(TV) ~= 0.0811`. The script therefore keeps the
standard Pinsker bounds; no uncertified tightening remains.

Retaining anchor weights did not make the screen informative: for the
centered edge at `n=2^10`, the outer rate remains zero with both 4 and 8
density bins (the 8-bin anchor has 249,344 of 262,144 cells viable), and the
half-density terminal action is zero. Refining only the local kernel cannot
repair the Bellman relaxation: max-plus composition still chooses a fresh
underlying density independently at each visit to the same coarse cell. The next
algorithmic step is to carry nested subcells or an explicit continuous
density potential across scales, rather than spending more effort tightening
the same per-transition scalar bound. Commands:

```text
python upper-bound/experiments/ub28-pinsker-cell-bellman.py --log-n 10 --bins 4 --high 280 --low 20 --anchor-rounds 150 --kernel-refine 1
python upper-bound/experiments/ub28-pinsker-cell-bellman.py --log-n 10 --bins 8 --high 280 --low 20 --anchor-rounds 150 --kernel-refine 1
```

The reset is visible already in a 4-bin one-round matching kernel with
`kernel-refine=4`. A zero-cost coarse path begins
`(1,1) -> (0,1) -> (0,1)`, where cell `i` represents
`[i/4,(i+1)/4]`. On the first transition choose exact source densities
`(1/4,1/4)`; the zero-rate mean output is `(1/16,7/16)`, still in cell
`(0,1)`. The next zero-rate kernel step instead chooses source `(0,1/4)` from
that same cell and outputs `(0,1/4)`, also in `(0,1)`. The two consecutive
profiles differ, so this is not a realizable zero-cost path; the DP permits
it because it remembers only cell indices. This explicit witness identifies
the needed repair: the Bellman state must retain the actual within-cell
profile (or a certified potential that prices its movement).

The lost coordinate in this witness can be identified exactly: the sum of
the two block densities is conserved during every repeated matching round.
The first zero-rate step has source `(1/4,1/4)` and output
`(1/16,7/16)`, with total `1/2`. The next zero-rate step's chosen source
`(0,1/4)` has total `1/4`. Thus augmenting each repeated-pair Bellman state
with its exact pair total (or a certified interval for it) rules out this
specific reset path. This is a necessary local invariant to carry into the
full cone; it has not yet been shown sufficient, especially across offset
changes and block splits.

I added an optional `--pair-total-cells` Bellman mode that holds the total
density of each matched pair in one fixed interval throughout the repeated
matching stage. At `n=2^10`, 4 density bins, and 8 total intervals on `[0,2]`,
the full outer Bellman still returns rate zero (`half_density_action=0`). Thus
pair-total memory removes this specific witness but does not repair the
selected-cut relaxation; residual within-cell resets and loss of profile
correlations across offset changes remain. Reproduce with:

```text
python upper-bound/experiments/ub28-pinsker-cell-bellman.py --log-n 10 --bins 4 --high 280 --low 20 --anchor-rounds 150 --pair-total-cells 8
```

Combining both refinements does not repair the rate: at `n=2^9`, 8 density
bins plus 8 persistent-total intervals still gives `max_log_rate_upper=0`
and `half_density_action=0` (target `-ln 2`). This run is smaller than the
previous 4-bin, `n=2^10` screen but directly tests the stronger state
partition. The max-plus relaxation still forgets within-cell values and
cross-offset profile correlations; adding more pair-total intervals alone is
not a promising next experiment.

```text
python upper-bound/experiments/ub28-pinsker-cell-bellman.py --log-n 9 --bins 8 --high 280 --low 20 --anchor-rounds 150 --kernel-refine 1 --pair-total-cells 8
```

I also extended the Bellman implementation to 12 density bins, processing
context states in chunks so the max-plus update does not allocate its full
four-dimensional temporary. The chunked update agrees exactly with the
original tensor calculation on a seeded random test. At `n=2^9`, the 12-bin
run without pair-total partition still returns rate zero (`2,660,832` viable
anchor cells out of `2,985,984`). This confirms the loose upper rate survives
moderate grid refinement; it does not establish a zero-rate realizable path.
The next UB-28 screen must preserve a continuous or nested profile through
successive transitions, rather than use a larger flat cell partition.

```text
python upper-bound/experiments/ub28-pinsker-cell-bellman.py --log-n 9 --bins 12 --high 280 --low 20 --anchor-rounds 150 --kernel-refine 1
```

## Proof gate

For every edge phase and boundary, construct a certified upper bound on the
maximum local trajectory
log-probability per input wire, strictly below `-ln 2` (equivalently, a
minimum cost strictly above `ln 2`).
Then bound the trajectory multiplicity by `exp(O(log^2 n))`, multiply by the
`n` possible bad edges, and obtain expected failing-input count below one for
all sufficiently large `n`. The main missing work is an outer approximation
of the full count state space: the current lattice computes a subset, while
the proof needs an upper bound over every count path. A plausible next tool is
a Bellman supersolution on density cells with interval-enclosed matching and
split kernels. No Lean formalization should start before that bound and its
uniform finite-width error are certified and independently reviewed.

### Thin-tail path through the random width-8 anchor (2026-10-24)

The current top-heavy screen leaves 150 random matchings per offset at widths
8 and 16. A new local path screen, `ub28-thin-tail-path.py`, flags a potential
fixed-width failure floor for that choice. For the 260/20 top-relative
schedule, choosing a hypergeometric mode at each matching and split gives the
central four width-8 counts `(2,1,7,6)` before the width-8 pass for every
tested `log_n` from 16 through 96. The count path is feasible, and the
full-vector implementation agrees at `log_n=24`. The central eight-block
mode path is already identical at every width 256,128,64,32,16,8 across the
tested exponents; for `log_n=24` it is
`(0,0,11,10,246,245,256,256)`, `(0,0,8,7,121,120,128,128)`,
`(0,0,5,5,59,59,64,64)`, `(0,0,4,3,29,28,32,32)`,
`(0,0,2,2,14,14,16,16)`, `(0,0,2,1,7,6,8,8)`.

Conditioned on those four counts, exact Fraction transfer through 150 random
matchings at each width-8 offset and then the exact width-4/2/1 tail gives

```text
P[central edge fails | width-8 counts=(2,1,7,6)]
= 1/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
```

This is a positive constant, with log about `-207.944`. Each specified
hypergeometric mode transition in the prefix has probability at least
`1/(h+1)` at width `h`; the two central input half-counts each have mass at
least `1/(n/2+1)`. Since the tracked dependency window is bounded and the
schedule uses a fixed number of rounds per scale, the resulting prefix path
has a coarse lower bound of the form `exp(-C (log n)^2)`. If the observed
width-8 profile stability is proved for all sufficiently large `n`, this
would imply `P[fixed central edge fails]=exp(-o(n))`, so the expected number
of failing inputs grows exponentially and the screened random-anchor schedule
cannot pass its first-moment gate. The all-`log_n` profile stability is not
proved yet; this is a strong obstruction screen, not a no-go theorem.

The immediate repair is to use the exact cyclic `h`-matching schedule at the
fixed anchor widths (at least 8 and 16), as the finite actual-schedule screen
already does below width 200. This changes only `O(1)` total depth and leaves
the asymptotic coefficient unchanged. It also kills this specific conditional
failure event: exact width-8 compare-split sends `(2,1,7,6)` through
`(0,0,8,8)` after the two offsets. The top-heavy rate screens currently use
150 random anchor rounds, so they must be rerun with the exact anchor before
they can support an all-size proof.

A stronger schedule variant removes every fixed-width random stage. For
`L=log_2 n`, choose `H` as the largest power of two at most `L/2`, use exact
cyclic `h`-matching stages for all dyadic `h<=H`, and use the 260/20
top-relative random schedule only for `h>H`. The exact tail costs
`2*sum_{h<=H} h = 4H-2 <= 2L-2` layers; omitting the bottom
`O(log L)` randomized scales changes the 280 coefficient by only
`O(log L)` depth. Thus this modification has modeled coefficient at most
282. It removes fixed-width random failure floors, but the global transfer
and all-profile rate gate still need proof; the exact tail is not yet shown
to repair every state delivered by the large-scale prefix.

Reproduce the path and exact conditional tail with:

```text
python upper-bound/experiments/ub28-thin-tail-path.py --log-n 24 --trace
```

The rate-grid implementation now also has `--exact-small-anchor` to use the
exact cyclic splitters at widths 8 and 16. At `log_n=24`, grid 16, and
top-relative rounds `(260,20)`, the feasible coarse-lattice rate remains
`0.816505354305 > ln 2`, essentially unchanged from the 150-round anchor
screen. This does not clear the thin-tail obstruction: the coarse lattice
still omits the mode path above. The exact-anchor screen command is:

```text
python upper-bound/experiments/ub28-rate-grid.py --log-n 24 --grid 16 --anchor-edge 126 --top-alternating-149-151 --top-high 260 --top-low 20 --exact-small-anchor
```

### Relationship to UB-40 mixed precision

UB-40's periodic-restoration screen is in [`sub500-screen/SCREEN.md`](sub500-screen/SCREEN.md), with its attempted D2 translation in [`prefix-flux/STATUS.md`](prefix-flux/STATUS.md). Its tolerance parameter multiplies Chvatal's local separator error, and its cost model assumes a global invariant that survives cheap stages and is restored by a precise stage. UB-28 has no corresponding local `eps_B` budget: its open gate is a pathwise first-moment bound over coupled density profiles. The UB-40 periodic cost figures therefore do not directly reprice UB-28. A refresh variant would first need a proved transition bound showing that a precise stage repairs the full count-profile state; the current UB-28 Bellman reset obstruction warns that coarse summaries lose the needed history.

### Exact width-8 phase-representative screen (2026-10-25)

I added `ub28-phase-rate-screen.py`, which takes one even output edge from each
of the nine exact width-8 support phases and evaluates its feasible grid-count
path rate using the exact width-8/16 anchor and the `(280,20)` top-relative
schedule. At `n=512`, grid4, centered placements, the sampled rates are:

| anchor edge | 0 | 16 | 32 | 48 | 64 | 192 | 208 | 224 | 240 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| rate | 4.216 | 6.580 | 3.765 | 3.080 | 3.080 | 3.080 | 3.765 | 6.580 | 4.216 |

All sampled feasible paths cost more than `ln 2`; sampled left-boundary cases
at edge0 and right-boundary edge240 had no bad path on this coarse lattice,
while edge16 at the left placement gave 22.323. This is finite diagnostic
evidence only. It does not bound omitted count paths, all placements within a
phase, larger exponents, or the continuous rate variational problem. The run
took about four minutes for the nine centered cases, so the present NumPy
transfer is not a good vehicle for broad brute-force sweeps; phase reduction
and tighter state representation matter more than a language rewrite at this
point. Reproduce the centered table with:

```text
python upper-bound/experiments/ub28-phase-rate-screen.py --log-n 9 --grid 4 --placements center
```

### Vectorized exact anchor and large-exponent phase screen (2026-10-25)

Profiling one grid4 case showed that the repeated Python enumeration in
`exact_split_pass` dominated the runtime: four deterministic width-8/16 passes
used 63.8 of 74.1 profiled seconds; the random-scale transfer used under one
second. I replaced that count-state loop by NumPy inverse-index arrays and
checked equality with the old transition on 18 randomized small tensors
(widths1,2,4; three block counts; both offsets). The edge-48 grid4 rate stayed
exactly `3.08025422748`; the nine grid4 phase cases then ran in about32 seconds
instead of roughly four minutes.

With that improvement, I screened all nine support-phase representatives at
`n=2^24`, grid16, exact width-8/16 anchor, top-relative rounds `(280,20)`,
and centered placement. The sampled rates were:

| anchor edge | 0 | 16 | 32 | 48 | 64 | 192 | 208 | 224 | 240 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| rate | 0.725317 | 0.872321 | 0.872321 | 0.872269 | 0.725420 | 0.872173 | 0.872298 | 0.872321 | 0.872321 |

The minimum sampled rate is `0.725316570849`, about `0.03217` above `ln 2`.
This is a materially tighter screen at a large exponent, but it is still only
an optimum over the feasible grid16 count lattice, uses binary64 log-binomial
values, samples one edge per support phase and only centered placements, and
has no uniform finite-type remainder bound. Off-lattice paths or unsampled
placements may lower the true rate. It is not an upper bound on the full path
maximum and does not prove sorting. Reproduce with:

```text
python upper-bound/experiments/ub28-phase-rate-screen.py --log-n 24 --grid 16 --placements center
```

Correction (2026-10-25): these nine rates are valid samples, but the screen's
representative rule grouped only by the support-closure phase and did not
preserve the exact terminal-window signature. Combining those two keys over
all 255 output edges yields 142 composite classes (72 even-edge and 70
odd-edge representatives), rather than nine. Thus the tables below are
exploratory samples only; they do not cover even all support/terminal phase
types. `ub28-phase-rate-screen.py` now groups by the composite key. A broader
screen must still establish that those finite classes cover every scale and
placement before it can support a proof.

The same nine representatives were then translated to the left and right ends
at `n=2^24`, again at grid16 with the exact small anchor. The minimum over
these 18 added cases is `1.19950251166` (edge0/right and edge240/left); the
centered minimum above remains the worst of the 27 samples. Full left/right
sample table:

| edge | 0 | 16 | 32 | 48 | 64 | 192 | 208 | 224 | 240 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| left | inf | 4.098380 | 2.924137 | 2.067257 | 2.923801 | 2.066948 | 1.801015 | 1.542194 | 1.199503 |
| right | 1.199503 | 1.542194 | 1.801015 | 2.066948 | 1.199561 | 1.199622 | 2.342963 | 3.089315 | 4.834770 |

`inf` means the grid16 recurrence has no feasible bad terminal state for that
representative, not that the true network edge is proved sorted by this
calculation. These 27 cases cover the chosen support representatives at three
translations, not every edge within each phase or off-grid count trajectories.

### Optional native max-plus kernel

The grid16 sweep over all 142 composite representatives at center and both
boundary placements completed with the optional C++ kernel in
`ub28-maxplus-kernel.cpp`. The 70 odd-edge classes were already sorted by the
exact width-8/16 anchor. The 72 even-edge center rates lie between
`0.725316570849` and `0.872320595699`; the minimum occurs at edges
`0,2,4,6,248,250,252,254` and is `0.032169390289` above `ln 2`. Across
left/right boundary placements, the minimum is `1.19950251166` (left placement,
edges 240 through 254). Every sampled finite class is above `ln 2`. This remains
a finite-size, feasible-lattice screen: it neither upper-bounds omitted count
paths nor proves that the 142 representatives cover every size and position.
Profiling the NumPy path at edge 0 took 52.8 seconds; the fused C++ max-plus update took 23.1 seconds
and returned `0.72531657084852`, agreeing with the NumPy result to the printed
precision. The native kernel also matched the NumPy update exactly on random
finite/`-inf` tensors for grids 1, 2, 4, and 8 with three different trailing
dimensions. Adding OpenMP across independent output rows brought that case to
17.2 seconds. The Python path now returns immediately when the exact anchor
has no bad terminal state, which accounts for the odd-edge `inf` cases without
running any large-scale transfers. This is a research-screen speedup, not a
mathematical strengthening of the rate bound. The Python path remains the
default. In a Visual Studio
Developer PowerShell, build and run the optional backend with:

```powershell
cl /nologo /O2 /openmp /LD upper-bound/experiments/ub28-maxplus-kernel.cpp /Fe:$env:TEMP\ub28_maxplus_kernel.dll
python upper-bound/experiments/ub28-phase-rate-screen.py --log-n 24 --grid 16 --placements left center right --native-dll $env:TEMP\ub28_maxplus_kernel.dll
```
