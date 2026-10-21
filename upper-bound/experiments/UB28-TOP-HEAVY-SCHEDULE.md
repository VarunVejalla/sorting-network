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
