# UB-28 periodic discounted Bellman target

Status: proof architecture, not a certified rate bound. This sharpens the
remaining gate in [`UB28-TOP-HEAVY-SCHEDULE.md`](UB28-TOP-HEAVY-SCHEDULE.md).

## Rate normalization

Fix one adjacent output edge and condition on its local count trajectory. At a
scale with block width `h`, let `z` be the vector of supported block densities
before that scale's matching passes, and `z'` the supported densities after
those passes and the split to width `h/2`. The support audit shows at most six
coordinates at every interior scale; top and bottom interfaces have smaller
support. Let `q_s^p(z,z')` be the limiting log probability per width `h` of
this local transition, where `s` is the high/low round phase and `p` is the
finite support-alignment phase. It is the maximum of the matching and split
entropy terms over the finitely many internal count paths for that scale.

At top-relative depth `j`, `h/n = 2^-(j+1)`. For top block densities `a,b`,
their initial binomial log probability per input wire is

```text
B(a,b) = (H(a) + H(b))/2 - ln(2).
```

Thus a fixed-edge trajectory has exponent

```text
B(a,b) + sum_{j>=0} 2^-(j+1) q_{s_j}^{p_j}(z_j,z_{j+1}),
```

up to `o(1)` in the exponent per input wire. The two top scales must be handled
explicitly: the top support has two coordinates, then four, before the
six-coordinate interior regime. The finite anchor must be defined against the
whole remaining schedule: the actual randomized matching passes at widths 16
and 8, their half-splits, and then the exact width-4/2/1 suffix. A width-4
forbidden profile by itself is not the anchor. The anchor is the set of
width-16 profiles, together with support/alignment phase, from which this
complete finite continuation has positive probability of producing the
specified bad adjacent edge. Its probability cost is constant independent of
`n`, so its log probability vanishes after division by `n`; the reachability
restriction must remain.

## Sufficient interior certificate

In the interior, high and low stages alternate. Support alignment evolves in a
finite transition graph; taking a worst case over every allowed next phase
covers arbitrary edge-bit histories. A sufficient certificate is a bounded
phase-dependent potential `U_s^p(z)` satisfying

```text
q_s^p(z,z') + U_(opposite s)^(p')(z')/2 <= U_s^p(z)
```

for every feasible one-scale transition whose target remains capable of
reaching the finite bad terminal set. Along any successful `K`-scale path,
write `r` for the first interior scale and weight its action relative to that
scale by `1, 1/2, 1/4, ...`. The inequalities telescope exactly to
`sum_{t=0}^{K-1} 2^-t q_{r+t} <= U_r(z_r) - 2^-K U_{r+K}(z_{r+K})`.
For bounded `U`, the terminal term is `O(2^-K)`. In the original per-input-
wire exponent, the interior starts at width `n/8`, so this contribution is
`U_r(z_r)/8 + O(2^-K/8)`. This is the `U/8` term in the top-interface test.

The two-coordinate/two-scale top interface then needs a separate certified
inequality. If it maps the top counts `(a,b)` through local profiles `z_1,z_2`
to an interior state `z_3`, its required form is

```text
B(a,b) + q_top,0/2 + q_top,1/4 + U_s^p(z_3)/8 <= -ln(2) - epsilon.
```

Here each `q_top,j` is normalized by that stage's block width. If a positive
uniform margin `epsilon` holds for every edge/alignment class, method-of-types
and trajectory-count errors of `o(n)` leave
`E[failing inputs] <= n * exp(-epsilon*n + o(n)) < 1`.
For the target route, use 280 matching rounds on high scales and 20 on
intervening scales (both offsets), with the existing 150-round small-width
anchor. This is depth `300 log2(n) + O(1)`. The less expensive 260/20
schedule has coefficient 280 and remains a possible improvement if it passes
the same rate gate; it has less screened margin.

## Obligations before treating this as a proof route

1. Extract the exact finite phase graph and one-scale transition maps from the
   support-tracking implementation, including boundary edges and odd/even
   alignments.
2. Compute the exact width-16 bad-reachable terminal set using the full
   width-16/8 random schedule and deterministic suffix, for every support
   geometry and alignment phase. The finite transfer is now reproducibly
   sampled by [`ub28-anchor-viability.py`](ub28-anchor-viability.py), but the
   phase coverage is incomplete. Compute its preimages and verify that the
   viable-state restriction is closed under every path counted by the first
   moment. Do not replace it with the smaller forbidden width-4 language.
3. Find a potential with enough margin. A global potential over all density
   states is likely too loose because typical zero-cost paths need not end in
   the bad set; the viability restriction is essential.
4. Certify all Bellman inequalities with outward interval bounds for the
   entropy kernels, including endpoints, and certify the top-interface
   inequality.
5. Bound the uniform finite-type errors and `exp(O(log^2 n))` path count, then
   independently review the complete rate certificate.

The toy affine-MGF screen in `ub28-affine-mgf-toy.py` found appreciable loss,
so it does not supply `U`. A practical candidate is a piecewise-smooth or
piecewise-linear `U` whose cells enclose one shared continuous profile across
each Bellman transition; independent cellwise suprema are not sufficient.

An 8-bin Pinsker cell run for the 235/35 schedule (`n=2^10`, edge 64,
150-round anchor) is still vacuous: the certified-kernel *prototype* reports
`max_log_rate_upper = 0`, and 249,344 of 262,144 six-coordinate anchor cells
are viable. This is consistent with the exact anchor mask, where 20,090,629
of 24,137,569 profiles are viable. The broad-cell OR compression is not the
only obstacle: the simple Pinsker relaxation also loses all rate margin. The
next certificate attempt should use the exact entropy kernel with correlated
profile constraints, or a stronger global potential, rather than merely
adding more Pinsker bins.

The zero is an abstraction artifact, rather than a witness trajectory. The
reproducible [`ub28-meanfield-terminal-screen.py`](ub28-meanfield-terminal-screen.py)
follows the exact zero-rate update `(a,b) -> (a*b, a+b-a*b)` from top
densities `(1/2,1/2)`, with equal-density children at each split. For `n=2^20`
and 235/35 rounds it reaches width-16 densities
`(0,0,2.06e-72,2.06e-72,0.00296,0.00296)` on the tested edge support; rounding
to width-16 counts gives `(0,0,0,0,0,0)`, which the exact finite anchor rejects.
Thus the coarse Bellman value zero cannot be read as an actual zero-cost
trajectory. Its transition kernels maximize independently over density
intervals, so consecutive transitions can select inconsistent representatives
inside their shared cells. A useful certificate must constrain the profile
across consecutive transitions (for example, a relational potential or
correlated interval enclosure).

## Independent audit (2026-10-21)

Two fresh reviews found no sign or discount-factor error: weighting the
interior inequality by `h/n` telescopes, and the top coefficients
`1/2, 1/4, 1/8` match widths `n/2, n/4, n/8`. They independently confirm that
the first-moment threshold is `ln(2)` per input wire. Both flag full finite-
anchor reachability and the complete phase graph as essential; the support
script's six-coordinate bound is only a dependency-locality check, not that
graph. The q-transition must optimize joint matching/split count paths,
retaining correlations between overlapping support blocks.

This remains an audited certificate architecture only. There is no computed
Bellman potential or rate table yet, and no certified evidence that the
300-depth (280/20) schedule clears the `ln(2)` rate gate. Its restricted
grid-16 central-edge screen is about `0.87217`, but that is a feasible path,
not an all-path upper bound. A later tail-period sweep finds that even-edge
residues 0 and 2 modulo 16 are more critical: their restricted grid-16 path
cost at `n=2^12` is about `0.53478`, while the same residue-0 path costs
`0.72246` at `n=2^20`. This apparent approach from below to a narrow margin
above `ln(2)` makes the continuum refinement decisive; it does not certify
the all-path rate. See the phase-residue screen below. The smallest decisive numerical
milestone is a viability-constrained period-two Bellman value on a complete
phase graph, with shared profile cells and outward-rounded entropy bounds,
followed by the top-interface supremum. A certified lower bound above
`-ln(2)` rejects this certificate route for the schedule; a certified upper
bound strictly below it supplies a candidate potential and margin for the
remaining uniform-error proof.

## Finite-anchor viability screen (2026-10-21)

`ub28-anchor-viability.py` reads finite versus `-inf` from the existing
max-plus transfer at `n=256`, after reversing the exact width-4/2/1 tail and
the 150-round randomized schedules at widths 8 and 16. Thus each reported
finite profile has a positive-probability continuation to the designated
bad edge; the log-probability magnitudes are not used. Selected results:

| output edge | supported width-16 blocks | viable profiles |
|---:|:---|---:|
| 0 | 0–3 | 288 / 83,521 |
| 2 | 0–3 | 2,589 / 83,521 |
| 6 | 0–3 | 14,068 / 83,521 |
| 14 | 0–3 | 64,142 / 83,521 |
| 30 | 0–3 | 66,565 / 83,521 |
| 62 | 0–5 | 20,090,629 / 24,137,569 |
| 126 | 4–9 | 20,090,629 / 24,137,569 |
| 254 | 12–15 | 288 / 83,521 |

Every odd-indexed adjacent output pair is directly sorted by the final
odd-offset comparator layer, so only even-indexed edges need a first-moment
union bound. The edge-1 zero count is a consistency check. In the sampled
interior six-block phases, about 83.2% of the full count-profile box remains
viable, so viability alone is weak pruning; a useful certificate must exploit
accumulated trajectory cost, not just remove terminally impossible states.
These are finite samples, not a proof that the listed edge representatives
exhaust all phases.

The companion [`ub28-support-phase-audit.py`](ub28-support-phase-audit.py)
enumerates support geometry for every even edge at powers of two from `2^8`
through `2^14`. It finds at most 15 normalized support/alignment/boundary
phases at any single width and confirms support size at most six in this
range. Capping boundary distances at six makes the phase transition
multivalued: the audit records 181 source-to-target arcs, with 55 source
phases having multiple observed targets. A Bellman check must include all
such targets. The audit is a finite discovery tool; a proof still needs an
inductive closure argument for the phase encoding at every size.

## Exact geometric phase closure (2026-10-21)

`ub28-phase-closure.py` reduces the interior support transition to a finite
interval calculation. A geometry phase is an interval length (at most six),
its left endpoint parity, and its left/right distances capped at six. One
backward scale step floors support indices by two, then closes the interval
under offsets one and zero. A single offset matching expands either endpoint
by at most one, so the transition uses only local boundary data.

The representative enumeration is exhaustive for this phase encoding. For
child block counts through 128, the script tests every placement. Above 128,
placements within 32 of either boundary are listed exactly; if both margins
are at least 32, the next support has margins greater than six and depends
only on the source length and left position modulo four. The center
representatives include every such residue class. The width-8 seed phases
come from the exact terminal support map at 64 width-4 blocks. That map is
periodic under shifting an interior output edge by 16 wires (four width-4
blocks), and its support spans at most six width-4 blocks, so the two boundary
zones are disjoint for every larger power-of-two block count. The script
checks seed stability at 64, 128, 256, 512, and 1024 blocks.

The resulting candidate graph has nine width-8 seed geometries, fourteen
reachable geometric phases, and 25 geometry transitions. Taking the product
with the alternating high/low schedule phase gives 28 period-two Bellman
states and 50 labeled transition arcs. It covers every geometry phase and
transition observed by the previous all-edge audit for `n=2^8` through
`2^14`; all observed interior source phases are in the closure. The local
interval transition was checked against set-based matching closure for every
interval on arrays of sizes 1 through 32. This closes the geometric phase
encoding on paper, subject to checking the stated locality/periodicity
argument in the full proof. It does not compute anchor viability masks, a
Bellman potential, or any entropy-rate bound. Those remain the decisive
obligations.

## Pinsker cell-potential pilot (2026-10-21)

For one matching round, the asymptotic log transition rate is minus the mutual
information of the two matched-block membership bits. If `A,B` are source
densities and `X` is their intersection density, Pinsker gives
`q <= -8 (X - A*B)^2`. For a split into child densities `L,R`, it gives
`q_split <= -(L-R)^2/2`. These yield safe interval-cell transition upper
bounds (in real arithmetic), implemented in
[`ub28-pinsker-cell-bellman.py`](ub28-pinsker-cell-bellman.py).

The central-edge Bellman relaxation returns maximum log exponent `0` for
2-, 4-, and 8-bin cells at `n=256`, and also for 4 and 8 bins at `n=1024`.
At `n=256`, the exact width-16 viability mask compresses to 64/64 viable cells
for 2 bins, 4,096/4,096 for 4 bins, and 249,344/262,144 for 8 bins. Thus even
though only 83.2% of exact six-count profiles are viable, essentially every
coarse cell contains at least one viable profile. This is vacuous, not a
schedule obstruction: a cell can contain both a low-cost representative and
a different representative that reaches the bad anchor. The result confirms
that a scalar value per fixed cell resets the profile between scales. Any
useful next certificate must retain within-cell profile dependence (for
example, a continuous or Lipschitz potential); further refinement of this
same cell-reset relaxation is not the next step.

## Tail-period rate screen (2026-10-21)

`ub28-rate-grid.py` now supports explicit `left`, `center`, and `right`
translation of its finite anchor. The former default recenters the anchor by
half the increase in width-16 block count; it is appropriate for interior
edges, but not for a right-boundary anchor. Right-boundary tests must translate
by the full block-count increase. The script has been corrected accordingly.

For the 280/20 top-relative schedule, a grid-16 restricted-path screen at
`n=2^12` over eight even output-edge residues modulo the 16-wire terminal
period gives:

| edge residue | anchor representative | restricted path cost (nats/input wire) |
|---:|---:|---:|
| 0, 2 | 64, 66 | 0.534776621056 |
| 4, 6 | 68, 70 | 0.746992700547 |
| 8, 10 | 72, 74 | 0.919495584497 |
| 12, 14 | 76, 78 | 1.11303981349 |

The residue-0 representative at larger even exponents gives `0.655352954001`
at `n=2^14`, `0.699477141009` at `n=2^16`, `0.716252053967` at `n=2^18`,
and `0.722464191513` at `n=2^20`, versus `ln(2) = 0.69314718056`. These
numbers are minima over a restricted grid of feasible density trajectories,
so each is an upper bound on the unrestricted *finite-size discrete* minimum
for that edge and anchor. They are not yet bounds on the continuum infimum:
the script uses finite binomial rates, does not save a maximizing path, and
stops at a fixed-width anchor. Values below `ln(2)` at smaller finite heights
therefore do not reject the asymptotic schedule. The slowly increasing
residue-0 sequence suggests a narrow limiting margin and makes this the first
phase to refine continuously. A corrected right-boundary screen for edge 240
at `n=2^12` gives `1.46826694685`; the previous half-shifted value is invalid
and is not used.

An independent review confirmed that the split normalization in both rate
scripts is consistent: the Pinsker cell kernel is parent-width normalized,
while the exact count-grid split kernel is child-width normalized and is
divided by two on return. The remaining issue is terminal/profile resolution,
not this scale factor. Exact anchor-mask OR compression loses within-cell
identity; the next useful bound needs a viability-resolved boundary relation
and an all-path continuum enclosure, starting with residue 0/2.

For comparison, the 270-coefficient top-relative schedule (235/35 rounds)
at `n=2^20`, grid 16, gives restricted finite-size discrete minima between
`0.76936` and `0.77249` over the eight centered even-edge residues modulo 16.
These are again only finite-size candidate-path diagnostics; they do not
establish the continuum rate gate. The smallest useful next computation is
to save and backtrack an attaining path for the critical residue, evaluate
its entropy-rate action, and bound its continuation through the top-relative
tail. This can reject a schedule if it finds a path at or below `ln(2)`; a
path above `ln(2)` cannot certify the required all-path lower bound.
