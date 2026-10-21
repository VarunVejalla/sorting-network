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
The zero-one principle then gives a sorter of depth
`280 log2(n) + O(1)`, hence the requested coefficient below 300.

## Obligations before treating this as a proof route

1. Extract the exact finite phase graph and one-scale transition maps from the
   support-tracking implementation, including boundary edges and odd/even
   alignments.
2. Compute the exact width-16 bad-reachable terminal set using the full
   width-16/8 random schedule and deterministic suffix, for every support
   geometry and alignment phase. Compute its preimages and verify that the
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
Bellman potential or rate table yet, and no evidence that the 280-depth
schedule clears the `ln(2)` rate gate. The smallest decisive numerical
milestone is a viability-constrained period-two Bellman value on a complete
phase graph, with shared profile cells and outward-rounded entropy bounds,
followed by the top-interface supremum. A certified lower bound above
`-ln(2)` rejects this certificate route for the schedule; a certified upper
bound strictly below it supplies a candidate potential and margin for the
remaining uniform-error proof.
