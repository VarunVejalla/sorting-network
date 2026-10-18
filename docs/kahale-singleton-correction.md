# Singleton-only corrections cannot repair the fiber charge

## Exact obstruction (2026-10-11)

Consider the same five-wire prefix as in the
[capacity-lift counterexample](kahale-capacity-lift.md):
`(0,1),(2,3)` followed by `(0,2)`. This time append just `(2,4)`.
Fix output wire 0 to zero and project onto wires 1 through 4.

The ten-term four-wire potential falls from `3` to `4/3`, a drop of `5/3`.
But every singleton input has exactly the same output before and after the
new comparator: the five output masks are `(2,2,8,8,16)`.
Thus the complete labeled singleton routing, not just its multiplicities,
is unchanged.

For any function `h` of singleton routing, therefore,

\[
 (\Phi(R)+h(q))-(\Phi(LR)+h(q'))=5/3>1.
\]

**Consequently no additive singleton-routing correction can repair this
potential's unit-layer inequality on actual conditional fibers.** This
argument does not depend on positivity, smoothness, or endpoint normalization
of `h`. It does not rule out a replacement potential or a joint correction
depending on more than singleton routing.

Even rescaling to `alpha Phi+h(q)` requires `alpha<=3/5` on this transition.
This restriction concerns this specific potential family, not the universal
sorting-depth coefficient.

## What changes despite identical singleton routes

The fiber's projected rank-two preimage masses change as follows. Masks use
the four projected wires; masses count original five-input weight-two states.

| Output mask | Before | After |
| --- | ---: | ---: |
| 3 | 1 | 0 |
| 5 | 4 | 4 |
| 6 | 1 | 0 |
| 9 | 2 | 3 |
| 12 | 2 | 3 |

The comparator merges the output points 3 into 9 and 6 into 12. Singleton
groups see no merger because the lower comparator wire carries no singleton
output. The rank-two obligations still progress. Rank-three masses also
change: the mass 4 at mask 7 merges into the mass 4 at mask 13.

This separates two kinds of preimage information: routing individual added
ones, and routing pairs or larger sets of added ones. Singleton capacities
give necessary constraints on the latter but do not measure their progress.

## Exact checks and next target

**Follow-up:** [pair preimage corrections](kahale-pair-correction.md) restore
the inequality exhaustively through five inputs, including an exactly
verified quadratic formula. That fitted formula fails a six-input scale
test; the quadratic family as a whole remains open beyond the finite fit.

The [script](../lower-bound/experiments/scripts/kahale_singleton_correction.py)
enumerates all 1019 reachable pairs of five-wire Boolean images and global
singleton multiplicity vectors. It checks 25475 parallel transitions, of
which 16416 preserve projected singleton multiplicities. Their maximum
uncorrectable drop is exactly `5/3`. The explicit prefix additionally checks
that labeled singleton routes are unchanged.
[Results](kahale-singleton-correction-results.json) retain the exact fiber
images and rank-one through rank-three preimage masses.

The next feasibility target is a joint correction tracking **pair preimage
masses and their overlap with singleton routes**, with zero sorted endpoint.
First test whether that information supports the layer inequality on actual
small prefixes. An across-scale sum still needs its own overlap bound; no
asymptotic improvement follows from this finite investigation.

This is an exact Python obstruction and a derived mathematical argument;
it has not been formalized in Lean. The verified coefficient remains
approximately 3.270559454.
