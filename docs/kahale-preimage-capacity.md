# Singleton preimage capacities and the nonlinear charge

## Exact finite result (2026-10-11)

The ten-term four-wire potential in [witness charges](kahale-witness-charge.md)
has layer drop at most 1 on **every domain containing the sorted points that
satisfies bottom singleton preimage capacities**. This is an exhaustive exact
Python result, not a Lean theorem or an asymptotic improvement.

The screen enumerates all 2048 domains containing `{0,8,12,14,15}`.
Of these, 101 satisfy the bottom capacities; all 909 domain/layer checks pass.
All 44 actual comparator-network images belong to this class.
Adding top singleton capacities leaves 50 domains, but is unnecessary for the
charge inequality. The maximum drop is exactly 1 in each tested class.

Code: [capacity screen](../lower-bound/experiments/scripts/kahale_preimage_capacity.py).
Data: [exact results](kahale-preimage-capacity-results.json).

## What the capacity condition says

For a monotone weight-preserving map `F` on the four-dimensional cube, write
`F({i})={q(i)}`. Necessarily `q(S)` is contained in `F(S)`.
The screen asks for one singleton routing `q` onto the domain's rank-one slice
such that, at each higher rank:

- Every input subset has at least one permitted output in the domain.
- Every distinct output has a distinct permitted input preimage.

Permitted means `q(S)` is contained in the output. Bipartite augmenting paths
check the second condition exactly. Together these conditions permit total,
surjective assignments independently at each rank. They do **not** assert
that those assignments fit together into one monotone map.

Thus the result uses a strictly broader domain class than actual network
images, and even avoids requiring full cross-rank monotonicity. The previous
abstract counterexample is excluded by these capacities.

## Next mathematical obligation

### A general algebraic capacity inequality

Let `m_i` be the number of input singleton sources routed to output wire `i`.
For any family `E` of distinct rank-two output points, viewed as edges `{i,j}`,
singleton Hall capacities imply

\[
 |E| \le \sum_{\{i,j\}\in E}m_i m_j
       +\sum_{i\in V(E)}\binom{m_i}{2}.
\]

**Proof (derived, not Lean checked).** Choose a distinct input-pair preimage
for each output edge. Its two singleton routes must lie in that edge. Pairs
from different routing groups occur in exactly one eligible edge, contributing
`m_i m_j`. Pairs within group `i` are eligible for every incident edge but
count only once in the union, contributing `binom(m_i,2)`. This counts the
entire union of permitted input pairs, proving the inequality. The argument
holds for any number of wires. The script independently checks the formula
on all 35 four-source multiplicity vectors and all 64 edge families (2240
checks).

For a rank-`k` output point `y`, the corresponding individual condition is
`sum_{i in y} m_i >= k`: its preimage needs `k` distinct singleton sources
whose routes lie in `y`. All ranks must use the same multiplicities `m_i`.

### Why both parts matter

The updated exhaustive screen isolates two failures:

1. **Individual capacities without Hall:** the domain
   `{0,4,5,6,8,9,10,12,14,15}` has drop `5/3` under `(0,1),(2,3)`.
   Singleton outputs are wires 2 and 3. Outputs 5 and 6 require `m_2>=2`;
   outputs 9 and 10 require `m_3>=2`. Hence both multiplicities equal 2.
   But the four edges `{5,6,9,10}` have union capacity only
   `binom(2,2)+binom(2,2)=2`, contradicting the displayed inequality.
   Each output individually has a possible preimage; they cannot all have
   distinct preimages.
2. **Rank-two Hall without higher-rank demands:** the domain
   `{0,1,3,7,8,9,11,12,14,15}` has drop 2 under `(1,3)`.
   Singleton routes use wires 0 and 3. Outputs 3 and 12 force
   `m_0=m_3=2`, while rank-three output 7 excludes wire 3 and therefore
   requires `m_0>=3`, a contradiction.

Rank-two Hall plus individual rank-three capacities already selects the same
101 domains as the full screen, and suffices for all 909 layer checks.
This equivalence is an exhaustive four-wire result, not a general theorem.
The simplified necessary assumptions now give a more concrete target for a
short proof of the ten-term charge inequality.

### Lifting obligation

**Update:** the direct conditional-fiber lift fails on an actual five-wire
prefix: the potential drops by 2, with five singleton sources on four output
wires. See [the explicit counterexample](kahale-capacity-lift.md). General
Hall capacities and full monotonicity hold there; the source budget differs.

Extract a short implication from singleton capacities to the ten-term layer
inequality, identifying the specific forbidden witness configurations. That
would explain the correction without relying on a finite image catalogue.

For a larger cube, conditioning on a baseline gives a monotone conserving
map on the remaining input coordinates, with output increments relative to
that baseline. It does not generally give a four-input/four-output map:
increments can use additional output wires. Arbitrary four-wire projections
therefore do not inherit this screen's assumptions.

A scalable proof must retain those extra preimage sources, and bound the
combined charge across overlapping scales in one parallel layer. Summing
local four-wire certificates alone supplies no logarithmic depth bound.
The universal verified coefficient remains approximately 3.270559454.
