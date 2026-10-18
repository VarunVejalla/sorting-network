# Uniform first-split bounds and the remaining partition levels

Status, 2026-10-10: rigorous scalar-envelope derivation with exact rational
arithmetic in Python. It is conditional on the proposed network adapters;
neither these adapters nor this envelope are kernel checked. There is no new
global sorting bound.

## Uniform envelope replaces the single-size estimate

Run `python upper-bound/experiments/paterson/uniform_concentration.py`.
Fix halver error `1/4` and stopping density `1/10`. For every integer block
size `m` in an interval `[lo,hi]`, use the same certified wrong-key upper
budget `K`. The envelope bounds both core size and depth for every such `m`.
This covers all actual root-window capacities and bag sizes, including
partial bags, by their existing cardinality and stranger bounds.

Terminal sizes have `m < 10K`; their maximum whole-block core size is
`min(hi,10K-1)`. Active sizes instead lie in `[max(lo,10K),hi]`.
Their dirty child sizes range from `ceil(active_lo/2)` to `ceil(hi/2)`,
and clean child sizes from `floor(active_lo/2)` to `floor(hi/2)`.
The budgets are respectively `K` and `floor(K/4)`.

For core size, take the maximum of the terminal bound and the sum of the
two child envelopes, capped at `hi`. For depth, take the certified primitive
cost plus the maximum child depth. Empty intervals and zero budgets cost zero;
singleton budgets use a max/min tournament. Induction on maximum size proves
the envelope without assuming monotonicity of the original recurrence in `m`.

The halver support `alpha=K/ceil(m/2)` is largest at the smallest active size.
The existing [depth-ratio monotonicity](../../alternatives/legacy/AKS/Halver/PatersonMonotonicity.lean)
therefore lets one upper support bound cover all active sizes in that interval.

## Exact entropy ceiling certificates

The script uses no floating-point arithmetic for certification. It bounds
each logarithm by reducing its argument to `2^j*z`, with `1 <= z <= 2`, and
using the positive-term series

    log z = 2 sum_{i>=0} t^(2i+1)/(2i+1),  t=(z-1)/(z+1).

After `p=24` terms, the omitted tail is between zero and

    2 t^(2p+1) / ((2p+1)*(1-t^2)).

The same bounds cover `log 2`; negative exponents reverse its interval
endpoints when multiplied by `j`. Rational interval arithmetic then bounds
binary entropies from above and the positive depth-formula denominator from
below. Taking the ceiling of that upper rational quotient is conservative.
In particular, support `alpha<=1/5`, error `1/4` has a uniformly certified
primitive ceiling of **8**. The interval recursion often uses a smaller ceiling.

These are mathematical rational certificates checked by the Python program,
not Lean proofs of the logarithm series or its instantiations. The distinction
matters: no new depth hypothesis has been inserted into production Lean.

## Uniform scalar result

| Original bag level | Maximum integer size budget | Wrong-key budget | Uniform core bound | Uniform depth bound |
|---:|---:|---:|---:|---:|
| 2 | 13,541,622 | 4727 | 750,035 | 152 |
| 4 | 305,532,147 | 32 | 6,122 | 190 |

The envelope deliberately covers all smaller integer sizes, not just the
actual multiples of 32 or sizes compatible with a specific capacity. This
causes some overestimation, especially for level 4, but makes the coverage
explicit and removes the earlier monotonicity gap.

Four level-2 cores, sixteen level-4 cores, and at most 606937 root/cold wires
give a uniform pool bound **3,705,029**. This fits below `2^22`, so the existing
full bitonic pool sort costs at most **253** layers. Concentration costs at
most **190**, and known-label layout costs **1**. Thus the scalar budget is

    uniform first split <= 190 + 253 + 1 = 444.

This is a conditional network cost, pending the recursive core theorem,
odd-size padding/restriction, tournament construction, exact pool counting,
and known-binary-pattern matching adapter. The former **406** estimate remains
a single-size candidate, not the uniform bound.

## Can the three remaining levels fit in 117 layers?

The sufficient condition is `remaining depth < 117` for a strict improvement
over the 561-layer repair. At present, no suffix construction establishes it.
The first-split interface proves only half purity. It allows arbitrary
ordering within a half and supplies no quarter, eighth, or sixteenth errors.
For example, exchanging the lower and upper quarter value sets inside a
native half preserves half purity and destroys the quarter-bin guarantee.
This is a counterexample to implication between the output properties, not
a claim that the particular proposed concentrator performs that exchange.

The generic hierarchy's additional mismatch budgets, at minimum capacity,
are only 80, 4570, and 260496 per respective output bin. Thus its next split
requires very accurate quarter selection on blocks that may contain billions
of keys. Applying a plain restricted halver to such an otherwise unstructured
half would require `epsilon*K <= 80` for a possible cohort `K` near half
that block's size. This makes `epsilon` extremely small. The existing entropy
bound then becomes enormous; the generic low-error-halver adapter does not
fit 117 layers. This does not prove an impossibility for other networks or
for algorithms exploiting stronger retained structure.

An unconditional sufficient suffix is to sort each native half completely,
in parallel. Their cardinalities are at most `2^32`, costing at most
`32*33/2 = 528`. Exact half purity makes their concatenation globally sorted,
so all bin contracts follow. But its combined budget is **972**, worse than
the existing root sort. This is a conservative complete conditional fallback,
not a candidate improvement.

## Missing structural obligation

The remaining proof must describe the *actual* first-split transformation,
not just its pure-half output. Concentration preserves each original bag's
value multiset until the common-pool step. Pool sorting and the final layout
then redistribute keys across fixed rebuilt bins. One must bound that transfer
for every ancestor level consumed by the level-2 and level-4 rebuild.

A useful strengthened contract would track:

- The protected complement of each original bag and its remaining native
  interval errors for levels 2, 3, and 4.
- The pool's prefix-count discrepancies after removing these complements.
- Fixed output slots assigned to each protected bag and to the sorted pool.
- The resulting errors in every rebuilt ancestor bin, including the effect
  of the final matching on those slots.

It is not safe to assume that the original stranger invariant survives pool
mixing, nor that a small half-error count also bounds quarter errors. The
existing invariant budgets can be saturated, so replacement contamination
requires explicit slack accounting.

## Recommendation

Do not implement a generic three-level suffix on top of the 444-layer
first-split interface. First investigate a **joint bin-preserving pool
allocation** that obtains all four levels in the same repair operation.
If protected-bag/pool prefix discrepancies fit the rebuild budgets, this
could avoid sequentially paying for three new selections. If they do not,
the current concentration scheme is not a cost-effective complete repair.
Production should retain the 561-layer sorter until that joint contract and
its depth are proved.
