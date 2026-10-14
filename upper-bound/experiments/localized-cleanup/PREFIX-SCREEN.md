# Early-stop screen for UB-26

Date: 2026-10-14. Claim level: `model` for the source-derived cost and
`hand-proof` for the recurrences. This note does not claim an improved bound.

## Two terminal contracts

For a fixed `0-1` input, call an interval `I` dirty if all positions before
it contain zero and all positions after it contain one. The values inside
`I` are unrestricted. An s-sorted output has such an interval of length at
most `s`.

A rank-pure partition into consecutive blocks is stronger: for each block,
its values on every permutation input are exactly one consecutive rank
interval, and the block intervals occur in output order. At any Boolean
threshold, at most one block is mixed. Sorting each block independently in
parallel therefore yields a full sorter.

Suppose a binary prefix on `N` wires establishes rank purity with block
width `B(N) <= c*N^theta`, `theta<1`. Let its depth be
`P(N) <= p*log₂(N)+O(1)`. Recursive exact sorting within all blocks at once
gives

```text
F(N) <= P(N) + F(B(N))
C <= p + theta*C
C <= p/(1-theta).
```

Padding to powers of two changes `B` by a constant factor and adds only
lower-order depth terms. The formal argument must handle every input size,
the exact finite base case, and variable last blocks. The sub-200 gate is
`p<200*(1-theta)`.

Alternatively suppose the prefix gives only an s-sorted output with
`s <= c*N^theta`. Partition into blocks of length `s`. Sorting paired blocks
`(0,1),(2,3),...` and then shifted pairs `(1,2),(3,4),...` catches any dirty
interval of length at most `s`: if it crosses a boundary between pairs in
the first pass, it lies within one shifted pair in the second. Outside the
original interval the Boolean values are pure and sorting preserves them,
so the second pass sees a dirty interval no wider than `s`.

The two passes cost `2F(2B)`, since every window in a pass is disjoint and
all windows run in parallel. Therefore

```text
F(N) <= P(N) + 2*F(2*ceil(c*N^theta)),
C <= p + 2*theta*C,
C <= p/(1-2*theta),    theta<1/2.
```

The gate is `p<200*(1-2*theta)`. For `theta=1/4`, it requires `p<100`.
This is stricter than the rank-pure contract and explains why searching for
the stronger local guarantee can be worthwhile.

## What the checked Chvatal prefix supplies

The checked assembly has `N=64^d`. After `tf7 d` stages, every level
`d-7` parent contributes a block of exactly `64^7=2^42` wires. Its 64
children at level `d-6` are pure with respect to rank-1 outsiders; the
source proves that the block consists of the corresponding consecutive
global rank interval. The current final bitonic networks on those blocks
cost at most 903 layers. See `best/AKS/Chvatal/RealBlocks.lean`,
`FinalSorts.lean`, and `RealNetwork.lean`.

The proved rank purity is stated only at the **actual terminal time**
`tf7 d`, where each level-`d-6` child has fixed capacity `64^6`; its
integer outsider bound is then below one. `P_all` gives fractional outsider
bounds at earlier times, but it does not make larger bags rank-pure. Thus
one cannot simply stop at `d'` and invoke the one-call rank-pure recurrence.

There is a useful rough screen for the obvious attempt to promote those
fractional bounds to an s-sorted output. Suppose the stop leaves active bags
with native rank scale `B=64^k≈N^theta`. Their reference capacities are
within constant factors of B in the bottom part of the schedule. To force
the invariant's order-j outsider count below one requires roughly

```text
mu * delta^(j-1) * B < 1,
j ≈ log₂(B) / log₂(1/delta).
```

Here `delta=1/(5.3e9)` and one rank-tree level multiplies native interval
width by 64. Thus `64^j` is about `B^gamma`, where
`gamma=log₂(64)/log₂(1/delta)≈0.186`. The rank region that must remain
unresolved can consequently be as large as `B^(1+gamma)≈N^(1.186*theta)`.
This is only an exponent screen: it needs a careful treatment of variable
frontier capacities, integer rounding, and the actual sets of wires assigned
to the bags. A rank interval is not automatically a contiguous interval of
physical output positions.

If, counterfactually, early stopping at `d'` did establish rank-pure blocks
of width `64^(d-d')`, it would take `3d'-21` ordinary nodes, each depth
2838, plus the fixed root depth. Setting `d-d'≈theta*d` and using
`log₂ N=6d` gives

```text
prefix depth / log₂ N -> (3*2838/6)*(d'/d)
                       = 1419*(1-theta).
```

Under that unproved rank-purity premise, the one-call recurrence would give
`1419*(1-theta)/(1-theta)=1419`, so even the optimistic direct early-stop
adaptation cannot beat the accepted constant. The actual proof gap is larger:
the source does not establish the premise, and the rough stranger-tail screen
inflates the candidate unresolved rank width. No claim that the existing
prefix is an s-sorter is made.

The primary construction target is therefore a new rank-pure prefix for
blocks of size `N^theta`, with depth coefficient `p<200*(1-theta)`; for
`theta=1/4`, `p<150`. A weaker s-sorted prefix remains viable if its
coefficient is below `200*(1-2*theta)` and the physical cleanup windows can
be implemented as two fixed disjoint-window passes. Candidate stages must
establish their *simultaneous* global partition or localization guarantee.
Independent one-cut halvers do not establish this, and replacing their
arity-k comparators with full binary sorters incurs the existing UB-08
compilation cost.

## First candidate class to price

Try recursive rank partitioning by a fixed sequence of coarse thresholds
implemented as oblivious compare-split stages. A stage should divide a
region into a fixed number of consecutive output blocks, with every block
receiving an interval of global ranks. Recurse independently on blocks;
charge each stage's exact binary depth and do not assume the values can be
routed to a block by an input-dependent permutation. The missing construction
is an oblivious multiway partition network; its whole-network depth, not its
number of rank cuts, is the quantity to compare with 100--150 layers per
input bit.

An immediate falsification screen is to construct the comparator layers for
small widths and SAT-check rank purity for all Boolean inputs. A counterexample
for one threshold invalidates rank purity. Passing small widths supplies
only model evidence; any candidate still needs a uniform all-width
construction and a deterministic proof.
