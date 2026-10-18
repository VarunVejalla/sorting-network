# A depth obstruction for repair on the enlarged tail class

Informal derivation, 2026-10-10. This is a lower bound for a specified repair
interface, not a sorting-network lower bound or a proof that actual reachable
states defeat the intended construction.

## Interface under examination

Suppose a column-local depth-`d` repair must work after a fixed second row
scramble for every sorted intermediate profile with

```
mass j <= delta*f*n,
E_g < eta*j.
```

The two-round relative-fringe note proves its second-scramble existence on
this enlarged class. A repair need not work on this whole class, but if it
does, the following obstruction applies. No initial-scramble reachability
claim is assumed.

## Long-column witness

Let one intermediate source column be entirely marked and give every other
column height at most `g`. The tail mass is `T=m-g`. Take

```
j = floor((m-g)/eta)+1,
```

so `T<eta*j`. For the numerical parameters and large `m`, choose `n=m`.
Then `j/n` is about `5800`, below `delta*f=8192`, and the remaining mass
`j-m` can be placed in the other columns below height `g`. Thus this is an
admissible enlarged-class profile. The tall source may be chosen adversarially;
the other heights can be adjusted to keep exactly the same `j`.

For each output column, the union of the input ancestors of its bottom `f`
outputs contains at most `f*2^d` positions: one comparator layer increases
each output's possible input ancestors by at most a factor of two. A distinct
key starting outside this union cannot end in that output fringe.

For a fixed row scramble, average over the choice of the tall source column.
In each row its position is uniformly distributed across destination columns,
since that row's scramble is a permutation. Hence some tall-source choice
puts at least

```
m - f*2^d
```

of its marked keys outside their destination fringes' ancestor unions. Those
keys remain outside the final fringe regardless of the other column heights.
This averaging argument also allows a different fixed repair network in each
column; it is not restricted to identical column repairs.

Consequently a universal repair on this enlarged class necessarily satisfies

```
f*2^d >= m - epsilon*j.
```

At `eta=1/5800`, `epsilon=1/86000000`, the allowed ratio `epsilon*j/m`
is approximately `5800/86000000`, about `0.00006744`, for large `m`.
At the scheduler's narrow fringe ratio `f/m=4095/2^37`, depth `25` covers
only the fraction `4095/4096` of input positions, leaving `1/4096`, about
`0.00024414`. This exceeds the allowance: **at least 26 layers are necessary**
on this interface. A fortiori, a 19-layer repair is impossible on it.

If the fixed second scramble already meets the proposed universal full-sort
fringe theorem, its ideal sorted outputs also satisfy that theorem on this
profile. The obstruction therefore persists despite a good ideal fringe
count; it concerns whether a shallow physical repair can realize it.

## Consequence for the proposed global budget

The candidate fringe proof uses a lower scale near `2^43`, typically requiring
column height ceiling `2^44` across templates. Two bitonic sorts at that
ceiling consume 1980 layers, leaving only 19 for a strict sub-1000 stage.
The enlarged tail-promise repair interface cannot fit that budget.

This does not rule out a repair limited to states actually reachable after
the chosen first scramble. The long-column witness may be excluded by a
stronger universal first-stage property. It also does not cover repairs that
compare across columns: those have different ancestor and routing geometry.

The useful alternatives are therefore precise:

1. lower the fringe/height scale enough to leave the 107-layer budget;
2. prove a stronger reachable-state promise and design repair on that class;
3. use comparisons across columns with a fully charged implementation; or
4. reduce the first two sort costs and rebuild the global budget.

More accurate scalar bulk tails alone cannot remove this ancestor obstruction
while retaining the same enlarged state class and column-local repair.
