# Two exact `botDesc` phase identities for `(3,3,2)` D2

2026-10-22. Paper derivation with finite exact-flow audits; not Lean checked,
and not a sorting or `limsup` theorem.

## Schedule and capacities

For parameters `k=A=8`, `nu=1/4`, let `c=S*cap(d,i,t)` at a sender
`(i,t)`. The schedule formula gives, for each eligible level `i>=2`, two
bottom-descending visits:

```text
t_s = 3*i - 4,     t_w = 3*i - 2.
```

At either time `omega(t)=i` and `omega(t+1)=i+1`, so both have role
`botDesc`. From `native(i)/cap(d,i,t)=2^(4+2*t-6*i)`,

```text
strong time t_s: native(i)/c = 1/16,   native(i+1)/c = 1/128;
weak time   t_w: native(i)/c = 1,      native(i+1)/c = 1/8.
```

At `t_s-1=3*i-5`, the eight children at level `i+1` have not yet entered the
active schedule and still have their full native deficits `c/128`. At
`t_w-1=3*i-3`, each such child is a `botRise` node; its whole bag rises, so its
deficit becomes the full native child size `c/8`. Thus the eight current
child deficits `U_j` are all `c/128` at the strong visit and all `c/8` at the
weak visit.

Write the current sender state as `(G,low,high)`, where `low+high=G`, and let
`a` and `pi` be its allocation and up-port size. For a `botDesc` sender,
`pi=15*c/4096`. Since `a=sum_j U_j-G`, this gives exact identities

```text
strong: a = c/16 - G;
weak:   a = c - G.
```

## Exact child-block sizes, conditional on the cut fronts staying in the end children

The D2 cuts are `L=low+pi/2` and `R=sum_j U_j-high-pi/2`. The proposed
all-depth state invariant `G<=c/512` implies `L` is smaller than either end
child deficit in both phases; the reflected inequality gives the same for
`high`. Hence only the two end children are clipped, yielding

```text
strong: first block = 49*c/8192 - low,
        six interior blocks = c/128,
        last block  = 49*c/8192 - high;

weak:   first block = 1009*c/8192 - low,
        six interior blocks = c/8,
        last block  = 1009*c/8192 - high.
```

The `G<=c/512` premise also makes all displayed end blocks positive. When
`G=low=high=0`, division by `a` recovers the two fixed shapes in
`INVERSION-LOCALIZATION-GATE.md` (`15/256` up and `49/512` edges in the strong
phase; `15/4096` up and `1009/8192` edges in the weak phase). For arbitrary
reachable bags, the `low/high` terms matter: schedule role alone does not
determine the normalized port fractions.

## Why this is useful, and what it does not close

There is also a direct use for the strong-phase endpoint formula in the
exceptional two-step sender estimate. If the intermediate level `i+1` is
`botRise` at `t-1`, the schedule forces level `i` to be `botDesc` at `t-2`;
writing `i=j+1` gives `t-2=3*i-4`, exactly its strong visit. Let `c` be the
current level-`i` capacity. The strong parent capacity is `16*c` and the
intermediate child capacity is `32*c`. The eight child bags made by the
strong cut have endpoint sizes

```text
first = 49*(16*c)/8192 - low,
last  = 49*(16*c)/8192 - high,
middle = (16*c)/128.
```

At the next `botRise` visit each child's whole bag is its up-port. Since
`low,high >= 0`, normalizing by `32*c` bounds the two endpoint quotas by
`49/16384` and each of the six interior quotas by `1/256`. Their sum is
`241/8192`, exactly the finite-screen maximum. This identifies the apparent
slack as a strong-parent endpoint effect, rather than a mysterious correlation
among eight quotas. The Lean file now checks both the endpoint-to-aggregate
arithmetic and the relaxed `g_old<=23/4096` factor estimate. To use this in the
all-depth proof, the strong-phase child-block identity must be established for
the actual reachable transition under the relaxed deficit cap; that link is
not yet proved.

These identities reduce the phase geometry to a small state `(G,low,high)`.
The main unproved step is now to combine the 13-row tail operator with these
state-sensitive port lengths and derive a closed transfer of the child/up
rank defects from one strong visit to the next. The recurrence must include
all sibling packets, the root state, common local-provider witnesses, and
the remaining non-`botDesc` roles. If it yields a uniform global inversion
bound `inv<=N^theta` for `theta<27/301`, the fixed cleanup in
`INVERSION-LOCALIZATION-GATE.md` would give a coefficient below300 for the
conditional 273 prefix schedule.

The exact finite audit is:

```text
python upper-bound/experiments/prefix-flux/d2_phase_identities.py --depth 100
```

At depth100 and scale8192 it checked 7,053 strong and 7,044 weak distinct
compressed state rows; at depth30 it checked 543 strong and 534 weak rows.
Every positional copy is represented by one of these interned states, and
each check includes all eight child deficits and both end-cut formulas.
These are finite cross-checks of the integer `FlowDAG`, not an all-depth
proof of the schedule, the `G` invariant, the common provider, or global
sorting.
