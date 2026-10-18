# Recurrence and cost gate for a new stage/scheduler

Status: design specification and arithmetic screen, not a construction or a
sorting theorem. Target: `limsup D(n)/log2(n) <= 500`.

## Stage contract to aim for

Fix a scale factor `p >= 2`. One macro-stage takes each active region of size
`N` and sends its items into `p` ordered child regions, each with its stated
capacity. It is one fixed oblivious binary-comparator network of depth `T(p)`;
`T` includes all serial partition, combine, local-sort, and cleanup layers.
The contract must cover every input, both orientations, all child cuts, and
the rank-distance information used by the next stage.

For each active region/bag `b` and rank-distance coordinate `r >= 1`, let
`x_(b,r)` be its nonnegative integer impurity count. A useful finite contract
has the form

```text
x'_(b,r) <= e_(b,r) + sum_(c,s) K[(b,r),(c,s)] * x_(c,s),
```

where `c` ranges over the old regions that can send items to `b`. `K` must
include the actual rank shifts, sibling contamination, and all child/parent
channels; `e` is the stage's fresh error. This is a simultaneous profile
guarantee for one network, not a separate promise for each cut. The stage also
states child capacities and the terminal condition that makes every leaf
exactly sortable. A bounded real-valued error potential alone is insufficient
unless it implies that integer terminal impurities vanish.

## Composition lemma / proof obligation

For the finite active state at a stage, choose positive weights `w_(b,r)` and
put `Phi = sum_(b,r) w_(b,r) * x_(b,r)`. If the stage and schedule prove

```text
sum_(b,r) w_(b,r) * K[(b,r),(c,s)] <= rho * w_(c,s)  for every (c,s),
sum_(b,r) w_(b,r) * e_(b,r) <= (1-rho) * B,
```

for some `rho < 1`, then `Phi' <= rho*Phi + (1-rho)*B`. By induction,
`Phi_t <= max(Phi_0,B)` for every number of stages. To conclude sorting, the
root initialization and leaf/terminal lemma must put the potential below the
least positive potential of any nonzero terminal impurity (or directly prove
terminal impurity zero). This last conversion is part of the theorem, not an
informal consequence of contraction.

For varying stage types, use a matrix `K_i` and local vector `e_i` at each
level. The same calculation composes if one common weight vector satisfies
the weighted-column bounds for every `K_i` and the cumulative weighted error
remains below the terminal threshold. A periodic block can instead be treated
as one macro-stage using the product transfer matrix and summed error vector.
This is the needed way to include multistage repair without hiding its cost.

## Depth recurrence and the 500 budget

If one complete macro-stage grows each recursively handled region by factor
`p`, and the profile/terminal lemmas justify recursion, then

```text
D(p^L * n0) <= L*T(p) + D(n0) + O(1),
C <= T(p) / log2(p).
```

For a periodic block with stages `(p_i,T_i)`, the corresponding price is

```text
C <= (sum_i T_i) / (sum_i log2(p_i)).
```

These formulas include all serial cleanup in `T_i`. The basic budget table is:

| Growth per complete macro-stage | Growth in bits | Maximum total binary depth for C <= 500 |
|---:|---:|---:|
| 16 | 4 | 2,000 |
| 64 | 6 | 3,000 |
| 256 | 8 | 4,000 |
| 1,024 | 10 | 5,000 |

The current schedule spends `3 * 2838 = 8514` layers per factor-64 growth,
which prices to 1419. Therefore a factor-64 macro-stage would have to be a
genuine replacement costing at most 3000 total layers, a 64.8% reduction from
that current three-stage block. The current 2838-layer `NodeSpec` network is
not itself such a replacement: its theorem is consumed three times per
factor-64 growth, and it does not prove that one use has the proposed
macro-stage profile/terminal contract.

## Feasibility screen from current work

The existing evidence does **not yet** make C <= 500 plausible within the
current Chvatal schedule family:

* The checked endpoint has `T=2838` for each of three ordinary rounds per six
  bits of growth. The separate Variant B proof target gives 1354.5, a useful
  incremental gain but far from 500.
* The tapered Chvatal parameter model's best fully combined scenario is about
  650 ideal / 700–780 after the integer window and finite fringe floor. It
  requires nonuniform flow, a changed top-node condition, larger fringe
  fraction, and stronger per-side/locality estimates; these are research
  estimates, not proved stage contracts. Its own conclusion says the current
  family is unlikely to get below 600 without another structural change.
* The direct-multiway transfer audit's first weighted-max candidate fails:
  its exceptional rank-1 local error already uses about 0.969 of the target
  budget, and the complete row bounds exceed 1. This rules out that specific
  repair with current scalar constants, not profile potentials in general.

| Candidate schedule | Growth and depth price | Error-profile status | Result |
|---|---|---|---:|
| Checked Chvatal schedule | Factor 64 per 3 nodes; `3*2838 = 8514` layers | Closed tapered stranger invariant and terminal sorting | 1419 |
| Variant B smaller window | Factor 64 per 3 nodes; projected `3*2709 = 8127` | Exact-mass round-1 and geometry obligations remain open | 1354.5 |
| Tapered L4 parameter model | Continuous model: about 1.49 growth bits per modeled stage and 788 layers/stage; windowed integer parameter search prices at about 700 | Assumes nonuniform flow, changed top-node condition, fringe fraction near 1/2, and per-side/locality bounds; no closed stage transfer theorem | 528 ideal / about 700 windowed |

The last row is the closest existing numerical signal, but it still misses 500
after integer/window effects and relies on several unproved changes. Its
continuous 528 is not evidence for a finite network until the stage contract
and recurrence are actually proved. No current candidate clears the 500 gate.

So the present go/no-go is: **do not search a large finite network yet**. No
derived recurrence currently prices below 500. The new-scheduler route remains
the right high-upside direction, but first it needs a closed transfer matrix,
fresh-error budget, initialization bound, and terminal-purity argument whose
stage budget lands under a row of the table. If the best closed contract is
still above 500, change the schedule/invariant before network search.

A first refinement of the current tree transfer is recorded in
[`TRANSFER-AUDIT.md`](TRANSFER-AUDIT.md): higher-rank sibling terms can be
rewritten as sums of deeper rank-profile coordinates. However, the initial
rank-1 screen below `0.508` at `alpha=1/2` incorrectly assumed parent outsiders
could be charged once across disjoint child outputs. Ordered address/rank cuts
show that one-sided outsiders can create about `32` mismatches per outsider
across the 64 children. The existing per-child theorem gives a conservative
`64*alpha` rank-1 coefficient, so a contraction might still use a much smaller
`alpha`, but the whole weighted operator must be recomputed. Fresh-error
budget, initialization, and depth-uniform terminal conversion also remain
open. This route is still worth deriving, but no sub-0.508 transport or
sub-500 recurrence has been established.

## Immediate derivation tasks

1. Choose the actual state coordinates from the tree proof: rank-distance
   impurities, capacities, and every sibling/parent send channel. Do not use
   a scalar sum that loses rank or level information.
2. Prove the aggregate ordered-window/boundary-displacement inequality with
   explicit fringe terms and the per-child defect vector. State one
   macro-stage's full affine transfer inequality, pricing rank-1 separately
   and making the number of source bags explicit.
3. Close the root initialization and leaf-purity conversion. Then solve the
   finite weighted inequalities exactly (rational arithmetic is enough).
4. Only if the resulting schedule prices below 500, search a structured
   finite realization of its required transfer profile. Record construction
   depth and every proof-relevant cut/rank guarantee.

Relevant current audits: [`RESEARCH-SEQUENCE.md`](RESEARCH-SEQUENCE.md),
[`TRANSFER-AUDIT.md`](TRANSFER-AUDIT.md),
[`tapered/NOTES.md`](../tapered/NOTES.md), and the
[1419 cost audit](../../../../docs/upper-bound-1419-cost-audit.md).
