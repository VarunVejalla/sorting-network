# Full reachable-hull flow gate (2026-11-11)

**Numerical result: the full hull relaxation matches the exact true joint
maximum in the tested twelve-column example, at 7/12 rows.**
No intrinsic convex-hull gap was found. The previous 2/3 plateau came from an
incomplete cut family on the evidence of this solve. The hull upper bound is
numerical, unlike the earlier exhaustive true-network optimum; do not promote
this to an exact hull-optimality theorem or an n-uniform bound.

## Extended formulation

For n input columns, m rows, fixed total mass M, use DP nodes (u,s) where u
columns have been assigned and their heights sum to s. Retain only nodes with
0<=s<=u*m and 0<=M-s<=(n-u)*m. An arc (u,s,h) goes to (u+1,s+h), for a legal
height h in [0,m], and contributes

    a_v(u,h) = sum_{r<h} [P1(r,u)=v]

to intermediate coordinate v. Put continuous unit flow from (0,0) to (n,M),
with conservation at every other node. Equate each intermediate height y_v
with the sum of arc flows times a_v(u,h).

Every unit flow in this acyclic graph is a convex combination of source-sink
paths. Each path is an actual input height vector of mass exactly M, and its
output moments are the actual first-round intermediate profile. Conversely,
any convex combination of such inputs induces a feasible unit flow. Therefore
this is an exact extended formulation of conv(R), not the weaker relaxation
that constrains only expected total input mass.

Keep y integer via one-hot height variables. Apply the actual round-two
prefix-count objective to y and maximize positive final excess. This optimizes
over conv(R) intersected with the integer intermediate profiles. It does not
apply round two separately to each member of an input mixture.

## Implementation and witness checks

`d2_joint_hull_flow.py` builds the flow MILP with the existing finite scramble
model. After solving, it decomposes the flow into input paths. A small LP picks
a basic convex combination of those paths reproducing y; exact rational linear
algebra then recovers its weights. The verifier uses Fraction arithmetic and
integer network simulation to check nonnegative weights summing to one, fixed
mass for every input, exact equality of the averaged intermediate profile to y,
and the resulting integer round-two score. This proves witness feasibility,
not MILP optimality. All permutation arrays are saved explicitly.

## Results

| n | m | DP arcs | Hull witness | Numerical hull upper | Exact true-network maximum |
|---:|---:|---:|---:|---:|---:|
| 6 | 8 | 486 | 2/3 | 2/3 | 2/3 |
| 12 | 4 | 660 | 7/12 | 7/12 (within solver tolerance) | 7/12 |

Seed=0 and M=24 in both cases. HiGHS reports optimal with zero MIP gap.
Both returned hull witnesses have only one positive path: the maximizing
intermediate profile is actually reachable. Replay of each rational witness
passes exactly. The numerical n=12 upper is 0.5833333333327598; its tiny
undershoot of 7/12 is solver error, not a stronger mathematical bound.

For n=12, the model uses intermediate profile

    [3,2,1,4,3,1,1,3,0,4,1,1].

The integer score is 84/144=7/12. This matches the independent enumeration of
19,611,175 inputs from D2-JOINT-DIRECT.md. The earlier collected-cut value
2/3 is higher. This tests objective equality only: it does not show that every
integer point of conv(R) is reachable or that hull relaxation is always exact.

## Reproduce and status

    python upper-bound/experiments/prefix-flux/d2_joint_hull_flow.py --output <hull_n12.json>
    python upper-bound/experiments/prefix-flux/d2_joint_hull_flow.py --verify <hull_n12.json>
    python upper-bound/experiments/prefix-flux/d2_joint_hull_flow.py --columns 6 --rows 8 --output <hull_n6.json>

Artifacts live in the ignored main-checkout sub300 cache as
`d2_joint_hull_flow_n12.json` and `d2_joint_hull_flow_n6.json`. No Lean edits or
builds were involved. The rational verifier checks only feasibility; an exact
global upper certificate for the mixed-integer flow model is not implemented.

## Next research gate

The full DP-flow formulation replaces a growing list of support cuts and is
the cleaner finite joint screen. Before more Lean, compare it with the direct
joint model at a few wider/taller fixed instances using bounded solver time,
explicitly tracking witness lower bounds versus numerical upper bounds.
If the hull stays tight, seek a compact bound on its flow/dual potentials that
can be proved uniformly for random row permutations. That is the mathematical
step needed for a bulk bound near 12 at m=8192; finite optimization alone does
not supply it. Startup, capture, the global recurrence and terminal cleanup
still require their own contracts. No priced path below 300 is proved here.
