# Joint reachable-profile gate (2026-11-11)

**Status: positive small exact screen; no all-n or 8192-row bound.**
The scalar round-one spread budget loses useful information. Weighted support
cuts recover the exact worst two-round leakage in all ten tested instances.
This is a reason to investigate the joint interface, not a sub-300 proof.

## Precise model

Fix n columns, m rows, two row-permutation arrays P1,P2, and total mass M.
An input is h in {0,...,m}^n with sum h=M. Round one produces

    y_v = sum_u sum_{r<h_u} [P1(r,u)=v].

Round two applies the identical rule with y and P2. Its leakage is
sum_v max(final_v-M/n,0)/n. Enumerate every fixed-mass input to obtain the
reachable set R, then enumerate every possible intermediate profile at that
mass. Compare the maximum leakage over R with these successive relaxations:

1. Scalar: mean absolute deviation at most max_{y in R} mean |y-M/n|.
2. Subset: scalar plus p.y <= H(p) for every p in {0,1}^n.
3. Tiered: subset plus all p in {0,1,2}^n (translation duplicates removed).

Here H(p)=max_{y in R} p.y is an exact round-one support bound. The objective is
maximized over all final positive-excess sets implicitly, not just final halves.
Every comparison uses integer arithmetic, including mass, cuts and objectives.
The tiered feasible set can contain unreachable profiles even when its maximum
leakage equals the reachable maximum.

## Support bound without input enumeration

For arbitrary weights p, define A_u(h)=sum_{r<h} p[P1(r,u)]. Then exactly

    H(p) = max_{sum h_u=M} sum_u A_u(h_u).

A knapsack DP computes this: V_0(0)=0 and
V_{u+1}(s)=max_{0<=h<=m} (V_u(s-h)+A_u(h)); H(p)=V_n(M).
Consequently every actual intermediate profile obeys p.y<=H(p), including
weights chosen after inspecting P2. The identity is a direct decomposition of
the input height choices, not a probabilistic independence assumption.
The implementation compares the DP with exhaustive support maxima for every
cut used in these tests. This DP is not yet efficient at full sender dimensions.

## Exhaustive results

Each seed fixes both random permutation arrays before maximizing over inputs.
At n=6,m=8 there are 32,661 fixed-mass inputs; at m=12 there are 204,763.

| m | seed | Reachable | Scalar only | Subset cuts | Tiered cuts |
|---:|---:|---:|---:|---:|---:|
| 8 | 0 | 2/3 | 1 | 5/6 | 2/3 |
| 8 | 1 | 2/3 | 1 | 2/3 | 2/3 |
| 8 | 2 | 2/3 | 1 | 5/6 | 2/3 |
| 8 | 3 | 2/3 | 5/6 | 5/6 | 2/3 |
| 8 | 4 | 5/6 | 1 | 5/6 | 5/6 |
| 12 | 0 | 5/6 | 4/3 | 1 | 5/6 |
| 12 | 1 | 5/6 | 7/6 | 1 | 5/6 |
| 12 | 2 | 5/6 | 7/6 | 5/6 | 5/6 |
| 12 | 3 | 1 | 4/3 | 1 | 1 |
| 12 | 4 | 5/6 | 1 | 5/6 | 5/6 |

Units are rows of leakage, not coefficients of log n. These sizes cannot be
compared directly with the approximately 12-row gate at m=8192. In particular,
n=6 is not the intended n much larger than m regime. The results concern only
half total mass, not all input masses or the capture/fringe contracts.

## Reproduce and next gate

    python upper-bound/experiments/prefix-flux/d2_joint_reachable_gate.py --columns 6 --rows 8 --tiered --output <ignored-output.json>
    python upper-bound/experiments/prefix-flux/d2_joint_reachable_gate.py --columns 6 --rows 12 --tiered --output <ignored-output.json>

Generated JSON (including extremizing middle and final profiles) is stored in
the main checkout's ignored sub300-check cache under prefix-flux, named
`d2_joint_reachable_n6_m8.json` and `d2_joint_reachable_n6_m12.json`.

Next: develop a separation procedure selecting a small number of weighted cuts
from the second-round objective, rather than enumerating 3^n cuts. Test it in
wider instances with exact optimization bounds, then seek a uniform probabilistic
bound for the resulting joint quantity at 8192 rows. Keep the shared mass and
row-permutation dependence intact. Neither the small screen nor the support
identity supplies that uniform bound; 276 remains a conditional stage cost.

Follow-up completed: [D2-JOINT-CUTS.md](D2-JOINT-CUTS.md). Adaptive cuts
recover small exact optima, but wider tightening is modest and the
twelve-column case stalls through 100 cuts. Resolve cut strength versus
convex-hull loss before larger sweeps.
