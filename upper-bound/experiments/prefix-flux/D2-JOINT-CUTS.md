# Objective-guided joint cut loop (2026-11-11)

**Status: implemented and validated exhaustively at small size; modest wider
numerical tightening. No uniform 8192-row bound.**

## Algorithm and quantifiers

Fix both row-permutation arrays and half total mass M. A MILP chooses an integer
middle height per column, subject initially only to total mass, and maximizes
the exact two-round leakage objective after round two. One-hot heights encode
round-two prefix counts; a binary per final column selects its positive excess.
No final half restriction and no guessed scalar spread budget are used.

For the resulting middle y, solve a separation LP over weights p in [-1,1]^n.
A column-generation loop asks the exact round-one fixed-mass knapsack oracle
for H(p) and a maximizing reachable middle r. If p.y>H(p), add that support cut
to the master. Otherwise add r to the separation LP and continue. Before adding
a cut, round p to integer weights, remove the common shift and gcd, then
recompute H(p) in integer arithmetic. Thus every added cut is independently
valid for every actual input at this fixed mass. The support oracle returns
input heights and checks the resulting reachable middle against its objective.

A numerical failure to separate establishes neither reachability nor exact
convex-hull membership. Even all support cuts describe the convex hull, which
may contain unreachable integer profiles. A time-limited master incumbent is
not an upper bound: retain the smallest solver dual upper bound across all
iterations. Solver upper bounds are numerical, not exact rational certificates.

## Verification and results

The small test enumerates every intermediate profile at this mass and checks
the master optimum after each cut whenever HiGHS reports optimal. It also
computes the true reachable maximum independently by exhaustive two-round runs.

| n | m | seed | Cuts | Initial upper | Best upper | Reachable lower |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 4 | 0 | 7 | 0.75 | 0.25 | 0.25 (exhaustive) |
| 6 | 8 | 0 | 40 | 7/6 | 2/3 | 2/3 (exhaustive) |
| 6 | 8 | 1 | 35 | 7/6 | 2/3 | 2/3 (exhaustive) |
| 6 | 8 | 2 | 29 | 7/6 | 2/3 | 2/3 (exhaustive) |
| 12 | 4 | 0 | 20 | 0.75 | 2/3 | 0.5 (exact witness) |
| 12 | 4 | 0 | 100 | 0.75 | 2/3 | 0.5 (exact witness) |
| 16 | 4 | 0 | 30 | 0.75 | 0.6875 | 0.5625 (exact witness) |

Upper values in the wider rows are solver bounds; cuts and witness lower values
are checked with integers. The final n=16 master timed out with a weaker dual
bound, so the table uses the best earlier upper bound. Times are limited to
three seconds per wider master. No comparison of these row counts with the
12-row target at m=8192 is warranted. These widths still do not establish the
intended n much larger than m asymptotics, other masses, or fringe capture.

## Reproduce

    python upper-bound/experiments/prefix-flux/d2_joint_cut_loop.py --exhaustive --cuts 40 --output <small.json>
    python upper-bound/experiments/prefix-flux/d2_joint_cut_loop.py --columns 12 --rows 4 --seeds 0 --cuts 20 --seconds 3 --output <wide.json>
    python upper-bound/experiments/prefix-flux/d2_joint_cut_loop.py --columns 16 --rows 4 --seeds 0 --cuts 30 --seconds 3 --output <n16.json>

Source: `d2_joint_cut_loop.py`. Generated histories/cuts are in the ignored
main-checkout sub300 cache: d2_joint_cut_small.json, d2_joint_cut_wide.json,
d2_joint_cut_n16.json. New runs checkpoint iteration history to an output-side
.progress.json file and remove that checkpoint when complete. They save the
integer cuts so support caps can be replayed independently.

## Assessment

Objective-guided cuts do avoid listing all 3^n weights and recover the small
exact maximum. The wider tests improve the bound only modestly, and many
successive adversaries survive. Increasing the twelve-column run from 20 to 100 cuts does not improve either
the best upper bound or the support-witness lower bound. The MILP master is
already a scaling obstacle.
This is not yet evidence that a small fixed family of weighted cuts gives the
needed uniform bulk bound. A theoretical joint inequality or a provably compact
family of weights is still needed before this becomes a sub-300 route.

Next bounded gate: distinguish weak cut selection from intrinsic convex-hull
loss on the twelve-column instance. Optimize separation strength or solve
convex-hull membership at an extremizer, with a replayable membership witness.
A convex combination of reachable profiles would show that linear support
cuts cannot exclude that extremizer; failed quick separation alone cannot.
Avoid wider blind sweeps before resolving this distinction.
