# Direct joint optimum (2026-11-11)

**Exact finite exhaustive result: the twelve-column example has maximum leakage
7/12 rows, strictly below the collected support-cut bound 2/3.**
This is not an n-uniform theorem, an 8192-row bound, or a Lean kernel proof.

## Coupled model and independent check

`d2_joint_direct.py` uses one-hot variables for both the original input height
h_u and each intermediate height y_v. It enforces

    y_v = sum_u sum_{r<h_u} [P1(r,u)=v],     sum h_u=M.

It then maximizes the exact round-two positive-excess objective using the same
one-hot prefix counts and sign-selection formulation as the earlier master.
Unlike that master, it retains actual first-round reachability. Integer network
simulation checks the input, intermediate and final profiles returned by HiGHS.
The reported solver upper bound is numerical.

`d2_joint_exhaustive.cpp` independently enumerates every input-height vector
at fixed total mass. It updates first-round destination counts during the
recursion, recomputes round two at each leaf, and scores with integer arithmetic.
An independent coefficient-count DP checks that the number of leaves is the
coefficient of z^M in (1+z+...+z^m)^n. Python additionally checks that count and
both the MILP and exhaustive maximizing witnesses by network simulation.
This is exhaustive finite computation with an ordinary optimized C++ executable;
it does not use native_decide, extend Lean trust, or establish any general bound.

## Results

Both scrambles use seed 0 from the existing Stage generator; each output saves
both permutation arrays explicitly.

| n | m | M | Inputs enumerated | Exact maximum | Collected-cut upper |
|---:|---:|---:|---:|---:|---:|
| 6 | 8 | 24 | 32,661 | 2/3 | 2/3 |
| 12 | 4 | 24 | 19,611,175 | 7/12 | 2/3 |

For n=12 the integer objective numerator is 84 with denominator 144. One
exhaustive maximizing input is

    [0,4,0,3,3,1,3,0,4,4,2,0].

The MILP independently found a different maximizing input with the same score.
Its objective and numerical upper bound agree with exhaustive enumeration.
The collected-cut excess is 1/12 row (one eighth of its 2/3 upper value).
The earlier 1/2 support-witness lower bound was incomplete; it was not the
actual joint maximum. All results here are for half total mass and fixed
scramble arrays, with n small relative to the eventual application.

## Reproduce

Use an ignored output prefix in the main checkout's sub300 cache.

    python upper-bound/experiments/prefix-flux/d2_joint_direct.py --output <direct.json>

This writes direct.json plus direct.json.instance.txt containing n,m,M and both
permutation arrays. Compile the C++ source with optimization in a configured
compiler environment, keeping the executable/object outside tracked source:

    cl /nologo /O2 /EHsc /std:c++17 upper-bound/experiments/prefix-flux/d2_joint_exhaustive.cpp /Fe:<ignored.exe> /Fo:<ignored.obj>
    <ignored.exe> <direct.json.instance.txt> <audit.json>
    python upper-bound/experiments/prefix-flux/d2_joint_direct.py --verify-audit <direct.json> <audit.json>

MSVC requires its developer environment (vcvars64.bat); the source is also
standard C++17. The exhaustive tool rejects runs exceeding 200 million profiles.
Cached outputs: d2_joint_direct_n12.json, d2_joint_exhaustive_n12.json,
d2_joint_direct_n6.json, d2_joint_exhaustive_n6.json.

## Next gate

Actual reachability improves the joint objective, but this does not show that
linear support cuts can recover the improvement. The tested plateau target
was outside the hull; other targets of the same objective might lie inside it.
Instead of collecting more cuts, encode the entire fixed-mass reachable convex
hull as a flow through the height-choice DP: a path chooses one height per
column and ends at mass M. Continuous unit flow represents a convex combination
of such paths; output moments are the resulting middle coordinates. Couple
those moments to integer middle heights and the round-two objective.

Solve that small extended formulation at n=12,m=4. A 2/3 value with an exact
rational path-mixture witness would establish intrinsic convex-hull loss.
A maximum 7/12 would instead show that all support cuts suffice in this example
and that their extended formulation closes the finite gap. Either result would
be more informative than more generic cut sweeps. No scaled bound is implied.
