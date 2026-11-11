# Convex-hull versus weak separation gate (2026-11-11)

**Result: the saved twelve-column obstruction is exactly separable. Stronger
separation helps the small case but does not remove the wider plateau.**
No general failure of linear support bounds is proved, and no uniform bulk
bound or sorting coefficient improvement follows.

## Exact outside-hull witness

Take n=12, m=4, seed=0, M=24, with the same scramble pair as the preceding
100-cut screen. Re-solving its final master gives leakage 2/3 at

    y = [0,2,1,0,3,0,4,3,0,4,4,3].
    w = [0,0,0,0,1,0,1,1,0,1,1,1].

The exact fixed-mass round-one support DP gives H(w)=19, whereas w.y=21.
Every reachable middle, and every convex combination of reachable middles,
satisfies w.y<=19. Thus this particular target is outside that convex hull.
This conclusion uses integer arithmetic and is independent of the numerical
master's optimality claim. It does not establish that all profiles with
leakage 2/3 are outside the hull or unreachable. In particular, the current
0.5 witness lower bound is not the true optimum unless separately proved.

`d2_joint_hull_gate.py` saves both permutation arrays, the target, integer
weights, cap and gap. Its verifier recomputes the support cap and checks the
strict violation without relying on SciPy optimization or random generation.
Replay passed with cap=19, target value=21, gap=2. This is an exact Python
combinatorial check, not a Lean kernel proof.

## Stronger separator

The original loop returned the first integer-valid violated cut. The new
`--strong` mode retains that valid cut and continues column generation to
maximize p.y-H(p) over ||p||_infinity<=1. It normalizes rounded integer cuts to
the same range and returns the strongest verified cut found. Search and
termination are numerical; each returned inequality is checked using the
integer support oracle. Failure to find a cut still proves no membership claim.

| Instance | First-violated strategy | Strong strategy | Best upper / found reachable lower |
|---|---|---|---|
| n=6,m=8,seed=0 | 40 cuts, exact objective recovered | 17 cuts, exact objective recovered | 2/3 / 2/3 |
| n=12,m=4,seed=0 | 100 cuts | 40 cuts | 2/3 / 1/2 |

For the six-column strong run, each optimally solved master was again compared
against exhaustive enumeration under exactly its current cuts. The wider
bounds remain numerical MILP dual bounds. Strong separation has not improved
the twelve-column best upper bound or its support-witness lower bound.

## Reproduce

Use the main checkout's ignored cache directory
LLM-helpers/sub300-check/artifacts/sub300-structural/prefix-flux for outputs.

    python upper-bound/experiments/prefix-flux/d2_joint_hull_gate.py generate <d2_joint_cut_wide100.json> --output <d2_joint_hull_n12.json>
    python upper-bound/experiments/prefix-flux/d2_joint_hull_gate.py verify <d2_joint_hull_n12.json>
    python upper-bound/experiments/prefix-flux/d2_joint_cut_loop.py --columns 6 --rows 8 --seeds 0 --cuts 40 --exhaustive --strong --output <d2_joint_cut_strong_small.json>
    python upper-bound/experiments/prefix-flux/d2_joint_cut_loop.py --columns 12 --rows 4 --seeds 0 --cuts 40 --seconds 3 --strong --output <d2_joint_cut_strong_n12.json>

## Next useful distinction

The plateau is not explained by convex-hull membership of the tested target.
Stronger individual cuts also fail to improve the tested wider objective.
Before more adaptive-cut sweeps, directly optimize both actual rounds in the
small twelve-column instance (including original input heights). This would
compare the true joint optimum with the 2/3 support-cut upper level. A reachable
2/3 witness would show that the objective level was already right; a smaller
proved optimum would quantify the remaining relaxation loss. Only then choose
between a compact family of joint constraints and a different stage. None of
these fixed small-instance tests supplies the required n-uniform theorem.

Direct joint follow-up completed: [D2-JOINT-DIRECT.md](D2-JOINT-DIRECT.md).
The true maximum is 7/12 by exhaustive computation. Next compare the full
reachable convex hull via its fixed-mass DP-flow formulation with this value.
