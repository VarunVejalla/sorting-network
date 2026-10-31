# Hard-tail alignment gate for the D2 recurrence

Date: 2026-10-27. This is an adversarial selected-cut LP diagnostic, not a
sorting-network counterexample or proof.

The local hypothesis tested is deliberately strong: impose zero separator
crossings whenever a retained local cut is at least 80 rows from the allowed
threshold-count interval. This models the hoped-for far-tail consequence of a
52-row column-height envelope followed by band repair. The coupled LP also
uses ordered root prefixes, the root-tail initialization, and all-row
dominance. It asks whether the single scalar potential `V + E/8`, with
geometric level weight `1/4`, has nonpositive one-step drift.

Reproduce the depth-5 phase-2 gate with:

```powershell
python -u upper-bound/experiments/prefix-flux/coupled_rank_lp.py `
  --depth 5 --scale 128 --threshold 1/3 --ordered-prefix --root-tail `
  --all-row-dominance --params 3 3 2 --row-bits 7 `
  --distance-tail-profile 80=0 --alignment-drift-stage 2 `
  --alignment-drift-span 1 --alignment-weight 1/4 `
  --alignment-drift-rho 1 --alignment-prev-floor 100 `
  --alignment-error-weight 1/8 --time-limit 60
```

HiGHS timed out with a feasible incumbent, so the reported objective is a
lower bound on the maximum drift, not an optimum. The incumbent has positive
drift `+18,770.8608`; the LP reports equality residual `3.5e-9` and inequality
residual `3.2e-9`, with `all_row_dominance=true` and 74 hard-tail constraints.
Thus this relaxation admits a feasible violation of contraction for this
fixed scalar potential even under the hard-tail assumption. It does not show
that the fixed D2 comparator network realizes that point, and it does not
exclude a phase-dependent or spatially weighted state.

At depth 3, scale 1024, the same assumptions solve the first-phase gate to
optimality with maximum drift `-75`. That early contraction does not persist
as a usable invariant: the later-phase depth-5 feasible point above has
positive drift, and its trace moves mass into off-spine bags. The depth-3
all-row build at scale 8192 was prohibitively large (over 1.5 GB before a
result); it was stopped. The reduced-scale depth-5 build took about four
minutes and used about 700 MB.

I also tested the flat level weight `w_i=1` with the same phase, tail,
all-row, and `E/8` assumptions. The depth-5 / scale-128 solve again timed out,
but returned a feasible phase-2 drift of `+30,879.61` with equality residual
`1.4e-9` and inequality residual `2.3e-9`. Its trace has cross-bag L1 mass
608,478 at the source and 638,686 at the destination, mostly off the threshold
spine. Thus simply replacing the geometric weights by unweighted total
alignment also fails in this relaxation. The results do not rule out
phase-dependent weights or a potential that records distance/side within each
bag.

A frontier-centered fixed spatial profile
`(1/4,1/2,1,1/2,1/4,1/8)` also returned a feasible phase-2 drift
`+13,702.94` under the same constraints (time limit; residuals below
`7e-10`). The corresponding source alignment was near its allowed floor, so
this only rejects that particular weight vector; it does not optimize over
all spatial weights.

Finally, I tested the two-transition return `t=2` to `t=4` with the same flat
level weights at both endpoints. The solve again timed out with a feasible
incumbent, with positive return drift `+6,600.00`; equality and inequality
residuals were each below `2e-9`. Reproduce by changing the command above to
`--alignment-drift-span 2` and keeping `--alignment-level-weights
1,1,1,1,1,1`. This is a bounded-depth relaxation witness against the flat
two-step potential, not an optimum or a fixed-network counterexample.

Conclusion for the proof plan: a uniform one-step inequality for `V + E/8`
is not a plausible route, even with an optimistic 80-row tail. Any viable
recurrence needs phase-dependent weights that track off-spine transfers, or a
stronger provider constraint coupling the local outputs to the actual fixed
comparator network. Do not extend the Lean stage bridge to claim this scalar
contraction.
