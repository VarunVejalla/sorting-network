# Reduced D2 third-moment gate

2026-10-28. This tests whether the existing reduced exact-core model supports
a strict one-stage contraction of the global third distance moment. It does
not test an all-depth theorem.

With `depth=2`, `scale=16`, threshold `1/3`, row height `2`, all global cuts,
and the continuous pairwise sorting hull, the stage-1 gate is optimal. At
`rho=1` its maximum `M3(next)-M3(current)` is zero to solver tolerance. At
`rho=0.99`, the optimum is `392,567,010.6`, with source and destination
moments both about `39.2567` billion. Thus this relaxation admits profiles
that do not contract by even one percent in one transition. The optimizer is
fractional (`integral_solution=false`), so this is not a counterexample to the
fixed network.

Reproduce with:

```powershell
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 2 --scale 16 --threshold 1/3 --ordered-prefix --root-tail --params 3 3 2 --row-bits 1 --all-global-cuts --continuous-slope-core --pairwise-slope-core-hull --inversion-drift-stage 1 --inversion-moment-order 3 --inversion-prev-floor 1000 --inversion-drift-rho 99/100 --time-limit 30
```

The corresponding exact Boolean core MILP at this size hit its 45-second
limit without a feasible incumbent. A smaller exact run (`depth=2`, `scale=8`,
row height `1`) solved with zero drift, but that core is only a permutation
and is not informative about sorting. The next useful gate needs either a
tractable exact two-row witness or a different state that controls the global
center shifts; this scalar `M3` contraction test in the current relaxation
does not certify the route.
