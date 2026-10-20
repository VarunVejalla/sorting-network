# Why a larger exact frontier cannot repair this coarse interface

2026-10-20. Codex (GPT-6), with fresh-context derivation by
`/root/flux_contract_review`. Reviewed hand argument, not Lean. This concerns
the oracle interface in PLAN/REVIEW, not every fixed comparator provider.

In `frontier-witness.json`, d12, threshold q=5592405. Subtree(3,17) has
native interval [17*262144,18*262144), entirely below q, so it must eventually
contain only zeros. At t5 its bag contains1099 ones. Its high fringe exports
421; its last child receives678 ones. Those678 remain in the native subtree.

The only subsequent upward transfers across this subtree's boundary have
capacities448 at t7 and28 at t9. At t11 its root retires downwards. Even if
both fringes consist entirely of wrong ones, at least678-448-28=202 ones
cannot escape. All later local operations may be exact and still fail.
The actual final trace leaves440 ones in that subtree.

This extends beyond one cutoff. Replace d by12+r, N by4^r*N, q by4^r*q,
and repeat each bit of the early words S=4^r times. Through t5 the clipped
top levels and all bottom levels are unchanged; the D2 rows scale by S.
All cuts, counts, prefix dominance and strict supported-fringe promises
scale. Early ideal choices remain admissible; choose r large enough that
the few nonideal bags all exceed any prescribed fixed exact cutoff C.
One need not repeat the later t7 nonideal decision in the stored trace.

After t5, level three is never bottom again: omega(t)>3 for all odd t>=7.
At its possible activations t=7+2j,

    c(3,t) = 65536*S / 16^j.

The upward capacity is zero for top-descending, c/128 for top-rising, and
7c/1024 for ordinary nodes. Each is at most c/128. Descendants can move
wrong keys within the subtree but cannot export them without this boundary.
Thus the entire future escape capacity, even before retirement truncates it,
is at most

    512*S * sum(j>=0,16^-j) = (8192/15)*S < 678*S.

At least(1978/15)*S ones remain trapped, whatever all subsequent oracles do.
Raising a fixed exact cutoff only moves this obstruction to a larger N.

`cut_certificate.py` checks the extracted678 count, exact early-row scaling
for d12..24, and the future role/capacity formulas on those schedules.
The all-r extension follows from the displayed schedule formulas and the
homogeneity of D2 interval cuts; it is a paper argument, not a finite-test
claim of universal verification. `replay.py frontier-witness.json` checks the
underlying integer monotone execution without an LP.

## A necessary gate for the next invariant

For every wholly wrong-color-free native subtree, its present wrong-color
population must not exceed its remaining upward capacity. An invariant that
permits a larger population is already too weak, regardless of terminal
sorting costs. For a constructive proof one also needs quantitative capture
and the competing colors' use of that capacity; capacity alone is not enough.

The next useful question is whether the actual fixed separator has a
rank-sensitive spill guarantee excluding the t4/t5 choices here. A uniform
bulk bound plus the currently supported fringe range does not do so. Merely
retuning the final exact-sort threshold or summing signed errors cannot close
this gap. Reuse existing UB-24/UB-26 tail work before creating new plumbing.
