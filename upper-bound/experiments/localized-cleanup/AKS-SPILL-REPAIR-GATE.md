# AKS spill-tail and oblivious-repair gate

Status: hand calculation from the existing AKS row-scramble contract, not a
new theorem. 2026-10-14.

## What the aggregate leakage theorem gives

For a row cut `h`, let `X_c` be the number of ones in output column `c` after
the row permutations and column sort, and put

```text
d_c(h) = max(0, X_c - (k-h))
Q_h(w) = #{c : d_c(h) >= w}.
```

The exact leakage identity recorded in
`upper-bound/experiments/ajtai-multiway/BELOW-200-PLAN.md` is

```text
leak_h = sum_c d_c(h) - max(0, m-(k-h)N),
```

where `m` is the input weight and `N` is the number of columns. The existing
uniform all-cut certificate bounds `leak_h <= E*m`. At the middle cut and
`m <= kN/2`, the subtracted baseline is zero, so

```text
w * Q_h(w) <= sum_c d_c(h) <= E*m.
```

For `m` near `kN/2` and the natural one-bin threshold `w=k/p`, this only gives

```text
Q_h(k/p) <= E*p*N/2.
```

Since `Q_h <= N`, this is vacuous whenever `E*p/2 >= 1`. Both currently
certified examples are deep in that regime: `(p,E)=(16,0.55)` and
`(32,0.45)`. The local all-cut theorem therefore does not imply a sparse
exception set. It gives an `O(N)` ceiling, while the forced-tail construction
in the same research packet shows that `Omega(p)` exceptional columns can be
unavoidable. The desired `Q=O(p)` estimate is a new theorem, with a factor
about `N/p=p` gap from what the aggregate contract supplies.

The estimate is a genuine limitation of the *contract*, not evidence that a
fixed row-permutation network has `Theta(N)` exceptions. To improve it, one
must exploit correlations among the column spill variables uniformly over
all monotone input height profiles, ranks, cuts, and orientations. The
existing weak-composition/Hoeffding screen does not close that joint event;
the filled-bottom equivalence-class reduction also loses its concentration
gap on most dense ranks. See `SPILL-TAIL-RESEARCH.md` in the AKS experiment
for the detailed calculations.

## Why sparse tails do not yet give a repair

Even a theorem `Q_h(k/p) <= C*p` would only count bad output columns. The
exceptional indices depend on the input, and a comparator network cannot be
given those indices as advice. A valid repair needs a fixed network that
detects/funnels the exceptional column mass, reinserts it in rank order, and
preserves all the other cut guarantees. The row-scramble contract does not
specify such a funnel or show that each exceptional column can be repaired
independently. Sorting the union of all possible exceptional columns is the
whole matrix and loses the depth gain.

This separates the proposed route into two independent gates:

1. Prove a simultaneous spill-tail envelope `Q_h(w) <= R(w)` for every
   monotone input and every cut/orientation. The first useful test is whether
   one can approach the unavoidable `R(k/p)=O(p)` scale.
2. Give an explicit input-independent comparator network of depth `G(k,p,R)`
   that converts that envelope into a composable ordered-bin contract. Charge
   `G` together with the 72/110-layer core in the recurrence; a small local
   core alone is not a prefix.

Passing only the first gate does not justify recursive sorting. If no
oblivious repair substantially cheaper than a full sort is found, stop this
reuse route even if the tail estimate succeeds.

## Recommendation

Do not formalize the current aggregate theorem further for UB-26: the
exception-count consequence is already quantitatively vacuous. The next
discriminating research task is a direct joint-discrepancy bound for the
fixed row-permutation family, retaining the exact monotone-height structure
and all-cut simultaneity. In parallel on paper, a candidate repair must state
how it identifies exceptional columns without input-dependent control. Until
both have finite parameters and a priced recurrence, this is a research lead,
not a credible sub-200 construction.
