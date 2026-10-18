# Profile-budgeted fresh-root recurrence

Research note, 2026-10-10. Informal and numerical; no Lean changes or new
sorting bound. This tests whether charging fresh-root blockers to the same
moderate-tail budget as exterior errors materially sharpens the 86-layer
funnel analysis.

## Coupled quantities

For one fixed sorted profile after the intermediate column sort, let

```
E_g = sum_c (z_c-g)_+,
E_f = sum_c (z_c-f)_+.
```

The high marks initially in the exterior `(f,T]` number `E_f-E_T`. The total
high marks in the four root chunks `(g,f]` number `E_g-E_f`. Under `E_g < eta*j`
and `E_T >= 0`, write

```
x = (E_f-E_T)/n,       mu = eta*j/n,
rho_i = (high marks in root chunk i)/(r_i*n).
```

Then `x + sum_i r_i*rho_i < mu`. Since the profile heights increase with row,
`rho_0 >= rho_1 >= rho_2 >= rho_3`. If root rows are assigned to tournament
groups by an independent uniform bijection, `rho_i` is the average root-high
probability for a fixed column and phase. This random bijection must be part of
the witness distribution; the original fixed-input estimates needed only a
uniform pointwise root bound.

For a fixed column, let `a_i` upper-bound `E[H_i]`, where `H_i` counts exterior
high marks before phase `i`, and let `b_i` upper-bound `E[(H_i)_2]`. The
pair-witness case split gives the profile-dependent recurrence

```
a_0=x,                  b_0=x^2,
a_(i+1)=rho_i*a_i + kappa_i*b_i/2,
b_(i+1)=(rho_i^2+rho_i*kappa_i)*b_i
         +(2*rho_i*kappa_i+tau_i)*x^3 + q_i*x^4.
```

Here `kappa_i,tau_i,q_i` are those in `funnel-pair-witness.md`. Initial
Poisson-binomial factorial moments satisfy `E[(H_0)_k] <= x^k`; later phases
use `H_i<=H_0` to bound third and fourth moments. Uniform random assignment of
distinct chunk rows gives root-pair probability at most `rho_i^2` by sampling
without replacement. These facts yield the displayed recurrence. It is a
fixed-profile expectation estimate only.

## Numerical diagnostic

The gitignored helper `LLM-helpers/funnel_profile_budget.py` numerically
maximizes `a_4/j` at the largest supported normalized rank `j/n=4096`, over
`0<=x<=eta*j/n` and all monotone root densities obeying the weighted budget.
It reports a maximum near

```
a_4/j = 1.396e-16,
(a_4/j)/(1/86000000) = 1.20e-8.
```

The optimizer places essentially all the mass in the exterior (`x=eta*j/n`)
and none in roots. Adding the untouched-window charge `40/T` gives about
`4.657e-9`, far below `epsilon=1/86000000`. This is consistent with the
pair-witness estimate: root-blocked escapes were the main expected-error cost;
collision-only escape is much smaller. The helper uses floating-point
SciPy differential evolution. It is exploratory, not a certified global
optimization, and the assumed worst rank endpoint was not proved here.

## Why this does not solve the common-witness problem

The previous fixed-profile Chernoff exponent is still only about
`5.5e-9*j`. Even the entropy bound for all moderate-tail profiles is about
`0.396*n` at `j=4096*n`. This new expectation optimization does not give an
exponential tail strong enough to union over those profiles, and Markov is
weaker still. The useful consequence is a sharper *local* constraint for a
reduced witness count: selected root blockers and initial exterior leaves
consume one shared profile mass budget. The next fringe proof target should
count merged witness graphs with this weighted source-height charge, while
retaining the first scramble's probability rather than conditioning and
unioning over every possible intermediate profile.

A proof attempt should first count one fixed reduced witness graph by its
numbers of distinct exterior leaves, selected roots in each chunk, and
source-column maxima. If the resulting multivariate entropy/probability
exponent is nonnegative at the largest supported rank, abandon that graph
encoding before formalization; do not inflate the claim from the numerical
expectation result.

## Relation to the central bulk target

This recurrence does not change the independent bulk obligation. Disjoint
scheduling leaves 107 layers for a central repair, but the only explicit
construction in the audit is still a 631-layer exact cut partitioner. A
plausible avenue is an approximate multiway separator/near-sorter that handles
all 63 cuts in one shared network; a cascade of ordinary constant-error
halvers cannot be charged as if errors multiply without a proved interface.
The existing [AKS multiway-halver lead](../../../docs/ajtai1992-multiway-halvers.md)
should therefore be checked against the exact central contract before
investing in a custom expander construction. No such 107-layer construction
or lower bound is known from this audit.

