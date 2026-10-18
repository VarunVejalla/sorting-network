# Exact count transitions for fresh tournament partitions

Informal derivation, 2026-10-10. This is a fixed-profile probability tool for
the [fresh-reservoir funnels](fresh-reservoir-funnels.md). It is not a universal
fringe theorem. It avoids enumerating comparator trees for a fixed column.

## A count process suffices within one fixed column

At a phase, condition on the complete exterior state, containing `H` high
marks. The fresh balanced partition is independent of that state. If its
group sizes are `m_1,...,m_r`, their occupancy vector `k` has distribution

```
P[k_1,...,k_r | H] = product_l binom(m_l,k_l) / binom(M,H),
sum_l k_l=H.
```

This depends only on `H`, not the actual marked positions or the previous
tournament history. The roots are fresh, in different rows, and independent
of these occupancies. With root-high probability `p_l`, a group leaves

```
(k_l-1)_+ + V_l*1[k_l>0]
```

exterior marks. The root indicators `V_l` are independent within this column.
Thus for generating variables `x,z` the exact conditional probability
generating function of the next count is

```
K_H(z) = [x^H] product_l F_l(x,z) / binom(M,H),
F_l(x,z) = 1 + sum(k=1..m_l, binom(m_l,k)*x^k
                         *((1-p_l)*z^(k-1)+p_l*z^k)).
```

For `z>=1`, increasing any `p_l` increases `K_H(z)`. Replacing the phase's
root probabilities by the uniform upper bound `p_i` gives a stochastically
dominating count transition, not just a first-moment estimate. The transition
is also monotone in `H`: add initial marks, use the same partition and roots,
and every group's exterior output count can only increase.

Use the phase-specific root bounds in
[the pair-witness note](funnel-pair-witness.md). Iterating these four kernels
provides a rigorous dominating one-column distribution for a fixed profile,
conditional on its initial exterior count. There is no assumption of
independence between successive exterior states.

## What this buys and what it does not

The one-column calculation automatically accounts for shared partners and
roots. It should be used before manually enumerating depth-four trees for a
fixed-input tail estimate. Only coefficients through the required degree `H`
are needed in each group polynomial; repeated equal-size groups can be
represented by powers rather than individual factors.

Initially the column's count is a sum of independent Bernoulli row marks.
Its factorial moments satisfy `E[(H_0)_k]<=mu^k`, where `mu<=eta*j/n`.
This does **not** imply stochastic domination by a Poisson variable: replacing
the initial count by a Poisson law needs a separate comparison valid for the
specific functional being bounded. The pair calculation already has that
comparison because its coefficients in falling factorials are nonnegative.

Column counts are not independent: the same row permutation allocates marks
without replacement across columns. Multiplying their generating functions
requires a proved joint inequality. A possible route is a suitable negative
dependence theorem for disjoint monotone functions of independent row samples,
followed by averaging the independent column-partition choices. That theorem
has not been established here.

**Subsequent progress:** [the joint-tail note](funnel-joint-tail.md) gives an
elementary informal proof of this joint-column inequality and a fixed-input
failure bound `exp(-4e-9*j)`. The reduced source-profile count remains open.

Even a valid fixed-input tail bound must defeat the profile count. Union over
all `(m+1)^n` profiles would charge about `n*ln(m+1)`. Rare-rank fringe failures
need a much smaller source-profile count, preserving the height cost of each
selected source column. The transition kernel by itself supplies no such
reduction and cannot establish one universal network.

## Concrete next calculation

1. Derive higher falling-factorial transition bounds from `K_H`, including
   shared-group terms, and obtain a justified exponential-moment envelope.
2. Establish the joint-column inequality rather than assuming independence.
3. Reduce the source-profile family using marked rows and total height cost;
   test the resulting scalar probability-versus-entropy inequality over all
   supported ranks, including unbounded column counts.

If step 3 does not close, change the physical construction or its input promise
before investing in Lean formalization. The 40% expectation ratio is evidence
that fixed-input performance has margin, not evidence that step 3 will close.

No production code, tests, or Lean builds were changed or run.
