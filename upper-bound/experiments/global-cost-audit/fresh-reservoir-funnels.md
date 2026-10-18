# Fresh-reservoir funnels: an 86-layer candidate

Derived argument, 2026-10-10; not Lean checked. This is a physical comparator
construction with a **fixed-input expectation estimate**, not a universal
separator theorem or a new sorting bound.

## Input promise and parameters

Consider high keys after the intermediate column sort and second independent
row scramble. Low keys use the reflected construction. Set

```
f = 131040, g = 83840, h = f-g = 47200,
a0 = delta*f = 4096, eta = 1/3650, epsilon = 1/86000000,
T = 2^33, M = T-f, p = a0/g.
```

For each supported rank `j<=a0*n`, require the intermediate sorted heights to
satisfy `E_g<eta*j` and the [dyadic tail promise](all-scale-tail-interface.md)
`E_T<40*j/T`. These promises concern total mass across columns. The moderate
tail argument in [the two-round note](two-round-relative-fringe.md), with the
parameters above, has scalar upper bound

```
C1 = (1+ln(H/(eta*a0)))/H
   + (2+ln(H^2/a0))/(eta*H) + 1+ln(a0/H)
H = g/2 = 41920
C1 < -0.02209 < -0.02.
```

The log bound was evaluated using rational intervals from
`paterson/uniform_concentration.py`. Applying the full reduced-witness
summation and common-witness adapters remains informal. The all-scale result
uses `a0<=8192`, so this smaller support is allowed.

## Comparator construction

In each column protect the bottom `f` positions, except the currently used
reservoir roots. Partition the band of row heights `(g,f]` into four disjoint
chunks with sizes

```
r = [472, 1888, 8496, 36344]   # sum = 47200
```

At phase `i`, partition the same `M` exterior slots of heights `(f,T]` as
evenly as possible into `r_i` groups. Each group receives a distinct root from
the current reservoir chunk. Run a maximum tournament on that group and its
root, placing the maximum at the root. The partitions are sampled uniformly
from balanced partitions, independently by column and phase, then fixed as
part of the eventual network witness.

All exterior positions precede their roots in ascending wire order. A binary
reduction tree can therefore use ascending comparators throughout, with each
comparison keeping the maximum at the later wire. Its depth is at most
`ceil(log2(1+ceil(M/r_i)))`. The four depths are

```
25 + 23 + 20 + 18 = 86.
```

All groups in one phase run in parallel. Earlier roots and future roots are
untouched. The reflected minimum tournaments work in the top window; both
orientations run in parallel when `m>=2*T`. Smaller-height cases need separate
accounting. No extra arbitrary wire permutation is assumed free: the
tournament groups themselves specify comparator pairs.

Captured high keys never leave the bottom fringe. In particular, this retains
exact small-rank capture whenever `eta*j<=h`: integer excess `E_g<eta*j<=h`
excludes a sorted column of height greater than `f`. Here `h/eta=172280000`.

## Fixed-input expectation calculation

Fix an intermediate sorted profile, a rank, and one column. A fresh root's
high-key probability is at most

```
j/(n*g) <= a0/g = p,
```

because a row of height at least `g` has at most `j/g` high source columns.
Fresh root rows have not been read by previous phases. Independence of row
scrambles makes their marks independent of the current exterior state.
Independence across columns is neither asserted nor needed here.

For a group containing `k` exterior high marks and root mark `v` in `{0,1}`,
the exterior count after its tournament is exactly

```
k - (1-v)*1[k>0] = (k-1)_+ + v*1[k>0].
```

Write `H_i` for the column's exterior count before phase `i`, and

```
s_i = ceil(M/r_i), kappa_i = (s_i-1)/(M-1).
```

Two specified exterior slots land in the same balanced group with probability
at most `kappa_i`. Using `(k-1)_+<=binom(k,2)` gives the conditional bound

```
E[H_(i+1) | exterior state] <= p*H_i + kappa_i*H_i*(H_i-1)/2.
```

Also `H_i<=H_0` pointwise. Initially a column's exterior marks are independent
Bernoulli variables across rows, with mean at most `eta*j/n`. Consequently

```
sum_columns E[H_0*(H_0-1)] <= (eta*j)^2/n.
```

Iterating the domination estimate and using `j/n<=a0` bounds the expected
total fringe escapes, including untouched rows outside the window, by `B*j`,
where

```
B = 40/T + eta*p^4
  + eta^2*a0/2 * sum(i=0..3, p^(3-i)*kappa_i)
B = approximately 1.156339572309233e-8
epsilon = approximately 1.162790697674419e-8.
```

The inequality `B<epsilon` was evaluated with exact rational arithmetic. Its
margin is only about 0.55% of the target. This bound is uniform in the column
count for each fixed profile and rank; it is not simultaneous over profiles.

**Subsequent improvement:** [the pair-witness calculation](funnel-pair-witness.md)
bounds surviving pairs after the first tournament and lowers this coefficient
to approximately `6.269879586e-9`, about 54% of `epsilon`. Using the same
moderate-tail promise to bound each successive root chunk further reduces it
to `4.668180720e-9`, about 40% of `epsilon`, at the same 86-layer depth.
The calculation below describes the limitations of the original bound;
the universal-witness problem persists after this improvement.

## The crucial missing theorem

We need **one fixed choice** of both scrambles and all partitions that satisfies
the actual strict fringe count for every admissible original sorted profile,
every supported rank, and both orientations. A separate favorable network for
each input does not suffice.

Expectation alone does not establish this. Markov's inequality only bounds a
fixed-input failure probability by about `B/epsilon=0.99445`, far too large to
union-bound the input family. A useful next target is a reduced bad-witness
description for the four physical tournaments, with a strong tail bound that
beats its entropy. It must retain dependence from sampling within rows and
track blocked roots as well as exterior collisions. The existing full-sort
overflow witness does not directly describe this tournament output.

## Global cost and other obligations

At the smaller geometry's height ceiling `2^43`, two bitonic column sorts cost
`1892`. Adding the funnels gives `1978`, leaving **21 layers** under a stage
ceiling of `1999`. Thus a sub-1000 coefficient is conditional on:

1. The universal common-witness fringe theorem just described.
2. Bulk repair, including its post-funnel input promise, within the remaining
   21 layers together with any additional charged operations.
3. Every template, smaller-height case, and ordinary-node fallback meeting the
   same stage ceiling, followed by the scheduler correctness proof.

No 21-layer bulk construction is supplied. Ascending comparisons preserve a
completed fringe guarantee, but do not automatically provide the input promise
of an unrelated bulk lemma. No improved global coefficient follows yet.

**Revised budget option:** [disjoint bulk repair](disjoint-bulk-budget.md)
derives informal first-round bounds for the edge cuts and protected windows.
If bulk repair is confined to the central rectangle, it can run in parallel
with the funnels, allowing up to **107** bulk layers instead of 21. The
central construction and universal fringe theorem both remain open.

No production Lean files, tests, or builds were changed or run.
