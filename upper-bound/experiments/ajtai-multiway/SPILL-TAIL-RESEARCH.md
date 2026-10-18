# Joint column-spill tail: proof target and repair contract

Status: research plan and diagnostic, not a theorem. This note concerns the
two-round row-permutation construction in `docs/ajtai1992.pdf`, pp. 691-692.
The paper proves an aggregate leakage estimate; it does not state the column
tail estimate proposed here.

## Tail event in the paper's random-permutation model

Fix a monotone input matrix with column heights `c_j` and total weight `m`.
For a fixed set `S` of `r` output columns, let `Y_S` be their total number of
ones after the independent row permutations. Its mean is `r*m/N`. The same
hypergeometric Hoeffding estimate used in Appendix 4.1 gives

```text
Pr[Y_S >= r*a] <= exp(-2 (r*a-r*m/N)^2/(k*r)),   a > m/N.
```

At row cut `h`, spill width `w` corresponds to `a=k-h+w`. Thus `Q_h(w)>=r`
implies this event for at least one `r`-set `S`. A direct union bound over
sets and all inputs of weight `m` is

```text
#{inputs of weight m} * binom(N,r)
  * exp(-2*r*(k-h+w-m/N)^2/k).
```

The crude input count `binom(m+N-1,N-1)` is much too large for the desired
`r=O(p), w=O(k/p)` regime. Its entropy contribution is order `N log k`, while
the fixed-set concentration exponent is only order `r*w^2/k = O(p)` when
`k=p^2`. This diagnoses why the current weak-composition screen cannot prove
the desired tail; it is not evidence the tail property is false.

For a concrete diagnostic, take the middle cut, `r` equal to the adversarial
one-bin floor already recorded in `BELOW-200-PLAN.md`, and rank
`m/N=k/2-w`. The standard entropy upper bound for the log of the union term,
divided by `N`, is
`g(mu)+H(r/N)-2(r/N)(k-h+w-mu)^2/k`, with
`g(mu)=(mu+1)log(mu+1)-mu log(mu)`. It is positive by a wide margin:

| `(k,p,N)` | `w` | `r` | concentration exponent | coarse log-union bound / `N` |
|---|---:|---:|---:|---:|
| `(1024,32,1024)` | 32 | 15 | 120 | 7.134 |
| `(256,16,256)` | 16 | 7 | 56 | 5.630 |

This is a deliberately coarse screen, not a certified tail probability. It
does establish that the existing weak-composition count is nowhere near the
desired event estimate, even before summing over cuts and ranks.

## How to adapt the paper's equivalence classes

For a rank `m=p_0 N` and target row cut `s`, the paper sets
`D=(p_0+k/2)/2` and identifies inputs having the same top (the first
`k-D` rows) and the same total weight. If any member of a class has a
monotone event, replacing its bottom `D` rows by ones preserves monotonicity
and contains that member entrywise. Since each row permutation preserves
entrywise order, the replacement also preserves the event. Therefore one
representative per top suffices for the union bound.

For the spill event the event is monotone: `Q_h(w)>=r` means there exists an
`r`-set of output columns whose column sums are at least `k-h+w`. This lets
the same representative reduction apply. The remaining work is precise and
finite:

1. For each rank `m`, cut `h`, orientation, and `r`, count distinct tops using
   Appendix Lemma 3's recurrence (not the weak-composition count).
2. For each top, use its filled-bottom representative. Its weight `m'` is
   generally larger than `m`; apply the fixed-set tail bound with mean
   `r*m'/N`, not `r*m/N`. If `m'/N >= k-h+w`, that class gives no useful
   concentration bound and must be grouped/handled separately.
3. Sum over tops, ranks, cuts, and both orientations, retaining exact
   integer ranks and outward rounding. First test whether any plausible
   threshold `r=Cp` and width `w=Bk/p` yields total probability below one.

The delicate point is step 2: the paper's event is a rank-relative *total*
leakage event, whereas this event requires `r` columns each to cross a fixed
occupancy threshold. The representative's filled bottom can erase the
deviation that Hoeffding needs. So the equivalence-class idea transfers, but
the published aggregate estimate cannot simply be quoted as the desired
column-tail theorem.

For the paper's cutoff `D=(mu+k/2)/2`, its representative has average height
at most

```text
mu' <= mu + D = 3*mu/2 + k/4.
```

At the middle cut, `a=k/2+w`, so even the *possibility* of a positive
Hoeffding deviation requires
`mu < k/6 + 2*w/3`. With one-bin width `w=k/p`, this is only about `k/6`
for the parameters of interest:

| `(k,p)` | `w=k/p` | largest `mu` allowed by `mu+D<a` |
|---|---:|---:|
| `(1024,32)` | 32 | 192 |
| `(256,16)` | 16 | 53 1/3 |

Thus the filled-bottom argument is useful, at best, for sparse ranks. It gives
no deviation bound for most ranks up to `k/2`. Choosing a shallower filled
band reduces this rank inflation, but reveals more of the input and loses the
top-count compression; the paper's one-cutoff balance was designed for its
aggregate leakage threshold, not this much smaller `r*w` surplus.

There is a tempting event-specific variant: for a fixed exceptional set `S`,
fill only those input cells which can contribute to `S`. But the relevant
source set in row `i` is `sigma_i^{-1}(S)`, so this representative depends on
the random row permutations being bounded. A union bound over these adaptive
representatives must also pay for their possible row-by-row source sets; the
apparent mass saving is not free. Filling every possible source cell restores
independence but returns to the large filled-bottom representative. This
closes the simplest proposed repair to the equivalence-class argument.

The exact missing probability problem can be written without referring to
equivalence classes. For fixed `S` of size `r`, let
`B_ij = 1[j in sigma_i^{-1}(S)]` and let `c_j` be input column heights. Then

```text
Y_S(c) = sum_j sum_{i <= c_j} B_ij,
sum_j c_j = m.
```

After centering, `Y_S(c) - r*m/N` is the sum of the column prefix deviations
`sum_{i<=c_j}(B_ij-r/N)`. A useful proof must control the maximum of this
quantity over *all* height profiles of mass `m` and all `r`-sets `S`, while
also converting a large selected-set sum into a lower bound on the number of
individual columns above threshold. The ordinary fixed-input Hoeffding bound
does not control this supremum. This is now the right formulation for a new
uniform empirical-process/discrepancy estimate, or for designing row
permutations with a built-in discrepancy guarantee.

## Repair interface required after a tail theorem

A useful theorem must be simultaneous for every row cut and both orientations,
and supply an explicit envelope `Q_h(w) <= R(w)`. A lone bound at the middle
cut is inadequate: comparator layers for one cut must not silently destroy
the guarantees at the other cuts. The forced-tail construction in
`BELOW-200-PLAN.md` already shows that `R(k/p)=0` is impossible; for the
screened tuples at least 15 (respectively 7) columns can be forced to spill
by one bin width.

Even `R(k/p)=O(p)` would not itself give a cheap repair. A fixed comparator
network cannot be told which columns are exceptional. The repair proof must
provide an oblivious way to gather/funnel their offending wires, sort or
reinsert them, and preserve all other cut guarantees. Its contract should
state:

```text
input:  individually sorted columns + simultaneous envelopes R(w)
output: an ordered p-way partition with stated fringe error at every cut
cost:   explicit binary-comparator depth G(k,p,R), independent of the input
```

Only after constructing that network can we charge `T+G` in a recursive
schedule. Charging a full sort of all `kN` wires is not a sparse repair; the
claimed savings must come from a proved oblivious routing/repair network.

## Go/no-go sequence

1. Derive the exact top-count bound from Appendix Lemma 3, including endpoint
   rounding and representative weights.
2. Implement a small outward-rounded tail certifier over `(h,m,r)` and first
   test `(1024,32,1024)` and `(256,16,256)`.
3. If the class bound closes only for `w` much larger than `k/p`, update the
   repair geometry and recompute its depth before proceeding.
4. In parallel on paper, formulate the oblivious repair interface; do not
   treat an existential identification of exceptional columns as a network.
5. Stop this route if the class bound is vacuous for every useful `(r,w)`, or
   if the only repair costs as much as a full sorter. Then seek a construction
   with built-in locality rather than spend time formalizing a failed screen.

The audit result is negative but informative: the aggregate AKS certificate
and the published equivalence-class count do not immediately yield an `O(p)`
one-bin column tail. The single-cutoff filled-bottom argument loses its
concentration gap on most ranks, and an event-specific representative is
adaptive to the random network. A successful extension needs a uniform
joint-event/discrepancy estimate or a construction with built-in locality,
not a relabeling of the paper's existing bound.
