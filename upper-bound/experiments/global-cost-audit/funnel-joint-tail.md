# A joint-column inequality and a fixed-input exponential tail

Informal derivation, 2026-10-10. This resolves a probability adapter left open
in [the count-transition note](funnel-count-transition.md). The universal
source-profile union bound remains open; no improved sorting theorem follows.

The relevant published framework is negative association, introduced in
[Joag-Dev and Proschan, 1983](https://doi.org/10.1214/aos/1176346079).
The special binary sampling case needed here has the elementary argument below.
This is an informal proof, not a Lean import or a new axiom.

## 1. A uniform binary row is negatively associated

Let a row be a uniformly chosen set of `k` marked columns. For increasing
functions `f,g` of disjoint coordinate subsets `A,B`, condition on the number
`t` of marks in `A`. Given `t`, the pattern in `A` is independent of the pattern
in the remaining coordinates. Therefore

```
E[f*g] = E[F(t)*G(t)],
F(t)=E[f | t], G(t)=E[g | t].
```

`F` is increasing: couple uniform `t`-subsets in `A` by adding one random
element. `G` is decreasing: the remaining coordinates receive a uniform
`(k-t)`-subset, which can be coupled by deleting marks as `t` increases.
For an independent copy `t'`,

```
2*Cov(F(t),G(t))
 = E[(F(t)-F(t'))*(G(t)-G(t'))] <= 0.
```

This proves `E[f*g]<=E[f]*E[g]` for the row.

Independent unions retain this property. For two independent coordinate
families, first condition on one and apply the inequality to the other;
the resulting conditional expectations are increasing functions on disjoint
subsets of the conditioned family, so applying its inequality completes the
proof. Induct over the independently scrambled rows.

## 2. Column-local tournaments allow a product mgf bound

Fix an intermediate profile and all tournament partitions. The exterior
output count `R_c` in column `c` is increasing in the input bits of that
column: ascending Boolean comparators are coordinatewise monotone. Distinct
columns use disjoint coordinates. Hence for `theta>=0`, iterating the
preceding inequality gives

```
E[exp(theta*sum_c R_c)] <= product_c E[exp(theta*R_c)].
```

The input columns need not be independent. Now average over the partitions.
Their choices are independent across columns, and each factor on the right
depends only on that column's partitions. Thus the same product bound holds
after this averaging. This step uses the specified independent partition
sampling; it is not a claim that arbitrary mixtures preserve negative
dependence.

The argument is for a fixed intermediate profile. Conditioning on the
first scramble is legitimate once that profile is fixed, but it does not
replace the subsequent all-profile existence argument.

## 3. Exponential tilting turns the moment estimate into a tail

Use the original funnel parameters and phase-specific root bounds from
[the pair-witness calculation](funnel-pair-witness.md). Write

```
mu_max = eta*a0 = 4096/3650,
C(x) = p_0^2+p_0*kappa_0
     + (2*p_0*kappa_0+tau_0)*x + q_0*x^2,
F_0(x)=x,
F_1(x)=p_0*F_0(x)+kappa_0*x^2/2,
F_(i+1)(x)=p_i*F_i(x)+kappa_i*C(x)*x^2/2  (i=1,2,3),
F(x)=F_4(x).
```

Here `tau_0,q_0` are the first-phase triple and pair-pair bounds. `F` is a
polynomial with nonnegative coefficients, and bounds expected final exterior
count for independent initial Bernoulli row marks of total mean at most `x`.

Let `H_0` be the initial exterior count in one column, with mean
`mu<=eta*j/n`. We always have `0<=R_c<=H_0`, and

```
2^R_c-1 <= R_c*2^H_0.
```

Tilting the independent exterior Bernoulli variables by `2^H_0` changes a
probability `q` to `2*q/(1+q)<=2*q`; their tilted total mean is at most `2*mu`.
The protected root rows and partition choices are independent of these
variables, so their distributions are unchanged by this tilt. Furthermore
`E[2^H_0]<=exp(mu)`. Consequently

```
E[2^R_c] <= 1 + exp(mu)*F(2*mu).
```

Combine this with the joint-column bound and `ln(1+y)<=y`:

```
ln E[2^sum R_c] <= n*exp(mu)*F(2*mu).
```

Since `mu<=mu_max<ln 4`, and `F(x)/x` is increasing, this is at most

```
j * 4*F(2*mu_max)/a0.
```

Rows outside the window contribute fewer than `(40/T)*j` escapes. Thus a
fixed profile/rank fails the strict fringe target only if

```
sum_c R_c > (epsilon-40/T)*j.
```

Markov at `theta=1` improves the fixed-input exponent. Since `e<11/4` and
`7*mu_max/4<ln 8`,

```
(e-1)*exp(mu*(e-1))*F(e*mu)
 <= 14*F((11/4)*mu_max).
```

Thus Markov at `theta=1` gives

```
P[fixed profile/rank fails] <= exp(-c*j),
c = epsilon-40/T - 14*F((11/4)*mu_max)/a0
  > 5.5e-9.
```

Rational evaluation with rational log intervals gives

```
F((11/4)*mu_max) = approximately 4.17600850175e-7,
c > 5.54394744779e-9.
```

The reported decimal for `c` is a conservative lower interval endpoint. The
weaker rational constant `5.5e-9` avoids depending on its displayed digits.
Small ranks already confined before the second scramble have failure
probability zero by the earlier deterministic argument.

## 4. The universal theorem still needs reduced profiles

This exponential bound is a genuine fixed-input improvement over Markov's
constant failure bound. It uses the actual dependence between columns.
However, it does not yet beat a naive union over all source profiles: at
`j=a0*n`, its certified rate is only `0.000022528*n`, while the coarse profile
entropy is of order `n*ln(m+1)`.

Even a first reduction to every intermediate tail profile above `g` is too
coarse. Such tails have total mass at most `eta*j` and support at most `j/g`.
At `j=a0*n`, writing `alpha=a0/g` and `tau=eta*a0`, the elementary binomial
entropy bound for their number has exponent

```
n*[h(alpha)+tau*h(alpha/tau)] < 0.397*n,
h(x)=-x*ln(x)-(1-x)*ln(1-x).
```

By comparison the fixed-profile failure rate supplies only `0.000016384*n`.
Thus conditioning on an arbitrary good first-round profile and unioning over
all such profiles cannot work with this tail estimate. The first scramble's
probability cost must be kept in the same witness calculation as the second
scramble and funnel survival.

The reduced failure certificate must distinguish three sources of survivors
in each phase: old exterior marks that collide in one balanced group, marks
blocked by a high fresh root, and groups with neither event (which lose one
mark). Root marks have a useful deterministic aggregate constraint: in each
physical row, their total over columns is exactly the input row count `a_r`,
and across a reservoir chunk these counts sum to at most `eta*j`. This alone
does not bound roots in survivor-selected groups, since those groups depend on
the scramble. A successful count must combine this row budget with a
simultaneous hit bound and the source-height cost of selected cells.

For `j<=h/eta=172280000`, exact small-rank capture avoids the issue entirely.
For larger ranks, if a set of `K>epsilon*j` survivors is traced backward, its
number of distinct initial exterior leaves lies between `K` and `16*K`.
Simply counting all `16*K`-leaf source profiles is far too expensive; the
lineages may share a root or collision partner. The required object is the
merged phase-by-phase dependency graph, weighted by distinct source rows and
by the height cost of their preimages under both row scrambles.

Even enumerating all tails above `g` loses too much. Only a reduced family of
profiles that actually witnesses tournament failure can plausibly close the
union bound. Its count must charge each source column's maximum selected row
and merge shared roots, partners, and groups. This remains the next open
fringe task; the joint-column dependence is no longer the missing informal
probability adapter.

No Lean changes, tests, or builds were performed. The published framework was
checked against its primary abstract; the specialized argument and numerical
bounds above were derived locally.
