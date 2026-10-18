# Disjoint bulk repair: recovering the 107-layer budget

Informal derivation, 2026-10-10. This supplies a possible modular interface and
first-round probability estimates, not a bulk repair construction or an
improved sorting theorem. It corrects the assumption that all bulk work must
be charged sequentially after the 86-layer fringe funnels.

## The physical split

The fringe funnels touch only the top and bottom `T=2^33` rows. Let a bulk
repair touch only the central rows, excluding these two windows. Then their
layers can execute in parallel: the combined repair costs

```
max(86, d_bulk), rather than 86+d_bulk.
```

At column height at most `2^43`, the first two column sorts cost `1892`.
Consequently a central repair of depth at most **107** fits a stage ceiling
of `1999`. The earlier 21-layer budget applies to a sequential implementation,
not to this disjoint implementation. Arbitrary routing outside the central
rows is not included and would need to be charged.

There are two obligations: the edge bulk cuts `i=f,m-f` need no central
repair, and central repair must tolerate incorrect threshold bits left inside
the protected edge windows. Neither follows just from the fringe theorem,
whose ranks stop at `4096*n`, whereas the edge bulk rank is `f*n`.

## A rank-sensitive first-round bound

For an input sorted profile of exact total mass `i*n`, and a set `S` of `s`
destination columns, let `X_S` be their total marks after the first scramble.
Its mean is `i*s`. The Poisson exponential-moment inequality underlying
`AKS/Chvatal/Lemma62Tail.lean` gives

```
P[X_S >= i*s+t] <= exp(-t^2/(2*(i*s+t/3))).
```

This sharper centered form is obtained by retaining the `-lambda*mean` term
in Markov's inequality and using, for `0<=lambda<3`,
`exp(lambda)-1-lambda <= lambda^2/(2*(1-lambda/3))`.
The latter follows term by term from `k!>=2*3^(k-2)` for `k>=2`.
Choose `lambda=t/(i*s+t/3)` to obtain the displayed bound.

If the sorted output heights have `E_i=sum_c(z_c-i)_+ >= A*n`, their overflow
columns supply a set `S` with `X_S>=i*s+A*n`. Union over at most `2^n` column
sets and at most `(m+1)^n` input profiles yields

```
P[exists input profile with E_i >= A*n]
 <= exp(n*[ln(2*(m+1))-A^2/(2*(i+A/3))]).
```

The profile count deliberately overcounts exact-mass profiles. The key
improvement over a height-only bulk estimate is retaining variance scale `i`
rather than replacing it by `m`.

## The two edge bulk cuts are cheap

Set `f=131040`, `A=4096`, and `m<=2^43`. At `i=f`, the exponent margin

```
A^2/(2*(f+A/3))-ln(2*(m+1)) > 31
```

holds by rational logarithm intervals (at the largest height it is about
`32.857`). Therefore one first scramble can make the high-side edge error
less than `4096*n` for every exact-rank `f*n` profile; the analogous low-side
statement follows by reflection. At rank `(m-f)*n`, use exact mass and the
identity between holes in the bottom region and high marks above its cut,
then apply the low-rank reflected estimate.

The second scramble preserves counts in every row region. All subsequent
ascending comparators decrease high-prefix and low-suffix error. Thus these
edge bulk bounds persist through both repairs, without adding comparisons.

For the intended geometry `m>=2^42`, the actual bulk allowance per column
`paperOrdinaryEpsB*m/2` is about `37183` at the lower endpoint and increases
with `m`. Hence `4096` is well within it. This comparison still needs the
exact constant and actual integer template ranges in the final formal proof;
it is not permission to replace `paperOrdinaryEpsB` by `1/59000000`.

## Protecting the edge windows at interior thresholds

For an interior cut `i=f+k*b`, `1<=k<=63`, suppose

```
i >= m/65, m-i >= m/65, m>=2^42, m<=2^43.
```

These follow in the nominal geometry from `b=(m-2*f)/64`; rounded templates
need their own inequalities. In particular `T<=i/4` and `T<=(m-i)/4`.

For the high-key threshold of rank `i*n`, let
`D=sum_c(T-z_c)_+` be holes in the bottom window after the intermediate sort.
If `D>=A*n`, its deficient columns `S` satisfy `s>=A*n/T` and receive at most
`T*s-A*n` high marks. Apply the positive exponential-moment bound to the
complement marks instead. Their mean is `(m-i)*s`, and their excess is at
least `(i-T)*s`. The actual threshold cannot exceed `m*s`, so the Bernstein
denominator is at most `2*m*s`. Consequently the fixed-profile/set event has
probability at most

```
exp(-(i-T)^2*s/(2*m))
 <= exp(-9*i^2*s/(32*m))
 <= exp(-9*m*A*n/(32*65^2*T)).
```

This uses only the positive-moment bound, not an unproved negative-moment
adapter. Union over profiles and column sets gives exponent margin

```
9*m*A/(32*65^2*T) - ln(2*(m+1)).
```

With `A=2048` and the displayed height range this is greater than `39`:
the first term is at least `69.80`, while the log term is below `30.51`.
Thus one first scramble can simultaneously bound bottom-window holes by
`2048*n`. The reflected complementary calculation bounds high marks in the
top window by `2048*n`. Finite union over interior ranks and orientations
can coexist with the earlier first-round promises; independence of success
events is not required.

These region totals are preserved by the second row scramble. Fringe
comparators only improve them. At each interior threshold, the final state
therefore has at most `2048*n` high keys in the protected top window, and at
most `2048*n` holes in the protected bottom window. This is an aggregate
statement; it does not make every protected column perfect.

## Central bulk-repair interface still to construct

In the central rectangle of height `m-2*T`, the bulk cut has local height
`i-T`. Its total high mass can differ from `(i-T)*n` by at most `2048*n`,
since the difference is bottom-window holes minus top-window high marks.
The original interior height profile remains the intermediate sorted profile
restricted to this rectangle, followed by the second row scramble.

A sufficient central theorem is a fixed ascending network, confined to this
rectangle, of depth at most `107`, with central high-prefix error at every
interior cut at most

```
EB - 2048*n,
```

for all reachable threshold profiles, both orientations, and the same second
scramble. The statement must explicitly allow the mass perturbation above.
Adding the protected top-window contribution then proves the global bulk
bound. Fringe guarantees remain valid and their random input law is unchanged
because the networks use disjoint wires.

No such central network is supplied here. Plausible next candidates are
approximate partitions at the 63 interior cuts, using disjoint bands only
after proving an aggregate bound on errors outside those bands. The existing
first-round L1 promise does not imply a maximum displacement bound, so simply
declaring short sorted runs or a clean band is invalid.

**Subsequent progress:** [the central feasibility audit](central-bulk-feasibility.md)
derives a stronger common localization promise, reserves its errors using
a smaller profile entropy count, and supplies a 631-layer exact band-cut
repair baseline. The requested 107-layer central repair remains open.

## Status and next decision

The edge estimates give a concrete way to remove the artificial 21-layer
sequential budget. The next mathematical tasks are now:

1. Prove or refute the universal fringe dependency-graph inequality.
2. Construct or obstruct a central 107-layer approximate bulk partitioner
   under the actual row-scrambled input class and perturbed mass promise.
3. Verify the geometry, common-witness probability sums, physical scheduling,
   and small-node fallback before asserting any global coefficient.

The moment, symmetry, and count adapters remain informal. No Lean changes,
tests, or builds were performed.
