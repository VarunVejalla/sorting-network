# Two-round relative fringe: a conditional counting proof

Derived mathematical argument, 2026-10-10; not Lean checked. This note gives
an informal uniform fringe-existence argument in the independent-row scramble
family. It still uses a full final column sort. It neither constructs a shallow
repair nor establishes an improved global sorting bound.

## Parameters and the result to audit

Use these fixed parameters (row counts, not wire counts):

```
f = 262080,             g = 157248,
H = g/2 = 78624,        h = f-g = 104832,
delta = 128/4095,       a0 = delta*f = 8192,
eta = 1/5800,          epsilon = 1/86000000.
```

For `m>=f` and `n>=16`, the proposed construction is

```
column sort; sigma_1; column sort; sigma_2; column sort.
```

The claim derived below is existence of one pair of scrambles providing both
orientations of the relative fringe guarantee for **every**
`0<j<=floor(a0*n)`. The first scramble can also provide the usual universal
bulk guarantee. The second can coexist with the separate two-round bulk
variance bound, if that bound is proved on the same input class.

Unlike the earlier small-rank-only calculation, ranks here are unbounded as
`n` grows. The proof does not enumerate ranks at representative matrix sizes.

The probabilistic primitive is already present as
[`scramble_tail_fixed_set`](../../best/AKS/Chvatal/Lemma62Tail.lean): for fixed
monotone input, row region, and `s` destination columns, with at most `T` marks
in that region, the probability of at least `K>=T*s/n` hits is at most
`(e*T*s/(n*K))^K`. The new witness counts and scalar estimates below are
informal adapters to that kernel-checked primitive.

## First scramble: moderate relative control at the inner fringe

Let `z` be the input sorted-column heights with total mass `j<=a0*n`.
If the first output heights have excess at least `eta*j` beyond row height
`g=2H`, take their overflowing destination columns `S`, `|S|=s>=1`.
They receive at least `g*s+eta*j` marks. At most `H*s` of these can originate
in the bottom `H` rows, so the region above those rows supplies at least

```
K = H*s + eta*j
```

hits into `S`.

Shrink each active source column above row height `H` to the last selected
hit. If `d` source columns remain, their original mass includes at least
`H*d`, giving `d<=j/H`. Their positive tail heights sum to at most `j`.
Consequently there are at most

```
binom(n,d)*binom(j,d)
```

possible reduced tail profiles of support `d`. This overcounts profiles
whose base-plus-tail mass exceeds `j`; such profiles need not be used as
witnesses. The counted tail mass bound suffices for the tail probability.

If `j<=H`, the region above height `H` is empty and no bad event is possible.
The support-sum estimate below is used only on the nonempty branch `j>H`.

For fixed `j,s`, put

```
y=j/s,       v=n*a0/j>=1,
A=y/H,      B=H+eta*y,       K=s*B.
```

The binomial bound and monotonicity of
`d*ln(e^2*n*j/d^2)` up to `d=j/H` give

```
sum_d binom(n,d)*binom(j,d)
 <= (j/H)*(e^2*n*j/(j/H)^2)^(j/H).
```

Monotonicity is valid because `n*j/(j/H)^2=n*H^2/j>=H^2/a0>1`.
Combine this with `binom(n,s)<=(e*n/s)^s` and the fixed-set tail bound.
The logarithmic exponent divided by `s`, excluding the prefactor `j/H`, is

```
Phi_1 = ln(e*y/a0) + (y/H)*ln(e^2*H^2/a0)
        + B*ln(e*a0/B) + (1+A-B)*ln(v).
```

Since `eta*H>1`, the coefficient of `ln(v)` is negative. Since `y<=B/eta`,
the remaining terms divided by `B` are bounded above by

```
C_1 = [1+ln(H/(eta*a0))]/H
      + [2+ln(H^2/a0)]/(eta*H)
      + 1+ln(a0/H)
    < -1/10.
```

Here the first term uses that `(1+ln(B/(eta*a0)))/B` decreases for `B>=H`.
The profile term uses `(y/H)/B<=1/(eta*H)`. The last term uses `B>=H`.
The resulting one-orientation bad-event bound for fixed `j,s` is

```
(j/H)*exp(-(H*s+eta*j)/10).
```

Summing over all positive `j,s` only enlarges the finite supported family.
Using `1-exp(-eta/10)>=eta/20` and
`exp(-H/10)/(1-exp(-H/10))<=2*exp(-H/10)`, the two-sided sum is at most

```
1600/(H*eta^2) * exp(-H/10) < 10^(-2000).
```

Therefore one first scramble satisfies

```
E_g(z_after_first_sort) < eta*j
```

for every supported rank and input in both orientations. Union with the
existing bulk bad events (less than `1/100` per orientation) still leaves
positive probability. This chooses a **common** first witness.

In particular, all ranks `j<=h/eta=608025600` already have every intermediate
height at most `f`, hence exact row confinement before the second scramble.
The smaller small-rank witness theorem is not additionally needed for this
parameter choice; it remains a separate useful interface.

## Second scramble: reduced witnesses with a multiplicity bound

The intermediate region above the bottom `g` rows has total tail mass
`T<eta*j`. If the final column sort has excess at least `epsilon*j` beyond
height `f=g+h`, its overflowing set `S` receives at least

```
K=h*s+epsilon*j
```

marks originating above the bottom `g` rows. Otherwise the at-most-`g*s`
contribution from those bottom rows would leave less than the claimed excess.

Here `T` is the actual integer tail mass. Strictness means
`T<=ceil(eta*j)-1`; the entropy and probability bounds safely relax this to
the real upper bound `eta*j`. Profile counting uses `binom(T,d)` for the
integer mass, while real thresholds in the tail bound are supported by the
existing theorem. The earlier expression `binom(floor(T),d)` is equivalent
because this `T` is an integer.

Choose `ceil(K)` hits and shrink each active source tail to its last chosen
row height. Each row has at most `s` selected preimages because it maps into
`S`. Thus the maxima of `d` source tails have multiplicity at most `s`, and
their sum is at least

```
sum_{q=1}^d ceil(q/s) >= d^2/(2*s).
```

Their sum is at most `T`; hence `d<=sqrt(2*T*s)`. This is the reduced-witness
support bound that replaces the much larger count of unrestricted profiles.
There are at most `binom(n,d)*binom(floor(T),d)` such reduced tails.

Set

```
y=j/s,         v=n*a0/j>=1,
A=sqrt(2*eta*y),   B=h+epsilon*y,   K=s*B.
```

The sum over tail supports costs a prefactor at most `s*A` and the profile
exponent `s*A*ln(e^2*n/(2*s))`. The entropy function is increasing up to this
support bound whenever `n>2s`. A nonzero event requires `K<=T`, which implies
`s<=eta*j/h<=eta*a0*n/h<n/2`; otherwise the event is impossible. This justifies
the monotonicity without assuming that `S` is a small set in advance.

Combining the profile count, destination-set count, and fixed-set tail yields

```
Phi_2 = ln(e*y/a0) + A*ln(e^2*y/(2*a0))
        + B*ln(e*eta*a0/B) + (1+A-B)*ln(v).
```

Put `J=1/epsilon` and `r=27/100`. The arithmetic-geometric mean inequality gives

```
A/B <= sqrt(eta*J/(2*h)) < r.
```

Also `B>=h` and `y<=J*B`. Hence the coefficient of `ln(v)` is negative and

```
Phi_2/B <= [1+ln(J*h/a0)]/h
           + r*[2+ln(J*h/(2*a0))]
           + 1+ln(eta*a0/h)
         < -4.
```

The log multiplying `A/B` is positive on nonempty events, so substitution of
the upper bound `r` has the required direction. Collecting the `ln(B)` terms
gives coefficient `r-1<0`, allowing replacement by `ln(h)`.

The prefactor `s*A=sqrt(2*eta*j*s)` is at most `j*s` for positive integers.
Consequently the two-sided union over all positive ranks and destination-set
sizes is bounded by

```
2 * sum_j j*exp(-4*epsilon*j) * sum_s s*exp(-4*h*s)
 <= 2*J^2*exp(-4*h) < 10^(-125000).
```

This second witness works uniformly for all intermediate tail profiles with
the first-stage mass promise, not just one input. There is no exchange of
input and scramble quantifiers. It can therefore be union bounded with a
universal second-stage bulk event proved on that class.

## Available reserve for a future repair

The same calculation can target `epsilon/2`: replace `J` by `172000000`
and use `r=38/100`. The last scalar upper bound is below `-1`, leaving a
summable tail and thus a strictly positive-probability second witness. This
supplies an informal **half-fringe-error reserve** for ranks not already
confined before the second scramble.

That reserve is a count allowance, not a repair construction. A column-local
replacement of the last sort must bound its extra fringe escape by the
remaining allowance while also delivering all bulk cuts. Exact small ranks
must remain lossless; those covered by the first-stage row-confinement promise
are automatically preserved by ascending comparators.

## Arithmetic checks and open adapters

Exact rational logarithm intervals from
`../paterson/uniform_concentration.py` give the following upper bounds:

```
C_1 < -0.1154459       (certified < -1/10),
C_2 < -4.2406099       (certified < -4),
C_2 at epsilon/2 < -1.5433570 (certified < -1).
```

Only the decimal displays are approximate; the comparisons with the rational
thresholds were evaluated with `Fraction` and explicit logarithm remainders.
These are not Lean certificates. The elementary witness reductions, profile
counts, orientation adapters, common-witness construction, and all-real
threshold bookkeeping still require mathematical review and formalization.

The result is shown at the stated exact fringe geometry. Extending it uniformly
to larger or rounded geometries requires checking the parameter inequalities,
not silently treating this instance as a general construction theorem.

## Global cost consequence

At the current minimum fringe ratio `f/m=4095/2^37`, `f=262080` corresponds
to height `m=2^43`. Scaling templates above that lower height typically needs
the ceiling `2^44`, where three bitonic sorts cost `2970` ordinary layers and
give coefficient `1485` **conditionally** on complete geometry, bulk and
fallback adapters. This is a candidate improvement over `1770`, not a proved
endpoint. The separate two-round bulk theorem also remains informal.

For a strict sub-1000 coefficient, two height-`2^44` sorts cost `1980`, leaving
only **19** layers for a replacement last operation. This note provides no
such operation. At smaller fringe `131040`, the corresponding two-sort repair
budget is more attractive, but the present coupled scalar bounds do not close.
Thus the new fringe argument does not establish the desired sub-1000 path.
