# A common random scramble for small-rank capture and bulk mixing

Derived mathematical argument, 2026-10-10. Not Lean checked. This establishes
an informal existence argument for two parts of the separator contract; it
does not construct a shallow final repair or prove a better sorting bound.

## Result and hypotheses

Let `J=86000000`, `delta=128/4095`, `f>=131040`, `m>=f`, and `n>=16`.
Choose each row permutation independently and uniformly, as in the existing
Chvatal bulk proof. After sorting the input columns, scrambling rows, and
sorting columns again, consider every Boolean input with mass

```
j <= min(J, floor(delta*f*n)).
```

The probability that **some such input** leaves a marked output column of
height greater than `f`, in either high or low orientation, is at most

```
10^(-65457).
```

Therefore this small-rank capture guarantee can coexist with the existing
universal bulk guarantee: their failure probabilities add to less than one.
This uses the same independent-row family; no separate cyclic witness or
assumed independence between the bulk and fringe failure events is needed.
The bound covers the full small-rank support `min(J,delta*f*n)` for every
such `f`, including the candidate `262080`.

## Reduced witnesses

Put `k=f+1>=131041`. If a destination column receives at least `k` marks,
choose exactly `k` marked row heights, measured from the bottom. For each
source column used by those marks, keep only the largest selected height.
These heights define a reduced sorted input profile `w` that still sends all
`k` selected marks into the destination and has total mass at most `j`.

If `d` source columns are used, their largest selected row heights are
distinct: the row permutation has only one preimage of the fixed destination
in any one row. Consequently

```
mass(w) >= 1+2+...+d = d*(d+1)/2.
```

Thus `d<=13114`, and the convenient upper bound `D=13115` is sufficient.
This support bound is the key improvement over counting all input profiles.
The reduced witness depends on the bad scramble, but the union bound ranges
over the fixed finite family of all profiles with this support and mass bound.

There are at most

```
binom(n,d) * binom(J,d)
```

profiles of support exactly `d` and total mass at most `J`: choose the labels
and then the positive heights. The latter count is the standard sum of
compositions, `sum_{t=d}^J binom(t-1,d-1)=binom(J,d)`. Including profiles with
height greater than `m` only enlarges the count; the probability argument is
applied to valid profiles.

## Probability for a fixed witness

For a fixed reduced profile of mass `j'`, the number of marks sent into one
destination column is a sum of independent row Bernoulli variables with mean
`mu=j'/n`. Row independence, rather than independence of marks in the same
row, is sufficient here. Since

```
mu <= min(J/n, delta*f),
```

the elementary Chernoff bound gives

```
P[number of marks >= k] <= (e*min(J/n,delta*f)/k)^k.
```

For the union bound, retain only reduced profiles with mass also at most
`floor(delta*f*n)`. Their number is bounded by the larger family counted with
`J`; their probability still enjoys the stronger mean bound.

Union over destinations, supports, profiles, and the two orientations gives

```
P_fail <= 2*n * sum_{d=1}^D binom(n,d)*binom(J,d)
                    * (e*min(J/n,delta*f)/k)^k.
```

The low orientation is obtained by measuring heights from the top and marking
small keys. Uniform independent row permutations have the same law under row
reversal. Both bad-event probabilities are union bounded; no different
scramble is chosen for the low orientation.

## Uniform bound for every n

Use only `e<3`, `3*delta<1/10`, and the integer pivot `N=21000`.
For `n>=16`, the function

```
x -> x*ln(e^2*n*J/x^2)
```

is increasing on `0<x<=D`, because its derivative is `ln(n*J/x^2)>0`.
Hence the binomial bound gives

```
sum_{d=1}^D binom(n,d)*binom(J,d)
    <= D*(e^2*n*J/D^2)^D.
```

Here `n*J>D^2` holds already at `n=16`. Also

```
9*N*J/D^2 < 100000,
3*delta*f/k < 3*delta < 1/10,
3*J/(N*k) < 1/10,
2*N*D < 10^9.
```

For `16<=n<=N`, these inequalities yield

```
P_fail < 10^9 * 10^(5D) * 10^(-k)
       <= 10^(-65457).
```

For `n>=N`, write `t=n/N>=1`. The profile count introduces `t^D`, the
destination factor introduces `t`, and the Chernoff bound introduces `t^-k`.
Thus the same bound is multiplied by `t^(D+1-k)<=1`. This closes the
unbounded-column-count case rather than checking only representative sizes.

## Combining with the bulk witness

### Sharpening to f >= 65520

The same proof works for `f>=65520`, with uniform failure less than
`10^(-1500)`, using tighter scalar estimates. Keep `D=13115`, set `N=42000`,
and use `e<11/4`. (The exponential series through degree four is `65/24`;
the remaining tail is at most `(1/120)/(1-1/6)=1/100`, proving this bound.)
The required rational inequalities are

```
(121/16)*N*J/D^2 < 160000,
(11/4)*delta = 352/4095 < 43/500,
(11/4)*J/(N*65521) < 43/500,
2*N*D < 2000000000.
```

Thus for all `n>=16`, splitting at `N` exactly as above,

```
P_fail < 2000000000 * 160000^13115 * (43/500)^65521
       < 10^(-1500).
```

The rational inequalities were evaluated exactly with Python `Fraction`.
For the last logarithmic comparison, the exact rational interval routine in
`../paterson/uniform_concentration.py` gives an upper bound below
`-1500*ln(10)`; its approximate value is `-3572.21295`. That routine uses a
24-term positive atanh series with an explicit remainder bound and rational
normalization by powers of two. This is an arithmetic certificate outside
Lean, not a kernel-checked proof. The new scalar threshold is sufficient,
not asserted optimal.

This covers the smaller template fringe sizes as well. It does not lower
the bulk height threshold or pay for a final bulk repair.

### Joint witness

At first-round bulk error `e_B(m)=sqrt(2*(1+ln m)/m)`, the existing Lemma 6.1
argument gives universal bulk failure below `1/100` per orientation for
`m>=100,n>=16`. A union bound with the preceding two-sided small-rank event
is strictly below one. Therefore one scramble satisfies both:

1. universal first-round bulk control at that error; and
2. maximum intermediate height at most `f` for every supported rank `j<=J`,
   with the analogous top-fringe statement for small keys.

This is exactly the intermediate promise needed for the two-round bulk
variance calculation and zero-escape propagation. After the intermediate
sort, these rare keys are already in their fringe rows. A second row scramble
and any ascending final repair preserve that capture, so rare-rank compaction
consumes no additional final-repair layers.

The existing bulk proof and this counting argument must still be integrated
with the semantic/physical common-witness bridge in Lean. No axiom or proof
adapter is introduced by this note.

## What remains

- Prove the elementary reduced-witness lemma, Bernoulli tail bound, profile
  count, and uniform scalar bound formally if this route is promoted.
- Establish relative fringe error for ranks `j>J`. This argument provides no
  estimate at those ranks and does not evade the existing one-round obstruction.
- Construct the shallow bulk repair with an explicit error reserve. Full
  second-round sorting still costs too much for coefficient below 1000.
- Handle template scaling and small-node fallback within the ordinary budget.

The substantive progress is a **joint small-rank-and-bulk existence argument**
in the existing scramble family, not an improved complete separator.
