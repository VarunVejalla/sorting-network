# An aggregate reachable-tail interface

Informal derivation, 2026-10-10. No Lean changes or improved global bound.
This follows the many-column obstruction in
[the height-envelope investigation](reachable-height-envelope.md).

## A stronger common-witness property

The first-stage moderate-fringe proof generalizes to a whole set of row
heights. For one first scramble, propose simultaneously, in both orientations,

```
E_t = sum_c max(z_c-t,0) < (40/t)*j
```

for every supported rank `0<j<=8192*n` and every dyadic threshold
`t=2^ell`, `ell>=18`, `t<=m`. Here `z` are the heights after the first
scramble and intermediate column sort. This is an aggregate tail promise,
not merely a bound on the largest height.

Use the earlier first-stage counting argument with

```
H=t/2, eta_t=40/t, a0=8192.
```

Its normalized exponent is bounded above by

```
C(t) = (2/t)*[1+ln(t^2/(80*a0))]
       +(1/20)*[2+ln(t^2/(4*a0))]
       +1+ln(2*a0/t).
```

At `t=2^18`, exact rational logarithm intervals certify `C(t)<-9/10`.
The derivative of the first term is
`(2/t^2)*[1-ln(t^2/(80*a0))]<0` at and above that threshold; the remaining
terms have derivative `-9/(10*t)`. Thus `C(t)` decreases throughout the
range. Using only the weaker bound `C(t)<-1/10`, the two-sided failure
probability at threshold `t` is at most

```
1600/(H*eta_t^2)*exp(-H/10) = 2*t*exp(-t/20).
```

Summing over dyadic thresholds is finite and bounded independently of `m`
by an extremely small geometric tail. This can be union bounded with the
previous bulk and moderate-inner-fringe bad events. It gives a common first
witness for the stronger aggregate property without assuming independent
success events or choosing a new scramble at each threshold.

The witness reductions and orientations inherit the same outstanding formal
adapters as the moderate-fringe note; the derivative and scalar comparisons
were checked informally, with the endpoint log inequality checked by exact
rational intervals. This is not a kernel certificate.

## Why this is different from maximum-height control

For the many-tall-column example `j=m^2`, its excess at `t=m/2` is about
`m^2/23200`. The new bound permits only

```
40*j/(m/2) = 80*m.
```

For the template heights this excludes the entire example, even though its
individual maximum height obeyed the square-root envelope. It controls the
number and total mass of tall columns, which is the information the failed
maximum-height interface omitted.

Excluding this witness does not prove that the entire strengthened interface
admits a 19-layer repair. No such claim is made.

## A concrete fringe-only consequence

Choose the fixed row height `T=2^33`. The all-scale promise gives

```
E_T < (40/2^33)*j < (epsilon/2)*j,
epsilon=1/86000000.
```

The second row scramble preserves this number of marks outside the bottom
`T` rows. Instead of fully sorting each final column, sort only its bottom
`T` entries for high-key capture, and its top `T` entries for low-key capture.
These regions are disjoint when `m>=2T` and run in parallel. Their bitonic
depth is `33*34/2=561`.

For a high threshold, let `s_c` be the full column count and `b_c` its count
in the bottom `T` rows after the second scramble. Sorting that window gives
total fringe escape

```
outside-window mass + sum_c max(b_c-f,0)
 <= outside-window mass + sum_c max(s_c-f,0).
```

Thus a common second scramble with ideal full-sort fringe escape below
`epsilon*j/2`, as in the earlier reserve calculation, yields actual fringe
escape below `epsilon*j` after window sorting. The reflected argument gives
the low side. Small ranks already confined before the second scramble remain
lossless under these ascending comparisons.

This is a computable fixed-region construction, not a data-dependent choice
of capture window. Restriction/scatter and depth adapters would still need
formalization. It addresses fringe only: it supplies no final bulk guarantee.

## Cost and the next substantive target

The construction saves fringe work compared with sorting all `m` rows, but
561 layers exceed both the 107-layer and 19-layer repair budgets. It is a
baseline for a stronger interface, not a complete upper-bound improvement.

The useful new target is an approximate fixed-window capture network:
within these two fixed windows, introduce at most the remaining relative
fringe allowance, on profiles satisfying **all** dyadic tail bounds. It must
also coexist with, or implement, the 65-cut bulk repair and preserve exact
small-rank capture. A sufficient success criterion is a physical network with
total final-operation depth within the appropriate 107/19-layer budget.

The all-scale tail property is a more meaningful input promise for this
problem than maximum height alone. Whether it is strong enough for that
network remains open. The smaller-fringe two-round estimate also remains
unclosed; neither route currently establishes a coefficient below 1000.
