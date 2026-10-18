# Central bulk feasibility: localized bands and a remaining cost gap

Informal research, 2026-10-10. This audits the
[disjoint bulk interface](disjoint-bulk-budget.md). It gives a concrete
631-layer bulk baseline, not the desired 107-layer construction. The
universal fringe theorem remains a separate open obligation.

## 1. What the current promises cannot justify

Take `m=2^43`, `i=m/2`, `v=m/4`, `w=2^24`, and
`alpha=w/(2*v)=2^-18`. For `n` a multiple of `2^18`, use `alpha*n` heights
`i+v`, `alpha*n` heights `i-v`, and the rest `i`.

The mean is exactly `i`, and the mean absolute deviation is `w`, below the
first-round allowance `e(m)*m`. The protected top and bottom windows are
perfect. Yet for any band half-width `W<=v/2`, the total high mass above
height `i+W` is

```
alpha*(v-W)*n >= (w/4)*n = 4194304*n.
```

The second scramble preserves this region total. A repair confined to that
band cannot remove it, and it greatly exceeds the actual bulk allowance
(about `74365*n`). Thus the existing L1 and protected-window promises do not
justify narrow-band repair. This is a counterexample in the enlarged retained
profile class, not a demonstrated state reachable after a chosen first
scramble. A stronger common first-scramble promise can exclude it.

## 2. A uniform localization promise

For any exact-rank input profile of mass `i*n`, let `z` be the heights after
the first scramble and intermediate sort. Consider

```
U = sum_c (z_c-i-W)_+,
D = sum_c (i-W-z_c)_+.
```

If `U>=A*n`, its overflow destination columns `S` receive at least
`(i+W)*|S|+A*n` marks. Their mean is `i*|S|`. The existing Poisson mgf bound,
with `lambda=ln(1+W/i)`, gives

```
P[bad for fixed profile and S] <= exp(-A*n*ln(1+W/i)).
```

Indeed the coefficient of `|S|` in the Markov exponent is
`W-(i+W)*ln(1+W/i)<=0`. Reflect and complement to bound `D`, using mean
`m-i`. Union over profiles and destination sets gives the safe rate

```
P[exists profile with U>=A*n or D>=A*n]
 <= 2*exp(n*[ln(2*(m+1))-A*ln(1+W/m)]).
```

Use

```
2^42 <= m <= 2^43,
W = 2^35-2^20,
A = m/2^30.
```

Then `A*ln(1+W/m)-ln(2*(m+1)) > 1.37` throughout the range. Endpoint
rational log evaluations give about `2.069` and `1.438`. For a conservative
whole-interval bound, use
`ln(1+x)>=x-x^2/2`, `W/m<=1/128`, and
`ln(2*(m+1))<=ln(2*(2^43+1))`; the resulting lower bound is above `1.375`.
At `n>=16`, union over the 63 interior cuts and both reflected orientations
has a very small failure probability. Combine it with the other first-stage
bad events by addition.

The bands of height `2*W` are disjoint in the nominal geometry: even at the
lower endpoint `2*W < b=(m-2*f)/64`, with `f=131040`. They lie strictly
between the protected windows. These statements still need checking for
every rounded scheduler template.

## 3. Sorting a band does not globally balance columns

This count distinction is essential. For a fixed column after the second
scramble, write `s_c` for its total mass, `D_c` for holes below the band, and
`U_c` for high marks above it. A full column-local band sort leaves

```
Q_c = U_c + (s_c-i+D_c-U_c)_+
    <= (s_c-i)_+ + D_c + U_c.
```

Consequently

```
Q_band <= Q_full_column_sort + D+U.
```

It is invalid to replace the full-column baseline by just the excess of the
total matrix mass: column-local sorting cannot transfer capacity between
columns. The outside-band allowances consume up to `2*A*n`; a second-round
bulk proof must explicitly reserve that amount.

## 4. A smaller entropy count funds that reserve

Let the first-round mean absolute deviation bound be `L`, so
`sum_c |z_c-i|<=L*n`. The number of admissible integer height profiles is
at most

```
exp(n*[1+ln(2*L+1)]),
```

which is much smaller than `(m+1)^n`. To prove this, put `x=L/(L+1)` and
sum `x^sum|z_c-i|` over all integer deviation vectors, extending their range
to all integers. The generating function is

```
((1+x)/(1-x))^n = (2*L+1)^n.
```

Each admissible vector contributes at least `x^(L*n)`, and
`L*ln(1+1/L)<=1` proves the claimed count. This overcounts the zero-sum
condition, which is harmless.

The [joint-tail argument](funnel-joint-tail.md) establishes the needed
cell-level mgf comparison informally: row bits are negatively associated,
so their exponential moment is bounded by the product of their Bernoulli
moments. Independent rows then multiply. For a centered Bernoulli variable,
every absolute moment of order at least two is at most its variance; the
same power-series bound as in the Bernstein derivation gives variance proxy
`V=sum_r p_r*(1-p_r)<=L` per column. The inequality for `V` follows from
`V=(1/(2*n^2))*sum_(c,d)|z_c-z_d|` and the triangle inequality about `i`.
These adapters remain to be formalized. For full-column excess at least
`beta*m*n`, Bernstein and the subset union give rate

```
I = beta^2*m / (2*(L/m+beta/3)),
entropy <= 1+ln(2*(2*L+1)).
```

Use the safe bounds

```
e(m)<=2^-18, L<=m/2^18,
paperOrdinaryEpsB > 1/60000000,
beta = 1/120000000 - 1/2^29.
```

The second inequality for the bulk constant follows from its explicit square
and a rational lower bound on `ln 2`; it must be formalized rather than
substituting a weaker upper tolerance. The first bound follows at `2^42`
and is decreasing thereafter. Throughout the height range,

```
I >= 24.12266,
entropy <= 19.71498,
margin > 4.40.
```

These comparisons were evaluated with rational arithmetic and rational log
intervals. Finite union over the required cuts and orientations then leaves
ample probability mass for a common second witness, as far as bulk alone is
concerned. Combining this witness with fringe still requires its universal
failure bound.

By construction `beta*m+2*A = m/120000000`, strictly below the actual bulk
allowance per column. Thus the baseline can fund the outside-band reserve.

## 5. A concrete bulk baseline, and its price

Sort the two halves of each band columnwise, both in ascending order, then
compare mirror pairs across the cut in one layer. For a Boolean threshold,
the sorted halves have suffixes of `k_1,k_2` high bits. The top half after
the mirror layer contains exactly `(k_1+k_2-W)_+` high bits: it intersects
one suffix with the reflected other suffix. Thus it has the same cut count
as a full band sort, without needing the whole band sorted afterwards.

Each half has fewer than `2^35` rows. The depth bound is

```
35*36/2 + 1 = 631.
```

All bands run in parallel, and also in parallel with the fringe funnels.
Ascending comparisons retain every completed threshold count guarantee.
This provides a complete informal bulk count route under the explicit
probability adapters above. It costs far more than 107 layers.

With the two initial sorts, its conditional ordinary-stage depth is `2523`,
giving coefficient `1261.5` under the retained scheduler. **This is not a new
sorting theorem:** fringe universality, geometry, fallback, and formal
probability adapters remain open. It is a repair baseline against which to
compare cheaper constructions.

## 6. Preserving long runs has a real tradeoff

One tempting shortcut is to make the second scramble constant on blocks of
length `B`, retaining sorted runs. On the retained profile class, take half
the heights `i+w` and half `i-w`, with `w=2^24`, and align the dirty interval
with `2*w/B` whole blocks. Independent block permutations give each column

```
s_c-i = B*(Binomial(2*w/B,1/2)-w/B).
```

For `B=2^21`, the runs permit a 94-layer merge of a `2^25`-row dirty band,
but even the ideal full-column excess has expectation exactly

```
B*q*binom(2*q,q)/(2*4^q) = 1647360,
q=w/B=8,
```

per column, versus a bulk allowance about `74365`. This invalidates carrying
over the independent-row variance calculation to these block scrambles.
It is not a proof that every correlated block-permutation design fails or
that the profile is reachable under every first witness.

## Research decision

The 107-layer construction remains open. The next candidate must either
exploit the actual row-scrambled law inside the wide bands, or provide a
stronger common first-round localization promise with affordable reserve.
Uniform tiny-error halvers on these entire bands and assumed long runs do
not currently provide the needed certificate.

The restricted-profile entropy lemma is useful independently: it should be
carried into future mixing estimates instead of repeatedly paying `ln m`.
No Lean files, tests, or builds were changed or run.

## 7. Rebalanced protected-window reserve

The earlier `2048*n` protected-window allowance does not quite compose with
the `beta*m+2*A=m/120000000` band-error bound after reserving the windows:
using the actual `paperOrdinaryEpsB`, the remaining per-column budget
`E_B-2048` minus that band bound is about `-1516` at `m=2^42` and `-984` at
`m=2^43`. This is a small constant mismatch, but the 631-layer baseline must
not be called budget-compatible with that reserve as written.

The protected-window estimate can be retuned using the actual interior-cut
distance instead of the coarse `m/65` bound. For `i_k=f+k*b`,
`m=2*f+64*b`, and `1<=k<=63`,

```
min(i_k,m-i_k) >= m/64.
```

The existing Bernstein exponent therefore gives, for a protected-window
allowance `A_w*n`, the profile-union margin

```
9*m*A_w/(32*64^2*T) - ln(2*(m+1)),    T=2^33.
```

Choose `A_w=896`. At `m=2^42` this margin is about `1.695`; it increases with
`m`. Including 63 cuts, two orientations, and the two window regions gives a
union bound below `4.3e-10` at `n=16` from this numerical margin. The first and
last interior cuts are the bottleneck; at `k=2` the margin is already about
`96.2`, and it grows toward the middle.

To preserve a little count slack while funding the band repair, set

```
beta = 1/120000000 - 1/2^29 - 1024/2^42.
```

Using only the proved lower estimate `paperOrdinaryEpsB/2 > 1/120000000`, for
every `2^42<=m<=2^43` we then have

```
beta*m + 2*(m/2^30) + A_w
  <= m/120000000 - 1024*m/2^42 + 896
  <= m/120000000 - 128
  < E_B.
```

With `L=m/2^18`, the second-round profile-tail exponent margin from Section 4
is about `3.397` at the lower endpoint and increases with `m`; a 252-event
union bound at `n=16` is about `6.4e-22`. The script
[central_slack_envelope.py](central_slack_envelope.py) checks the exact cut
formula over a 1,025-point height grid and reports the endpoint values.

This reallocation appears to close the numeric reserve gap for the informal
631-layer band construction, under the same probability adapters and nominal
geometry. It does not construct the desired 107-layer network, prove those
adapters, settle rounded scheduler templates, or improve the checked bound.
The scalar `0.0022` stress threshold from the separate two-height profile is
not the operative target for this reachable localized-band class.
