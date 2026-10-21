# UB-28 local expander-halver lemma

2026-10-21. Paper-level derivation, independently checked in a fresh review;
the elementary numerical bounds are also checked by
[`ub28-halver-bounds.py`](ub28-halver-bounds.py). This closes a local primitive
gate only. It does not prove the multiscale UB-28 schedule sorts.

## Sharper local gate: 1/9 in 70 rounds for all `h >= 200`

Choose 70 independent uniform perfect matchings. With positive probability
their union has both properties below:

1. Every subset `A` on either side with `1 <= |A| <= h/10` has
   `|N(A)| >= 8 |A|`.
2. There is no edge-free rectangle `A x B` with both sides of size at least
   `h/10`.

For property 1, a violation for `|A|=a` is covered by a set `B` of size `8a`
containing `N(A)`. For fixed `A,B`, the probability that all 70 matchings map
`A` into `B` is at most `(8a/h)^(70a)`. The binomial union bound is

```text
exp(a * (9 + 62 ln(8) - 61 ln(h/a)))
  <= exp(-2.49 a),                 (a <= h/10).
```

Thus the two side-expansion failure probabilities sum to less than
`2/(exp(2.49)-1) < 1/5`.

For property 2, for fixed relative sizes `x=a/h`, `y=b/h`, the union-bound
exponent is
`F(x,y)=H(x)+H(y)+70 x ln(1-y)`. Both partial derivatives are negative for
`x,y >= 1/10`: use `ln(9)<3`, `ln(1-y) <= -1/10`, and
`70x/(1-y) >= 7`. Hence `F` is maximized at `(1/10,1/10)`. The exact-rational
checks give `H(1/10)<0.3251` and `ln(9/10)<=-0.105`, so `F < -0.084`.
For `h>=200`, `(h+1)^2 exp(-0.084h) < exp(-4.8) < 1/100`; this bounds the
rectangle failure probability. The total failure probability is therefore
less than `1/5+1/100 < 1`, proving existence.

For a binary input with `H<=h` ones, let `A` be the final left-block ones and
`B` the final right-block zeros. There is no edge from `A` to `B`, and
`|B|=h-H+|A| >= |A|`. Property 2 implies `|A|<h/10`; property 1 then gives
`H >= |A|+|N(A)| >= 9|A|`. The symmetric argument handles the upper tail, so
this is a `1/9`-halver. For `h<200`, use the `h` cyclic matchings of the
complete bipartite graph, which exactly split the two blocks. Consequently
the UB-28 two-offset schedule can use 70 rounds per pass at every scale
`h>=200`; all smaller scales contribute only a finite additive depth. For
`n=2^L`, the complete small scales `h=1,2,...,128` cost at most
`2(1+2+...+128)=510` layers, so the total local-gadget depth is at most
`140 max(L-8,0)+510 <= 140 L+510`. This leaves up to 160 coefficient points
for a global composition argument.

The rational checks for the sharpened constants are in
[`ub28-halver-bounds.py`](ub28-halver-bounds.py). This is a reviewed
paper-level local lemma, not a proof that the global schedule sorts.

To obtain the repository's permutation/rank definition, fix a permutation and
threshold its values to `Bool` (top `k` values mapped to `true`, or bottom
`k` mapped to `false`). A threshold map is monotone, so comparator-network
execution commutes with it by `ComparatorNetwork.exec_comp_monotone` in
`AKS.Sort.Monotone`. The binary bounds above therefore give the initial- and
final-segment rank bounds in `AKS.Halver.Defs.IsEpsilonHalver`.

## Earlier fallback claim: 1/11 in 99 rounds

For every `h >= 100`, there is a bipartite multigraph `G` on two `h`-wire
blocks which is the union of 99 perfect matchings and has both properties:

1. For every subset `A` on either side with `1 <= |A| <= 2h/25`, its
   neighbor set has size at least `10 |A|`.
2. There are no subsets `A,B` on opposite sides with no edge between them and
   both `|A|,|B| >= 2h/25`.

Apply the 99 matching layers as comparators, always sending the minimum to
the left block. For any binary input with `H <= h` ones total, let `A` be the
left-block ones after the layers and `B` the right-block zeros. Every left
wire's value can only decrease and every right wire's value can only increase.
Therefore no edge of `G` can join final `A` to final `B`. Also
`|B| = h - H + |A| >= |A|`. Property 2 forces `|A| < 2h/25`; property 1 then
gives

```text
H >= |A| + |N(A)| >= 11 |A|,
```

so at most `H/11` ones remain in the left block. By the symmetric properties,
when `H >= h`, at most `(2h-H)/11` zeros remain in the right block. These are
the two binary threshold conditions for a `1/11`-halver. The same threshold
argument gives the repository's permutation/rank formulation.

For `h <= 99`, use the `h` cyclic perfect matchings of `K_{h,h}` (depth `h`);
their union is complete, so the pair split is exact. Thus there is a family
of `1/11`-halvers of depth at most 99 for every `h`.

## Existence of the matching graph

Choose 99 independent uniform perfect matchings. For fixed `A` of size `a`
and `B` of size `10a`, the probability all neighbors of `A` lie in `B` is at
most `(10a/h)^(99a)`. The union bound over `A,B`, using
`binom(h,k) <= (e h/k)^k`, is at most

```text
exp(a * (11 + 89 ln(10) - 88 ln(h/a))) <= exp(-3.6a),
```

for `a <= 2h/25`; here `ln(5/4) >= 1/5` and `ln 10 < 3` suffice. Summing over
`a >= 1` gives less than `1/(e^3.6-1)` for failure of property 1 on one side;
the other side has the same bound.

For property 2, the probability of no edge between fixed `A,B` of relative
sizes `x=a/h`, `y=b/h` is at most `(1-y)^(99a)`. The union-bound exponent is

```text
F(x,y) = H(x) + H(y) + 99 x ln(1-y),
```

where `H` is binary entropy in natural-log units. For `x,y >= 2/25`, both
partial derivatives of `F` are negative: use
`ln((1-z)/z) <= ln(23/2) < 3`, `ln(1-y) <= -2/25`, and
`99x/(1-y) >= 99(2/25)`. Thus the maximum is at `x=y=2/25`. Elementary
logarithm bounds give `H(2/25) < 0.27888` and
`ln(23/25) <= -0.0832`, hence `F < -0.101`. There are at most `(h+1)^2`
size pairs, so this failure probability is at most
`(h+1)^2 exp(-0.101h) < exp(-0.3)` for `h >= 100` (the bound decreases with
`h`; use `ln 101 < 4.9`). The two expansion failures plus the rectangle
failure have total probability below
`2/(e^3.6-1) + exp(-0.3) < 1`; therefore a graph satisfying both properties
exists for every `h >= 100`.

For exact numerical certificates, `ub28-halver-bounds.py` uses rational
arithmetic. Its logarithm upper bounds follow from
`ln(q)=2 sum_{j>=0} z^(2j+1)/(2j+1)`, `z=(q-1)/(q+1)`, with the tail bounded by
`2 z^(2N+1)/((2N+1)(1-z^2))`; its exponential lower bounds use finite positive
Taylor sums. In particular it verifies `H(2/25)<0.27888`,
`ln(23/25)<=-0.0832`, `ln(23/2)<3`, `ln(101)<4.9`, and the combined
probability bound. These checks are exact rational comparisons, not floating
point sampling.

## What this does and does not buy

Using the 70-round halver in each matching pass gives the UB-28 two-offset
schedule an asymptotic local cost of `140 log2(n)` layers on powers of two.
The exact small-width cases contribute only an additive constant. The local
lemma does not show that this schedule sorts: later offset passes may disturb
earlier block boundaries, and a global invariant or a paired-witness count is
still required. Once a power-of-two sorter is proved, the existing
`AKS.Sort.Shrink.restrictWires_sorts` and `restrictWires_depth_le` lemmas give
the arbitrary-`n` version at no greater depth.

There is a reusable legacy bridge at
`upper-bound/alternatives/legacy/AKS/Separator/FromHalver.lean`, but its
current `halverToSeparator_props` charges separator error additively as
`t * epsilon`. The direct Seiferas bag parameter interface is incompatible
with `epsilon=t/9` (see `docs/sub300-search.md`); a different global assembly
theorem is necessary. No Lean work has started.
