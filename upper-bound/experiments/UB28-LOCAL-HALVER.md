# UB-28 local expander-halver lemma

2026-10-21. Paper-level derivation, independently checked in a fresh review;
the elementary numerical bounds are also checked by
[`ub28-halver-bounds.py`](ub28-halver-bounds.py). This closes a local primitive
gate only. It does not prove the multiscale UB-28 schedule sorts.

## Claim

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

Using one such halver in each matching pass gives the UB-28 two-offset
schedule at at most `198 log2(n)` layers on powers of two. The local lemma
does not show that this schedule sorts: later offset passes may disturb
earlier block boundaries, and a global invariant or a paired-witness count is
still required. Padding/arbitrary `n` also needs a proof in the project's
network model.

There is a reusable legacy bridge at
`upper-bound/alternatives/legacy/AKS/Separator/FromHalver.lean`, but its
current `halverToSeparator_props` charges separator error additively as
`t * epsilon`. With `epsilon=1/11`, that interface alone is not a sub-300
route for `t` growing with `log n`; a sharper global assembly theorem would
be necessary. No Lean work has started.
