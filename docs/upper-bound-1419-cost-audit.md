# Cost audit of the 1419 upper bound

Research audit, 2026-10-10. The checked endpoint is
`limsup D(n)/log_2 n <= 1419`, formalized without hypotheses in
[`upper-bound/best`](../upper-bound/best/README.md). This note separates its
dominant repeated cost from additive terms and screens two possible next steps.

## Where 1419 comes from

For `N=64^d`, the formal depth budget is

```text
totalDepth(d) = 6320 + (3d - 21) * 2838 + 903
              = 8514*d - 52375.
```

Since `log_2(64^d)=6d`, the repeated ordinary-node term gives
`3*2838/6 = 1419`. The root's 6320 layers and final sorter's 903 layers are
additive constants; reducing either does not change the limsup coefficient.
The depth bottleneck is therefore the **2838-layer ordinary node**, repeated
three times per factor-64 scale.

`pack2_depth_le` gives ordinary two-round pack depth at most
`3*k*(k+1)/2` when the matrix height `m <= 2^k`. The current node geometry is
`2^42 < m <= 2^43`, so `k=43` and the bound is exactly 2838. The final blocks
remain size `2^42`; they contribute only the additive 903-layer final sort.

## Nearest local candidate: the two-tail bulk variant

The best immediate target in the current proof notes is Variant B of
[`BULK2.md`](../upper-bound/best/notes/two-round/BULK2.md). Its hand proof and
certified numerical checks indicate the bulk contraction at `m >= 2^41`,
using exact-mass, two-tailed estimates in both rounds. The listed parameters
are `E1=366/10^8`, `lambda=1/216`, and `d=1/59,000,000`; the margins are
positive. This variant is **not yet Lean-formalized**.

If the ordinary node window can be changed to `2^41 < m <= 2^42`, the same
pack-depth theorem uses `k=42`:

```text
ordinary node depth <= 3*42*43/2 = 2709
projected limsup coefficient = 3*2709/6 = 1354.5.
```

That is a 64.5-point (about 4.55%) reduction. This projection is plausible
because the existing two-round fringe argument has a much smaller minimum
scale (`f >= 131040`) than either row window. The current formal theorem still
requires `m >= 2^42`, however, and the current geometry proof uses the old
window. Variant B and the smaller window therefore need a full proof audit
before this can be called a candidate theorem.

The concrete obligations are:

1. Formalize the exact-mass, two-tailed round-1 failure bound at `m >= 2^41`
   and combine it with the existing exact-mass round-2 bound, preserving the
   failure budget shared with the fringe predicates and both orientations.
2. Lower the `m` threshold in the joint bulk/fringe existence theorem. The
   current `F2Exists` proof uses the one-tailed `m >= 2^42` round-1 estimate;
   its small-rank and large-rank fringe events need to remain compatible with
   the new exact-mass first-round predicate.
3. Adapt `NodeGeom` and `GeometryScale` to `2^41 < m <= 2^42`. Check each
   template's scaled fringe size remains either zero or even and at least
   131040; the old generic ratio lemma only directly certifies the old lower
   endpoint, so template-specific arithmetic may be needed.
4. Change the ordinary node pack budget from `k=43` to `k=42` and propagate
   the 2709-layer bound through the scheduler and total-depth arithmetic.
   Root and final-sorter costs need not improve for the limsup result.

## Why the AKS multiway core is not yet the next coefficient improvement

The local interval screen in
[`ajtai1992-multiway-halvers.md`](ajtai1992-multiway-halvers.md) gives
two-round all-cuts cores at `(k,p,N,E)=(256,16,256,.55)` and
`(1024,32,1024,.45)`, with numerical total failure bounds below one. Their
Batcher binary depths are 72 and 110. If they could serve as ordinary stages
in the existing three-stages-per-factor-64 schedule, their local depth charges
would correspond to coefficients 36 and 55. Those are raw-stage comparisons,
not end-to-end bounds: the AKS core does not satisfy the current `NodeSpec`.

The current ordinary bulk tolerance is `1/59,000,000`, and its fringe clause
requires rank-relative leakage below `1/86,000,000` for the supported fringe
ranks. AKS's all-cuts leakage fractions `.45` and `.55` are tens of millions
of times larger than the bulk tolerance, and the core supplies no matching
rank-sensitive fringe guarantee. Its paper also leaves the p-way combining
step unspecified. There is therefore no valid scheduler substitution or
end-to-end coefficient to compare against 1419 yet.

## Priority

Formalize and integrate Variant B first. It targets a verified reduction to
1354.5 using the existing Chvatal scheduler and has a concrete finite
parameter set. Keep the AKS lead as a separate construction search; resume it
for coefficient improvement only after specifying its combiner and a global
error-recovery invariant that meets the actual node interface.
