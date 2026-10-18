# Multi-bag pooling audit

Status: first-pass requirements-versus-cost analysis, October 12. This is a
research calculation, not a Lean theorem or a construction.

## Candidate pooling idea

The local pack provider needs at least `2^38` live wires. At the low end of the
ordinary schedule, one bag has about `C=2^34` wires. The smallest plausible
pool is therefore 16 adjacent bags. Run one `2^38`-wire pack on their union,
then assign the output intervals back to the 16 original bags. This could
preserve the per-stage depth (one depth-1890 pack per pool), but it changes
both the separator error and the routing interface.

## Error tax

For a pooled size `N ≈ q C`, the existing arbitrary-cut theorem gives
crossing error at most

```
(epsB / 2) * N + columns
  ≈ q * ((epsB / 2) * C) + columns.
```

Thus the per-bag error budget grows by `q`. To retain the current local
charge for `q=16`, the pooled pack needs `epsB_pool <= epsB/16 = 2^-25`.
The current ordinary scalar screen's exact positive margin is only
`4441485454561/174859758926424965120 ≈ 2.54e-8`; the extra unadjusted
`15*epsB ≈ 7.15e-6` would exceed it by about 282 times. Pooling at the present
`epsB=2^-21` therefore fails the existing screen decisively.

## Existing rate model also blocks the needed error reduction

Let `delta` be the target B2 error and `E` the first-round error. The current
two-round inequalities require

```
L := log(2(m+1)) + 1/2 <= m E^2
L <= m * (lambda*delta/2
          - lambda^2*(1/2 + 2*lambda/9)*E/2).
```

Since `1/2 + 2*lambda/9 >= 1/2`, the second-round rate is at most
`lambda*delta/2 - lambda^2*E/4 <= delta^2/(4E)`, after optimizing the
quadratic over `lambda`. Combining with the first-round lower bound on `E`
gives

```
m * second_round_rate <= m^(3/2) * delta^2 / (4*sqrt(L)).
```

At the required `m=2^34` and pooled target `delta=2^-25`, this upper bound is
about `0.10`, while `L` is about `24.76`. So merely retuning `E` and `lambda`
cannot make the existing probabilistic certificate 16 times sharper at the
same rectangle size.

## Routing and fringe obligations left by pooling

Even with a sharper pack, the proof would need to:

1. define pools as unions of live registers with an explicit injective wire
   map into the pack network;
2. prove disjoint coverage and exact output repartition into the 16 child
   slots, including ragged/unequal bag sizes;
3. derive all internal slot-boundary crossing bounds from the pooled B2
   theorem;
4. derive each slot's higher-order rare-rank send bound. A pooled outer-tail
   F2 estimate alone does not automatically give the required estimate at
   every internal slot boundary;
5. re-run the ordinary order-zero scalar screen with the resulting error.

The depth looks acceptable in isolation; the B2 accuracy requirement is the
first quantitative blocker, followed by the unproved per-slot fringe
transfer. Pooling remains a possible construction change only if both are
improved together.

## Recommendation

Do not implement the 16-bag pool yet. The direct one-bag path needs a new
local certificate at about `2^34` wires. The pooled path needs a `2^-25` B2
certificate plus a new internal-slot F2 transfer. The former is the smaller
mathematical target; first investigate whether the two-round analysis can be
replaced by a better uniform concentration argument at fixed B2 error, or
whether another explicit small-register separator is available.
