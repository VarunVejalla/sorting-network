# Weighted swap charging: an exact identity and a concrete obstruction

## Formal foundation

`Kahale.rankFiberSize_append_comparator` states that, for a strictly ordered
output `w`, appending a comparator merges exactly the two prefix fibers at
`w` and its swapped partner. Their cardinalities add because the fibers are
disjoint. This applies to every prefix, without assuming uniform prefix outputs.

This is a counting theorem. The entropy formula and structural conjectures
below are not yet Lean theorems.

The focused build of `AKS.Kahale.RankFiberMerge` and its separate axiom audit
succeeded. The theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. Reproduce with
`lake build AKS.Kahale.RankFiberMerge AKS.Kahale.RankFiberMergeAxioms`.

## Sorted-block calculation

Sort two disjoint blocks of size `k` independently, under uniform random input
rank permutations. The resulting states are the `binom(2k,k)` interleavings,
each with the same input-fiber weight `(k!)^2`.

For a **single** comparison of the two `r`th order statistics, both predecessors
are possible precisely when those values are global ranks `2r-1,2r`. To swap
them while keeping both blocks ordered, no value from either block can lie
strictly between them. Their common number of predecessors is therefore

```text
gain(k,r) = 2*binom(2r-2,r-1)*binom(2k-2r,k-r)/binom(2k,k).
```

All ambiguous fibers have equal weights, so this probability is exactly the
entropy loss in bits. For `r=1` it is `k/(2k-1)`, approaching one half.

### Parallel comparisons introduce collective ambiguity

Comparing all `k` corresponding positions at once does **not** give the sum
of those single-gate gains computed at the initial prefix. Swaps at several
positions can jointly preserve the block order even when one swap alone
cannot. Two blocks of size two already give `5/3` bits for the layer versus
`4/3` for the sum of initial single-gate losses.

There is an exact combinatorial description. Encode an interleaving by a
balanced walk: an `A` rank contributes `+1`, a `B` rank contributes `-1`.
Let `e` count returns to zero after times `2,4,...,2k`, including the final
return. Each excursion permits an independent exchange of the two block
labels without changing the layer output; inside an excursion, the labels
are forced once the first label is chosen. Thus its layer-output fiber has
size `2^e` among interleavings.

In particular, the single-swap graph of the initial reachable image need not
connect all states in one whole-layer fiber. A multiple-position swap can be
valid even though its intermediate single-swap states are unreachable.
Use the fibers of the whole layer, or a relation allowing simultaneous swaps,
when defining the structural bank.

To see why these are exactly the choices, write the output as unordered pairs
of corresponding block entries. Successive pairs whose intervals overlap
must retain consistent orientations to keep both predecessor blocks sorted.
A break between pairs occurs exactly when all earlier entries precede all
later entries, equivalently at a return of the balanced walk to zero.

Consequently the layer entropy loss is

```text
E[e] = sum_{r=1}^k binom(2r,r)*binom(2k-2r,k-r)/binom(2k,k)
     = 4^k/binom(2k,k) - 1.
```

The convolution identity follows by multiplying the generating series
`sum binom(2r,r)*x^r = (1-4x)^(-1/2)` by itself. Stirling's formula gives
`E[e] = sqrt(pi*k)*(1+O(1/k))-1`. This family therefore has many comparison
slots but only order `sqrt(k)` bits of layer information. The calculation is
a derived argument, not a universal sorting-network theorem.

[Exact finite counts](kahale-sorted-block-fibers.json) enumerate every
interleaving through `k=8`, including the entire layer's fiber histogram.
Entropy values are numerical; the combinatorial counts are exact.

## A falsifiable universal conjecture

For a depth-`d` sorting network, fix an order within each parallel layer.
Let `M=d*floor(n/2)`, `G` be its actual gate count, and `h_g` its entropy loss
under uniform input permutations. Ask whether an absolute constant `C` exists
such that

```text
(M-G) + sum_g (1-h_g) >= rho*M - C*n
```

for **every** such network. First investigate `rho=2/5`, which would give
coefficient `10/3`; the stronger target `rho=1/2` would give coefficient `4`.
Both remain conjectures. The current theorem only implies a saving fraction
approaching `0.388483827...`, with a subleading error, not either conjecture.

A useful potential proof would construct a bank from weighted reachable rank
states, prove a per-layer bound

```text
layer_entropy_loss <= (1-rho)*floor(n/2) + B_t - B_(t+1),
```

and independently establish `B_0-B_d <= C*n`. This is a sufficient proof
template, not a construction of the missing bank. Unused slots are included
in the layer capacity. The bank must handle collective swap components and
their weights, rather than summing only single-swap ambiguities.

## Next mathematical obligations

1. Prove the sorted-block excursion/fiber correspondence combinatorially.
   It supplies a precise model for collective ambiguity.
2. Define the corresponding weighted ambiguity components for arbitrary
   reachable rank images. Determine what structure replaces ordered blocks.
3. Propose a bank with a quantitative local transition inequality. Check
   whether overlapping components can spend the same earlier slack repeatedly.
4. Prove endpoint control separately. A cost of order `n*log n` would invalidate
   the claimed coefficient even if the local inequality holds.

The sorted-block formula exhibits useful slack, but supplies no rule assigning
that slack to future gates of an arbitrary sorting network. That assignment,
including a bound on repeated use, remains the main open problem.

Reproduce the finite calculation with:

```text
python -B scripts/kahale_sorted_block_fibers.py --output docs/kahale-sorted-block-fibers.json
```
