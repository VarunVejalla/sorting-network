# Final-round repair: findings and a smaller next target

Informal investigation, 2026-10-10. No new comparator construction or Lean
theorem is established. See the [exact contract](repair-contract.md) and
[candidate audit](repair-candidates.md).

**Follow-up:** [lossless fringe capture](lossless-fringe.md) corrects the
arbitrary-compaction interpretation below for the existing small-rank premise:
those marks are already in fringe rows before the second scramble. It also
derives a deterministic cyclic small-rank capture construction; joint bulk
compatibility remains unproved.

## The useful reduction

For a column-local repair, let `s_c` be a column's number of high-threshold
marks, and let `h_c` be its marks in the bottom `i` outputs. Then

```
actual escape = sum_c (s_c - h_c)
full-sort escape = sum_c max(s_c - i, 0)
repair defect = sum_c (min(s_c, i) - h_c) >= 0.
```

This is an identity: full column sorting packs as many marked keys as possible
into each destination suffix. A weaker repair needs only to control the defect
at the 65 specified bulk cuts and the fringe cut for every supported rank;
it need not sort its outputs. The low orientation uses the corresponding
prefix counts on the original ordered keys.

The available bulk allowance is `floor(EB)-full-sort escape`. The fringe
allowance is `ceil(epsF*j)-1-full-sort escape`. For `j<=86000000` the latter
is zero. Thus an approximate bulk partitioner alone will not close the proof:
lossless small-rank capture is a separate obligation.

## A modular composition lemma

There is a simple reason to separate rare-rank capture from bulk repair.
Every comparator in the current network model has wire indices `i<j` and
places the smaller key at `i`. For any fixed rank threshold and any prefix:

- the count of high keys in the prefix cannot increase;
- the count of low keys outside the prefix cannot increase.

Proof: comparators with both endpoints on one side preserve that count. Across
the boundary, an exchanged high/low pair moves the high key right and the low
key left; every other comparison preserves the count. Induction gives the
statement for an entire comparator network.

Consequently an exact fringe-capture network followed by an ascending bulk
repair preserves the established fringe guarantee. The reverse order also
preserves an established bulk guarantee. This gives a sufficient modular
construction, with **summed** depths `d_F+d_B`; it does not justify parallel
execution on overlapping wires. Any intermediate wire permutation must itself
preserve the relevant prefix regions, or be included in a separate proof.

This permits the first construction question to be smaller:

> After the fixed second scramble, build one column-local network that sends
> every small-rank marked key into the correct fringe, in both orientations.
> State the reachable-state promise precisely and prove its depth. Then give
> a bulk-repair theorem on the state after that capture network.

The second clause matters: a bulk repair proved only on the original scrambled
states does not automatically apply after fringe capture. Alternatively, prove
bulk repair first and establish fringe capture on its outputs. Monotonicity
preserves a completed guarantee; it does not transfer an unproved network's
input promise.

If the only small-rank promise is `s_c<=f`, the high-side task is lossless
compaction of an arbitrary supported column state into its bottom `f` wires.
Both sides must be handled by the same network. Stronger promises can help,
but must actually follow from the common scramble witnesses.

## Error reserve also has a cost

The previous Bernstein calculation assumes a full final column sort. To pay
for a repair defect, it must deliver a smaller bulk error first. With

```
d = paperOrdinaryEpsB
  = sqrt(2*(1+58*ln 2)/2^58),
e(m) = sqrt(2*(1+ln m)/m),
I(m,d') = (d')^2*m / (8*e(m) + 4*d'/3),
required margin = ln(2*(m+1)) + ln(200*m)/16,
```

the following floating-point evaluations are exploratory, not certificates:

| Exact height | Fraction of bulk allowance used upstream | `I` | Required margin |
| --- | ---: | ---: | ---: |
| `2^42` | 1 | 42.4421 | 31.9560 |
| `2^42` | 3/4 | 23.8782 | 31.9560 |
| `2^43` | 3/4 | 66.7585 | 32.6925 |
| `2^43` | 1/2 | 29.6784 | 32.6925 |

So the current sufficient bulk calculation at exactly `2^42` does not fund a
quarter of the allowance for repair. Raising the minimum height makes reserve
easier but increases the sort budget. A height ceiling of `2^43` leaves only
107 repair layers; a ceiling of `2^44` leaves only 19. Bounds must hold over
the entire template height interval, not merely at its upper endpoint.

The rare-rank zero-escape obligation is unaffected by this bulk reserve.
Sharper bulk tails cannot buy permission for a small-rank fringe escape.

## Decision

We have a precise interface and a modular composition argument, but no repair
meeting the 193/107-layer budget. Current partial-bitonic and run-reuse ideas
do not supply one. The most informative next construction attempt is lossless
two-sided fringe capture on the actual reachable state family, paired from
the start with a charged bulk repair and its post-capture input promise.

Keep two outcomes distinct: a successful count interface is progress toward
modularity; an improved sorting bound requires a physical network, joint
bulk/fringe witnesses, template scaling, and a fitting small-node fallback.
