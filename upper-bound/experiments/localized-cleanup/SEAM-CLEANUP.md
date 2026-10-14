# Sort chunks once, then merge their seams

Claim level: `hand-proof` for the Boolean cleanup lemma and asymptotic depth
gate; `simulation` for the finite check. The odd-even merge network and the
full recurrence have not been formalized in Lean.

## Cleanup construction

Assume a fixed prefix of depth

```text
P(n) <= p log2(n) + O(1)
```

which maps every Boolean input to zeros, then a dirty interval of length at
most `s(n)`, then ones. Choose a power of two `B >= s(n)` with `B < 2s(n)`
(rounding the degenerate `s=0` case up to `B=1`). For sufficiently large n,
`B=o(n)`. Partition the wires into chunks of length `2B`; if there is a
short remainder, combine it with the previous full chunk. Thus every chunk
has length in `[2B,4B)` and the final one may be longer than `2B`.

1. Recursively sort every chunk in parallel. The maximum recursive size is
   less than `4B`.
2. For every boundary between neighboring chunks, merge the last `B` wires
   of the left chunk with the first `B` wires of the right chunk. These seam
   windows are disjoint: each chunk contributes its prefix half to its left
   seam and its suffix half to its right seam. Use Batcher's odd-even merge
   network on two sorted runs of length `B`; its depth is `log2(2B)` and it
   compares the physical wires directly, with no reversal or wire routing.

For a Boolean input, the prefix guarantee gives a single transition region
of width at most `B`. It meets at most two chunks. After step 1 every chunk is
sorted. If the dirty region is contained in one chunk, all other chunks are
constant false or true; seam merges with those constant runs preserve the
order at the chunk's two ends. If it crosses a chunk boundary, its left part
lies in that chunk's suffix half and its right part in the next chunk's
prefix half. That one seam merge sorts the only possible inversion; adjacent
seams touch pure halves. The final Boolean output is monotone. By the
zero-one principle, the resulting comparator network sorts arbitrary values.

## Depth consequence

Let `F(n)` be the depth of this recursive sorter family. The full cleanup
recurrence is

```text
F(n) <= P(n) + max_(k < 4B(n)) F(k) + log2(2B(n)) + O(1).
```

For `s(n) <= c*n^theta`, `0 < theta < 1`, we have
`log2 B(n) = theta*log2(n) + O(1)`. If
`limsup F(n)/log2(n) <= C`, then

```text
C <= p + theta*C + theta,
C <= (p+theta)/(1-theta).
```

So the sufficient gate for a coefficient below 200 is

```text
p + theta < 200*(1-theta),
p < 200 - 201*theta.
```

At `theta=1/4`, the prefix budget is `p<149.75`; at `theta=1/10`, it is
`p<179.9`. This is dramatically less restrictive than sorting both
overlapping window passes recursively, which had required `p<100` at
`theta=1/4`. It is close to the stronger rank-pure-block budget `p<150`.

For arbitrary n, take an exact finite base range large enough that outside it
`n >= 4B(n)`, so every recursive chunk is strictly smaller. The combined
remainder chunk handles the one irregular end without padding sentinels. Its
size stays below `4B`; all seam windows still have exactly `B` wires on each
side. The limsup argument absorbs fixed factors, the finite base range, and
integer rounding into `O(1)` terms.

## Executable screen and remaining proof obligations

`seam_cleanup_check.py` mirrors the fixed odd-even merge comparator network
and the chunk/seam layout. It exhaustively checked 139,506 s-sorted Boolean
inputs through `n=16`, and all pairs of sorted Boolean runs through run size
16. This is only finite model evidence.

The next formal work is (i) define and prove the odd-even merge network sorts
two sorted equal-length runs in `q+1` layers, (ii) prove the s-sorted
chunk/seam cleanup lemma including the irregular final chunk, and (iii) prove
the all-n recurrence/limsup bound in Lean. None of these supplies the missing
preprocessor. The crucial open construction remains a fixed binary prefix
with `s(n)=O(n^theta)` and coefficient `p<200-201*theta`, with its positional
guarantee for every Boolean input and all its own routing charged.
