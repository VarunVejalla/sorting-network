# UB-25 local merge-and-deal screen

Claim level: `hand-proof` for the Boolean count identity conditional on the
existing bitonic-merge theorem; `simulation` for the independent finite check.
No whole sorting-network improvement is claimed.

Let both packets have length `m=2^q` and be sorted in nondecreasing order.
For a Boolean threshold, write their zero counts as `x` and `y`. Their
concatenation with the second packet reversed has the form

```text
0^x 1^(m-x) 1^(m-y) 0^y.
```

Its true entries form one interval, so it satisfies `Bitonic.Window`. The
existing `Bitonic.bitonicMerge_sorts` theorem therefore says that applying
`Bitonic.bitonicMerge (q+1)` produces a nondecreasing Boolean vector. The
network preserves the multiset because every comparator only exchanges its
two inputs. The output consequently has exactly `x+y` zeros, in the prefix
`[0,x+y)`. Assigning even output indices to packet A and odd indices to
packet B gives two nondecreasing subsequences. Among the first `x+y` indices,
there are `ceil((x+y)/2)` even indices and `floor((x+y)/2)` odd indices, so
the packet counts are exactly

```text
(ceil((x+y)/2), floor((x+y)/2)).
```

The comparator depth is at most `q+1`, by
`Bitonic.bitonicMerge_depth_le`. Reversal of the second input is a fixed
interpretation of its packet wires. Dealing is also an output wire-label
convention: the two sorted packets occupy the even and odd output positions.
Neither operation is data-dependent routing. The existing
`Untangle.untangle` theorem realizes a generalized network as an ordinary
comparator network at the same greedy depth when the composed network has a
specified sorted output order. It may support carrying these labels through
the full algorithm, but the required packet-label composition and final
ordering map still need an implementation and proof.

The independent script `merge_deal_check.py --max-q 7` checked 22,363 pairs
of sorted Boolean packets, covering every pair of zero counts for packet
lengths through 128. It mirrors the recursive half-cleaner definition, so
this is a model check, not a Lean proof of the adapter.

## What this does not resolve

The local primitive is not the main risk. A fixed matching schedule must
balance an unbounded number of packet counts; a useful proof needs both a
bulk estimate and a rare-cohort tail. L2 contraction alone gives an
aggregate deviation screen, not a multiplicative bound for small cohorts.
The global AKS flow must also split sorted packets into fragments at ports,
keep those fragments sorted, and charge all re-merging and frontier repair.
No matching family, tail theorem, or complete scheduler is currently known
to fit the UB-25 depth budget.
