# Structural route toward a sub-200 binary coefficient

**Status: parked.** The active high-upside route is now `../direct-multiway/RESEARCH-SEQUENCE.md`. This document preserves the earlier row-scramble route and its diagnostics.

Status: research plan, 2026-10-10. No new sorting bound is claimed.

## Target and architecture choices

The checked baseline is `limsup D(n)/log2(n) <= 1419`. In its current
factor-64 scheduler, each scale increase runs three node operations in
parallel across the bags; each node costs 2838 layers. Thus the coefficient is
`3 * 2838 / 6 = 1419`. Replacing only the node primitive while keeping that
scheduler requires node depth below 400 for a coefficient below 200 (below
600 for a coefficient below 300). This is the strict first budget gate.

A different recursive architecture can amortize a partition primitive over
more than six bits of scale. If a primitive of depth `T` contracts each
subproblem by a factor `p` and its error-recovery/glue costs `G` per level, the
first-order coefficient is `(T+G)/log2(p)`. This is a separate accounting
model: it is valid only after proving that approximate bins can be repaired
and recursively sorted with that contraction. The 1992 paper's multiway
remark does not supply that proof.

## What the finite evidence says

The local AKS two-round construction has a numerically certified all-cuts
existence result at `(k,p,N,E)=(1024,32,1024,0.45)`: two k-sorter layers
simulate to 110 Batcher binary layers, and one fixed row-permutation vector
works for all 31 cuts and all monotone 0-1 inputs under the stated counting
lemmas. The bound permits as much as 45% of the minority mass to leak at a
cut. At `(256,16,256,0.55)`, the corresponding cost is 72 layers and leakage
is 55%. These are real local certificates at the numerical/research-note
level, but neither contract is remotely a complete global sorting interface.

A bounded rerun of the existing outward-rounded dense-rate search confirms
how narrow the current certificate is: `E=0.45` closes in 258 boxes with a
total failure bound below `10^-10`; at `E=0.44`, a 10,000-box budget does not
close (its remaining interval upper bound is still enormous). This is only a
limitation of the current union bound and interval subdivision, not evidence
that `E=0.44` is impossible. It does show that simply asking the existing
screen for a noticeably sharper local constant is not presently a quick win.

Therefore do not spend effort merely shaving the 110-layer core. The missing
combiner/global invariant must turn this coarse partition into recursive
contraction, or a stronger local theorem must reduce the error substantially.
The current Chvatal node contract is rank-sensitive and two-sided; the coarse
relative all-cuts bound above does not imply it.

| `(k,p,N)` | Binary core `T` | certified `E` | combiner/recovery `G` | contraction proved? | depth-only `T/log2(p)` |
|---|---:|---:|---:|---|---:|
| `(256,16,256)` | 72 | 0.55 | unknown | no | 18 |
| `(1024,32,1024)` | 110 | 0.45 | unknown | no | 22 |

The last column is only an optimistic arithmetic reference, **not** a sorting
coefficient: it charges neither `G` nor the cost of repairing errors, and no
recurrence currently justifies dividing by `log2(p)`. Conversely, the 400-layer
gate applies to replacing a node in the existing factor-64 scheduler, not to
this unproved recursive architecture.

## Why the present leakage contract does not compose by local cleanup

At the middle rank `q=n/2`, the all-cuts contract gives only
`L_j(q) <= E*n/2` misplaced high keys above boundary `j`; the same number of
low keys can be on the wrong side. For `(p,E)=(32,.45)`, this permits `0.225n`
of each type at a boundary, or 7.2 bin-widths per type. For `(16,.55)`, it
permits 4.4 bin-widths per type. In an optimistic model where those errors
already sit next to the boundary, the repair window is about `E*n` wires;
windows spaced `n/p` apart then overlap heavily whenever `E > 1/p` (true for
both candidates). Sorting all overlapping windows reduces to a global cleanup,
whose ordinary exact-sort depth is quadratic in `log n` with Batcher networks.

This is not an impossibility theorem for the core: the leakage statement is
only a count bound, and the actual fixed network may have much more structure.
But the count bound alone does not even imply adjacent-bin closure. Here is an
explicit abstract output profile showing this. Start from `p` sorted bins of
size `s=n/p`, and swap the entire contents of bin `a=p/4` with bin `b=3p/4`
(take `p` divisible by four). Every output bin remains internally sorted. At
each cut between these bins, the excess number of top-`q` keys is at most `s`;
all other cuts have zero excess. This excess can be nonzero only for
`n/4-s < q < 3n/4`, where
`min(q,n-q) >= n/4-s`. Thus the all-cuts count contract holds whenever
`E >= 4/(p-4)`. Both screened candidates satisfy this: `0.45 > 1/7` for
`p=32`, and `0.55 > 1/3` for `p=16`. Yet there are inversions between bins
separated by about `p/2` blocks. So the certified count bounds alone permit
nonadjacent-bin errors; they cannot justify repairing only adjacent boundary
windows. This is a contract-level counterexample, not a claim that the AKS
network actually outputs this profile.

More generally, the count bound does not locate the misplaced keys near the
boundary or show that one boundary's repair leaves neighboring bins' promises
intact. Therefore no valid `T + D(E*n)` recurrence follows from the certified
`E` values.

A composable primitive needs an additional **localized crossing** clause. For
each boundary and threshold, it should bound not only the number of wrong-side
keys, but certify that the wrong high keys lie within a specified suffix band
and wrong low keys within a prefix band. With band width `w`, disjoint
one-pass repairs require `2w < n/p`; then exact sorting of the two-sided
boundary bands repairs all cross-bin inversions only if a further invariant
proves there are no nonadjacent-bin inversions. This last implication must be
proved, not assumed. The next proof target is therefore either (i) derive this
localized crossing and closure property from the AKS row-scramble construction,
or (ii) exhibit an admissible output profile showing it cannot be derived from
the all-cuts count contract alone.

For the actual two-round AKS matrix, the right local statistic is available.
At row cut `h`, let `X_c` be the number of ones in output column `c` before
reading the matrix row-major, after the final column sort, and set
`d_c(h) = max(0, X_c-(k-h))`. Since each output column is sorted, these leaked
ones occupy a contiguous strip immediately above row cut `h`, and

```text
leak_h = sum_c d_c(h) - max(0, m-(k-h)N).
```

This is the exact identity already used in the all-cuts probability reduction.
The existing certificate controls only the sum. The next AKS-specific screen
should control the *profile* `(d_c(h))`: for example, bound
`#{c : d_c(h)>w}`, simultaneously over every monotone input, rank, and p-way
cut. A uniform maximum-width bound is impossible, as shown next; a small tail
of exceptional columns may still be repairable separately.

## Universal per-column localization has a sparse-tail obstruction

Fix **any** row permutations `sigma_r`, and take `N=k`, `k` even. For a set
`C` of `t` destination columns and the bottom `s` rows `R`, define the source
set `A_r = sigma_r^{-1}(C)` in each row. Give source column `j` height

```text
h_j = max({ k-r+1 : r in R and j in A_r } union {0}).
```

Then every destination column in `C` receives a one in every selected row,
so its count before the final column sort is at least `s`. The input is a
valid monotone-column 0-1 matrix. For a fixed `C`, its mass satisfies

```text
sum_j h_j <= sum_(r in R) |A_r| (k-r+1) = t*s*(s+1)/2.
```

There is a stronger bound by averaging over all `t`-subsets `C`. For a source
column `j`, the event `h_j >= u` requires `C` to hit the destinations of `j`
in the `s-u+1` selected rows with threshold at least `u`. A uniformly random
`t`-subset hits those at most `s-u+1` destinations with probability at most
`min(1,t*(s-u+1)/k)`. Summing tail probabilities for `h_j`, then summing over
all `k` source columns, gives

```text
average_C sum_j h_j <= k * sum_(v=1)^s min(1,t*v/k).
```

Hence some `C` has mass at most this average. If it is at most `m=k^2/2`,
increase arbitrary column heights until the mass is exactly `m`; this cannot
remove any selected ones. At the middle cut `h=k/2`, the global ideal leakage
is zero, and each `c in C` has `d_c(h) >= s-k/2`. Thus, writing `w` for a
desired spill width, any `t` satisfying

```text
1 <= t <= k,   s = ceil(k/2 + w),
sum_(v=1)^s min(1,t*v/k) <= k/2
```

can be forced for every fixed row-permutation vector. This averaging
improves the simpler bound `t*s*(s+1)/2 <= m`. In particular:

| `(k,p,N)` | one-bin spill `w=k/p` | at least this many | two-bin spill `w=2k/p` | at least this many |
|---|---:|---:|---:|---:|
| `(1024,32,1024)` | 32 rows | 15 | 64 rows | 7 |
| `(256,16,256)` | 16 rows | 7 | 32 rows | 3 |

The input may depend on the fixed permutations, which is legitimate because
the claimed halver guarantee is universal over all monotone inputs. Therefore
no proof can show that **every** output column has spill less than one bin.
For the target instances, any universal one-bin tail theorem must allow at
least 15 (respectively 7) exceptional columns; at two-bin spill the forced
minimum is at least 7 (respectively 3). These are still a small fraction of
the 1024 (respectively 256) columns. The useful target is a sharp simultaneous
*upper* tail bound not much larger than these minima, followed by an explicit
network that repairs the sparse columns while preserving the other cut and
fringe guarantees. The existing aggregate all-cuts bound gives no useful tail
estimate at this scale. As `k=p^2` grows, the construction forces about `p/2`
columns at one-bin spill and about `p/4` at two-bin spill, so the natural
exception budget is `O(p)` out of `N=p^2`, rather than zero or `O(1)`.

## Work plan with stop/go criteria

1. **Reconstruct the primitive exactly.** From the 1992 paper, define the
   fixed two-round network, its row permutations, output bins, both
   orientations, and an explicit finite leakage function `E(k,p,N)`.
   Separately identify what the page-689 “combine parts” operation must do.
   Do not treat the 60–100 private estimate as a theorem or a parameter set.
2. **Derive a composable interface.** First establish localized crossing and
   adjacent-bin closure, or a counterexample to deriving them from the current
   count contract. If localization holds, try overlapping recursive bins and
   explicitly sort their error bands. Prove a recurrence for maximum subproblem
   size and total depth, including partial bins and the terminal sorter. The
   recurrence must show contraction by a fixed factor greater than one at every
   scale.
3. **Run the budget gate before Lean.** For the unchanged factor-64 schedule,
   require total node depth `<400` for `<200`. For a p-ary recursive schedule,
   compute `(T+G)/log2(p)` from proved finite parameters and demand `<200`.
   Include all serial k-sorter, combiner, overlap-sort, and fringe-repair
   layers. If the best contract is only `E >= 0.4`, stop trying to feed it to
   the current scheduler; it needs a different recurrence.
4. **Attack the bottleneck, not the small sorter.** For each cut `h` and spill
   width `w`, bound `Q_w = #{c : X_c >= k-h+w}` simultaneously over monotone
   inputs, ranks, and cuts. The adversary above proves `Q_w` cannot be zero;
   a plausible first target is `Q_{k/p}=O(p)`, with both orientations and
   enough slack for a fixed repair network. The current proof controls only
   aggregate leakage and uses a coarse weak-composition count for dense ranks.
   Replace that count with the paper's monotone-matrix/equivalence-class
   structure for this tail event, jointly over cuts. If the best universal tail
   bound is much larger than `O(p)`, this row-scramble core is unlikely to be
   the path; seek a new construction or recover the missing AKPS k-sorting
   exposition.
5. **Formalize only the surviving local theorem.** Keep it in this experiment
   package. First prove a finite theorem for one explicit parameter tuple,
   then its recurrence and depth theorem. Promote only when the full global
   bound beats 1419 and has passed the axiom guard.

## Immediate next deliverable

Produce a small parameter/recurrence table with columns `(k,p,N)`, binary core
depth, certified `E`, proposed combiner/recovery depth `G`, contraction factor,
and resulting coefficient. At present the first three local entries are
known, but `G` and contraction are unknown. This table is the decisive missing
artifact: without those entries, a claimed coefficient below 200 is not yet a
quantitative research path.

## Decision

Keep the multiway route as a high-upside structural experiment, but do not
present sub-200 as reasonably established. The current certified core by
itself is insufficient, and the unspecified combiner is the critical gap.
The most valuable next step is the composability proof (or a precise
counterexample/barrier), not another isolated halver constant optimization.
