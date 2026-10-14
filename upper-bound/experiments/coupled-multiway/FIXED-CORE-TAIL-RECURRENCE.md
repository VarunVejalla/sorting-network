# Fixed-core spill tails and the induced rank profile

Status: exact counting identities and a negative screen of the currently
available contract. No simultaneous tail theorem or improved bound is proved.
The AKS row-scramble files were inspected in the main checkout:
`upper-bound/experiments/ajtai-multiway/BELOW-200-PLAN.md`,
`SPILL-TAIL-RESEARCH.md`, `certify_dense.py`, and `screen_multicut.py`.

## What is—and is not—the fixed core

The local `(k,p,N,E)=(1024,32,1024,0.45)` result is an existence screen: it
shows that the random-permutation argument has total failure probability
below one for the all-cut aggregate leakage clauses, so some vector of row
permutations works. That proof does not identify its witness vector. The
analogous `(256,16,256,0.55)` record has the same status.

For an adversarial test, this note now fixes a separate concrete candidate
vector by NumPy PCG64 seed `20261014`. The generator and core hash are recorded
in [`seeded_spill_attack.py`](seeded_spill_attack.py) and
[`seed-20261014-middle-spill.json`](seed-20261014-middle-spill.json). This
seeded candidate is **not** certified to satisfy the universal `E=0.45`
contract, and it is not claimed to be the existential witness from the
probability screen. It lets us evaluate actual input profiles against one
reproducible fixed core; it does not establish a universal upper tail.

This matters: sampling one vector and trying random inputs would not verify a
universal tail property. Also, the universal adversary already recorded in
`ajtai-multiway/BELOW-200-PLAN.md` forces at least 15 columns to spill by one
bin width and 7 by two bin widths for the 1024/32 tuple. A useful tail must
allow a nonzero exceptional set. The seed-specific greedy attack below finds
42 one-bin spill columns, sharpening the concrete lower witness for this
candidate.

## Seeded adversarial profile

For each possible output column `c`, precompute its least required input
height vector: at source column `j`, it is the largest threshold `k-r` among
the targeted bottom rows `r` for which that row permutation sends `j` to
`c`. For a set of selected output columns, the coordinatewise maximum of
these height vectors is the least monotone-column input forcing every
selected output column to contain a one in every targeted row. Greedily add
the destination with the least increase in total input mass. This is a
heuristic set search, not a global optimum.

For the seeded 1024-by-1024 core, target cut `h=512`, spill `w=32`, and rank
mass `m=524288`, greedy selection of 42 output columns requires 523,992 ones.
Padding 296 arbitrary input cells gives exact rank mass without destroying
the forced spill. The actual output has:

| Quantity on this one input profile | Exact value |
|---|---:|
| Selected columns with at least 32 spill rows at `h=512` | 42 |
| Total minority leakage at `h=512` | 2,431 |
| Largest leakage over all 1,023 row cuts | 2,431, only at `h=512` |
| `Q(33)` at `h=512` | 11 |
| `Q(64)` at every row cut | 0 |
| Spill mass extending beyond one full 32-row band at `h=512` | 14 |
| Spill mass extending beyond two full bands | 0 |

The 42 count is `1.3125*p`, so this witness is still consistent with a
constant-times-`p` exceptional-column target; it does not refute that target.
It does show why the total leakage contract is weak for tail analysis: the
all-cut budget at this rank is `0.45*m = 235,929.6`, while this input uses
only 2,431 leakage and already has 42 columns at the one-bin spill threshold.
The sparse tail and the long-range tail are distinct: 42 columns spill at
least one band, but only 14 wires extend beyond that band, and none extend
beyond two bands, on this input.

The same greedy construction was run at each lower-half child-boundary rank
`m=q*C`, with row cut `h=q*k/p` and one-band spill `w=k/p`. These entries are
**found lower witnesses** for the fixed seed, not maxima or upper bounds:

| `q` (rank in child capacities) | Greedy feasible columns `Q(w)` |
|---:|---:|
| 1–7 | 0 |
| 8 | 1 |
| 9 | 1 |
| 10 | 1 |
| 11 | 2 |
| 12 | 3 |
| 13 | 4 |
| 14 | 7 |
| 15 | 12 |
| 16 | 42 |

The counts rise sharply near the middle rank. This is consistent with the
rank-profile formula's center bottleneck and suggests the next attack should
optimize jointly over `(h,m,w)`, rather than spend effort on a fixed-rank
tail estimate. A universal bound still needs a principled upper-tail argument
for all monotone height profiles; the greedy search cannot provide one. Zero
means this particular forced-row construction did not fit even one selected
column into that rank's mass budget; it does not prove `Q(w)=0` for all inputs.

Reproduce with:

```text
python upper-bound/experiments/coupled-multiway/seeded_spill_attack.py \
  --save upper-bound/experiments/coupled-multiway/seed-20261014-middle-spill.json
```

This command reports the full input height vector and hashes the regenerated
row-permutation vector as little-endian 16-bit entries. The full input profile
is saved in the JSON result; the core can also be materialized with
`--save-core <path>.npz`.

## Exact tail-to-crossing identity

Fix a binary rank threshold `m` and an output row cut `h`. After the final
column sort, let `X_c(m)` be the number of threshold-one keys in output column
`c`. Use the minority orientation that can fit on one side of the cut, and
put

```text
d_(h,m,c) = if m <= (k-h)*N
              then max(0, X_c(m) - (k-h))
              else max(0, (k-h) - X_c(m)),
Q_(h,m)(w) = #{c : d_(h,m,c) >= w}.
```

In the first case, `d` counts ones that spill above the bottom `k-h` rows. In
the second, it counts zeros that spill below the top `h` rows. These are the
two symmetric error orientations, and the total minority leakage has the
exact form

```text
L_h(m) = sum_c d_(h,m,c) = sum_{w>=1} Q_(h,m)(w).
```

The second equality is the integer layer-cake identity
`d = sum_{w>=1} 1[d>=w]`. If instead one always uses the raw one-spill
quantity `max(0,X_c-(k-h))`, its sum contains the unavoidable baseline
`max(0,m-(k-h)N)` when ones do not fit below the cut; that raw quantity must
not be mistaken for error or used directly as a localized error tail. For a
band width `b=k/p` rows, the number of misrouted minority keys whose per-column
spill extends at least `ell` whole row-bands past the cut is exactly

```text
Xcross_(h,m)(ell) = sum_c max(0, d_(h,m,c) - ell*b)
                  = sum_{w>ell*b} Q_(h,m)(w).
```

The corresponding identity for zeros is already included by the second case
in the definition of `d`. Therefore a simultaneous envelope
`Q_(h,m)(w) <= R_(h,m)(w)`
for every cut, rank, width, and orientation immediately gives both total
misrouting and long-range-crossing bounds by summing `R` over widths. This is
the clean interface a localized repair would consume. It is also more
informative than a single aggregate leakage number because it separates
adjacent-band traffic from long jumps.

## What the existing `E=0.45` theorem induces

The all-cut theorem only says `L_h(m) <= E*min(m,kN-m)`. With the minority
orientation above, it implies the cumulative bound at every cut without a
baseline correction

```text
sum_w Q_(h,m)(w) <= E*min(m,kN-m),
Q_(h,m)(w) <= ceil(E*min(m,kN-m)/w).
```

At the one-bin spill width `w=k/p`, this Markov bound is much too weak for
dense ranks. For `k=N=1024`, `p=32`, `m=kN/2`, it gives
`Q(32) <= 7373`, exceeding the total 1024 columns. At a sparse child-boundary
rank `m=qC`, where `C=kN/p` is one child capacity and `0<=q<=p`, the bound
becomes

```text
Q_(h,qC)(w) <= E*min(q,p-q)*C/w.
```

It is still vacuous for central `q` at `w=k/p`; it does not imply the desired
`O(p)` exceptional-column bound. This is an algebraic consequence of the
current theorem, not evidence that the actual core has a large tail.

The existing attempt to prove a stronger universal tail from random row
permutations also has a specific failure mode. A union bound over input
height vectors and exceptional column sets pays entropy much larger than the
fixed-set Hoeffding exponent in the desired `r=O(p), w=O(k/p)` regime. The
paper's top-row equivalence-class reduction helps sparse ranks, but filling
the bottom of each representative raises its average above the spill
threshold for most dense ranks. The event-specific fill depends on the row
permutations and cannot be counted as an independent representative. These
are the findings in `SPILL-TAIL-RESEARCH.md`; the tail remains open.

## Rank-distance profile induced by all-cut leakage

Let `p` be the number of equal row-bands, `b=k/p`, and `C=bN` wires per
child. Number children `q=0,...,p-1`. For a clean parent whose local rank
interval agrees with the global rank interval, define `x_(q,s)` as the
number of keys in child `q` whose global ranks lie outside the interval
`[(q-s)C,(q+1+s)C)`, clipped to `[0,kN]`. For each valid outer boundary,
those keys cross the corresponding output cut. Hence the exact per-cut
contract implies

```text
x_(q,s) <= L_((q-s)*b)((q-s)*C)
         + L_((q+1+s)*b)((q+1+s)*C),
```

omitting terms with indices outside `0,...,p`. Thus the aggregate theorem
induces the rank-envelope

```text
x_(q,s) <= E*C * (
    min(q-s, p-q+s) + min(q+1+s, p-q-1-s)),
```

with negative/out-of-range terms replaced by zero. This is a valid one-stage
rank-distance profile for a clean parent. For `p=32`, `E=0.45`, and the
central child `q=15`, the `s=0` envelope is
`0.45*(15+16)*C = 13.95*C`. At an edge child the envelope is only `0.45*C`.
The profile therefore grows toward the center and is not a contraction in
child-capacity units. The all-cut aggregate theorem is too coarse to close a
recursive impurity invariant.

For a parent with prior impurity, let `u_b(m)` be the discrepancy between the
number of local keys below global rank `m` and the ideal clipped interval
count. The local binary input to the core then has rank `m+u_b(m)`, not `m`.
A candidate recurrence must include this shift. At a cut corresponding to
ideal cohort size `a`, a deliberately coarse bound is

```text
new_cut_error <= u_b(m)
               + E*(min(m,parent_size-m)+u_b(m)),
```

provided the shifted cohort size remains in range; endpoint clipping needs a
separate case. The two boundary errors around child `q` give its rank-1
profile, and the expanded-boundary formula above gives higher `s`. This
exposes a noncontracting central row even before accounting for the parent's
own profile. Replacing `E*min(...)` by the tail sum derived above is exactly
where a stronger fixed-core theorem would enter.

## Coupled profile interface if a tail theorem is found

For a general parent profile `u_b`, define a rank/cut transfer matrix
`K_(q,s),(r,t)` by bounding the shifted local cohort and all long-range
crossings from parent coordinate `(r,t)` into child `(q,s)`. Define fresh
profile `e_(q,s)` from `R_(h,m)(w)` via the layer-cake sums. The target is the
affine stage inequality

```text
x'_(q,s) <= e_(q,s) + sum_(r,t) K_(q,s),(r,t) * x_(b,r,t),
```

for every input, with one positive weight vector satisfying a strict
weighted-column contraction and with the weighted fresh error below the
terminal integer-purity budget. The local/global two-potential version may
be needed to retain deepest-leaf purity. The previous `COUPLED-RECURRENCE.md`
prices schedule-level additive errors but does not provide this core-specific
`K` or `e`.

The recurrence is not yet a proof because (i) no nontrivial simultaneous
upper envelope `R_(h,m)(w)` is known for all inputs to a fixed vector, (ii) the
existentially selected vector from the aggregate probability proof remains
unidentified, (iii) a sparse exceptional-column tail does not itself provide
an oblivious gathering network, and (iv) the current aggregate contract yields
a central rank-profile coefficient as large as `13.95` before old impurities
are added. A successful next result should be one of: a refined all-rank tail
certificate for a concrete vector; a new probabilistic existence proof for
one vector with the full tail envelope; or a construction whose
matching/routing structure supplies localization deterministically.
