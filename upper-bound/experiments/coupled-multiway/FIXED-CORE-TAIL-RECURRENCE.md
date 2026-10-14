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
permutations works. The experiment does not save that witness vector or a
certificate identifying it. The analogous `(256,16,256,0.55)` record has the
same status. Thus there is no concrete permutation vector in the repository
whose spill tail can currently be measured or certified. Any result for the
actual chosen core first needs either an explicit vector plus a universal
certificate, or a stronger simultaneous probabilistic existence argument
that selects one vector satisfying both aggregate and tail clauses.

This matters: sampling one vector and trying random inputs would not verify a
universal tail property. Also, the universal adversary already recorded in
`ajtai-multiway/BELOW-200-PLAN.md` forces at least 15 columns to spill by one
bin width and 7 by two bin widths for the 1024/32 tuple. A useful tail must
allow a nonzero exceptional set.

## Exact tail-to-crossing identity

Fix a binary rank threshold `m` and an output row cut `h`. After the final
column sort, let `X_c(m)` be the number of threshold-one keys in output column
`c`. Orient ones at the bottom and put

```text
d_(h,m,c) = max(0, X_c(m) - (k-h)),
Q_(h,m)(w) = #{c : d_(h,m,c) >= w}.
```

The leaked-one count at that cut has the exact form already used in the
row-scramble analysis:

```text
L_h(m) = sum_c d_(h,m,c) - max(0, m - (k-h)*N)
       = sum_{w>=1} Q_(h,m)(w) - max(0, m - (k-h)*N).
```

The second equality is the integer layer-cake identity
`d = sum_{w>=1} 1[d>=w]`. For a band width `b=k/p` rows, the number of
one-entries in these strips extending at least `ell` whole row-bands past the
cut is exactly

```text
Xcross_(h,m)(ell) = sum_c max(0, d_(h,m,c) - ell*b)
                  = sum_{w>ell*b} Q_(h,m)(w).
```

For zeros, apply the same formulas to the complemented matrix and reverse the
orientation. Therefore a simultaneous envelope `Q_(h,m)(w) <= R_(h,m)(w)`
for every cut, rank, width, and orientation immediately gives both total
misrouting and long-range-crossing bounds by summing `R` over widths. This is
the clean interface a localized repair would consume. It is also more
informative than a single aggregate leakage number because it separates
adjacent-band traffic from long jumps.

## What the existing `E=0.45` theorem induces

The all-cut theorem only says `L_h(m) <= E*min(m,kN-m)`. In the range where
the baseline term in the identity is zero, it implies the cumulative bound

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
`R_(h,m)(w)` is known for the fixed core, (ii) the existentially selected
permutation vector is not stored, (iii) a sparse exceptional-column tail
does not itself provide an oblivious gathering network, and (iv) the current
aggregate contract yields a central rank-profile coefficient as large as
`13.95` before old impurities are added. A successful next result should be
one of: a refined all-rank tail certificate for a concrete vector; a new
probabilistic existence proof for one vector with the full tail envelope; or
a construction whose matching/routing structure supplies localization
deterministically.
