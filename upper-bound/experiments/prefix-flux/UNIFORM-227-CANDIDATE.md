# A uniform-flow candidate at conditional coefficient 227.5

2026-10-21. Structural paper candidate for **uniform Chvatal design U**; no
sorting theorem is claimed. Finite closed-form checks are in
`uniform_227_geometry.py`; finite checks against the actual explicit U
scheduler are in `uniform_227_explicit_check.py`; local F2 numerical screens
are in `uniform_227_probability_screen.py`.

## Flow and nominal cost

Use uniform Chvatal flow parameters `(x,y,z)=(3,2,2)`, hence
`k=8`, `A=4`, `nu=1/4`. The schedule has `tf(d)=(5/2)d+O(1)`, while
`log2(k^d)=3d`, so the stage/log rate is `5/6`. Three padded bitonic sorts on
at most 8192 rows cost `3*(13*14/2)=273` layers per stage. The nominal
limsup coefficient is therefore

```text
273 * 5/6 = 455/2 = 227.5.
```

This is below300 if the local separators compose through the full scheduler.
The root and final native blocks must still be shown to cost only `O(1)` in
the family depth.

The scale `S=2^14` multiplies the entire base family: the actual input size is
`N=S*8^d`, and every flow allocation is multiplied by `S`. Thus the root has
`S*8^d` wires, and the notation `a=8^d` below denotes its unscaled flow
allocation. The additive `log2(S)=14` does not change the limsup stage rate.

## Exact role geometry

Here `Q=A^2*k^2=1024` and `A*nu*k=8`. The schedule gives
`native/c = 2^(3+2t-5i)`. The seven observed bottom-descending residues are
`native/c=2^-j`, `0<=j<=6`. For a positive bottom-descending role with residue
`r`,

```text
a/c = r - 1/1024,       up/c = 7/1024,
up/(2a) = 7/(2048*r - 2).
```

The exact rectangular choices below satisfy the **scaled** identities
`S*a=m*n`, `S*up=2*f*n`, `S*down=b*n`, and `m=2*f+8*b`, where `S=2^14`.
The displayed `n` is `S*a/m`. These identities give a scaled rectangle with
`m` rows, `n` columns, `f` rows per fringe, and `b` rows per child block. This
is uniform U: each of its `k=8` children receives exactly `down(d,i,t)` wires.
The D2 cut-layout scheduler and its variable child-blocks are a different
flow and are not evidence for this candidate.

| Role | `m` | `f` | `b` | `n` |
|---|---:|---:|---:|---:|
| topDesc, `t>0` | 8 | 0 | 1 | `2048*c` |
| topRise | 8192 | 32 | 1016 | `2*c` |
| mid | 8184 | 28 | 1016 | `2*c` |
| botDesc, `r=1` | 8184 | 28 | 1016 | `2*c` |
| botDesc, `r=1/2` | 8176 | 56 | 1008 | `c` |
| botDesc, `r=1/4` | 4080 | 56 | 496 | `c` |
| botDesc, `r=1/8` | 8128 | 224 | 960 | `c/4` |
| botDesc, `r=1/16` | 8064 | 448 | 896 | `c/8` |
| botDesc, `r=1/32` | 7936 | 896 | 768 | `c/16` |
| botDesc, `r=1/64` | 7680 | 1792 | 512 | `c/32` |
| botRise | bypass | — | — | all wires go up (`up=a`, `down=0`) |

The root at `t=0` is handled separately with `a=8^d`, `m=8`, `f=0`, `b=1`,
and `n=S*8^d/8`. All row counts are at most8192. The finite script checks
exact allocation, divisibility, block sizes,
integer columns and `n>=16` through depth100; it also checks that the observed
bottom residues exhaust `{1,1/2,...,1/64}` on those depths. This is not an
all-depth schedule proof.

The independent explicit-scheduler check runs `slackfree/explicit.py` with
design U and compares every generated active node's allocation and up-count
with the closed forms, while checking its eight actual child blocks are each
exactly `down(d,i,t)`. It passes through depth7 (90,202 active-node instances).
The explicit table grows quickly, so this is a finite cross-check of the U
interpretation, not an all-depth proof. In particular, D2 `FlowDAG` results
must not be transferred to this U candidate.

## First local-provider screen

The critical small fringe is `f=28`. `uniform_227_probability_screen.py`
checks the generalized F2 interval envelope at `delta=10^-5` using
`g1=floor(2f/5)`, `g2=floor(4f/5)`, `c=1/2`, `b=5`, `J=30`, and the exact
small-`E=2` support count. It passes numerically for every fringe in the table:
`28,32,56,224,448,896,1792`. At the finite minimum column count of each
positive-fringe role, `floor(delta*f*n)>=1`; unlike the earlier `(3,3,2)` flow,
the tiny-rank cap is not identically zero on the narrow cases.

The scanned minima give `min(delta*f*n)=1.14688` across positive-fringe roles
(attained for `f=28,n=4096` and `f=896,n=128`). This is the likely replacement
for the existing `F2Pre.hf16` guard, which requires `delta*f*16>=1` uniformly
for all `n>=16` and fails here. In the current Lean code that guard is used to
prove the rank cap `jmax=floor(delta*f*n)` is positive. Replacing it with the
rectangle-specific `1<=delta*f*n` appears structurally local, but the exact
failure-bound hypotheses and the three-way provider conjunction still need
to be audited and proved for every role; the finite minima are not yet
all-depth bounds.

The screen now uses the `1/10000` per-event budget required by the existing
`FringeCert` wrapper (its doubled SR+R1 and R2 envelopes both pass), rather
than the earlier exploratory `1/1000` threshold. The exact parameter list,
finite `n` minima, and Lean-specific local-rank and `E=2` gaps are recorded in
`UNIFORM-227-PROVIDER-GATE.md`.

This remains a numerical screen, not a probability theorem or Lean instance.
The current checked Lean F2 interface assumes a much larger fringe; the
small-f exact-support extension and its positivity split are not formalized.
The probability budget must include a common witness for every baseline and
both orientations.

There is a more basic unresolved local gate: every node also needs bulk B2.
The current checked B2 provider is proved only for `m>=2^42`, while these
rectangles have at most8192 rows and eight children. Moreover, the exponent in
the existing B2 union bound at its current error target is about `7.93e-8`
per column at `m=8192`, versus a state-count cost about `9.70`; merely
generalizing its shape hypotheses cannot close that gap. See
`UNIFORM-227-PROVIDER-GATE.md`. This candidate therefore needs either a new
small-row bulk proof or a U-specific reachable-profile invariant that avoids
the universal B2 obligation.

The address-flow experiment now gives a sharper global warning: under the
actual uniform-U schedule, ideal rank-ordered local splits still leave 1,280
wrong-address keys after the last stage at depth5 (worst terminal node
fraction 0.078125). D2's cut-layout control leaves zero for the same input.
This rules out a zero-error address-preservation induction for U; a compensating
rank/address recurrence would have to be demonstrated before the conditional
227.5 coefficient is a live route. See `UNIFORM-227-ROUTING-OBSTRUCTION.md`.

## Gates before Lean

1. Prove by schedule induction the role/residue classification, all-depth
   divisibility and lower bounds for the listed column counts, plus
   `tf(d)=(5/2)d+O(1)` and terminal native-size bounds.
2. Prove a uniform local separator theorem for all rectangles in the table,
   with the rank-tail and prefix postconditions needed by the actual static
   port layout. Show the common-witness union still fits the probability
   budget.
3. Close root initialization, coupled rank/prefix tails, and terminal purity
   for the uniform-flow scheduler. The local F2 statement alone does not imply
   a sorting network.
4. Prove constant-cost cleanup and arbitrary-`n` padding, then formalize the
   complete family and limsup estimate.

No Lean work should start until the all-depth paper geometry and the global
rank-tail transfer have a complete specification and pass independent review.
