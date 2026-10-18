# Four-block hybrid epoch: a contraction theorem and support gap

Status, 2026-10-10: informal theorem for an abstract all-threshold paired
repair, plus exhaustive small threshold-count exploration. This is not a
constructed network or a new Paterson bound.

## Epoch

Four ordered physical blocks each have `m` wires. Use three parallel phases:

    (0,1) and (2,3)
    (0,2) and (1,3)
    (1,2)

Each operation sorts or approximately repairs fixed cores, assigning their
smallest keys to the earlier block. Assume the pair has the relative residual
contract at every threshold relevant to the proof. Equal nominal block
cardinalities and balanced global rank counts are assumed in this model.
The upper forest's deep-prefix discrepancies require additional imbalance
terms; they are not silently set to zero here.

## Exact oracle sorts four blocks

At a fixed threshold, let `x_i` count low keys in block `i`. An exact
compare-split transforms a pair by

    (x_i,x_j) -> (min(m,x_i+x_j), max(0,x_i+x_j-m)).

The five-pair schedule packs all low keys to the left. To see this, after
phase 1 each adjacent pair is packed. If their low totals are `s,t`, write
their packed states as `(min(m,s),(s-m)_+)` and similarly for `t`.
Phase 2 puts `min(m,s+t)` low keys in block 0, and
`(s+t-3m)_+` in block 3. This follows by splitting into cases `s,t<=m`,
`s,t>=m`, and the two mixed cases. Their sum fixes the total in middle blocks.
The final middle compare-split packs those too. The result is the unique
left-packed state for the total low-key count.

For native threshold `c*m`, `c=1,2,3`, this state has `m` low keys in the first
`c` blocks and zero in the rest. The argument works for all `m`, not just the
finite example in the script.

## Approximate error bound: factor 5 epsilon

For a pair, the preceding excess-crossing lemma implies that its left low
count differs from exact compare-split by a nonnegative deficit

    d <= epsilon * min(H,L),

with the same surplus on the right. Here `H=m-x_i` and `L=x_j`. The operation
therefore has at most `2d` L1 discrepancy from exact compare-split on the
same input count state.

Exact count compare-split is L1 nonexpansive: its two outputs depend on the
sum `x_i+x_j`, and their combined absolute change is exactly the absolute
change in that sum. Unchanged blocks contribute their existing differences.
By induction through the five operations, the final L1 distance from the
ideal all-exact run is at most `2 sum d`.

Fix native threshold `c*m` and initial directional crossing error

    E0 = c*m - sum_{i<c} x_i.

Global balance makes this also the number of low keys in the other blocks.
Ordered core repairs cannot increase it. At each pair operation:

- If both blocks are left of the target cut, `H <= E0`.
- If both are right, `L <= E0`.
- If the pair crosses the cut, both are at most `E0`.

Thus `min(H,L)<=E0` and every `d<=epsilon*E0`. Final crossing error is half
the final L1 distance from the ideal balanced state, giving

    E_final <= 5 epsilon E0.

This is conservative but supplies genuine epoch contraction for
`epsilon<1/5`. At `epsilon=1/8` it is at most **5/8**. Repeating the abstract
epoch `t` times gives `(5/8)^t E0`, provided every primitive contract remains
valid throughout. The proof cannot replace the per-step support obligations.

## Small-model exploration

`four_block_epoch.py` exhaustively explores all balanced binary count states
for `m=8`, all three native thresholds, and all integer residual outcomes
allowed by `epsilon=1/4`. It reports:

| Schedule | Largest final/initial crossing ratio |
|---|---:|
| One two-phase adjacent sweep | 1 |
| Three-phase five-pair epoch above | 2/5 |
| Four alternating adjacent phases | 1/2 |

This supports investigating the nonadjacent epoch. It is not a proof of a
uniform 2/5 bound, not a test of actual comparator networks, and not evidence
that the current supported primitive satisfies the assumed all-threshold
contract. The uniform bound proved informally above uses smaller epsilon.

The one-sweep witness has all low keys in the last block: one adjacent sweep
moves them only partway left and makes no progress at the first cut.

## What local guard follows from aggregate crossing bounds?

Assume initially each block has at most `kappa` keys outside its own native
interval, and each native interval contains exactly `m` keys globally.
At cut `c`, directional crossing counts obey

    H_c=L_c <= min(c,4-c)*kappa.

Every ordered core repair preserves these bounds by monotonicity. A middle
block's low strangers are bounded by `L` at its lower cut, and its high
strangers by `H` at its upper cut. Consequently:

    outer block errors <= kappa,
    middle block errors <= 3*kappa.

This is a guard obtainable from the aggregate proof, not an assertion that
every operation attains threefold overload. A sharper operation-specific
guard might improve it. But the current proof does not maintain the old
local envelope, and cannot invoke a primitive whose support is only
`.02*m` when the justified error envelope is `3*.0199*m`.

Moreover, the epoch argument needs relative concentration at **all relevant
thresholds**, including thresholds where one side of a pair has a large
cohort and the other has a sparse cohort. A primitive that assumes both
one-sided wrong-key counts are locally small does not automatically meet
that contract. The proof's bound on `min(H,L)` is not a bound on both.

This is an additional asymmetric-contract obligation, even if a sharper
local guard is found. A full compare-split satisfies it but incurs the dense
selection/sorting costs we are trying to avoid.

## Cost interface and missing implementation

If an epoch pair primitive has uniform depth `p`, its epoch depth is at most
`3p`, because disjoint pairs execute in parallel. The five operations in the
error bound are not five sequential depth charges. After `t` epochs the
depth is at most `3pt`, plus final allocation/correction costs.

No useful `p` is established for the needed asymmetric all-threshold contract.
The existing exact-core cost tables cannot be treated as that primitive:
they assume specified small extreme cohorts, and exact concentration can
create a large core. Thus the epoch theorem supplies a scheduler-level
conditional result, but no improved sorting coefficient.

## Supported extreme cores resolve the asymmetric correctness interface

There is a useful sufficient primitive weaker than demanding relative
residuals for both full wrong-key cohorts. Require fixed left/right cores
that capture at least `(1-epsilon)*j` of the left block's largest `j` keys
and the right block's smallest `j` keys, for every integer `j<=K`.
Suppose only `min(H,L)<=K`.

If `H<=L`, the left core captures at least `(1-epsilon)*H` high keys, so
`a<=epsilon*H`. The right block's smallest `H` keys are all low; its core
therefore contains at least `(1-epsilon)*H` low keys. Consequently

    b <= L-(1-epsilon)*H,
    b-Delta <= epsilon*H,
    H' <= epsilon*H.

If `L<=H`, use the symmetric argument with the smallest `L` right keys and
largest `L` left keys to obtain `L'<=epsilon*L`. Thus the removable excess
contracts by epsilon even though the *larger* full error cohort need not
lie in the supported range.

This is an informal all-threshold adapter directly motivated by the existing
supported-extreme definition. A single supported halver gives such cores of
half-block size. Smaller-fringe separators or exact recursive concentration
can also supply them, but their core costs must be accounted for. A contract
only at the maximal rank `K` is insufficient; the quantifier over smaller
actual ranks is essential.

Within the epoch proof, `min(H,L)<=E0` for each target threshold. Initially
`E0<=min(c,4-c)*kappa<=2*kappa`, and monotonicity preserves that bound. Hence
supporting extreme cores up to **2*kappa** in each block suffices for the
conditional all-threshold epoch theorem. This bypasses the factor-three
local-total-error guard for this specific root-epoch oracle. It does not
justify the ordinary bag scheduler's other uses of local stranger bounds.

At `kappa=.0199*m`, the requisite core support is `.0398*m`, still beyond
the existing certified `.02` support and its 1/32 fringe capacity. A half-core
restricted halver can support it, but sorting the combined half cores creates
a large cost. A new smaller-core implementation must respect the necessary
fringe capacity `(1-epsilon)*.0398*m` per side and provide error 1/8 or better
for the conservative epoch factor 5 epsilon. Its budget is not the old
989-depth small-fringe separator budget.

The next useful obligation is therefore narrower: construct and cost
**all-supported-rank extreme cores** at that support/error, then combine them
with fixed-quota joint core sorting. Correctness no longer needs a separately
pure reservoir or both full cohorts to be sparse. Core size and epoch depth
remain the unresolved implementation costs.
