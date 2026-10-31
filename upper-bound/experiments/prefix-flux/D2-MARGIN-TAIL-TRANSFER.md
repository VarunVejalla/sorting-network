# D2 variance to band-repair margin tails

Status (2026-10-27): the margin-tail arithmetic is kernel-checked in
`D2Slope25MarginTail.lean`. `D2LiftedShuffleBridge.lean` now also proves that
the actual Chvatal `semanticExec2` network for strides 35 then 25 maps every
4096-by-64 column-prefix Boolean input to the exact `fullHeightTwoShuffle`
profile. The band-repair wiring and its effect on the global rank invariant
are still open.

The input precondition has now been normalized to the scheduler's useful
boundary state. `columnMonotone_eq_lowPrefixBool` proves every column-sorted
Boolean matrix is represented by its per-column false counts, and
`semanticExec2_two_stride_eq_fullHeight_of_columnMonotone` applies the exact
profile theorem to any such matrix. The macro's output is again
column-monotone (`semanticExec2_two_stride_preserves_columnMonotone`). Thus
the fixed core is a closed transition on the column-sorted Boolean state
space; this alone gives no relation between its output positions and global
key ranks, and it does not yet identify the scheduler's ragged tile ports.

The 52-row profile deviation now yields a wire-level cut localization:
`semanticExec2_two_stride_flat_cut_band` proves every false output wire lies
before the output false-count cut plus 3392 wires, and every true wire lies no
earlier than 3392 wires before that cut. The constant allows 53 rows of slack,
covering the 52-row profile deviation and the within-row offset. This is a
Boolean output statement; relating its cut to each key's original rank
requires transporting every threshold through the value-valued network, and
connecting tile cuts to the D2 scheduler remains open.

## Reusable connection to UB-34

UB-34's deterministic band lemma says that after a row-preserving scramble,
sorting disjoint vertical bands of radius `W` makes the number of keys that
cross a cut from distance at least `d` at most the first-round excess beyond
margin `d-W`. This step does not depend on randomness; randomness is used only
to supply a tail bound for that excess. Its Lean proof already exists in the
best package: `Chvatal.bandStage_rowCount_le` and
`Chvatal.mergeBandPack2Net_low_crossings_le` in
`upper-bound/best/AKS/Sub800/MergeBandPack.lean`. Those theorems use the
Sub800 comparator-network model, while the current D2 core is formalized as a
height transition, so the remaining work is an adapter from D2's physical
tile addresses to that matrix-network interface rather than reproving L3a.

For the 4096-row D2 two-shuffle core, the checked theorem
`fullHeightTwoShuffle_area_per_column_le_169_over_eight` supplies a stronger,
deterministic input. Write `x_j` for its 64 output column heights and
`mu = (sum_j x_j)/64`. Its bound is

```text
(1/2) * sum_j (x_j - mu)^2 <= 64 * (169/8) = 1352.
```

The generic reciprocal estimate is useful for smaller margins: for every
real margin `r > 0`, `(z-r)_+ <= z^2/(4r)`. Thus both upper and lower excess
profiles satisfy

```text
sum_j (x_j - mu - r)_+ <= 676/r,
sum_j (mu - r - x_j)_+ <= 676/r.
```

The `+` notation is positive part. Thus, if this variance bound applies to the
profile immediately before the within-row scramble, UB-34's band argument
would give at most `676/(d-W)` far-crossing keys at a cut with `d > W`,
without a probabilistic tail certificate. For example, excess margin `r=28`
gives a bound below 25 keys; with band radius `W=28`, this covers crossings
whose rank distance is at least `d=56`. This is a deterministic profile
bound, not yet a bound on the complete D2 stage or its terminal rank error.

There is a stronger hard cutoff. Since each squared deviation is one term of
the total, the same area theorem implies `|x_j-mu| <= 52` for every column.
Both excess sums are exactly zero beyond margin 52; this stronger statement is
also kernel-checked in `fullHeightTwoShuffle_column_deviation_le_52` and
`fullHeightTwoShuffle_margin_52_excess_eq_zero`. In UB-34's L3a interface,
for a row-aligned threshold, band radius `W=28` therefore forbids any crossing
over a cut from distance at least 80 rows. Non-row-aligned thresholds require
a one-row rounding charge. If the same bound persists at the terminal
separator, only bounded-width boundary runs can contain out-of-interval keys;
sorting/merging those runs could make terminal cleanup a constant-depth tail.
That conclusion still depends on proving the full D2 stage and terminal
address correspondence.

## What has to line up

The right schedule is to place a row-preserving scramble after the
variance-controlled column sorts, then sort vertical bands centered at the
actual child cuts **in place of the final full column sort**. The bands must
be disjoint (cut separations at least `2W`); their offsets must be represented
by the physical wire addresses; and the next stage must consume the resulting
crossing bound without losing it to another unrestricted shuffle. A 64-row
padded bitonic band sort costs 21 layers in parallel across columns. The
4096-row candidate's three preceding full sorts cost `3*78=234` layers. If
the existing 21-layer sparse-edge repair is also retained in the last
scramble, the modeled stage costs `234+21+21=276` layers, giving coefficient
`276*(5/6)=230`. If that edge repair is unnecessary, the cost falls to 255
layers, coefficient 212.5. These are cost models only: neither resulting
macro-stage has a proved D2 transition or all-depth rank invariant.

The minimum fringe and the spacing between child cuts are different
quantities. Exact screens of the sparse-bottom flow found the minimum
positive output block (in row units for a 64-column tile) to be:

| Flow scale | depth 25 | depth 50 | depth 100 |
|---:|---:|---:|---:|
| 4096 | 128 | 64 | 256 |
| 8192 | 256 | 128 | 512 |

Every positive block in these screens is also a multiple of the flow scale.
Since one tile row has 64 wires, the scale-4096 cut residues lie on a
64-row lattice modulo the 4096-row tile; distinct residues are therefore at
least 64 rows apart (or coincide). Zero-sized blocks repeat a cut and can
share one band. Thus the abstract finite schedule passes the 56-row spacing
gate for `W=28`, even though another sender has only a 2.45-row fringe. This
is evidence that the thin-fringe observation does not itself obstruct
disjoint bands.

Reproduce the scale-4096 check with
`python d2_band_spacing_gate.py --depths 25 50 100`, or use
`--scale 8192` for the second row. It checks the exact finite FlowDAG output
blocks, not their physical wire realization, and does not prove a uniform
all-depth spacing bound.

## Immediate gate

The next gate is to prove that the physical D2 addresses realize the checked
contiguous intervals, preserve the scale-4096 block lattice at all depths,
place the repair after the relevant row scramble, and show later stages
retain its crossing bound. Then sum `676/(d-W)` over the active cuts against
the existing per-stage rank-error allowance. The finite spacing screen
clears only the first abstract arithmetic gate.


## Terminal cleanup from logarithmic rank displacement

There is a simpler exact terminal contract than a power-law inversion bound.
Suppose a fixed prefix network leaves every key at a position `p` whose
correct sorted rank `r(p)` satisfies `|r(p)-p| <= W`, uniformly over every
Boolean input. Choose `W` to be a power of two and partition the wires into
blocks of length `B=8W` (with the last partial block handled by fixed padding).
The following fixed cleanup sorts the output: first sort every block; then,
for each boundary `b` between blocks, sort the window `[b-2W,b+2W)`, of length
`4W`. These seam windows are disjoint because `B>=4W`.

Here is the rank argument. Before the first sorting pass, every key in the
left block of a boundary `b` has rank at most its old position plus `W`, so
at most `2W` keys in that block can have rank `>= b-W`: their old positions
must be among its final `2W` positions. After sorting that block, all such
keys lie in its last `2W` slots. Symmetrically, at most `2W` keys in the right
block have rank `< b+W`, and after sorting they lie in its first `2W` slots.
Every key in the seam window is greater than every key in the left interior:
its left-block keys follow that interior in the already sorted left block,
and its right-block keys have rank at least `b-W`. Symmetrically, every seam
key is smaller than every key in the right interior: its right-block keys
precede that interior in the sorted right block, and its left-block keys have
rank at most `b+W-1`. The left interior has rank `< b-W` because at most `2W`
left-block keys can reach that threshold; the right interior has rank `>=b+W`
by the symmetric count. Sorting the seam window therefore orders it with
respect to both interiors. The block interiors and seam windows partition the
wire line, so the whole output is sorted.

If `W=O(log n)`, Batcher bitonic sorting of blocks and seam windows costs
`O(log^2 W)=O(log^2 log n)=o(log n)` depth. Therefore the band-repair route
only needs a universal prefix theorem giving maximum rank displacement
`O(log n)`; its asymptotic coefficient is then unchanged. This terminal lemma
is independent of D2 and has a direct finite proof, but it does not establish
the required displacement bound. The next critical result is to derive a
per-macro-stage bound `W_next <= W_current + C` from the row-distance-80
crossing contract and the actual D2 address/spacing invariant. The UB-34 band
lemma alone does not yet imply that recurrence.

The generic conversion from an all-threshold zero-crossing contract to a
pointwise displacement bound is now kernel-checked in
`D2CrossingToDisplacement.lean`. Its two hypotheses are exact: for every
threshold `k` and output cut `p`, no key of rank `< k` occurs at an output
position `>= p` when `k + C <= p`; and no key of rank `>= k` occurs at an
output position `<= p` when `p + C < k`. These imply for every position `p`
that `|rank(p)-p| <= C`. This closes the count-to-pointwise implication once
the D2 band stage supplies those two zero counts for every threshold and cut.
It does not prove that supply condition or the macro-stage recurrence.

`D2RankDisplacementComposition.lean` now kernel-checks the next abstract
composition step. For an arbitrary finite list of stage rank maps, if every
stage satisfies the two crossing conditions with the same `C`, the composite
has displacement at most `numberOfStages * C`. This formalizes the
linear-in-stage accumulation needed by logarithmic-displacement cleanup. The
construction-specific premise remains open: no theorem currently shows that
the actual D2 physical sender/routing/band-repair stage satisfies the crossing
conditions for every threshold and cut. The focused Lean check passed by
building the module in the `upper-bound/best` Lean environment.

## Exact sorting preserves displacement on an arbitrary sender set

`D2BlockSortDisplacement.lean` now kernel-checks the sender-set version of the
block lemma. Let `addr : Fin M -> Fin N` enumerate any sender's physical wires
in increasing address order. If the incoming global rank map is within `E` of
physical address, then an exact local sort of the keys in that sender keeps
every key within `E` of its address in the same ordered sender set. The proof
uses only that `addr` is strictly increasing and the local sort is monotone;
the sender addresses may be noncontiguous. The approximate version,
`ordered_sender_approximate_sort_adds_error`, adds a local pointwise rank error
`D`, giving `E+D`.

The new `partitioned_sender_stage_adds_error` combines these estimates over a
whole stage. It accepts an explicit owner and local-slot decoder for each
physical wire and proves that disjoint sender-local operations with error `D`
give one global stage with error `D`. The next stage may use a different owner
map: rank-slice routing only changes that classification, not the physical
wire where the current output value resides. Thus the remaining local gate is
not a separate cost for routing; it is to instantiate the decoder for the
actual D2 active senders and prove their fixed local network's global-rank
error relative to exact sorting of each sender.

`local_rank_displacement_with_address_gaps` now isolates the physical-address
conversion. If an exact sorted sender profile is within `E` of its ordered
wire addresses, the local network moves each output key by at most `C` slots
in sender-rank order, and consecutive sender addresses have gaps at most `G`,
then the output key is within `E + G*C` of its physical wire. This applies the
existing 3392-slot D2 core estimate with global charge 3392 on a contiguous
tile (`G=1`). For a ragged sender set, the largest address hole can make `G`
large; the sharper target is to prove that the local rank movement never
crosses a hole, or to charge only the holes actually crossed using the band
tail. Thus the local stage gate is now a fixed-tile rank-displacement theorem
plus a run-boundary crossing theorem for the actual sender masks.

This would make a linear-in-stages displacement recurrence sufficient, without
contracting a global inversion potential. The remaining D2 bridge is precise:
prove that the fixed four-sort/band-repair network is within a uniform `D` of
exact sorting for each actual sender and wire the exact D2 owner/slot decoder
to this theorem. Existing local bounds apply to a full fixed tile with
column-monotone input; they do not yet provide this pointwise contract for
every scheduled sender. The focused Lean check passed in the
`upper-bound/best` environment.

## Physical-network interface audit

The repository does have a general comparator-network interface for an
arbitrary row-preserving shuffle: `AKS.Chvatal.MatrixBridge.semanticExec2`
means column sort, shuffle 1, column sort, shuffle 2, column sort, and
`F2Det.semanticExec2_decode` exposes its exact intermediate column counts.
`D2Slope25BundleSort.lean` also proves an exact physical realization of a
stride-25 two-step schedule, but only for a 64-by-64 tile and its sparse
40-mass gate. The 4096-by-64 full-height variance model is a separate lifted
profile transition; no theorem yet identifies it with a `semanticExec2`
execution or supplies the final band network. The next adapter should define
the row permutations on `Fin 4096`, prove that the Boolean threshold's
post-sort false-prefix heights are `fullHeightTwoShuffle`, then apply the
band stage and its rank-count contract. This isolates the remaining physical
gap instead of treating the height calculation as an already-realized stage.

The two row permutations needed by that adapter are explicit. For a height
profile `h`, let

```text
H_s(h)(d) = sum_c |{ r < h(c) : c + s*r = d (mod 64) }|.
```

Then `H_35(h)` is exactly `slope35PhysicalOutputHeight h`. The current lifted
definition of `fullHeightTwoShuffle` is
`slope25PhysicalOutputHeight (fun c => H_35(h) (35*c))`. Reindexing its source
column by the permutation `c -> 35*c mod 64` shows this equals `H_25(H_35(h))`.
Thus the target `semanticExec2` scrambles are the row-wise cyclic shifts by
`35*r` and `25*r` on `Fin 4096`; both preserve rows, and the second pass uses
all 64 repetitions of the base residue cycle. The outstanding Lean adapter is
now a precise count identity between these cell permutations and the existing
lifted profile formula, followed by decoding false-prefix heights from the
general two-shuffle execution.

The profile-level identity is kernel-checked in
`D2LiftedShuffleBridge.lean`: `fullHeightTwoShuffle_eq_two_rowShiftLoads`
rewrites the lifted formula as `rowShiftLoad 25 (rowShiftLoad 35 h)`. This
formalizes the factor-35 reindexing. The theorem does not yet mention a Bool
matrix or `semanticExec2`; establishing that equality is the next physical
adapter obligation.


## D2 tile alignment audit (finite; all-depth lemma target)

I added `d2_tile_alignment_gate.py` to check the sparse-bottom `(3,3,2)`
integer flow against the physical tile dimensions; `(3,3,2)` matches the
candidate's `15/4096` ordinary quota factor. At scale4096, a core tile is
`4096*64=262144` wires, with the 4096 grid dividing the candidate's actual
8192 base scale. Through depth100 the run has286 stages and 217,470
active stage-state rows. It passes the 64-row alignment check, and all observed
tile remainders are multiples of4096. This is finite evidence only. Reproduce
with `python d2_tile_alignment_gate.py --depth 100 --audit-reachable`.

An additional all-tree-state audit through depth100 checked 556,565 reachable
tree states: every node deficit and allocation is divisible by4096, while
both endpoint deficits are divisible by2048. Active quotas and child blocks
are 4096-aligned, and half-quotas are 2048-aligned. The gate reproduces these
checks with `--audit-reachable`. Across 1,634,784 ordinary child cuts, each
quota is divisible by8192, both computed fronts are 4096-aligned, and each
cut is individually 4096-aligned. `D2CutAlignment.lean` proves that
4096-aligned fronts and child boundaries yield 4096-aligned cuts. It also
proves every ordinary candidate quota is 8192-divisible for all `d ≥ 7`, by
role-specific exponent bounds. Thus `d2FlowCandidateRun_tileAligned_of_frontContracts`
only assumes the recursive front-alignment contract for actual run trees; the
scale-8192 initial state and generic all-depth transition are formalized.
Finite screens support, but do not prove, this remaining scheduler contract.
Even a completed alignment theorem would not prove the comparator network's
fixed-mask specialization or the parent-to-child 448-error contraction.

2026-10-27 threshold-to-rank bridge: `D2LiftedShuffleBridge.lean` proves
`semanticExec2_comp_monotone`, the conservation identity
`fullHeightTwoShuffle_total`, and
`semanticExec2_two_stride_flat_cut_band_input_total`. These combine in
`semanticExec2_two_stride_rank_interval`: for every value at every output
wire, its number of strictly smaller input keys is at most `position+3392`,
and its position is strictly less than the number of input keys at most that
value plus 3392. Thus the fixed core has a kernel-checked 3392-wire rank
interval on any one 4096-by-64 tile whose input columns are sorted. Both strict
and non-strict thresholds handle duplicates. The remaining gap is global:
the D2 scheduler must supply these fixed tiles/column-sorted boundaries and
transfer their local rank intervals across ragged ports and successive stages.
