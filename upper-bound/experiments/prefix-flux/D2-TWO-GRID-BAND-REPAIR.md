# Two-grid band repair from the slope-25 profile range

2026-10-28. Local fixed-network construction and finite screen. This is a
candidate replacement for a full final column sort inside the D2 macro; it is
not yet connected to the global scheduler or proved correct in Lean.

## One-column lemma

Let `m` be divisible by 64. Let `x : Fin m -> Bool` have threshold-local
disorder of width at most `w`:

```text
x[r] = 1 for r < a,
x[r] = 0 for r >= b,
b - a <= w <= 32.
```

Apply two fixed segment-sort layers, in descending Boolean order:

1. Sort every aligned 64-row segment `[64j,64j+64)`.
2. Sort every shifted segment `[32+64j,96+64j)` that fits.

The output is globally sorted. If `[a,b)` is contained in one aligned segment,
the first layer sorts the whole word. Otherwise it crosses exactly one aligned
boundary `t`, since `w<64`. After layer 1, any remaining inversion is confined
to `[t-w,t+w)`: zeros on the left occupy at most the final `w` positions of
the left segment, and ones on the right occupy at most the first `w` positions
of the right segment. The shifted segment `[t-32,t+32)` contains this interval.
Layer 2 sorts it; every other shifted segment lies wholly in an already
constant part of the word. This is a fixed, input-independent network.

The divisibility condition matters: with an incomplete final segment, this
particular fitting-segment implementation can leave a defect at the tail
(for example, 64 ones followed by a zero at height 65). For a matrix whose
rows outside `[a,b)` are uniform across columns, an
arbitrary row-preserving column permutation retains this same exceptional-row
interval in every output column. Applying the two grids independently in
every column therefore restores column monotonicity. Each layer has depth at
most `bitonicDepthBudget 6 = 21`, so the pair costs at most42 comparator
layers, independent of matrix height.

## D2 connection and open bridge

`D2Slope25LiftProvider.fullHeightTwoShuffle_range_le_thirteen` proves that the
local 64-column profile after the two-shuffle core has pairwise range at most
13 for every natural input-height profile. Represent that sorted state as a
4096-by-64 bottom-suffix unary matrix. If the column heights range from `hmin`
to `hmax`, then rows below `4096-hmax` are all zero and rows at or above
`4096-hmin` are all one; the intervening band has width `hmax-hmin <= 13`.
A subsequent row-preserving column permutation keeps those exterior rows
uniform. Each resulting column is therefore a threshold word with dirty width
at most 13. The screen uses the dual (top-prefix, descending) orientation;
complementing bits and reversing comparator directions gives the bottom-suffix
ascending repair with the same depth. This gives a concrete schedule idea: use the two-grid network
to replace the third post-shuffle 4096-wire column sort, after the two-shuffle
profile has been restored to unary form. One initial 4096-wire sort and two
post-shuffle 4096-wire sorts cost `3*78`; the replacement costs `2*21=42`,
for 276 local layers total. At the candidate stage/log rate `5/6`, this prices
at coefficient 230, leaving 70 for other asymptotic costs. Under the same
cleanup formula `(p+theta)/(1-theta)` used in the p=273 route, this price
would tolerate `theta <= 7/37 ~= 0.1892` while staying at most 300. This is a
conditional price, not a proved sorting bound.

The variance consequence in `D2Slope25MarginTail.lean` also gives the weaker
pointwise bound of 52. The range-13 theorem is the sharper input: only 13
consecutive rows can be mixed, so the width-32 premise has slack.

`D2Slope35Physical4096.lean` now defines the actual 4096-row cyclic row
permutation as a `Scramble` and proves that the scrambled unary matrix has the
expected per-column count: `column_count_eq_row_sum` identifies it with the
number of rows whose inverse-shifted source column is occupied. This checks the
wire-level row action and matrix coordinates at height 4096. The companion
`residue_hits_eq_finRows` theorem identifies each source column's provider
residue count with the cardinality of the corresponding occupied-row subset
of the actual matrix. `row_sum_eq_physical_height` completes that aggregate identity by a finite
sum reindexing across source columns and rows, and
`column_count_eq_physical_output_height` states the resulting exact equality.
`columnSort_exec_eq_bottomUnaryProfile` then proves generically that a vertical
column sort turns any matrix with a given profile into its bottom-unary matrix;
`slope35SortPhysical_eq_bottomUnaryProfile` instantiates it for the actual
4096-row stride-35 phase. The module now also formalizes the required row
reversal and multiplication-by-35 column relabeling, proves the affine
slope-25 row action has exactly `slope25PhysicalOutputHeight` counts, and
proves `fullHeightTwoShuffle_physical`: the complete two-shuffle,
two-column-sort network outputs the bottom-unary matrix for the provider's
4096-row profile. The unresolved local bridge is now specifically the
post-profile row-preserving shuffle plus two-grid segment-sort network, and the
rank-port recurrence that consumes its output counts. This module
also passes a focused `lake env lean ../prefix-flux/D2Slope35Physical4096.lean`
check from `upper-bound/experiments/runaware` with the prefix-flux directory on
`LEAN_PATH`.

`D2BandRepair4096Network.lean` now defines both fixed networks directly on the
4096-by-64 wires. Each is a flatMap of disjoint 64-wire bitonic sorters; the
kernel-checked depth bounds are 21 per grid and 42 total. The file proves that
each aligned or shifted 64-wire segment is sorted after its respective pass,
and contains a local theorem that their composition sorts every threshold word
whose dirty band has width at most32. The source also contains the direct
composition with the range-13 physical D2 band interface, after an arbitrary
row-preserving column permutation. Both the local threshold-band theorem and
the physical composition now pass focused Lean checks. The physical check was
run with the worktree's existing provider `.olean` directory appended to
`LEAN_PATH`, and the source was checked by the Lean kernel. Existing
`D2Slope25BundleSort.lean` realizes only a 64-by-64 physical fragment, while
`D2Slope25LiftProvider.lean` proves a scalar 4096-height profile bound. The
existing 448-per-tile count transfer does not provide the global rank-port
recurrence. No coefficient improvement is established until band correctness,
the root, all-depth transfer, terminal cleanup, and full depth schedule are
proved.

## Exact physical profile transfer

The Lean network module now proves the two-grid comparator list is column-local.
Using the generic per-column true-count preservation theorem, it shows that
the repaired output column count equals the row-sum of the scrambled input
profile. It identifies this row-sum with the existing scrambledColSum operator,
including the affine slope-25 shuffle used in the physical D2 module. Together
with the checked band theorem, each repaired column is exactly the bottom-unary
profile of that deterministic output height. The output heights also have
pairwise range at most 13 for any row-preserving permutation. This closes the
local stage count and range interface; the recursive schedule's rank cuts/tags
and all-depth recurrence remain unproved.

## Finite check

`band_repair_screen.py` implements the exact two fixed grids using segment
sorting. The checked run exhaustively covered127,741 threshold words of length
256 with dirty widths at most8, then tested100,000 random words with dirty
width at most32; every output was sorted. This is a diagnostic of the stated
combinatorial claim, not the proof (the case argument above is the proof) and
not a Lean verification of the comparator network realization.

### Aggregate inversion budget after the two-grid fixed repair (2026-10-28)

`D2BandInversion.lean` proves that if a Boolean word is false before and true after a band of at most `W` wires, its one-before-zero inversion count is at most `W^2`: every inversion pair must lie wholly inside the band. `D2BandRepairInversion.lean` specializes this to the formal physical two-grid stage using `physical_twoGridRepair_common_wire_band`, giving the per-threshold, per-sender bound `832^2 = 692224`, with no dependence on the height profile. Both modules pass focused kernel checks.

This provides an aggregate local inversion allowance for the hybrid aggregate-plus-seam contract in `HIGHER-DISTANCE-MOMENT.md`. It is only a local allowance: the global schedule still needs to control cross-sender alignment, charge the seam terms, initialize the required rank state, and prove terminal cleanup and depth.

The physical interface now also exposes `a <= b` and both band endpoints inside the 4096-row domain. `D2BandRepairInversion.lean` uses this to prove `physical_twoGridRepair_misplaced_bits_within_832`: for every threshold, the exact zero-count cut lies between the common band endpoints, and every misplaced one or zero is within 832 wire ranks of that cut. This is the stronger local localization contract; the `832^2` inversion bound above is a coarser consequence. The remaining obstruction is global: the recursive flow must identify each sender's local zero-count cut with the correct global rank up to a controlled spatial error, including at startup and terminal seams.

`D2BandRepairMoment.lean` now derives the explicit local third-moment bound
`M_3 <= 832^4` from the same two checked facts (at most 832 misplaced wires,
each within 832 ranks of the sender's own exact cut). This is independent of
the 4096-row input profile. It is strictly a within-sender moment: transporting
the center from the sender's zero-count cut to the global rank cut still
requires the missing spatial alignment recurrence, so this bound alone does
not establish an `N^theta` global moment.

The strengthened local contract includes an aggregate count: for every threshold and every fixed physical sender output, at most 832 bits are on the wrong side of that sender's exact zero-count cut (`physical_twoGridRepair_wrong_population_le_832`). The same proof gives the per-bit 832-rank localization above. These are unconditional in the input height profile and row-preserving permutation, but remain sender-local; they do not bound how wrong-side mass aligns when multiple senders are partitioned and routed into the next stage.
