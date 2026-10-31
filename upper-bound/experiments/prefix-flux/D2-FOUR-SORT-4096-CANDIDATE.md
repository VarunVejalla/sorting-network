# D2 four-sort, 4096-row candidate

### New physical local-stage checkpoint (2026-10-28)

`D2ReflectedPhysicalPack.lean` now closes the row-orientation gap for the
fixed 4096-by-64 profile stage. It chooses row-dependent column scrambles
`sigma35(r)=shift35(reverse(r))` and
`sigma25(r)=lift35^{-1} * affine25(reverse(r))`. The resulting ordinary
`physicalPack2Net` has three actual vertical column sorts, and its semantic
height transition is exactly the existing full-height two-shuffle recurrence.
Appending `twoGridRepair` gives a genuine comparator network of depth at most
276 (`3*78+42`). For every Boolean input, the checked theorem gives monotone
output columns and a common row-major interval of at most 832 wires outside
which all output bits are false below and true above. The reflected pointwise
identities, recurrence, physical relabeling, and repair interfaces all
kernel-check. A cached local olean is under the ignored
`LLM-helpers/sub300-check/` directory.

This is a checked local stage, **not** an asymptotic sorting theorem. Its
832-wire exceptional interval is input- and threshold-dependent. A global
rank/address recurrence must explain how this uncertainty is composed across
stages and how it reaches a terminal exact sorter; the 276-layer local cost
cannot yet be converted into a limsup coefficient.

### Physical-profile transfer gate (2026-10-29)

The abstract clipped profile recurrence preserves a `512` error allowance
per output tile from parent error `512` plus fresh local error `448` per input
tile, when tile count doubles. However, `D2RowMajorFlowCuts` applies the `448`
provider to the semantic `fullHeightTwoShuffle` profile, whereas
`D2ReflectedPhysicalPack.reflectedPhysicalPack2Exec` identifies the actual
physical output with that profile followed by the row-preserving
`rowScrambleWirePerm2`. The two-grid repair restores column monotonicity and
preserves the resulting column counts; it does not undo that reindexing.
Therefore the `448` theorem is not yet the physical receiver-profile bound.
The next local theorem should bound the grouped exact-rank profile error for
the post-permutation column counts under the schedule's actual receiver cuts
by at most `512` per tile. The full `512` allowance is the numerical ceiling
for the doubled-budget recurrence, not an established bound. Even after this
local gate, the all-depth schedule-to-receiver map and terminal global order
remain open.

Status (2026-10-28): **the arbitrary-height dense output-area and 416 rectangular port-transfer providers remain kernel-checked. `D2Slope35Physical4096.lean` proves the full-height two-shuffle scalar recurrence using a semantic row reorientation. `D2ReflectedPhysicalPack.lean` now realizes that same recurrence with row-preserving shuffles and actual comparator networks, without a vertical wire reversal. `D2TwoGridPhysicalBand.lean` proves uniform exterior rows and band width at most 13 after any row-wise column permutation. `D2BandRepair4096Network.lean` defines the aligned and half-shifted 64-wire segment networks on the actual wires, proves each depth is at most 21 (total 42), and proves each segment's output is sorted. Their composition is kernel-checked to restore column monotonicity and yields one input-dependent row-major interval of at most 832 wires outside which each threshold output is sorted. The exact local height transition is also packaged as `d2LocalProfileStep`; Lean proves every positive iterate returns to the range-13 state space. The full-stage rank/profile invariant, dense global rank-transfer, and terminal seam criterion remain open.**

The reduced third-moment drift diagnostic is recorded in
[`D2-M3-REDUCED-GATE.md`](D2-M3-REDUCED-GATE.md). Its continuous two-row
relaxation admits no one-percent contraction; the exact integer version timed
out, so this neither refutes nor proves the fixed-core route.

## Cost point

Keep the sparse-bottom `(3,2,2)` D2 flow and use row height `m=4096`. Its
stage/log rate is `(x+y)/(x*z)=5/6`. A bitonic sort on 4096 wires has depth
`12*13/2=78`. Use one initial column sort and three row-scramble/column-sort
rounds, for four vertical sorts. This gives a baseline modeled depth of312 and
conditional coefficient

```text
312 * 5/6 = 260.
```

This leaves40 coefficient for additional asymptotic work. The intermediate
profile sorter formalized below has depth21 on a 64×64 tile; if needed in the
full-height stage, charging it gives `(312+21)*5/6=277.5`. That price is
conditional until the tile is integrated into the 4096-row construction. The
depth-100 exact
flow screen at this row height has 241 stages and 1,019,814 shared states; its
largest observed terminal native size is `2^21`, but an all-depth cleanup
bound remains to prove. Its minimum observed fringe is only
`28672/11691 ~= 2.45` rows, attained on a high-only mid sender. This is the
main provider obstacle: the existing F2 screens need substantially larger
fringes. The 4-sort core might permit a sharper small-fringe provider, but
none has been proved. The current reused F2 envelope illustrates the gap:
at support cap 18 and `n=8307`, the Lean-friendly closed certificate now
passes at `f=9` using a rational R1b tangent bracket; the unbracketed closed
envelope first passed at `f=11`. Selected points at `f=6,7,8` fail the exact
check. Thus this certificate family remains well above the observed
`2.45`-row gate.
These are screens of this envelope, not impossibility results for a different
local provider or for a profile-sensitive treatment of the boundary sender.

### Checked physical height transition

`D2Slope25BundleSort.lean` constructs a standard 4096-wire network by
transposing the existing 64-column bitonic sorter. Its depth is at most21, and
its action on each row is the standard ascending 64-wire network. On a
64×64 Boolean tile, the file formalizes a standalone stride-25 row shift,
column sorting, rowwise profile sorting, transpose/reflection, then stride39.
The resulting column counts equal the abstract recurrence exactly, and the
mass-40 nonincreasing-profile gate is kernel checked. This realizes that local
abstract recurrence physically. The current 4096-row D2 route uses a different
full-height shuffle (including a preceding stride-35 map); the tile lemma has
not been lifted or connected to that route. It therefore does not close the
full-height profile invariant, dense global rank-transfer, or terminal
contracts.

### Smaller-row extra-round tradeoff

A hypothetical five-sort core at row height `2048` has bitonic depth
`11*12/2=66` per sort, so its conditional coefficient is
`5*66*(5/6)=275`, worse than the 4096-row four-sort coefficient260. The
ordered-profile expectation recurrence after four scramble rounds gives
`0.00021980` of `m*n` (versus `0.00031594` after three rounds at 4096 rows),
but the depth-100 sparse-bottom flow screen has minimum fringe only
`14336/11691 ~= 1.226` rows and terminal native size at most `2^20`. Thus the
extra-round/smaller-row tradeoff improves the expected local error but worsens
the coefficient and the all-depth fringe gate; it is not a better candidate
without a new sub-row edge contract. The geometry result is reproduced by
`python d2_sparse_bottom_screen.py --depth 100 --row-bits 11 --params 3 2 2`.

The sparse edge check is also unfavorable for the simplest fixed scramble.
With four row-scramble rounds on64 columns and support cap18, the seed0 MILP
found an initial profile of total support18 whose terminal maximum column
height is3. Thus this core does not guarantee the needed `<=1` escapes at
fringe `1.226`. The solve hit its 120-second limit, but the incumbent is a
directly checked counterexample for seed0. This rejects that seed/core
instance, not all fixed scrambles. Reproduce from the repository root with
`python upper-bound/experiments/prefix-flux/d2_sparse_support_core_gate.py
--columns 64 --support 18 --rounds 4 --seeds 0 --time-limit 120`.

The same MILP screen supports explicit row-dependent cyclic scrambles: in
round `t`, row `r` sends column `c` to `c+a_t*r (mod 64)`. For multipliers
`(1,3,7)`, it found a support-18 profile with terminal maximum3; direct
re-evaluation confirms round maxima `(5,3,3,3)`. The initial nonzero heights
(1-based columns) are `4:1, 5:1, 46:3, 47:2, 48:1, 50:2, 51:1, 54:5,
58:1, 61:1`. The 120-second solve timed out before proving optimality, but
the incumbent is a verified counterexample to this cyclic design. This does
not rule out other row-permutation families. Reproduce with
`python upper-bound/experiments/prefix-flux/d2_sparse_support_core_gate.py
--columns 64 --support 18 --rounds 3 --time-limit 120
--cyclic-multipliers 1 3 7`.

### Targeted row-spread repair for the sparse edge

There is a deterministic way to meet the `<=2` edge gate without adding a
fifth 4096-wire sort. In the final row shuffle, replace the permutation on
the first and last40 rows by a 64-wire descending bitonic sort on each such
row, followed by row-dependent cyclic starts. Use
`L=(0,27,42,52,58,23,38,49,20,62,18,36,16,47,14,13,12,11,10,9,8,7,6,5,4,3,2,1,28,29,30,31,32,33,34,35,36,37,38,39)`:
map a top prefix by `c -> L_r+c` and a bottom zero suffix by
`c -> L_r+63-c`, modulo64. Keep the chosen row permutations on all other
rows and retain the final 4096-wire column sort. The 80 row sorters run in
parallel, so the added depth is21, and the
modeled coefficient becomes `(4*78+21)*(5/6)=277.5`.

At the input to this final shuffle, columns are sorted. If the one-sided
minority mass is at most40, its row counts form a nonincreasing partition of
at most40, so the support lies entirely in the repaired first (or last)40
rows. For ones at the top, each row sorter turns its ones into a prefix;
the cyclic starts distribute these intervals with maximum load2. The first
28 starts pack every profile of mass at most28 with load1. For zeros at the
bottom, the reflected map sends suffixes to the same intervals, giving the
same bounds. The exact enumerator checks all 215,308 partitions through mass
40 in both orientations; the pairwise certificate checks all 2,064 feasible
width cases for mass28. Reproduce the full profile gate with
`python upper-bound/experiments/prefix-flux/d2_sparse_row_spread_gate.py
--support 40 --packing --max-load 2` and use
`--support 28 --packing --max-load 1` for the zero-collision subgate. This
raises the finite sparse allowance from18 to40 while still meeting `<2.45`
as an integer escape allowance. Sorting80 edge rows instead of36 does not
change the 21-layer parallel row-sort depth; its effect on dense profiles
has only been sampled so far.

The earlier packed-screen area numbers are superseded: its bottom-row model
placed the one interval at the zero-packing offset, instead of at the
complementary interval required by the reflected zero-suffix permutation.
After correcting both full recomputation and incremental updates, the matched
`(1,35)` plus packed-49, 40-edge-row screen found `Aw=104.21875` (range8)
over64 starts x 50,000 steps. The corrected incremental update matched full
recomputation across 300 random mutations at each of three geometries. This
is still heuristic evidence, not a uniform area bound.

### Full-row cyclic repair rejected

Sorting every row in the final shuffle has the same21-layer depth as sorting
only the edge bands, so I screened the tempting full-row variant. The exact
monotone-profile DP in `d2_full_row_rotation_adversary.py` finds a valid
4096x64 input profile for row step41 whose output area is10,912, versus the
local `0.0085*m*n` target2,228.224. Its row widths are 410 rows of64, then25
rows of each width63 down to1, then2,111 zero rows; output column heights range
from1,166 to1,229. Thus the all-row version fails the universal local area
contract even though an eight-start hill climb reported area12. The former
edge-only area166 screen is superseded by the corrected bottom-row mapping
above. This is a genuine
input to the full-row final transformer, not a counterexample to the
edge-only candidate or a reachable trace of the complete scheduled network.
Reproduce with `python
upper-bound/experiments/prefix-flux/d2_full_row_rotation_adversary.py`.

This closes only the 4096-row sparse edge subgate. It does not establish the
full bulk-error or all-cut rank contract after modifying the final shuffle.
For the 2048-row/five-sort alternative, whose edge allowance is `<1.226`,
there is a stronger row-specific packing repair. Sort the first and last20
rows, then map top-row column `c` to `L_r+c` and bottom-row column `c` to
`L_r+63-c` modulo64, where
`L_0=0` and `L_r=sum_{k=1}^r floor(19/k)`. A nonincreasing row-width profile
of total mass at most20 has disjoint intervals under these maps: if rows
`i<j` are both nonempty, then
`(i+1)w_i+(j-i)w_j<=20` and `w_j>=1`, so
`w_i<=floor(19/(i+1))<=L_j-L_i`. Also
`max_{0<=r<20}(L_r+floor(20/(r+1)))=61`, so no wraparound occurs.
Reflection on bottom rows maps zero suffixes to the
same packed-prefix geometry. Exact enumeration checks all 2,714 partitions
through mass20 with maximum load1. Its modeled cost, including the 21-layer
row repair, is `(5*66+21)*(5/6)=292.5`. Reproduce with
`python upper-bound/experiments/prefix-flux/d2_sparse_row_spread_gate.py
--support 20 --row-count 2048 --max-load 1 --packing`. This improves on the
fixed-stride cap16 gate. The corresponding simple F2 screen at `n=8307`,
support16, still fails at `f=8` for `(g1,g2,c,b,J)=(2,4,2/5,1,1)`; this is a
parameter-point failure, not an impossibility result. The updated
40-row packed-schedule dense-profile hill climb tested64 starts on seed0 and found
area104.21875 (`0.000398` of `m*n`), below the `0.0085*m*n = 2228.224`
screening target. The analogous 2048-row four-round/20-row packing repair
hill climb found maximum area53 (`0.000404` of `m*n`) over64 starts on seed0,
below its `0.0085*m*n = 1114.112` target. These are heuristic screens only. The next
gate is a uniform area/rank-profile bound for a repaired core, then feeding
that profile into the coupled global recurrence. Until those pass, 277.5 and
292.5 are cost models, not sorting bounds.

### Improved sparse packing: 28 repaired rows, mass 28

The sparse allowance can be raised without changing the 292.5 cost: sort the
first and last 28 rows (the 64-wire row sorts still run in parallel at depth21)
and use cyclic starts
`(0,27,42,52,58,23,38,49,20,62,18,36,16,47,14,13,12,11,10,9,8,7,6,5,4,3,2,1)`.
Map top prefixes forward from each start and bottom suffixes backward from the
same starts. For any nonincreasing edge profile of total mass at most 28, rows
`i<j` with widths `u>=v>0` satisfy
`(i+1)u+(j-i)v<=28`. The exact integer checker verifies all 2,064 feasible
row-pair/width cases have disjoint cyclic intervals (minimum slack0 in both
directions). Thus all 28 repaired rows have maximum column load1 for every
such profile. After any preceding scramble and column sort, a binary input
with at most28 ones again has a nonincreasing height profile of total mass at
most28, so the final repaired shuffle and column sort send all those ones to
distinct columns. By complement, the reflected bottom repair handles at most28
zeros in the same way. Exhaustive enumeration independently checks all 18,460
profiles through mass28; mass29 first fails at `(28,1)` for these offsets.
This repairs the final-stage failure seen in the earlier un-repaired scramble
tests; it does not address dense profiles.
Reproduce the pairwise and profile checks with
`python upper-bound/experiments/prefix-flux/d2_sparse_row_spread_gate.py
--support 28 --packing --mass-cap 28` and use `--mass-cap 29` to see the first
failure. The 2048x64/four-round area hill climb with this repair found area51
over eight seed-0 starts (`0.0003891` of `m*n`); this remains a heuristic
dense-profile screen. The exact sparse-support-28 terminal gate is now closed
for this core, but the uniform dense-profile provider and global rank transfer
are still open.

## Fixed-core stress tests

`local_core_multiround_adversary.py` starts from arbitrary column heights
after the mandatory first sort, applies fixed independent row scrambles and
column sorts, then hill-climbs the initial heights. Its incremental update was
checked against full recomputation for all accepted/rejected moves in 8x4
examples with one to three rounds. These searches are heuristic, not maximum-
profile certificates.

For 4096 rows and 64 columns, the 2-round and 3-round runs use the same seed,
so the 3-round network adds one scramble-sort round to the identical first two
scrambles. Each run used64 random starts; the 3-round run also used100,000
annealing steps. The results are:

| seed | 2 rounds, 3 sorts | 3 rounds, 4 sorts | reduction |
|---:|---:|---:|---:|
| 0 | 1818 (`0.006935`) | 150 (`0.000572`) | `12.1x` |
| 1 | 2151 (`0.008205`) | 153 (`0.000584`) | `14.1x` |
| 2 | 1690 (`0.006447`) | 159 (`0.000607`) | `10.6x` |

Fractions are aggregate full-row defect divided by `m*n`. At 4096 rows and
256 columns, 12-start coordinate ascent found 3-round areas 488 and475 for
seeds0 and1 (fractions `0.000465` and `0.000453`); the matched 2-round
baselines were 2899 and2881 (about sixfold larger). A stronger 32-start,
20,000-step anneal gave 488 and522 for the 3-round seeds, with fractions
`0.000465` and `0.000498`. These remain input-profile searches, not universal
local bounds.

## Exact slope-profile bound for the cyclic 64-column core (2026-10-26)

For the fixed cyclic row shifts `(1,35,17)` modulo64, the last two rounds
already have a deterministic all-input range bound. After the slope-35 round,
remove the common full-row quotient and call the residual column heights
`y[d]` (`0<=y[d]<=64`). Comparing the contribution to columns `d` and
`d-35`, every source column contributes a nonpositive difference except the
unique source whose row index wraps from63 to0, which contributes at most1.
Hence

```text
y[d] - y[d-35] <= 1.
```

For the slope-17 round and an ordered output pair `(0,delta)`, the difference
is a sum of unary terms
`g_c(y[c]) = 1[(17^-1*(-c) mod64)<y[c]] -
1[(17^-1*(delta-c) mod64)<y[c]]`. Maximizing this sum over all integer
profiles satisfying only the displayed one-sided slope constraint is a
maximum-weight labeling problem on one 64-cycle. The exact max-plus recurrence
is

```text
F_next(t) = g_c(t) + max_{u >= t-1} F_previous(u),
```

with the cycle closed by the same constraint. The exact DP in
`d2_slope_profile_bound.py` checks every `delta=1,...,63`; its maximum is15
(at `delta=1,53`). Thus the exact finite calculation gives range at most15
for every profile after the slope-35 round, regardless of earlier input, and

```text
A_w / 64 <= 15^2/8 = 225/8 = 28.125.
```

The common quotient before the final shuffle contributes full rows of ones;
the remaining row phase only rotates the output columns, so it does not alter
range. The 4096-row schedule has period64, making the residual calculation
exact. The DP recurrence was checked against exhaustive profile enumeration
for `n=4` on two coprime slope pairs, and 100 random 4096-row profiles entering
the slope-35 round passed the decomposition, slope, and phase checks. This is
an exact integer computation, but the DP itself is not yet Lean-checked or
independently reviewed. The variance step is now kernel-checked in
`D2RankAlignment.lean`: `half_variance_le_range_sq_div_eight` proves the
general Popoviciu bound, and `half_variance_64_le_225_over_eight` derives
`A_w/64 <= 225/8` conditionally on the range-15 premise and exact mean.
`nat_half_variance_64_le_225_over_eight` obtains that mean from the conserved
total of a natural-valued column-height profile. The structural
`cyclic_successor_indicator_count_le` lemma also checks that a cyclic step of
row thresholds, with one wrap, can raise the hit count by at most one. This
is instantiated for the slope-35 row map by
`slope35_adjacent_height_difference_le_one`, proving the one-sided gradient
for the residual profile at every adjacent output pair. The physical
row-count bridge is also kernel checked: `residueHits64_eq`,
`slope35_row_destination_iff_residue`,
`slope35PhysicalOutputHeight_eq`, and
`slope35PhysicalOutputHeight_gradient` prove the exact quotient/residue
formula and one-sided gradient for arbitrary natural input heights, including
cancellation of the common full-cycle quotient. The final max-plus range
proof is still computational and unformalized.

This closes the uniform variance provider only for the width-64 cyclic core.
It does not prove a bound uniform in the number of columns: the same relaxed
last-two-round DP at width128 has maximum20 (at separation113), above the
range19 needed for `Gamma<=48`. That is a weakness of this relaxation, not a
counterexample to the full three-round core; a 96-start direct search at
width128 found range6 but is only heuristic. The D2 global alignment and
terminal rank-transfer gaps also remain open.

### Exhaustive slope-pair screen for the range-only relaxation (2026-10-26)

I exhaustively ran the same exact max-plus recurrence over all 32 odd choices
for the preceding cyclic slope and all 32 odd choices for the final slope
modulo64. Every pair has an optimal relaxed output range of at least13; the
minimum is13. The best examples include `(35,49)` and `(13,41)`, improving on
the earlier `(35,17)` value15, but none reaches the range11 sufficient for
the 2048-row alternative's dense-area budget `1114.112` via Popoviciu
(`64*R^2/8`). The scan is in `d2_slope_pair_screen.cpp`; its integer
recurrence agrees with the Python implementation on `(1,11)` and `(35,49)`.

I also summed the per-separation bounds instead of using only the maximum
range. For any output profile `x`,
`Aw = (1/(4*64))*sum_{i,j}(x[i]-x[j])^2`. Translation invariance lets the
exact DP bound each separation by `R[d]=max(M[d],M[64-d])`, where `M[d]` is
the maximum ordered difference from the DP. Exhaustive scanning of the same
1024 slope pairs gives the smallest certificate numerator
`sum_d R[d]^2 = 4659`, hence only `Aw <= 4659/4 = 1164.75`; this narrowly
exceeds `1114.112` for the 2048-row alternative. Crucially, it is below the
4096-row dense-core allowance `Aw<=2048` (and the full local target
`0.0085*4096*64=2228.224`). For the best pair `(previous,final)=(1,49)`,
the bound therefore clears the 4096-row dense-interior area gate, conditional
only on the one-sided-gradient lemma and the exact DP table. The maximizing
profiles for different separations need not coincide, so the actual area may
be smaller still.

The range-only threshold still rules out using this relaxation to prove the
2048-row area gate by Popoviciu alone. For the 4096-row core, the later
kernel-checked `(35,49)` provider gives `A_w <= 1352`, below its dense
allowance. This does not cover the low/high sparse fringe cases of the packed
repair, nor the all-cut/global rank and terminal obligations.

### Dual-certificate Lean check (2026-10-26)

For the `(35,49)` relaxed profile, an exact integer potential table was found
for each directed output separation `delta`. Each certificate has layer
potentials `p_i(h)` and nonnegative budgets `b_i`, with

```text
1 + out_0 - out_delta at layer i
  <= b_i + p_(i-1)(h_(i-1)) - p_i(h_i)
```

whenever the one-sided gradient permits `h_i <= h_(i-1)+1`; all 64 budget
sums are at most77. The LP only discovers the tables: Python rechecks the
rounded inequalities using integers. Lean then checks the suffix-minimum
recurrences and the local unary inequalities, one separation per generated
module. All 64 separation modules have passed. The generator, exact verifier and runner are
`d2_slope49_potential_cert.py`, `d2_slope49_emit_lean.py`, and
`check_d2_slope49_all.py`.

`D2Slope49Abstract.lean` proves that valid per-edge inequalities telescope
around the cycle and that the unary objective is exactly
`64 + out_0 - out_delta`. The generated Lean modules now check the
suffix-minimum recurrences, local unary inequalities, and table-to-edge bridge
for all 64 directed separations. `D2Slope49Provider.lean` imports that family
and proves, for every input profile with the slope-35 one-sided gradient, that
all final output heights differ by at most 13. It also derives the Popoviciu
bound `A_w/64 <= 169/8 = 21.125`.

The physical row-count bridge is now kernel-checked in
`D2Slope49Physical.lean`: the final slope-49 output is exactly the abstract
profile used by the certificates, and a 64-row band has output heights at
most 64. `D2Slope49Provider.slope35_then_slope49_area_per_column_le_169_over_eight`
composes this with the already checked slope-35 gradient. For the unmodified
cyclic 4096-row core this gives `A_w <= 1352`, below the dense-interior
allowance 2048. The packed final repair changes the row maps at both edges,
so this theorem does not yet cover the packed network; only the corrected
heuristic screen has been rerun there. The packed dense/sparse local provider,
all-depth rank-transfer and terminal exact-count obligations remain open.

I screened the same relaxation for another last-round pair, `(5,61)`, to test
whether the width64 result is a quirk of `(35,17)`. Its exact relaxed maxima
are15 at width64 and at least21 at width256 (the latter is attained by the
relaxed DP for separation200); width128's maximum is19. Thus this pair also
does not give the needed uniform `Gamma<=48` certificate from the one-sided
profile invariant. These are bounds on the relaxed profile class, not
counterexamples to the full multi-round core.

## Exact joint-profile toy gate

I generalized `aggregate_profile_union.py` to propagate the exact histogram
of column heights through any number of independent row-scramble/column-sort
rounds. This is a sufficient joint state for the randomized core: conditioned
on the current height histogram, each next row independently chooses a
uniform subset of its prescribed size, and the next column sort is determined
by the resulting heights. The union bound sums over every labeled initial
height profile, so a value below1 proves existence of one fixed sequence of
row scrambles that meets the bound for all binary inputs at that finite size.

At `m=8,n=4`, the 3-round core (four column sorts including the initial sort)
has exact union mass
`3803886291211556362489 / 3833759992447475122176 ~= 0.992208` at the bad
threshold `area >= 5`. Since this is below1, some fixed triple of row
scrambles has aggregate area at most4 for every one of the `9^4=6561`
initial height vectors. The 2-round core only certifies area at most8 at this
size (its bad-threshold union mass is about0.436). This is a real finite
existence result for the randomized toy core, but the margin is small and the
normalized guarantee `4/32=12.5%` is far from the 0.85% local budget needed by
the D2 route. It does not scale to 4096 rows or prove the seam-weighted port
contract. Exact Python propagation at this toy size takes roughly two
minutes, so a compiled implementation would help extend the finite screen;
the main obstacle remains deriving a strong n-uniform probability bound.

The transition also has a simple exact first-moment identity. If `c_r` is the
number of ones in input row `r`, `M=sum_r c_r`, and `H_j` is the output height
of column `j` after one scramble and column sort, then

```text
E[area(H)] = 1/2 * (sum_r c_r(n-c_r)/n - rem*(n-rem)/n),
rem = M mod n.
```

The `rem` term subtracts the unavoidable squared deviation of the most
balanced integer height vector from its real-valued mean. The exact transition
enumerator now checks this identity for every histogram state before doing the
multi-round propagation. It supplies a clean first-moment recurrence, but its
worst-case expectation alone is not strong enough to union-bound over all
initial profiles; the needed next result is a tail or higher-moment bound that
retains dependence between the column heights.

Combining the identity with Cauchy--Schwarz gives a uniform first-moment
recurrence for a fixed input under fresh independent scrambles. Let `A_t` be
the random area after round `t`, and let `rho` be the squared-deviation
correction for rounding the mean height to integers, so `0<=rho<=n/4` and
`sum_j(h_j-M/n)^2 = 2*A_t+rho`. Since
`sum_r c_r(n-c_r)=sum_{i<j}|h_i-h_j|`, one round satisfies

```text
E[A_(t+1) | h] <= sqrt((n-1)*(2*A_t+n/4)/8).
```

The right side is concave in `A_t`, so Jensen iterates this for unconditional
expectations. Using `A_0<=n*m^2/8`, at `m=4096,n=64` the resulting upper
bounds after rounds1,2,3 are respectively `0.175391`, `0.003247`, and
`0.000444` of the `m*n` area. Thus the *per-input expected* 3-round area is
comfortably below the `0.85%` target. This is a meaningful quantitative
signal for the four-sort core, but it does not yet produce one fixed network
that works for all inputs: the all-input union bound needs a tail stronger
than this first-moment estimate. The key next proof is a uniform concentration
bound for the random walk of nested row subsets `S_1 superset ... superset
S_m` under the independent row permutations, followed by the three-round
area transfer. This formulation captures the cross-row correlations
discarded by a scalar per-cut LP.

### Sharper ordered-profile first moment

The preceding Cauchy step can be tightened by using that the heights are
sorted. Write `h_1<=...<=h_n`, `mu=M/n`, and `S=sum_j(h_j-mu)^2=2*A+rho`.
The pairwise spread has the exact ordered form

```text
W = sum_{i<j}(h_j-h_i) = sum_i (2*i-n-1) h_i.
```

The coefficients sum to zero and their squared norm is
`sum_i(2*i-n-1)^2=n*(n^2-1)/3`. Therefore

```text
W^2 <= n*(n^2-1)*S/3,
Var(H_j) = W/n^2,
E[A_(t+1) | h] <= W/(2*n)
                  <= sqrt((n^2-1)*(2*A+n/4)/(12*n)).
```

This replaces the looser `sqrt((n-1)*(2*A+n/4)/8)` recurrence above. Both
right sides are concave in `A`, so either can be iterated by Jensen. Starting
from the same `A_0<=n*m^2/8`, the ordered-profile recurrence gives fractions
`0.144320`, `0.0024233`, and `0.00031595` of `m*n` after rounds1,2,3 at
`m=4096,n=64`; the previous recurrence gives `0.175390`, `0.0032465`, and
`0.00044372`. The sharpened mean is about29% lower after three rounds. It
still only bounds a per-input expectation; a tail uniform over all initial
height profiles is required to select one fixed core.
The exact identity and inequality were exhaustively checked on 3,418 sorted
profiles with `1<=m,n<=6`; reproduce the audit and recurrence table with
`python d2_ordered_profile_moment.py` from this directory.

### Conditional one-round tail from negative association

There is a more structured tail bound than bounded differences. In one
scramble, row `r` chooses a uniform `c_r`-subset of columns. Its indicator
vector is negatively associated; independent union over rows and coordinate-
wise summation preserve negative association. Thus the output heights `H_j`
are negatively associated and have the same Poisson-binomial marginal `X`,
with mean `mu=M/n` and summands `Bernoulli(c_r/n)`. These closure facts are
the standard negative-association properties for sampling without
replacement [Joag-Dev and Proschan](https://doi.org/10.1214/aos/1176346079).

Write `S=sum_j(H_j-mu)^2` and define
`M_+(u)=E exp(u*(X-mu)_+^2)` and
`M_-(u)=E exp(u*(mu-X)_+^2)`. The upper-tail factors are increasing functions
of `H_j`; the lower-tail factors are decreasing. Negative association and
Cauchy--Schwarz therefore give, for every `lambda>0`,

```text
E exp(lambda*S) <= [M_+(2*lambda)*M_-(2*lambda)]^(n/2),
P(area >= T | input profile h)
    <= inf_lambda exp(-lambda*(2*T+rho))
       * [M_+(2*lambda)*M_-(2*lambda)]^(n/2).
```

Here `rho = rem*(n-rem)/n`, where `rem=M mod n`, is the exact squared-
deviation correction for rounding the mean to integer heights. The event
`area >= T` implies `S >= 2*T+rho`, so retaining `rho` sharpens the Chernoff
exponent compared with dropping this nonnegative correction. This is an
explicit profile-dependent tail certificate: the `c_r` determine the
Poisson-binomial law, so different input profiles need not share a worst-case
variance bound. It applies to one scramble conditional on the complete
previous profile; iterating it over three rounds still requires summing over
reachable intermediate histograms or proving a compressed envelope. I have
not shown that its rate beats the all-profile entropy at the 4096x64 target.

The implementation and its toy audit are in
`aggregate_profile_union.py`. Running
`python upper-bound/experiments/prefix-flux/aggregate_profile_union.py --rows 3 --columns 3 --audit-na-tail`
checks the bound against all exact one-round transitions for the 20 possible
3-column histograms, at thresholds 1 and 2 (40 comparisons, with
`lambda=0.02`). This checks the numerical implementation and the inequality
on a toy instance; it does not certify the large-instance profile envelope.

For scale, Markov at the target `0.0085*m*n` gives only a per-profile failure
bound `0.000444/0.0085 ~= 0.0522`. The full union is over labeled height
vectors, `(m+1)^n`, whose logarithm is about532.35 at `m=4096,n=64`. There
are only `binom(m+n,n)` unlabeled histograms (log about327.67), but each
histogram represents multiple labeled inputs; its exact multiplicity must be
included in the union. The required concentration must exploit much more than
a small mean and sum profile-dependent rates with these multiplicities.

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/aggregate_profile_union.py --rows 8 --columns 4 --rounds 3
```

## Endpoint-profile reduction fails

I tested whether the all-profile union could be reduced to the `2^n`
endpoint profiles with every height in `{0,m}`. It cannot: for `m=n=3` and
three fixed scramble rounds generated with Python `random.Random(1)`, all
eight endpoint profiles have final area0, while the interior profile
`(0,1,2)` has area1 and final matrix
`[[1,0,1],[1,0,0],[0,0,0]]`. The row permutations (destination-to-source)
are

```text
[[[0,2,1],[0,1,2],[1,2,0]],
 [[0,1,2],[1,2,0],[2,1,0]],
 [[2,0,1],[1,0,2],[0,2,1]]].
```

So convexity/vertex reasoning cannot discard intermediate column heights for
a fixed core. The exact histogram union over all `(m+1)^n` profiles is doing
essential work; any scalable tail proof must account for this profile entropy
or establish a different structural reduction.

## Final-round conditional tail screen

For three representative inputs (half zero/half full columns, a linear ramp,
and alternating zero/full columns), fixed seed-0 first and second scrambles
produce intermediate areas579,614,632 at 4096x64. Applying the one-round
negative-association Chernoff formula to a fresh random final scramble gives
best-grid log tail bounds `-387.80`, `-409.56`, and `-398.12` at the target
area2229. These do not beat the full labeled-profile entropy532.35, even for
these individual intermediate states. This is only a screen: the two earlier
scramble probabilities have not been charged, and no uniform envelope over
all inputs or intermediate profiles is established. It shows that a final-
round-only union is insufficient here; the proof needs a joint three-round
path bound that combines the probability of reaching an intermediate profile
with its conditional final tail. Reproduce with
`python d2_final_round_tail_screen.py` from this directory.

## Tighter-local-error routing diagnostic

The ordered-profile D2 LP was rerun at depth4/two transitions, scale8192,
`(3,2,2)`, row-bits8, with root-tail initialization, ordered global profiles,
and every active row cut. Giving both aggregate and seam defects a common
fraction `epsilon` produces optimal relaxed terminal wrong mass about
`3.3624e6*epsilon`: 3,362 at `epsilon=1/1000`, 336 at `1/10000`, and exactly
zero at `epsilon=0`. The residual at the positive caps is cross-bag alignment
after local bags are sorted. This is a fractional relaxation, not a network
counterexample or a calibrated bound for the 4096-row core. It says this
two-transition contract reaches terminal purity only in the zero-error limit;
a positive local budget needs a priced cleanup stage or a stronger coupled
rank invariant. An optimistic exact local refresh at the intermediate
snapshot (`--exact-refresh-stage 1`) removes within-bag defect there but still
leaves about3,050 terminal wrong keys; it does not restore cross-bag rank
alignment. Stage2 is the terminal snapshot and has no active local outputs,
so `--exact-refresh-stage 2` adds no constraints and is not a terminal-cleanup
test. Reproduce with `coupled_rank_lp.py --depth 4 --scale 8192
--threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride
1 --aggregate-defect-fraction EPS --seam-defect-fraction EPS --params 3 2 2
--row-bits 8 --time-limit 120`, substituting `EPS` with `1/1000`, `1/10000`,
or `0`; add `--exact-refresh-stage 1` for the intermediate-refresh screen.

## Next gate

Prove or disprove a local provider for this exact 4-sort core at the reachable
ragged D2 rectangles, especially fringe widths near2--3 rows. The provider
must give the seam-weighted port defects needed by the global recurrence, not
only the full-row aggregate measured here. Then rerun the integer coupled
rank-transfer adversary with those actual bounds. If the provider needs more
than40 extra coefficient, this cost point no longer meets300.

Reproduce the 64-column search with:

```text
python upper-bound/experiments/prefix-flux/local_core_multiround_adversary.py --rows 4096 --columns 64 --rounds 3 --seeds 0 1 2 --restarts 64 --anneal-steps 100000
```

## Reduced-grid all-cut LP screen for the packed 2048-row candidate

I also ran the coupled rank LP at depth4, scale2048, row-bits8 (256 row-cut
grid), with ordered-prefix, root-tail, all-row-dominance, and both aggregate
and seam defect caps set to `10109/25000000` (about0.00040436). HiGHS solved
this fractional relaxation to optimality: 14,346 variables, including 650
piecewise binary selectors, and nine aggregate-defect constraints. The
solution has terminal cross-bag alignment about301.36 keys, within-bag defect
about1,366.00, and global-prefix defect about1,667.36; the reported scalar
terminal purity count is63 bad blocks. This establishes that these scalar
aggregate-plus-seam caps do not imply the terminal exact-count contract at
this grid and scale. It is not a counterexample to the fixed sorting network:
the LP is a relaxation, row-bits8 is a reduced grid, and no integral network
trace was produced. The full row-bits11 model did not finish within its time
limit, so it supplies no verdict. Do not use the LP objective value alone as
a concrete number of wrong keys; use the decoded stage trace and terminal
purity diagnostic.

An integral MILP rerun with the same parameters reached the 120-second limit
without proving optimality, but returned a fully feasible integral witness:
334 terminal wrong keys across 63 bad blocks, with zero equality, inequality,
bound, and integrality residuals. The duality gap was about1.45e-6 relative to
the solver objective. This rules out fractional interpolation as the sole
cause of failure for this reduced-grid interface. It remains an abstract
selected-cut adversary, not a trace of the fixed comparator network, and the
MILP's nonoptimal status must be retained.

Reproduce with `coupled_rank_lp.py --depth 4 --scale 2048 --threshold 1/3
--ordered-prefix --root-tail --all-row-dominance --row-stride 1
--aggregate-defect-fraction 0.00040436 --seam-defect-fraction 0.00040436
--params 3 2 2 --row-bits 8 --integer --time-limit 120`.

### Actual packed final-layer dense screen

`d2_packed_final_core_screen.py` runs cyclic slopes `(1,5,25)`, then packs the first and last28 rows using the support-28 schedule above, with slope61 in the middle. Incremental updates matched full recomputation on 500 accepted random moves at 64 rows and 100 at 2048 rows. At 2048 rows, 24 starts x 20,000 moves found `Aw=43.9922` (`Aw/64=0.68738`, output range5); 64 starts x 50,000 moves found `Aw=49.96875` (`Aw/64=0.78076`, range6). These are heuristic adversarial witnesses, not a worst-case upper bound. They show the exact packed repair retains the low observed dense-profile error of the cyclic candidate; the uniform local provider and global rank transfer remain unproved.

### Exact interior equivalence for the packed last layer

After any cyclic round on 2048 rows and 64 columns, each output height is
`Q+R_c`, where `Q` is common to all columns and `0<=R_c<=64`; hence the
height range is at most64. In the support-28 final layer, if every input
column height to that layer lies in `[28,2020]`, rows0--27 are completely full
and rows2020--2047 are empty. The packed top rows therefore contribute exactly
28 wires to every output column, the bottom rows contribute none, and the
middle rows use slope61 exactly as in the unmodified cyclic layer. Thus the
packed and cyclic outputs agree exactly in this interior case. If the interior
condition fails, the range-64 fact implies either every height is at most91,
or every height is at least1957. By mass conservation, these exceptional
cases have at most5824 ones or at most5824 zeros, respectively. This reduces
the packed-vs-cyclic analysis to a dense interior and two absolute sparse-mass
fringes; it does not yet bound either fringe's output area.

The dense interior would be certified by a uniform cyclic output range at most
11, since the range-variance inequality then gives `Aw <= 968`, below the
1114.112 local area budget. I added the translation-normalized exact query to
`d2_cyclic_range_bv.py`; its 64-column QF_BV instance for any separation at
least12 timed out at120s. Width8 sanity witnesses pass, but this supplies no
64-column verdict and the uniform dense provider remains open.

### 4096-row dense-core gate

For the 40-row packed edge repair, the same range argument gives exact
agreement with the cyclic last round in the interior `[40,4056]`. Any failure
of that condition forces at most6592 minority wires in the whole bag. I tested
the natural three-round slope sequence `(1,5,41)` with the exact endpoint
QF_BV gate; range at least17 (the negation of the sufficient range-16 bound
`Aw<=2048`) timed out at120s. This is not a verdict on the candidate. It does
show the 4096-row/277.5-cost alternative has the same open dense-provider
gate, alongside its low/high fringe case.

### Packed interval-row toy screen — not a bound for the fixed core (2026-10-26)

`d2_packed_width_dp.cpp` exhaustively optimizes a restricted interval-row
model. Its edge-row intervals are valid because the added edge row sort packs
ones into prefixes, but it also represents every middle-row active set as a
cyclic interval of width `w`. The fixed core does not sort middle rows: their
active sets are `{c | h[c] > r}` and can be arbitrary subsets. The one-sided
gradient `h[i] <= h[i-1] + 1` does not imply interval superlevel sets. Thus the
reported range28, pairwise area bound6240.5, witness area1242.88, and the
reverse/rotate experiments are results for a toy restriction, not bounds or
counterexamples for the fixed network. Do not use this screen to certify its
dense gate.

The corrected local problem must retain the actual height vector through the
unmodified middle rows, while applying prefix packing only to the first and
last40 rows. The separate `d2_packed_final_core_screen.py` does simulate this
fixed network, but its hill-climb values remain heuristic. A uniform bound for
that arbitrary-subset transition is still open.

As a corrected low-fringe gate, `d2_packed_reachable_range_milp.py` models
arbitrary height profiles `h[i] <= 103` with the one-sided slope-35 condition,
sorts and packs only rows0--39, and preserves the actual subsets in rows40--102
under slope49. For the fixed output pair `(40,12)`, the LP relaxation has
optimum45.91. The integer solve timed out at120s with incumbent difference7
and dual upper bound41, so it is inconclusive and far too weak for a range-16
certificate. It models the correct row behavior for this low-fringe slice; it
does not cover the high fringe, certify area, or prove a full-core bound.
Reproduce with
`python upper-bound/experiments/prefix-flux/d2_packed_reachable_range_milp.py
--pair 40 12 --height-cap 103 --time-limit 120`.

The corrected full-core heuristic (`d2_packed_final_core_screen.py`) was also
extended to 64 starts x 100,000 steps at `(1,35)` plus packed49 on 4096 rows.
It again found `Aw=104.21875` and output range8. This is an actual-network
witness screen only, not a worst-case bound.

To test whether the slope-35 one-sided invariant alone might suffice, I also
searched directly over all profiles in the low-fringe superset `h<=103` that
satisfy `h[i]<=h[i-1]+1`. The correct arbitrary-subset transition evaluator
found a valid profile with `Aw=1429.9921875` and output range25 after64 starts
x100,000 moves; a second run with128 starts x200,000 moves found maximum
`Aw=1332.2421875`. The profile class is a superset of the reachable inputs,
and both witnesses remain below the2048 allowance, so these are promising
screens but not a uniform bound. Incremental updates matched full transition
recomputation on2,000 accepted random moves.

Two exact optimization attempts remain inconclusive. The corrected pair-range
MILP for low profiles timed out with pair `(40,12)` incumbent7 and dual bound41
after120s. An exact binary-product MILP for the full quadratic area over the
gradient superset timed out after120s without a primal solution (11,100
variables,13,548 constraints). The next mathematical target is a certificate
for `Aw<=2048` on this gradient class, or a tighter reachable-state
description that makes such a certificate tractable.

The `Aw=1429.99` gradient-class witness is not reachable from a slope-1
shuffle followed by slope35: `d2_slope35_preimage_gate.py` encodes a possible
slope-1 output as a one-sided-gradient source and asks for the exact target
after slope35. HiGHS proves this fixed-profile feasibility model infeasible
(4,096 binary variables,4,160 constraints). This confirms that the full
`(1,35,packed49)` reachable set is substantially smaller than the gradient
superset; the result is a solver screen, not a kernel-checked theorem.

I encoded that low-fringe reachable set directly in
`d2_packed_reachable_core_range_milp.py`: input residues, both cyclic shuffles,
their common quotient/carries, the packed first40 rows, and unsorted middle
rows. The exact range MILP has17,732 variables and17,731 constraints but
found no incumbent in120s; the fixed-pair version also timed out without a
primal point. Its LP relaxation for pair `(40,12)` gives only45.91. The model
captures the right local composition, but needs a stronger formulation or a
mathematical invariant to produce a useful certificate.


### Slope-25 unmodified core: dense provider and support-40 sparse gate (2026-10-26)

The last two cyclic scrambles can use slopes `(35,25)` instead of `(35,49)`.
The inverse of25 modulo64 is41. I emitted a separate exact dual-potential family
for all64 directed output separations, rechecked its integer edge inequalities
in Python, and kernel-checked every Lean certificate module. The aggregate
`D2Slope25Provider.lean` compiles and proves that for a single 64-row residual
profile after slope35, physical slope25 yields output-column height range at
most13; Popoviciu gives `A_w/64 <= 169/8`, or `A_w <= 1352` over64 columns.
This is below the per-profile dense allowance2048. The physical shuffle bridge
`D2Slope25Physical.lean` also compiles. However, the 4096-row network starts
with arbitrary heights up to4096. The phase lift is now kernel-checked:
`D2Slope25Lift.lean` proves the slope35 quotient/residue decomposition and the
slope25 uniform-shift identity; `D2Slope25LiftProvider.lean` composes these with
the residual certificate to prove output range at most13 for every 4096-row
input-height profile. `D2Slope25LiftArea.lean` transfers the residual
variance certificate through the common offset and destination permutation,
proving the full physical quadratic-area bound `A_w <= 1352` for arbitrary
4096-row input-height profiles. For source heights bounded by4096, it also
proves the output-capacity bound and an aggregate `l1` port-deviation bound
of416 over every complete per-column interval partition. The new
`D2Slope35Physical4096.lean` theorem `fullHeightTwoShuffle_physical` now
proves an exact matrix-level implementation of this two-shuffle profile and
its two column sorts for every bounded input-height vector. This closes the
full-height arithmetic-to-network bridge for that local two-round core. The
two-grid replacement network is now kernel-checked locally, including its
composition with the range-13 profile after any row-preserving permutation.
What remains open is inserting and pricing that network in the actual recursive
schedule, proving the all-depth rank/alignment transfer, exact terminal cleanup,
and completing the global sorting construction.

The unmodified final slope25 also passes the exact sparse support-40 gate:
`first_failure(40,64,25,4096,2,False)` exhausts215,308 sorted edge profiles
(top and reflected bottom) and finds maximum output load2 on each side, with
no failure through total mass40. This supports the fringe contract for the
unmodified cyclic core, although this Python enumeration has not yet been
ported to Lean.

A useful compressed proof target for that gate is now identified. If rows
`i<j<k` all hit one output column `c`, put
`d_r=(c-25r mod64)`. The nonincreasing input row widths must be at least
`1+max(d_i,d_j,d_k)` through row `i`, at least `1+max(d_j,d_k)` through row
`j`, and at least `1+d_k` through row `k`. Thus support is at least

```text
(i+1)(1+max(d_i,d_j,d_k))
+ (j-i)(1+max(d_j,d_k)) + (k-j)(1+d_k).
```

Exact enumeration over `c<64` and `i<j<k<40` gives minimum41, attained at
`c=13`, `(i,j,k)=(0,3,21)`, with required widths `(14,3,1)`. Therefore no
support-40 profile can load any output column three times. This reduces the
sparse provider to a bounded arithmetic certificate, but the exhaustive
finite check has not yet been kernel-certified.

The local sequence `(1,35,25)` retains the four-sort 4096-wire stage price
`4*78*(5/6)=260`. The sparse edge screen is closed for this sequence; the
dense provider still needs the full-height phase-lift lemma. The all-depth
rank/alignment transfer, exact terminal cleanup, and bridge from this stage to
the full sorting construction also remain unproved. The exact pairwise DP screen reports a
potentially tighter `A_w<=1230.25` for `(35,25)`, but that sum-of-squared-pair
bound has not been kernel-checked and is not used above.

Reproduce the sparse gate with:

```text
python -c "import runpy; m=runpy.run_path('upper-bound/experiments/prefix-flux/d2_sparse_row_spread_gate.py'); print(m['first_failure'](40,64,25,4096,2,False))"
```

The Lean artifacts and certificate pipeline are `D2Slope25Abstract.lean`,
`D2Slope25Physical.lean`, `D2Slope25Certificate00.lean` through
`D2Slope25Certificate63.lean`, `D2Slope25Provider.lean`, and the corresponding
`d2_slope25_*` emit/check scripts. All64 certificate checks and the aggregate
provider compile passed with `lake env lean`.

### Reordered three-round candidate `(25,25,35)`

There is a candidate with the same four-sort cost260 that addresses the sparse
support-40 boundary more strongly. Use row slopes `(25,25,35)` after the
initial column sort. Exact enumeration of all215,308 nonincreasing profiles of
mass at most40 shows that the first two slope-25 rounds leave maximum column
load1, for both top ones and reflected bottom zeros. The last slope-35 round
preserves that property: a column-sorted profile of load at most1 has a single
occupied edge row, and that row's cyclic permutation is a bijection.
Reproduce the two-pass gate with
`python d2_sparse_row_spread_gate.py --support 40 --row-step 25
--second-step 25 --max-load 1` from `prefix-flux/`.
The exact gate is tight at support41: the same enumerator finds profile
`(14,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1)`, whose final top and
reflected bottom peaks are both2. Thus this particular schedule has a precise
sparse threshold, rather than a monotone claim extending beyond40.

There is a shorter proof target than enumerating all215,308 profiles. If a
first-pass column were hit by rows `i < j < k`, monotonicity forces mass at
least `(i+1)A + (j-i)B + (k-j)c`, where `A=max(a,b,c)`,
`B=max(b,c)`, and `a,b,c` are the forward interval lengths from those three
row starts to the hit column. Translation removes `i`; minimizing over the
two gaps and the target gives41, attained at gaps `(3,18)` and target13.
So any top profile of mass at most40 has first-pass column height at most2.
For the second pass, if two intervals hit one column, their distinct starts
must be the two adjacent positions `x-1,x`. Under stride25 the row-gap is
then41 or23. Monotonicity forces total mass at least43 or48, respectively,
contradicting40. This proves the second-pass load-one claim from just
`max(height)≤2` and `mass≤40`. The exact first-pass minimization is now
reproducible with
`python d2_sparse_row_spread_gate.py --triple-mass-gate --row-step 25`; it
checks124,992 gap/target cases and returns the tight mass41 witness above.
Across all admissible gap pairs, that screen found the minimum at one of the
three row starts every time. Lean now checks the whole sparse profile gate in
`D2Slope25Sparse40.lean`. `slope25_first_pass_max_load_le_two` proves the
first rotation has load at most2 in each column for every nonincreasing input
profile of mass≤40. `slope25_second_pass_max_load_le_one` proves that a second
stride-25 rotation has load at most1 when its input is again nonincreasing,
has mass≤40, and has maximum height≤2. These use the mass-41 triple bound,
interval-sum accounting, and the checked modular gaps41 and23. The new
`slope25Load_sum_eq_profile_sum` proves exact first-rotation mass conservation
by summing the cyclic-distance indicators. A standard ascending bitonic sort
followed by stride39 also passes the exact sparse gate. Reproduce the
top-and-bottom exhaustive screen with
`python d2_sparse_row_spread_gate.py --support 40 --row-step 25
--second-step 39 --max-load 1 --ascending-sort`; it checks all215,308
nonincreasing profiles of mass≤40 with no collision. Lean proves the all-profile result in
`slope25_then_ascending_sort_stride39_no_collision`, using row reflection to
reduce the increasing sorted profile to the existing decreasing-profile gate.
This removes the dual-order comparator issue.

`D2Slope25BundleSort.lean` constructs the flattened 4096-wire row-parallel
sorter by transposing and relabeling the existing column-sort network. The
result uses standard comparators, has depth at most21, and its wire-level
execution is the 64-wire bitonic network independently on each row. The unary
prefix and suffix lemmas identify its scalar height action. This makes the
scalar height-sort component physically realizable with a standard network.
If inserted in the four-sort schedule, its 21-layer overhead gives the
conditional cost already budgeted as `(4*78+21)*(5/6)=277.5`. Both
`D2Slope25Sparse40.lean` and `D2Slope25BundleSort.lean` pass focused Lean
checks in `runaware`. Remaining work is to connect the preceding physical
column sort and row shuffle to the sparse profile interface, then close the
dense/full-height provider and global rank-transfer and terminal cleanup.
The full-height physical lift and global rank-transfer and cleanup steps
remain open.

The dense 64-row residue gate also looks favorable. The exact integer DP
`d2_slope_profile_bound.py --previous-slope 25 --final-slope 35` bounds every
ordered output-height difference by13, assuming only the one-sided gradient
condition supplied by the preceding slope-25 round. Popoviciu then gives the
same centered area allowance1352 on these residue profiles. A full-height
4096-row quotient lift for this reordered pair remains to be proved. The
integer dual-certificate generator verified all64 separations for `(25,35)`
with worst budget77; its JSON is in ignored `LLM-helpers/` as
`d2_slope25_35_potentials.json`.
Reproduce it with `python -u d2_slope49_potential_cert.py
--previous-slope 25 --final-slope 35 --output
LLM-helpers/d2_slope25_35_potentials.json` from the repository root.

This is a promising local-core replacement, not yet a Lean provider. The
`(25,35)` abstract module and certificate sources have now been generated; the
abstract module and certificates 00 and 07 compile in the `runaware` Lake
package. Certificate 07 has the worst total dual budget (77). These checks
caught and fixed an old-namespace reference in the certificate emitter. The
other 62 certificate modules have not yet been kernel-checked, and there is no
`(25,35)` physical/full-height quotient lift or aggregate provider.
The two-pass sparse enumeration is still a Python screen. The global
rank-transfer and terminal long-distance cleanup gaps are unchanged.

## Cost compatibility warning

The tempting arithmetic `(312+42)*(5/6) = 295` combines the four-sort schedule's 312-layer baseline with the 42-layer two-grid repair proved for the
separate two-shuffle physical core. The current sources do not establish that
the four-sort candidate has the range-13 input profile required by this
repair, so 295 is not yet the price of one proved macro. Keep the routes
separate until that profile and network interface are connected.

## Physical D2 profile transfer update (2026-10-29)

`D2PhysicalProfileMass.lean` proves that the row-preserving reindex leaves each
tile's total key mass unchanged and extends the physical 448 exact-rank error
provider from full row partitions to the clipped partial-row cuts used by the
flow. `D2PhysicalFlowProfileTransfer.lean` then proves the grouped global
profile recurrence for the actual post-permutation, two-grid repaired profile:
parent error plus 448 per input tile, hence the 512-per-output-tile allowance
when tile count doubles. Receiver tags are arbitrary in this theorem. The
remaining bridge is to identify the schedule's actual wire-to-receiver tags,
next-tile column profiles, root state, and terminal sorting criterion; no
limsup coefficient follows until those all-depth interfaces and depth charges
are proved.

The balanced-profile consequence is now kernel checked in
`D2BalancedPrefixProfile.lean` and `D2RankProfileRouting.lean`: if actual and
ideal destination profiles have equal total mass, an l1 error of `448` bounds
the leakage in either direction across any union of destination cells by
`224`. At the `(3,3,2)` ordinary half-port margins (`480` for mid/botDesc,
`512` for topRise), this leaves `256` or `288` wires of local slack. This is a
usable one-sided local reserve once the actual destination cells are
identified; it does not establish the parent tile-mass hypothesis or the
global schedule tag map above.

### Correction: local D2 port tags already have a rank-interval adapter (2026-10-29)

The preceding paragraph overstates the missing local port-tag bridge.
`D2FlowRankBridge.lean` proves `d2FlowStage_regular_sender_rank_ports_cover`:
under the ordinary cut hypotheses, one sender's live wire set is partitioned
by its two parent half-ports and eight child down-ports, with widths given by
the actual post-stage child-root deficits. Receiver identity is explicit at
this one-sender, local-rank level.

The unresolved step is global rank. These intervals use rank within the
sender's live set; the 448 profile transfer compares a threshold profile
against exact rank within a tile. Neither theorem proves that sender address
order tracks global sorted rank, or that the clipped tile boundaries in
`D2PhysicalFlowProfileTransfer.lean` are the actual globally ranked packets.
`D2PhysicalSenderRankDisplacement.lean` supplies a possible adapter, but its
error is multiplied by 3455 times the sender's address-gap bound, and no
useful schedule-wide gap bound is established. The blocker is therefore a
global rank/alignment invariant connecting local packet partitions to the
all-depth profile recurrence. Root initialization, terminal cleanup, and
depth accounting also remain open.

### Fixed-core absolute port-seam bound (2026-10-29)

D2RankCutSeamBound.lean now proves rankCut_crossers_le: if each output slot's
rank within its sender is within C of that slot, at most 2*C+1 slots cross
any one rank cut, independently of sender width. Composing with
D2LocalRankDisplacement.localCore_rank_displacement gives at most 1665
crossers at each cut. localCore_actual_d2_sender_seams_le instantiates the
nine cumulative boundaries of an ordinary D2 sender, so the fixed macro has
at most 14985 slot/cut crossings per sender over its two parent half-ports
and eight child ports. The focused Lean check passes.

This replaces a relative-per-sender seam allowance by an absolute local
crossing count. It is not yet a global rank or inversion bound: the proof
counts rank-cut crossers before translation through the sender's static
address runs. One possible translation uses
D2StaticWireSets.destinationPiece_staticHoleList_child_inter_cell, but
charging each crossing by raw hole length is too costly in the finite
schedule screen below. The goal is a receiver-label or spatial-potential
transfer that composes with the all-depth recurrence.

The label-counting bridge is now formalized in the same module:
`portLabel_mismatches_le_crossers` bounds the number of slots whose port label
differs between physical slot and sender-rank by the sum of seam-crossing
incidences. Its D2 specialization,
`localCore_actual_d2_sender_port_mismatches_le`, therefore gives an absolute
14,985 mislabelled-slot bound for the nine ordinary sender seams. This avoids
charging full address-hole lengths for the local receiver-profile mismatch.
It still assumes the physical destination label is described by these ordered
sender-slot cuts; the static address-run to actual next-stage receiver map and
the all-depth parent-profile recurrence have not yet been composed.

The finite diagnostic `d2_absolute_seam_screen.py` shows why that direct
translation is unlikely to close as stated: the sum of internal static-hole
lengths over active sender occurrences is `282.33 N` by depth 30, and
`3567.67 N` by depth 100. These finite values grow roughly quadratically with
depth. Charging each seam crosser by the full physical hole length would
therefore give an `O(N log^2 n)` aggregate allowance, too weak for the current
terminal argument. A useful next theorem must charge receiver-label changes
or a spatial potential directly, rather than raw address distance. This is a
screen, not an all-depth asymptotic estimate.

### Variable sender-cut family transfer (2026-10-29)

`D2VariableTilePhysicalFlowTransfer.lean` now kernel-checks the grouped
physical-profile recurrence when each input tile has its own monotone rank
cuts and destination tags. It proves receiver error `<= parentError + 448 *
inputTiles`, and hence preserves the 512-per-output-tile budget whenever the
output tile count doubles. This removes the previous interface restriction
that unrelated senders share one global cut map. Focused direct Lean check
passed using the cached D2 dependency chain.

The theorem is still an abstract transfer interface: no theorem yet assigns
each actual scheduled wire to one of its tile/column/port cells and proves
that the resulting tag is the next-stage receiver. In particular, the local
sender rank partition in `D2FlowRankBridge.lean` has not been composed with
the physical tile placement/static-hole map. That schedule-to-physical-tag
map remains the next necessary bridge before this recurrence can be iterated
from a root state.

Follow-up: `D2VariableTilePhysicalFlowTransfer.lean` now also proves
`d2FlowStage_regular_sender_boundary_valid` and
`d2FlowStage_regular_sender_port_length`. The first packages the actual
ordinary-stage conservation equation as a monotone ten-port boundary on an
arbitrary sender set of the correct cardinality. The second gives the exact
length of every adjacent port interval: quota/2 at each end and the actual
child deficit reduction in the middle. Both pass a focused kernel check.
This sharpens the rank-side input to the missing placement bridge, but still
does not identify any physical comparator output with a receiver tag.

### 4096-grid alignment screen (2026-10-29)

`d2_port_cell_alignment_audit.py` now expands each active sender's exact
rank-port slices through its ordered static address runs, then checks that
the resulting pieces partition all of `[0,N)` and that every piece endpoint
is divisible by 4096. For `(3,3,2)`, scale 8192, this passes at depths 7, 8,
and 9, at every stage. The depth-9 audit covers `N=2^40` using 589,824
sender-port pieces at its largest stage. Thus each 4096-address physical
column lies wholly in a single port piece in these finite instances.

This suggests replacing the address-gap displacement adapter with an
all-depth grid-divisibility theorem: prove every static hole endpoint and
every actual sender rank-port boundary lies on the 4096 grid. The arithmetic
appears plausible because native scales and the ordinary quota formulas
have large powers of two; however, recursive whole-up (`botRise`) allocations
must also preserve the half-quota grid. The audit is exploratory evidence,
not a proof of divisibility or of the comparator output's receiver label.
If the induction closes, each physical column can receive one exact port
tag, giving the 448 profile theorem the schedule's actual cuts without
paying a raw static-hole length.

The transfer interface has now been generalized accordingly:
`variable_column_physical_profile_error_le_parent_add_448` allows separate
monotone port cuts in every column and keeps the same `parentError + 448 *
tiles` bound; `variable_column_physical_profile_error_le_next_budget` closes
the 512-per-output-tile recurrence when tile count doubles. Both kernel-check.
The finite audit confirms the needed single-port-per-column condition, but
the all-depth proof that static hole endpoints and sender port boundaries
stay on the 4096 grid is still open. The audit also finds port-index descents
within some tiles, so the earlier shared tile-wide-cut interface cannot be
used directly; the new columnwise interface removes that extra restriction.

### Sender-boundary divisibility bridge (2026-10-29)

`D2VariableTilePhysicalFlowTransfer.lean` now proves a parameterized arithmetic
bridge: if an ordinary sender's child deficits are on an `m`-grid, its quota
half is on that grid, and the stage's child deficits remain on that grid, then
all eleven cumulative rank-port boundaries are on the same grid. A second
kernel-checked theorem packages this for actual aligned D2 trees, converting
the child-tree grid facts and an active quota divisible by 8192 into 4096-grid
port boundaries. More strongly, `d2FlowStage_sender_boundary_dvd_all`
inducts over the recursive tree and proves the port-grid claim at every active
ordinary node, using the exact local reserve contract
`d2FlowStageInvInputs`. The candidate wrapper uses the all-stage endpoint and
quota-alignment theorems, so its only remaining flow hypotheses are that
`d2FlowTreeInv` and `d2FlowStageInvInputs` hold at each stage. The latter is
the unsolved global schedule/reserve gate. The physical placement theorem
matching each 4096-address column to its rank-port piece remains open too.
The arbitrary-column-cut `+448` transfer is also kernel-checked.
Focused check: direct Lean compilation of `D2CutAlignment.lean` and
`D2VariableTilePhysicalFlowTransfer.lean` succeeds.

The same module now proves the address-side endpoint arithmetic. Under an
ordinary sender's 8192-divisible quota and 4096-aligned parent origin, child
width, and parent fronts, `d2FlowStage_ordinary_staticHoleList_endpoints_dvd`
shows every actual child-hole endpoint is 4096-aligned. Generic lemmas carry
grid alignment from holes to their complementary static runs and identify
those runs with `staticGapRuns`. Thus the hole/run side of whole-column
placement has a formal interface; connecting every run's rank slices to the
ten actual port intervals remains open.

The rank-slice interface is now explicit as well. `orderedRunSliceInCell_grid_uniform`
proves that any ordered list of 4096-aligned static intervals, cut at 4096-aligned
cumulative ranks, intersects a physical 4096-cell either fully or not at all.
`staticGapRuns_rankSlice_wholeCell` specializes this to the actual fitted
complementary runs. The endpoint and rank-grid premises are theorem-level inputs;
the all-stage invariant and the physical comparator-to-port labeling still have
to establish and compose them. The focused direct Lean check passes.

### Physical profile range (2026-10-29)

`D2ReflectedPhysicalPack.lean` now proves
`reflectedPhysicalPackTwoGrid_columnCount_range_le_13`: after the actual
row-dependent permutation and two-grid repair, any two output columns differ
in true-count by at most 13. The proof uses the existing common-band theorem
(at most 832 consecutive row-major wires) and column monotonicity, so it
applies to the physical network rather than only the semantic height recurrence.
This is the key local input for recovering the 448 exact-rank l1 allowance
physically: the exact rank profile has range at most one, the physical output
profile has range at most 13, and both have the same total mass.

The zero-sum estimate is now kernel-checked as
`sum_abs_int_le_448_of_zero_sum_range14`, using a second-moment interval
bound and Cauchy-Schwarz. New `D2PhysicalProfileRangeTransfer.lean` composes it
with the physical range-13 theorem and proves
`physical_output_exact_rank_l1_le_448`. More strongly,
`physical_output_exact_rank_port_cells_l1_le_448` gives the same 448 allowance
after arbitrary monotone, per-column row-port cuts, summed over every
column/port cell. This is the local interface needed before arbitrary receiver
tags are grouped in the clipped global transfer. Focused direct Lean checks of
both modules pass. The all-stage schedule-to-tag realization, global
inversion/moment recurrence, and terminal cleanup remain open.
