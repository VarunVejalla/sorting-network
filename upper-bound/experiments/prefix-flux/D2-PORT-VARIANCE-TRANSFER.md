# D2 port transfer from column variance

## Per-column refinement and arbitrary rebinning (2026-10-27)

`D2Slope25LiftArea.lean` now proves the stronger bound

```text
sum_column sum_port |actual(column,port)-uniform_reference(column,port)| <= 416.
```

The earlier 416 estimate took the absolute value after summing over columns,
which did not retain enough information to split a port by its output column.
The refined estimate instead applies the complete-interval l1 identity to
each column separately, then uses Cauchy--Schwarz with the already checked
fixed-core area bound. `fullHeightTwoShuffle_column_refined_port_l1_le_416`
instantiates this for the physical 4096-row two-shuffle core.

`D2RankRebatch.lean` now proves that grouping signed rational cell errors by
any finite output map cannot increase their l1 total, and
`D2ColumnRebatchBridge.lean` composes that with the 416 bound. Its group type
can represent `(next tile, column)`, so a complete refinement of each output
column may be split at partial-tile offsets and rebinned without another
error charge. Both new Lean modules and the updated area module pass focused
kernel checks.

This closes the variance and rebatching arithmetic for refined column-port
cells. It still assumes complete per-column cuts and an explicit grouping
map; deriving those from the scheduled D2 wire addresses and proving they are
exactly the next stage's 64-column profile remain open. The rational uniform
reference also still needs to be matched to the global rank targets in the
all-depth flow invariant.

Status: generic arithmetic transfer, row-major partitions, and arbitrary
ordered-mask partitions are kernel-checked in `D2RankAlignment.lean`. The
(35,25) physical fixed-core variance and its 416 aggregate port-deviation
bound for rectangular 4096-row senders are kernel-checked in
`D2Slope25LiftArea.lean`. The exact-rank correction over any complete
rectangular row-major partition is kernel-checked with cost at most 32. The
cumulative identity matching each flattened cut to the sum of its
column-uniform prefix masses is now proved in `D2RowMajorMismatch.lean`; the
composition in `D2Slope25RowMajorBridge.lean` gives a kernel-checked 448
aggregate exact-rank port allowance for the actual fixed core. At a full
4096-by-64 sender this is `448/262144 = 7/4096` of capacity. Wiring this
contract into the actual D2 flow and proving global contraction remain open.
The signed integer port errors conserve mass, so the existing
`balanced_port_directional_leakage` theorem gives at most 224 wires in either
direction. `D2Slope25RowMajorBridge.lean` kernel-checks that multiplying this
by the D2 flow scale8192 fits within the `capacity/512` sender-deficit cap for
one `2^18`-wire tile. This establishes numerical compatibility only: the
actual-state interpretation of this leakage as flow deficit, and its transfer
across a tiled sender and successive stages, are still open.

The flow-side geometry is now exact in `D2FlowRankBridge.lean`: for every
active ordinary role (`topRise`, `mid`, or `botDesc`), each recursive child
deficit equals the low-prefix plus high-suffix mass on that child's concrete
`d2FlowPosition` interval. The eight-child profile has total `G + quota` under
the usual balanced, even, endpoint, and noncrossing gates. This identifies the
abstract flow update with interval accounting, but does not yet identify
physical marked-key counts or per-tile rank errors with those front masses.

`D2Slope25RebatchBridge.lean` now composes the checked 448-per-tile core
estimate with the parent tile-mass error and an arbitrary explicit grouping
of refined tile-port cells, yielding `E_out <= E_parent + 448 * tiles`. The
group type can be `(next tile, column)`, so the bound also applies to the full
64-column height profile. With twice as many output tiles, its normalized l1
error is at most `15/8192`, below the `1/512` input allowance. This handles
the arithmetic for partial offsets once cells and their destination columns
are specified; deriving that partition and grouping map from the actual D2
routing remains open.

`D2Slope25TiledBridge.lean` now sums the checked one-tile estimate over any
finite family of complete 4096-by-64 tiles. It proves total local exact-rank
port l1 error at most 448 per tile, and total leakage in either direction at
most 224 per tile; after scale 8192 this fits the aggregate `capacity/512`
budget for capacity `262144*tiles`. Each tile is compared with its own exact
rank split. This additive statement does not show that those separate tile
references agree with one global sender rank split, nor that the D2 schedule
preserves the required tile decomposition. Thus the geometric summation gap
is closed conditionally, while the parent-to-child semantic alignment and
flow-reserve identification remain open.

In addition, `tiled_global_rank_error_le_parent_add_448_per_tile` and
`tiled_global_rank_error_preserves_doubled_budget` now compose the tile-local
errors with parent misalignment. If the parent's total l1 error across tile
masses is at most `512*tiles`, the child rank error is at most `960*tiles`.
After capacity doubles from `262144*tiles`, the normalized child error is at
most `15/8192`, exactly `15/16` of the parent cap `1/512`. This proves a
strict one-stage numerical contraction for the tile-mass state. The existing
`D2FlowTreeInv` only records flow deficits,
endpoint reserves, and child coverage; it has no key-rank field, so its
current hypotheses do not establish that tile-mass premise. The all-depth
proof must augment the routing invariant with that spatial rank state (or
derive it from concrete comparator traces), and must separately price terminal
cleanup since the maintained error is small but not zero.

This is a candidate interface aimed at the cross-bag alignment left by the
scalar B2 cut contract.

### Rank-cut error gives an all-prefix escape profile (2026-10-28)

`D2RankCutTail.lean` now kernel-checks the following conversion. Suppose a
sender's output positions are a permutation of `[0,|K|)`, and for every key
rank threshold `q` and output cut `c`, the number of rank-`<q` keys before `c`
differs from `min(q,c)` by at most `e`. Then, for every `j` and protected
margin `m`,

```text
top-j keys before |K|-m  <= min(j, max(j-m,0)+e)
bottom-j keys at/after m <= min(j, max(j-m,0)+e).
```

The theorem converts a uniform spatial rank-cut error into precisely the
all-`j` tail interface used by `sent_outside_le_of_tail_profile`; in
particular it handles `j <= m` with only the additive defect `e`, without a
separate bound on the total number of outsiders. The same module also composes
the two profiles with `sent_outside_le_of_tail_profile`, giving a fringe-send
bound with no `Jmax` premise. The D2 fixed-core row-cut
theorem has defect 896, so this suggests `e=896` for a full tile after its
threshold-wise output-profile theorem is connected to linear wire positions.
That connection has not yet been proved: the existing 896 statement compares
column-prefix sums to exact rank-column prefixes, while the new interface is
stated on the actual finite sender and its output permutation. Nor does this
local profile establish the all-depth D2 transition or terminal cleanup.

The stronger pointwise route is now formalized in the same module:
`rank_cut_error_of_pointwise_displacement` proves cut error `e` from a
pointwise displacement bound `e`, and `sent_outside_le_of_pointwise_displacement`
turns it directly into the full fringe-send profile. `D2LocalRankDisplacement.lean`
now exposes the local macro's bijectivity, and
`d2_localCore_sent_outside_profile` instantiates the route with `e=832` for a
rank-coded full tile satisfying the scheduled descending-column precondition.
This is a kernel-checked local provider. It still needs transfer from the
actual keys in a scheduled ragged sender to the rank-coded tile execution and
then integration into the all-depth profile recurrence.

An exact FlowDAG screen tested the shape of this forcing term on the
`(3,3,2)`, scale-8192 D2 candidate (depth 100; 204,348 reachable shared
states). Substituting the abstract flow state's low/high deficits for the two
outsider counts, `T(j)=min(j,max(j-pi/2,0)+832)` gives at most 832 spill in
each active sender in the scanned `mid` and `botDesc` roles; this is
`13/65536` of the smallest corresponding child native capacity. The same
forcing exceeds a naive 512-wire local reserve by a factor `13/8`. This is
finite model evidence only: the flow deficits have not been identified with
the actual key outsider counts, and the 512 tile-mass reserve is not itself
the proved fringe budget. It does indicate that the tail profile's useful
large-`j` subtraction by `pi/2` must be carried through the coupled recurrence;
charging its additive 832 as a scalar per-sender error would lose that gain.
The reproducible diagnostic is
`LLM-helpers/sub300-check/d2_tail_profile_flow_gate.py`.

`D2RankCutTail.lean` now proves the aggregate algebraic interface
`T(j)+T(k) <= 2e + max(j+k-m,0)` for `T(j)=min(j,max(j-m,0)+e)` (using natural
truncated subtraction). Thus the two-sided sender forcing keeps one full
protected margin `m` in its total-mass recurrence while paying `2e` fresh
error. At the D2 choice `m=pi/2`, `e=832`, the candidate recurrence term is
`1664 + max(Hhi+Hlo-pi/2,0)`. This is a checked algebraic bound, but a useful
all-depth invariant still needs to identify `Hhi+Hlo` with the actual spatial
outsider mass and show that the remaining half-quota subtraction beats the
schedule's other fresh errors at every active level.

The companion `rankCutTail_one_sided_le` sharpens this to
`T(j)+T(k) <= e + max(j+k-m,0)` if one of `j,k` is zero. This is only a
conditional interface. The finite scan's zero co-occurrence is not an
all-depth proof, and the D2 flow's stored `low/high` endpoint reserves do not
by themselves establish that a rank-outsider count vanishes. A global-state
proof must identify the sided rank quantities and prove this condition for
every reachable sender before charging one fresh error allowance.

There are two checked schedule facts that nearly supply this condition.
`d2_ordinary_update_shape_of_reserve` says a regular cut writes only the left
deficit to child 0, only the right deficit to child 7, and zero to the six
interior children. `active_nonTop_parent_role_cases` says that every active
non-`topDesc` sender has a parent active in the preceding stage, whose role is
`topDesc` or an ordinary cut role (never `botRise`). Thus, conditional on the
parent's endpoint reserves at that preceding snapshot, the child state at the
current active sender is one-sided: `topDesc` resets it to zero; a regular cut
overwrites it with the endpoint-only profile. This avoids a separate long
history invariant. The remaining condition is specific and measurable:
prove the parent's actual reserve and cut-geometry hypotheses uniformly for
every preceding active ordinary sender, then formalize the two existing
schedule lemmas into the reachable-state assertion used by the tail bound.

The current source boundary is still the Run-13 to Run-14 invariant transition,
but its Stage-14 input proof is now partially assembled. The actual level-six
and level-five contracts, plus the full level-four contract, are kernel
checked for every depth at least 14. The remaining active input senders are
levels 0 (`topDesc`) and 2 (`mid`); once those and the root are packaged,
the Stage-14 invariant transition can be proved. A reusable continuation
beyond Stage 14, including later `botRise` cases, is still needed for an
all-depth result. The finite depth-120 audit remains supporting evidence only.

For `d >= 14`, the Stage-14 active levels and roles are level 0 (`topDesc`),
levels 2 and 4 (`mid`), and level 6 (`botDesc`). The level-four proof now
obtains its endpoint reserves, balance, deficit, quota, aggregate allocation,
and recursive level-five inputs from checked Stage-13 facts. The next local
gap is level 2 plus assembling the root reset and complete Stage-14 transition;
no `botRise` case is needed for this first transition.
The finite Stage-14 check agrees: at `d=14`, the exact FlowDAG has 21 shared
ordinary-sender state occurrences at those levels, all with `low=0` or
`high=0`; all 340 ordinary sender occurrences through the run pass the
deficit, quota, and endpoint-reserve gates. This helps validate the proposed
Stage-14 induction statement but does not prove it for arbitrary depth.

`D2Stage14Arithmetic.lean` kernel-checks the all-`d≥14` Stage-14 active
frontier and roles, and the exact identity
`capacity(level 6, stage 14) = 128 * native(level 7)`. It now also proves the
full-child property in the actual candidate run: levels below seven are
inactive through stages 0–13, except for a level-six `botRise` at stage 12;
that role preserves its immediate children, and ancestor overwrites only
change roots. Consequently the actual Stage-14 level-six endpoint reserves
hold for every depth, with equality. The same module now proves that each
actual level-six node is balanced and its deficit satisfies the Stage-14
`1/512` cap: Stage 13's level-five cut writes endpoint deficits at most
`G + quota/2` and clears interior children, while the scheduled capacity
doubles from that sender to the next level. The focused Lean check into the
ignored helper build directory passed on 2026-10-28.

The tight level-six reserve, balance, and deficit gates are kernel-checked in
`D2Stage14Arithmetic.lean`. `D2Stage14Inputs.lean` kernel-checks the
inactive-child obligation, and `D2Stage14Contract.lean` provides generic
contract assemblers for `botDesc`, `mid`, and inactive levels. The actual
Stage-14 level-six, level-five, level-four, level-three, and level-two input
contracts are now checked for every depth at least 14 in
`D2Stage14ActualInputs.lean`, `D2Stage14ActualLevelFiveInputs.lean`,
`D2Stage14ActualLevelFourInputs.lean`, `D2Stage14ActualLevelThreeInputs.lean`,
and `D2Stage14ActualLevelTwoInputs.lean`. Level two's balance/deficit and
endpoint reserve providers are in `D2Stage14ActualLevelTwoBalance.lean` and
`D2Stage14ActualLevelTwoReserve.lean`. The level-two full contract required
a 30-million-heartbeat focused check because of path-indexed recursive-tree
type reduction. The only remaining Stage-14 input obligation is the root
level-zero `topDesc` reset and child assembly; after that the actual
Run-13-to-Run-14 transition can be packaged. A reusable continuation beyond
Stage 14, including later `botRise` cases, the global spatial recurrence,
and terminal cleanup remain open.
The level-four half-quota arithmetic is now used in the actual contract proof:
`D2Stage14ActualLevelFourInputs.lean` composes it with the Stage-13 endpoint
reserve, actual balance/deficit, exact quota budget, and recursive child
contracts. The full level-four gate is kernel checked; this closes the local
obligation described in the earlier arithmetic-only notes.
The stage-14 sender margins at `d=14` are especially informative. The maximum
`G/cap` is `1/1024`, `53/32768`, and `233/131072` at levels 2, 4, and 6,
respectively, against the allowed `1/512`; `pi/cap` is exactly `15/4096` at
each level. The minimum endpoint factors `128*childDeficit/cap` are `75/4`,
`75/4`, and `1`, respectively. Thus the level-six `botDesc` sender is the
tight reserve case; the level-two and level-four gates have ample reserve.
These are exact ratios from the finite trace and suggest proving level six
first from the Stage-13 bottom-descending output. The entire table and the
3/7/11 sender counts repeat exactly at `d=20` and `d=64`, suggesting Stage 14
is a depth-independent finite bootstrap that may admit a direct symbolic
proof from the Stage-13 profile. Reproduce the exact-rational gate at any
chosen depth `d ≥ 14` with
`python LLM-helpers/sub300-check/d2_stage14_snapshot_gate.py --depth d`.

The supporting generic Lean interface in `D2Stage14Arithmetic.lean` proves
that a subtree is unchanged when all its levels are inactive, and that its
immediate children survive a run when the root is inactive or `botRise` and
all deeper levels are inactive. The candidate run path and ancestor overwrite
callbacks are connected to this interface in the all-depth full-child theorem
above.

## Terminal seam gate from the physical range-13 repair (2026-10-28)

`D2BandRepair4096Network.lean` now proves that after the physical two-grid
repair, every Boolean threshold is constant outside one common row band of
height at most13. In row-major order the dirty interval therefore has at most
832 wires. A full fixed-size sort at each terminal tile can clean this
within-tile disorder at constant depth.

That does not yet make the concatenated tiles globally sorted. The aggregate
rank-transfer theorem bounds the **sum** of tile-port errors by `parentError +
448*tiles`; even a bound of `960*tiles` allows all the error to concentrate at
one terminal seam. The local band theorem cannot prevent that concentration,
because it says where a tile's threshold disorder lies relative to its own
profile, not whether the tile has the globally correct threshold count.

The next terminal gate should be a uniform `K` bound, independent of the
number of tiles, on the number of threshold keys routed across any one seam
after the final active sender stage. Together with the 832-wire local dirty
band, this would allow each tile to be sorted and each seam to be repaired in
parallel by fixed-size networks, with asymptotically zero added coefficient.
The missing proof obligation is now specific: strengthen the aggregate
`D2Slope25TiledBridge`/`D2Slope25RebatchBridge` transfer to a per-receiver
seam bound, using the actual clipped row-major port map and an invariant that
prevents concentration. The current aggregate contraction alone is not a
terminal correctness criterion.

`D2Slope25TiledBridge.one_tile_exact_rank_count_distance_le_448` and
`tiled_receiver_rank_error_le_fiber_bound` now formalize one conditional
strengthening: if every source tile has parent rank error at most `B`, and a
receiver fiber contains at most `F` tile-port cells, then that receiver's
error is at most `F*(B+448)`. The theorem compiles in the `best` Lake
environment. The actual D2 schedule has not yet been shown to supply either
uniform premise; the aggregate `512*tiles` invariant does not imply the
pointwise `B` bound. Thus this is an interface for the seam gate, not a
closed terminal argument.

The address audit `d2_receiver_fiber_screen.py` gives a useful geometric
refinement. For `(3,3,2)`, scale8192, it counts exact source bag/port routing
pieces intersecting each next receiver bag and each 262144-wire address
tile. At depths4,5,6,7 the maximum whole-bag counts are16,128,1024,8192,
while the maximum per-address-tile counts are1,2,2,2. Thus a uniform bound is
false for a whole bag but remains plausible after splitting receivers into
fixed address tiles. This is finite evidence about bag-port pieces only: it
does not yet count the refined `(source rank tile, port)` cells in the Lean
map `outputCell`, so it does not discharge `hfiber`.

Even a uniform pointwise bound for each receiver tile would only control local
tile mass error. It would not by itself bound the cumulative prefix alignment
`A(r)`: same-sign errors across many consecutive tiles can add up at a later
seam. The terminal proof therefore still needs a signed, spatial recurrence
for prefix alignment (or an equivalent distance-weighted potential). The
fiber estimate can limit fresh error at one receiver, but cannot replace that
global recurrence.

## Column profile and port map

Consider a sender represented by columns `j=1,...,n`. Column `j` has `L_j`
live wires, and after its final column sort contains `x_j` marked keys in a
prefix, where `0 <= x_j <= L_j`. Put

```text
L = sum_j L_j,       H = sum_j x_j,       theta = H/L,
A_w = (1/2) * sum_j (x_j - theta*L_j)^2.
```

A child port occupies a consecutive slice `[u_j,v_j)` in each column. Its
marked-key count is

```text
P = sum_j clip(x_j-u_j, 0, v_j-u_j),
clip(z,0,w) = min(max(z,0),w).
```

The uniform-density reference profile has `theta*L_j` marks in column `j`.
Define its port count by

```text
P_0 = sum_j clip(theta*L_j-u_j, 0, v_j-u_j).
```

Since every clip function is 1-Lipschitz,

```text
|P-P_0|
  <= sum_j |x_j-theta*L_j|
  <= sqrt(n * sum_j (x_j-theta*L_j)^2)
  = sqrt(2*n*A_w).
```

This controls every port of a sender from the same variance bound, without a
union bound over ports. For a rectangular `m x n` sender, `L_j=m`, so a
uniform provider bound `A_w <= Gamma*n` implies

```text
|P-P_0| <= n*sqrt(2*Gamma),
|P-P_0| / (m*n) <= sqrt(2*Gamma)/m.
```

For a rectangular port spanning rows `[r,r+w)`, its reference count is the
piecewise-linear rank map
`P_0 = clip(H-r*n, 0, w*n)`. This is the candidate ideal child-mass map to
compare with the exact D2 flow allocation. For a ragged fixed live mask, the
sum-of-clips definition above remains valid column by column.

## Aggregate error across a complete port partition

Suppose sender ports partition each live column into consecutive intervals
`I_{j,1},...,I_{j,K}` (include both fringes, so no live wire is omitted).
Write `P_i` and `P_{0,i}` for actual and reference counts in port `i`. For a
single column, the vectors of counts obtained by intersecting the prefix of
length `x_j` and the reference prefix of length `theta*L_j` with the partition
have differences of one sign and total absolute value exactly
`|x_j-theta*L_j|`. Summing columns and applying the triangle inequality gives

```text
sum_i |P_i-P_{0,i}|
  <= sum_j |x_j-theta*L_j|
  <= sqrt(n * sum_j (x_j-theta*L_j)^2)
  = sqrt(2*n*A_w).
```

Also `sum_i(P_i-P_{0,i})=0`, so the total positive port leakage and total
negative port deficit are each at most `sqrt(n*A_w/2)`. Unlike the pointwise
bound, this controls the *sum* of errors over all children and both fringes;
it avoids paying one full sender allowance per port. At `A_w<=Gamma*n`, the
aggregate l1 error is at most `n*sqrt(2*Gamma)`. For rectangular aligned ports,
the l1 error fraction of the parent capacity is at most `sqrt(2*Gamma)/m`.

This feeds an address potential only if the reference port counts `P_{0,i}`
match the exact child rank intervals. Under that condition, half the l1 error
is the minimum number of keys whose child addresses disagree with their
target counts for this tracked binary threshold. The D2 cut-layout identity
for every ragged sender and fringe remains a required proof obligation; a
variance estimate cannot repair a reference-map mismatch.

There is also a clear limitation. If the parent's actual class count is `H`
and its target count is `H*`, both uniform reference maps are prefix splits
over the same complete port partition, so
`sum_i |P0_i(H)-P0_i(H*)|=|H-H*|`. The triangle inequality then gives only
`child_l1_error <= parent_l1_error + local_port_l1_error`. Summing over
senders is nonexpansive but not contractive; a per-stage `O(N/m)` local error
would accumulate over `O(log N)` stages if used alone. The rank proof must
also use a strict contraction, or show the flow reserve absorbs the local
errors without carrying them as new rank error. This identifies the precise
role of the existing saturated-aware flow invariant: it must turn aggregate
port leakage into absorbed reserve, not merely propagate an l1 error bound.

`D2RankAlignment.lean` kernel-checks the full arithmetic transfer: across any
finite collection of children, total actual-to-ideal count error is at most
the parent displacement plus summed local transfer allowances. The parent
displacement is charged once. For ragged senders, `ragged_column_port_partition_distance`
proves that the total reference displacement across all ports is at most the
sum of per-column prefix displacements.

The same file now proves `ragged_nat_rational_port_variance_bound`. For
integer prefix heights, any rational uniform density, and a complete ragged
interval partition in each column, the square of the aggregate port l1 error
is at most the number of columns times the sum of squared column deviations.
The proof includes the interval conservation and same-sign identity, the
natural-count/rational-mass conversion, and Cauchy--Schwarz. The wrapper
`ordered_mask_rational_port_variance_bound` then specializes it to an
arbitrary static ordered list of live addresses: every contiguous partition
of that list induces complete ragged intervals in each column, with no
rectangular-mask assumption. Thus the address-partition geometry is no longer
an assumption. This theorem controls deviation from the per-column uniform
density reference. The exact-rank correction is handled for rectangular
row-major senders below; arbitrary ragged fixed-mask rank targets still need a
separate mismatch estimate. The physical provider must verify that the core
leaves each induced column sorted before the ports are read, and the uniform fixed-core variance provider is now kernel-checked for the
4096-row (35,25) physical shuffle in `D2Slope25LiftArea.lean`; arbitrary ragged
fixed-mask rank targets still need the separate mismatch estimate.

## Row-major reference correction for rectangular senders

For a full `m × n` row-major sender, the exact rank-prefix target used by the
coupled LP is `I(b)=min(H,b)` at flattened boundary `b`. The uniform-density
column profile gives another cumulative count `U(b)`: write `b=kn+s` and
`H=qn+r`, with `0≤s,r<n`. Then `U(b)=I(b)` unless `k=q`, and on that single
boundary row

```text
I(qn+s)-U(qn+s) = min(r,s) - s*r/n.
```

This discrepancy starts at zero, rises linearly to `r(1-r/n)`, then falls
linearly to zero. Its full discrete total variation is therefore
`2r(1-r/n) ≤ n/2`. For any complete partition of the flattened sender, each
port's target mismatch is the difference of this cumulative discrepancy at
its two boundaries. The sum of absolute port mismatches is at most the full
total variation, hence at most `n/2`, independent of the number or ragged
widths of the ports. `D2RowMajorMismatch.lean` now kernel-checks the boundary
formula and pointwise bound `0 <= I(b)-U(b) <= 16` for `n=64`, then sums the
single triangular bump to prove full boundary variation at most32. The exact-
Fraction audit `row_major_reference_mismatch.py` also checked the general
`n/2` variation identity for 10,800 `(m,n,H)` cases through `n=16,m=12`.
The transfer from checked variation to the l1 error over an arbitrary
complete row-major port partition is kernel-checked by
`rowMajor_complete_port_rank_correction_le_32` in
`D2RowMajorMismatch.lean`. The remaining identity that connects the local
column-uniform port reference to the row-major cumulative reference is an
explicit premise of `D2Slope25RowMajorBridge.lean`, not yet a proved theorem.

Combining this correction with `ragged_nat_rational_port_variance_bound`
gives, conditionally on `A_w≤48n`,

```text
sum_ports |actual - exact-rank-target|
  ≤ sqrt(96)*n + n/2.
```

At row height `m=8192`, allocation `a=mn`, and `a/c≤279/256`, this gives
`error/c ≤ (279/256)*(sqrt(96)+1/2)/8192 < 21/16384 * 279/256
< 1/512`. Thus the uniform-density/exact-rank mismatch is not an obstruction
for rectangular row-major senders; it fits inside the existing normalized
transfer allowance with slack; the final rational arithmetic is
kernel-checked as `d2_row_major_port_transfer_budget` in
`D2RankAlignment.lean`. This closes that particular map mismatch for these
senders, but the `Gamma=48` provider and the mapping from the resulting
per-threshold errors into the reachable D2 flow state remain unproved. Ragged
fixed masks still need their own mismatch estimate.
The one-column identity itself is reduced by
`column_port_abs_error_eq_total_deviation` to two facts: interval errors all
have the same sign as the total column deviation, and their signed sum equals
that deviation.

The side budgets are now formal too. `balanced_port_leakage_equal` and
`balanced_port_directional_leakage` in `D2RankAlignment.lean` prove that when
actual and reference ports conserve the same total mass, the total positive
and negative leakage are equal and each is at most half the aggregate l1
error. The focused Lean check passes via
`lake env lean ../prefix-flux/D2RankAlignment.lean` from
`upper-bound/experiments/runaware`. This supplies the exact low/high split
needed by an endpoint-reserve argument; it still does not identify these
leakage terms with the concrete flow fields `L,H`.

**Sparse-bottom edge-reserve compatibility (2026-10-26).** The sub-300
candidate is the sparse-bottom `(3,2,2)` flow, whose edge invariant has a
different reserve condition from the regular `(3,3,2)` flow. I initially
tested the latter's `c/128` endpoint gate; that result does not apply to this
candidate. Re-running the actual sparse-bottom edge screen at row height
8192 (`python d2_edge_trace_screen.py --depths 25 50 100 --row-bits 13`)
reproduces its role-specific minimum tail reserves: `211/256 c` for
`topRise`, `1673/2048 c` for `mid`, and `21/2048 c` for `botDesc`.

The conditional Gamma=48 port transfer has one-sided error `< c/1024 =
2/2048 c`, smaller than even the tight `botDesc` edge reserve `21/2048 c`.
So this aggregate transfer allowance is numerically compatible with the
candidate's *edge* reserve, unlike the regular-flow gate I first checked.
This is useful evidence for the boundary-path invariant, but does not yet show
that the physical leakage consumes this reserve one-for-one, prove the
Gamma=48 fixed-core provider, handle interior senders, or establish terminal
sorting. The edge screen itself is finite through depth 100.

The arithmetic margin is now kernel-checked by
`d2_sparse_botDesc_leakage_preserves_endpoint_gate` in `D2RankAlignment.lean`:
`21/2048 - 1/1024 = 19/2048 > 1/128`. This confirms that a loss bounded by
the proposed one-sided port leakage would still leave the bot-descending
endpoint gate. It does not establish the needed semantic fact that actual
rank leakage reduces this reserve by at most the same amount.

There is also scalar room to absorb the proposed rank state into the tolerant
D2 sender gate: the scheduled strict deficit is at most `15/8192` of
capacity, and a carried rank error of `1/512` adds `16/8192`; their sum
`31/8192` is below the tolerant `23/4096 = 46/8192` cap. The inequality is
kernel-checked as `d2_strict_deficit_plus_rank_error_fits_tolerant_budget`.
This only closes the scalar budget calculation. The missing invariant must
still show how signed threshold errors update `G,L,H` and maintain endpoint
balance/reserves, so the tolerance theorem's hypotheses do not yet follow.

For a fixed complete child partition, the cut update itself is now
nonexpansive in its two front positions:
`aggregate_two_front_profile_distance` proves that the l1 change in all child
deficits is at most the sum of the left-front and right-front displacements.
This formalizes one transition component. It does not yet cover the moving
child partition `d2FlowPosition`, or prove that physical port-count errors
induce only those front displacements; those are the remaining steps before
this can instantiate the rank-error invariant.

Changing the partition can double the **l1** error even with fixed fronts.
The exact Lean example `moving_partition_two_front_counterexample` uses
child sizes `(0,1,1,1)` and `(1,1,1,0)`, with low front `1` and high suffix
starting at `2`: size-profile l1 error is `2`, while child-deficit-profile
l1 error is `4`. The two output profiles have equal total mass, so their
one-sided positive leakage is only `2`. This points to tracking conserved
one-sided leakage through the transition, rather than asking for l1
contraction. The theorem `moving_two_front_partition_directional_leakage`
now proves the general one-sided bound for complete partitions: width
variation is charged once, plus the two front displacements. It resolves the
abstract factor-two issue; the remaining gap is to identify these
front/width changes with the actual physical rank leakage and reachable
`G,L,H` update.

The prefix and reflected-suffix parts are now kernel-checked as
`prefixProfile_moving_partition_distance` and
`suffixProfile_moving_partition_distance` in `D2RankAlignment.lean`. For
complete partitions of `[0,a)` with widths `s_i,t_i`, cumulative boundaries
`b_i,c_i`, and fixed threshold `H`, each theorem bounds the l1 discrepancy in
the clipped per-child counts by `sum_i |s_i-t_i|`. The prefix proof uses the
potential `delta_i=min(b_i,H)-min(c_i,H)` and telescopes its endpoint terms;
the suffix theorem reflects the complete partition and reuses that argument.

The combined theorem `aggregate_moving_partition_two_front_profile_distance`
handles moving fronts and moving child boundaries together: the aggregate
two-tail child-profile l1 error is at most the sum of the two front
displacements plus `2*sum_i |s_i-t_i|`. The factor two on the boundary term is
sharp, as shown by `moving_partition_two_front_counterexample`. If the fronts
are fixed, both profiles have the same total mass, so each one-sided leakage
is at most half this l1 bound, namely `sum_i |s_i-t_i|`; the example attains
that leakage bound. The new kernel-checked theorem
`moving_two_front_partition_directional_leakage` handles moving fronts too:
each direction is bounded by `sum_i |s_i-t_i| + |left-left'| +
|right-right'|`, removing one copy of the width variation from the symmetric
l1 estimate. This gives the right one-sided quantity for charging flow
reserves. It remains conditional on the real D2 port map inducing these
complete partitions, and does not identify physical errors with the flow
fronts or reachable `G,L,H` state; those semantic bridges remain open.

The local overlap formulas now match the executable D2 cut arithmetically:
`prefixIntervalMass_eq_left_front_overlap` and
`suffixIntervalMass_eq_right_front_overlap` identify them with
`d2LeftCut`/`d2RightCut` after setting `v=pos+size` in
`D2ScheduleReserve.lean`. The focused Lean file check passes. This closes the
definition-level geometry match; it does not connect the marked-key counts
after a physical separator to these deficit counts.
Exhaustive arithmetic checked 2,212,262 small two-tail cases (`n<=4`, total
width `<=8`) without finding a violation; this is supporting evidence only.

The geometry is also formalized. `orderedColumnCut` counts column labels
before a boundary in any static ordered list of live wires. A complete
partition of that list induces complete monotone intervals in every column,
and `aggregate_ordered_mask_port_error_le_parent_add_transfer` applies the
transfer bound without assuming a rectangular mask. The row-major corollary
specializes this to the layout used by the current LP.

For rectangular row-major senders, the fixed-list address bridge and exact-
rank reference correction are now handled above. Remaining work is to connect
the actual D2 core's sorted-column output to this abstraction, handle any
ragged sender/reference mismatch, and transfer the per-threshold error into
the reachable `G,L,H` state through the all-depth schedule. The 4096-row
(35,25) fixed-core variance provider is now kernel-checked in
`D2Slope25LiftArea.lean`; this does not resolve the ragged rank-target mismatch. These Lean lemmas alone do not improve
the bound.

## Why the scale is interesting

The existing exact one-round expectation calculation in
`d2_ordered_profile_moment.py` bounds excess column area by

```text
f_n(A) = sqrt((n^2-1)*(2*A+n/4)/(12*n)).
```

For a rectangular sender, the worst input excess area per column is
`c_0=m^2/8`. Iterating the expectation recurrence gives, at `m=8192`,
`n=64`,

```text
c_0 = 8,388,608
c_1 <= 1,182.27
c_2 <= 14.04
```

Here `c=A/n` is the excess area per column; the full variance `A_w/n` adds
at most the integer-rounding term `1/8`, so the two-round expectation screen
is about `14.17` per column. This is only an expectation bound for fresh
independent row scrambles. It does not imply that one fixed scramble pair
satisfies a uniform all-input variance cap.

As a target for a fixed-provider theorem, `Gamma=48` would give
`sqrt(96)/8192 < 1/800` port discrepancy as a fraction of sender capacity.
The margin over the expectation is plausible enough to test, but no uniform
tail/union bound has been proved. The current B2 provider controls individual
spill cuts; it does not supply this variance contract.

## Seeded fixed-core adversarial screen

`d2_variance_fixed_core_attack.py` directly evaluates two fixed layers of
per-row column permutations and column sorts on binary inputs represented by
their initial column heights. It uses an exact constant-time update when one
input height changes by one: exactly one bit changes in each round, so only
one output column height changes at each step. For 256 annealed searches of
50,000 proposals, it found a largest total `A_w` of `1498.4296875`, or `23.41`
per column, for a seeded `8192 x 64` core (NumPy PCG64 core seed
`20261025`). This is below the proposed total cap `48*64=3072`, but remains a
heuristic lower witness to the true maximum, not an upper bound. The
incremental evaluator matched full recomputation for 5,000 random moves and
the vectorized round evaluator matched 100 literal small cases. Reproduce with:

```sh
python upper-bound/experiments/prefix-flux/d2_variance_fixed_core_attack.py \
  --restarts 256 --steps 50000
```

The result makes the cap less obviously implausible for this one random core;
it does not prove the cap for that core, nor show that the chosen core meets
the probabilistic provider requirements of the construction.

### Independent-core stress sweep (2026-10-26)

I repeated the same profile adversary on eight independently seeded
`8192 x 64` two-scramble cores. Each core used eight restarts of 10,000
single-height proposals. Every found profile stayed below `48` variance
units per column; the largest was `22.296387` per column (core seed
`20261031`). The other per-column maxima were
`16.125854, 19.622925, 17.034668, 18.050293, 22.090698, 18.522339,
19.042480`. Reproduce with:

```sh
python upper-bound/experiments/prefix-flux/d2_variance_seed_sweep.py
```

This is a broader plausibility screen, not an upper bound: the search is
heuristic and each core saw only finitely many profiles. It neither supplies
the uniform all-input `A_w <= 48*n` theorem nor checks the full three-round
candidate core's other provider conditions. The fixed-core variance proof
remains open.

### Port-variance contract in the coupled D2 gate (2026-10-26)

I added the corrected width-64 margin-tail profile and the optimistic
per-sender aggregate port-l1 contract to the depth-2, scale-8192 coupled
model, with all-row prefix dominance. The variance contract is the current
`sqrt(2*Gamma)*columns + columns/2` bound: the second term is the proved
worst-case total-variation correction from uniform-density ports to exact
row-major rank intervals. Optimal continuous-model terminal wrong masses
were:

| assumed `Gamma` | terminal wrong mass | largest single terminal block |
|---:|---:|---:|
| 48 | 741.453048 | 330 |
| 14.17 | 419.294376 | 186 |
| 0 | 36 | 16 |

All three runs had 2,461 equalities, 26,753 inequalities, 1,991 distance-tail
constraints and 9 variance-port constraints; equality and inequality residuals
were below `1e-9`. These are relaxation results, not fixed-core traces.

I then implemented `--variance-port-l1-residue`, which replaces the uniform
`columns/2` term by the exact `2*r*(1-r/columns)` total variation and forces
the sender mass residue through integer quotient/residue selectors. At
`Gamma=0`, this mixed-integer relaxation solves to 31 terminal wrong keys
(largest single block14; 137 integer selectors; 2,479 equalities; 26,753
inequalities; zero MIP gap; maximum solution inequality residual below
`1e-9`). The improvement is only five keys. All other rank/profile counts
remain continuous. The script's default sorted-witness diagnostics are not
applicable to this deliberately near-perfect-provider assumption and report
a violation, so only the optimizer's primal feasibility and zero MIP gap
support the 31-key result.

At tree depth3 (root size `4,194,304`), the same exact-residue,
`Gamma=0` gate is optimal at `254.21875` terminal wrong keys (largest block
102; 9,576 variables; 1,033 integer residue selectors; maximum inequality
residual `7.46e-9`; zero MIP gap). The normalized residual is `6.06e-5`,
close to the depth2 ratio `31/524,288 = 5.91e-5`. Thus even the idealized
zero-variance, exact-residue local contract leaves a small but nonvanishing
global-alignment density in these shallow relaxations. This is not a
fixed-network lower bound; it identifies what a global transfer or priced
cleanup must resolve.

This sensitivity test makes aggregate port control a stronger lead than the
tail profile alone, but it still does not yield terminal purity at the
candidate `Gamma=48`. The exact residue correction removes only five keys
from the `Gamma=0` relaxation, so the remaining error is global alignment,
not primarily the uniform-reference approximation. A better local provider
may lower the residual further, but this gate gives no evidence that local
port precision alone can force exact terminal counts. The uniform provider
and all-depth flow-state induction remain open.

Reproduce the runs by adding the following options to the profiled shallow
gate in `D2-DISTANCE-TAIL-PERIOD-GATE.md`:
`--all-row-dominance --variance-port-l1-gamma G`, with `G=48`, `14.17`, or
`0`; omit `--integer` for the optimal values in the table. Add
`--variance-port-l1-residue` to reproduce the 31-key mixed-integer result.
The full integral-count gamma-zero variant returns a time limit without a
primal point.

### Structured cyclic shuffles (2026-10-26)

I screened deterministic row shifts instead of random row permutations. In
round one, row `r` shifts columns by `r`; in round two, row `r` shifts by
`35*r+17` modulo64. A 64-restart/20,000-step search on both the 512-row
residue model and the full 8192-row core found the same best score:
`A_w=286.875`, or `4.482422` per column, with output column range13. A
separate sweep over odd second slopes at 512 rows found `(1,35)` promising
(3.65 per column in its smaller search) but also found bad pairs, including
second slope63 at160.49 per column. The schedule therefore needs a proved
slope choice; periodicity alone is not enough. Reproduce the candidate screen
with:

```sh
python upper-bound/experiments/prefix-flux/d2_cyclic_core_screen.py \
  --rows 8192 --first-slope 1 --second-slope 35 --second-offset 17
```

There is an exact reduction behind the 512-row screen. For `n=64` and any
row count divisible by64, write input heights as `x_j=64*q_j+t_j`. After the
first cyclic shift, column counts are `Q+R_c`, where `Q=sum q_j` and
`R_c=sum_j [((c-j) mod64)<t_j]`. After the second shift the final counts are
a common additive constant plus
`S_d=sum_c [((d-c-17)*35^{-1} mod64)<((Q+R_c) mod64)]`.
Consequently the centered output profile depends only on the 64 residues
`t_j` and `Q mod64`, not on the row count. At 512 rows the allowed quotients
already realize every `Q mod64` for each residue vector, so this is the full
residue domain of the 8192-row core. I checked the formula against direct
two-round evaluation on 200 random height profiles at both row counts.

The range target is sufficient for the provider: for `n` values in an
interval of width `R`, their centered sum of squares is at most `n*R^2/4`,
so `A_w/n <= R^2/8`. Thus a uniform range bound of19 would imply
`A_w/n <= 45.125 < 48`; the searched range13 would imply at most21.125.

I encoded that reduced worst-case search as a MILP, with one-hot encodings of
the final column counts to linearize the exact quadratic variance. It solves
the 8-column `(1,3)` sanity case to zero gap (`A_w=6`), but the 64-column
`(1,35)` instance (16,515 variables, 8,259 constraints) hit 120 seconds
without a primal solution. The reduction is exact; the current optimization
formulation does not yet certify the 64-column maximum. A useful next step is
to prove a direct discrepancy bound for the composed cyclic interval maps,
or find a more tractable exact certificate for the residue optimization.

I also replaced the quadratic objective by a linear maximum-range objective.
The 8-column sanity case solves exactly with maximum range4. At 64 columns,
HiGHS timed out after120 seconds with a feasible range-8 witness but a loose
range-64 dual bound. The sharper feasibility query requiring range at least20
also timed out without a primal point. Neither run proves nor refutes the
candidate cap. The scripts are `d2_cyclic_variance_milp.py` and
`d2_cyclic_range_milp.py`.
Reproduce the quick all-odd-slope sweep with
`d2_cyclic_core_screen.py --rows 512 --first-slope 1 --second-offset 17
--restarts 6 --steps 5000 --sweep-odd-second-slopes`.

A direct Z3 `QF_LIA` gate for an output range of at least20 was also tried;
it timed out at 120 seconds with `unknown`. The same encoding proves the
8-column `(1,3)` sanity gate `range<5` unsatisfiable in about3 seconds. The
exact SMT encoding is retained as `d2_cyclic_range_smt.py`. Thus both the
quadratic and linear exact
optimizers remain inconclusive at the target width; do not interpret their
timeouts as support for the range bound.

### Three-shuffle 4096-row core reduction (2026-10-27)

The four-sort `(3,2,2)` candidate has three shuffle/sort rounds at row height
4096, so its local core must be screened separately from the two-round
8192-row experiment above. For a cyclic round with `C=64` columns, row shift
`a*r+b (mod 64)`, and `gcd(a,64)=1`, write each input height as
`h_c=64*q_c+t_c`, `0<=t_c<64`. The output height at column `d` is exactly

```text
sum_c q_c + sum_c [ ((d-c-b)*a^{-1} mod 64) < t_c ].
```

Thus the output vector, up to a common additive constant, depends only on the
residue vector `t` and `sum q_c mod 64`. Applying the same identity round by
round shows that the centered final profile of any fixed number of cyclic
rounds depends only on those inputs, independent of row height as long as it
is a multiple of64 and all intermediate heights remain in range. Every such
state has a representative at row height512: for any `t`, each column allows
at least seven quotient units, so the total quotient capacity is at least
448 and realizes every residue modulo64. This proves that the 512-row
optimization domain covers the full 4096-row domain for this core; it is not
merely a scaled-witness heuristic. This is an exact paper derivation, not yet
Lean-formalized.

For slopes `(1,35,17)` and zero offsets, a 64-restart/20,000-step search at
both 512 and4096 rows found `Aw=103.6796875` (`1.619995` per column) and
output range8. A further 1,000 random 4096-row profiles were mapped to
512-row representatives with the same residue vector and quotient sum mod64;
the three-round centered outputs and variances agreed exactly. These checks
validate the reduction implementation but do not certify the maximum: the
heuristic value is only a lower bound on worst-case `Aw`, while the 64-column
exact MILP/SMT optimizers above remain unresolved. The reduction makes a
uniform provider proof finite and row-height independent. The exact maximum
variance remains open, but the one-sided-profile DP below proves the weaker
range cap needed for `Gamma<=48` at width64.
I extended `d2_cyclic_range_smt.py` to encode this third round, including the
otherwise easy-to-miss quotient baseline modulo64. Its 8-column sanity model
matches direct three-round evaluation after centering. At 64 columns, the
exact query asking whether the range can reach20 returned `unknown` at the
120-second timeout, so it neither proves nor refutes the desired range bound.
The checked command used slopes `(1,35,17)`, all offsets zero, and threshold20.
An initial follow-up accidentally used offset17 in round two and is excluded
from this assessment. The correct-schedule timeout shows the current SMT
encoding is not yet a practical certificate method at width64; it is no
evidence for the range cap.

**Longer exact-solver gate (2026-10-26).** I reran the 64-column,
three-round `(1,35,17)` range MILP for 600 seconds. The maximum-range model
still timed out with a feasible range-5 profile and dual upper bound 63
(11.6% gap); the direct `range >= 20` feasibility model timed out at 600
seconds without either a primal witness or a bound. Reproduce with
`d2_cyclic_range_milp.py --columns 64 --first-slope 1 --second-slope 35
--second-offset 0 --third-slope 17 --third-offset 0 --time-limit 600`, adding
`--require-range 20` for the decision gate. This longer run does not change
the proof status. Simply extending the current all-endpoints MILP is not a
productive certificate route. Fixing the output-pair separation removes the
endpoint-selection variables but still leaves the main weakness; the next
model needs to capture discrete carry/interval correlations across rounds.

Fixing the separation to `delta=32` did not yet rescue the formulation: the
`range >= 20` MIP also timed out at 120 seconds without a primal point or
bound. Its LP relaxation solves in 3.3 seconds but has the trivial upper bound
32 for that pair. Thus pair-fixing removes the endpoint-selection variables
but not the main weakness; useful strengthening must capture the discrete
carry/interval correlations across the three rounds.

I also extended `d2_cyclic_range_milp.py` to three rounds, preserving the
sum of first-round quotients that shifts the third-round residues. Its
8-column optimal range model agrees with direct 64-row simulation. At width
64, the full `range >= 20` MILP has 12,546 integer variables and 12,353
constraints; HiGHS reached 120 seconds without a feasible point or a bound.
Fixed-pair 5-second gates reported infeasibility for separations `1,48,56`,
while the other sampled separations timed out. These floating solver outcomes
are diagnostics, not certificates.

The LP relaxation was solved to optimality for every endpoint separation
`delta=1,...,63`. Its upper bound for `T[0]-T[delta]` is exactly
`(15*delta mod 64)`, since the inverse of final slope17 is49, and the last
round's unary interval indicators alone impose that limit: the two tested
residues for each source differ by `k=(49*delta mod64)`, and only the
`64-k` nonwrapping starts can contribute positively. Thus
`64-k=(15*delta mod64)`. This analytically prunes 19 separations (those whose
bound is below20); the other44 have
relaxation bounds at least20, so the first two rounds' integrality is still
essential. The full interval of LP bounds is reproducible by calling
`solve(..., relax_integrality=True, delta=delta)` in
`d2_cyclic_range_milp.py`. This LP alone gave no uniform range result; the
subsequent one-sided-profile DP below supplies a width-64 range cap.

A third encoding in `d2_cyclic_range_bv.py` uses fixed-width bit-vectors so
residue extraction is low-bit slicing rather than integer modulo. It returns
and independently reconstructs a valid witness on the 8-column sanity gate.
At width64, the fixed-separation `delta=2`, range-20 query still returns
`unknown` after60 seconds. This does not improve the proof status, but keeps
the exact recurrence in a SAT-friendly form for further solver experiments.

### One-sided profile DP closes the width-64 variance cap (2026-10-26)

The full residue MIP is unnecessary for the target `Gamma=48`. After the
slope-35 shuffle, its residual heights `y[d]` satisfy
`0<=y[d]<=64` and `y[d]-y[d-35]<=1`: for a fixed output pair, each source
column's indicator changes by at most zero downward, except the unique wrapped
row index, which contributes at most one upward. The common quotient before
the slope-17 shuffle only contributes full rows and rotates the residual
output, so it does not affect range.

For each output separation `delta`, the slope-17 output difference is a sum
of unary functions of `y[d]`. Maximizing this sum subject only to the
one-sided slope constraint is an exact maximum-weight labeling DP on the
64-cycle. The recurrence and all 63 results are in
`d2_slope_profile_bound.py`; the maximum is15, at separations1 and53. The
exact finite calculation therefore gives output range at most15 for every
input profile at this width, and `A_w/64 <= 15^2/8 = 225/8 = 28.125`.
This is a candidate deterministic provider stronger than `Gamma=48` for width
64; the integer DP is not yet Lean-checked or independently reviewed. The
range-to-area implication is kernel-checked in
`D2RankAlignment.lean` as `half_variance_le_range_sq_div_eight` and its
width-64 corollaries `half_variance_64_le_225_over_eight` and
`nat_half_variance_64_le_225_over_eight`; the latter derives the exact mean
directly from a natural-valued height profile's conserved total. All retain
the range-15 premise explicitly, so the finite DP remains the unformalized
provider obligation. The same Lean module also proves
`cyclic_successor_indicator_count_le` and instantiates it for the concrete
slope-35 residue map: `slope35_adjacent_height_difference_le_one` gives the
one-sided adjacent-column height gradient for every destination. The exact
physical row-count bridge is checked too: `residueHits64_eq` counts residues
below any height as full 64-row cycles plus the partial-cycle hit;
`slope35_row_destination_iff_residue` identifies the inverse-affine row
threshold; `slope35PhysicalOutputHeight_eq` gives the quotient/residue output
profile; and `slope35PhysicalOutputHeight_gradient` proves the one-sided
gradient for arbitrary natural input heights, with the common quotient
canceled. The final slope-17 max-plus range DP remains unformalized.

The argument is not uniform in column count. Running the same relaxation at
width128 gives maximum20 (separation113), so the one-sided invariant alone
does not provide `Gamma<=48` there. This is not a counterexample to the full
three-round core: a direct 96-start width-128 search found range6, but that
search is heuristic. The actual D2 sender-width interface still needs a
uniform-in-width argument or a priced finite-tile/seam construction; the
global rank-alignment and terminal-count gaps also remain open.

### Structured slope sweep (2026-10-28)

The exact row-update heuristic was run on several zero-offset slope triples
at 512 rows. With 24 restarts and 15,000 moves, `(1,5,25)` found
`Aw/64=1.4917` and output range7; `(1,35,49)` found1.6172/range8,
`(1,35,17)` found1.6200/range8, `(1,13,41)` found1.5347/range8,
`(1,3,9)` found1.8750/range9, and `(1,9,27)` found3.9097/range11.
These are lower bounds on the respective worst cases, not provider bounds.
For one round of slope `s`, its residue output `R` satisfies
`(P_s R)_x=F(P_s t)_x`, where `F` is cyclic interval coverage and
`(P_s g)_x=g_{sx}`. Thus slope `s` conjugates `F` by the dilation `P_s`.
For zero-baseline residue maps, the `(1,5,25)` triple composes to
`P_25^{-1} F(P_5(F(P_5(F(t)))))`; the final coordinate permutation does not
affect range or variance. The full height map also carries a shared quotient
residue between rounds, so this conjugacy has not yet closed that state. It
is a candidate for a stronger profile invariant. The
64-column MILP test for a range-20 witness at
fixed separation1 timed out after60s without a primal point; no exact bound
for this slope triple is established.

The same search extended to four rounds at the 2048-row candidate scale.
For slopes `(1,5,25,61)` (the first four powers of5 modulo64), a 64-restart,
50,000-move search on the complete 512-row residue domain found
`Aw/64=0.76514` and range5. The generalized bit-vector gate reproduces the
four-round recurrence and passes a four-round width-8 direct-simulation
check, but the width64 query for range at least20 at separation1 returns
`unknown` after60s. The powers-of5 schedule is thus a stronger local
candidate for the 2048-row/five-sort 292.5 cost point, but its uniform local
provider and global rank transfer remain open. This four-round screen uses
cyclic shuffles on every row; the 292.5 construction replaces the first and
last28 rows of its final shuffle with the packed edge repair, whose effect on
this dense-profile variance/range statistic still needs a separate bound.
For the unmodified cyclic core, 40 random 2048-row profiles also matched
their canonical 512-row representatives exactly after all four rounds.

## Selected-cut global recurrence screen

In a rectangular aligned sender, `Gamma=48`, `m=8192` implies a much sharper
bound for every common row-prefix or row-band port. Let `e_j=x_j-H/n`, so `sum e_j=0`,
and write `L=sum (e_j)_+=sum (-e_j)_+`. If `p` deviations are positive,
Cauchy gives

```text
sum e_j^2 >= L^2/p + L^2/(n-p) >= 4*L^2/n,
L <= sqrt(A_w*n/2) <= n*sqrt(Gamma/2).
```

For every row prefix, the defect `d(r)=min(H,r*n)-P(r)` is between zero and
`L`: below the mean it sums only negative deviations, and above the mean it
sums only positive deviations. For a common row band `[u,v)`, its reference
count minus actual count is `d(v)-d(u)`, whose absolute value is also at most
`L`. Thus for `Gamma=48`, both prefix and common-band error fractions are at
most `sqrt(24)/8192 < 1/1672` (`24*1672^2 < 8192^2`). This sharp bound uses
equal column lengths and a common row band. For a rectangular sender with
column-dependent slice intervals, retain the general Cauchy bound
`sqrt(96)/8192`; unequal live column lengths need separate normalization.
I reran the existing depth-2, scale-8192 integral selected-cut gate with
local-cut defect tightened from `1/800` to `1/1672`.

The sum of prefix defects also obeys

```text
sum_(r=1)^(m-1) d(r)
  <= A_w + (1/2)*sum_j |e_j|
  <= n*(Gamma + sqrt(Gamma/2)).
```

The first inequality follows by summing the integer triangular tails of each
column deviation; the second is Cauchy. At `Gamma=48`, this is below `53*n`,
giving the attempted aggregate-area fraction `53/8192`.

An exact `Fraction` checker verifies the one-sided prefix inequality and the
aggregate area inequality below on 1,270 small rectangular profiles; the
general ragged-band transfer separately passes 278,912 small cases. These are
sanity checks of the algebra, not substitutes for its proof.

The MILP ran 300 seconds and reached 31,718 nodes. Its best feasible solution
has zero terminal wrong mass, but it did not prove optimality: `mip_gap` was
`0.00363886`, and the dual bound permits at most 626 wrong keys in this
selected-cut model (objective constant 172,032 minus dual bound 171,406).
This is a promising screen signal, not a purity proof. For comparison, the
weaker `1/836` gate solves optimally and leaves 1,254 wrong keys. An attempted
all-row aggregate-area gate at fraction `53/8192` timed out without a primal
solution after building 413,230 variables and 1,238,985 inequalities; it is
not presently the efficient route. The row-stride-1 LP with the `1/1672`
prefix cap also timed out without a primal solution (409,846 variables,
131,485 equalities, 1,228,824 inequalities).

The `1/836` result is an optimal terminal wrong mass of 1,254 keys. Its
threshold defect is 969, split into 627 cross-bag
alignment and 342 within-bag defect. The LP retains 4,345 variables and 1,437
equalities; the solution's integrality residual is below `3e-9`. The `1/836`
run uses the same row-stride-128 sampled cuts and history relaxation as the
prior baseline.

I added an optional necessary shape constraint for the final column sort:
row occupancies are nonincreasing, so cumulative profile counts are concave
at equally spaced row boundaries. The small sorted witness satisfies it with
zero residual. With this constraint and `1/1672` local defects, the
row-stride-128 MILP again has a zero-wrong incumbent; after 120 seconds its
dual bound permits at most 579 wrong keys (7,410 nodes, gap `0.00337`). A
row-stride-64 continuous LP solves optimally but still admits 587.284 terminal
wrong keys; its stage-1 threshold defect is 483.57 (alignment 295.12 plus
within-bag 188.45). Thus sampled column-profile shape alone does not close the
relaxation. The corresponding row-stride-64 MILP is unusable: HiGHS reported
infeasible even though the independently checked sorted witness satisfies all
equalities, inequalities, bounds, and integrality exactly.

Thus the variance allowance is representable in the existing recurrence
screen, but this marginal tightening does not eliminate the alignment
witness. It is not a fixed-network counterexample or an all-cuts induction
failure: the model is still an integral selected-cut flow. Reproduce by
replacing `--local-cut-defect-fraction 1/800` with
`--local-cut-defect-fraction 1/836` in the command in
`D2-DISTANCE-TAIL-PERIOD-GATE.md`.

## Gates before using this in the global proof

1. Formalize the deterministic clip/Lipschitz/Cauchy transfer, including the
   ragged live-mask version and both key orientations.
2. Prove a fixed `m=8192` two-round core has `A_w <= Gamma*n` for every binary
   input, with an explicit `Gamma` that leaves a useful port budget. The
   random expectation recurrence is not this theorem; obtain a uniform tail
   bound over input profiles or a direct deterministic certificate.
3. Show the reference port map `P_0(H)` agrees with the D2 child-rank target,
   including the fixed-mask boundary mismatch and all partial/ragged ports.
4. Replace the scalar sender constraints in the global rank recurrence with
   these coupled port-map constraints, then test the all-depth invariant and
   terminal exact-count condition. A positive finite relaxation witness under
   this stronger interface would reject this route before more Lean bridge work.

The lemma supplies a concrete route to constrain the input/output rank-profile
correlation missing from the current selected-cut LP. It does not yet improve
the proved coefficient: `273` remains conditional on the provider, D2 flow,
global recurrence, and terminal proof.

## Sparse prefix-area cone screen (2026-10-25)

The aggregate bound above can be applied to sampled cuts without adding an
auxiliary defect variable at every row. Since `d(r)` is `n`-Lipschitz, a
sampled defect `D` forces area at least

```text
g_R(D) = D + 2 * sum_(s=1)^R max(0, D - s*n)
```

within radius `R`. For sampled centers more than `2R` apart these cones are
disjoint, so their costs sum to at most the global `53*n` area budget. The
screen uses the history lower bound `Hlo` in each defect and the profile
concavity implied by final column sorting. For stride 1 it uses the direct
signed sum of all lower-bound defects, avoiding per-cut epigraph variables.
The `d2_port_variance_transfer_check.py` audit checks 7,239 small cone cases.

The continuous depth-2, scale-8192 screens with `Gamma=48`, local prefix cap
`1/1672`, history/cardinality relaxations, and column-profile concavity admit
these terminal wrong-mass optima:

| Row stride | Variables | Terminal wrong mass |
|---:|---:|---:|
| 128 | 7,180 | 388.69 |
| 64 | 14,156 | 296.52 |
| 32 | 28,108 | 220.78 |
| 16 | 56,010 | 149.42 |
| 8 | 102,611 | 103.84 |
| 4 | 151,781 | 68.19 |
| 2 | 250,094 | 42.66 |
| 1 | 409,846 | 37.44 |

These are optimal values of finite continuous relaxations, not fixed-network
sorting failures. The steady decrease suggests sampling granularity matters;
the full-row solve is still positive, so these area and concavity constraints
alone do not certify purity. The stride-1 run was optimal (HiGHS), with 131,485
equalities, 1,302,552 inequalities, 9 area-cone constraints, and 73,719
profile-concavity constraints; primal residual was `6.4e-10`. Its stage-1
prefix defect was 65.94, and stage 2 ends with 37.44 wrong mass (35.78
cross-bag alignment and 29.99 within-bag defect in the threshold-flux identity).
The solution has an inversion-proxy value above 100,000, so this is a loose
relaxation witness rather than an actual low-inversion trace. Sorting each
native interval alone would not fix its wrong mass: the outstanding contract
is to route the interval counts to their exact global ranks. A terminal repair
is useful only if it establishes that exact-count/address contract at a
schedule-priced cost. Simply increasing row-cut sampling is no longer the
explanation. Even a zero optimum would only certify this relaxation under the
assumed `Gamma=48` provider, not the provider or global all-depth recurrence.

A sensitivity run at the tighter but still unproved `Gamma=32` gives terminal
wrong mass `53.36` at stride4 (151,781 variables; optimal HiGHS LP). Its stage-1
prefix defect is `160.27`, and stage 2 has defect `120.46` split into `44.84`
cross-bag alignment and `75.62` within-bag defect. This improves on the
`Gamma=48` stride4 optimum `68.19`, but does not close the relaxation. The
fixed-core search maximum `23.41` variance per column makes `Gamma=32` a
plausible research target, not a justified universal cap.

## Aggregate port-l1 LP gate (2026-10-25)

`coupled_rank_lp.py` now adds the partition-level constraint
`sum_i |P_i-P0_i| <= sqrt(2*Gamma)*columns` for every active sender covered by
the variance cap. It uses exact selectors for `min(H,s)` at port boundaries
and a rational upward approximation to the square root. The exact checker
passes 2,654 small ragged partition cases in addition to the earlier port,
prefix, and cone checks. At `Gamma=48`, stride4, with the prior `1/1672`
pointwise cap, history/cardinality relaxations, and profile concavity, the
optimal terminal wrong mass decreases from `68.19` to `60.66` (151,883
variables, 33,181 equalities, 399,522 inequalities; primal residual
`2.04e-10`; sorted-path witness residual zero). The constraint adds nine
sender-level inequalities. It improves the interface but does not prove
terminal purity; additional gate comparisons are below.

Removing the pointwise `1/1672` cap, along with its history/cardinality
relaxation, while keeping `Gamma=48` area cones, complete port-l1 constraints,
and profile concavity leaves the optimum unchanged to `3e-11`:
`60.66012592634` wrong mass. HiGHS is optimal with the same 151,883 variables
and 399,522 inequalities; the sorted witness satisfies all constraints, and
primal residual is `3.8e-10`. Thus the pointwise cap does not explain the
remaining relaxed alignment on this gate.

With the area cones removed but the same `Gamma=48` aggregate port-l1 bound
retained, the optimal wrong mass is `705.453048` (115,037 variables, 33,181
equalities, 362,667 inequalities; sorted witness residual zero; primal
residual `8.0e-11`). With neither variance-derived constraint, the baseline
optimum is `8,501.737179`. All three are continuous, selected-cut relaxations.
The comparison shows the area profile carries most of the tightening, while
aggregate port coupling is still valuable; neither closes exact terminal
rank assignment. The next proof interface should preserve both the area shape
and l1 port coupling while using D2's endpoint reserves to absorb leakage.

## Numerical match to the D2 reserve budget

The proposed all-depth D2 allocation bound is `a/c<=279/256` for ordinary
senders, where `a` is sender allocation and `c` is its flow capacity. If a
`Gamma=48` variance provider and the exact reference-port/rank identity both
hold, then

```text
sum_i |P_i-P0_i| / c
  <= (279/256) * sqrt(96) / 8192
  < 1/512,
```

since `279^2*96 < 4096^2`. The total positive leakage is half this l1 bound,
so it is `<c/1024`. This is smaller than the saturated-aware flow's sender
deficit cap `c/512`, quota cap `c/256`, and endpoint reserve `c/128`. The
scale match is promising: the aggregate local rank error is within the
existing reserve budget without imposing a separate `1/1672` cut cap.
However, the flow `G,L,H` invariant has not yet been connected to class-count
misrouting, and the all-depth `279/256` allocation theorem is itself open.
Proving that rank-error absorption bridge is now the most promising next
mathematical step after the fixed-core provider and reference-map identity.

## Capacity-doubling rank-error induction target

For a rectangular sender, let `E=|H-H*|` be its input count error for one
threshold, and let `H_i*` be the exact target count in child interval `i`.
If the reference port map is the exact rank split, then
`P0_i(H)=clip(H-u_i,0,v_i-u_i)` and `H_i*=P0_i(H*)`. Therefore

```text
|H_i-H_i*|
  <= |P_i(H)-P0_i(H)| + |P0_i(H)-P0_i(H*)|
  <= Delta + E,
```

where `Delta=sum_i |P_i-P0_i|` includes all children and fringes. Suppose the
sender is covered by `A_w<=48*n` and `a/c<=279/256`; the numeric result above
gives `Delta<c/512`. If the parent rank error invariant is `E<=c/512`, then
each child error is `<c/256`. The D2 schedule has
`c_child(t+1)=2*c_parent(t)`, so this is exactly
`c_child(t+1)/512`. Thus the normalized per-active-node rank-error allowance
is preserved in one ordinary parent-to-child transition. This capacity-
doubling induction avoids adding a fixed error over all `O(log N)` stages.

This argument is conditional and narrower than the full sorting proof. It
needs the rank/count error to be represented by the saturated-aware tree
state, an all-depth `279/256` schedule theorem, the exact ragged port map, and
role-specific cases for `topDesc`, `botRise`, inactive intervals, and the
terminal frontier. The numeric fit indicates that the existing D2 reserve
invariant may be the right state; it does not establish that `G,L,H` absorb
these key-count errors or that every off-spine terminal block is pure.

The generic arithmetic interface is now kernel-checked in
`D2RankAlignment.lean`:
`child_count_error_le_parent_add_transfer` packages the two directional
triangle inequalities, and `child_count_error_preserves_doubled_capacity`
proves the normalized `1/512` budget survives when child capacity is twice
parent capacity. These lemmas are deliberately independent of the flow tree.
The fixed-interval Lipschitz fact is now kernel-checked in
`D2RankAlignment.lean`: `prefixIntervalMass_count_change` proves the reference
count changes by at most the parent-prefix change for every valid interval,
including ragged ones, and `ragged_child_count_error_le_parent_add_transfer`
composes that fact with the local transfer-error hypothesis into the desired
one-step recurrence. The missing bridge is now specifically semantic: for
each threshold, prove the concrete sorter satisfies the two transfer
inequalities and show the resulting errors are represented by the reachable
flow state through all role transitions. No such bridge is claimed yet.

The terminal arithmetic is kernel-checked as
`exact_count_of_small_capacity`: if the normalized error satisfies
`512*error<=capacity` and the integer capacity is `<512`, then the actual and
ideal counts agree exactly. This makes exact terminal rank counts follow
automatically if the all-depth invariant reaches a node below that capacity;
whether the concrete D2 schedule and its terminal network provide that
endpoint is still open.

The active schedule does not reach `capacity < 512`, but its terminal rank
budget is materially smaller than a scale-8192 reading suggests. Substituting
`t=tfD2(d)=3*d-14` into the actual `active` inequalities gives the unique
terminal active level `i=d-4`; the exponent in
`d2FlowCandidateCapacityExponent` is then25, while the native physical
capacity `capacityD2` is4096 (`d2FlowCandidateCapacity` includes the scale
factor8192). Hence a physical integer rank error satisfying
`512*error<=capacityD2` is at most8 keys per threshold at the last active
sender. An integer sweep over `d=7..10000` confirms the formulas; the exact
Lean endpoint lemma is being added. This corrects the previous statement that
the terminal allowance could be thousands: that counted the scaled capacity
without dividing by8192. The rank-to-flow scaling bridge is still open, and
the remaining eight-key error can include outsiders from distant rank
intervals, so a priced terminal repair is still required unless a stronger
invariant makes the counts exact.

The existing selected-cut LP clarifies why exact sorting of each terminal bag
is insufficient: its `terminal_wrong_mass` objective is computed from the
bag's threshold count compared with the target interval count. Any internal
sort preserves that count, so it leaves this address error unchanged. A tail
repair must exchange keys across neighboring bags (or prove the count error
zero); merely replacing the last local sorters by exact bag sorters cannot
close this gate. A grouped merge/readdressing gate should therefore measure
error after aggregating contiguous terminal bags, and price the depth of those
cross-bag comparators.

## What a terminal per-bag count bound says about the keys

There is a sharper exact consequence of a uniform terminal count-error bound.
Let a sorted terminal bag have `a` keys and target rank interval `[L,L+a)`,
and suppose for every threshold `x` its actual below-threshold count differs
from the count in that target interval by at most `E`. For a key at local
index `j` whose global rank lies inside the target interval, use that key as
the threshold: its rank differs from `L+j` by at most `E`. A threshold at the
first target key shows that at most `E` bag keys lie below the interval, so
they occupy the first `E` positions. If a next global rank exists, using
that next key as threshold gives the analogous last-`E` bound for keys above
the interval; if the target interval ends at the global maximum, there are no
such keys. Thus all keys whose ranks belong to other bags are confined to the
first or last `E` positions, while in-interval keys have at most `E` local
rank displacement.

The count-to-position implications are kernel-checked in
`D2TerminalProfile.lean` (`in_interval_position_close`,
`below_interval_count_le`, `above_interval_count_le`, and
`total_outside_interval_count_le`). In particular, at most `2E` terminal
keys lie outside the bag's target interval. Their input is the per-threshold
profile bound itself; no D2 provider or reachable-state bridge is assumed by
those lemmas.

The stronger lane statement is now kernel-checked in the same module.
`middle_position_in_interval` and `middle_position_rank_close` show that every
bag key at local rank `j` with `E<=j` and `j+E<a` belongs to the target
interval and differs from target rank `L+j` by at most `E`.
`adjacent_middle_positions_strict` then proves that, for adjacent target
blocks of width `a>2E`, the keys at any common middle position are strictly
increasing across the blocks. At the candidate terminal values `a=4096`,
`E=8`, all but the first and last eight lanes therefore have this vertical
order. This reduces the direct-cleanup problem to the two 8-lane edge bands
and their interactions with the ordered middle; it does not yet give a
network that sorts those exceptional streams.

This is stronger than a bound on total wrong mass: it separates bounded local
displacement from the at-most-`E` long-range outsiders at either edge. It is
not itself a cleanup theorem. The edge outsiders may belong to distant target
intervals, and correcting them can shift interior keys by up to `E`; sorting
only the edge wires once is therefore insufficient. A terminal construction
for the 273 coefficient candidate must sort this constrained family of
blockwise near-identity profiles, with the edge outliers included, in depth
at most `27*log2(N)+o(log N)` (or improve the prefix coefficient enough to
enlarge that budget). The D2 rank-error invariant would supply `E<=c/512`
only after its still-open provider and schedule bridges are proved.

### Exact core-and-edge reduction

There is a sharper way to state the remaining terminal network problem. For
each sorted bag of width `B`, retain only local positions `E,...,B-E-1` as
its core. The position lemmas above put every core key in its own target rank
interval and within `E` ranks of its local position. The last core key in one
bag therefore has rank at most the last rank of that bag's target interval;
the first core key in the next bag has rank at least the first rank of the
next interval. Since each core is internally sorted, the concatenation of
all cores is globally sorted.

The pairwise order assertion is now kernel-checked as
`adjacent_core_positions_strict` in `D2TerminalProfile.lean`; it allows the
two retained keys to occupy different local positions. Chaining it over the
bags gives the stated sorted-core decomposition.

The removed keys are exactly two sorted runs of length `E` per bag (the low
and high edge bands). Thus, conditional on the per-threshold profile bound,
terminal sorting reduces to sorting `2m` sorted runs of length `E`, followed
by one ordinary merge of that sorted edge stream with the already sorted
core. At `B=4096,E=8`, this is `2m` runs of length8. This reduction handles
the interaction between edge outliers and the middle without assuming the
outliers are local in global rank. It does not price the run-sorting network:
pairwise Batcher merging gives a quadratic-in-`log m` depth by the direct
recurrence, so an explicit low-constant linear-log merger for these short
sorted runs is still required to fit the 27-depth-per-log budget. The profile
invariant and its reachability proof also remain open.

### Long-range swap obstruction to the inversion cleanup gate

The uniform profile bound `E` does not imply the sublinear inversion
hypothesis used by `INVERSION-LOCALIZATION-GATE.md`, even when `E=1`. Let
`N=mB`, `B=4096`, and partition ranks into `m` target blocks of size `B`.
Make the first sorted bag contain ranks `1,...,B-1,N-1`, the last contain
`0,N-B,...,N-2`, and every middle bag its exact target interval. Each bag's
threshold-count profile differs from its target by at most1 at every
threshold. Yet the locally sorted concatenation has `2(N-B)-1` inversions:
the misplaced maximum precedes every key outside the first bag, and the
misplaced minimum follows every key outside the last bag, with their mutual
pair counted once. This is linear in `N`, so no `theta<1` inversion bound
follows from the terminal per-bag profile contract alone. The example is an
abstract terminal configuration, not a reachable D2 trace. A successful
cleanup must exploit additional reachability/distance structure or directly
sort this long-range edge-outlier family within its priced depth.

### Reduced grouped-frontier gate

I screened `terminal_error_level` at every level of the depth-3, scale-8,
row-height-8 selected-cut model, with ordered prefixes, root-tail history,
all-row dominance, and integral count/profile variables. HiGHS returned
zero-gap optima `0, 0, 1788, 0` at levels `0,1,2,3`, respectively; the
level-2 primal has zero exact equality, inequality, and integrality residuals.
So even this small model has a specific intermediate frontier whose grouped
rank error survives the relaxation, while the other frontier objectives can
be made zero in their separate optimizations. This is not one common trace,
does not encode the fixed separator, and has no local-provider constraints;
it only warns against assuming grouped error decreases monotonically with
frontier level. Reproduce by running the integer `coupled_rank_lp.py` gate
with `--depth 3 --scale 8 --row-bits 3 --params 3 3 2 --row-stride 1
--ordered-prefix --root-tail --all-row-dominance --integer --terminal-error-level L`
for `L=0,1,2,3`.

A second exact encoding represents each residue round by interval endpoints:
if `E_x` counts intervals ending at x and `F_x` is the coverage load, then
`F_0` is the number of intervals covering zero and
`F_x=F_(x-1)+1-E_x` for `x=1,...,63`. The cyclic slope is handled by
conjugating with its column dilation. This replaces the direct 4096 threshold
comparisons per round with endpoint counts and a cumulative recurrence in the
QF_BV model. The recurrence matched direct coverage on 3,000 random residue
profiles (widths8,16,64), and the all-separations width8 witness gate passed.
At width64, the four-round range-12 query still timed out at120s, so this
encoding is not yet a certificate method.


### Fixed-core port budget (2026-10-26)

`area_to_ragged_port_l1_le_416` converts any centered area bound
`(1/2) * sum_c (x_c - mean(x))^2 / 64 <= 169/8` into an aggregate local
port deviation at most416. Its columns all have capacity4096; the port cuts may
be any complete monotone interval partitions of those columns. The specialized
`fullHeightTwoShuffle_ragged_port_l1_le_416` instantiates this for the physical
slope-(35,25) core, using the kernel-checked full-height area theorem and its
output-capacity lemma. The reference is the uniform-density profile, not yet
the exact rank-prefix profile on ragged fixed masks. For the rectangular
row-major reference, the separate total-variation calculation gives an
additional mismatch allowance32 at64 columns, but that correction still needs
a Lean proof and actual-flow wiring.

### Terminal count error does not imply local seam cleanup

The terminal bound of at most eight count errors per threshold is not enough
to justify sorting only the 16 positions at each adjacent seam. For block
width `A`, take three sorted blocks with target intervals `[0,A)`, `[A,2A)`,
`[2A,3A)` and rank sets

```text
B0 = {0,...,A-2} ∪ {2A}
B1 = {A,...,2A-1}
B2 = {A-1} ∪ {2A+1,...,3A-1}.
```

They partition `{0,...,3A-1}`. Each block's threshold-count profile differs
from its target interval by at most one at every threshold, yet the largest
key in `B0` exceeds every key in `B1`. Sorting only the last/first eight
positions at each seam cannot move that key across the whole middle block.
This example already works for `A=8` and scales to the actual terminal width
`A=4096`.

Thus the eight-key-per-threshold bound does not close terminal cleanup with a
constant-width local repair. It needs a stronger invariant bounding how far
outsiders can lie from their target intervals, or a priced network that routes
sparse long-distance outsiders across many terminal blocks. The current D2
count-error recurrence supplies neither distance guarantee.

## Weighted spatial transfer from a single fixed core (2026-10-28)

`D2WeightedPortDefect.lean` proves a stronger weighted interface for the
range-13 full-height two-shuffle core. At every independently chosen cut in
each of the 64 columns, the aggregate prefix count differs from the exact
rank-column prefix by at most 896 wires. Discrete summation by parts then
shows that for any sequence of monotone per-column cuts and any rational port
weights `w`,

```text
|sum_i w_i * signed_port_error_i|
  <= 896 * (|w_last| + |w_0| + sum_i |w_i - w_(i+1)|).
```

This is kernel-checked and is useful when candidate spatial-potential weights
have small total variation: it prices the fixed core's contribution directly
by that variation instead of charging its full 448 l1 allowance at every
port. The theorem accepts arbitrary monotone per-column cuts, so the flat
row-major cut map can be substituted once its scheduler-level interpretation
is established. It does not prove that the D2 address map realizes such a
potential, nor that the potential contracts or remains bounded through all
stages. The global recurrence, root initialization, terminal seam control,
and end-to-end depth proof for coefficient 300 remain open.

The same theorem now adds over any finite family of sender tiles with tile-dependent cuts and weights (`tiled_weighted_column_port_error_le_896_variation`). For a proposed receiver potential `W`, instantiate the source-port weight as `W (outputCell tile port)`. This reduces the fixed-core contribution to the explicit sum of endpoint magnitudes and adjacent potential differences along each tile's output-port map. The remaining mathematical gate is to define that map from the actual recursive D2 schedule and prove its variation contribution is absorbed by the chosen global potential; the current theorem does not supply either fact.

## One mixed tile transfer (2026-10-28)

`D2BandRepairInversion.lean` now states the local 832 bound as Hamming distance from the sorted Boolean word with the same exact zero count (`physical_twoGridRepair_hamming_le_832`). `physical_twoGridRepair_zeroCount_eq` verifies that the fixed comparator network preserves the tile mass, so this bound is relative to the actual incoming rank-count error.

`D2SparseMixedTileTransfer.lean` combines that provider with the fact that a monotone rank partition has at most one mixed interval. For any family of full 4096-by-64 tiles partitioning rank space, the sum of post-repair Hamming errors from the globally sorted threshold word is at most the incoming tile-count mismatch plus 832, independent of the tile count. The focused Lean check passed by building the module into the best-package Lean environment.

The result is conditional on full-sized tiles and a rank-ordered partition; a partial-tile version and the exact active-tile map of the D2 schedule remain open. It bounds Hamming mismatch, not positional distance or inversions. Thus it does not close the all-depth spatial recurrence or establish the coefficient-300 theorem.

`D2Stage14LevelFourReserve.lean` now proves a concrete schedule fact: after
Stage 13, the actual level-four endpoint deficits at both extreme children
cover the Stage-14 level-four capacity with the required factor 128. The proof
uses the level-five bottom-descending quota and the explicit Stage-13-to-parent
projection; it is more than the earlier quota arithmetic, but still proves
only endpoint reserves. The level-four sender's balance/deficit contract and
the all-depth recurrence remain open.

`D2Stage14MidBudgets.lean` closes the exact local arithmetic margin for the
level-four mid gate: Stage 14's capacity and quota are both twice their
Stage-13 level-three counterparts, its quota satisfies the 1/256 cap, and
`512 * (G + oldQuota/2) <= newCapacity` whenever the old sender had
`512 * G <= oldCapacity`. This is the tight deficit estimate needed for the
new child roots; the schedule-level derivation of the full sender contract,
especially aggregate allocation and the recursively valid children, remains.
The same file also packages the generic sender step: any valid Stage-13
level-three mid input produces balanced level-four child roots whose deficits
fit the Stage-14 level-four cap. This closes the balance/deficit part locally;
instantiating it at every actual node and proving the allocation and recursive
input clauses are still needed for the full level-four gate.
`D2Stage14ActualLevelFourBalance.lean` now supplies that all-path
instantiation: every actual level-four node in the Stage-14 input tree is
balanced and satisfies its 1/512 deficit bound. The remaining level-four gate
conditions are the quota/aggregate-allocation inequalities and recursive
level-five input contracts; this does not yet establish the Stage-14 invariant.
The checked `d2FlowCandidateStage14_levelFour_allocation_of_endpoint` lemma
then proves the aggregate allocation inequality from just that deficit bound
and one endpoint reserve: the endpoint's `capacity/128` lower bound exceeds
the root deficit plus the mid quota. The actual pathwise assembly of this
local implication is still outstanding.

`D2Stage14ActualLevelTwoInputs.lean` and its run adapter prove the complete
level-two gate from the Stage-13 level-one contracts, and
`D2Stage14ActualRootInputs.lean` now assembles the complete Stage-14 root
input contract. The level-one nodes are inactive and inherit those level-two
contracts; the root's zero deficit follows from the Stage-12 reset preserved
through Stages 12 and 13, and its balance follows from the invariant. The
focused Lean compilation produced `D2Stage14ActualRootInputs.olean` on
2026-10-29. This closes Stage-14 input assembly. The next paragraph records
the checked transition to the Run-15 invariant; an all-depth continuation,
global spatial rank/inversion recurrence, and terminal cleanup required for
coefficient 300 remain open.
`D2Stage14PreservesInv.lean` then applies that complete root input contract to
prove the actual Stage-14 transition preserves the invariant, yielding the
Run-15 invariant. The Lean check completed successfully on 2026-10-29 and wrote
`D2Stage14PreservesInv.olean` to the ignored helper check directory. This is a
finite-stage extension; it does not yet provide an induction for arbitrary
later stages.
