# Sub-300 D2 handoff

State checked against the `sub300-structural` worktree on 2026-11-01. This is
research status, not a proved improvement to the repository's accepted bound.

## Latest focused checkpoint (2026-11-01)

`D2BotRiseStaticFit.lean` now proves that every candidate-run `botRise`
snapshot has clamped static-hole fit both before and after the update, for any
selected path satisfying the schedule window. Before the update, the saturated
children's clamped empty-hole markers remain ordered in the valid parent
interval. It also proves the current sender bag has exactly `8 * width - G`
wires, its flow allocation. After the update, the updated parent's physical
static sender bag is empty: child preservation makes its post-step deficit
equal full capacity. The proof uses
`D2BotRiseRunBridge.lean` to identify the role and
`D2PathNativePreservation.lean` to preserve child roots through callback
history. Current-source focused checks pass for `D2PhysicalBagState.lean` and
`D2BotRiseStaticFit.lean`. The file also proves the allocation is even at every
candidate path, then applies `bot_rise_sender_piece_partition` uniformly to
any finite sender set with the required flow-allocation cardinality. This
supplies the bot-rise local routing contract for the dynamic-set layout; it
does not identify routed pieces with next-stage receiver sets or prove the
receiver-cardinality recurrence. Its output also prices the bot-rise parent
piece exactly at the allocation and proves all eight child pieces empty.

`D2DynamicSenderNode.lean` now also proves
`d2OrdinaryRankSenderPorts_of_stage_inputs`: for any ordinary active node and
any sender set with the required flow-allocation cardinality, its stage-input
contract and flow invariant imply the complete disjoint port partition and
exact parent/child port sizes. The proof derives both endpoint-front bounds
from the 1/512 deficit, 1/256 quota, and endpoint reserves; it uses no static
sender-bag fit. Together with the bot-rise adapter, this advances the
all-role dynamic-layout gate. The top-descending arbitrary-set adapter now also supplies the exact port
sizes: zero to the parent and each child deficit drop to its child. Thus all
three active-role cases (`topRise`/`mid`/`botDesc`, `topDesc`, `botRise`) have
local arbitrary-set partition and port-size providers under the flow-size
contract. The next construction gate is to assemble these local providers in
the flat layout and prove its receiver bags have the post-stage flow
allocations, including inactive nodes and overwrite cases. The spatial profile
recurrence remains the main analytic blocker.

`D2DynamicSenderCardinality.lean` now packages the inactive internal-node
equation as `d2FlowTreeAllocation_after_inactive_node_incoming_ports`: after
the recursive child update and a parent overwrite, the receiver's allocation
is its old allocation plus the incoming parent down-port and its child
up-ports. The no-overwrite specialization is
`d2FlowTreeAllocation_after_inactive_node_ports`. Focused current-source
checks pass for both `D2DynamicSenderCardinality.lean` and its downstream
`D2DynamicSenderNode.lean`. This closes the abstract inactive-receiver
arithmetic, but does not prove the physical routed pieces have those
widths/tags or identify a receiver bag with the flow allocation.

`D2DynamicSenderNode.lean` now lifts this equation to the recursive set
representation. `d2SenderLayoutStage_inactive_root_card_eq_allocation` proves
the retained root bag has the updated flow allocation when child up-ports
have their prescribed widths and are disjoint from each other and the root
bag. `d2SenderLayoutStage_inactive_child_overwrite_card_eq_allocation` adds
the parent's down-port and proves the overwritten child's root bag also has
its updated flow allocation. These are conditional layout adapters: actual
candidate port widths and global disjointness/coverage still need deriving
from the node routing contracts. The focused current-source check passes.

The same module now proves `d2SenderNodeLocalPiece_partition_contract` and
`d2SenderNodeRoute_preserves_partition_of_active_contract`. Thus, from a
partition of the current sender bags and a local parent/eight-child partition
at each active node, the flat destination routing partitions all wires at the
next stage (with the external boundary bucket included). Inactive-node local
contracts are automatic. This composes the already-proved role-specific
arbitrary-set partitions into a stage-wide conservation theorem; the candidate
all-stage source-size provider and the boundary-empty instantiation remain to
be proved. Focused current-source check passes.

## Candidate and price

The strongest deterministic candidate is the `(3,3,2)` D2 schedule with the
reflected 4096-by-64 physical core and two-grid repair. The fixed comparator
network has checked depth at most 276 and, for every Boolean input, puts each
threshold's errors inside a common interval of at most 832 wires. The schedule
rate is `5/6`, so the conditional coefficient is `276 * 5/6 = 230`, leaving
70 coefficient units for asymptotic cleanup and other costs. This is a local
price only; no limsup bound below 300 is proved.

## What is checked

- `D2ReflectedPhysicalPack.lean`, `D2PhysicalPackTwoGrid.lean`, and
  `D2BandRepair4096Network.lean` give the physical fixed-tile network, its
  Boolean dirty-band contract, and the depth-276 price.
- `D2LocalRankDisplacement.lean` proves a local 832 rank-displacement bound
  when the sender input has the required within-column order.
- `D2PhysicalProfileGlobalTransfer.lean` gives an aggregate 448-per-tile
  profile-error transfer for arbitrary monotone receiver cuts. The abstract
  doubling arithmetic is checked in `D2GeometricProfileBudget.lean`.
- `D2StaticWireSets.lean`, `D2VariableTilePhysicalFlowTransfer.lean`, and
  `D2NativePathIntervals.lean` provide pieces of cell, rank-slice, and
  boundary geometry. They do not identify the actual all-stage profile map.
- `D2RoutedMass.lean` proves both true- and false-mass receiver partition
  identities for disjoint sender pieces. The false form is ready for the
  prefix-oriented profile route; neither form yet identifies the physical
  profile slices with the concrete schedule pieces.
- `D2ProfileOrientationGate.lean` proves the fixed core's `bottomUnaryProfile`
  has true bits in the bottom `height` rows and that physical row interval
  `[lo,hi)` has count
  `prefixIntervalMass height (4096-hi) (4096-lo)`. It also gives a
  one-true witness that the unreflected expression
  `prefixIntervalMass height 0 64` is not the count in the top physical
  64-row cell.
- `D2FalseProfileTransfer.lean` now proves
  `reflected_core_false_exact_rank_port_error_le_448`: for arbitrary legal
  input column counts, the reflected physical core's false-count profile has
  range at most 13 and incurs at most 448 exact-rank error over any monotone
  full-height port cuts. `reflected_core_false_total_eq_input` proves the
  core preserves total false mass, and the `_of_input_mass` wrapper supplies
  the local port theorem from the sender's input false count.
- `D2FalseClippedTransfer.lean` proves the full-height clipped extension and
  its arbitrary-tag composition: for any global monotone rank partition and
  receiver tags, the grouped false-profile error is at most parent mass error
  plus `448 * tiles`. This composes actual clipped cuts with the core provider.
  It does not yet show that a candidate-run sender's tags or child ideal
  masses are the ones passed to this theorem. Ragged source heights below 4096
  are also not covered by this extension.
- Stage-specific reserve/invariant proofs reach the Run-20-to-Run-21
  transition. `D2AllStageInvariant.lean` lifts a provider to all stages
  conditionally. `D2AffineCoreAllStages.lean` now proves the abstract flow
  provider at every stage; the missing provider is the construction-specific
  link from physical sender profiles and tags to that flow state.

These are source-level results with focused Lean checks recorded in the
historical log. The moved `.olean` files are caches, not verification evidence;
rebuild affected modules from current source before relying on them.

Focused source rebuilds on 2026-10-31 passed for
`D2VariableTilePhysicalFlowTransfer.lean`, `D2LocalRankDisplacement.lean`,
`D2CrossingToDisplacement.lean`, `D2RankDisplacementComposition.lean`, and
`D2BlockSortDisplacement.lean` via `check_prefix_flux_lean.py`. This verifies
the cited static-cell/port, local 832-displacement, abstract crossing,
composition, and sender-set lemmas from current Lean sources. It does not
verify a construction-specific all-stage hypothesis or close either global
transition gate.

The same focused checker now passes `D2ProfileOrientationGate.lean`, which
kernel-checks the reflected-cut formula and the one-true mismatch witness.
It also passes current-source rebuilds of `D2BandRepair4096Network.lean`,
`D2LiftedShuffleBridge.lean`, `D2ReflectedPhysicalPack.lean`,
`D2Range13PortError.lean`, and `D2FalseProfileTransfer.lean`. This rebuilds
the false-profile 448 port theorem and its direct dependencies. The theorem
resolves the local row-orientation/provider issue; it does not identify the
schedule's actual sender cuts, tags, or output mass.
The focused checker also passes the updated `D2RoutedMass.lean` with its
false-mass receiver partition identity.
Current-source focused checks additionally pass `D2ClippedFlowProfileTransfer.lean`
and `D2FalseClippedTransfer.lean`; the former exposes the existing rational to
integer error conversion lemma, and the latter proves the clipped full-height
false-profile transfer for arbitrary tags.
`D2TreePathGeometry.lean` also kernel-checks the height-zero branch needed by
the recursive core-provider transition: a full-depth path lands at a leaf,
where the affine-core predicate has no terminal obligations. It also proves
the positive-height path transition and its root specialization. Now
`D2AffineCoreAllStages.lean` combines this with checked snapshots 0 through 3
and invariant bootstrap to prove the abstract affine-core provider and tree
invariant for every stage and dimension `d >= 7`. A focused current-source
rebuild passes. This closes the abstract flow-reserve induction; it does not
identify physical sender counts or receiver tags.
`D2AllStageTwoFrontGate.lean` additionally proves zero aggregate ideal-prefix
overrun and per-child domination of exact-prefix mass by two-front reserves
for every active ordinary candidate path. It also proves
`d2FlowCandidateRun_active_ordinary_mass_overrun_le_transfer_atPath`: if the
eight actual grouped child counts have aggregate L1 error at most `E` from
their exact-prefix ideal counts, and those ideal counts are bounded by the
corresponding rank-interval masses, then actual overrun above the next
two-front reserves is at most `E`. A focused current-source rebuild passes.
This provides the one-sided analytic interface, but not its physical count
and rank/tag hypotheses.

## Spatial weighted local bound (2026-10-31)

`D2WeightedPortDefect.lean` now improves the fixed-core row-cut discrepancy
from 896 to 448. The proof uses the same per-column height error bound 14
(total L1 at most 896), then uses equality of actual and ideal total mass to
halve either directional prefix error. Summation by parts propagates this to
`fullHeightTwoShuffle_weighted_column_port_error_le_448_variation` and its
tiled counterpart, with charge `448 * total weight variation` instead of 896.
A focused current-source Lean rebuild passes. This is a local fixed-core
improvement; it does not identify the schedule's spatial weights or prove an
all-stage recurrence. The exact physical transition remains the top priority.

## Main unresolved gate

The fixed-core-to-schedule **count identity** is still open. Some of its
address geometry is already exact, so do not redo it:
`D2StaticWireSets.lean` proves
`destinationPiece_staticHoleList_child_inter_cell`, which identifies the
intersection of an actual child rank-port piece with a destination cell as
the corresponding ordered gap-run rank fragments. In
`D2VariableTilePhysicalFlowTransfer.lean`, `staticGapRankPort_cells` and its
injectivity theorem show that aligned 4096-rank pieces of such a sender map
to distinct whole physical cells. The sender-port boundaries are proved
grid-aligned conditionally from the stage invariants.

The local orientation/provider and its full-height clipped arbitrary-tag
composition are now available. Do not redo the complete-tile local
count/tag identity: `D2ClippedCellRankInterval.lean` theorem
`reflected_core_ordinary_child_grouped_count_eq_physical` proves it for an
arbitrary sender set, quota, eight child widths, complete sender-rank tiles,
and uniform child-port tags. Its cuts are exactly
`d2SenderPortBoundaryNat`; `d2FlowStage_regular_sender_port_length` supplies
their ordinary-stage lengths. This does not provide the reachable Boolean
source profile, its macro parent-error bound, the ragged rank suffix, or the
identification of a relaxed sender set with the concrete recursive schedule.

The next analytic gate is a reachable spatial profile invariant: define the
Boolean false-mass profile on each actual static sender bag in canonical rank
order, prove its startup base, and derive a one-stage update that bounds the
macro parent discrepancy together with the local `+448` transfer. The state
must retain enough rank-distance information to support all-depth contraction
and terminal cleanup; existing selected-cut LPs do not establish this for the
fixed network. Include clipped final tiles and startup/exceptional roles in
the transition. Exact equality between
single-prefix masses and two-front child deficits is false in general and is
not required: `D2AllStageTwoFrontGate.lean` proves each ideal exact-prefix
child mass is at most its corresponding two-front reserve for actual
candidate flow states. Its transfer-error theorem means the physical bridge
only needs aggregate L1 error against those ideal child masses; that error
directly bounds reserve overrun. The arbitrary-tag `+448` transfer and parent
mass error are candidate sources for that estimate. A regular sender has ten ordered
ports (two parent halves and eight child intervals), so its cuts are the
eleven boundary positions `0..10`. Extend the count transition to sub-4096
ragged heights, startup, and exceptional intervals. `botRise` static fit and
its empty post-stage sender bag are proved for the candidate run, but its full
physical count transition is not supplied by the full-height lemma.

The corrected arbitrary-root selected-cut LP keeps exact total root mass yet
still admits large terminal error under the current independent tail
constraints. This shows those constraints are too weak; it is not a
counterexample to the fixed network.

### Allocation shortcut checked and rejected

Do not identify a child's post-stage subtree allocation with its previous
allocation plus the parent's down-port width. `d2FlowStage` recursively steps
the child subtree first, then overwrites the child's root deficit using the
parent's cut. The down-port width is exactly old child-root deficit minus new
child-root deficit, but the child's allocation also depends on the recursively
updated descendant deficits. A receiver-mass proof must account for those
descendant updates and the actual tagged address pieces together; the root
deficit or its drop alone is not a receiver's ideal false mass.

### Single-prefix versus two-front profile mismatch

`D2FalseClippedTransfer.lean` compares grouped output false counts with one
single exact-rank prefix per sender. The ordinary flow update is explicitly a
two-front quantity: `d2FlowStage_regular_child_deficit_eq_rank_mass` identifies
each new child deficit with a low-prefix plus high-suffix mass. This is a real
non-equality, but it need not block a one-sided error argument. The checked witness
`D2PrefixTwoFrontObstruction.lean` takes eight size-10 children, `G=5`,
`low=3`, `high=2`, and quota 4. It gives first/last child deficits 5 and 4;
the single-prefix profile of the *post-stage* total mass 9 gives 9 and 0.
However, this is only a comparison of ideal profiles: the actual sender's
Boolean false mass has not been identified with its pre-stage deficit `G=5`.
The flow tree stores deficit data, while the physical provider counts false
wires in source tiles. Thus the witness corrects the profile equality test but
does not establish that the ideal prefix is the right reference for the
physical sender.

`D2FlowRankBridge.lean` now proves the general domination budget: across the
eight children, total positive overrun of the pre-stage exact-prefix mass over
the post-stage two-front reserves is at most
`G - min(G, low + quota/2)`. The tolerant `4096*G <= 23*capacity` contract is too weak for the proposed
per-tile profile recurrence. Candidate capacity is in 8192-unit flow blocks,
while one physical 4096-by-64 core tile is 262144 wires (32 such blocks).
Thus the tolerant estimate `31*capacity/8192` is 992 per physical tile, not
31, and does not fit with the local 448 core error inside the 512-per-tile
doubling budget.

`D2TolerantOverrunScaleObstruction.lean` gives a local witness satisfying
the tolerant predicate: capacity 1048576 (four core tiles), deficit 5888,
quota 3840, and eight children of size 131072. Its first-child ideal-prefix
overrun is 3968 = 992 per tile. This refutes deriving the recurrence from the
tolerant predicate alone; it is not a reachable-run counterexample. The
stronger `8192*G <= 15*capacity` reserve makes the ideal overrun zero because
half the candidate quota is at least `15/8192` of capacity. This implication
is kernel-checked in `candidate_sender_two_front_overrun_zero_of_15over8192`,
and `D2AllStageTwoFrontGate.lean` derives the reserve at every active ordinary
candidate path, then proves each ideal prefix child mass is bounded by its
corresponding two-front reserve. This remains an abstract flow fact; actual
physical source-tile false mass and receiver groups are not yet shown to
instantiate the transfer-error hypothesis.
The weaker strict `512*G <= capacity` reserve gives 32 per physical tile;
either strict bound leaves the local 448 charge within the 512-per-tile
doubling budget.

`D2PhysicalTwoFrontGate.lean` now composes the full-height physical
false-profile theorem with the all-stage two-front gate. Under an aggregate
parent tile-mass discrepancy `P`, exact identification of the eight grouped
child actual/ideal counts, and the one-sided rank-interval hypothesis for
those ideal groups, it proves actual child overrun at most `P + 448*tiles`.
The theorem supports an arbitrary positive number of ordered ports, with the
two parent ends tagged separately from the eight child groups; their error is
included in the all-tag transfer estimate. This is the current
ordinary-sender invariant interface. It does not yet prove the
schedule supplies these hypotheses: the root-to-sender tile mass invariant,
static receiver tags/cuts, and ideal grouped-mass domination remain open;
partial-height and exceptional roles are outside this full-height theorem.
The composition passes a focused current-source Lean rebuild. The next step is
to derive its parent-mass, actual-tag, and ideal-rank hypotheses from one
ordinary sender's static-hole routing geometry.
The rank hypothesis can now be stated in the physical coordinates: ideal
child mass need only be bounded by the prefix mass on the interval shifted by
the sender's left-parent offset. `D2FlowRankBridge.lean` proves that shifting
an interval right cannot increase its initial-prefix mass, and the composition
uses this to obtain the unshifted two-front reserve bound. This removes the
coordinate-shift concern; deriving the shifted ideal-group identity from the
actual tile allocation remains open. `D2ClippedFlowProfileTransfer.lean` now
proves that, within each full-height tile, summing exact-rank cell counts over
the 64 columns of one port equals the prefix mass in that tile's clipped
flattened interval. `D2ClippedTilePrefixAllocation.lean` proves that the
clipped tile intervals partition a global prefix interval, and
`D2ClippedTilePortAggregation.lean` composes the two: when each tile's ideal
mass is the restriction of one global prefix, all exact-rank cells across all
tiles and columns of one port sum exactly to that port's global prefix mass.
`clippedFlowGroupedRank_eq_shifted_child_interval` packages the consequence:
if a receiver tag selects exactly one child port uniformly over tiles and
columns, and its two global boundaries equal the sender-offset flow cuts, its
grouped ideal mass is exactly the shifted flow interval. The next gate is to
prove those tag/boundary hypotheses from the actual static routing, and then
identify physical Boolean tile masses/tags with this ideal model.

Two prerequisites for that gate are now kernel-checked. `D2AllStagePortGrid.lean`
derives the stage-input contract from the all-stage affine-core theorem and
proves that every active ordinary candidate sender has 4096-aligned ten-port
boundaries, at every stage and for every dimension `d >= 7`.
`D2CutAlignment.lean` now projects descendant endpoint alignment to a
concrete positive-depth candidate path, while `D2AllStagePortGrid.lean`
projects the all-stage sender-input contract to any path. In
`D2StaticWireSets.lean`, `d2FlowStageInvInputs_static_holes` no longer assumes
the schedule capacity equals the full native tree capacity: the actual
deficit/quota limits and endpoint reserves directly imply the two-front hole
fit from native child bounds. The exact path-level composition of these facts
is still to be proved. `D2AlignedPortReceiverCells.lean` shows that, given the
static-hole fit and grid premises, every 4096-rank fragment of an ordinary
child port is a whole physical 4096-wire cell contained in that child's
`destinationPiece`. This establishes the local receiver label for aligned
fragments. Its new
`ordinary_child_rank_port_cells_are_receiver_of_aligned_endpoints` wrapper
derives the number of such fragments from aligned ordered endpoints, so callers
need not supply a separate cell-count equation. Still to prove is
the full actual-schedule instantiation of the static-hole premises and the
identification of each clipped tile/column profile cell and its false count
with those physical routed cells.

`D2ClippedCellRankInterval.lean` adds the exact local criterion: a row and
column lie in a tile's clipped port iff their flattened coordinate
`tile*262144 + 64*row + column` lies in the global port interval. Under the
sender-rank placement equation, this proves the corresponding wire is in the
child's physical destination. The new theorem
`ordered_tile_profile_cell_wire_in_child_receiver` eliminates that placement
equation for a complete rank tile: `Finset.orderEmbOfFin` supplies the actual
sender wire, and its rank theorem supplies the coordinate. The focused
current-source rebuild passes. The strengthened theorem
`ordered_tile_profile_cell_tag_iff` proves the converse too: the wire is in
the child destination exactly when its row lies in the clipped port. This
closes the local cell-to-address step for full tiles when the stage uses the
canonical ordered embedding; ragged tiles and instantiating that embedding in
the global stage remain open.

Correction to the previous priority note: `D2RankCutSeamBound.lean`'s 14,985
bound compares an output slot with the rank of the value currently in that
slot. It is not a direct additive error in the physical profile transfer,
which compares output-slot cell counts to the exact-rank profile and already
proves the aggregate 448 bound. Do not add the seam count to that recurrence.
The next decisive gate is instead to compose the complete-tile ordered
embedding, clipped cell counts, and receiver tags into one actual ordinary
sender transition, then expose the partial-tile/startup exceptions.

### Current incremental gate: one-tile false-count identity

`ordered_tile_child_false_count_eq_profile` in
`D2ClippedCellRankInterval.lean` proves that, for one complete sender-rank
tile, the sum of clipped `prefixIntervalMass` values for a port equals the
actual number of false wires in that tile whose canonical `orderEmbOfFin`
addresses lie in the tagged child destination. Its hypotheses make the
coordinates explicit: port endpoints match the child's static destination
boundaries, and each physical column is an exact false-prefix.

The stronger wrapper `reflected_core_ordered_tile_child_false_count_eq_profile`
removes the profile hypothesis for the actual reflected physical core on an
arbitrary Boolean input. It uses the checked fact that the core output is
column-monotone, hence exactly the false-prefix profile whose heights are its
actual per-column false counts. Focused current-source rebuild of
`D2ClippedCellRankInterval.lean` passed on 2026-10-31. This discharges the
fixed-core output-profile part of the one-tile identity, but not the schedule
bridge: still aggregate tile identities, derive cuts and tags from the actual
sender routing, relate source false mass to the flow deficit, include parent
tags, and cover ragged/startup/exceptional roles.

The identities now compose over any finite family of complete sender-rank
tiles via `reflected_core_complete_tiles_child_false_count_eq_profile`. This
is an exact sum over actual reflected-core false wires whose ordered sender
addresses lie in the tagged child destination. It deliberately stops at the
last complete 262144-wire tile; the residual rank suffix has no theorem yet.
The ordinary-sender bridge can now focus on (a) proving the schedule's static
rank intervals and receiver labels agree with these tile cuts, (b) covering
the ragged suffix, and (c) connecting total physical false mass to the flow
deficit.

The child-port specialization is now checked as well:
`reflected_core_ordinary_child_tile_false_count_eq_profile` instantiates the
ten ordinary sender cuts `d2SenderPortBoundaryNat` at port `child + 1`, and
uses `d2FlowRankBoundary widths` and `quota / 2` for the corresponding child
destination. Its all-complete-tiles form,
`reflected_core_ordinary_child_complete_tiles_false_count_eq_profile`, sums
the actual child counts and clipped core profile masses over all full tiles
for arbitrary per-tile Boolean inputs. It assumes only that every indexed
tile is complete. It does not yet prove that these inputs are the recursively
scheduled sender contents or cover the residual suffix.

The fixed-core count bridge now reaches the actual one-step ordinary sender
port formulas: for child `j`, port `j+1` of
`d2SenderPortBoundaryNat quota senderCard widths` is matched to
`destinationPiece` with child interval boundaries
`quota/2 + d2FlowRankBoundary widths j`. The corresponding all-complete-tiles
theorem is checked in `D2ClippedCellRankInterval.lean` and assumes only the
complete-tile bounds; the local identity itself does not need total sender
conservation. `clippedFlowGroupedActualOfProfile_eq_uniform_port` then
reindexes the actual-profile group by its selected port, and
`reflected_core_ordinary_child_grouped_count_eq_physical` equates that grouped
count to the false outputs routed to the child over all complete tiles. These
are focused-current-source checked. This resolves the local flow-cut-to-child
label composition at full-tile scale. It is not yet an identification with a
recursive run: the schedule still must provide the same finite set `S`,
per-tile inputs, static-hole destination sets, and next child bags, as well as
the leftover suffix and startup/exceptional adapters.

`canonicalSenderRankTileInput` now extracts each full tile directly from an
arbitrary global Boolean word using `S.orderEmbOfFin` in sender-rank order.
The checked theorem `reflected_core_sender_word_ordinary_child_grouped_count_eq_physical`
states the grouped child-count identity for this canonical input, eliminating
the unrelated-per-tile-input gap. It still does not define or identify the
recursive sequence of sender sets across stages.

The local transition is now represented by an actual global comparator
network as well. `canonicalSenderRankTileEmbedding` embeds each complete
262144-wire rank tile into the global wire universe;
`reflectedSenderFullTileStageNet` scatter-embeds the reflected core on all
such tiles. Its execution theorem proves that each embedded tile runs on the
canonical slice of the global input word. Finally,
`reflected_sender_stage_grouped_child_count_eq_physical` equates the ordinary
child's grouped clipped-profile count to false outputs of this actual stage
network whose addresses lie in that child's `destinationPiece`. The focused
current-source rebuild passes. This closes the one-sender, full-tile local
network/count composition. The network leaves a ragged suffix untouched; no
profile transition for it is proved. More significantly, the repository still
has no recursive definition connecting these per-sender stage networks and
their destination pieces to the next stage's sender sets/inputs and the
all-depth `d2FlowCandidateRun` state. That recursive realization remains the
main physical-flow bridge.

`D2StrongDeficitPropagation.lean` already proves the sharp local affine
profile transition for ordinary eight-child updates. The profile is
`G = 0 ∧ 256*pi <= c`, or
`8192*G + 7 <= 15*c ∧ 4096*pi <= 15*c`; it propagates to every child at
capacity `2*c`, implies the existing deficit and quota caps, and preserves the
seven-unit slack. This local arithmetic is closed and should not be repeated.

Further current-source adapters are already present: `D2StrongFlowCoreInputs.lean`
converts a full-tree affine core provider to the sender contract;
`D2StrongAffineChild.lean` transports the profile through a concrete ordinary
parent update; `D2TopDescHistory.lean` handles reset history and classifies
active child root profiles; and `D2CoreProviderReserveStep.lean` transports
both profiles and two-visit endpoint reserves along actual paths. Focused
current-source checks passed for `D2StrongFlowCoreInputs.lean`,
`D2TopDescHistory.lean`, `D2CoreProviderReserveStep.lean`,
`D2RootFrontierCase.lean`, `D2FlowPathLast.lean`, and
`D2AffineCoreBootstrap.lean`. The path adapters still assume prior full-tree
core snapshots. `D2AffineCoreAllStages.lean` now closes the all-time abstract
core-provider induction. The moving
root-frontier case is isolated in `D2RootFrontierCase.lean`: an active
level-zero node is top-descending, and its current deficit is zero given the
prior core at `t-2`. `D2FlowPathLast.lean` adds a checked last-edge
decomposition for root-first paths to support composing the path adapters.
`D2AffineCoreBootstrap.lean` proves the initial and first post-bootstrap run
snapshots satisfy the full affine core provider. The first positive snapshot
uses the exact top-rise role and full-grandchild endpoint reserves. Snapshots
2 and 3 are now checked as well. At stage two, the proof upgrades the exact
bottom-descending boundary sender from the strict input contract to the sharper
affine profile; its deficit cases are exactly `0` and `2^(3*d+7)`, and the
endpoint reserves come from `d2FlowCandidateStage2_sender_inputs`. It then
assembles the eight children and the complete root snapshot. For stage three,
the bottom-rise nodes need only the balance field already supplied by strict
inputs; the top-rise subtree reuses the proved endpoint reserves. The affine
bootstrap snapshots 0 through 3 pass a focused current-source rebuild. The
all-stage induction is closed by `D2AffineCoreAllStages.lean`.
`D2StrongAffineChild.lean` proves
`d2FlowTreeRunWithParentOverwrites_child_balanced`: an ordinary active parent
writes balanced root data into each child even through arbitrary
ancestor-overwrite history. `D2CoreProviderReserveStep.lean` lifts this to
ordinary parents on actual candidate paths. Finally,
`D2TopDescHistory.lean` proves
`d2FlowCandidateRun_active_child_balanced_of_prior_core`, combining the
schedule's parent-role split, top-descending reset history, and the next-tree
invariant to get balance for every active child. Focused current-source
rebuilds pass for both modules. `D2TreePathGeometry.lean` packages the local
child profile and endpoint-reserve theorems into the full-tree transition;
`D2AffineCoreAllStages.lean` closes its induction from the bootstrap. The
remaining gap is the physical schedule-to-flow identification, not another
flow-reserve induction.

The final-stage edge case in the two-visit endpoint reserve is now closed.
`D2TerminalScheduleFacts.lean` proves the exact top-frontier levels at `tfD2`
and two stages before it, then extends the regular-sender predecessor-role
classification to include `t = tfD2`. `D2CoreProviderReserveStep.lean` now
uses the non-strict terminal bound throughout; current-source focused rebuilds
pass for that module and its `D2TopDescHistory.lean` dependent. This closes the
strict-before-terminal schedule side condition for endpoint reserves. It does
not by itself establish the full provider. `D2FlowPathLast.lean` now proves a
cast-aware path-snoc projection and transports the candidate run/core contract
across the associated height indices. Its
`d2FlowCandidateRun_active_child_affine_local_contract` combines balance,
the role-dependent root profile, and endpoint reserves for the *same* actual
active child. The focused current-source rebuild passes. Thus the local child
contract and its path/index adapter are closed. It derives the needed
next-snapshot invariant from the current invariant and current affine core
using the existing one-stage preservation theorem, so it no longer assumes a
future invariant. The same module packages root balance, exact-zero profile,
and top-descending role for an active root. Its focused current-source rebuild
passes. Packaging the root and child contracts recursively into a full-tree
transition and then an all-stage theorem is now closed by
`D2TreePathGeometry.lean` and `D2AffineCoreAllStages.lean`.

The exact compressed-flow screen
`d2_deficit_tolerance_screen.py --depth 100 --scale 8192 --params 3 3 2`
checks 217470 reachable stage/node entries. Its maximum is
`G/capacity = 15/8192 - 7/capacity`; all quota and endpoint gates pass. This
is finite model evidence, not an all-depth theorem. The affine local update
and its side conditions are now proved for the abstract candidate flow tree
at all stages, and `D2AllStageTwoFrontGate.lean` closes its ideal overrun gate.
What remains is to identify actual physical sender profiles
and tags with this tree for the fixed schedule, including startup, top-rise,
mid, bottom-descending, exceptional, and ragged roles.

After the physical profile transition, the proof still needs an invariant
linking actual sender masses to the abstract flow state, a spatial or
distance-sensitive terminal bound, fixed terminal cleanup, and depth/padding
accounting. Aggregate L1 error alone does not imply terminal purity or bounded
displacement.

## Next proof gate: define the physical recursive run

The all-time abstract full-tree affine-core plus invariant theorem is kernel-
checked in `D2AffineCoreAllStages.lean`; the all-tile/all-column ideal port
identity is checked in `D2ClippedTilePortAggregation.lean`. The candidate-run
path interface now also supplies sender-input invariants and aligned port
boundaries at one path (`d2FlowCandidateRun_stage_inv_inputs_atPath` and
`d2FlowCandidateRun_sender_boundary_grid_atPath` in `D2AllStagePortGrid.lean`).

The physical transition is specified in Python source, not yet proved in
Lean. `flow_dag.py` defines the compressed tree updates and each bag's
ordered static intervals; `wire_partition_check.py` assembles every next bag
from retained inactive bags, parent down-ports, and child up-ports, then checks
exact interval equality and no duplicate routing. The receiver-context logic
in `receiver_fiber_types.py` additionally records the important parent-root
overwrite case. These scripts are source (not generated artifacts). The
compressed exact-routing screen now passes at depths 40, 80, and 120 for
scale 1: respectively 96,008, 765,356, and 2,577,568 routing cases over
29,483, 247,233, and 847,827 shared states. This remains finite model
evidence. On the Lean side,
`D2OrdinaryRankRouting.lean` proves local pieces partition an arbitrary
sender and has the generic `routed_local_destinations_preserve_partition`,
which takes the target map as input; the static-hole lemmas do not yet prove
that the Python interval recurrence is the candidate tree's all-depth
physical execution.

`D2-RECEIVER-FIBER-DEGREE-SCREEN.md` records a related finite locality
diagnostic: with `scale=8192`, `(3,3,2)`, and depths 7–10, maximum source-tile
fan-out is 3 while target fan-in reaches 4 (already at depth 9). This may help design a spatial
potential, but it does not bound error mass or prove contraction. The current
screen expands physical tiles and is too slow for deep asymptotic exploration;
replace that expansion with compressed interval incidence before extending
the numerical range.

`D2PhysicalBagState.lean` now defines `d2FlowNodeStaticBag` as the node's
occupied native interval minus its eight child holes, and
`d2FlowNodeStaticRuns` as the corresponding ordered gaps. The checked theorem
`d2FlowNodeStaticBag_eq_runs` proves exact equality and run ordering whenever
the holes fit; `d2FlowNodeChildHole_eq_interval` identifies every nonsaturated
child hole with its native address interval. This is a local representation
interface, not yet an all-stage invariant: it assumes `StaticHolesFit` and
does not show routed pieces equal the next node's bag. The accompanying
`d2FlowTreeInv_alone_not_static_holes_fit` theorem is an exact warning: the
recursive capacity/balance invariant by itself does not imply this fit. Its
counterexample is an arbitrary legal invariant tree, not a reachable candidate
state. The scheduled proof must use the stronger endpoint reserves and stage
history; do not try to derive the fit from `d2FlowTreeInv` alone.

The recursive property `d2FlowTreeStaticFits` is now defined, and its initial
case is proved: both `d2FlowTreeFull_static_fits` and
`d2FlowTreeInitial_static_fits` establish nested static-hole fit for every
depth. `D2PhysicalBagState.lean` also proves
`d2FlowStage_regular_child_root_data`, identifying each active ordinary
post-stage child's root tuple with its cut tuple, and
`d2FlowStage_active_ordinary_static_fit`, proving that those holes fit between
the updated parent fronts. The ordinary stage-input balance and quota clauses
establish the equality between the cut endpoint `total - (high + quota/2)`
and the stage assignment `total - high - quota/2`. The inactive-node case is
proved by `d2FlowStage_inactive_node_static_fit`: child deficit/front
monotonicity preserves an inactive parent's hole fit through the recursive
stage. This is local geometry only; recursive whole-tree preservation and
active exceptional/overwrite cases remain open.

Important correction: the current canonical point markers for saturated
empty holes do **not** define an all-stage `StaticHolesFit` invariant. The
reproducible `static_hole_fit_screen.py` finds failures in exact reachable
`FlowDAG` states: 20/100 node-stages at d=7, 36/184 at d=8, 76/426 at d=10,
128/800 at d=12, and 456/4138 at d=20. The first failures are stage 3,
level 3, where saturated-hole markers fall out of address order after a
frontier moves across slots. The compressed wire-routing screen still passes
at d=20 (32,750 routing cases, 4,831 shared states), so this is a
marker/representation failure, not a routing counterexample.
`D2PhysicalBagState.lean` kernel-checks that clamped markers remove the same
wire set as the current markers. Clamped fit has zero failures at all tested
depths through 20. Two Lean interfaces now support this representation:
`d2FlowNodeStaticHolesClamped_fit_of_child_intervals_contained` proves fit
from containment of every nonsaturated child interval, while
`d2FlowNodeStaticHolesClamped_fit_of_static_fit` converts any already-fitting
canonical list to the clamped list. The new
`d2FlowNodeStaticHolesClamped_fit_of_fronts_mono` also preserves clamped fit
when child deficits and both fronts move inward. Thus the inactive-node stage
case is now proved from a clamped input fit. The active ordinary-stage fit is
also converted to clamped fit by
`d2FlowStage_active_ordinary_static_fit_clamped`. Existing initial-fit results
can be converted as well. The active top-descending fit is now proved by
`d2FlowStage_active_top_desc_static_fit_clamped`, since all eight child holes
are their full native slots after reset. The active bottom-rising case also
has `d2FlowStage_active_bot_rise_static_fit_clamped`, which proves clamped fit
under the explicit native-front and first/last-child containment conditions
already used by the bot-rise bag-conservation lemma. Supplying these
conditions from the arbitrary-path schedule history remains open, as does
routed next-bag identity.

The same file now proves `d2FlowStage_active_top_desc_static_bag_empty` for
positive native width: the startup top-descending reset sets all eight child
root tuples to zero, so their static holes fill the parent interval. This
closes the local parent-bag case for top-descending alongside the ordinary
case; it does not establish the startup receiver-tag or Boolean-profile
transition.

`d2FlowStage_root_fronts_mono` proves that a subtree's own recursive stage
never decreases either root front offset; together with deficit monotonicity,
this supplies the inactive-parent clamped-fit preservation above. It does not
cover a later parent `setRoot` overwrite; active-parent cases need their cut
geometry and special-role lemmas.

`d2FlowNodeStaticBag_eq_empty_of_child_total_eq_G` proves that a fitted node
bag is empty whenever its child deficits sum to the parent deficit. Combining
ordinary-cut conservation with stage invariant preservation gives
`d2FlowStage_active_ordinary_static_bag_empty`: after an active ordinary cut,
the updated parent bag is empty because the children account for all of its
deficit. This is only the parent-side conservation fact; it does not identify
the routed child port with the next-stage child's static bag.

For `.botRise`, `D2OrdinaryRankRouting.lean` proves that, when the child level
is inactive, the whole sender is routed to its parent and the child pieces are
empty. `D2PhysicalBagState.lean` now proves the matching conditional
conservation fact, `d2FlowStage_active_bot_rise_static_bag_empty`, with a
post-step fit hypothesis. The attempted full-list fit reduction is not an
actual reachable invariant under the current canonical empty-hole markers
(see the correction above); retain the empty-bag cardinality result, but use a
clamped or nonordered empty-marker representation for an all-stage statement.
The exact receiver union (parent down-port, retained self bag, and child
up-ports) equaling its next-stage static bag remains open.

`D2OrdinaryRankRouting.lean` already proves the generic local destination-piece
partition for an abstract sender set; do not reprove it.
`D2PhysicalBagState.lean` now proves that a fitting hole union's cardinality
is its interval-length sum, each child hole has length `nativeWidth - deficit`,
and a valid nonsaturated node's static bag has cardinality `child-total - G`.
It instantiates the generic rank-port partition with this concrete bag, so the
parent/child pieces cover the sender set disjointly. The next step is to prove
`d2FlowNodeStaticBag_child_port_eq_run_slice` and
`d2FlowNodeStaticBag_parent_ports_eq_run_slices` identify the concrete
child and parent destination pieces with canonical ordered-run slices. The
clamped representation now has its own run list and a kernel-checked
bag-union/order theorem, plus child/parent rank-slice and per-cell identities
(`d2FlowNodeStaticBag_*_clamped_*`). These are the interfaces to use for the
repaired marker convention. The next step is still to prove these pieces match
the actual next physical bags: inactive retained bags, the parent's down-port,
and active children's up-ports. Match exact indices/
overwrite behavior in
`wire_partition_check.py` and `receiver_fiber_types.py`. This would supply
concrete receiver tags for the clipped-tile identity. Cover startup,
exceptional roles, and ragged cases before claiming the full bridge. The
profile transition, spatial terminal invariant, fixed cleanup, and
depth/padding accounting remain open. Aggregate error alone is not terminal
purity.

## Candidate representation pivot (2026-10-31)

`D2-DYNAMIC-SENDER-SETS.md` specifies a proposed alternative to proving that
the routed physical sets equal the canonical static-hole bags. It stores each
sender as an actual `Finset (Fin n)`, partitions an active sender by its local
rank-port theorem, retains inactive senders, and defines each next sender set
as the union of pieces routed to that node. The existing
`routed_local_destinations_preserve_partition` theorem supplies global
coverage/disjointness once the source sets partition the wires and local port
pieces partition each source.

This is only a representation proposal. The decisive unproved part is an
all-tree-level cardinality theorem matching each dynamically defined sender
set to `d2FlowTreeAllocation` after `d2FlowStage`, including exceptional roles,
startup, and parent-root overwrites. Even if that closes, it only supplies a
physical layout and receiver tags; the all-stage spatial false-profile
contraction and terminal cleanup still need proof. First test the one-stage
partition-plus-cardinality theorem before adding more profile adapters. If its
allocation recurrence fails in a reachable case, record the counterexample
and return to the static-bag transition gate.

`D2DynamicSenderCardinality.lean` now closes the local size algebra. The D2
parent and child rank pieces have their exact port widths, and the generic
routed receiver cardinality is the sum of its incoming piece sizes. On the
flow side, `d2FlowTreeAllocation_after_inactive_recursive_stage` proves that
an inactive receiver's allocation changes by exactly its parent down-port
plus its children's up-ports. It requires the parent-overwritten root to be
below the receiver's recursively updated child mass. The unresolved physical
bridge is now specifically to instantiate the source partition and these
identities together for the candidate tree. For ordinary parent cuts,
`d2FlowStage_regular_child_root_drop` proves the root drop and
`d2FlowStage_regular_child_postoverwrite_cover` supplies the child-cover
condition, assuming the existing cut validity, recursive-child invariant, and
native cap. The top-descending reset gives both facts directly by setting the
child root to zero; at a bottom-rise visit with an inactive next level, child
roots are preserved and there is no child down-port. Zero post-stage
allocation is proved conditionally for all active roles (`regular`,
`topDesc`, and `botRise`). `d2FlowCandidate_root_active_role_topDesc` also
proves that the candidate root is only active as `topDesc`; hence the root has
no parent up-port requiring a receiver outside the tree. The separate
zero-root input contract for this reset is still needed.
`d2FlowCandidateActive_no_adjacent` proves neighboring levels are never active
simultaneously, and `d2FlowCandidate_leaf_inactive` proves level `d` is never
active for candidate depth `d >= 7`. Together with the root-role result, the
schedule has no active sender beyond the represented tree boundaries.
Startup/exceptional role routing still needs integration into the set-valued
layout. None of these size/layout facts establishes the spatial profile
contraction.

`D2DynamicSenderLayout.lean` now defines the recursive set-valued transition:
process children first; an inactive node keeps its set and absorbs child
up-ports; an active node empties itself, adds its down-ports to child results,
and returns its up-port. The active/inactive root equations, empty up-port for
inactive nodes, flattening lemma for adding a down-port, and finite-union
distributivity/congruence lemmas are kernel-checked.
The flat-index route and its conditional global partition/cardinality
interfaces are now in `D2DynamicSenderNode.lean`. A direct nested
`Finset.biUnion` conservation proof was discarded after elaboration failures;
do not resume that proof strategy. The remaining construction-specific
obligation is to identify actual schedule node bags and local port pieces with
the flat interfaces, including exceptional roles and parent-root overwrites.

## Flat-index checkpoint (2026-11-01)

`D2DynamicSenderNode.lean` now defines a finite `Sigma` index for every node
across levels `0..depth`, with parent/child option-valued navigation and a
projection from an indexed node to its corresponding `D2FlowTree` subtree.
It extracts the recursive `D2SenderLayout` bag at each flat index and defines
the one-stage route: `none` is the parent port, `some j` is child `j`, and an
`Option` receiver's `none` is the external boundary bucket. Inactive nodes
retain their source bag locally. The theorem
`d2SenderNodeRoute_preserves_partition` instantiates the generic destination
partition theorem on this actual finite parent/child map. Its focused check
passes, but its source partition and local-piece partition hypotheses have not
been derived for the candidate execution. The same file now packages a
parent-plus-eight-child local partition as an `Option (Fin 8)` port contract;
`d2OrdinaryRankSenderPorts_contract` adapts the existing rank-cut partition
theorem to that interface. Thus the regular/top-desc/bot-rise local partition
results can supply the local part whenever their stage and sender-cardinality
hypotheses hold. The receiver-cardinality lemma expresses each routed bag's
size as the sum of incoming port sizes. The external bucket is proved empty
assuming active roots have empty parent output and the leaf level is inactive;
the candidate schedule supplies leaf inactivity and the root-role fact, but
connecting that role to the concrete split remains open. The next decisive
step is to define node-dependent source bags and splits from the actual
candidate stage/static bags, then match receiver cardinality to
`d2FlowTreeAllocation` without assuming the agreement.

The flat route now also has checked parent/child level lemmas and
`d2SenderNodeRouteTarget_level_relation`: every piece reaching a receiver
originates at the same level (inactive self-retention) or an adjacent level
(active parent/child transfer). This is the first structural reduction of
the incoming-port sum. Next combine it with the schedule's no-adjacent-active
levels property to eliminate impossible senders and identify the surviving
port terms with the inactive allocation recurrence.

`D2DynamicSenderNode.lean` now also defines a concrete static physical bag for
each flat flow-tree node, using its native base-eight address and the checked
static-hole construction. The root selector reduces to the root subtree, and
`d2SenderNodePhysicalBag_initial_root_eq_univ` proves that the initial root
source bag is exactly the full wire universe (including depth zero and zero
width). The same file packages all recursive static bags as a
`D2SenderLayout`; `d2FlowTreePhysicalBag_full_eq_empty` and
`d2FlowTreePhysicalLayout_full_wires_eq_empty` show that a full-capacity
subtree contributes no wires, and
`d2FlowTreePhysicalLayout_initial_wires_eq_univ` proves that the initial
recursive layout covers the complete wire universe. These are base-state
results. The equality between flat-index bag projections and these recursive
physical bags is now proved by `d2FlowTreePhysicalLayout_bagAtPath` and its
flat-node adapter `d2SenderNodeBag_physical_eq`. The generic containment
lemma `d2SenderLayoutBagAtPath_subset_wires` shows that a selected bag is
contained in its recursive subtree's total wire set. This can be used with
the empty-full-subtree result to prove non-root startup bags empty. The
startup flat source partition is now proved by
`d2SenderNodeBag_initial_physical_partition`: the root bag is the full
universe, every non-root bag is empty, and the bags are pairwise disjoint.
This supplies the flat route theorem's source-partition premise at the
initial state. For an ordinary active cut, `d2OrdinaryRankSenderPorts_card_eq_flow_widths`
now proves the parent port has exactly the role quota size and each child port
has size equal to that child's flow-deficit decrease, assuming the established
cut gates and sender-cardinality equation. This supplies the local numeric
input to the receiver recurrence. `d2OrdinaryRankSenderPorts_complete_contract`
now packages the local partition and exact sizes together for downstream use.
`d2FlowNodeStaticBag_card_eq_flow_allocation_of_fit` and
`d2FlowTreePhysicalBag_leaf_card_eq_allocation` discharge the sender
cardinality equation for internal and leaf static bags, respectively, under
the flow invariant, geometric fit (internal nodes), and wire-bound hypotheses.
The clamped representation now has the matching pricing lemma:
`d2FlowNodeStaticBag_card_eq_child_total_sub_G_of_clamped_fit` proves the same
exact sender-bag cardinality from clamped fit, and
`d2FlowNodeStaticHolesClamped_card` proves its holes have the required total
length. `D2DynamicSenderNode.lean` now exposes this as
`d2FlowNodeStaticBag_card_eq_flow_allocation_of_clamped_fit`, preserving the
canonical-fit theorem as a wrapper. It also provides
`d2OrdinaryRankSenderPorts_static_bag_complete_contract`, which instantiates
the ordinary partition and exact port-size theorem directly on a clamped-fit
static bag. `d2FlowNode_active_ordinary_piece_partition` now likewise accepts
clamped fit and proves the concrete static bag's parent/child rank pieces
partition it. Focused current-source rebuilds of both files pass.
This removes the mismatch between the reachable clamped representation and
the sender-cardinality interface; it does not establish clamped fit at every
reachable stage. Canonical hole markers still fail the all-stage fit screen,
and the clamped representation still lacks an all-stage fit provider. Every
post-stage bag identity remains open. Next close the reachable fit/provider
gate, then compose the local port sizes through the recursive stage and compare
each post-stage routed receiver with `d2FlowTreeAllocation`; startup/exceptional
roles and root overwrites remain to be covered. The decisive risk remains
whether this exact identity holds for all role and overwrite cases.

## Files and artifacts

Start at `README.md` for the module map. `STATUS-HISTORY.md` preserves the
chronological log; it is not current status. Build outputs were moved to the
ignored `LLM-helpers/sub300-check/artifacts/sub300-structural/` tree and listed
with hashes in its `MANIFEST.tsv`. Use
`python LLM-helpers/sub300-check/check_prefix_flux_lean.py <source> --repo-root
.claude/worktrees/sub300` for focused checks; rebuild dependencies when their
sources changed.


## Bot-rise allocation parity checkpoint (2026-11-01)

`D2BotRiseStaticFit.lean` now proves, for every reachable candidate-run
`botRise` path snapshot, that the symmetric parent allocation
`d2FlowTotal(children deficits) - G` is even. The proof uses the existing
all-stage alignment theorem: every selected node has `4096` dividing `G`; all eight
children are saturated in this role, so their total deficit is a multiple of
4096 as well. The local `bot_rise_sender_piece_partition` theorem in
`D2OrdinaryRankRouting.lean` therefore has its parity premise available for
these snapshots, alongside the previously proved exact sender cardinality and
child-root preservation. Focused current-source Lean check: PASS for
`D2BotRiseStaticFit`. This remains a local bot-rise routing fact; it does not
identify routed receiver sets with next-stage bags, establish the full
all-role physical transition, or prove profile contraction/terminal cleanup.
The parity result is now composed with `bot_rise_sender_piece_partition` in
`candidate_botRise_path_piece_partition`, uniformly for any sender set with the
correct flow-allocation size. This is reusable by the dynamic-set layout. Next,
assemble the ordinary, top-descending, and bottom-rising local providers in the
flat layout and prove the receiver-allocation induction. The arbitrary-root
profile recurrence also remains open, so the central sub-300 risk is unchanged.
