# Sub-300 D2 handoff

State checked against the `sub300-structural` worktree on 2026-10-31. This is
research status, not a proved improvement to the repository's accepted bound.

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
composition are now available. The remaining ordinary-sender composition
must (1) instantiate the Boolean input tile and its column profile on the
actual `d2FlowCandidateRun`, (2) identify the cumulative rank cuts and each
receiver tag from the run's static sender sets, and (3) control the physical
source false mass against the sender flow deficit `G`. Exact equality between
single-prefix masses and two-front child deficits is false in general and is
not required: `D2AllStageTwoFrontGate.lean` proves each ideal exact-prefix
child mass is at most its corresponding two-front reserve for actual
candidate flow states. Its transfer-error theorem means the physical bridge
only needs aggregate L1 error against those ideal child masses; that error
directly bounds reserve overrun. The arbitrary-tag `+448` transfer and parent
mass error are candidate sources for that estimate. A regular sender has ten ordered
ports (two parent halves and eight child intervals), so its cuts are the
eleven boundary positions `0..10`. Then extend to sub-4096 ragged heights,
startup, `botRise`, and exceptional intervals; those cases are not supplied
by the current full-height lemma.

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
`D2AlignedPortReceiverCells.lean` shows that, given the static-hole fit and
grid premises, every 4096-rank fragment of an ordinary child port is a whole
physical 4096-wire cell contained in that child's `destinationPiece`. This
establishes the local receiver label for aligned fragments. Its new
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

## Next proof gate

The all-time abstract full-tree affine-core plus invariant theorem is now
kernel-checked in `D2AffineCoreAllStages.lean`, using the bootstrap snapshots
and the one-step transition from `D2TreePathGeometry.lean`. The generic
all-tile/all-column ideal port identity is also checked by
`D2ClippedTilePortAggregation.lean`. The next formal gate is to derive actual
receiver tags from the fixed static sender sets and show they select the
corresponding flow ports (with the left-parent shift). Then identify the
physical sender mass/profile with the ideal prefix restriction, including
ragged heights and startup/exceptional roles. The existing path adapters
establish only the abstract flow-reserve state; they do not link it to the
Boolean tile profiles or actual receiver tags. After that identity, a spatial
terminal invariant, fixed cleanup, and depth accounting remain open.
Aggregate error alone is not terminal purity.

## Files and artifacts

Start at `README.md` for the module map. `STATUS-HISTORY.md` preserves the
chronological log; it is not current status. Build outputs were moved to the
ignored `LLM-helpers/sub300-check/artifacts/sub300-structural/` tree and listed
with hashes in its `MANIFEST.tsv`. Use
`python LLM-helpers/sub300-check/check_prefix_flux_lean.py <source> --repo-root
.claude/worktrees/sub300` for focused checks; rebuild dependencies when their
sources changed.
