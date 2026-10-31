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
  conditionally; the required universal sender-input provider is missing.

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
receiver tag from the run's static sender sets, and (3) prove the per-child
ideal false mass equals the next child's capacity/deficit. The exact child
identity is required per child, not only after summing all eight. A regular
sender has ten ordered ports (two parent halves and eight child intervals),
so its cuts are the eleven boundary positions `0..10`. Prove the parent mass
error from the flow state and use the arbitrary-tag `+448` theorem. Then
extend to sub-4096 ragged heights, startup, `botRise`, and exceptional
intervals; none of those cases is supplied by the current full-height lemma.

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
is kernel-checked in `candidate_sender_two_front_overrun_zero_of_15over8192`.
The weaker strict `512*G <= capacity` reserve gives 32 per physical tile;
either strict bound leaves the local 448 charge within the 512-per-tile
doubling budget.

The exact compressed-flow screen
`d2_deficit_tolerance_screen.py --depth 100 --scale 8192 --params 3 3 2`
checks 217470 reachable stage/node entries. All ordinary senders satisfy
`G/capacity <= 15/8192`, with equality at the maximum, and all quota and
endpoint gates pass. This is finite model evidence, not an all-depth theorem.
The all-depth reserve proof and the physical sender-mass/tag identity remain
open; ragged, startup, and exceptional cases also need coverage.

After the exact profile transition, the proof still needs an all-depth sender
invariant, a spatial/distance-sensitive terminal bound, fixed terminal
cleanup, and depth/padding accounting. Aggregate L1 error alone does not imply
terminal purity or bounded displacement.

## Next proof gate

Prove the all-depth candidate-run reserve `8192*G <= 15*capacity` for every
active ordinary sender. The exact compressed-flow screen through depth 100
has maximum ratio `15/8192`; the local per-role recurrences in
`D2ScheduleReserve.lean` already include
`normalized_same_child_preserves_15over8192`. Then use the checked zero-overrun
implication to close the arithmetic part of the 512-per-tile recurrence.
Independently specify the joint state linking actual per-tile false masses to
flow ideal rank profiles and prove the actual receiver tags. Extend both parts
to ragged heights and exceptional roles. After the exact profile transition,
prove an all-depth spatial/distance invariant and terminal cleanup. Aggregate
error alone is not terminal purity.

## Files and artifacts

Start at `README.md` for the module map. `STATUS-HISTORY.md` preserves the
chronological log; it is not current status. Build outputs were moved to the
ignored `LLM-helpers/sub300-check/artifacts/sub300-structural/` tree and listed
with hashes in its `MANIFEST.tsv`. Use
`python LLM-helpers/sub300-check/check_prefix_flux_lean.py <source> --repo-root
.claude/worktrees/sub300` for focused checks; rebuild dependencies when their
sources changed.
