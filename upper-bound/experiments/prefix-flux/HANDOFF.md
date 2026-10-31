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

After the exact profile transition, the proof still needs an all-depth sender
invariant, a spatial/distance-sensitive terminal bound, fixed terminal
cleanup, and depth/padding accounting. Aggregate L1 error alone does not imply
terminal purity or bounded displacement.

## Next proof gate

Use `clipped_fullheight_false_core_grouped_error_le_parent_add_448` for one
ordinary sender of an actual `d2FlowCandidateRun` transition. Prove its ten
port intervals, receiver tags, input false mass, and per-child ideal false
masses from the run's rank boundaries and static sender sets. If this identity
closes for arbitrary legal profiles, extend to ragged heights and exceptional
roles; then test whether the recurrence yields an all-depth spatial/distance
invariant and terminal cleanup. Aggregate error alone is not terminal purity.

## Files and artifacts

Start at `README.md` for the module map. `STATUS-HISTORY.md` preserves the
chronological log; it is not current status. Build outputs were moved to the
ignored `LLM-helpers/sub300-check/artifacts/sub300-structural/` tree and listed
with hashes in its `MANIFEST.tsv`. Use
`python LLM-helpers/sub300-check/check_prefix_flux_lean.py <source> --repo-root
.claude/worktrees/sub300` for focused checks; rebuild dependencies when their
sources changed.
