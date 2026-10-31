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
- `D2RoutedMass.lean` proves `routedTargetPiece_trueMass_eq_sum`: for any
  disjoint pieces of one sender, the true-bit mass assigned to a receiver is
  exactly the sum of the masses of pieces tagged for it. This is the
  count-valued form of the existing set partition, not yet the physical
  profile-to-flow identity.
- `D2ProfileOrientationGate.lean` proves the fixed core's `bottomUnaryProfile`
  has true bits in the bottom `height` rows and that physical row interval
  `[lo,hi)` has count
  `prefixIntervalMass height (4096-hi) (4096-lo)`. It also gives a
  one-true witness that the unreflected expression
  `prefixIntervalMass height 0 64` is not the count in the top physical
  64-row cell. The stage bridge must explicitly justify its row orientation.
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

The remaining ordinary-sender composition has two explicit steps: first,
connect the `variableColumnGrouped` cuts to physical row intervals with the
correct orientation (for bottom-unary outputs, physical `[lo,hi)` counts use
the reflected cuts `[4096-hi,4096-lo)`); second, identify the corresponding
ideal profile sum with the next child capacity/deficit from `d2FlowStage`.
The child-specific rank-mass calculation is needed, not merely its sum over
all eight children. Both steps must use the actual
`d2FlowCandidateRun` rank boundaries and tags. Then apply the existing
arbitrary-tag `+448` transfer with hypotheses derivable from that run. Extend
the ordinary case to startup, `botRise`, clipped final tiles, and exceptional
intervals only after this gate passes.

The corrected arbitrary-root selected-cut LP keeps exact total root mass yet
still admits large terminal error under the current independent tail
constraints. This shows those constraints are too weak; it is not a
counterexample to the fixed network.

After the exact profile transition, the proof still needs an all-depth sender
invariant, a spatial/distance-sensitive terminal bound, fixed terminal
cleanup, and depth/padding accounting. Aggregate L1 error alone does not imply
terminal purity or bounded displacement.

## Next proof gate

Prove which way the actual candidate placement maps the core's row coordinate
to sender rank/address order. The checked core profile is bottom-unary, while
`rowMajorFlowCuts` are top-oriented; either prove that the placement reverses
these coordinates or rebase the physical profile transfer on reflected cuts.
Then prove the ordinary-sender identity from tagged rank-port pieces to the
corresponding per-column counts, aggregate with
`routedTargetPiece_trueMass_eq_sum`, and establish the per-child
ideal-count/deficit equation. Quantify over arbitrary legal input profiles
and use actual run boundaries/tags. If this closes, extend to startup and
exceptional roles, then test whether the `+448` recurrence yields an
all-depth spatial/distance invariant and terminal cleanup. The aggregate
`512` budget alone is not terminal purity.

## Files and artifacts

Start at `README.md` for the module map. `STATUS-HISTORY.md` preserves the
chronological log; it is not current status. Build outputs were moved to the
ignored `LLM-helpers/sub300-check/artifacts/sub300-structural/` tree and listed
with hashes in its `MANIFEST.tsv`. Use
`python LLM-helpers/sub300-check/check_prefix_flux_lean.py <source> --repo-root
.claude/worktrees/sub300` for focused checks; rebuild dependencies when their
sources changed.
