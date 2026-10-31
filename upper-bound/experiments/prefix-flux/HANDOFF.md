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
- Stage-specific reserve/invariant proofs reach the Run-20-to-Run-21
  transition. `D2AllStageInvariant.lean` lifts a provider to all stages
  conditionally; the required universal sender-input provider is missing.

These are source-level results with focused Lean checks recorded in the
historical log. The moved `.olean` files are caches, not verification evidence;
rebuild affected modules from current source before relying on them.

## Main unresolved gate

The exact arbitrary-root profile transfer is still open. The fixed-tile
provider is uniform over Boolean tile inputs, but the global proof must carry
the actual 64-column height profile, partial-tile offsets, and schedule
receiver tags from one stage to the next. The corrected arbitrary-root
selected-cut LP keeps exact total root mass yet still admits large terminal
error under the current independent tail constraints. This shows that those
constraints are too weak; it is not a counterexample to the fixed network.

After the exact profile transition, the proof still needs an all-depth sender
invariant, a spatial/distance-sensitive terminal bound, fixed terminal
cleanup, and depth/padding accounting. Aggregate L1 error alone does not imply
terminal purity or bounded displacement.

## Next proof gate

Specify one exact stage transition on the full tile profile and physical
receiver tags, including the first-sort dominance and arbitrary root profile.
Check whether that state closes under the actual `(3,3,2)` recurrence and
implies a distance-sensitive terminal criterion. Do not treat independent
local tail caps or finite oracle traces as a substitute for this gate.

## Files and artifacts

Start at `README.md` for the module map. `STATUS-HISTORY.md` preserves the
chronological log; it is not current status. Build outputs were moved to the
ignored `LLM-helpers/sub300-check/artifacts/sub300-structural/` tree and listed
with hashes in its `MANIFEST.tsv`. Use
`python LLM-helpers/sub300-check/check_prefix_flux_lean.py <source> --repo-root
.claude/worktrees/sub300` for focused checks; rebuild dependencies when their
sources changed.
