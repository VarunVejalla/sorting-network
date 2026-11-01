# Prefix-flux / D2 research

This folder contains the active structural route toward a sub-300 upper bound.
For the current mathematical status, read [HANDOFF.md](HANDOFF.md). The old
chronological status log is retained as [STATUS-HISTORY.md](STATUS-HISTORY.md)
and should be consulted only for provenance.

## Source map

| Area | Start here | Purpose and current limit |
|---|---|---|
| Fixed physical core | `D2-FOUR-SORT-4096-CANDIDATE.md`, `D2ReflectedPhysicalPack.lean`, `D2BandRepair4096Network.lean` | Depth 276; checked 832-wire Boolean band for one fixed tile. Local result only. |
| Local rank/profile transfer | `D2LocalRankDisplacement.lean`, `D2PhysicalProfileGlobalTransfer.lean`, `D2GeometricProfileBudget.lean` | 832 local displacement and 448-per-tile aggregate interfaces; actual stage tags/correlation remain open. |
| False-profile clipped transfer | `D2FalseProfileTransfer.lean`, `D2FalseClippedTransfer.lean`, `D2PhysicalTwoFrontGate.lean` | Checked 448 local port error and parent-error-plus-448 arbitrary-tag recurrence for full-height tiles. `D2PhysicalTwoFrontGate.lean` composes this with the all-stage affine reserve: parent tile-mass discrepancy plus 448 per source tile bounds actual two-front reserve overrun, assuming exact grouped counts and ideal interval domination. The actual schedule has not yet been shown to meet those assumptions; ragged source heights remain open. |
| Affine flow provider | `D2StrongDeficitPropagation.lean`, `D2StrongFlowCoreInputs.lean`, `D2StrongAffineChild.lean`, `D2TopDescHistory.lean`, `D2CoreProviderReserveStep.lean`, `D2TerminalScheduleFacts.lean`, `D2RootFrontierCase.lean`, `D2AffineCoreBootstrap.lean`, `D2FlowPathLast.lean`, `D2TreePathGeometry.lean`, `D2AffineCoreAllStages.lean`, `D2AllStageTwoFrontGate.lean`, `D2PhysicalTwoFrontGate.lean` | Kernel-checked local affine update and path adapters for profile, role resets, root frontier, endpoint reserves (including the terminal active stage), and balanced endpoints at every active child. `D2AffineCoreAllStages.lean` proves the all-time abstract flow-core plus invariant for every dimension at least seven; the two-front gates turn ideal child domination and physical aggregate transfer error into a reserve-overrun bound. The actual schedule's count/tag identities remain open. See `HANDOFF.md`. |
| Flow and reserves | `D2-FLOW-STATE-SPEC.md`, `D2ScheduleReserve.lean`, `D2Stage20PreservesInv.lean`, `D2AllStageInvariant.lean`, `D2AffineCoreAllStages.lean`, `D2AllStageTwoFrontGate.lean` | Abstract affine flow-core plus reserve induction and the ideal two-front overrun gate are closed for all stages. `D2AllStageInvariant.lean` lifts a construction-specific physical sender-input provider to all stages, but that provider and its identification with actual tile profiles/tags remain open. |
| Physical routing | `D2StaticWireSets.lean`, `D2VariableTilePhysicalFlowTransfer.lean`, `D2NativePathIntervals.lean` | Cell/rank-slice and boundary geometry; no closed all-depth spatial recurrence. |
| Arbitrary-root gates | `D2-DISTANCE-TAIL-PERIOD-GATE.md`, `D2-PORT-VARIANCE-TRANSFER.md` | Selected-cut relaxations expose alignment failures; they are not executions of the fixed network. |
| Other candidates and screens | `D2-SPARSE-BOTTOM-300.md`, `D2-M3-REDUCED-GATE.md`, `PROFILE-GATE.md` | Cost/probability/moment diagnostics. Read the scope caveats before using a number. |

Lean sources and scripts stay in the repository. Reproducible outputs and
compiled artifacts live in the ignored worktree-specific cache at
`LLM-helpers/sub300-check/artifacts/sub300-structural/`; its manifest records
the original paths and hashes. JSON potential tables next to their emitters
are source inputs and remain in this folder.

Run focused Lean checks through
`LLM-helpers/sub300-check/check_prefix_flux_lean.py` with `--repo-root`
pointing at this worktree. Cached `.olean` files are not proof evidence and
must be rebuilt after changing their source or dependencies.
