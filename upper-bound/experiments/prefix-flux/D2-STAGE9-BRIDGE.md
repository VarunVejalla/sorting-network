# Stage-nine gate bridge

2026-10-23. The checked Stage 8 preservation theorem gives the actual input
tree for stage nine. For `d>=11`, the kernel-checked frontier classifier
`d2FlowCandidateStage9_frontiers` gives the active levels and roles:

| level | role |
|---:|---|
| 1 | `topRise` |
| 3 | `mid` |
| 5 | `botRise` |

Level 7 is inactive. The `d=10` startup phase differs at level 1 and is a
finite case irrelevant to the asymptotic coefficient.

The transfer geometry is promising and matches the existing generic lemmas.
Stage 8's root `topDesc` resets every level-one root to `(G,low,high)=(0,0,0)`.
Those level-one nodes are stage-nine `topRise` senders; their level-two child
roots were increased by stage-eight `mid` quotas, which are at least the
stage-nine endpoint-reserve target. At level three, the stage-eight level-two
`mid` cuts give the sender cap and balance, while stage-eight level-four
`botDesc` quota increments supply the level-four endpoint reserves. The
stage-eight level-four cuts write balanced root data to the level-five
`botRise` nodes. Below level five, stage nine is inactive.

The root-reset fact is proved by
`d2FlowCandidateStage9_levelOne_rootdata_zero`. The stage-eight level-two quota
lower bound and its scaled level-one endpoint reserve are proved by
`d2FlowCandidateStage9_levelTwo_quota_lower` and
`d2FlowCandidateStage9_levelOne_endpoint_reserves`. These assemble the full
local gate for each stage-nine level-one sender in
`d2FlowCandidateStage9_levelOne_inputs`, assuming the recursive level-two
predicates. `d2FlowCandidateStage9_levelFour_quota_lower` extracts the stage-
eight level-four `botDesc` increments. Together with the level-five balance
lemma and inactive tail, these close the level-three `mid` gate in
`d2FlowCandidateStage9_actual_levelThree_inputs`. The full root predicate is
assembled in `d2FlowCandidateStage9_actual_inputs`, and
`d2FlowCandidateStage9_preserves_inv` carries the invariant through run stage
10. These theorems are kernel checked for `d>=11` by the focused Lean-file
check.

The Stage 8-to-9 bridge now also proves that every actual level-six root in
the stage-nine input tree remains at native deficit, via the saturated
stage-seven level-five roots and the inactive level-six tail. This is checked
as `d2FlowCandidateStage8_actual_levelSix_native`.

The next frontier is stage 10: levels 0/2/4 are active with roles
`topDesc`/`mid`/`botDesc`, and level 6 is inactive. Its frontier classifier is
now checked as `d2FlowCandidateStage10_frontiers`. The local level-four
`botDesc` gate arithmetic is checked in
`d2FlowCandidateStage10_botDesc_inputs`: its endpoint and sender-cap premises
pay the quota with slack 32 versus 23 at a common power-of-two scale. The
actual level-four gate is now proved in
`d2FlowCandidateStage10_actual_levelFour_inputs`, using the Stage 9 level-three
mid cut for its cap and balance and the native level-five roots for its
endpoint reserves. The level-two/root gates and preservation through stage ten
remain open. The all-depth recurrence, provider/rank transfer,
terminal contract, and sorting theorem also remain open. The conditional
coefficient is still 273.

As a finite cross-check, `d2_reachable_reserve_audit.py` passes at depths 30 and
60, checking respectively 4,660 and 42,128 active ordinary sender states for
deficit, quota, and both endpoint-reserve conditions. This includes the
stage-ten phase but is diagnostic evidence only; the all-depth Lean recurrence
is still missing.

2026-10-23 update: Stage 10 is now fully closed as a concrete run transition
for `d>=11`. The stage-ten level-three endpoint reserve is transported from
the stage-nine level-three mid quota. The level-two sender cap and endpoint
balance follow from the stage-nine level-one top-rise cut, with its capacity
exactly twice the next sender capacity. These facts and the existing actual
level-four bot-descending gate build `d2FlowCandidateStage10_actual_inputs`;
the root-zero argument uses the stage-eight top-descending reset and the
inactive stage-nine root. `d2FlowCandidateStage10_preserves_inv` then carries
the invariant through run stage 11. The focused Lean check passes. The next
finite bootstrap frontier is stage 11; the all-depth reserve/cap recurrence,
provider/rank transfer, terminal contract, and sorting proof remain open.
