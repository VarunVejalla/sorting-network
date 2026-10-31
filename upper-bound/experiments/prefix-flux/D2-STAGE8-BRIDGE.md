# Stage-eight gate bridge

2026-10-23. `d2FlowCandidateStage8_frontiers` is kernel checked for `d>=10`:
stage eight is active at levels 0, 2, and 4 with roles `topDesc`, `mid`, and
`botDesc`; level 6 is inactive. The complete recursive stage-eight input
predicate on the actual run-stage-8 tree is now proved, and generic
preservation carries the invariant through run stage 9.

## Gate decomposition

1. **Level-four `botDesc`.** Its sender cap should follow from the stage-seven
   level-three `botDesc` gate through
   `d2FlowStage_regular_child_g_bound_of_tree_inputs`; the capacity ratio is
   `c(stage 8, level 4) = 2*c(stage 7, level 3)`. The two level-five endpoint
   reserves must be extracted from the actual stage-seven cut and its unchanged
   descendants. The reserve target is exactly the level-five native size:
   `c(stage 8, level 4)/128 = 8192*8^(d-5)`. Stage four already has full-native
   level-four roots, and the new checked lemma
   `d2FlowTreeInv_native_node_children` says child-cover plus native child caps
   forces all eight child roots to be native. The remaining proof is to project
   those stage-four level-five roots through stages five to seven, where level
   five is inactive and parent root overwrites leave these deeper roots intact.
   The local transport is now kernel checked by
   `d2FlowCandidateStage5_levelFour_child_root`,
   `d2FlowCandidateStage6_levelFour_child_root`, and
   `d2FlowCandidateStage7_levelFour_child_root`: each says a level-four
   sender's level-five child root deficits are preserved. The generic
   `d2FlowStage_regular_child_grandchild_stage` also packages the tree
   projection through an active regular sender and one inactive intermediate
   level. The actual full-tree transport is now closed by
   `d2FlowCandidateStage4_actual_levelFive_native` through
   `d2FlowCandidateStage7_actual_levelFive_native`, using the generic
   `d2FlowStage_path5_projection`. `d2FlowCandidateStage8_botDesc_inputs`
   packages the local gate, and `d2FlowCandidateStage8_actual_levelFour_inputs`
   proves it on every level-four sender in the actual stage-seven output.
   Thus item 1 is closed for `d>=10`.
2. **Level-two `mid`.** The sender cap should export from the actual stage-seven
   level-one `topRise` gate, again with a factor-two capacity ratio. Its endpoint
   reserves come from the stage-seven level-three `botDesc` root increments:
   each such root increases by its scheduled quota, which exceeds the
   stage-eight level-two `c/128` target. The level-three nodes are inactive at
   stage eight, so their recursive obligations reduce to the level-four gates
   in item 1. `d2FlowCandidateStage8_actual_levelTwo_inputs` proves this gate
   for every actual level-two sender.
3. **Root `topDesc`.** The root is either inactive or top-descending during
   stages 0–7, so its initial zero deficit persists. The run-stage-8 invariant
   supplies endpoint balance; together with the level-two predicates below
   each level-one child, these facts give the complete root input predicate in
   `d2FlowCandidateStage8_actual_inputs`.
4. `d2FlowCandidateStage8_preserves_inv` applies
   `d2FlowStage_preserves_inv_of_inputs`, carrying the invariant through run
   stage 9. Items 1–4 are kernel checked for `d>=10`.

## Evidence and limits

The exact DAG audit `d2_reachable_reserve_audit.py` passes at depths 20, 40,
and 80, checking respectively 1,208, 11,755, and 102,825 active ordinary
sender states for deficit, quota, and both endpoint-reserve conditions. This
supports the proposed stage-eight bridge but is finite diagnostic evidence.
This remains a finite bootstrap, not a general all-stage induction. The next
gate is stage nine, followed by a reusable transition pattern (or verified
phase recurrence) through the remaining schedule stages and termination.
