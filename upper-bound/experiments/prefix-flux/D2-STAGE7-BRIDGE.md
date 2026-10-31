# Stage-seven gate bridge

2026-10-23. Stage seven is now proved end to end on the actual stage-six tree:
`d2FlowCandidateStage7_preserves_inv` preserves the saturated-aware invariant
through run stage 8 for every `d >= 9`. The exact capacity exponents give the
following margins:

* Stage-six level-two `mid` has capacity `c6 = 2^(3d+3)` and quota
  `q6 = 15*2^(3d-9)`.
* Stage-seven level-one `topRise` has capacity `2^(3d-2)`, quota
  `2^(3d-10)`, and endpoint-reserve target `2^(3d-9)`. Every child level-two
  root gains `q6`, so this reserve is available with factor 15.
* Stage-seven level-three `botDesc` has capacity `c7 = 2^(3d+4)` and
  quota `q7 = 15*2^(3d-8)`. Its deficit cap is `c7/512 = 2^(3d-5)`.
  The generic checked lemma `d2FlowStage_regular_child_g_bound_of_tree_inputs`
  exports `512*G_child <= 2*c6` from each actual stage-six level-two `mid`
  gate, where `c6 = 2^(3d+3)`; this is exactly `G_child <= c7/512`.
* Its endpoint-reserve target is `c7/128 = 2^(3d-3)`. Stage-five level-three
  `botDesc` has quota `q5 = 15*2^(3d-4)`. On the first/last equal-native
  level-four child, the stage-five cut writes exactly `low+q5/2` or
  `high+q5/2`, hence at least `q5/2 = 15*2^(3d-5)`, which exceeds the
  stage-seven target by a factor `15/4`.

The structural endpoint argument is: project the stage-five level-three
ordinary cut to its equal-native level-four children with
`d2FlowCutChild_uniform_asymmetric`; use the stage-five invariant's child-cover
at each level-four node; then stage-six `botRise` sets that level-four root to
the sum of its level-five child deficits. The level-five roots are unchanged
by stage six, so each level-four endpoint reserve carries into the stage-seven
snapshot. The stage-six level-two cut overwrites level-three roots but leaves
these recursively updated level-four descendants intact.

`d2FlowCandidateStage5_endpoint_reserves` is now kernel checked: for every
actual stage-five level-three sender, the equal-native profile plus its proved
gate shows that both endpoint level-four roots receive at least `q5/2`.
`d2FlowCandidateStage6_local_endpoint_reserves` carries these lower bounds
through the actual level-four `botRise` calls. The new
`d2FlowCandidateStage6_endpoint_reserves` proves that these local results are
the endpoint children of every actual level-three node in the whole stage-six
snapshot; `d2FlowCandidateStage6_levelTwo_projection` supplies the root
projection used for this identification.

The local stage-seven gate lemmas are also kernel checked in
`D2ScheduleReserve.lean`: `d2FlowCandidateStage7_botDesc_inputs` takes the
exported sender-deficit cap, endpoint reserves, and aggregate child mass. This
replaces the earlier unnecessarily strong requirement that every child carry
the same reserve. A single reserved endpoint plus the sender cap already
supplies enough total mass for the quota. The theorem
`d2FlowCandidateStage7_boundary_mass_suffices` checks that arithmetic, and
`d2FlowCandidateStage7_topRise_inputs` takes the zero root and stage-six `mid`
child-root increments. The generic checked lemma
`d2FlowStage_regular_child_g_bound_of_tree_inputs` exports exactly the
stage-seven level-three deficit cap from the actual stage-six level-two gate.
`d2FlowCandidateStage7_actual_levelThree_inputs` proves the local gate at each
actual level-three node. `d2FlowCandidateStage7_actual_levelTwo_inputs` then
assembles the inactive level-two predicates;
`d2FlowCandidateStage7_actual_levelOne_inputs` proves the level-one `topRise`
gate from stage-six `mid` root increments and top-descending zero child data;
`d2FlowCandidateStage7_actual_inputs` assembles the inactive root. The final
preservation theorem applies the generic recursive invariant theorem to the
actual stage-six output.

The next schedule frontier is also checked in Lean:
`d2FlowCandidateStage8_frontiers` gives root `topDesc`, level-two `mid`, and
level-four `botDesc` for `d>=10`. This means stage eight is not just the same
top-rise/bottom-descending pair: it needs a new level-four reserve bridge from
the stage-seven output, then the familiar mid-sender cap and top-descending
root assembly. The remaining global proof still needs every subsequent stage
through termination, the terminal sorting contract, and the asymptotic
coefficient bridge. Finite FlowDAG checks remain diagnostics only.

A finite exact FlowDAG scan at depths 9, 12, 20, 40, and 80 confirms the
stage-seven gates. Across unique active sender states, the maximum normalized
deficit `512G/c` is `23/32`, maximum `256*pi/c` is `1`, and maximum endpoint
reserve usage `c/(128*U)` is `1/16`. This is diagnostic evidence only.
