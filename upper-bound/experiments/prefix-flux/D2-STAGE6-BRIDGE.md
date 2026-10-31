# Candidate stage-six invariant bridge

2026-10-23. Proof sketch and partial formalization for the first repeating-
schedule transition after the kernel-checked five-stage bootstrap. This is
not yet a full stage-six transition or a global sorting proof.

For candidate dimension `d >= 9`, the exact schedule frontiers at stage five
are levels 1 and 3 with roles `topRise` and `botDesc`. At stage six they are
levels 0, 2, and 4 with roles `topDesc`, `mid`, and `botRise`. The intended
transition is from the actual stage-five output to the stage-six input
predicate, then through the existing generic `d2FlowStage_preserves_inv_of_inputs`
lemma.

Write `c = d2FlowCandidateCapacity d 2 6`. Exact exponent arithmetic gives
```text
capacity(d,1,5) = c/2,
capacity(d,3,5) = 32c,
quota(d,1,5,topRise) = c/512,
quota(d,3,5,botDesc) = 15c/128,
quota(d,2,6,mid) = 15c/4096.
```

At each stage-five level-one `topRise`, the incoming parent has `G=L=H=0`.
Apply `d2FlowStage_regular_child_g_bound_of_inputs` to its actual gate: for
each resulting level-two child, `512*G2 <= 2*capacity(d,1,5) = c`. The
stage-five invariant gives the level-two endpoint balance because this cap is
strictly below native size. The gate also needs its incoming level-two reserve
`15*2^(3d-5) = 15c/256`; that reserve discharges the stage-five top-rise gate.
It is not the reserve for the stage-six mid gate: that gate sees the level-three
children after stage-five's bot-descending cuts.

For each stage-five level-three `botDesc`, its actual input gate gives
`G3 >= 0`, so its updated parent deficit is at least its quota,
`15c/128`. These level-three outputs are the child roots seen by their
stage-six level-two parent. Thus each of the eight children has at least
`15c/128`, which implies the stage-six endpoint reserves `c <= 128*U_j`.
Their total mass also exceeds the stage-six quota plus parent deficit:
`8*(15c/128) - c/512 >= 15c/4096 + c/512`.
The fixed quota is even and satisfies `256*quota <= c` by the existing
schedule lemmas. Together these facts give the complete ordinary `mid` gate
at every stage-six level-two node.

The stage-six level-four `botRise` nodes are level-four children overwritten
by the stage-five level-three `botDesc` cut. `d2FlowStage_regular_child_setroot`
identifies their root data as `(cutLeft+cutRight, cutLeft, cutRight)`, hence
their endpoints balance exactly. Stage six is inactive below level four, so
the arbitrary deeper subtrees satisfy its recursive input obligations by a
tree induction.

The complete bridge is now kernel checked in `D2ScheduleReserve.lean`:

* `d2FlowCandidateStage6_frontiers` proves the active levels and roles stated
  above, and that level six is inactive, for every `d >= 9`.
* `d2FlowCandidateStage6_capacity_identities` proves
  `2*capacity(d,1,5)=capacity(d,2,6)` and
  `capacity(d,3,5)=32*capacity(d,2,6)`.
* `d2FlowCandidateStage6_mid_inputs_of_state` proves the complete local
  level-two `mid` gate from the precise remaining state hypotheses: the parent
  balance, `512*G <= c`, a stage-five bot-desc quota lower bound on each of
  its eight children, and recursive stage-six input predicates below them.
  Its proof checks the quota, allocation, parity, and both endpoint reserves.
* `d2FlowCandidateStage6_actual_mid_state` extracts the needed cap and all
  eight child reserves from the actual stage-five output. The cap is exported
  by the level-one top-rise gate; the child reserves are the stage-five
  level-three bot-descending quotas.
* `d2FlowCandidateStage6_actual_levelFour_inputs` uses the exact ordinary-cut
  root overwrite to prove balance at every stage-six level-four bot-rise node;
  `d2FlowStageInvInputs_all_inactive` handles all descendants below it.
* `d2FlowCandidateStage6_actual_levelThree_inputs`,
  `d2FlowCandidateStage6_actual_levelTwo_inputs_closed`, and
  `d2FlowCandidateStage6_actual_levelOne_inputs` assemble the recursive gates.
  `d2FlowCandidateStage6_actual_inputs` also proves the root top-descending
  gate from the zero-root bootstrap shape and the stage-five invariant.
* `d2FlowCandidateStage6_preserves_inv` composes the generic local theorem
  with those actual gates, extending the checked whole-tree invariant through
  six scheduled stages for every `d >= 9`.

The focused check
`lake env lean ../prefix-flux/D2ScheduleReserve.lean` passes from
`upper-bound/experiments/runaware`; the file has no `sorry` or `admit`.

This closes only the first repeating transition, not the repeating invariant.
The all-depth reserve/cap induction, `279/256` sender factor, provider/rank
recurrence, and terminal sorting argument remain separate obligations, so the
coefficient `273` remains conditional.

The next schedule pair is now classified by
`d2FlowCandidateStage7_frontiers`: it again has level-one `topRise` and
level-three `botDesc`, with level five inactive. The next useful test is to
derive those actual stage-seven gates from the stage-six output and invariant;
that will show whether the first two-stage pattern can be bootstrapped into an
inductive schedule argument.
