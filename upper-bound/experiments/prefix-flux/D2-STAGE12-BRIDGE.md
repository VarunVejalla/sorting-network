# D2 finite reserve bridge through Stage 13

Checked 2026-10-26 on branch `sub300-structural`.

`D2ScheduleReserve.lean` now proves the saturated-aware flow-tree invariant
through the actual finite run transition at Stage 13. The latest theorem is
`d2FlowCandidateStage13_preserves_inv`: for `depth >= 8`, it carries the
invariant from the Stage 13 input tree to the Stage 14 input tree. The file
also contains the actual-input gate assemblies for Stages 10 through 13.
The focused check passed with:

```text
cd upper-bound/experiments/runaware
lake env lean ../prefix-flux/D2ScheduleReserve.lean
```

This extends only the checked finite prefix by one stage. It does not prove
the reserve invariant at every later stage, the fixed local separator
provider, the bridge from local rank/port errors to the flow state, or
terminal purity.

The Stage-13 frontier classifier has now been added and checked in the same
focused Lean run: for `d >= 13`, its active levels are 1 (`topRise`), 3
(`mid`), and 5 (`botDesc`); level 7 is inactive. This repeats Stage 11's odd
frontier. Stage 12 has the matching even frontier at levels 0 (`topDesc`), 2
and 4 (`mid`), and 6 (`botRise`). This is evidence for a two-stage role period,
but not yet a proof that the reserve contracts repeat.

Stage 13's actual level-one, level-three, and level-five gates are now
assembled from the Stage-12 outputs, and `d2FlowCandidateStage13_preserves_inv`
checks the actual transition. This is evidence for the two-stage role period,
not an all-depth induction. The next schedule proof should abstract the paired
Stage-12/13 reserve transfer into a role-periodic invariant rather than
unrolling further isolated stages. The main theorem still needs an all-stage
reserve invariant, a fixed local separator provider, the bridge from local
rank/port errors to the flow state, and terminal purity.

`D2ScheduleReserve.lean` now also proves the Stage-13 level-three
endpoint-reserve theorem and its local mid-sender and boundary-mass
interfaces. The Stage-12 level-four mid quota gives 15 times the required
endpoint reserve. The actual Stage-13 level-three inputs are now also
kernel-checked: they derive from the actual Stage-12 level-two mid cut, the
endpoint reserves, and the recursive level-four and level-five gates. The
level-four and level-five actual input gates are checked dependencies.

For the Stage-13 level-five gate, an exact native-reserve carry through
Stage 11 is invalid: the level-five `botDesc` cut replaces child deficits by
the cut profile. The right transfer uses its endpoint profile instead: the
first and last children retain at least half the old quota, and half that
quota exceeds Stage 13's endpoint requirement. The finite-run transfer is now
kernel checked by `d2FlowCandidateStage13_actual_levelSix_endpoint_reserves`:
it extracts the actual Stage 11 gate at the selected level-five node, applies
the tolerant endpoint-profile theorem, projects the result to the Stage 12
tree, and transports it through Stage 12's inactive level-five cut and
monotone level-six recursion. This proves only the two endpoint reserve
inequalities needed for Stage 13's level-five sender. The full level-five
input contract is now also kernel checked by
`d2FlowCandidateStage13_actual_levelFive_inputs`. It gets the node cap and
balance from the actual Stage-12 level-four mid cut, uses the endpoint
transfer above for its two reserves, and discharges the deeper recursive
inputs because Stage 13 has no active sender from level six onward. Its
actual level-one contract uses the Stage-12 top-descending reset and the
Stage-12 level-two mid quotas; the Stage-12 inactive-level projection is
kernel checked. `d2FlowCandidateStage13_actual_inputs` and
`d2FlowCandidateStage13_preserves_inv` then package the three active levels
and prove the actual Run-13 to Run-14 transition. The focused Lean check
completed successfully on 2026-10-26 with no diagnostics. Do not infer an
all-stage reserve theorem from this finite extension.

For the conditional `(3,3,2)` prefix cost `p=273`, the inversion-localization
cleanup reaches coefficient 300 when the final global inversion count is at
most `N^theta` with `theta <= 27/301`; strict inequality gives a coefficient
strictly below 300. The global inversion/rank-transfer theorem is still open.
See `INVERSION-LOCALIZATION-GATE.md` and `D2-PORT-VARIANCE-TRANSFER.md` for
those separate obligations.
