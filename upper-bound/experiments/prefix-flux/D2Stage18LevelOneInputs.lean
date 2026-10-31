import D2Stage18LevelTwoInputs

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- Stage-18 level one is inactive; its eight children satisfy the complete
startup/late level-two contract. -/
theorem d2FlowCandidateRun_stage18_levelOne_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (j : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild run18 j
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 1 tree := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let tree := d2FlowTreeChild run18 j
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse : d2FlowCandidateActive d 18 1 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage18_iff hd14).mp ht
    by_cases hsmall : d <= 15 <;> simp [hsmall] at hlevels <;> omega
  apply d2FlowStageInvInputs_inactive_of_children
    (active := d2FlowCandidateActive d 18)
    (role := d2FlowCandidateRole d 18)
    (quota := d2FlowCandidateQuota d 18)
    (cap := fun x => d2FlowCandidateCapacity d x 18)
    8192 1 tree hfalse
  intro k
  have hk := d2FlowCandidateRun_stage18_levelTwo_inputs
    childDepth hd j k
  simpa [d, initial, run18, tree] using hk

end Chvatal.D2Reserve
