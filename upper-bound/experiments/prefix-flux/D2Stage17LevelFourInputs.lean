import D2Stage17LevelFiveInputs

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- Every actual Stage-17 level-four node is inactive; its level-five
children satisfy the complete active middle-sender input contract. -/
theorem d2FlowCandidateRun_stage17_levelFour_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run17 j) k) m) l
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 4 tree := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild run17 j) k) m) l
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse : d2FlowCandidateActive d 17 4 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage17_iff hd14).mp ht
    rcases hlevels with h | h | h | h <;> omega
  apply d2FlowStageInvInputs_inactive_of_children
    (active := d2FlowCandidateActive d 17)
    (role := d2FlowCandidateRole d 17)
    (quota := d2FlowCandidateQuota d 17)
    (cap := fun x => d2FlowCandidateCapacity d x 17)
    8192 4 tree hfalse
  intro q
  have hq := d2FlowCandidateRun_stage17_levelFive_inputs
    childDepth hd j k m l q
  simpa [d, initial, run17, tree] using hq

end Chvatal.D2Reserve
