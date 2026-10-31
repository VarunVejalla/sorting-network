import D2Stage14ActualRootInputs

namespace Chvatal.D2Reserve

set_option maxHeartbeats 30000000
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-- Stage 14 preserves the invariant on its actual scheduled run. -/
theorem d2FlowCandidateStage14_preserves_inv
    (childDepth : Nat) (hd : 7 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 15) := by
  let d := childDepth + 7
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  have hinv : d2FlowTreeInv 8192 before := by
    simpa [d, before] using
      d2FlowCandidateStage13_preserves_inv (childDepth + 1) (by omega)
  have hstrict : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
      (d2FlowCandidateQuota d 14)
      (fun q => d2FlowCandidateCapacity d q 14) 0 before := by
    change d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (childDepth + 7) 14)
      (d2FlowCandidateRole (childDepth + 7) 14)
      (d2FlowCandidateQuota (childDepth + 7) 14)
      (fun q => d2FlowCandidateCapacity (childDepth + 7) q 14) 0
      (d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
    exact d2FlowCandidateStage14_actual_root_inputs childDepth hd
  have hinputs := d2FlowStageInvInputs_tolerant_of_strict before hstrict
  have hpres := d2FlowStage_preserves_inv_of_tolerant_inputs
    (active := d2FlowCandidateActive d 14)
    (role := d2FlowCandidateRole d 14)
    (quota := d2FlowCandidateQuota d 14)
    (cap := fun q => d2FlowCandidateCapacity d q 14)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192 (d2FlowCandidateStage d 14 before)
  simpa [d, before, d2FlowCandidateRun, d2FlowCandidateStage] using hpres

end Chvatal.D2Reserve
