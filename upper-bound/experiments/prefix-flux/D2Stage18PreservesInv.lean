import D2Stage18RootInputs

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- The checked Stage-18 sender contracts carry the reserve invariant from
Run 18 to Run 19 at every eligible depth. -/
theorem d2FlowCandidateStage18_preserves_inv
    (childDepth : Nat) (hd : 7 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 19) := by
  let d := (childDepth + 6) + 1
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 18
  have hinv : d2FlowTreeInv 8192 before := by
    simpa [d, initial, before] using
      d2FlowCandidateStage17_preserves_inv childDepth hd
  have hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun q => d2FlowCandidateCapacity d q 18) 0 before := by
    simpa [d, initial, before] using
      d2FlowCandidateRun_stage18_root_inputs childDepth hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive d 18)
    (role := d2FlowCandidateRole d 18)
    (quota := d2FlowCandidateQuota d 18)
    (cap := fun q => d2FlowCandidateCapacity d q 18)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192 (d2FlowCandidateRun d initial 19)
  rw [d2FlowCandidateRun.eq_def]
  exact hpres

end Chvatal.D2Reserve
