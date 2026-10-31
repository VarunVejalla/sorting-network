import D2Stage20RootInputs
import D2Stage19PreservesInv

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Stage 20's complete sender contracts preserve the reserve invariant from
Run 20 to Run 21 for every candidate depth at least 16. -/
theorem d2FlowCandidateStage20_preserves_inv
    (childDepth : Nat) (hd : 6 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 10)
        (d2FlowTreeInitial 8192 (childDepth + 10)) 21) := by
  let d := childDepth + 10
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 20
  have hinv : d2FlowTreeInv 8192 before := by
    simpa [d, initial, before] using
      d2FlowCandidateStage19_preserves_inv (childDepth + 1) (by omega)
  have hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
      (d2FlowCandidateQuota d 20)
      (fun q => d2FlowCandidateCapacity d q 20) 0 before := by
    simpa [d, initial, before] using
      d2FlowCandidateRun_stage20_root_inputs childDepth hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive d 20)
    (role := d2FlowCandidateRole d 20)
    (quota := d2FlowCandidateQuota d 20)
    (cap := fun q => d2FlowCandidateCapacity d q 20)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192 (d2FlowCandidateRun d initial 21)
  rw [d2FlowCandidateRun.eq_def]
  exact hpres

end Chvatal.D2Reserve
