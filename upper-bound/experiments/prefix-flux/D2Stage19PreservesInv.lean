import D2Stage19LevelOneInputs
import D2Stage18PreservesInv

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- The complete Stage-19 sender contracts preserve the reserve invariant
from Run 19 to Run 20 for every depth d >= 16. -/
theorem d2FlowCandidateStage19_preserves_inv
    (childDepth : Nat) (hd : 7 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 9)
        (d2FlowTreeInitial 8192 (childDepth + 9)) 20) := by
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 19
  have hinv : d2FlowTreeInv 8192 before := by
    simpa [d, initial, before] using
      d2FlowCandidateStage18_preserves_inv (childDepth + 2) (by omega)
  have hfalse0 : d2FlowCandidateActive d 19 0 = false := by
    have hd14 : 14 <= d := by dsimp [d]; omega
    cases h : d2FlowCandidateActive d 19 0 with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage19_iff (i := 0) hd14).mp h
        by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
  have hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun q => d2FlowCandidateCapacity d q 19) 0 before := by
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (cap := fun q => d2FlowCandidateCapacity d q 19)
      8192 0 before hfalse0
    intro j
    simpa [d, initial, before] using
      d2FlowCandidateRun_stage19_levelOne_inputs childDepth hd j
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive d 19)
    (role := d2FlowCandidateRole d 19)
    (quota := d2FlowCandidateQuota d 19)
    (cap := fun q => d2FlowCandidateCapacity d q 19)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192 (d2FlowCandidateRun d initial 20)
  rw [d2FlowCandidateRun.eq_def]
  exact hpres

end Chvatal.D2Reserve
