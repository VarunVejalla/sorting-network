import D2Stage14PreservesInv
import D2Stage15LevelOneInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

/-- Stage 15 preserves the D2 flow invariant on the actual scheduled run.
The root is inactive; its level-one children carry the four checked active
sender contracts down through the recursive input predicate. -/
theorem d2FlowCandidateStage15_preserves_inv
    (childDepth : Nat) (hd : 7 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 16) := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 15
  have hinv : d2FlowTreeInv 8192 before :=
    d2FlowCandidateStage14_preserves_inv childDepth hd
  have hstrict : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun i => d2FlowCandidateCapacity d i 15) 0 before := by
    have hfalse : d2FlowCandidateActive d 15 0 = false := by
      cases hvalue : d2FlowCandidateActive d 15 0 with
      | false => rfl
      | true =>
          have hlevel := d2FlowCandidateActive_stage15_level_bound hvalue
          rcases hlevel with h | h | h | h <;> omega
    have hchildren : forall j : Fin 8,
        d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
          (d2FlowCandidateQuota d 15)
          (fun i => d2FlowCandidateCapacity d i 15) 1
          (d2FlowTreeChild before j) := by
      intro j
      have hj := d2FlowCandidateRun_stage15_levelOne_inputs
        childDepth hd j
      change d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun i => d2FlowCandidateCapacity d i 15) 1
        (d2FlowTreeChild before j) at hj
      exact hj
    have hroot : d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun i => d2FlowCandidateCapacity d i 15) 0 before :=
      d2FlowStageInvInputs_inactive_of_children
        (active := d2FlowCandidateActive d 15)
        (role := d2FlowCandidateRole d 15)
        (quota := d2FlowCandidateQuota d 15)
        (cap := fun i => d2FlowCandidateCapacity d i 15)
        8192 0 (h := childDepth + 6) before hfalse hchildren
    exact hroot
  have htolerant := d2FlowStageInvInputs_tolerant_of_strict before hstrict
  have hpreserved := d2FlowStage_preserves_inv_of_tolerant_inputs
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (cap := fun i => d2FlowCandidateCapacity d i 15)
    (i := 0) before hinv htolerant
  change d2FlowTreeInv 8192 (d2FlowCandidateStage d 15 before)
  exact hpreserved

end Chvatal.D2Reserve
