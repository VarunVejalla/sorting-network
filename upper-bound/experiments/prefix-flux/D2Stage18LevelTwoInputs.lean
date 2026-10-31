import D2Stage18LevelTwoLateInputs
import D2Stage18LevelTwoStartupInputs

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- The complete Stage-18 level-two contract: top-descending at the two
startup depths and middle thereafter. -/
theorem d2FlowCandidateRun_stage18_levelTwo_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (j k : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild (d2FlowTreeChild run18 j) k
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 2 tree := by
  by_cases hstartup : childDepth <= 8
  · exact d2FlowCandidateRun_stage18_levelTwo_startup_inputs
      childDepth hd hstartup j k
  · have hlate : 9 <= childDepth := by omega
    exact d2FlowCandidateRun_stage18_levelTwo_late_inputs
      childDepth hlate j k

end Chvatal.D2Reserve
