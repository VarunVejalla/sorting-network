import D2Stage14ActualLevelTwoRunAdapter
import D2Stage14Contract

namespace Chvatal.D2Reserve

set_option maxHeartbeats 30000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false

/-- Project the checked Stage-14 level-two input contract to the corresponding
nested-child tree, so downstream sender bounds do not normalize `AtPath`. -/
theorem d2FlowCandidateStage14_actual_levelTwo_child_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (j k : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (childDepth + 7) 14)
      (d2FlowCandidateRole (childDepth + 7) 14)
      (d2FlowCandidateQuota (childDepth + 7) 14)
      (fun q => d2FlowCandidateCapacity (childDepth + 7) q 14) 2
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) := by
  have htwo := d2FlowCandidateStage14_actual_levelTwo_inputs_for_run
    childDepth hd
    (d2FlowCandidateRun (childDepth + 7)
      (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
    (by rfl) j k
  exact d2FlowStageInvInputs_path2_child
    (active := d2FlowCandidateActive (childDepth + 7) 14)
    (role := d2FlowCandidateRole (childDepth + 7) 14)
    (quota := d2FlowCandidateQuota (childDepth + 7) 14)
    (cap := fun q => d2FlowCandidateCapacity (childDepth + 7) q 14)
    8192 (h := childDepth + 5)
    (d2FlowCandidateRun (childDepth + 7)
      (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j k htwo

end Chvatal.D2Reserve
