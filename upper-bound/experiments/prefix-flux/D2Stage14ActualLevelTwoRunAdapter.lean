import D2Stage14ActualLevelTwoInputs

namespace Chvatal.D2Reserve

set_option maxHeartbeats 30000000

theorem d2FlowCandidateStage14_actual_levelTwo_inputs_for_run
    (childDepth : Nat) (hd : 7 <= childDepth)
    (run : D2FlowTree (childDepth + 7))
    (hrun : run = d2FlowCandidateRun (childDepth + 7)
      (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
    (j k : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (childDepth + 7) 14)
      (d2FlowCandidateRole (childDepth + 7) 14)
      (d2FlowCandidateQuota (childDepth + 7) 14)
      (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 2
      (d2FlowTreeAtPath 2 run (.cons j (.cons k .nil))) := by
  subst run
  exact d2FlowCandidateStage14_actual_levelTwo_inputs childDepth hd j k

end Chvatal.D2Reserve
