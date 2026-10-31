import D2Stage14ActualLevelFourInputs

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000
set_option linter.constructorNameAsVariable false

/-- Level three is inactive at Stage 14. Its complete input contract follows
from the actual level-four contracts below every child. -/
theorem d2FlowCandidateStage14_actual_levelThree_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k m,
      let run : D2FlowTree (childDepth + 7) :=
        d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 14
      let path : D2FlowPath 3 := .cons j (.cons k (.cons m .nil))
      let tree : D2FlowTree (childDepth + 4) :=
        d2FlowTreeAtPath 3 run path
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 3
        tree := by
  intro j k m
  let d := childDepth + 7
  let run : D2FlowTree d :=
    d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let path : D2FlowPath 3 := .cons j (.cons k (.cons m .nil))
  let tree : D2FlowTree (childDepth + 4) := d2FlowTreeAtPath 3 run path
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
    (d2FlowCandidateQuota d 14)
    (fun x => d2FlowCandidateCapacity d x 14) 3 tree
  have hinactive3 : d2FlowCandidateActive d 14 3 = false := by
    simp [d2FlowCandidateActive]
  have hchildren : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun x => d2FlowCandidateCapacity d x 14) 4
        (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowCandidateStage14_actual_levelFour_inputs
      childDepth hd j k m s
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
    (d2FlowCandidateQuota d 14)
    (fun x => d2FlowCandidateCapacity d x 14) 3 tree
  exact d2FlowStageInvInputs_inactive_of_children 8192 3 tree
    hinactive3 hchildren

/-- Run-parameterized adapter for the recursive contract: exposing the run
as an argument lets adjacent path lemmas share it without unfolding the
concrete candidate run during typeclass-style unification. -/
theorem d2FlowCandidateStage14_actual_levelThree_inputs_for_run
    (childDepth : Nat) (hd : 7 <= childDepth)
    (run : D2FlowTree (childDepth + 7))
    (hrun : run = d2FlowCandidateRun (childDepth + 7)
      (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
    (j k m : Fin 8) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (childDepth + 7) 14)
      (d2FlowCandidateRole (childDepth + 7) 14)
      (d2FlowCandidateQuota (childDepth + 7) 14)
      (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 3
      (d2FlowTreeAtPath 3 run (.cons j (.cons k (.cons m .nil)))) := by
  subst run
  exact d2FlowCandidateStage14_actual_levelThree_inputs
    childDepth hd j k m

end Chvatal.D2Reserve
