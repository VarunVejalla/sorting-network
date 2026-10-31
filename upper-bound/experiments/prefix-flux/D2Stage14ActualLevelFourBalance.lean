import D2Stage14MidBudgets

namespace Chvatal.D2Reserve

set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

/-- The preceding balance/deficit bridge applies at every actual level-four
node in the Stage-14 input tree, using the proved Stage-13 level-three gates. -/
theorem d2FlowCandidateStage14_actual_levelFour_balance_deficit
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k m s,
      let output := d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) s
      (d2FlowTreeRootData output).2.1 + (d2FlowTreeRootData output).2.2 =
          d2FlowTreeRootDeficit output /\
        512 * d2FlowTreeRootDeficit output <=
          d2FlowCandidateCapacity (childDepth + 7) 4 14 := by
  intro j k m s
  dsimp only
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 13
  let source := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m
  have hinputs := d2FlowCandidateStage13_actual_levelThree_inputs
    (childDepth + 1) (by omega) j k m
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun r => d2FlowCandidateCapacity d r 13) 3 source at hinputs
  have hprojection := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 13)
    (role := d2FlowCandidateRole d 13)
    (quota := d2FlowCandidateQuota d 13)
    (h := childDepth + 3) (i := 0) before j k m s
  have hrun : d2FlowCandidateRun d initial 14 =
      d2FlowCandidateStage d 13 before := rfl
  have hprojection' :
      d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun d initial 14) j) k) m) s =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 13)
          (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
          (childDepth + 4) 3 source) s := by
    rw [hrun]
    exact hprojection
  cases hsource : source with
  | node G low high children =>
      rw [hsource] at hinputs
      rw [hsource] at hprojection'
      have hstate :=
        d2FlowCandidateStage14_levelFour_child_state_of_stage13_mid
          d (by omega) (childDepth + 3) G low high children
          hinputs s
      rw [hprojection']
      exact hstate

end Chvatal.D2Reserve
