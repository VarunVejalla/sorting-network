import D2Stage14MidBudgets

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000
set_option linter.constructorNameAsVariable false

/-- Every actual level-two node in the Stage-14 input tree is balanced and
fits its scheduled deficit allowance, by projecting Stage 13's level-one
top-rise update to the node. -/
theorem d2FlowCandidateStage14_actual_levelTwo_balance_deficit
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k,
      let run : D2FlowTree (childDepth + 7) :=
        d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 14
      let path : D2FlowPath 2 := .cons j (.cons k .nil)
      let tree : D2FlowTree (childDepth + 5) :=
        d2FlowTreeAtPath 2 run path
      (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
          d2FlowTreeRootDeficit tree /\
        512 * d2FlowTreeRootDeficit tree <=
          d2FlowCandidateCapacity (childDepth + 7) 2 14 := by
  intro j k
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let before : D2FlowTree d := d2FlowCandidateRun d initial 13
  let run : D2FlowTree d := d2FlowCandidateRun d initial 14
  let path : D2FlowPath 2 := .cons j (.cons k .nil)
  let output : D2FlowTree (childDepth + 5) := d2FlowTreeAtPath 2 run path
  let gate : D2FlowTree (childDepth + 5) -> Prop := fun tree =>
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
        d2FlowTreeRootDeficit tree /\
      512 * d2FlowTreeRootDeficit tree <= d2FlowCandidateCapacity d 2 14
  let source := d2FlowTreeChild before j
  have hinputs := d2FlowCandidateStage13_actual_levelOne_inputs
    (childDepth + 1) (by omega) j
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun r => d2FlowCandidateCapacity d r 13) 1 source at hinputs
  have hprojection := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive d 13)
    (role := d2FlowCandidateRole d 13)
    (quota := d2FlowCandidateQuota d 13)
    (h := childDepth + 5) (i := 0) before j k
  have hrun : run = d2FlowCandidateStage d 13 before := rfl
  have hprojection' : output =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 13)
          (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
          (childDepth + 6) 1 source) k := by
    change d2FlowTreeChild (d2FlowTreeChild run j) k = _
    rw [hrun]
    exact hprojection
  cases hsource : source with
  | node G low high children =>
      rw [hsource] at hinputs
      have hprojectionNode := hprojection'
      rw [hsource] at hprojectionNode
      have hstate :=
        d2FlowCandidateStage14_levelTwo_child_state_of_stage13_topRise
          d (by omega) (childDepth + 5) G low high children hinputs k
      have hstate' : gate
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
              (childDepth + 6) 1 (.node G low high children)) k) := hstate
      have htransported : gate output :=
        Eq.mp (congrArg gate hprojectionNode.symm) hstate'
      change gate output
      exact htransported

end Chvatal.D2Reserve
