import D2Stage15Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

/-- After the stage-15 bottom frontier, every deeper subtree contributes only
vacuous recursive input obligations. -/
theorem d2FlowCandidateStage15_inactive_tail_inputs
    (d i : Nat) (hi : 8 <= i) {h : Nat} (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun k => d2FlowCandidateCapacity d k 15) i tree := by
  apply d2FlowStageInvInputs_all_inactive
  intro k hk
  have hfalse : d2FlowCandidateActive d 15 k = false := by
    cases hvalue : d2FlowCandidateActive d 15 k with
    | false => rfl
    | true =>
        have hlevel := d2FlowCandidateActive_stage15_level_bound hvalue
        rcases hlevel with rfl | rfl | rfl | rfl <;> omega
  exact hfalse

end Chvatal.D2Reserve
