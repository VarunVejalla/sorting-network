import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

private theorem decide_false_of_not {p : Prop} [Decidable p]
    (hn : Not p) : decide p = false := by
  cases h : decide p with
  | false => rfl
  | true => exact (hn (of_decide_eq_true h)).elim

/-- From level seven down, Stage 14 is completely inactive. -/
theorem d2FlowCandidateStage14_inactive_inputs
    {d h i : Nat} (hd : 14 ≤ d) (hi : 7 ≤ i)
    (tree : D2FlowTree h) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 14)
      (d2FlowCandidateRole d 14)
      (d2FlowCandidateQuota d 14)
      (fun k => d2FlowCandidateCapacity d k 14) i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowStageInvInputs]
      constructor
      · intro j
        exact ih j (i := i + 1) (by omega)
      · have hnot : ¬ (2 ≤ 14 ∧ 14 ≤ tfD2 d ∧ i % 2 = 14 % 2 ∧
            3 * i + 3 * d ≥ 2 * 14 + 11 ∧ 3 * i < 14 + 8) := by omega
        have h14zero : Not ((14 : Nat) = 0) := by omega
        have h14one : Not ((14 : Nat) = 1) := by omega
        have hfalse : d2FlowCandidateActive d 14 i = false := by
          unfold d2FlowCandidateActive
          rw [if_neg h14zero, if_neg h14one]
          exact decide_false_of_not hnot
        simp [hfalse]

set_option maxHeartbeats 10000000

end Chvatal.D2Reserve
