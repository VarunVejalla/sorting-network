import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

private theorem d2DecideFalseOfNot {p : Prop} [Decidable p]
    (hn : ¬ p) : decide p = false := by
  cases h : decide p with
  | false => rfl
  | true => exact (hn (of_decide_eq_true h)).elim

/-- The schedule is inactive at level seven throughout updates 0 through 14. -/
theorem d2FlowCandidateActive_stageBefore15_levelSeven_false
    (height : Nat) :
    ∀ k, k < 15 -> d2FlowCandidateActive (height + 8) k 7 = false := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [d2FlowCandidateActive]
  · by_cases hk1 : k = 1
    · subst k
      simp [d2FlowCandidateActive]
    · have hfalse :
          ¬ (2 <= k ∧ k <= tfD2 (height + 8) ∧ 7 % 2 = k % 2 ∧
            3 * 7 + 3 * (height + 8) >= 2 * k + 11 ∧ 3 * 7 < k + 8) := by
        intro h
        rcases h with ⟨_, _, hpar, _, hwindow⟩
        have hk14 : k = 14 := by omega
        subst k
        norm_num at hpar
      unfold d2FlowCandidateActive
      rw [if_neg hk0, if_neg hk1]
      exact d2DecideFalseOfNot hfalse

/-- Updates 0 through 14 do not activate any level strictly below seven. -/
theorem d2FlowCandidateActive_stageBefore15_deeper_false
    (height : Nat) :
    ∀ k, k < 15 -> ∀ q, 7 < q ->
      d2FlowCandidateActive (height + 8) k q = false := by
  intro k hk q hq
  by_cases hk0 : k = 0
  · subst k
    have hq0 : q ≠ 0 := by omega
    simp [d2FlowCandidateActive, hq0]
  · by_cases hk1 : k = 1
    · subst k
      have hq1 : q ≠ 1 := by omega
      simp [d2FlowCandidateActive, hq1]
    · have hfalse :
          ¬ (2 <= k ∧ k <= tfD2 (height + 8) ∧ q % 2 = k % 2 ∧
            3 * q + 3 * (height + 8) >= 2 * k + 11 ∧ 3 * q < k + 8) := by
        intro h
        rcases h with ⟨_, _, _, _, hwindow⟩
        have hlow : 24 <= 3 * q := by omega
        have hhigh : k + 8 <= 22 := by omega
        omega
      unfold d2FlowCandidateActive
      rw [if_neg hk0, if_neg hk1]
      exact d2DecideFalseOfNot hfalse

end Chvatal.D2Reserve
