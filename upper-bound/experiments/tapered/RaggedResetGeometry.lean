import RaggedBootstrapGeometry
import Mathlib.Tactic

namespace Tapered945

def resetUnit (d : Nat) : Nat := 2 ^ (6 * d - 28)

def resetSenderInput (d x j : Nat) : Nat :=
  bootstrapSlotRows x j * bootstrapColumns d

/-- A power-of-two row rescaling for the four address classes. An endpoint
parent's middle slot is just below `2^37`, so it also needs the factor 64. -/
def resetScale (x j : Nat) : Nat :=
  if isEndAddress x ∨ isEndAddress j then 64 else 32

def suggestedResetRows (x j : Nat) : Nat :=
  (if isEndAddress j then 64 else 32) * bootstrapSlotRows x j

theorem suggested_middle_scale_falls_below_range :
    suggestedResetRows 0 1 < 2 ^ 42 := by
  norm_num [suggestedResetRows, bootstrapSlotRows, isEndAddress,
    bootstrapRows]

def resetRows (x j : Nat) : Nat := resetScale x j * bootstrapSlotRows x j

def resetColumns (d x j : Nat) : Nat :=
  if isEndAddress x ∨ isEndAddress j then 2 ^ (6 * d - 55)
  else 2 ^ (6 * d - 54)

def resetDownRows (x j : Nat) : Nat :=
  if isEndAddress x ∨ isEndAddress j then 1020 * 2 ^ 27
  else 1020 * 2 ^ 26

def resetDownCount (d : Nat) : Nat := 1020 * resetUnit d

def resetUpCount (d x j : Nat) : Nat :=
  (resetRows x j - 64 * resetDownRows x j) * resetColumns d x j

def resetFringeRows (x j : Nat) : Nat :=
  (resetRows x j - 64 * resetDownRows x j) / 2

theorem reset_columns_factor (d x j : Nat) (hd : 14 ≤ d) :
    bootstrapColumns d = resetScale x j * resetColumns d x j := by
  by_cases h : isEndAddress x ∨ isEndAddress j
  · simp [bootstrapColumns, resetScale, resetColumns, h]
    rw [show 6 * d - 49 = 6 + (6 * d - 55) by omega, pow_add]
    norm_num
  · simp [bootstrapColumns, resetScale, resetColumns, h]
    rw [show 6 * d - 49 = 5 + (6 * d - 54) by omega, pow_add]
    norm_num

theorem reset_down_factor (d x j : Nat) (hd : 14 ≤ d) :
    resetDownCount d = resetDownRows x j * resetColumns d x j := by
  by_cases h : isEndAddress x ∨ isEndAddress j
  · simp [resetDownCount, resetUnit, resetDownRows, resetColumns, h]
    rw [show 6 * d - 28 = 27 + (6 * d - 55) by omega, pow_add]
    norm_num
    ring
  · simp [resetDownCount, resetUnit, resetDownRows, resetColumns, h]
    rw [show 6 * d - 28 = 26 + (6 * d - 54) by omega, pow_add]
    norm_num
    ring

theorem reset_input_factor (d x j : Nat) (hd : 14 ≤ d) :
    resetSenderInput d x j = resetRows x j * resetColumns d x j := by
  unfold resetSenderInput resetRows
  rw [reset_columns_factor d x j hd]
  ring

theorem reset_rows_bounds (x j : Nat) :
    2 ^ 42 < resetRows x j ∧ resetRows x j ≤ 2 ^ 43 := by
  by_cases hx : isEndAddress x <;> by_cases hj : isEndAddress j
  all_goals
    norm_num [resetRows, resetScale, bootstrapSlotRows, isEndAddress,
      hx, hj, bootstrapRows]

theorem reset_fringe_split (x j : Nat) :
    resetRows x j = 2 * resetFringeRows x j +
      64 * resetDownRows x j := by
  by_cases hx : isEndAddress x <;> by_cases hj : isEndAddress j
  all_goals
    norm_num [resetFringeRows, resetRows, resetScale, resetDownRows,
      bootstrapSlotRows, isEndAddress, hx, hj, bootstrapRows]

theorem reset_columns_ge16 (d x j : Nat) (hd : 14 ≤ d) :
    16 ≤ resetColumns d x j := by
  by_cases h : isEndAddress x ∨ isEndAddress j
  · simp [resetColumns, h]
    have he : 4 ≤ 6 * d - 55 := by omega
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (6 * d - 55) := Nat.pow_le_pow_right (by norm_num) he
  · simp [resetColumns, h]
    have he : 4 ≤ 6 * d - 54 := by omega
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (6 * d - 54) := Nat.pow_le_pow_right (by norm_num) he

theorem reset_fringe_good (x j : Nat) :
    131040 ≤ resetFringeRows x j ∧ Even (resetFringeRows x j) := by
  have hlarge : 131040 ≤ resetFringeRows x j := by
    by_cases hx : isEndAddress x <;> by_cases hj : isEndAddress j
    all_goals
      norm_num [resetFringeRows, resetRows, resetScale, resetDownRows,
        bootstrapSlotRows, isEndAddress, hx, hj, bootstrapRows]
  have heven : 2 ∣ resetFringeRows x j := by
    by_cases hx : isEndAddress x <;> by_cases hj : isEndAddress j
    all_goals
      norm_num [resetFringeRows, resetRows, resetScale, resetDownRows,
        bootstrapSlotRows, isEndAddress, hx, hj, bootstrapRows]
  refine ⟨hlarge, ?_⟩
  rcases heven with ⟨k, hk⟩
  exact ⟨k, by omega⟩

theorem reset_fringe_residual (x j : Nat) :
    resetRows x j - 64 * resetDownRows x j = 2 * resetFringeRows x j := by
  have h := reset_fringe_split x j
  omega

/-- Each of the four stage-two address classes has an ordinary separator
geometry with the same down-flow `1020 * 2^(6d-28)`. The endpoint-parent,
middle-slot class uses 64-fold scaling because its row count is slightly below
`2^37`; the other middle-slot class admits the 32-fold scaling. -/
theorem reset_sender_node_geom (d x j : Nat) (hd : 14 ≤ d) :
    Nonempty (Chvatal.NodeGeom (resetSenderInput d x j)
      (resetUpCount d x j) (resetDownCount d)) := by
  have hsplit := reset_fringe_split x j
  have hinput := reset_input_factor d x j hd
  have hdown := reset_down_factor d x j hd
  refine ⟨⟨resetRows x j, resetColumns d x j,
    resetFringeRows x j, resetDownRows x j, hsplit, hinput, ?_, ?_,
    (reset_rows_bounds x j).1, (reset_rows_bounds x j).2,
    reset_columns_ge16 d x j hd, ?_⟩⟩
  · unfold resetUpCount
    rw [reset_fringe_residual]
  · exact hdown
  · obtain ⟨hf, he⟩ := reset_fringe_good x j
    exact Or.inr ⟨hf, he⟩

/-- Conservation at a stage-two sender: its incoming slot is divided into its
up-flow and 64 equal canonical down-flows. -/
theorem reset_sender_conserves (d x j : Nat) (hd : 14 ≤ d) :
    resetSenderInput d x j = resetUpCount d x j + 64 * resetDownCount d := by
  rw [reset_input_factor d x j hd]
  rw [reset_down_factor d x j hd]
  unfold resetUpCount
  rw [reset_fringe_residual]
  rw [reset_fringe_split]
  simp [Nat.add_mul]
  ring

end Tapered945
