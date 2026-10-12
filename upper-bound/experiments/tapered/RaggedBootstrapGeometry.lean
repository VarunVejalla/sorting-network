import CandidateSeed
import Mathlib.Tactic

namespace Tapered945

/-- The fixed row count used by the address-dependent first separator. -/
def bootstrapRows : Nat := 2 ^ 43

/-- Its column count, so the input at a level-one bag has exactly `C` wires. -/
def bootstrapColumns (d : Nat) : Nat := 2 ^ (6 * d - 49)

abbrev isEndAddress (x : Nat) : Prop := x = 0 ∨ x = 63

def bootstrapAddressQ (x : Nat) : Rat :=
  if isEndAddress x then qEnd else qMid

def bootstrapDownCoeff (x : Nat) : Rat :=
  if isEndAddress x then rEnd else rMid

/-- The debt at a level-one address is the first digit's correction divided by 64. -/
def firstAddressDebt (x : Nat) : Rat := bootstrapAddressQ x / 64

theorem first_address_debt_cases (x : Nat) :
    firstAddressDebt x = qEnd / 64 ∨ firstAddressDebt x = qMid / 64 := by
  by_cases hx : isEndAddress x
  · left
    simp [firstAddressDebt, bootstrapAddressQ, hx]
  · right
    simp [firstAddressDebt, bootstrapAddressQ, hx]

/-- Number of output rows in slot `j`, for a level-one parent with address `x`.
The four cases are all integers, despite the rational definition of the profile. -/
def bootstrapSlotRows (x j : Nat) : Nat :=
  (if isEndAddress j then 2047 * 2 ^ 26 else 2 ^ 37) +
    (if isEndAddress x then 0 else 2 ^ 9) -
    (if isEndAddress x then 31 * 2 ^ 9 else 0)

/-- The row count sent upward by a level-one sender. -/
def bootstrapUpRows (x : Nat) : Nat :=
  if isEndAddress x then 2 ^ 27 + 31 * 2 ^ 15 else 2 ^ 27 - 2 ^ 15

def bootstrapFringeRows (x : Nat) : Nat := bootstrapUpRows x / 2

def bootstrapAverageDownRows (x : Nat) : Nat :=
  (bootstrapRows - bootstrapUpRows x) / 64

theorem bootstrapRows_gt_lower : 2 ^ 42 < bootstrapRows := by
  norm_num [bootstrapRows]

theorem bootstrapRows_le_upper : bootstrapRows ≤ 2 ^ 43 := by
  norm_num [bootstrapRows]

theorem bootstrapColumns_ge16 (d : Nat) (hd : 14 ≤ d) :
    16 ≤ bootstrapColumns d := by
  unfold bootstrapColumns
  have he : 4 ≤ 6 * d - 49 := by omega
  calc
    16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (6 * d - 49) := Nat.pow_le_pow_right (by norm_num) he

theorem bootstrap_input_factorization (d : Nat) (hd : 14 ≤ d) :
    seedRootDown d = bootstrapRows * bootstrapColumns d := by
  unfold seedRootDown bootstrapRows bootstrapColumns
  rw [show 6 * d - 6 = 43 + (6 * d - 49) by omega, pow_add]

theorem bootstrap_up_rows_even (x : Nat) : Even (bootstrapUpRows x) := by
  unfold bootstrapUpRows
  split_ifs <;> norm_num [Even]

theorem bootstrap_fringe_rows_exact (x : Nat) :
    bootstrapUpRows x = 2 * bootstrapFringeRows x := by
  by_cases hx : isEndAddress x
  · norm_num [bootstrapUpRows, bootstrapFringeRows, hx, isEndAddress]
  · norm_num [bootstrapUpRows, bootstrapFringeRows, hx, isEndAddress]

theorem bootstrap_slot_rows_exact (x j : Nat) :
    (bootstrapSlotRows x j : Rat) =
    (bootstrapDownCoeff j + firstAddressDebt x / 64) * bootstrapRows := by
  by_cases hx : isEndAddress x <;> by_cases hj : isEndAddress j
  · simp [bootstrapSlotRows, firstAddressDebt, bootstrapDownCoeff, hx, hj,
      isEndAddress, bootstrapRows, bootstrapAddressQ, qEnd, rEnd]
    norm_num
  · simp [bootstrapSlotRows, firstAddressDebt, bootstrapDownCoeff, hx, hj,
      isEndAddress, bootstrapRows, bootstrapAddressQ, qEnd, rMid]
    norm_num
  · simp [bootstrapSlotRows, firstAddressDebt, bootstrapDownCoeff, hx, hj,
      isEndAddress, bootstrapRows, bootstrapAddressQ, qMid, rEnd]
    norm_num
  · simp [bootstrapSlotRows, firstAddressDebt, bootstrapDownCoeff, hx, hj,
      isEndAddress, bootstrapRows, bootstrapAddressQ, qMid, rMid]
    norm_num

theorem bootstrap_up_rows_exact (x : Nat) :
    (bootstrapUpRows x : Rat) =
      (upFlow - firstAddressDebt x + 1 / cap) * bootstrapRows := by
  by_cases hx : isEndAddress x
  · simp [bootstrapUpRows, hx, firstAddressDebt, isEndAddress, bootstrapAddressQ,
      qEnd, upFlow, cap, bootstrapRows]
    norm_num
  · simp [bootstrapUpRows, hx, firstAddressDebt, isEndAddress, bootstrapAddressQ,
      qMid, upFlow, cap, bootstrapRows]
    norm_num

theorem bootstrap_slots_sum (x : Nat) :
    (∑ j : Fin 64, bootstrapSlotRows x j.val) =
      64 * bootstrapAverageDownRows x := by
  by_cases hx : isEndAddress x
  · simp [bootstrapSlotRows, bootstrapAverageDownRows, bootstrapRows,
      bootstrapUpRows, isEndAddress, hx, Fin.sum_univ_succ]
  · simp [bootstrapSlotRows, bootstrapAverageDownRows, bootstrapRows,
      bootstrapUpRows, isEndAddress, hx, Fin.sum_univ_succ]

theorem bootstrap_row_split (x : Nat) :
    bootstrapRows = bootstrapUpRows x +
      ∑ j : Fin 64, bootstrapSlotRows x j.val := by
  rw [bootstrap_slots_sum]
  unfold bootstrapAverageDownRows
  have hu : bootstrapUpRows x ≤ bootstrapRows := by
    unfold bootstrapUpRows bootstrapRows
    split_ifs <;> norm_num
  have hdiv : 64 ∣ bootstrapRows - bootstrapUpRows x := by
    unfold bootstrapUpRows bootstrapRows
    split_ifs <;> norm_num
  have heq : 64 * ((bootstrapRows - bootstrapUpRows x) / 64) =
      bootstrapRows - bootstrapUpRows x := Nat.mul_div_cancel' hdiv
  omega

theorem bootstrap_avg_split (x : Nat) :
    bootstrapRows = 2 * bootstrapFringeRows x +
      64 * bootstrapAverageDownRows x := by
  rw [← bootstrap_fringe_rows_exact]
  rw [show 64 * bootstrapAverageDownRows x =
      ∑ j : Fin 64, bootstrapSlotRows x j.val by rw [bootstrap_slots_sum]]
  exact bootstrap_row_split x

/-- The variable-width first-stage profile has the same average separator
geometry as the existing level-one template. -/
theorem bootstrap_level_one_node_geom (d x : Nat) (hd : 14 ≤ d) :
    Nonempty (Chvatal.NodeGeom (seedRootDown d)
      (bootstrapUpRows x * bootstrapColumns d)
      (bootstrapAverageDownRows x * bootstrapColumns d)) := by
  have hsplit := bootstrap_avg_split x
  have hfactor := bootstrap_input_factorization d hd
  refine ⟨⟨bootstrapRows, bootstrapColumns d,
    bootstrapFringeRows x, bootstrapAverageDownRows x, ?_, ?_, ?_, ?_,
    bootstrapRows_gt_lower, bootstrapRows_le_upper,
    bootstrapColumns_ge16 d hd, ?_⟩⟩
  · exact hsplit
  · exact hfactor
  · rw [bootstrap_fringe_rows_exact]
  · rfl
  · have hfEven : Even (bootstrapFringeRows x) := by
      unfold bootstrapFringeRows bootstrapUpRows
      split_ifs <;> norm_num [Even]
    have hfLarge : 131040 ≤ bootstrapFringeRows x := by
      unfold bootstrapFringeRows bootstrapUpRows
      split_ifs <;> norm_num
    exact Or.inr ⟨hfLarge, hfEven⟩

end Tapered945
