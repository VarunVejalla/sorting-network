import CandidateFrontier
import FrontierFlowFamily
import Mathlib.Tactic

namespace Tapered945

private theorem candidateOmega_six_zero (k : Nat) :
    candidateOmega (6 * k) = 2 * k + 2 := by
  have hdiv : (6 * k + 4) / 3 = 2 * k + 1 := by
    rw [show 6 * k + 4 = 4 + (2 * k) * 3 by omega,
      Nat.mul_comm (2 * k) 3,
      Nat.add_mul_div_left 4 (2 * k) (by norm_num : 0 < 3)]
    omega
  unfold candidateOmega candidateOmegaBase
  rw [hdiv]
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem candidateOmega_six_one (k : Nat) :
    candidateOmega (6 * k + 1) = 2 * k + 1 := by
  have hdiv : (6 * k + 1 + 4) / 3 = 2 * k + 1 := by
    rw [show 6 * k + 1 + 4 = 5 + (2 * k) * 3 by omega,
      Nat.mul_comm (2 * k) 3,
      Nat.add_mul_div_left 5 (2 * k) (by norm_num : 0 < 3)]
    omega
  unfold candidateOmega candidateOmegaBase
  rw [hdiv]
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem candidateOmega_six_two (k : Nat) :
    candidateOmega (6 * k + 2) = 2 * k + 2 := by
  have hdiv : (6 * k + 2 + 4) / 3 = 2 * k + 2 := by
    rw [show 6 * k + 2 + 4 = 6 + (2 * k) * 3 by omega,
      Nat.mul_comm (2 * k) 3,
      Nat.add_mul_div_left 6 (2 * k) (by norm_num : 0 < 3)]
    omega
  unfold candidateOmega candidateOmegaBase
  rw [hdiv]
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem candidateOmega_six_three (k : Nat) :
    candidateOmega (6 * k + 3) = 2 * k + 3 := by
  have hdiv : (6 * k + 3 + 4) / 3 = 2 * k + 2 := by
    rw [show 6 * k + 3 + 4 = 7 + (2 * k) * 3 by omega,
      Nat.mul_comm (2 * k) 3,
      Nat.add_mul_div_left 7 (2 * k) (by norm_num : 0 < 3)]
    omega
  unfold candidateOmega candidateOmegaBase
  rw [hdiv]
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem candidateOmega_six_four (k : Nat) :
    candidateOmega (6 * k + 4) = 2 * k + 2 := by
  have hdiv : (6 * k + 4 + 4) / 3 = 2 * k + 2 := by
    rw [show 6 * k + 4 + 4 = 8 + (2 * k) * 3 by omega,
      Nat.mul_comm (2 * k) 3,
      Nat.add_mul_div_left 8 (2 * k) (by norm_num : 0 < 3)]
    omega
  unfold candidateOmega candidateOmegaBase
  rw [hdiv]
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem candidateOmega_six_five (k : Nat) :
    candidateOmega (6 * k + 5) = 2 * k + 3 := by
  have hdiv : (6 * k + 5 + 4) / 3 = 2 * k + 3 := by
    rw [show 6 * k + 5 + 4 = 9 + (2 * k) * 3 by omega,
      Nat.mul_comm (2 * k) 3,
      Nat.add_mul_div_left 9 (2 * k) (by norm_num : 0 < 3)]
    omega
  unfold candidateOmega candidateOmegaBase
  rw [hdiv]
  unfold Chvatal.ceilParity
  split_ifs <;> omega

/-- The lower frontier's six-step cycle, including both expansion and
contraction phases. -/
theorem candidate_omega_six_stage_cycle (k : Nat) :
    candidateOmega (6 * k) = 2 * k + 2 ∧
    candidateOmega (6 * k + 1) = 2 * k + 1 ∧
    candidateOmega (6 * k + 2) = 2 * k + 2 ∧
    candidateOmega (6 * k + 3) = 2 * k + 3 ∧
    candidateOmega (6 * k + 4) = 2 * k + 2 ∧
    candidateOmega (6 * k + 5) = 2 * k + 3 ∧
    candidateOmega (6 * k + 6) = 2 * k + 4 := by
  rw [candidateOmega_six_zero, candidateOmega_six_one,
    candidateOmega_six_two, candidateOmega_six_three,
    candidateOmega_six_four, candidateOmega_six_five,
    show 6 * k + 6 = 6 * (k + 1) by omega,
    candidateOmega_six_zero]
  omega

/-- At any phase where the scheduled lower frontier advances, the bottom
reservoir is large enough for the lower-expansion integerizer. -/
theorem candidate_lower_expansion_scale_gate (t : Nat)
    (hmove : candidateOmega (t + 1) = candidateOmega t + 1) :
    3 * candidateOmega t ≤ t + 4 := by
  let k := t / 6
  let r := t % 6
  have hdecomp : t = 6 * k + r := by
    dsimp [k, r]
    omega
  have hr : r < 6 := by dsimp [r]; omega
  have hmove' : candidateOmega (6 * k + r + 1) =
      candidateOmega (6 * k + r) + 1 := by
    rw [← hdecomp]
    exact hmove
  have h0 := candidateOmega_six_zero k
  have h1 := candidateOmega_six_one k
  have h2 := candidateOmega_six_two k
  have h3 := candidateOmega_six_three k
  have h4 := candidateOmega_six_four k
  have h5 := candidateOmega_six_five k
  have h6 : candidateOmega (6 * (k + 1)) = 2 * (k + 1) + 2 :=
    candidateOmega_six_zero (k + 1)
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rw [hdecomp]
  rcases hcases with h | h | h | h | h | h
  · rw [h] at hmove' ⊢
    rw [show 6 * k + 0 = 6 * k by omega, h0,
      show 6 * k + 0 + 1 = 6 * k + 1 by omega, h1] at hmove'
    norm_num at hmove'
  · rw [h] at hmove' ⊢
    rw [show 6 * k + 1 + 1 = 6 * k + 2 by omega, h1, h2] at hmove'
    rw [h1]
    omega
  · rw [h] at hmove' ⊢
    rw [show 6 * k + 2 + 1 = 6 * k + 3 by omega, h2, h3] at hmove'
    rw [h2]
    omega
  · rw [h] at hmove' ⊢
    rw [show 6 * k + 3 + 1 = 6 * k + 4 by omega, h3, h4] at hmove'
    norm_num at hmove'
  · rw [h] at hmove' ⊢
    rw [show 6 * k + 4 + 1 = 6 * k + 5 by omega, h4, h5] at hmove'
    rw [h4]
    omega
  · rw [h] at hmove' ⊢
    rw [show 6 * k + 5 + 1 = 6 * (k + 1) by omega, h5, h6] at hmove'
    rw [h5]
    omega

/-- On every lower-expansion phase, the scheduled bottom reservoir is at least
one two-bit scale below the local reference capacity, as required by the
bottom-expansion integerizer. -/
theorem candidate_bottom_expansion_integer_scale
    (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht : t < candidateTf d)
    (hmove : candidateOmega (t + 1) = candidateOmega t + 1) :
    candidateReferenceCapacity d (candidateOmega t) t / 256 ≤
      (2 : Rat) ^ (6 * d - 6 * candidateOmega t) := by
  have hgate := candidate_lower_expansion_scale_gate t hmove
  have hw := candidate_omega_le_depth d hd t (by omega)
  have hexp : candidateCapacityExponent d (candidateOmega t) t ≤
      (6 * d - 6 * candidateOmega t) + 8 := by
    unfold candidateCapacityExponent
    omega
  have hpow : (2 : Rat) ^ candidateCapacityExponent d (candidateOmega t) t ≤
      (2 : Rat) ^ ((6 * d - 6 * candidateOmega t) + 8) :=
    pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) hexp
  have hfactor : (2 : Rat) ^ ((6 * d - 6 * candidateOmega t) + 8) =
      256 * (2 : Rat) ^ (6 * d - 6 * candidateOmega t) := by
    rw [pow_add]
    norm_num [mul_comm]
  have hmul : candidateReferenceCapacity d (candidateOmega t) t ≤
      256 * (2 : Rat) ^ (6 * d - 6 * candidateOmega t) := by
    simpa [candidateReferenceCapacity] using hpow.trans_eq hfactor
  rw [div_le_iff₀ (by norm_num : (0 : Rat) < 256)]
  nlinarith [hmul]

/-- The candidate schedule supplies the reservoir and capacity hypotheses of
the bottom-expansion integerizer, so callers only provide the actual tagged
parent count and the phase-local debt bound. -/
theorem candidate_bottom_expansion_integer_split
    (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht : t < candidateTf d) (e : Rat)
    (parent : ScheduledFlowCount .bottomExpansion
      ((2 : Rat) ^ (6 * d - 6 * candidateOmega t))
      (candidateReferenceCapacity d (candidateOmega t) t) e)
    (he : -eAbs ≤ e ∧ e ≤ ePos)
    (hmove : candidateOmega (t + 1) = candidateOmega t + 1) :
    ∃ up : Nat, Even up ∧ up ≤ parent.count ∧
      |(up : Rat) - frontierInteriorUp
        (candidateReferenceCapacity d (candidateOmega t) t) e| ≤ 1 ∧
      ∃ blocks : Fin 64 → Nat,
        (∑ j, blocks j) = parent.count - up ∧
        ∀ j, |(blocks j : Rat) - frontierBottomMass
          (((2 : Rat) ^ (6 * d - 6 * candidateOmega t)) / 64)
          (4 * candidateReferenceCapacity d (candidateOmega t) t)
          (debtStep (addressQ j.val) e)| ≤ 1 + 70 / 64 := by
  let B : Rat := (2 : Rat) ^ (6 * d - 6 * candidateOmega t)
  let C : Rat := candidateReferenceCapacity d (candidateOmega t) t
  have ht' : t ≤ candidateTf d := by omega
  have hbottomScale : C / 256 ≤ B := by
    dsimp [B, C]
    exact candidate_bottom_expansion_integer_scale d hd t ht hmove
  have hcapacity : 2 ^ 34 ≤ C := by
    dsimp [C]
    apply candidate_active_capacity_lower d hd t ht' (candidateOmega t)
    exact candidate_frontiers_order d hd t ht'
  simpa [B, C] using
    (bottom_expand_integer_split B C e parent hcapacity hbottomScale he)

end Tapered945
