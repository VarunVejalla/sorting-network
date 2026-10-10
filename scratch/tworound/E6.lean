import AKS.Chvatal.Bulk2Count
import AKS.Chvatal.GeneralParams
open Finset

namespace Chvatal

theorem failFactorB2_le {m n : Nat} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n) :
    (2 * ((m : ℝ) + 1)) ^ n *
      Real.exp (-((n : ℝ) * m * ((1 / 437 : ℝ) * (1 / 59000000) / 2 -
        (1 / 437 : ℝ) ^ 2 * (1 / 2 + 2 * (1 / 437 : ℝ) / 9) * (371 / 10 ^ 8)))) ≤ 1 / 1000 := by
  have hmR : (2 : ℝ) ^ 42 ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmR
  set K : ℝ := (1 / 437 : ℝ) * (1 / 59000000) / 2 -
        (1 / 437 : ℝ) ^ 2 * (1 / 2 + 2 * (1 / 437 : ℝ) / 9) * (371 / 10 ^ 8) with hK
  have hK9 : (9 / 10 ^ 12 : ℝ) ≤ K := by rw [hK]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hlogm : Real.log m ≤ 42 * Real.log 2 + (m / 2 ^ 42 - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hm0 (by positivity : (0 : ℝ) < 2 ^ 42))
    rw [Real.log_div hm0.ne' (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hlog2m : Real.log (2 * ((m : ℝ) + 1)) ≤ 2 * Real.log 2 + Real.log m := by
    rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2) ]
    sorry
  sorry

end Chvatal
