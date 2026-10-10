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
    have h4 : (2 : ℝ) * ((m : ℝ) + 1) ≤ 4 * m := by nlinarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 42)]
    calc _ ≤ Real.log (4 * m) := Real.log_le_log (by positivity) h4
      _ = 2 * Real.log 2 + Real.log m := by
        rw [Real.log_mul (by norm_num) hm0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
  have hkey : Real.log (2 * ((m : ℝ) + 1)) ≤ m * K - 1 := by
    have h1 : (m : ℝ) / 2 ^ 42 ≤ m / 2 ^ 42 := le_rfl
    have h2 : (m : ℝ) * (9 / 10 ^ 12) ≤ m * K := mul_le_mul_of_nonneg_left hK9 hm0.le
    have h3 : (m : ℝ) / 2 ^ 42 = m * (1 / 2 ^ 42) := by ring
    have h4 : (2 : ℝ) ^ 42 * (9 / 10 ^ 12 - 1 / 2 ^ 42) ≤ m * (9 / 10 ^ 12 - 1 / 2 ^ 42) :=
      mul_le_mul_of_nonneg_right hmR (by norm_num)
    norm_num at h4 h3 ⊢
    linarith
  have hq : 2 * ((m : ℝ) + 1) * Real.exp (-((m : ℝ) * K)) ≤ Real.exp (-1) := by
    have : 2 * ((m : ℝ) + 1) ≤ Real.exp (m * K - 1) := by
      calc 2 * ((m : ℝ) + 1) = Real.exp (Real.log (2 * ((m : ℝ) + 1))) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.2 hkey
    calc _ ≤ Real.exp (m * K - 1) * Real.exp (-((m : ℝ) * K)) := by gcongr
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hrew : Real.exp (-((n : ℝ) * m * K)) = Real.exp (-((m : ℝ) * K)) ^ n := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hrew, ← mul_pow]
  calc _ ≤ (Real.exp (-1)) ^ n := pow_le_pow_left₀ (by positivity) hq n
    _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-16) := by
        have : (16 : ℝ) ≤ n := by exact_mod_cast hn
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ 1 / 1000 := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have h1 : (2.7 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
          pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) 16
        rw [← Real.exp_nat_mul] at h1
        norm_num at h1 ⊢
        linarith

end Chvatal
