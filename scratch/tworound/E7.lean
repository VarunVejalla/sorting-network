import AKS.Chvatal.GeneralParams
namespace Chvatal

theorem epsB1_le {m : ℕ} (hm : 2 ^ 42 ≤ m) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤ 371 / 10 ^ 8 := by
  have hmR : (2 : ℝ) ^ 42 ≤ m := by exact_mod_cast hm
  have hmono := chernoff_mono (M := (2 : ℝ) ^ 42) (m := m) (one_le_pow₀ (by norm_num)) hmR
  rw [Real.log_pow] at hmono
  have hl2 := Real.log_two_lt_d9
  rw [Real.sqrt_le_left (by norm_num)]
  refine hmono.trans ?_
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num at hl2 ⊢
  nlinarith

end Chvatal
