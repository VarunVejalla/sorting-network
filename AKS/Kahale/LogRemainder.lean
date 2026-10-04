module

public import AKS.Kahale.FibonacciBound

/-! # The logarithmic remainder in the finite depth bound -/

@[expose] public section

namespace Kahale

open Filter
open scoped Topology

theorem log_remainder_nonneg (d : ℕ) :
    0 ≤ 2 * Real.logb 2 ((d : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio := by
  have h₁ : 0 ≤ Real.logb 2 ((d : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have h₂ := (Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    Real.one_lt_goldenRatio).le
  linarith

theorem log_remainder_div_tendsto :
    Tendsto (fun d : ℕ ↦
      (2 * Real.logb 2 ((d : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio) / (d : ℝ))
      atTop (𝓝 0) := by
  have hcast : Tendsto (fun d : ℕ ↦ (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun d : ℕ ↦ (d : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hshift : Tendsto (fun d : ℕ ↦ (d : ℝ) + 1) atTop atTop :=
    hcast.atTop_add tendsto_const_nhds
  have hlog : Tendsto (fun d : ℕ ↦
      Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hshift
  have hratio : Tendsto (fun d : ℕ ↦ ((d : ℝ) + 1) / (d : ℝ)) atTop (𝓝 1) := by
    apply (show Tendsto (fun d : ℕ ↦ 1 + (d : ℝ)⁻¹) atTop (𝓝 1) by
      simpa using tendsto_const_nhds.add hi).congr'
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hdp : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    field_simp
  have hmain : Tendsto (fun d : ℕ ↦ Real.logb 2 ((d : ℝ) + 1) / (d : ℝ))
      atTop (𝓝 0) := by
    apply (show Tendsto (fun d : ℕ ↦
        (Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1) *
          (((d : ℝ) + 1) / (d : ℝ))) / Real.log 2) atTop (𝓝 0) by
      simpa using (hlog.mul hratio).div_const (Real.log 2)).congr'
    filter_upwards [] with d
    rw [Real.logb]
    have hp : (d : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have h := (hmain.const_mul 2).add
    (hi.const_mul (1 + Real.logb 2 Real.goldenRatio))
  simpa only [mul_zero, add_zero] using h.congr (fun d ↦ by
    simp only [add_div, mul_div_assoc, div_eq_mul_inv]
    ring)

end Kahale
