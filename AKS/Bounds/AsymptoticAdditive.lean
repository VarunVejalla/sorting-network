import AKS.Bounds.Asymptotic

/-! Additive startup costs vanish in the logarithmic depth ratio. -/

namespace SortingDepth

open Filter
open scoped Topology

theorem limsup_of_additive_depth_bound (C B : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, (minimum n : ℝ) ≤ C * (Nat.clog 2 n : ℝ) + B) :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ C := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop
  have henv : Tendsto (fun n : ℕ ↦ C + (C + B) * (Real.logb 2 (n : ℝ))⁻¹)
      atTop (𝓝 C) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp hlog).const_mul (C + B))
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (minimum n : ℝ) / Real.logb 2 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_nonneg (Nat.cast_nonneg _) (Real.logb_pos (by norm_num) hnR).le
  have hle : ∀ᶠ n : ℕ in atTop,
      (minimum n : ℝ) / Real.logb 2 n ≤ C + (C + B) * (Real.logb 2 (n : ℝ))⁻¹ := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
    have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
      rw [← Real.natCeil_logb_natCast]
      exact Nat.ceil_lt_add_one hl.le
    calc (minimum n : ℝ) / Real.logb 2 n
        ≤ (C * (Real.logb 2 n + 1) + B) / Real.logb 2 n := by
          apply div_le_div_of_nonneg_right _ hl.le
          exact (hbound n).trans (add_le_add (mul_le_mul_of_nonneg_left hceil.le hC) le_rfl)
      _ = C + (C + B) * (Real.logb 2 (n : ℝ))⁻¹ := by
        rw [mul_add, mul_one, add_div, add_div, mul_div_cancel_right₀ _ hl.ne',
          div_eq_mul_inv, div_eq_mul_inv, add_mul]
        ring
  exact (limsup_le_limsup hle
    (isCoboundedUnder_le_of_eventually_le atTop hnonneg) henv.isBoundedUnder_le).trans
      henv.limsup_eq.le

end SortingDepth
