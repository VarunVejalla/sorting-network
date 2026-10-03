import AKS.Bounds.Upper
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup

/-! # The upper bound on limsup D(n)/log₂(n)

The ceiling logarithm contributes a vanishing additive term after division
by `log₂ n`. This module states the research objective using the minimum over
all sorting networks, not merely the depth of one particular construction.
-/

namespace SortingDepth

open Filter
open scoped Topology

theorem limsup_minimum_div_logb_le :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤
      (102 * 10 ^ 62 : ℝ) := by
  let C : ℝ := 102 * 10 ^ 62
  have hC : 0 ≤ C := by positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop
  have henv : Tendsto (fun n : ℕ ↦ C + C * (Real.logb 2 (n : ℝ))⁻¹)
      atTop (𝓝 C) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp hlog).const_mul C)
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (minimum n : ℝ) / Real.logb 2 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_nonneg (Nat.cast_nonneg _) (Real.logb_pos (by norm_num) hnR).le
  have hle : ∀ᶠ n : ℕ in atTop,
      (minimum n : ℝ) / Real.logb 2 n ≤ C + C * (Real.logb 2 (n : ℝ))⁻¹ := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
    have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
      rw [← Real.natCeil_logb_natCast]
      exact Nat.ceil_lt_add_one hl.le
    have hd : (minimum n : ℝ) ≤ C * (Nat.clog 2 n : ℝ) := by
      dsimp [C]
      exact_mod_cast minimum_depth_le n
    calc (minimum n : ℝ) / Real.logb 2 n
        ≤ (C * (Real.logb 2 n + 1)) / Real.logb 2 n := by
          apply div_le_div_of_nonneg_right _ hl.le
          exact hd.trans (mul_le_mul_of_nonneg_left hceil.le hC)
      _ = C + C * (Real.logb 2 (n : ℝ))⁻¹ := by
        field_simp
  exact (limsup_le_limsup hle
    (isCoboundedUnder_le_of_eventually_le atTop hnonneg) henv.isBoundedUnder_le).trans
      henv.limsup_eq.le

end SortingDepth
