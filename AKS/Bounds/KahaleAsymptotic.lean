import AKS.Bounds.Kahale
import AKS.Kahale.LogRemainder

/-! # The asymptotic Kahale lower bound, with base-two logarithms -/

namespace SortingDepth

open Filter
open scoped Topology

theorem eventually_minimum_div_logb_ge_kahale_envelope :
    ∀ᶠ n : ℕ in atTop,
      1 / ((1 - Real.logb 2 Real.goldenRatio) +
        (2 * Real.logb 2 ((minimum n : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio) /
          (minimum n : ℝ)) ≤ (minimum n : ℝ) / Real.logb 2 n := by
  filter_upwards [eventually_ge_atTop 2,
    minimum_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hd
  have hdR : 0 < (minimum n : ℝ) := by exact_mod_cast (show 0 < minimum n by omega)
  have hl : 0 < Real.logb 2 (n : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have hc : 0 < 1 - Real.logb 2 Real.goldenRatio := by
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      Real.goldenRatio_pos Real.goldenRatio_lt_two
    rw [Real.logb_self_eq_one (by norm_num)] at h
    linarith
  have he := Kahale.log_remainder_nonneg (minimum n)
  have hp : 0 < (1 - Real.logb 2 Real.goldenRatio) +
      (2 * Real.logb 2 ((minimum n : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio) /
        (minimum n : ℝ) := add_pos_of_pos_of_nonneg hc (div_nonneg he hdR.le)
  apply (div_le_div_iff₀ hp hl).2
  have hb := minimum_logarithmic_bound (show 0 < n by omega)
  nlinarith [div_mul_cancel₀
    (2 * Real.logb 2 ((minimum n : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio) hdR.ne']

theorem kahale_envelope_tendsto :
    Tendsto (fun n : ℕ ↦
      1 / ((1 - Real.logb 2 Real.goldenRatio) +
        (2 * Real.logb 2 ((minimum n : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio) /
          (minimum n : ℝ))) atTop (𝓝 Kahale.depthConstant) := by
  have hc : 1 - Real.logb 2 Real.goldenRatio ≠ 0 := by
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      Real.goldenRatio_pos Real.goldenRatio_lt_two
    rw [Real.logb_self_eq_one (by norm_num)] at h
    linarith
  simpa only [add_zero, Kahale.depthConstant] using
    tendsto_const_nhds.div (tendsto_const_nhds.add
      (Kahale.log_remainder_div_tendsto.comp minimum_tendsto_atTop)) (by simpa using hc)

theorem minimum_div_logb_cobounded :
    atTop.IsCoboundedUnder (· ≥ ·) (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) := by
  apply isCoboundedUnder_ge_of_eventually_le atTop
    (x := (2 : ℝ) * (102 * 10 ^ 62))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
  have hl₁ : 1 ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn : (2 : ℝ) ≤ n)
    simpa using h
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one hl.le
  have hd : (minimum n : ℝ) ≤ (102 * 10 ^ 62 : ℝ) * (Nat.clog 2 n : ℝ) := by
    exact_mod_cast minimum_depth_le n
  apply (div_le_iff₀ hl).2
  nlinarith

theorem liminf_minimum_div_logb_ge_kahale :
    Kahale.depthConstant ≤
      liminf (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop := by
  rw [← kahale_envelope_tendsto.liminf_eq]
  exact liminf_le_liminf eventually_minimum_div_logb_ge_kahale_envelope
    kahale_envelope_tendsto.isBoundedUnder_ge minimum_div_logb_cobounded

theorem eventually_minimum_depth_ge_kahale_logb (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Kahale.depthConstant - ε) * Real.logb 2 n ≤ (minimum n : ℝ) := by
  filter_upwards [eventually_minimum_div_logb_ge_kahale_envelope,
    kahale_envelope_tendsto.eventually (eventually_gt_nhds (by linarith :
      Kahale.depthConstant - ε < Kahale.depthConstant)),
    eventually_ge_atTop 2] with n hn he hn₂
  have hl : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < n by omega))
  exact (le_div_iff₀ hl).1 (he.le.trans hn)

end SortingDepth
