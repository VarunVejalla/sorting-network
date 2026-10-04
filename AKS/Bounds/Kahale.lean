import AKS.Kahale.NetworkBound
import AKS.Bounds.Asymptotic

/-! # The Kahale lower bound on minimum sorting-network depth

All combinatorial ingredients are proved locally; published results are used
as mathematical references, not as assumptions.
-/

namespace SortingDepth

open Filter
open scoped Topology

theorem minimum_fibonacci_bound (n : ℕ) :
    n * Nat.fib (minimum n + 1) ≤
      2 ^ (minimum n + 1) * (minimum n + 1) ^ 2 := by
  obtain ⟨net, hs, hd⟩ := minimum_attained n
  simpa only [hd] using Kahale.sorting_network_fibonacci_bound net hs

theorem minimum_exponential_bound (n : ℕ) :
    (n : ℝ) * Real.goldenRatio ^ minimum n ≤
      Real.goldenRatio * 2 ^ (minimum n + 1) * ((minimum n + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨net, hs, hd⟩ := minimum_attained n
  simpa only [hd] using Kahale.sorting_network_exponential_bound net hs

theorem minimum_tendsto_atTop : Tendsto minimum atTop atTop := by
  refine tendsto_atTop.2 fun k ↦ ?_
  filter_upwards [eventually_ge_atTop (2 ^ (k + 1) * (k + 1) ^ 2 + 1)] with n hn
  by_contra hk
  have hd : minimum n ≤ k := by omega
  have hf : 1 ≤ Nat.fib (minimum n + 1) := Nat.fib_pos.mpr (by omega)
  have hb := (Nat.mul_le_mul_left n hf).trans (minimum_fibonacci_bound n)
  simp only [mul_one] at hb
  have hpow : 2 ^ (minimum n + 1) * (minimum n + 1) ^ 2 ≤
      2 ^ (k + 1) * (k + 1) ^ 2 := by gcongr <;> omega
  omega

theorem minimum_logarithmic_bound {n : ℕ} (hn : 0 < n) :
    Real.logb 2 n ≤ (1 - Real.logb 2 Real.goldenRatio) * (minimum n : ℝ) +
      2 * Real.logb 2 ((minimum n : ℝ) + 1) + 1 + Real.logb 2 Real.goldenRatio := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos hnR (pow_pos Real.goldenRatio_pos _)) (minimum_exponential_bound n)
  rw [Real.logb_mul hnR.ne' (pow_pos Real.goldenRatio_pos _).ne',
    Real.logb_pow, Real.logb_mul (mul_pos Real.goldenRatio_pos (by positivity)).ne'
      (by positivity), Real.logb_mul Real.goldenRatio_pos.ne' (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  push_cast at h
  linarith

end SortingDepth
