module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Chvátal Lemma 6.2 (ii): `C(a,k) ≤ (e·a/k)^k` and `C(n,k)·C(J,k) ≤ (e²·n·J/k²)^k` -/

@[expose] public section

namespace Chvatal

open Nat

/-- `C(a,k) ≤ (e·a/k)^k` for `k ≥ 1`. -/
theorem choose_le_exp_pow (a : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose a k : ℝ) ≤ (Real.exp 1 * a / k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (k : ℝ) ^ k ≤ Real.exp 1 ^ k * (k ! : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
    rwa [div_le_iff₀ hf, show Real.exp (k : ℝ) = Real.exp 1 ^ k by
      rw [← Real.exp_nat_mul, mul_one]] at h
  refine (Nat.choose_le_pow_div k a).trans ?_
  rw [div_pow, mul_pow, div_le_div_iff₀ hf (pow_pos hkpos k)]
  calc (a : ℝ) ^ k * (k : ℝ) ^ k ≤ (a : ℝ) ^ k * (Real.exp 1 ^ k * (k ! : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (Nat.cast_nonneg a) k)
    _ = _ := by ring

/-- `C(n,k)·C(J,k) ≤ (e²·n·j/k²)^k` for `k ≥ 1` and `J ≤ j`. -/
theorem choose_mul_choose_le_of_le (n : ℕ) {J j : ℕ} (hJ : J ≤ j) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose n k : ℝ) * (Nat.choose J k : ℝ) ≤
      (Real.exp 1 ^ 2 * n * j / (k : ℝ) ^ 2) ^ k := by
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have h := mul_le_mul (choose_le_exp_pow n hk) (choose_le_exp_pow J hk)
    (Nat.cast_nonneg _) (by positivity)
  refine h.trans ?_
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [show Real.exp 1 * n / k * (Real.exp 1 * J / k) = Real.exp 1 ^ 2 * n * J / (k : ℝ) ^ 2 by
    field_simp]
  gcongr

end Chvatal
