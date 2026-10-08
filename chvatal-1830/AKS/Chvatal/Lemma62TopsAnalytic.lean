module

/-
  # Chvátal Lemma 6.2, claim (ii): analytic binomial estimates

  `C(a,k) ≤ (e·a/k)^k` and the product form `C(n,k)·C(J,k) ≤ (e²·n·J/k²)^k`,
  used to bound the number of tops (see `Lemma62TopsCount`).
-/

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace Chvatal

open Nat

/-- `k^k ≤ e^k · k!`. -/
theorem pow_self_le_exp_pow_mul_factorial (k : ℕ) :
    (k : ℝ) ^ k ≤ Real.exp 1 ^ k * (k ! : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf] at h
  have he : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [he] at h
  exact h

/-- `C(a,k) ≤ (e·a/k)^k` for `k ≥ 1`. -/
theorem choose_le_exp_pow (a : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose a k : ℝ) ≤ (Real.exp 1 * a / k) ^ k := by
  have h1 : (Nat.choose a k : ℝ) ≤ (a : ℝ) ^ k / (k ! : ℝ) := Nat.choose_le_pow_div k a
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hkk : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have h2 := pow_self_le_exp_pow_mul_factorial k
  refine h1.trans ?_
  rw [div_pow, mul_pow, div_le_div_iff₀ hf hkk]
  have ha : (0 : ℝ) ≤ (a : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg a) k
  calc (a : ℝ) ^ k * (k : ℝ) ^ k ≤ (a : ℝ) ^ k * (Real.exp 1 ^ k * (k ! : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 ha
    _ = Real.exp 1 ^ k * (a : ℝ) ^ k * (k ! : ℝ) := by ring

/-- `C(n,k)·C(J,k) ≤ (e²·n·J/k²)^k` for `k ≥ 1`. -/
theorem choose_mul_choose_le (n J : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose n k : ℝ) * (Nat.choose J k : ℝ) ≤
      (Real.exp 1 ^ 2 * n * J / (k : ℝ) ^ 2) ^ k := by
  have h := mul_le_mul (choose_le_exp_pow n hk) (choose_le_exp_pow J hk)
    (Nat.cast_nonneg _) (by positivity)
  refine h.trans (le_of_eq ?_)
  rw [← mul_pow]
  congr 1
  field_simp

/-- Monotone form: any `J ≤ j` may be replaced by `j`. -/
theorem choose_mul_choose_le_of_le (n : ℕ) {J j : ℕ} (hJ : J ≤ j) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose n k : ℝ) * (Nat.choose J k : ℝ) ≤
      (Real.exp 1 ^ 2 * n * j / (k : ℝ) ^ 2) ^ k := by
  refine (choose_mul_choose_le n J hk).trans ?_
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hk2.le
  have : (J : ℝ) ≤ j := by exact_mod_cast hJ
  have hc : (0 : ℝ) ≤ Real.exp 1 ^ 2 * n := by positivity
  nlinarith

end Chvatal
