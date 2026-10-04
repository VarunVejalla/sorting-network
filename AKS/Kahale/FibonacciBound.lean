module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Summing the depth inequalities gives a Fibonacci bound

This is an alternative derivation of the scalar optimization in Kahale et al.,
Theorem 6. Its binomial hypotheses must still be proved for sorting networks.
No network lower bound is asserted by this module alone.
-/

@[expose] public section

namespace Kahale

open Finset

/-- The paper's constant, written using the golden ratio. All logs are base 2. -/
noncomputable def depthConstant : ℝ := 1 / (1 - Real.logb 2 Real.goldenRatio)

theorem depthConstant_pos : 0 < depthConstant := by
  unfold depthConstant
  apply one_div_pos.mpr
  have h : Real.logb 2 Real.goldenRatio < 1 := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_lt_logb (by norm_num) Real.goldenRatio_pos Real.goldenRatio_lt_two
  linarith

theorem binomial_constraints_fibonacci_bound (n d : ℕ)
    (h : ∀ s ≤ d, n * Nat.choose (d - s) s ≤ 2 ^ (d + 1) * (s + 1)) :
    n * Nat.fib (d + 1) ≤ 2 ^ (d + 1) * (d + 1) ^ 2 := by
  rw [Nat.fib_succ_eq_sum_choose, mul_sum]
  calc ∑ p ∈ antidiagonal d, n * Nat.choose p.1 p.2
      ≤ ∑ _p ∈ antidiagonal d, 2 ^ (d + 1) * (d + 1) := by
        apply sum_le_sum
        intro p hp
        have he := mem_antidiagonal.mp hp
        have hs : p.2 ≤ d := by omega
        have hd : d - p.2 = p.1 := by omega
        rw [← hd]
        exact (h p.2 hs).trans (Nat.mul_le_mul_left _ (by omega))
    _ = 2 ^ (d + 1) * (d + 1) ^ 2 := by simp [Finset.Nat.card_antidiagonal]; ring

theorem goldenRatio_pow_le_fib (d : ℕ) :
    Real.goldenRatio ^ d ≤ Real.goldenRatio * (Nat.fib (d + 1) : ℝ) := by
  have hi := Real.goldenRatio_mul_fib_succ_add_fib d
  have hm : (Nat.fib d : ℝ) ≤ Nat.fib (d + 1) := by
    exact_mod_cast Nat.fib_mono (by omega : d ≤ d + 1)
  have hf : 0 ≤ (Nat.fib (d + 1) : ℝ) := Nat.cast_nonneg _
  have hs := Real.goldenRatio_sq
  rw [pow_succ] at hi
  nlinarith [Real.goldenRatio_pos]

/-- A finite exponential bound conditional only on the binomial inequalities.
The polynomial loss does not affect the limiting logarithmic coefficient. -/
theorem binomial_constraints_exponential_bound (n d : ℕ)
    (h : ∀ s ≤ d, n * Nat.choose (d - s) s ≤ 2 ^ (d + 1) * (s + 1)) :
    (n : ℝ) * Real.goldenRatio ^ d ≤
      Real.goldenRatio * 2 ^ (d + 1) * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hb : (n : ℝ) * (Nat.fib (d + 1) : ℝ) ≤
      (2 : ℝ) ^ (d + 1) * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast binomial_constraints_fibonacci_bound n d h
  calc (n : ℝ) * Real.goldenRatio ^ d
      ≤ (n : ℝ) * (Real.goldenRatio * (Nat.fib (d + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left (goldenRatio_pow_le_fib d) (Nat.cast_nonneg _)
    _ = Real.goldenRatio * ((n : ℝ) * (Nat.fib (d + 1) : ℝ)) := by ring
    _ ≤ Real.goldenRatio * ((2 : ℝ) ^ (d + 1) * ((d + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hb Real.goldenRatio_pos.le
    _ = _ := by ring

end Kahale
