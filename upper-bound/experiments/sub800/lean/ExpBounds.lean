import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Rational bounds for `exp` and `log` (numerics of LEAN-PLAN W4.5)

`exp x` for rational `x` is bracketed by a Taylor polynomial with Mathlib's remainder bound
(`Real.exp_bound`, valid for `|y| ≤ 1`) at `y = x / 2^k`, raised to the power `2^k`. Logs are
bounded through `exp`. The final inequalities are closed by `norm_num` on rationals. -/

open Finset BigOperators

namespace ExpBounds

/-- Taylor upper value: `Σ_{i<N} y^i / i! + |y|^N (N+1)/(N! N)`. -/
noncomputable def tup (y : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, y ^ i / (i.factorial : ℝ) + |y| ^ N * ((N + 1 : ℕ) / ((N.factorial : ℝ) * N))

/-- Taylor lower value. -/
noncomputable def tlo (y : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, y ^ i / (i.factorial : ℝ) - |y| ^ N * ((N + 1 : ℕ) / ((N.factorial : ℝ) * N))

theorem exp_le_tup (y : ℝ) (hy : |y| ≤ 1) (N : ℕ) (hN : 0 < N) : Real.exp y ≤ tup y N := by
  have h := Real.exp_bound hy hN
  have := (abs_le.1 h).2
  unfold tup
  push_cast at this ⊢
  linarith

theorem tlo_le_exp (y : ℝ) (hy : |y| ≤ 1) (N : ℕ) (hN : 0 < N) : tlo y N ≤ Real.exp y := by
  have h := Real.exp_bound hy hN
  have := (abs_le.1 h).1
  unfold tlo
  push_cast at this ⊢
  linarith

theorem exp_eq_pow (x : ℝ) (k : ℕ) : Real.exp x = Real.exp (x / 2 ^ k) ^ (2 ^ k) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- **Upper bound.** -/
theorem exp_le (x : ℝ) (k N : ℕ) (hN : 0 < N) (hy : |x / 2 ^ k| ≤ 1) (q : ℝ)
    (hq : tup (x / 2 ^ k) N ^ (2 ^ k) ≤ q) : Real.exp x ≤ q := by
  rw [exp_eq_pow x k]
  refine le_trans ?_ hq
  exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_tup _ hy N hN) _

/-- **Lower bound.** -/
theorem le_exp (x : ℝ) (k N : ℕ) (hN : 0 < N) (hy : |x / 2 ^ k| ≤ 1) (q : ℝ)
    (h0 : 0 ≤ tlo (x / 2 ^ k) N) (hq : q ≤ tlo (x / 2 ^ k) N ^ (2 ^ k)) : q ≤ Real.exp x := by
  rw [exp_eq_pow x k]
  exact hq.trans (pow_le_pow_left₀ h0 (tlo_le_exp _ hy N hN) _)

/-- `log y ≤ q` from `y ≤ exp q`. -/
theorem log_le (y q : ℝ) (hy : 0 < y) (h : y ≤ Real.exp q) : Real.log y ≤ q :=
  (Real.log_le_iff_le_exp hy).2 h

/-- `q ≤ log y` from `exp q ≤ y`. -/
theorem le_log (y q : ℝ) (hy : 0 < y) (h : Real.exp q ≤ y) : q ≤ Real.log y := by
  rw [Real.le_log_iff_exp_le hy]; exact h

/-- Six-term Taylor bounds in closed form (for `|y| ≤ 1`), avoiding symbolic factorials. -/
theorem exp_le_six (y : ℝ) (hy : |y| ≤ 1) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + |y| ^ 6 * (7 / 4320) := by
  have h := exp_le_tup y hy 6 (by norm_num)
  simp only [tup, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at h
  norm_num at h
  linarith

theorem six_le_exp (y : ℝ) (hy : |y| ≤ 1) :
    1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 - |y| ^ 6 * (7 / 4320) ≤ Real.exp y := by
  have h := tlo_le_exp y hy 6 (by norm_num)
  simp only [tlo, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at h
  norm_num at h
  linarith

/-- **Upper bound**, closed form: `exp x ≤ (P(x/2^k) + |x/2^k|^6 · 7/4320)^(2^k)`. -/
theorem exp_le' (x : ℝ) (k : ℕ) (hy : |x / 2 ^ k| ≤ 1) (q : ℝ)
    (hq : (1 + x / 2 ^ k + (x / 2 ^ k) ^ 2 / 2 + (x / 2 ^ k) ^ 3 / 6 + (x / 2 ^ k) ^ 4 / 24 +
      (x / 2 ^ k) ^ 5 / 120 + |x / 2 ^ k| ^ 6 * (7 / 4320)) ^ (2 ^ k) ≤ q) : Real.exp x ≤ q := by
  rw [exp_eq_pow x k]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_six _ hy) _) hq

/-- **Lower bound**, closed form. -/
theorem le_exp' (x : ℝ) (k : ℕ) (hy : |x / 2 ^ k| ≤ 1) (q : ℝ)
    (h0 : 0 ≤ 1 + x / 2 ^ k + (x / 2 ^ k) ^ 2 / 2 + (x / 2 ^ k) ^ 3 / 6 + (x / 2 ^ k) ^ 4 / 24 +
      (x / 2 ^ k) ^ 5 / 120 - |x / 2 ^ k| ^ 6 * (7 / 4320))
    (hq : q ≤ (1 + x / 2 ^ k + (x / 2 ^ k) ^ 2 / 2 + (x / 2 ^ k) ^ 3 / 6 + (x / 2 ^ k) ^ 4 / 24 +
      (x / 2 ^ k) ^ 5 / 120 - |x / 2 ^ k| ^ 6 * (7 / 4320)) ^ (2 ^ k)) : q ≤ Real.exp x := by
  rw [exp_eq_pow x k]
  exact hq.trans (pow_le_pow_left₀ h0 (six_le_exp _ hy) _)

/-- Squaring step, upper: `exp z ≤ v` from `exp w ≤ u`, `z = 2w`, `u² ≤ v`. -/
theorem exp_le_sq (z w u v : ℝ) (hw : z = 2 * w) (h : Real.exp w ≤ u) (hv : u ^ 2 ≤ v) :
    Real.exp z ≤ v := by
  rw [hw, show 2 * w = w + w by ring, Real.exp_add]
  have h0 : 0 ≤ Real.exp w := (Real.exp_pos w).le
  nlinarith

/-- Squaring step, lower: `v ≤ exp z` from `l ≤ exp w`, `0 ≤ l`, `z = 2w`, `v ≤ l²`. -/
theorem le_exp_sq (z w l v : ℝ) (hw : z = 2 * w) (h : l ≤ Real.exp w) (h0 : 0 ≤ l)
    (hv : v ≤ l ^ 2) : v ≤ Real.exp z := by
  rw [hw, show 2 * w = w + w by ring, Real.exp_add]
  nlinarith

/-- Base step, upper (Taylor, `|y| ≤ 1`). -/
theorem exp_le_base (y u : ℝ) (hy : |y| ≤ 1)
    (hu : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + |y| ^ 6 * (7 / 4320) ≤ u) :
    Real.exp y ≤ u := (exp_le_six y hy).trans hu

/-- Base step, lower. -/
theorem le_exp_base (y l : ℝ) (hy : |y| ≤ 1)
    (hl : l ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 - |y| ^ 6 * (7 / 4320)) :
    l ≤ Real.exp y := hl.trans (six_le_exp y hy)

-- smoke test
example : Real.exp (3 / 2) ≤ 4.4817 := by
  apply exp_le' (3 / 2) 6 (by rw [abs_le]; constructor <;> norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2 / 2 ^ 6)]
  norm_num

end ExpBounds
