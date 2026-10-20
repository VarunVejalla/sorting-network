import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # General lemmas behind the per-cell numerics (LEAN-PLAN W4.5) -/

open Finset BigOperators Real

namespace NumGlue

/-- `log C(n,s) ≤ n · H(s/n)` (one term of the binomial expansion is at most 1). -/
theorem log_choose_le (n s : ℕ) (hs : 0 < s) (hsn : s < n) :
    Real.log (n.choose s) ≤ n * binEntropy ((s : ℝ) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_trans hs hsn)
  set p : ℝ := (s : ℝ) / n
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by
    rw [div_lt_one hn]; exact_mod_cast hsn
  have hq0 : 0 < 1 - p := by linarith
  -- C(n,s) p^s (1-p)^(n-s) ≤ (p + (1-p))^n = 1
  have hterm : (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) ≤ 1 := by
    have hsum := add_pow p (1 - p) n
    rw [show p + (1 - p) = 1 by ring, one_pow] at hsum
    have hmem : s ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have := Finset.single_le_sum (f := fun k => p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ))
      (fun k _ => by positivity) hmem
    simp only at this
    calc (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) = p ^ s * (1 - p) ^ (n - s) * (n.choose s : ℝ) := by ring
      _ ≤ _ := this
      _ = 1 := hsum.symm
  have hC : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hsn.le
  have hlog := Real.log_le_log (by positivity) hterm
  rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hsR : (s : ℝ) = n * p := by simp [p]; field_simp
  have hnsR : ((n - s : ℕ) : ℝ) = n * (1 - p) := by
    rw [Nat.cast_sub hsn.le, hsR]; ring
  rw [hnsR, hsR] at hlog
  simp only [binEntropy, Real.log_inv]
  nlinarith

/-- `log((n-1)/η)/n ≤ log(15/η)/16` for `n ≥ 16` and `η ≤ 1/100`. -/
theorem log_union_le (n : ℕ) (hn : 16 ≤ n) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 100) :
    Real.log ((n - 1) / η) / n ≤ Real.log (15 / η) / 16 := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsplit : Real.log ((n - 1) / η) = Real.log (15 / η) + Real.log ((n - 1) / 15) := by
    rw [← Real.log_mul (by positivity) (by
      have : (0 : ℝ) < n - 1 := by linarith
      positivity)]
    congr 1; field_simp
  have hlog1 : Real.log ((n - 1) / 15) ≤ (n - 1) / 15 - 1 :=
    Real.log_le_sub_one_of_pos (by
      have : (0 : ℝ) < n - 1 := by linarith
      positivity)
  have hbig : (16 : ℝ) / 15 ≤ Real.log (15 / η) := by
    have h1500 : (1500 : ℝ) ≤ 15 / η := by
      rw [le_div_iff₀ hη0]; nlinarith
    have : (16 : ℝ) / 15 ≤ Real.log 1500 := by
      have h3 : Real.exp 2 ≤ 1500 := by
        have := Real.exp_one_lt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [h2]; nlinarith [Real.exp_pos 1]
      have : (2 : ℝ) ≤ Real.log 1500 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]; exact h3
      linarith
    exact this.trans (Real.log_le_log (by norm_num) h1500)
  rw [div_le_div_iff₀ hn0 (by norm_num), hsplit]
  nlinarith

/-- **Rate condition on a cell from two tangent checks.** With `u = e^α - 1`, the function
`log(1 + p u) - α(p + λ)` lies below the line through the tangent of `log` at `p_a`. -/
theorem rate_of_tangent (pa pb lam α : ℝ) (hα : 0 ≤ α) (h0 : 0 ≤ pa)
    (ha : Real.log (1 + pa * (Real.exp α - 1)) ≤ α * (pa + lam))
    (hb : Real.log (1 + pa * (Real.exp α - 1)) +
        (pb - pa) * (Real.exp α - 1) / (1 + pa * (Real.exp α - 1)) ≤ α * (pb + lam))
    (p : ℝ) (hpa : pa ≤ p) (hpb : p ≤ pb) :
    1 - p + p * Real.exp α ≤ Real.exp (α * (p + lam)) := by
  set u := Real.exp α - 1
  have hu : 0 ≤ u := by have := Real.one_le_exp hα; linarith
  have hy0 : 0 < 1 + pa * u := by positivity
  have hy : 0 < 1 + p * u := by
    have : 0 ≤ p := le_trans h0 hpa
    positivity
  -- log concavity: log y ≤ log y0 + (y - y0)/y0
  have htan : Real.log (1 + p * u) ≤ Real.log (1 + pa * u) + (p - pa) * u / (1 + pa * u) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hy0)
    rw [Real.log_div hy.ne' hy0.ne'] at h
    have : (1 + p * u) / (1 + pa * u) - 1 = (p - pa) * u / (1 + pa * u) := by
      field_simp; ring
    linarith
  -- the affine bound is ≤ 0 at both ends, hence inside
  have hlin : Real.log (1 + pa * u) + (p - pa) * u / (1 + pa * u) ≤ α * (p + lam) := by
    rcases eq_or_lt_of_le (le_trans hpa hpb) with hab | hab
    · have : p = pa := le_antisymm (hab ▸ hpb) hpa
      subst this; simpa using ha
    · set w := (p - pa) / (pb - pa)
      have hw0 : 0 ≤ w := div_nonneg (by linarith) (by linarith)
      have hw1 : w ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hne : pb - pa ≠ 0 := by linarith
      have hp : p = pa + w * (pb - pa) := by
        simp only [w]; rw [div_mul_cancel₀ _ hne]; ring
      have e1 : (p - pa) * u / (1 + pa * u) = w * ((pb - pa) * u / (1 + pa * u)) := by
        rw [hp]; ring
      rw [e1]
      have := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 1 - w))
        (mul_le_mul_of_nonneg_left hb hw0)
      nlinarith
  have hfin : Real.log (1 + p * u) ≤ α * (p + lam) := htan.trans hlin
  have := Real.exp_le_exp.2 hfin
  rw [Real.exp_log hy] at this
  calc 1 - p + p * Real.exp α = 1 + p * u := by simp only [u]; ring
    _ ≤ _ := this

end NumGlue
