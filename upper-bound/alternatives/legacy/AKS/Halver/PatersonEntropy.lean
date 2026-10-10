module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Data.Nat.Choose.Basic

/-! # Sharp binomial estimate for the Paterson union bound

The needed square-root prefactor follows from monotonicity of the normalized
Stirling sequence and its lower bound by sqrt(pi). This avoids requiring the
stronger Robbins remainder theorem.
-/

@[expose] public section

namespace Paterson

private theorem log_stirling_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (Stirling.stirlingSeq b) ≤ Real.log (Stirling.stirlingSeq a) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
  exact Stirling.log_stirlingSeq'_antitone (show a ≤ b by omega)

private theorem log_stirling_lower {n : ℕ} (hn : 0 < n) :
    Real.log Real.pi / 2 ≤ Real.log (Stirling.stirlingSeq n) := by
  have h := Real.log_le_log (Real.sqrt_pos.mpr Real.pi_pos)
    (Stirling.sqrt_pi_le_stirlingSeq (Nat.ne_of_gt hn))
  rwa [Real.log_sqrt Real.pi_nonneg] at h

private theorem log_factorial_eq (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) = (n : ℝ) * Real.log n - n +
      (Real.log 2 + Real.log n) / 2 + Real.log (Stirling.stirlingSeq n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) hnR.ne',
    Real.log_div hnR.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- Sharp logarithmic bound for a binomial coefficient. Written in the
equivalent scaled-entropy form to keep all arguments positive explicitly. -/
theorem log_choose_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.log ((a + b).choose a : ℝ) ≤
      (a + b : ℝ) * Real.log (a + b : ℝ) -
        a * Real.log (a : ℝ) - b * Real.log (b : ℝ) -
        Real.log ((min a b : ℕ) : ℝ) / 2 - Real.log Real.pi / 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < (a + b : ℝ) := add_pos haR hbR
  have hca : (0 : ℝ) < (a + b).choose a := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right a b)
  have hfa : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hfb : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hprod : ((a + b).choose a : ℝ) * a.factorial * b.factorial =
      (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    simp only [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hlogs := congrArg Real.log hprod
  rw [Real.log_mul (mul_pos hca hfa).ne' hfb.ne',
    Real.log_mul hca.ne' hfa.ne'] at hlogs
  have hfn := log_factorial_eq (a + b) (by omega)
  have hfa' := log_factorial_eq a ha
  have hfb' := log_factorial_eq b hb
  simp only [Nat.cast_add] at hfn
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    have hseq := log_stirling_antitone hb (Nat.le_add_left b a)
    have hlow := log_stirling_lower ha
    have hlog := Real.log_le_log hnR
      (show (a + b : ℝ) ≤ 2 * (b : ℝ) by exact_mod_cast (by omega : a + b ≤ 2 * b))
    rw [Real.log_mul (by norm_num) hbR.ne'] at hlog
    linarith
  · rw [min_eq_right hba]
    have hseq := log_stirling_antitone ha (Nat.le_add_right a b)
    have hlow := log_stirling_lower hb
    have hlog := Real.log_le_log hnR
      (show (a + b : ℝ) ≤ 2 * (a : ℝ) by exact_mod_cast (by omega : a + b ≤ 2 * a))
    rw [Real.log_mul (by norm_num) haR.ne'] at hlog
    linarith

/-- The homogeneous form of binary entropy. -/
theorem entropy_scaled {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * Real.binEntropy (a / (a + b)) =
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
  have hn : a + b ≠ 0 := (add_pos ha hb).ne'
  have hc : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hc]
  simp only [Real.negMulLog_def]
  rw [Real.log_div ha.ne' hn, Real.log_div hb.ne' hn]
  field_simp
  ring

/-- Paterson's sharp binomial entropy estimate, including the square-root
prefactor needed to make the all-size union bound summable. -/
theorem log_choose_le_entropy (n r : ℕ) (hr : 0 < r) (hrn : r < n) :
    Real.log (n.choose r : ℝ) ≤
      n * Real.binEntropy ((r : ℝ) / n) -
        Real.log ((min r (n - r) : ℕ) : ℝ) / 2 - Real.log Real.pi / 2 := by
  have hs : 0 < n - r := Nat.sub_pos_of_lt hrn
  have hn : r + (n - r) = n := Nat.add_sub_of_le hrn.le
  have hnR : (r : ℝ) + (n - r : ℕ) = n := by exact_mod_cast hn
  have h := log_choose_le r (n - r) hr hs
  rw [hn, hnR] at h
  have he := entropy_scaled (show (0 : ℝ) < r by exact_mod_cast hr)
    (show (0 : ℝ) < (n - r : ℕ) by exact_mod_cast hs)
  rw [hnR] at he
  linarith

/-- A single size-pair contribution is summable once the entropy budget is
met. The factor `1 / (pi * r)` is the gain that the coarse binomial estimate
would lose. -/
theorem failure_term_le {m r s c : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (hsm : r + s ≤ m)
    (hbudget : (m : ℝ) *
      (Real.binEntropy ((r : ℝ) / m) + Real.binEntropy ((s : ℝ) / m)) ≤
        -((c : ℝ) - 1) * r * Real.log ((s : ℝ) / m)) :
    (m.choose r : ℝ) * m.choose s * ((s : ℝ) / m) ^ (r * c) ≤
      ((s : ℝ) / m) ^ r / (Real.pi * r) := by
  have hs : 0 < s := hr.trans_le hrs
  have hrm : r < m := by omega
  have hsm' : s < m := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq : (0 : ℝ) < (s : ℝ) / m := div_pos hsR hmR
  have hcr : (0 : ℝ) < m.choose r := by exact_mod_cast Nat.choose_pos hrm.le
  have hcs : (0 : ℝ) < m.choose s := by exact_mod_cast Nat.choose_pos hsm'.le
  have hleft : (0 : ℝ) < (m.choose r : ℝ) * m.choose s *
      ((s : ℝ) / m) ^ (r * c) := mul_pos (mul_pos hcr hcs) (pow_pos hq _)
  have hright : (0 : ℝ) < ((s : ℝ) / m) ^ r / (Real.pi * r) :=
    div_pos (pow_pos hq _) (mul_pos Real.pi_pos hrR)
  have h1 := log_choose_le_entropy m r hr hrm
  have h2 := log_choose_le_entropy m s hs hsm'
  rw [min_eq_left (show r ≤ m - r by omega)] at h1
  have hmin : r ≤ min s (m - s) := by omega
  have hlmin := Real.log_le_log hrR
    (show (r : ℝ) ≤ ((min s (m - s) : ℕ) : ℝ) by exact_mod_cast hmin)
  apply (Real.log_le_log_iff hleft hright).mp
  rw [Real.log_mul (mul_pos hcr hcs).ne' (pow_pos hq _).ne',
    Real.log_mul hcr.ne' hcs.ne', Real.log_pow,
    Real.log_div (pow_pos hq _).ne' (mul_pos Real.pi_pos hrR).ne',
    Real.log_pow, Real.log_mul Real.pi_pos.ne' hrR.ne']
  push_cast
  nlinarith only [h1, h2, hbudget, hlmin]

end Paterson
