module

/- `Theorem51Params g` for every §7 scramble geometry: `ε_B` is the paper's
`paperOrdinaryEpsB` / `paperRootEpsB` (valid for `m ≥ 2^59` resp. `m ≥ 2^79`). -/

public import AKS.Chvatal.GeneralSeparator
public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.Theorem51Core
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace Chvatal

/-- Monotonicity of `2(1+log x)/x` on `x ≥ 1`. -/
private theorem chernoff_mono {M m : ℝ} (hM : 1 ≤ M) (hmM : M ≤ m) :
    2 * (1 + Real.log m) / m ≤ 2 * (1 + Real.log M) / M := by
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < m := by linarith
  have htan := Real.log_le_sub_one_of_pos (div_pos hm0 hM0)
  rw [Real.log_div hm0.ne' hM0.ne'] at htan
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM
  rw [div_le_div_iff₀ hm0 hM0]
  have h1 : M * (m / M) = m := by field_simp
  nlinarith [mul_nonneg hlM (sub_nonneg.2 hmM)]

private theorem sqrt_chernoff_le {m k j : ℕ} (hm : 2 ^ k ≤ m) (hkj : 2 ^ k = 2 * (2 ^ j) ^ 2) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤
      Real.sqrt (1 + k * Real.log 2) / (2 : ℝ) ^ j := by
  have hmR : (2 : ℝ) ^ k ≤ m := by exact_mod_cast hm
  have hkjR : (2 : ℝ) ^ k = 2 * ((2 : ℝ) ^ j) ^ 2 := by exact_mod_cast hkj
  have hmono := chernoff_mono (M := (2 : ℝ) ^ k) (m := m) (one_le_pow₀ (by norm_num)) hmR
  rw [Real.log_pow] at hmono
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, hmono.trans (le_of_eq ?_)⟩
  rw [div_pow, Real.sq_sqrt (by positivity), hkjR]
  have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  field_simp

theorem epsB_general {m : ℕ} (hm : 2 ^ 59 ≤ m) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤ paperOrdinaryEpsB := by
  simpa [paperOrdinaryEpsB] using sqrt_chernoff_le (j := 29) hm (by norm_num)

theorem epsB_root_general {m : ℕ} (hm : 2 ^ 79 ≤ m) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤ paperRootEpsB := by
  simpa [paperRootEpsB] using sqrt_chernoff_le (j := 39) hm (by norm_num)

/-- `Theorem51Params` for every ordinary geometry (`δ_F = 128/4095`, `ε_F = eps`). -/
noncomputable def theorem51Params_general (g : ScrambleGeometry) (_ : 17 * 10 ^ 9 ≤ g.f)
    (hm : 2 ^ 59 ≤ g.m) : Theorem51Params g where
  epsB := paperOrdinaryEpsB
  deltaF := 128 / 4095
  epsF := eps
  hepsB_pos := by unfold paperOrdinaryEpsB; positivity
  hepsB_lb := epsB_general hm

end Chvatal
