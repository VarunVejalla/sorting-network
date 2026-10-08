module

/-
  # `Theorem51Params g` for every §7 scramble geometry (A8)

  For every `ScrambleGeometry g` with `f ≥ 1.7·10^10` and `m ≥ 2^59` (ordinary) resp.
  `m ≥ 2^79` (root), builds `Theorem51Params g` with `δ_F = 128/4095`, `ε_F = eps = 1/(8·10^7)`
  and the paper's `ε_B` (`paperOrdinaryEpsB`, `paperRootEpsB`), and applies
  `ExistsScrambleSeparator_general`.
-/

public import AKS.Chvatal.GeneralSeparator
public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.Theorem51Core
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 2400000

@[expose] public section

namespace Chvatal

/-- Tangent-line bound `log x ≤ log c + x/c - 1`. -/
private theorem log_le_tangent {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at h
  linarith

private theorem logDenom_gt_third :
    (1 / 3 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
  rw [show (0.12 : ℝ) = (12 / 100 : ℝ) from by norm_num]
  have h14 : (141 / 100 : ℝ) < (12 / 100 : ℝ) / (Real.exp 1 * (128 / 4095 : ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < (41 / 100 : ℝ))
  rw [show (1 : ℝ) + 41 / 100 = (141 / 100 : ℝ) from by ring] at h
  have hl : Real.log (141 / 100 : ℝ) < Real.log ((12 / 100 : ℝ) / (Real.exp 1 * (128 / 4095 : ℝ))) :=
    Real.log_lt_log (by norm_num) h14
  have : (1 / 3 : ℝ) < 2 * (41 / 100) / (41 / 100 + 2) := by norm_num
  linarith

private theorem log_f0_le : Real.log ((17 * 10 ^ 9 : ℕ) : ℝ) ≤ 35 * Real.log 2 := by
  have h : (((17 * 10 ^ 9 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ 35 := by norm_num
  have := Real.log_le_log (by norm_num) h
  rwa [Real.log_pow, Nat.cast_ofNat] at this

/-- **(a)** Lemma 6.2 floor for all `f ≥ 1.7·10^10` at `δ_F = 128/4095`. -/
theorem epsF_floor_general {f : ℕ} (hf : 17 * 10 ^ 9 ≤ f) :
    epsF_lemma62_lb f (128 / 4095 : ℝ) ≤ eps := by
  unfold epsF_lemma62_lb eps
  have hfR : (17 * 10 ^ 9 : ℝ) ≤ f := by exact_mod_cast hf
  have hD := logDenom_gt_third
  have hDpos : (0 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by linarith
  have hL2 := Real.log_two_lt_d9
  have hL2p := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hf0 := log_f0_le
  have hfpos : (0 : ℝ) < f := by linarith
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have := Real.log_le_log (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≤ 2 ^ 2)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have htan := log_le_tangent hfpos (by norm_num : (0 : ℝ) < 17 * 10 ^ 9)
  have hsplit : Real.log (3 * Real.exp 5 * (f : ℝ)) = Real.log 3 + 5 + Real.log f := by
    rw [Real.log_mul (by positivity) hfpos.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp]
  have hf0' : Real.log ((17 * 10 ^ 9 : ℕ) : ℝ) = Real.log ((17 * 10 ^ 9 : ℝ)) := by norm_num
  have hT : Real.log (3 * Real.exp 5 * (f : ℝ)) ≤ 29.65 + f / (17 * 10 ^ 9) := by
    rw [hsplit]
    have h0 : Real.log (17 * 10 ^ 9 : ℝ) ≤ 35 * Real.log 2 := hf0' ▸ hf0
    norm_num at h0 htan ⊢
    linarith
  have hTpos : 0 ≤ Real.log (3 * Real.exp 5 * (f : ℝ)) := by
    rw [hsplit]
    have : (1:ℝ) ≤ f := by linarith
    have := Real.log_nonneg this
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
    linarith
  have hdiv : Real.log (3 * Real.exp 5 * (f : ℝ)) /
      Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) ≤
      3 * Real.log (3 * Real.exp 5 * (f : ℝ)) := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  have hsub : (0 : ℝ) < (f : ℝ) - 2 := by linarith
  have key : 2 / ((f : ℝ) - 2) * (1 + Real.log (3 * Real.exp 5 * (f : ℝ)) /
      Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤ 1 / (8 * 10 ^ 7) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hsub]
    have : (1 + Real.log (3 * Real.exp 5 * (f : ℝ)) /
      Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) * 2 ≤
        (1 + 3 * (29.65 + f / (17 * 10 ^ 9))) * 2 := by linarith
    rw [mul_comm 2]
    refine this.trans ?_
    have : f / (17 * 10 ^ 9 : ℝ) = f * (1 / (17 * 10 ^ 9)) := by ring
    nlinarith
  simpa using key

/-- **(b)** `4e/f ≤ eps` for `f ≥ 1.7·10^10`. -/
theorem four_e_div_le {f : ℕ} (hf : 17 * 10 ^ 9 ≤ f) :
    (4 * Real.exp 1) / (f : ℝ) ≤ eps := by
  unfold eps
  have hfR : (17 * 10 ^ 9 : ℝ) ≤ f := by exact_mod_cast hf
  have he := Real.exp_one_lt_d9
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Monotonicity of `2(1+log x)/x` on `x ≥ 1`. -/
private theorem chernoff_mono {M m : ℝ} (hM : 1 ≤ M) (hmM : M ≤ m) :
    2 * (1 + Real.log m) / m ≤ 2 * (1 + Real.log M) / M := by
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < m := by linarith
  have htan := log_le_tangent hm0 hM0
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

/-- **(c)** ordinary `ε_B` for all `m ≥ 2^59`. -/
theorem epsB_general {m : ℕ} (hm : 2 ^ 59 ≤ m) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤ paperOrdinaryEpsB := by
  unfold paperOrdinaryEpsB
  have := sqrt_chernoff_le (j := 29) hm (by norm_num)
  simpa using this

/-- **(c')** root `ε*` for all `m ≥ 2^79`. -/
theorem epsB_root_general {m : ℕ} (hm : 2 ^ 79 ≤ m) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤ paperRootEpsB := by
  unfold paperRootEpsB
  have := sqrt_chernoff_le (j := 39) hm (by norm_num)
  simpa using this

theorem delta_pos : (0 : ℝ) < 128 / 4095 := by norm_num
theorem delta_le : (128 / 4095 : ℝ) ≤ 1 / 25 := by norm_num

/-- **(d)** `Theorem51Params` for every ordinary geometry. -/
noncomputable def theorem51Params_general (g : ScrambleGeometry) (hf : 17 * 10 ^ 9 ≤ g.f)
    (hm : 2 ^ 59 ≤ g.m) : Theorem51Params g where
  epsB := paperOrdinaryEpsB
  deltaF := 128 / 4095
  epsF := eps
  hepsB_pos := by unfold paperOrdinaryEpsB; positivity
  hepsB_lb := epsB_general hm
  hdeltaF_pos := delta_pos
  hdeltaF := delta_le
  hepsF_pos := eps_pos
  hepsF_ge_4e := four_e_div_le hf
  hepsF_ge_lemma62 := epsF_floor_general hf




end Chvatal
