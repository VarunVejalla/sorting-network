import AKS.Sub800.F2DR2d
import AKS.Sub800.ExpBounds

/-! # Cells for the R2 `θ`-function `hR2`

Each bound is linear in `θ` on its cell after the logarithms are replaced by witnesses, so it is
checked at the two endpoints. -/

namespace Chvatal

theorem lin_le_max (θa θb θ X B : ℝ) (ha : θa ≤ θ) (hb : θ ≤ θb)
    (h1 : θa * X ≤ B) (h2 : θb * X ≤ B) : θ * X ≤ B := by
  rcases le_or_gt 0 X with hX | hX
  · exact le_trans (mul_le_mul_of_nonneg_right hb hX) h2
  · exact le_trans (mul_le_mul_of_nonpos_right ha hX.le) h1

theorem log_frac_mono (θ θb : ℝ) (h0 : 0 < θ) (hb : θ ≤ θb) :
    Real.log (θ / (θ + 1)) ≤ Real.log (θb / (θb + 1)) := by
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- Middle cell `[θa, θb]`. -/
theorem hR2_mid (P : F2PD) (L0 κ1 θa θb la ub Lk B1 B2 H θ : ℝ) (h0 : 0 < θa)
    (hθa : θa ≤ θ) (hθb : θ ≤ θb) (hla : la ≤ Real.log θa) (hub : Real.log (θb / (θb + 1)) ≤ ub)
    (hLk : Real.log (κ1 / P.Φ) ≤ Lk) (hΦ : 1 ≤ P.Φ)
    (hB1a : θa * (L0 - la) ≤ B1 * P.Φ) (hB1b : θb * (L0 - la) ≤ B1 * P.Φ)
    (hB2a : (θa + 1) * (1 + Lk + ub) ≤ B2) (hB2b : (θb + 1) * (1 + Lk + ub) ≤ B2)
    (hH : B1 + B2 ≤ H) : hR2 P L0 κ1 θ ≤ H := by
  have hθ0 : 0 < θ := lt_of_lt_of_le h0 hθa
  have hΦ0 : (0 : ℝ) < P.Φ := by exact_mod_cast (lt_of_lt_of_le one_pos hΦ)
  unfold hR2
  have hl : la ≤ Real.log θ := hla.trans (Real.log_le_log h0 hθa)
  have t1 : θ / P.Φ * (L0 - Real.log θ) ≤ B1 := by
    have h := lin_le_max θa θb θ (L0 - la) (B1 * P.Φ) hθa hθb hB1a hB1b
    have h' : θ * (L0 - Real.log θ) ≤ B1 * P.Φ :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) hθ0.le) h
    rw [div_mul_eq_mul_div, div_le_iff₀ hΦ0]; exact h'
  have t2 : (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤ B2 := by
    have hq := log_frac_mono θ θb hθ0 hθb
    have h := lin_le_max θa θb θ (1 + Lk + ub) (B2 - (1 + Lk + ub)) hθa hθb (by linarith)
      (by linarith)
    have h' : (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤
        (θ + 1) * (1 + Lk + ub) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  linarith

/-- First cell `(0, θ1]` (needs `0 ≤ L0` and a nonpositive slope `Q`). -/
theorem hR2_first (P : F2PD) (L0 κ1 θ1 ub Lk H θ : ℝ) (h0 : 0 < θ) (hθ1 : θ ≤ θ1)
    (hL0 : 0 ≤ L0) (hub : Real.log (θ1 / (θ1 + 1)) ≤ ub)
    (hLk : Real.log (κ1 / P.Φ) ≤ Lk) (hΦ : 1 ≤ P.Φ) (hQ : 1 + Lk + ub ≤ 0)
    (hH : (θ1 * L0 + 1) / P.Φ + (1 + Lk + ub) ≤ H) : hR2 P L0 κ1 θ ≤ H := by
  have hΦ0 : (0 : ℝ) < P.Φ := by exact_mod_cast (lt_of_lt_of_le one_pos hΦ)
  unfold hR2
  have t1 : θ / P.Φ * (L0 - Real.log θ) ≤ (θ1 * L0 + 1) / P.Φ := by
    have hlog := Real.one_sub_inv_le_log_of_pos h0
    have h1 : -(θ * Real.log θ) ≤ 1 := by
      have : θ * (1 - θ⁻¹) ≤ θ * Real.log θ := mul_le_mul_of_nonneg_left hlog h0.le
      have e : θ * (1 - θ⁻¹) = θ - 1 := by field_simp
      linarith
    have h2 : θ * L0 ≤ θ1 * L0 := mul_le_mul_of_nonneg_right hθ1 hL0
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hΦ0.le
  have t2 : (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤ 1 + Lk + ub := by
    have hq := log_frac_mono θ θ1 h0 hθ1
    have h' : (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤
        (θ + 1) * (1 + Lk + ub) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  linarith

/-- Last cell `[θmax, ∞)` (needs `L0 ≤ log θmax` and `1 + Lk ≤ 0`). -/
theorem hR2_last (P : F2PD) (L0 κ1 θmax la Lk H θ : ℝ) (h0 : 0 < θmax) (hθ : θmax ≤ θ)
    (hla : la ≤ Real.log θmax) (hL0 : L0 ≤ la)
    (hLk : Real.log (κ1 / P.Φ) ≤ Lk) (hΦ : 1 ≤ P.Φ) (hK : 1 + Lk ≤ 0)
    (hH : (θmax + 1) * (1 + Lk) ≤ H) : hR2 P L0 κ1 θ ≤ H := by
  have hθ0 : 0 < θ := lt_of_lt_of_le h0 hθ
  have hΦ0 : (0 : ℝ) < P.Φ := by exact_mod_cast (lt_of_lt_of_le one_pos hΦ)
  unfold hR2
  have t1 : θ / P.Φ * (L0 - Real.log θ) ≤ 0 := by
    have : L0 - Real.log θ ≤ 0 := by linarith [Real.log_le_log h0 hθ]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have t2 : (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤ (θmax + 1) * (1 + Lk) := by
    have hq : Real.log (θ / (θ + 1)) ≤ 0 :=
      Real.log_nonpos (by positivity) (by rw [div_le_one (by linarith)]; linarith)
    have h' : (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤ (θ + 1) * (1 + Lk) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h'' : (θ + 1) * (1 + Lk) ≤ (θmax + 1) * (1 + Lk) :=
      mul_le_mul_of_nonpos_right (by linarith) hK
    linarith
  linarith

/-- `log (exp k * a / b) ≤ k + A` from `a / b ≤ exp A`. -/
theorem log_exp_mul_div_le (k a b A : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a / b ≤ Real.exp A) :
    Real.log (Real.exp k * a / b) ≤ k + A := by
  rw [mul_div_assoc, Real.log_mul (Real.exp_pos k).ne' (div_pos ha hb).ne', Real.log_exp]
  linarith [ExpBounds.log_le _ _ (by positivity) h]

end Chvatal
