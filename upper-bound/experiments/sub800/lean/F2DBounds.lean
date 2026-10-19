import F2DCells

/-! # Rational-witness forms of the fringe numerics -/

namespace Chvatal

/-- Two-sided log witness. -/
theorem log_between (y v lo hi U : ℝ) (hy : y = v) (hv : 0 < v) (hU : Real.exp lo ≤ U)
    (hUv : U ≤ v) (hvhi : v ≤ Real.exp hi) : lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  subst hy
  exact ⟨ExpBounds.le_log _ _ hv (hU.trans hUv), ExpBounds.log_le _ _ hv hvhi⟩

/-- `log (e^k v) ≤ k + A` from `v ≤ e^A`. -/
theorem log_exp_mul_le (y k v A : ℝ) (hy : y = Real.exp k * v) (hv : 0 < v)
    (h : v ≤ Real.exp A) : Real.log y ≤ k + A := by
  subst hy
  rw [Real.log_mul (Real.exp_pos k).ne' hv.ne', Real.log_exp]
  linarith [ExpBounds.log_le _ _ hv h]

/-- The block constant from rational bounds. -/
theorem block_M_le (c LY H A Ea Eb W U1 U0 hi2 lo2 X1 X0 : ℝ) (hc : 0 ≤ c) (hEb : 0 ≤ Eb)
    (hW : 0 ≤ W) (hA : A = Real.exp 2 * W) (he2hi : Real.exp 2 ≤ hi2) (he2lo : lo2 ≤ Real.exp 2)
    (hX1 : LY + Ea * (c * LY + H) ≤ X1) (hU1 : Real.exp X1 ≤ U1)
    (hEa : 1 ≤ Ea) (hX0 : LY + lo2 * W + Ea * (c * LY - lo2 * W) ≤ X0) (hU0 : Real.exp X0 ≤ U0) :
    (c * Eb + 2) * (Real.exp 2 * (Eb * W) * Real.exp (LY + Ea * (c * LY + H)) +
      2 * Real.exp (LY + A + Ea * (c * LY - A))) ≤
      (c * Eb + 2) * (hi2 * (Eb * W) * U1 + 2 * U0) := by
  have k1 : Real.exp (LY + Ea * (c * LY + H)) ≤ U1 := (Real.exp_le_exp.mpr hX1).trans hU1
  have k2 : Real.exp (LY + A + Ea * (c * LY - A)) ≤ U0 := by
    refine (Real.exp_le_exp.mpr ?_).trans hU0
    rw [hA]
    have : lo2 * W * (Ea - 1) ≤ Real.exp 2 * W * (Ea - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he2lo hW) (by linarith)
    nlinarith
  have hpos : 0 ≤ c * Eb + 2 := by positivity
  have hh : 0 ≤ hi2 := (Real.exp_pos 2).le.trans he2hi
  have hu1 : 0 ≤ U1 := (Real.exp_pos _).le.trans hU1
  have hw : 0 ≤ hi2 * (Eb * W) := by positivity
  gcongr

/-- The tail constant from rational bounds. -/
theorem tail_M_le (c LY lam mu A0 ET W hi2 elo U3 U4 U5 U6 : ℝ) (hc : 0 ≤ c) (hW : 0 ≤ W)
    (hlam : 0 < lam) (hmu : 0 < mu) (helo : 0 < elo)
    (he2hi : Real.exp 2 ≤ hi2) (he1 : elo ≤ Real.exp 1)
    (hU3 : Real.exp (LY - lam / 2 * ET) ≤ U3) (hU4 : Real.exp (-(lam / 2)) ≤ U4) (hU4' : U4 < 1)
    (hU5 : Real.exp (LY + A0 - mu / 2 * ET) ≤ U5) (hU6 : Real.exp (-(mu / 2)) ≤ U6) (hU6' : U6 < 1) :
    (c + 2) * (Real.exp 2 * W * (4 / (Real.exp 1 * lam)) ^ 2 *
        (Real.exp (LY - lam / 2 * ET) / (1 - Real.exp (-(lam / 2)))) +
      2 * (2 / (Real.exp 1 * mu)) *
        (Real.exp (LY + A0 - mu / 2 * ET) / (1 - Real.exp (-(mu / 2))))) ≤
    (c + 2) * (hi2 * W * (4 / (elo * lam)) ^ 2 * (U3 / (1 - U4)) +
      2 * (2 / (elo * mu)) * (U5 / (1 - U6))) := by
  have h4 : 0 < 1 - U4 := by linarith
  have h6 : 0 < 1 - U6 := by linarith
  have hq1 : 4 / (Real.exp 1 * lam) ≤ 4 / (elo * lam) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_right he1 hlam.le)
  have hq2 : 2 / (Real.exp 1 * mu) ≤ 2 / (elo * mu) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_right he1 hmu.le)
  have hd1 : Real.exp (LY - lam / 2 * ET) / (1 - Real.exp (-(lam / 2))) ≤ U3 / (1 - U4) :=
    div_le_div₀ ((Real.exp_pos _).le.trans hU3) hU3 h4 (by linarith)
  have hd2 : Real.exp (LY + A0 - mu / 2 * ET) / (1 - Real.exp (-(mu / 2))) ≤ U5 / (1 - U6) :=
    div_le_div₀ ((Real.exp_pos _).le.trans hU5) hU5 h6 (by linarith)
  have hd10 : 0 ≤ Real.exp (LY - lam / 2 * ET) / (1 - Real.exp (-(lam / 2))) := by
    have : Real.exp (-(lam / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  have hd20 : 0 ≤ Real.exp (LY + A0 - mu / 2 * ET) / (1 - Real.exp (-(mu / 2))) := by
    have : Real.exp (-(mu / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  have hpos : 0 ≤ c + 2 := by linarith
  have hh : 0 ≤ hi2 := (Real.exp_pos 2).le.trans he2hi
  have hw : 0 ≤ hi2 * W * (4 / (elo * lam)) ^ 2 := by positivity
  gcongr

end Chvatal
