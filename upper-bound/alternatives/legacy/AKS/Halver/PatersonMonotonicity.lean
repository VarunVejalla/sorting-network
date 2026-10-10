module

public import AKS.Halver.PatersonEntropy

/-! # Monotonicity of the restricted-halver entropy bound -/

@[expose] public section

namespace Paterson

set_option backward.isDefEq.respectTransparency false

/-- The entropy quotient in Paterson's depth bound (before adding one). -/
noncomputable def depthRatio (a e : ℝ) : ℝ :=
  (Real.binEntropy (e * a) + Real.binEntropy ((1 - e) * a)) /
    (-(e * a) * Real.log ((1 - e) * a))

private theorem entropy_formula (x : ℝ) :
    Real.binEntropy x = -x * Real.log x - (1 - x) * Real.log (1 - x) := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  ring

/-- The entropy inequality responsible for monotonicity in the supported
fraction. A non-strict version suffices for the existence bound. -/
theorem log_mul_log_le_entropy {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Real.log x * Real.log (1 - x) ≤ Real.binEntropy x := by
  have hy : 0 < 1 - x := sub_pos.mpr hx1
  have h1 := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hx.le
  have h2 := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hy) hy.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at h1
  rw [mul_sub, mul_one, mul_inv_cancel₀ hy.ne'] at h2
  have hlx : Real.log x ≤ 0 := (Real.log_neg hx hx1).le
  have hly : Real.log (1 - x) ≤ 0 := (Real.log_neg hy (by linarith)).le
  have h3 := mul_le_mul_of_nonneg_right h1 (neg_nonneg.mpr hly)
  have h4 := mul_le_mul_of_nonneg_right h2 (neg_nonneg.mpr hlx)
  rw [entropy_formula]
  nlinarith only [h3, h4]

private theorem fraction_bounds {a e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e < 1) :
    0 < e * a ∧ e * a < 1 ∧ 0 < (1 - e) * a ∧ (1 - e) * a < 1 := by
  constructor
  · exact mul_pos he ha
  constructor
  · nlinarith
  constructor
  · exact mul_pos (sub_pos.mpr he1) ha
  · nlinarith

private noncomputable def alphaDerivative (a e : ℝ) : ℝ :=
  ((e * (Real.log (1 - e * a) - Real.log (e * a)) +
      (1 - e) * (Real.log (1 - (1 - e) * a) - Real.log ((1 - e) * a))) *
      (-(e * a) * Real.log ((1 - e) * a)) -
    (Real.binEntropy (e * a) + Real.binEntropy ((1 - e) * a)) *
      (-e * Real.log ((1 - e) * a) - e)) /
    (-(e * a) * Real.log ((1 - e) * a)) ^ 2

private theorem hasDerivAt_alpha {a e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e < 1) :
    HasDerivAt (fun a => depthRatio a e) (alphaDerivative a e) a := by
  obtain ⟨hp, hp1, hq, hq1⟩ := fraction_bounds ha ha1 he he1
  have hd : -(e * a) * Real.log ((1 - e) * a) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hp.ne') (Real.log_neg hq hq1).ne
  have dp := (hasDerivAt_id a).const_mul e
  have dq := (hasDerivAt_id a).const_mul (1 - e)
  have du := ((Real.hasDerivAt_binEntropy hp.ne' (ne_of_lt hp1)).comp a dp).add
    ((Real.hasDerivAt_binEntropy hq.ne' (ne_of_lt hq1)).comp a dq)
  have dv := dp.neg.mul (dq.log hq.ne')
  have h := du.div dv hd
  convert h using 1
  dsimp [alphaDerivative]
  congr 1
  field_simp [ha.ne', (sub_pos.mpr he1).ne']
  <;> ring

private theorem alphaDerivative_nonneg {a e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (he : 0 < e) (hehalf : e ≤ 1 / 2) : 0 ≤ alphaDerivative a e := by
  have he1 : e < 1 := by linarith
  obtain ⟨hp, hp1, hq, hq1⟩ := fraction_bounds ha ha1 he he1
  have hlog := Real.log_le_log hp (show e * a ≤ (1 - e) * a by nlinarith)
  have hlog1p : Real.log (1 - e * a) ≤ 0 :=
    (Real.log_neg (sub_pos.mpr hp1) (by linarith)).le
  have hm := mul_le_mul_of_nonpos_right hlog hlog1p
  have hbp := log_mul_log_le_entropy hp hp1
  have hbq := log_mul_log_le_entropy hq hq1
  have hE : 0 ≤ Real.binEntropy (e * a) + Real.binEntropy ((1 - e) * a) -
      Real.log ((1 - e) * a) *
        (Real.log (1 - e * a) + Real.log (1 - (1 - e) * a)) := by
    nlinarith only [hm, hbp, hbq]
  unfold alphaDerivative
  apply div_nonneg _ (sq_nonneg _)
  have hmul := mul_nonneg hp.le hE
  rw [entropy_formula, entropy_formula] at hmul ⊢
  nlinarith only [hmul, ha]

/-- Increasing the supported fraction cannot decrease the entropy budget. -/
theorem depthRatio_mono_alpha {e : ℝ} (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    MonotoneOn (fun a => depthRatio a e) (Set.Ioc 0 1) := by
  have he1 : e < 1 := by linarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1)
    (f' := fun a => alphaDerivative a e)
  · intro a ha
    exact (hasDerivAt_alpha ha.1 ha.2 he he1).continuousAt.continuousWithinAt
  · intro a ha
    have hmem := interior_subset ha
    exact (hasDerivAt_alpha hmem.1 hmem.2 he he1).hasDerivWithinAt
  · intro a ha
    have hmem := interior_subset ha
    exact alphaDerivative_nonneg hmem.1 hmem.2 he hehalf

private noncomputable def epsilonDerivative (a e : ℝ) : ℝ :=
  ((a * (Real.log (1 - e * a) - Real.log (e * a)) -
      a * (Real.log (1 - (1 - e) * a) - Real.log ((1 - e) * a))) *
      (-(e * a) * Real.log ((1 - e) * a)) -
    (Real.binEntropy (e * a) + Real.binEntropy ((1 - e) * a)) *
      (-a * Real.log ((1 - e) * a) + e * a / (1 - e))) /
    (-(e * a) * Real.log ((1 - e) * a)) ^ 2

private theorem hasDerivAt_epsilon {a e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e < 1) :
    HasDerivAt (depthRatio a) (epsilonDerivative a e) e := by
  obtain ⟨hp, hp1, hq, hq1⟩ := fraction_bounds ha ha1 he he1
  have hd : -(e * a) * Real.log ((1 - e) * a) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hp.ne') (Real.log_neg hq hq1).ne
  have dp := (hasDerivAt_id e).mul_const a
  have dq := ((hasDerivAt_const e (1 : ℝ)).sub (hasDerivAt_id e)).mul_const a
  have du := ((Real.hasDerivAt_binEntropy hp.ne' (ne_of_lt hp1)).comp e dp).add
    ((Real.hasDerivAt_binEntropy hq.ne' (ne_of_lt hq1)).comp e dq)
  have dv := dp.neg.mul (dq.log hq.ne')
  have h := du.div dv hd
  convert h using 1
  dsimp [epsilonDerivative]
  congr 1
  field_simp [ha.ne', (sub_pos.mpr he1).ne']
  <;> ring

private theorem epsilonDerivative_nonpos {a e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e < 1) : epsilonDerivative a e ≤ 0 := by
  obtain ⟨hp, hp1, hq, hq1⟩ := fraction_bounds ha ha1 he he1
  have hlp : Real.log (1 - e * a) ≤ 0 :=
    (Real.log_neg (sub_pos.mpr hp1) (by linarith)).le
  have hlq : Real.log ((1 - e) * a) ≤ 0 := (Real.log_neg hq hq1).le
  have hlqc : Real.log (1 - (1 - e) * a) ≤ 0 :=
    (Real.log_neg (sub_pos.mpr hq1) (by linarith)).le
  have hnorm : Real.log (1 - e * a) + a * Real.log ((1 - e) * a) +
      (1 - a) * Real.log (1 - (1 - e) * a) ≤ 0 := by
    exact add_nonpos (add_nonpos hlp (mul_nonpos_of_nonneg_of_nonpos ha.le hlq))
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha1) hlqc)
  have hv : 0 ≤ -(e * a) * Real.log ((1 - e) * a) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hp.le) hlq
  have hU : 0 ≤ Real.binEntropy (e * a) + Real.binEntropy ((1 - e) * a) :=
    add_nonneg (Real.binEntropy_nonneg hp.le hp1.le) (Real.binEntropy_nonneg hq.le hq1.le)
  have hpiece : 0 ≤ (Real.binEntropy (e * a) + Real.binEntropy ((1 - e) * a)) *
      e * (e * a) / (1 - e) :=
    div_nonneg (mul_nonneg (mul_nonneg hU he.le) hp.le) (sub_nonneg.mpr he1.le)
  have hmul := mul_nonpos_of_nonneg_of_nonpos hv hnorm
  unfold epsilonDerivative
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  apply nonpos_of_mul_nonpos_right ?_ he
  convert sub_nonpos.mpr (hmul.trans hpiece) using 1 <;>
    simp only [entropy_formula] <;> field_simp [(sub_pos.mpr he1).ne'] <;> ring

/-- Increasing the tolerated error cannot increase the entropy budget. -/
theorem depthRatio_anti_epsilon {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    AntitoneOn (depthRatio a) (Set.Ioo 0 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1)
    (f' := fun e => epsilonDerivative a e)
  · intro e he
    exact (hasDerivAt_epsilon ha ha1 he.1 he.2).continuousAt.continuousWithinAt
  · intro e he
    have hmem := interior_subset he
    exact (hasDerivAt_epsilon ha ha1 hmem.1 hmem.2).hasDerivWithinAt
  · intro e he
    have hmem := interior_subset he
    exact epsilonDerivative_nonpos ha ha1 hmem.1 hmem.2

/-- The two monotonicities together compare each discrete witness against
the advertised pair of real parameters. -/
theorem depthRatio_le {a a' e e' : ℝ}
    (ha : 0 < a) (haa' : a ≤ a') (ha' : a' ≤ 1)
    (he : 0 < e) (hee' : e ≤ e') (he' : e' ≤ 1 / 2) :
    depthRatio a e' ≤ depthRatio a' e := by
  have he1 : e < 1 := by linarith
  have he'1 : e' < 1 := by linarith
  calc
    depthRatio a e' ≤ depthRatio a e :=
      depthRatio_anti_epsilon ha (haa'.trans ha') ⟨he, he1⟩
        ⟨he.trans_le hee', he'1⟩ hee'
    _ ≤ depthRatio a' e := depthRatio_mono_alpha he (by linarith)
      ⟨ha, haa'.trans ha'⟩ ⟨ha.trans_le haa', ha'⟩ haa'

end Paterson
