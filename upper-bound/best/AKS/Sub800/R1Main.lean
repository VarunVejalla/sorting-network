import AKS.Sub800.R1Nets

/-! # Headline at a generic R1 point: `limsup D(n)/log₂ n ≤ 3 · 3S(q)/4`

With stage depth `D = 3 S(q)` (`R1Point.stage`) and `log₂ N = 4d` on `N = 16^d` wires:
* `R1Point.certificate`: for `n ≥ 16^12`, a sorting network of depth `≤ (3D/4) · log₂ n + 3D`;
* `R1Point.minimum_depth_le`, `R1Point.limsup_minimum_div_logb_le`: the corresponding bounds on the
  canonical minimum depth `D(n)`.

The concrete 789.75 point (`D = 1053`) is `R1At78975`. -/

namespace R1T

open SortingDepth Filter

namespace R1Point

variable (P : R1Point)

/-- The certificate for `C = 3D/4`, `K = 3D`. -/
noncomputable def certificate :
    UpperBoundCertificate ((3 * P.stage : ℕ) / 4 : ℝ) (3 * P.stage : ℕ) where
  threshold := 16 ^ 12
  network := fun n hn => by
    have hn1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
    set d := Nat.clog 16 n
    have hd12 : 12 ≤ d := by
      have := Nat.clog_mono_right 16 hn
      rwa [Nat.clog_pow 16 12 (by norm_num)] at this
    have hle : n ≤ 16 ^ d := Nat.le_pow_clog (by norm_num) n
    obtain ⟨T, hs, hdep⟩ := r1_sorter P hd12
    refine ⟨T.restrictWires n hle, restrictWires_sorts T n hle (fun v ↦ hs (α := Bool) v), ?_⟩
    have hlt : 16 ^ (d - 1) < n := by
      have := Nat.pow_pred_clog_lt_self (b := 16) (by norm_num) hn1
      rwa [Nat.pred_eq_sub_one] at this
    have hbig := P.stage_big
    unfold stage at hdep
    have hdn : (T.restrictWires n hle).depth ≤ 3 * P.stage * d := by
      have := restrictWires_depth_le T n hle
      have h3 : 2709 + 3 * bitonicDepthBudget P.bulk.q * (3 * d - 15) + 136 ≤
          3 * (3 * bitonicDepthBudget P.bulk.q) * d := by
        have e : 3 * bitonicDepthBudget P.bulk.q * (3 * d - 15) + 15 * (3 * bitonicDepthBudget P.bulk.q) =
            3 * (3 * bitonicDepthBudget P.bulk.q) * d := by
          rw [show 15 * (3 * bitonicDepthBudget P.bulk.q) = 3 * bitonicDepthBudget P.bulk.q * 15 by ring,
            ← Nat.mul_add, Nat.sub_add_cancel (by omega : 15 ≤ 3 * d)]; ring
        omega
      unfold stage; omega
    have hdR : ((T.restrictWires n hle).depth : ℝ) ≤ ((3 * P.stage : ℕ) : ℝ) * d := by
      exact_mod_cast hdn
    have hlog : (4 : ℝ) * ((d : ℝ) - 1) < Real.logb 2 n := by
      have h1 : ((2 : ℝ) ^ (4 * (d - 1)) : ℝ) < n := by
        have : (16 : ℕ) ^ (d - 1) = 2 ^ (4 * (d - 1)) := by rw [pow_mul]; norm_num
        rw [this] at hlt
        exact_mod_cast hlt
      have h2 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h1
      rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)] at h2
      have h3 : ((4 * (d - 1) : ℕ) : ℝ) = 4 * ((d : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      linarith
    have hD : (0 : ℝ) ≤ ((3 * P.stage : ℕ) : ℝ) := by positivity
    have : ((3 * P.stage : ℕ) : ℝ) * d ≤ ((3 * P.stage : ℕ) : ℝ) / 4 * Real.logb 2 n +
        ((3 * P.stage : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog.le hD
      nlinarith
    linarith

/-- **Pointwise bound.** For every `n ≥ 16^12`, `D(n) ≤ (3D/4) · log₂ n + 3D`. -/
theorem minimum_depth_le {n : ℕ} (hn : 16 ^ 12 ≤ n) :
    (minimum n : ℝ) ≤ ((3 * P.stage : ℕ) / 4 : ℝ) * Real.logb 2 (n : ℝ) + (3 * P.stage : ℕ) :=
  P.certificate.minimum_bound hn

/-- **`limsup D(n)/log₂ n ≤ 3D/4`.** -/
theorem limsup_minimum_div_logb_le :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ ((3 * P.stage : ℕ) / 4 : ℝ) :=
  P.certificate.limsup_bound

end R1Point

end R1T
