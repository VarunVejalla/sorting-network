import R1Nets

/-! # Headline: `limsup D(n)/log₂ n ≤ 789.75 ≤ 800`

* `R1T.minimum_depth_le`: for `n ≥ 16^12`, `D(n) ≤ 789.75 · log₂ n + 3159`.
* `R1T.limsup_minimum_div_logb_le_78975`: `limsup D(n)/log₂ n ≤ 789.75`.
* `R1T.limsup_minimum_div_logb_le_800`: `limsup D(n)/log₂ n ≤ 800`. -/

namespace R1T

open SortingDepth Filter

/-- The certificate for `C = 789.75`. -/
noncomputable def r1Certificate : UpperBoundCertificate (3159 / 4) 3159 where
  threshold := 16 ^ 12
  network := fun n hn => by
    have hn1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
    set d := Nat.clog 16 n
    have hd12 : 12 ≤ d := by
      have := Nat.clog_mono_right 16 hn
      rwa [Nat.clog_pow 16 12 (by norm_num)] at this
    have hle : n ≤ 16 ^ d := Nat.le_pow_clog (by norm_num) n
    obtain ⟨T, hs, hdep⟩ := r1_sorter hd12
    refine ⟨T.restrictWires n hle, restrictWires_sorts T n hle (fun v ↦ hs (α := Bool) v), ?_⟩
    have hlt : 16 ^ (d - 1) < n := by
      have := Nat.pow_pred_clog_lt_self (b := 16) (by norm_num) hn1
      rwa [Nat.pred_eq_sub_one] at this
    have hdn : (T.restrictWires n hle).depth ≤ 3159 * d := by
      have := restrictWires_depth_le T n hle
      omega
    have hdR : ((T.restrictWires n hle).depth : ℝ) ≤ 3159 * d := by exact_mod_cast hdn
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
    linarith

/-- **Pointwise bound.** For every `n ≥ 16^12`, `D(n) ≤ 789.75 · log₂ n + 3159`. -/
theorem minimum_depth_le {n : ℕ} (hn : 16 ^ 12 ≤ n) :
    (minimum n : ℝ) ≤ 3159 / 4 * Real.logb 2 (n : ℝ) + 3159 :=
  r1Certificate.minimum_bound hn

/-- **`limsup D(n)/log₂ n ≤ 789.75`.** -/
theorem limsup_minimum_div_logb_le_78975 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (3159 / 4 : ℝ) :=
  r1Certificate.limsup_bound

/-- **`limsup D(n)/log₂ n ≤ 800`.** -/
theorem limsup_minimum_div_logb_le_800 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (800 : ℝ) :=
  limsup_minimum_div_logb_le_78975.trans (by norm_num)

end R1T
