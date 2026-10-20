import UpperBoundContrib.Spec
import AKS.Bounds.Sub800Final

/-! # The currently accepted best constant

Trusted record (fingerprinted by CI; update it only when `upper-bound/best` is promoted, together with
`upper-bound/STATUS.json`). `currentBest_spec` re-derives the headline of `upper-bound/best` in the
trusted `BoundSpec` form. -/

namespace UpperBoundContrib

open Filter

/-- The accepted best coefficient of the checked package `upper-bound/best`. -/
def currentBest : ℝ := 789.75

theorem currentBest_spec : BoundSpec currentBest := by
  intro ε hε
  have hlog_atTop : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (16 ^ 12),
    hlog_atTop.eventually (eventually_gt_atTop (3159 / ε))] with n hn hk
  have h := SortingDepth.minimum_depth_le_78975_logb hn
  have hK : 3159 < ε * Real.logb 2 (n : ℝ) := by
    have h' := (div_lt_iff₀ hε).1 hk
    linarith
  show (SortingDepth.minimum n : ℝ) ≤ (789.75 + ε) * Real.logb 2 (n : ℝ)
  norm_num at h ⊢
  nlinarith

end UpperBoundContrib
