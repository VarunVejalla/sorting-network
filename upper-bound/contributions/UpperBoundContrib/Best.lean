import UpperBoundContrib.Spec
import AKS.Bounds.Chvatal1830Final

/-! # The currently accepted best constant

Trusted record (fingerprinted by CI; update it only when `upper-bound/best` is promoted, together with
`upper-bound/STATUS.json`). `currentBest_spec` re-derives the headline of `upper-bound/best` in the
trusted `BoundSpec` form. -/

namespace UpperBoundContrib

/-- The accepted best coefficient of the checked package `upper-bound/best`. -/
def currentBest : ℝ := 1419

theorem currentBest_spec : BoundSpec currentBest := by
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop (64 ^ 7)] with n hn
  have hlog : (0 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact Real.logb_nonneg (by norm_num) hn1
  have h := SortingDepth.minimum_depth_le_1419_logb hn
  show (SortingDepth.minimum n : ℝ) ≤ (1419 + ε) * Real.logb 2 (n : ℝ)
  nlinarith [mul_nonneg hε.le hlog]

end UpperBoundContrib
