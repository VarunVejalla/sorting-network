import AKS.Bounds.Minimum
import AKS.Sub800.R1At78975

/-! # The 789.75 bound (design P, one round of fringe separation per stage)

* `SortingDepth.minimum_depth_le_78975_logb`: for every `n ≥ 16^12`,
  `D(n) ≤ 789.75 · log₂ n + 3159`.
* `SortingDepth.limsup_minimum_div_logb_le_78975`: `limsup D(n)/log₂ n ≤ 789.75`.
* `SortingDepth.limsup_minimum_div_logb_le_800`: `limsup D(n)/log₂ n ≤ 800`.

The witness on `16^d` wires (`d ≥ 12`) is `R1T.r1_sorter` (`AKS/Sub800/R1Nets.lean`) at the point
`R1T.point78975` (`AKS/Sub800/R1At78975.lean`), of depth `2709 + 1053 (3d − 15) + 136 = 3159 d − 12950`,
restricted to `n` wires with `d = ⌈log₁₆ n⌉` (`R1T.R1Point.certificate`, `AKS/Sub800/R1Main.lean`). The paper proof is `notes/sub800/R1-PROOF.md`. -/

namespace SortingDepth

open Filter

/-- **Pointwise bound.** For every `n ≥ 16^12`, `D(n) ≤ 789.75 · log₂ n + 3159`. -/
theorem minimum_depth_le_78975_logb {n : ℕ} (hn : 16 ^ 12 ≤ n) :
    (minimum n : ℝ) ≤ 3159 / 4 * Real.logb 2 (n : ℝ) + 3159 :=
  R1T.minimum_depth_le hn

/-- **`limsup D(n)/log₂ n ≤ 789.75`.** -/
theorem limsup_minimum_div_logb_le_78975 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (3159 / 4 : ℝ) :=
  R1T.limsup_minimum_div_logb_le_78975

/-- **`limsup D(n)/log₂ n ≤ 800`.** -/
theorem limsup_minimum_div_logb_le_800 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (800 : ℝ) :=
  R1T.limsup_minimum_div_logb_le_800

end SortingDepth
