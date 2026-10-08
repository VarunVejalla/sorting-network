import AKS.Bounds.Chvatal1830Batcher
import AKS.Chvatal.RealSorter

/-! # Unconditional `limsup D(n)/log₂ n ≤ 1830`

The Chvátal DCS-TR-294 sorting network (`Chvatal.chvatal_sorter_exists`) discharges the
`Limsup1830Residual` obligation, so the limsup bound holds with no hypotheses. -/

namespace SortingDepth

open Chvatal Filter

theorem limsup1830Residual_holds : Limsup1830Residual := by
  intro d hd
  exact chvatal_sorter_exists (by
    have : batcherFitsTotalDepthMax = 603 := rfl
    omega)

/-- **`limsup D(n)/log₂ n ≤ 1830`**, unconditionally. -/
theorem limsup_minimum_div_logb_le_1830 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) :=
  limsup_minimum_div_logb_le_1830_of_batcher_and_residual limsup1830Residual_holds

end SortingDepth
