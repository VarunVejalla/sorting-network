import AKS.Bounds.Chvatal1830Final

/-! Replace this baseline with a closed proof of the canonical limsup statement.
The declaration name and type shape are the contribution check's entry point. -/

namespace UpperBoundContrib

theorem candidate_bound :
    Filter.limsup
      (fun n : ℕ => (SortingDepth.minimum n : ℝ) / Real.logb 2 n)
      Filter.atTop ≤ (1419 : ℝ) := by
  exact SortingDepth.limsup_minimum_div_logb_le_1419

end UpperBoundContrib
