import AKS.Bounds.Sub800Final
import UpperBoundContrib.Spec
import UpperBoundContrib.Best

/-! # Contribution entry point

Replace the baseline below with a closed proof that the canonical `D(n)` satisfies
`UpperBoundContrib.BoundSpec claimed` for your claimed constant. Keep the names `claimed` and
`candidate_bound` and this module path: the CI guards (`UpperBoundContrib.Axioms`,
`UpperBoundContrib.Improvement`) look them up. The statement is pinned by `Axioms.lean`
(`example : UpperBoundContrib.BoundSpec UpperBoundContrib.claimed := UpperBoundContrib.candidate_bound`),
so the type cannot be changed. See `README.md`. -/

namespace UpperBoundContrib

/-- The constant this contribution claims. -/
def claimed : ℝ := 789.75

theorem candidate_bound : BoundSpec claimed := currentBest_spec

end UpperBoundContrib
