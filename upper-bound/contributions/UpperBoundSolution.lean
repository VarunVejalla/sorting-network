import UpperBoundContrib.Candidate

/-! # Root-level solution of the comparator Challenge (draft)

The comparator tool matches the *type* of `upper_bound_certified` here against `challenge/Challenge.lean`
(Mathlib-only definitions), so the statement is written with the literal constant and root-level names.
`scripts/make-limsup-challenge C` regenerates both files for another constant. Not part of the default
build; build with `lake build UpperBoundSolution`. -/

theorem upper_bound_certified : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ net : ComparatorNetwork n, ComparatorNetwork.Sorts.{0} net ∧
      (net.depth : ℝ) ≤ ((1419 : ℝ) + ε) * Real.logb 2 (n : ℝ) := by
  have h := UpperBoundContrib.candidate_bound.netSpec
  unfold UpperBoundContrib.NetSpec UpperBoundContrib.claimed at h
  exact h
