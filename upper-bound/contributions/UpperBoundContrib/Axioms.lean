import UpperBoundContrib.Candidate

/-! # Contribution trust-boundary guard

1. The statement is pinned: `candidate_bound` must have *exactly* the trusted type
   `UpperBoundContrib.BoundSpec UpperBoundContrib.claimed`, with `BoundSpec` from the fingerprinted
   `Spec.lean` (the `example` below fails to compile otherwise).
2. The proof may depend only on Lean's standard axioms. -/

example : UpperBoundContrib.BoundSpec UpperBoundContrib.claimed :=
  UpperBoundContrib.candidate_bound

/-- info: 'UpperBoundContrib.candidate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpperBoundContrib.candidate_bound

/-- info: 'UpperBoundContrib.BoundSpec.limsup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpperBoundContrib.BoundSpec.limsup_le
