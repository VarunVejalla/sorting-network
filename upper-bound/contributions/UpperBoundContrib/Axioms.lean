import UpperBoundContrib.Candidate

/-! The contribution trust-boundary guard. If the candidate introduces an
additional axiom dependency, this expected-message check fails. -/

/-- info: 'UpperBoundContrib.candidate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpperBoundContrib.candidate_bound
