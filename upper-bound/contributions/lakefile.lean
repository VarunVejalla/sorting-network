import Lake
open Lake DSL

package upperBoundContributions where
  packagesDir := "../../.lake/packages"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, true⟩
  ]

require chvatal1830 from "../best"

@[default_target]
lean_lib UpperBoundContrib where
  globs := #[.submodules `UpperBoundContrib]


/-- Not part of the default build: compiles only when the candidate strictly improves on `currentBest`. -/
lean_lib UpperBoundGate where
  globs := #[.submodules `UpperBoundGate]

/-- Not part of the default build: root-level theorem matched against `challenge/Challenge.lean` by comparator. -/
lean_lib UpperBoundSolution where
  roots := #[`UpperBoundSolution]
