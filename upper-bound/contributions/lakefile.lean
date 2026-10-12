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

