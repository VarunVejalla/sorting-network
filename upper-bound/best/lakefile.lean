import Lake
open Lake DSL

package «chvatal1830» where
  -- reuse the Mathlib checkout (and its build) of the enclosing repository
  packagesDir := "../../.lake/packages"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, false⟩,
    ⟨`linter.unusedSimpArgs, false⟩,
    ⟨`linter.unusedVariables, false⟩,
    ⟨`linter.unnecessarySimpa, false⟩,
    ⟨`linter.unusedTactic, false⟩,
    ⟨`linter.unreachableTactic, false⟩,
    ⟨`weak.linter.unnecessarySeqFocus, false⟩,
    ⟨`linter.deprecated, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib «AKS» where
  globs := #[.submodules `AKS]
