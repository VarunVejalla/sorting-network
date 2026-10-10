import Lake
open Lake DSL

package limit_existence where
  packagesDir := "../../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]

require sorting_depth_lower_best from "../../lower-bound/best"

@[default_target]
lean_lib LimitAKS where
  globs := #[.one `AKS.Bounds.AmplificationAxioms, .one `AKS.Bounds.ConditionalLimit, .one `AKS.Bounds.DyadicLimit, .one `AKS.Sort.RepairBarrier, .one `AKS.Sort.RepairInterface]
