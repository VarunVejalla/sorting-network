import D2FlowPathLast

namespace Chvatal.D2Reserve

/-- A path whose length equals the tree height always lands at a leaf. -/
theorem d2FlowTreeAtPath_fullDepth_leaf {n : Nat}
    (tree : D2FlowTree (0 + n)) (path : D2FlowPath n) :
    ∃ G low high, d2FlowTreeAtPath (h := 0) n tree path = D2FlowTree.leaf G low high := by
  induction path with
  | nil =>
      cases tree with
      | leaf G low high => exact ⟨G, low, high, rfl⟩
  | @cons n port tail ih =>
      cases tree with
      | node G low high children =>
          exact ih (children port)

/-- The affine-core predicate has no terminal-node obligations, so its
full-depth path case is automatic. -/
theorem d2FlowStageAffineCoreInputs_atFullDepth
    {active : Nat → Bool} {role : Nat → D2Role} {cap : Nat → Nat}
    {n : Nat} (tree : D2FlowTree (0 + n)) (path : D2FlowPath n) :
    d2FlowStageAffineCoreInputs active role cap n
      (d2FlowTreeAtPath (h := 0) n tree path) := by
  obtain ⟨G, low, high, hleaf⟩ := d2FlowTreeAtPath_fullDepth_leaf tree path
  simp [hleaf, d2FlowStageAffineCoreInputs]

end Chvatal.D2Reserve
