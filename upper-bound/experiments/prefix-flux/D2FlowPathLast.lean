import D2TopDescHistory

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false

/-- Append a final port to a root-first path. -/
def d2FlowPathSnoc : {n : Nat} → D2FlowPath n → Fin 8 → D2FlowPath (n + 1)
  | 0, .nil, j => .cons j .nil
  | n + 1, .cons j tail, k => .cons j (d2FlowPathSnoc tail k)

/-- Every positive-length root-first path has a unique last-edge
decomposition. -/
theorem d2FlowPath_exists_snoc {n : Nat} (path : D2FlowPath (n + 1)) :
    ∃ parent : D2FlowPath n, ∃ port : Fin 8,
      d2FlowPathSnoc parent port = path := by
  induction n with
  | zero =>
      cases path with
      | cons port tail =>
          cases tail with
          | nil => exact ⟨.nil, port, rfl⟩
  | succ n ih =>
      cases path with
      | cons first tail =>
          cases htail : tail with
          | cons second rest =>
              obtain ⟨parent, port, hparent⟩ := ih (.cons second rest)
              exact ⟨.cons first parent, port, by
                simp [d2FlowPathSnoc, hparent]⟩

end Chvatal.D2Reserve
