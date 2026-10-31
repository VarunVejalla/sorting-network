import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-- A valid bottom-rise from eight full native child subtrees fills the parent
root to its native size. This is the exact gate transfer used at scheduled
bottom-rise frontiers. -/
theorem d2FlowStage_botRise_root_full_of_full_children
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {scale h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hactive : active i = true) (hrole : role i = .botRise)
    (hcover : G ≤ d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit (children j)))
    (hchildren : ∀ j, d2FlowTreeRootDeficit (children j) = scale * 8 ^ h) :
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = scale * 8 ^ (h + 1) := by
  rw [d2FlowStage_botRise_root_saturates children hactive hrole hcover]
  unfold d2FlowTotal
  calc
    (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit (children j)) =
      Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hchildren j
    _ = 8 * (scale * 8 ^ h) := by simp
    _ = scale * 8 ^ (h + 1) := by rw [Nat.pow_succ]; ring

end Chvatal.D2Reserve
