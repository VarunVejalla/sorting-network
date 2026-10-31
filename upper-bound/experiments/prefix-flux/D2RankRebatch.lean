import D2RankAlignment

open scoped BigOperators

namespace Chvatal.D2RankAlignment

set_option maxHeartbeats 500000

/-- Regrouping signed rational cell errors cannot increase their total l1
mass. This version allows a refined cell to be split by output column before
the pieces are assigned to next-stage tile/column groups. -/
theorem grouped_rational_abs_sum_le_refined_abs_sum
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (group : I -> J) (error : I -> Rat) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun i : I => group i = j).sum error)) <=
      Finset.univ.sum fun i : I => abs (error i) := by
  calc
    _ <= Finset.univ.sum fun j : J =>
        (Finset.univ.filter fun i : I => group i = j).sum fun i =>
          abs (error i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs (fun i => error i)
        (Finset.univ.filter fun i : I => group i = j)
    _ = Finset.univ.sum fun i : I => abs (error i) := by
      rw [Finset.sum_fiberwise_of_maps_to (g := group)
        (fun i hi => Finset.mem_univ (group i))
        (fun i => abs (error i))]

/-- Regrouping a finite refinement into larger output cells cannot increase
the total l1 count error. This is the arithmetic step needed when one sender's
tile/port pieces are rebinned into the next sender's tiles, including pieces
cut at partial-tile offsets. -/
theorem grouped_countDistance_le_refined_countDistance
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (group : I → J) (actual ideal : I → ℕ) :
    (∑ j : J,
      countDistance
        (∑ i ∈ Finset.univ.filter (fun i : I => group i = j), actual i)
        (∑ i ∈ Finset.univ.filter (fun i : I => group i = j), ideal i)) ≤
      ∑ i : I, countDistance (actual i) (ideal i) := by
  calc
    _ ≤ ∑ j : J,
        ∑ i ∈ Finset.univ.filter (fun i : I => group i = j),
          countDistance (actual i) (ideal i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact countDistance_sum_le
        (Finset.univ.filter (fun i : I => group i = j)) actual ideal
    _ = ∑ i : I, countDistance (actual i) (ideal i) := by
      rw [Finset.sum_fiberwise_of_maps_to (g := group)
        (fun i hi => Finset.mem_univ (group i))
        (fun i => countDistance (actual i) (ideal i))]

/-- A uniform source-cell error bound becomes a per-receiver bound whenever
each receiver has at most `fiberCap` incoming cells. This is the pointwise
counterpart to the aggregate regrouping estimate above and is the form needed
for fixed-width terminal seam cleanup. -/
theorem grouped_countDistance_each_receiver_le_of_bounded_fiber
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (group : I -> J) (actual ideal : I -> Nat)
    (fiberCap cellError : Nat)
    (hcell : forall i, countDistance (actual i) (ideal i) <= cellError)
    (hfiber : forall j : J,
      (Finset.univ.filter fun i : I => group i = j).card <= fiberCap) :
    forall j : J,
      countDistance
        ((Finset.univ.filter (fun i : I => group i = j)).sum actual)
        ((Finset.univ.filter (fun i : I => group i = j)).sum ideal) <=
        fiberCap * cellError := by
  intro j
  let fiber := Finset.univ.filter fun i : I => group i = j
  calc
    countDistance (fiber.sum actual) (fiber.sum ideal) <=
        fiber.sum fun i => countDistance (actual i) (ideal i) :=
      countDistance_sum_le fiber actual ideal
    _ <= fiber.sum fun _ => cellError :=
      Finset.sum_le_sum fun i hi => hcell i
    _ = fiber.card * cellError := by simp [fiber]
    _ <= fiberCap * cellError :=
      Nat.mul_le_mul_right cellError (hfiber j)

/-- A complete stage transfer remains valid after its refined port cells are
regrouped into the next active senders' tile profiles. The parent mismatch is
paid once globally, and local core errors are paid once per refined cell. -/
theorem grouped_child_rank_error_le_parent_add_transfer
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (group : I → J) (actual reference ideal transfer : I → ℕ)
    (parentError : ℕ)
    (hTransferUpper : ∀ i, actual i ≤ reference i + transfer i)
    (hTransferLower : ∀ i, reference i ≤ actual i + transfer i)
    (hParent :
      (∑ i : I, countDistance (reference i) (ideal i)) ≤ parentError) :
    (∑ j : J,
      countDistance
        (∑ i ∈ Finset.univ.filter (fun i : I => group i = j), actual i)
        (∑ i ∈ Finset.univ.filter (fun i : I => group i = j), ideal i)) ≤
      parentError + ∑ i : I, transfer i := by
  calc
    _ ≤ ∑ i : I, countDistance (actual i) (ideal i) :=
      grouped_countDistance_le_refined_countDistance group actual ideal
    _ ≤ parentError + ∑ i : I, transfer i :=
      aggregate_child_count_error_le_parent_add_transfer
        actual reference ideal transfer parentError
        hTransferUpper hTransferLower hParent

end Chvatal.D2RankAlignment
