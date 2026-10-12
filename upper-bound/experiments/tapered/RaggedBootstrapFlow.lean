import RaggedBootstrapGeometry
import RaggedFlowContract
import Mathlib.Tactic

namespace Tapered945

/-- Every address-dependent bootstrap slot receives at least one row. -/
theorem bootstrap_slot_rows_pos (x j : Nat) : 0 < bootstrapSlotRows x j := by
  by_cases hx : isEndAddress x <;> by_cases hj : isEndAddress j
  · norm_num [bootstrapSlotRows, isEndAddress, hx, hj]
  · norm_num [bootstrapSlotRows, isEndAddress, hx, hj]
  · norm_num [bootstrapSlotRows, isEndAddress, hx, hj]
  · norm_num [bootstrapSlotRows, isEndAddress, hx, hj]

/-- The selected bootstrap start fringe is positive at every address. -/
theorem bootstrap_fringe_rows_pos (x : Nat) : 0 < bootstrapFringeRows x := by
  by_cases hx : isEndAddress x
  · norm_num [bootstrapFringeRows, bootstrapUpRows, isEndAddress, hx]
  · norm_num [bootstrapFringeRows, bootstrapUpRows, isEndAddress, hx]

/-- The variable-width stage-one allocation is a ragged separator profile.
The starting and ending fringes both have the chosen address-dependent size;
the slot widths are exactly the row counts from the bootstrap geometry. -/
def bootstrapRaggedProfile (x : Nat) : RaggedFlowContract bootstrapRows where
  start := bootstrapFringeRows x
  rightFringe := bootstrapFringeRows x
  width := bootstrapSlotRows x
  widths_pos := by
    intro j hj
    exact bootstrap_slot_rows_pos x j
  conservation := by
    have hsplit := bootstrap_row_split x
    have hfringe := bootstrap_fringe_rows_exact x
    have hsum : (∑ j ∈ Finset.range 64, bootstrapSlotRows x j) =
        ∑ j : Fin 64, bootstrapSlotRows x j.val := by
      rw [← Fin.sum_univ_eq_sum_range]
    change bootstrapFringeRows x + raggedPrefixRows (bootstrapSlotRows x) 64 +
      bootstrapFringeRows x = bootstrapRows
    rw [raggedPrefixRows, hsum]
    omega
  cut_pos := by
    intro j hj
    have hs := bootstrap_fringe_rows_pos x
    change 1 ≤ bootstrapFringeRows x + raggedPrefixRows (bootstrapSlotRows x) j
    omega
  prefix_bound := by
    intro j hj
    have hprefix : (∑ i ∈ Finset.range j, bootstrapSlotRows x i) ≤
        ∑ i ∈ Finset.range 64, bootstrapSlotRows x i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      intro i hi hnot
      exact Nat.zero_le _
    have hsplit := bootstrap_row_split x
    have hfringe := bootstrap_fringe_rows_exact x
    have hsum : (∑ i ∈ Finset.range 64, bootstrapSlotRows x i) =
        ∑ i : Fin 64, bootstrapSlotRows x i.val := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [hsum] at hprefix
    change bootstrapFringeRows x + raggedPrefixRows (bootstrapSlotRows x) j ≤
      bootstrapRows - bootstrapFringeRows x
    rw [raggedPrefixRows]
    rw [← hsum] at hsplit
    omega

/-- The existing average separator geometry and the address-dependent ragged
profile coexist at level one. This records data compatibility only; it makes
no assertion about whether a comparator network satisfies every ragged cut. -/
theorem bootstrap_geometry_with_ragged_profile (d x : Nat) (hd : 14 ≤ d) :
    Nonempty (Chvatal.NodeGeom (seedRootDown d)
      (bootstrapUpRows x * bootstrapColumns d)
      (bootstrapAverageDownRows x * bootstrapColumns d)) ∧
    Nonempty (RaggedFlowContract bootstrapRows) := by
  exact ⟨bootstrap_level_one_node_geom d x hd, ⟨bootstrapRaggedProfile x⟩⟩

/-- The row-level first-stage allocation scales to an exact integer-wire
split of a level-one bag. The rational signed-flow targets agree exactly with
the chosen up-flow and each address-dependent child block. -/
theorem bootstrap_integer_split_exact (d x : Nat) (hd : 14 ≤ d) :
    Even (bootstrapUpRows x * bootstrapColumns d) ∧
    bootstrapUpRows x * bootstrapColumns d ≤ seedRootDown d ∧
    (∑ j : Fin 64, bootstrapSlotRows x j.val * bootstrapColumns d) =
      seedRootDown d - bootstrapUpRows x * bootstrapColumns d ∧
    ((bootstrapUpRows x * bootstrapColumns d : Nat) : Rat) =
      (upFlow - firstAddressDebt x + 1 / cap) * seedRootDown d ∧
    (∀ j : Fin 64,
      ((bootstrapSlotRows x j.val * bootstrapColumns d : Nat) : Rat) =
        (bootstrapDownCoeff j.val + firstAddressDebt x / 64) *
          seedRootDown d) := by
  let parent := seedRootDown d
  let up := bootstrapUpRows x * bootstrapColumns d
  let blocks : Fin 64 → Nat := fun j =>
    bootstrapSlotRows x j.val * bootstrapColumns d
  have hrows := bootstrap_row_split x
  have hfactor := bootstrap_input_factorization d hd
  have hsum : (∑ j : Fin 64, blocks j) =
      (∑ j : Fin 64, bootstrapSlotRows x j.val) * bootstrapColumns d := by
    simp only [blocks]
    rw [Finset.sum_mul]
  have htotal : up + (∑ j : Fin 64, blocks j) = parent := by
    dsimp [up, parent]
    rw [hsum, ← Nat.add_mul, ← hrows, hfactor]
  have hup_even : Even up := by
    dsimp [up]
    obtain ⟨k, hk⟩ := bootstrap_up_rows_even x
    refine ⟨k * bootstrapColumns d, ?_⟩
    rw [hk]
    ring
  have hup_le : up ≤ parent := by
    dsimp [up, parent]
    have hu : bootstrapUpRows x ≤ bootstrapRows := by omega
    rw [hfactor]
    exact Nat.mul_le_mul_right _ hu
  have hblocks : (∑ j : Fin 64, blocks j) = parent - up := by
    omega
  have hup_exact : ((up : Nat) : Rat) =
      (upFlow - firstAddressDebt x + 1 / cap) * parent := by
    dsimp [up, parent]
    rw [Nat.cast_mul, bootstrap_up_rows_exact, hfactor]
    push_cast
    ring
  have hblock_exact : ∀ j : Fin 64,
      ((blocks j : Nat) : Rat) =
        (bootstrapDownCoeff j.val + firstAddressDebt x / 64) * parent := by
    intro j
    dsimp [blocks, parent]
    rw [Nat.cast_mul, bootstrap_slot_rows_exact, hfactor]
    push_cast
    ring
  exact ⟨hup_even, hup_le, hblocks, hup_exact, hblock_exact⟩

end Tapered945
