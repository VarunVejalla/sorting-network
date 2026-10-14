import RaggedWireOwnership
import RaggedFlowContract
import Mathlib.Tactic

namespace Tapered945

/-- If the physical up-fringe and each physical child slot are scaled from a
row profile by the same column count, every physical slot boundary is exactly
the corresponding row-aligned pack boundary. -/
theorem ragged_slotLo_eq_profile_cut {N m n : Nat}
    {s : Finset (Fin N)} (split : RaggedWireSplit s)
    (profile : RaggedFlowContract m)
    (hup : split.up / 2 = profile.start * n)
    (hwidth : ∀ j, j < 64 → split.widths j = profile.width j * n)
    (j : Nat) (hj : j ≤ 64) :
    slotLo split.up split.widths j =
      (profile.start + raggedPrefixRows profile.width j) * n := by
  have hpref : slotPrefix split.widths j = raggedPrefixRows profile.width j * n := by
    unfold slotPrefix raggedPrefixRows
    calc
      (∑ i ∈ Finset.range j, split.widths i) =
          ∑ i ∈ Finset.range j, profile.width i * n := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hwidth i (by
          have := Finset.mem_range.mp hi
          omega)]
      _ = (∑ i ∈ Finset.range j, profile.width i) * n := by
        rw [Finset.sum_mul]
  unfold slotLo
  rw [hup, hpref]
  exact (Nat.add_mul _ _ _).symm

/-- The exclusive upper boundary of physical child slot `j` is the next
row-aligned pack boundary. -/
theorem ragged_slotHi_eq_profile_cut {N m n : Nat}
    {s : Finset (Fin N)} (split : RaggedWireSplit s)
    (profile : RaggedFlowContract m)
    (hup : split.up / 2 = profile.start * n)
    (hwidth : ∀ j, j < 64 → split.widths j = profile.width j * n)
    (j : Nat) (hj : j < 64) :
    slotHi split.up split.widths j =
      (profile.start + raggedPrefixRows profile.width (j + 1)) * n := by
  unfold slotHi
  rw [ragged_slotLo_eq_profile_cut split profile hup hwidth j (by omega),
    hwidth j hj]
  simp [raggedPrefixRows, Finset.sum_range_succ, Nat.add_mul, Nat.add_assoc]

end Tapered945
