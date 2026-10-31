import D2RankAlignment
import D2Slope49Abstract

set_option maxHeartbeats 1000000

namespace Chvatal.D2Slope49Physical

open Chvatal.D2RankAlignment

/-- The source column `35*c` followed by a row permutation of slope 49 lands
at destination `d` exactly when its row has this residue. -/
def slope49RowAt (d c : Fin 64) : Fin 64 :=
  ⟨(17 * ((d.val + 64 - (35 * c.val) % 64) % 64)) % 64,
    Nat.mod_lt _ (by omega)⟩

theorem slope49_row_destination_iff_residue (c d : Fin 64) (row : Nat) :
    (35 * c.val + 49 * row) % 64 = d.val ↔
      row % 64 = (slope49RowAt d c).val := by
  dsimp [slope49RowAt]
  omega

theorem slope49_source_hits_eq_residue (height : Nat) (c d : Fin 64) :
    ((Finset.range height).filter fun row =>
      (35 * c.val + 49 * row) % 64 = d.val).card =
        residueHits64 height (slope49RowAt d c).val := by
  unfold residueHits64
  congr 1
  ext row
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨h.1, (slope49_row_destination_iff_residue c d row).mp h.2⟩
  · intro h
    exact ⟨h.1, (slope49_row_destination_iff_residue c d row).mpr h.2⟩

/-- In a 64-row band, each fixed row residue occurs at most once. -/
theorem residueHits64_eq_indicator_of_le_64 (height residue : Nat)
    (hr : residue < 64) (hh : height ≤ 64) :
    residueHits64 height residue = if residue < height then 1 else 0 := by
  rw [residueHits64_eq height residue hr]
  by_cases hfull : height = 64
  · subst height
    simp [hr]
  · have hsmall : height < 64 := by omega
    simp [Nat.div_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall]

/-- Physical output height after applying the slope-49 row permutation to
the columns indexed by their preceding slope-35 destinations. -/
def slope49PhysicalOutputHeight (inputHeight : Fin 64 → Nat) (d : Fin 64) : Nat :=
  ∑ c : Fin 64,
    ((Finset.range (inputHeight c)).filter fun row =>
      (35 * c.val + 49 * row) % 64 = d.val).card

theorem slope49PhysicalOutputHeight_eq_binary
    (inputHeight : Fin 64 → Nat) (hbound : ∀ c, inputHeight c ≤ 64)
    (d : Fin 64) :
    slope49PhysicalOutputHeight inputHeight d =
      ∑ c : Fin 64,
        if (slope49RowAt d c).val < inputHeight c then 1 else 0 := by
  unfold slope49PhysicalOutputHeight
  apply Finset.sum_congr rfl
  intro c _
  rw [slope49_source_hits_eq_residue]
  exact residueHits64_eq_indicator_of_le_64 (inputHeight c)
    (slope49RowAt d c).val (slope49RowAt d c).isLt (hbound c)

/-- The physical slope-49 row count is exactly the abstract cyclic profile
used by the finite dual certificates, whenever every source band has at most
64 occupied rows. -/
theorem slope49PhysicalOutputHeight_eq_abstract
    (inputHeight : Fin 64 → Nat) (hbound : ∀ c, inputHeight c ≤ 64)
    (d : Fin 64) :
    (slope49PhysicalOutputHeight inputHeight d : Int) =
      Chvatal.D2Slope49Abstract.output49Height
        (fun c => ⟨inputHeight c, Nat.lt_succ_of_le (hbound c)⟩) d := by
  rw [slope49PhysicalOutputHeight_eq_binary inputHeight hbound d]
  unfold Chvatal.D2Slope49Abstract.output49Height
  norm_cast

/-- A slope-35 output formed from 64 source columns, each of height at most
64, again has height at most 64. -/
theorem slope35PhysicalOutputHeight_le_64
    (inputHeight : Fin 64 → Nat) (hbound : ∀ c, inputHeight c ≤ 64)
    (d : Fin 64) :
    slope35PhysicalOutputHeight inputHeight d ≤ 64 := by
  rw [slope35PhysicalOutputHeight_eq]
  calc
    (∑ c : Fin 64,
      (inputHeight c / 64 +
        if (slope35RowAt d c).val < inputHeight c % 64 then 1 else 0))
      ≤ ∑ _c : Fin 64, 1 := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hfull : inputHeight c = 64
        · simp [hfull]
        · have hsmall : inputHeight c < 64 := by have := hbound c; omega
          simp [Nat.div_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall]
          split_ifs <;> omega
    _ = 64 := by simp

end Chvatal.D2Slope49Physical
