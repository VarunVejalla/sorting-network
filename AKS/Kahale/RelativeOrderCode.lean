module

public import Mathlib.Data.Finset.Sort

/-! # Reconstructing ranks from their set and relative order

This is a combinatorial foundation for conditional entropy identities.
No entropy or improved sorting-depth inequality is assumed here.
-/

@[expose] public section

namespace Kahale

def coordinateRankSet {ι α : Type*} [Fintype ι] [DecidableEq α]
    (v : ι → α) : Finset α := Finset.univ.image v

def relativeOrderCode {ι α : Type*} [Fintype ι] [LinearOrder α]
    (v : ι → α) : ι → Fin (coordinateRankSet v).card := fun i ↦
  ((coordinateRankSet v).orderIsoOfFin rfl).symm
    ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

theorem reconstruct_relativeOrderCode {ι α : Type*} [Fintype ι] [LinearOrder α]
    (v : ι → α) (i : ι) :
    ((coordinateRankSet v).orderIsoOfFin rfl (relativeOrderCode v i)).val = v i := by
  exact congrArg Subtype.val
    (((coordinateRankSet v).orderIsoOfFin rfl).apply_symm_apply _)

def insertionCode {α : Type*} [LinearOrder α] (rest : Finset α) (a : α) :
    Fin (insert a rest).card :=
  ((insert a rest).orderIsoOfFin rfl).symm ⟨a, Finset.mem_insert_self a rest⟩

theorem reconstruct_insertionCode {α : Type*} [LinearOrder α]
    (rest : Finset α) (a : α) :
    ((insert a rest).orderIsoOfFin rfl (insertionCode rest a)).val = a := by
  exact congrArg Subtype.val (((insert a rest).orderIsoOfFin rfl).apply_symm_apply _)

theorem restRankSet_of_insertion {α : Type*} [LinearOrder α]
    (rest : Finset α) (a : α) (ha : a ∉ rest) : (insert a rest).erase a = rest := by
  simp [ha]

end Kahale
