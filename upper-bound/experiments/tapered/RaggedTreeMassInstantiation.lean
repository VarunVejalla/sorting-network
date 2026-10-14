import NativeChildrenPartition
import RaggedSlotMass

namespace Tapered945

open Chvatal

variable {d : Nat}

/-- Slot-error accounting specialized to the actual 64-ary native children
of a bag. The native partition and disjointness obligations are supplied by
`NativeChildrenPartition`; only scheduler-specific slot hypotheses remain. -/
theorem native_child_mass_lower_of_slot_errors
    (q : KBag 64 d) (hq : q.l < d)
    (S : Finset (Fin (64 ^ d)))
    (slots : Fin 64 → Finset (Fin (64 ^ d)))
    (width err : Fin 64 → Nat)
    (hslot : ∀ j, slots j ⊆ S)
    (hwidth : ∀ j, (slots j).card = width j)
    (hbad : ∀ j,
      ((slots j).filter (fun κ => κ ∉ nativeKeys (q.child j.val j.isLt hq))).card
        ≤ err j) :
    (∑ j : Fin 64, (width j - err j)) ≤ (S ∩ nativeKeys q).card := by
  apply descendant_native_mass_lower_of_slot_errors
    (Finset.univ : Finset (Fin 64)) (nativeKeys q) S slots
    (fun j => nativeKeys (q.child j.val j.isLt hq)) width err
  · exact native_children_cover q hq
  · intro i hi j hj hij
    exact native_children_disjoint q hq hij
  · exact hslot
  · exact hwidth
  · exact hbad

end Tapered945
