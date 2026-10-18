import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Tapered945

/-- Sum of slot capacities, minus slotwise bad-key allowances, is a lower
bound on the intended native mass in descendant storage. -/
theorem descendant_native_mass_lower_of_slot_errors
    {Key : Type*} [DecidableEq Key]
    (J : Finset (Fin 64)) (I S : Finset Key)
    (slots native : Fin 64 → Finset Key)
    (width err : Fin 64 → Nat)
    (hcover : J.biUnion native = I)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (native i) (native j))
    (hslot : ∀ j, slots j ⊆ S)
    (hwidth : ∀ j, (slots j).card = width j)
    (hbad : ∀ j, ((slots j).filter (fun x => x ∉ native j)).card ≤ err j) :
    (∑ j ∈ J, (width j - err j)) ≤ (S ∩ I).card := by
  classical
  let good : Fin 64 → Finset Key := fun j => slots j ∩ native j
  have hgood : ∀ j, width j - err j ≤ (good j).card := by
    intro j
    have hsplit := Finset.card_filter_add_card_filter_not (s := slots j)
      (fun x => x ∈ native j)
    have hgoodCard : (good j).card +
        ((slots j).filter (fun x => x ∉ native j)).card = (slots j).card := by
      simpa [good, Finset.filter_filter] using hsplit
    have hbad' := hbad j
    have hwidthBound : width j ≤ (good j).card + err j := by
      calc
        width j = (good j).card +
            ((slots j).filter (fun x => x ∉ native j)).card := by
              rw [hwidth j] at hgoodCard
              exact hgoodCard.symm
        _ ≤ (good j).card + err j := Nat.add_le_add_left hbad' _
    exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_comm] using hwidthBound)
  have hgoodSub : J.biUnion good ⊆ S ∩ I := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
    have hxs : x ∈ S := hslot j (Finset.mem_inter.mp hxj).1
    have hxnative : x ∈ native j := (Finset.mem_inter.mp hxj).2
    have hxi : x ∈ I := by
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨j, hj, hxnative⟩
    exact Finset.mem_inter.mpr ⟨hxs, hxi⟩
  have hgoodDisj : (J : Set (Fin 64)).PairwiseDisjoint good := by
    intro i hi j hj hij
    apply Finset.disjoint_of_subset_left Finset.inter_subset_right
    apply Finset.disjoint_of_subset_right Finset.inter_subset_right
    exact hdisj i hi j hj hij
  have hcardGood :
      (J.biUnion good).card = ∑ j ∈ J, (good j).card :=
        Finset.card_biUnion hgoodDisj
  have hsum :
      (∑ j ∈ J, (width j - err j)) ≤
        ∑ j ∈ J, (good j).card :=
    Finset.sum_le_sum (s := J) (f := fun j => width j - err j)
      (g := fun j => (good j).card) (fun j hj => hgood j)
  calc
    (∑ j ∈ J, (width j - err j)) ≤ (J.biUnion good).card := by
          rw [hcardGood]
          exact hsum
    _ ≤ (S ∩ I).card := Finset.card_le_card hgoodSub

/-- Bound native keys spilled into designated outside slots. If the interval
is disjoint from each such slot's intended native region, then every leaked
key is charged to that slot's error allowance. `ambient` accounts for older
outside storage or frontier ports not represented by these slots. -/
theorem outside_native_mass_upper_of_slot_errors
    {Key : Type*} [DecidableEq Key]
    (J : Finset (Fin 64)) (I Outside ambient : Finset Key)
    (slots native : Fin 64 → Finset Key) (err : Fin 64 → Nat) (A : Nat)
    (hcover : Outside ⊆ J.biUnion slots ∪ ambient)
    (hdisj : ∀ j ∈ J, Disjoint (native j) I)
    (hbad : ∀ j ∈ J,
      ((slots j).filter (fun x => x ∉ native j)).card ≤ err j)
    (hambient : (ambient ∩ I).card ≤ A) :
    (Outside ∩ I).card ≤ A + ∑ j ∈ J, err j := by
  classical
  let leaks : Fin 64 → Finset Key := fun j => slots j ∩ I
  have hleakSub : ∀ j ∈ J,
      leaks j ⊆ (slots j).filter (fun x => x ∉ native j) := by
    intro j hj x hx
    have hxSlot : x ∈ slots j := (Finset.mem_inter.mp hx).1
    have hxI : x ∈ I := (Finset.mem_inter.mp hx).2
    have hxNotNative : x ∉ native j := by
      intro hxNative
      exact Finset.disjoint_left.mp (hdisj j hj) hxNative hxI
    exact Finset.mem_filter.mpr ⟨hxSlot, hxNotNative⟩
  have hleakCard : ∀ j ∈ J, (leaks j).card ≤ err j := by
    intro j hj
    exact (Finset.card_le_card (hleakSub j hj)).trans (hbad j hj)
  have hsub : Outside ∩ I ⊆ (J.biUnion leaks) ∪ (ambient ∩ I) := by
    intro x hx
    have hxOutside := (Finset.mem_inter.mp hx).1
    have hxI := (Finset.mem_inter.mp hx).2
    rcases Finset.mem_union.mp (hcover hxOutside) with hslots | hambient
    · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hslots
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_inter.mpr ⟨hxj, hxI⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hambient, hxI⟩)
  have hcardSub : (Outside ∩ I).card ≤ (J.biUnion leaks).card + (ambient ∩ I).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardLeaks : (J.biUnion leaks).card ≤ ∑ j ∈ J, (leaks j).card :=
    Finset.card_biUnion_le
  have hsumLeaks : (J.biUnion leaks).card ≤ ∑ j ∈ J, err j :=
    hcardLeaks.trans (Finset.sum_le_sum fun j hj => hleakCard j hj)
  omega

end Tapered945
