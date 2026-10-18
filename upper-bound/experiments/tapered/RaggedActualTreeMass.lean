import RaggedTreeMassInstantiation
import RaggedStageSlotBridge
import RaggedRankRecurrence
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Actual global keys emitted by parent `q` into child slot `j` at stage `t`.
This uses the physical, input-independent partition of the parent's register. -/
noncomputable def raggedStageDownSlotKeys {d : Nat}
    (P : Nat → RaggedWirePartition d)
    (splits : ∀ t b, RaggedWireSplit ((P t).sets b))
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (q : KBag 64 d) (j : Fin 64) :
    Finset (Fin (64 ^ d)) :=
  (raggedDownSet ((P t).sets q) (splits t q).up (splits t q).widths j.val).image
    (raggedX P nets v (t + 1))

/-- A child is a strict descendant bag of its parent. -/
theorem child_mem_strictSubtreeBags {d : Nat} (q : KBag 64 d)
    (hq : q.l < d) (j : Fin 64) :
    q.child j.val j.isLt hq ∈ strictSubtreeBags d q := by
  let c := q.child j.val j.isLt hq
  have hdesc : c ∈ descendants 64 d (by norm_num) q 1 := by
    rw [mem_descendants]
    constructor
    · dsimp [c, KBag.child]
    · dsimp [c, KBag.child]
      rw [Nat.mul_add_div (by norm_num : 0 < 64), Nat.div_eq_of_lt j.isLt]
      simp
  have hsub : c ∈ subtreeBags 64 d (by norm_num) q := by
    unfold subtreeBags
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_range.mpr ?_, hdesc⟩
    have hle : 1 ≤ d - q.l := by omega
    omega
  unfold strictSubtreeBags
  exact Finset.mem_filter.mpr ⟨hsub, by dsimp [c, KBag.child]; omega⟩

/-- After the scheduled route, all keys in the parent down-slot are owned by
the corresponding child, including children at the terminal level. -/
theorem raggedStageDownSlotKeys_subset_strictSubtree
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (splits : ∀ t b, RaggedWireSplit ((P t).sets b))
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (q : KBag 64 d)
    (hq : q.l < d) (j : Fin 64)
    (hstep : P (t + 1) = (P t).route (splits t) raggedTreeDestination) :
    raggedStageDownSlotKeys P splits nets v t q j ⊆
      raggedStrictSubtreeKeys P nets v (t + 1) q := by
  let c := q.child j.val j.isLt hq
  have hc : 1 ≤ c.l := by dsimp [c, KBag.child]; omega
  have hmod : c.x % 64 = j.val := by
    dsimp [c, KBag.child]
    simp [Nat.add_mod]
  have hchild := ragged_stage_downslot_keys_subset_child
    P splits nets v t c hc hstep
  have hparent : c.parent (by norm_num) = q := by
    dsimp [c]
    exact KBag.child_parent q j.val j.isLt hq (by norm_num)
  rw [hparent, hmod] at hchild
  intro key hk
  unfold raggedStageDownSlotKeys at hk
  change key ∈ (raggedDownSet ((P t).sets q) (splits t q).up
      (splits t q).widths j.val).image (raggedX P nets v (t + 1)) at hk
  have hk' : key ∈ ((P (t + 1)).sets c).image (raggedX P nets v (t + 1)) := by
    have h := hchild
    simpa [c, hmod] using h hk
  unfold raggedStrictSubtreeKeys
  apply Finset.mem_biUnion.mpr
  refine ⟨c, child_mem_strictSubtreeBags q hq j, ?_⟩
  simpa [raggedPlacement] using hk'

/-- D-side descendant-mass accounting for a real ragged stage. Slot widths
are now discharged from the physical split and injectivity of the execution;
only the analytic per-slot wrong-key estimates remain as hypotheses. -/
theorem ragged_actual_child_mass_lower_of_slot_errors
    {d : Nat} (P : Nat → RaggedWirePartition d)
    (splits : ∀ t b, RaggedWireSplit ((P t).sets b))
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (q : KBag 64 d)
    (hq : q.l < d) (hstep : P (t + 1) = (P t).route (splits t) raggedTreeDestination)
    (err : Fin 64 → Nat)
    (hbad : ∀ j : Fin 64,
      ((raggedStageDownSlotKeys P splits nets v t q j).filter
        (fun κ => κ ∉ nativeKeys (q.child j.val j.isLt hq))).card ≤ err j) :
    (∑ j : Fin 64, ((splits t q).widths j.val - err j)) ≤
      (raggedStrictSubtreeKeys P nets v (t + 1) q ∩ nativeKeys q).card := by
  apply native_child_mass_lower_of_slot_errors q hq
    (raggedStrictSubtreeKeys P nets v (t + 1) q)
    (raggedStageDownSlotKeys P splits nets v t q)
    (fun j => (splits t q).widths j.val) err
  · intro j
    exact raggedStageDownSlotKeys_subset_strictSubtree
      P splits nets v t q hq j hstep
  · intro j
    rw [raggedStageDownSlotKeys, Finset.card_image_of_injective _
      (raggedX_injective P nets v (t + 1))]
    exact raggedDownSet_card (splits t q) j.val j.isLt
  · exact hbad

end Tapered945
