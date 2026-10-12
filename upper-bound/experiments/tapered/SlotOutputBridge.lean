import VariableSlots
import VariableWindow

namespace Tapered945

/-- An output slot's bad keys either have an ideal rank in the slot, or
cross one of its two rank boundaries. No sorting assumption is hidden here. -/
theorem output_slot_bad_card_le
    (a L H : Nat) (r : Fin a → Nat) (bad : Fin a → Prop)
    [DecidablePred bad] :
    (Finset.univ.filter (fun c : Fin a => L ≤ c.val ∧ c.val < H ∧ bad c)).card ≤
      (Finset.univ.filter (fun c : Fin a => L ≤ r c ∧ r c < H ∧ bad c)).card +
      (Finset.univ.filter (fun c : Fin a => r c < L ∧ L ≤ c.val)).card +
      (Finset.univ.filter (fun c : Fin a => H ≤ r c ∧ c.val < H)).card := by
  let W := Finset.univ.filter (fun c : Fin a => L ≤ c.val ∧ c.val < H ∧ bad c)
  let I := Finset.univ.filter (fun c : Fin a => L ≤ r c ∧ r c < H ∧ bad c)
  let B := Finset.univ.filter (fun c : Fin a => r c < L ∧ L ≤ c.val)
  let T := Finset.univ.filter (fun c : Fin a => H ≤ r c ∧ c.val < H)
  have hs : W ⊆ (I ∪ B) ∪ T := by
    intro c hc
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [I, B, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hL : r c < L
    · exact Or.inl (Or.inr ⟨hL, hc.1⟩)
    · by_cases hH : r c < H
      · exact Or.inl (Or.inl ⟨by omega, hH, hc.2.2⟩)
      · exact Or.inr ⟨by omega, hc.2.1⟩
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le I B) _))

/-- Network-dependent slot guarantees can be combined with any bound on
bad keys in the ideal rank window. -/
theorem output_slot_bad_le_of_spec
    (a pi : Nat) (tau : Nat → Nat) (EB : Rat) (p : Equiv.Perm (Fin a))
    (spec : VariableRankSlotSpec a pi tau EB p)
    (bad : Fin a → Prop) [DecidablePred bad] (j : Nat) (hj : j < 64)
    (A : Rat)
    (hA : ((Finset.univ.filter (fun c : Fin a =>
      slotLo pi tau j ≤ (p c).val ∧ (p c).val < slotHi pi tau j ∧ bad c)).card : Rat) ≤ A) :
    ((Finset.univ.filter (fun c : Fin a =>
      slotLo pi tau j ≤ c.val ∧ c.val < slotHi pi tau j ∧ bad c)).card : Rat) ≤
      A + 2 * EB := by
  have hn := output_slot_bad_card_le a (slotLo pi tau j) (slotHi pi tau j)
    (fun c => (p c).val) bad
  have hr : ((Finset.univ.filter (fun c : Fin a =>
      slotLo pi tau j ≤ c.val ∧ c.val < slotHi pi tau j ∧ bad c)).card : Rat) ≤
      ((Finset.univ.filter (fun c : Fin a =>
        slotLo pi tau j ≤ (p c).val ∧ (p c).val < slotHi pi tau j ∧ bad c)).card : Rat) +
      ((Finset.univ.filter (fun c : Fin a =>
        (p c).val < slotLo pi tau j ∧ slotLo pi tau j ≤ c.val)).card : Rat) +
      ((Finset.univ.filter (fun c : Fin a =>
        slotHi pi tau j ≤ (p c).val ∧ c.val < slotHi pi tau j)).card : Rat) := by
    exact_mod_cast hn
  have hlow := spec.low j hj
  have hhigh := spec.high j hj
  linarith

/-- Real-valued version for the actual semantic boundary estimates. -/
theorem output_slot_bad_le_real
    (a L H : Nat) (r : Fin a → Nat) (bad : Fin a → Prop)
    [DecidablePred bad] (A EL EH : Real)
    (hA : ((Finset.univ.filter (fun c : Fin a =>
      L ≤ r c ∧ r c < H ∧ bad c)).card : Real) ≤ A)
    (hL : ((Finset.univ.filter (fun c : Fin a => r c < L ∧ L ≤ c.val)).card : Real) ≤ EL)
    (hH : ((Finset.univ.filter (fun c : Fin a => H ≤ r c ∧ c.val < H)).card : Real) ≤ EH) :
    ((Finset.univ.filter (fun c : Fin a => L ≤ c.val ∧ c.val < H ∧ bad c)).card : Real) ≤
      A + EL + EH := by
  have hn := output_slot_bad_card_le a L H r bad
  have hr : ((Finset.univ.filter (fun c : Fin a =>
      L ≤ c.val ∧ c.val < H ∧ bad c)).card : Real) ≤
      ((Finset.univ.filter (fun c : Fin a => L ≤ r c ∧ r c < H ∧ bad c)).card : Real) +
      ((Finset.univ.filter (fun c : Fin a => r c < L ∧ L ≤ c.val)).card : Real) +
      ((Finset.univ.filter (fun c : Fin a => H ≤ r c ∧ c.val < H)).card : Real) := by
    exact_mod_cast hn
  linarith

/-- Injective actual key labels transfer the ideal-rank population to the
key-set formulation used by the input-tail lemmas. The rank identification
is an explicit premise, to be supplied by execution/rank semantics. -/
theorem ideal_rank_bad_card_eq_keys
    (a L H lo hi : Nat) (k : Fin a → Nat) (hk : Function.Injective k)
    (r : Fin a → Nat)
    (hr : ∀ c, r c = Chvatal.BW.rankN (Finset.univ.image k) (k c)) :
    (Finset.univ.filter (fun c : Fin a =>
      L ≤ r c ∧ r c < H ∧ ¬ (lo ≤ k c ∧ k c < hi))).card =
    ((Finset.univ.image k).filter (fun κ =>
      L ≤ Chvatal.BW.rankN (Finset.univ.image k) κ ∧
      Chvatal.BW.rankN (Finset.univ.image k) κ < H ∧ ¬ (lo ≤ κ ∧ κ < hi))).card := by
  let S := Finset.univ.filter (fun c : Fin a =>
    L ≤ r c ∧ r c < H ∧ ¬ (lo ≤ k c ∧ k c < hi))
  have he : S.image k = (Finset.univ.image k).filter (fun κ =>
      L ≤ Chvatal.BW.rankN (Finset.univ.image k) κ ∧
      Chvatal.BW.rankN (Finset.univ.image k) κ < H ∧ ¬ (lo ≤ κ ∧ κ < hi)) := by
    ext κ
    simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, rfl⟩, by simpa only [hr c] using hc⟩
    · rintro ⟨⟨c, rfl⟩, hc⟩
      exact ⟨c, by simpa only [hr c] using hc, rfl⟩
  rw [← he, Finset.card_image_of_injective _ hk]

end Tapered945
