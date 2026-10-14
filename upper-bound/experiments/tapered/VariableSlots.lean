import Mathlib.Tactic

namespace Tapered945

def slotPrefix (tau : Nat → Nat) (j : Nat) : Nat :=
  ∑ h ∈ Finset.range j, tau h

def slotLo (pi : Nat) (tau : Nat → Nat) (j : Nat) : Nat :=
  pi / 2 + slotPrefix tau j

def slotHi (pi : Nat) (tau : Nat → Nat) (j : Nat) : Nat :=
  slotLo pi tau j + tau j

/-- Two-sided boundary guarantee for a particular output permutation.
A separator contract must prove this for its own outputs for every input. -/
structure VariableRankSlotSpec (a pi : Nat) (tau : Nat → Nat) (EB : Rat)
    (p : Equiv.Perm (Fin a)) : Prop where
  low : ∀ (j : Nat), j < 64 →
    ((Finset.univ.filter fun c : Fin a =>
      (p c).val < slotLo pi tau j ∧ slotLo pi tau j ≤ c.val).card : Rat) ≤ EB
  high : ∀ (j : Nat), j < 64 →
    ((Finset.univ.filter fun c : Fin a =>
      slotHi pi tau j ≤ (p c).val ∧ c.val < slotHi pi tau j).card : Rat) ≤ EB

/-- The two boundary estimates bound all wrong keys in the corresponding
variable-width output slot. This is the unequal-width analogue of the
`NodeSpec.intruder_keys` counting step. -/
theorem variable_slot_intruders
    (a pi : Nat) (tau : Nat → Nat) (EB : Rat)
    (p : Equiv.Perm (Fin a)) (spec : VariableRankSlotSpec a pi tau EB p)
    (j : Nat) (hj : j < 64) :
    ((Finset.univ.filter fun c : Fin a =>
      slotLo pi tau j ≤ c.val ∧ c.val < slotHi pi tau j ∧
        ¬ (slotLo pi tau j ≤ (p c).val ∧ (p c).val < slotHi pi tau j)).card : Rat) ≤
      2 * EB := by
  let lo := slotLo pi tau j
  let hi := slotHi pi tau j
  let lowSet := Finset.univ.filter fun c : Fin a => (p c).val < lo ∧ lo ≤ c.val
  let highSet := Finset.univ.filter fun c : Fin a => hi ≤ (p c).val ∧ c.val < hi
  let wrong := Finset.univ.filter fun c : Fin a =>
    lo ≤ c.val ∧ c.val < hi ∧ ¬ (lo ≤ (p c).val ∧ (p c).val < hi)
  have hsubset : wrong ⊆ lowSet ∪ highSet := by
    intro c hc
    simp only [wrong, lowSet, highSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union] at hc ⊢
    rcases hc with ⟨hclo, hchi, hnot⟩
    by_cases hlow : (p c).val < lo
    · exact Or.inl ⟨hlow, hclo⟩
    · right
      have hrankhi : hi ≤ (p c).val := by omega
      exact ⟨hrankhi, hchi⟩
  have hcard : wrong.card ≤ lowSet.card + highSet.card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hlow := spec.low j hj
  have hhigh := spec.high j hj
  have hcast : (wrong.card : Rat) ≤ (lowSet.card : Rat) + (highSet.card : Rat) := by
    exact_mod_cast hcard
  have hlow' : (lowSet.card : Rat) ≤ EB := by simpa [lowSet, lo] using hlow
  have hhigh' : (highSet.card : Rat) ≤ EB := by simpa [highSet, hi] using hhigh
  change (wrong.card : Rat) ≤ 2 * EB
  linarith

end Tapered945
