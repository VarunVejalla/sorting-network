import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A zero far-crossing contract for every threshold implies a pointwise
rank-displacement bound. This is the interface needed to feed a band-repair
stage into the logarithmic-displacement terminal-cleanup lemma. -/

namespace Chvatal.D2CrossingToDisplacement

def lowKeysInSuffix {n : Nat} (f : Fin n -> Fin n) (k p : Nat) : Nat :=
  (Finset.univ.filter fun q : Fin n => p <= q.val /\ (f q).val < k).card

def highKeysInPrefix {n : Nat} (f : Fin n -> Fin n) (k p : Nat) : Nat :=
  (Finset.univ.filter fun q : Fin n => q.val <= p /\ k <= (f q).val).card

/-- If no threshold key can cross a cut by more than `C`, in either
direction, then every output position is within `C` of the key's rank. -/
theorem pointwise_displacement_le
    {n C : Nat} (f : Fin n -> Fin n)
    (hLow : forall k p, k + C <= p -> lowKeysInSuffix f k p = 0)
    (hHigh : forall k p, p + C < k -> highKeysInPrefix f k p = 0) :
    forall p : Fin n,
      (f p).val <= p.val + C /\ p.val <= (f p).val + C := by
  intro p
  constructor
  · by_contra h
    have hlt : p.val + C < (f p).val := by omega
    have hz := hHigh ((f p).val) p.val hlt
    have hmem : p ∈ Finset.univ.filter
        (fun q : Fin n => q.val <= p.val /\ (f q).val >= (f p).val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, le_rfl⟩
    have hpos : 0 < (Finset.univ.filter
        (fun q : Fin n => q.val <= p.val /\ (f q).val >= (f p).val)).card :=
      Finset.card_pos.mpr ⟨p, hmem⟩
    change (Finset.univ.filter
        (fun q : Fin n => q.val <= p.val /\ (f q).val >= (f p).val)).card = 0 at hz
    omega
  · by_contra h
    have hlt : (f p).val + C < p.val := by omega
    have hk : (f p).val + 1 + C <= p.val := by omega
    have hz := hLow ((f p).val + 1) p.val hk
    have hmem : p ∈ Finset.univ.filter
        (fun q : Fin n => p.val <= q.val /\ (f q).val < (f p).val + 1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_rfl, by omega⟩
    have hpos : 0 < (Finset.univ.filter
        (fun q : Fin n => p.val <= q.val /\ (f q).val < (f p).val + 1)).card :=
      Finset.card_pos.mpr ⟨p, hmem⟩
    change (Finset.univ.filter
        (fun q : Fin n => p.val <= q.val /\ (f q).val < (f p).val + 1)).card = 0 at hz
    omega

end Chvatal.D2CrossingToDisplacement
