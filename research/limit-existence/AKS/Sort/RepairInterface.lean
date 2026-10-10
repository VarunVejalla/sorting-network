import AKS.Kahale.Fanout
import AKS.Kahale.RankInputs

/-! # Locality of a prefix with a short sorting suffix

This exposes a reusable consequence of the existing Kahale rank-cover proof.
Removing s parallel layers from any sorter leaves rank displacement strictly
less than 2^s. This is an extraction theorem, not an amplification theorem:
no claim that these interfaces compose across scales is made.
-/

namespace SortingRepair

open Finset

/-- Every attainable rank lies strictly within `radius` of its output wire. -/
def RankLocal {n : ℕ} (pre : ComparatorNetwork n) (radius : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
    (pre.exec σ i).val < i.val + radius ∧
    i.val < (pre.exec σ i).val + radius

/-- A short parallel sorting completion gives a local rank interface. -/
theorem rankLocal_of_sorting_suffix {n : ℕ} (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ∀ σ : Equiv.Perm (Fin n),
      (ComparatorNetwork.mk suffix.flatten).exec (pre.exec σ) = id) :
    RankLocal pre (2 ^ suffix.length) := by
  intro σ i
  apply Kahale.rank_cover_displacement pre i (Kahale.suffixReach suffix {i})
    (Kahale.sorted_suffix_rank_cover pre suffix hp hs i)
  simpa only [card_singleton, mul_one] using Kahale.suffixReach_card suffix {i}

/-- Extraction from the repository's actual sorting predicate. -/
theorem rankLocal_of_sorts {n : ℕ} (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨pre.comparators ++ suffix.flatten⟩) :
    RankLocal pre (2 ^ suffix.length) := by
  apply rankLocal_of_sorting_suffix pre suffix hp
  intro σ
  have he := Kahale.sorting_rank_identity _ hs σ
  rw [ComparatorNetwork.exec_append] at he
  exact he

/-- Thresholding a local rank interface leaves a narrow uncertain band.
The statements outside that band are exact for every rank permutation. -/
theorem rankLocal_threshold {n radius : ℕ} {pre : ComparatorNetwork n}
    (h : RankLocal pre radius) (σ : Equiv.Perm (Fin n)) (t : ℕ) (i : Fin n) :
    (i.val + radius ≤ t → (pre.exec σ i).val < t) ∧
    (t + radius ≤ i.val → t ≤ (pre.exec σ i).val) := by
  have hi := h σ i
  constructor <;> intro ht <;> omega

/-- A uniform rank-local promise is monotone in the radius. -/
theorem RankLocal.mono {n a b : ℕ} {pre : ComparatorNetwork n}
    (h : RankLocal pre a) (hab : a ≤ b) : RankLocal pre b := by
  intro σ i
  have hi := h σ i
  constructor <;> omega

end SortingRepair
