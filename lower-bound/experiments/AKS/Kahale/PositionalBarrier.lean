module

public import AKS.Kahale.MethodBarrier
public import Mathlib.Order.Interval.Finset.Fin

/-! # Positional consequences of sorted certificate-height profiles

Splitting each constant-height block into a lower unchanged segment and an
upper incremented segment preserves monotonicity. For monotone profiles,
the low-height cardinality constraint implies the positional constraint.
The full scheduling and rounding construction is documented separately.
-/

@[expose] public section

namespace Kahale

def splitBlockProfile {n : ℕ} (h : Fin n → ℕ) (cut : ℕ → ℕ) : Fin n → ℕ :=
  fun i ↦ if i.val < cut (h i) then h i else h i + 1

theorem splitBlockProfile_monotone {n : ℕ} (h : Fin n → ℕ) (hm : Monotone h)
    (cut : ℕ → ℕ) : Monotone (splitBlockProfile h cut) := by
  intro i j hij
  have hv : i.val ≤ j.val := hij
  have hh := hm hij
  by_cases he : h i = h j
  · simp only [splitBlockProfile]
    rw [he]
    split_ifs <;> omega
  · simp only [splitBlockProfile]
    split_ifs <;> omega

theorem sorted_height_count_implies_position {n : ℕ} (h : Fin n → ℕ)
    (hm : Monotone h) (s B : ℕ)
    (hc : (Finset.univ.filter (fun j ↦ h j ≤ s)).card ≤ B)
    (i : Fin n) (hi : B ≤ i.val) : s + 1 ≤ h i := by
  by_contra hn
  have hh : h i ≤ s := by omega
  have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j ↦ h j ≤ s) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hm (Finset.mem_Iic.mp hj)).trans hh⟩
  have hcard := (Finset.card_le_card hsub).trans hc
  rw [Fin.card_Iic] at hcard
  omega

end Kahale
