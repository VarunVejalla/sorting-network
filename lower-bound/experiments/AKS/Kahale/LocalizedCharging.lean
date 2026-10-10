module

public import AKS.Kahale.AmortizedAccounting

/-! # Accounting for localized information creation

The hypothesis that untouched blocks cannot gain coupling remains explicit.
These lemmas do not prove that hypothesis or an improved depth coefficient.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

theorem positive_creation_localized {ι : Type*} [DecidableEq ι]
    (blocks touched : Finset ι) (delta : ι → ℝ)
    (stable : ∀ b ∈ blocks, b ∉ touched → delta b ≤ 0) :
    ∑ b ∈ blocks, max (delta b) 0 =
      ∑ b ∈ blocks.filter (fun b ↦ b ∈ touched), max (delta b) 0 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases ht : b ∈ touched
  · simp [ht]
  · simp [ht, max_eq_right (stable b hb ht)]

theorem positive_negative_difference (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases h : 0 ≤ x
  · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ 0)]
    ring
  · have hx : x ≤ 0 := le_of_not_ge h
    rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]
    ring

theorem positive_variation_balance (bank : ℕ → ℝ) (d : ℕ) :
    (∑ t ∈ Finset.range d, max (bank (t + 1) - bank t) 0) -
      (∑ t ∈ Finset.range d, max (bank t - bank (t + 1)) 0) = bank d - bank 0 := by
  rw [← Finset.sum_sub_distrib]
  have hsum : (∑ t ∈ Finset.range d,
      (max (bank (t + 1) - bank t) 0 - max (bank t - bank (t + 1)) 0)) =
      ∑ t ∈ Finset.range d, (bank (t + 1) - bank t) := by
    apply Finset.sum_congr rfl
    intro t _
    have h := positive_negative_difference (bank (t + 1) - bank t)
    simpa only [neg_sub] using h
  rw [hsum]
  have hneg : (∑ t ∈ Finset.range d, (bank (t + 1) - bank t)) =
      -(∑ t ∈ Finset.range d, (bank t - bank (t + 1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hneg, bank_telescope]
  ring

end Kahale
