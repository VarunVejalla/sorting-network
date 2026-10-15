import OddEvenMerge64
import Mathlib.Data.Fintype.BigOperators

/-! Scalar threshold-count accounting for reassembling sorted half-packets.
The network realization and the scheduler's complementary-half partition
must be supplied separately. No global sorting bound is asserted here. -/

namespace Chvatal.PacketAlignment

open Finset BigOperators

/-- A sorted packet's suffix half contains `min h x` true values and its
prefix half contains `x-h` true values. Pair one suffix with one prefix. -/
def halfRebin {ι : Type} (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) (i : ι) : Nat :=
  min h (x i) + (x (σ i) - h)

theorem half_count_split (h x : Nat) : min h x + (x - h) = x := by
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem half_count_positive_split (h x μ : Nat) :
    (min h x - min h μ) + ((x - h) - (μ - h)) = x - μ := by
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem half_count_negative_split (h x μ : Nat) :
    (min h μ - min h x) + ((μ - h) - (x - h)) = μ - x := by
  exact half_count_positive_split h μ x

/-- Complementary-half pairing preserves the exact total threshold count. -/
theorem halfRebin_sum {ι : Type} [Fintype ι]
    (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) :
    (∑ i, halfRebin h x σ i) = ∑ i, x i := by
  unfold halfRebin
  rw [Finset.sum_add_distrib]
  have he : (∑ i, (x (σ i) - h)) = ∑ i, (x i - h) :=
    Equiv.sum_comp σ (fun i => x i - h)
  rw [he, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => half_count_split h (x i))

/-- Rebinning does not create positive spill relative to any common count
reference. This holds for every half-packet pairing permutation. -/
theorem halfRebin_positive_spill_le {ι : Type} [Fintype ι]
    (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) (μ : Nat) :
    (∑ i, (halfRebin h x σ i - μ)) ≤ ∑ i, (x i - μ) := by
  calc
    (∑ i, (halfRebin h x σ i - μ)) ≤
        ∑ i, ((min h (x i) - min h μ) + ((x (σ i) - h) - (μ - h))) := by
      apply Finset.sum_le_sum
      intro i _
      have hμ := half_count_split h μ
      unfold halfRebin
      omega
    _ = (∑ i, (min h (x i) - min h μ)) + ∑ i, ((x i - h) - (μ - h)) := by
      rw [Finset.sum_add_distrib]
      rw [Equiv.sum_comp σ (fun i => (x i - h) - (μ - h))]
    _ = ∑ i, (x i - μ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => half_count_positive_split h (x i) μ)

theorem halfRebin_negative_spill_le {ι : Type} [Fintype ι]
    (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) (μ : Nat) :
    (∑ i, (μ - halfRebin h x σ i)) ≤ ∑ i, (μ - x i) := by
  calc
    (∑ i, (μ - halfRebin h x σ i)) ≤
        ∑ i, ((min h μ - min h (x i)) + ((μ - h) - (x (σ i) - h))) := by
      apply Finset.sum_le_sum
      intro i _
      have hμ := half_count_split h μ
      unfold halfRebin
      omega
    _ = (∑ i, (min h μ - min h (x i))) + ∑ i, ((μ - h) - (x i - h)) := by
      rw [Finset.sum_add_distrib]
      rw [Equiv.sum_comp σ (fun i => (μ - h) - (x i - h))]
    _ = ∑ i, (μ - x i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => half_count_negative_split h (x i) μ)

/-- Thus the two-sided aggregate rank-count error is nonincreasing. -/
theorem halfRebin_absolute_error_le {ι : Type} [Fintype ι]
    (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) (μ : Nat) :
    (∑ i, ((halfRebin h x σ i - μ) + (μ - halfRebin h x σ i))) ≤
      ∑ i, ((x i - μ) + (μ - x i)) := by
  simp only [Finset.sum_add_distrib]
  exact Nat.add_le_add (halfRebin_positive_spill_le h x σ μ)
    (halfRebin_negative_spill_le h x σ μ)

theorem halfRebin_bound {ι : Type} (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι)
    (hx : ∀ i, x i ≤ 2 * h) (i : ι) : halfRebin h x σ i ≤ 2 * h := by
  have ha := Nat.min_le_left h (x i)
  have hb := hx (σ i)
  unfold halfRebin
  omega

private theorem half_count_square_split (h x : Nat) :
    x ^ 2 = (min h x) ^ 2 + (x - h) ^ 2 + 2 * h * (x - h) := by
  by_cases hx : x ≤ h
  · simp [Nat.min_eq_right hx, Nat.sub_eq_zero_of_le hx]
  · rw [Nat.min_eq_left (by omega)]
    have he : h + (x - h) = x := by omega
    nlinarith

/-- Repair has no fresh quadratic-energy defect: a capped half contributes
at most `h` to its cross term, and permutation preserves the other terms. -/
theorem halfRebin_sum_squares_le {ι : Type} [Fintype ι]
    (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) :
    (∑ i, (halfRebin h x σ i) ^ 2) ≤ ∑ i, (x i) ^ 2 := by
  calc
    (∑ i, (halfRebin h x σ i) ^ 2) ≤
        ∑ i, ((min h (x i)) ^ 2 + (x (σ i) - h) ^ 2 + 2 * h * (x (σ i) - h)) := by
      apply Finset.sum_le_sum
      intro i _
      have hcross := Nat.mul_le_mul_right (x (σ i) - h) (Nat.min_le_left h (x i))
      unfold halfRebin
      nlinarith
    _ = ∑ i, ((min h (x i)) ^ 2 + (x i - h) ^ 2 + 2 * h * (x i - h)) := by
      simp only [Finset.sum_add_distrib]
      rw [Equiv.sum_comp σ (fun i => (x i - h) ^ 2),
        Equiv.sum_comp σ (fun i => 2 * h * (x i - h))]
    _ = ∑ i, (x i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => (half_count_square_split h (x i)).symm)

/-- In particular, within one sender, reassembly does not increase variance
around its old mean (or any other common real reference). Destination-bag
regrouping and the change of reference remain separate obligations. -/
theorem halfRebin_centered_energy_le {ι : Type} [Fintype ι]
    (h : Nat) (x : ι → Nat) (σ : Equiv.Perm ι) (μ : Real) :
    (∑ i, ((halfRebin h x σ i : Real) - μ) ^ 2) ≤
      ∑ i, ((x i : Real) - μ) ^ 2 := by
  have hs : (∑ i, (halfRebin h x σ i : Real) ^ 2) ≤ ∑ i, (x i : Real) ^ 2 := by
    exact_mod_cast halfRebin_sum_squares_le h x σ
  have hc : (∑ i, (halfRebin h x σ i : Real)) = ∑ i, (x i : Real) := by
    exact_mod_cast halfRebin_sum h x σ
  have hid (f : ι → Real) :
      (∑ i, (f i - μ) ^ 2) = (∑ i, (f i) ^ 2) -
        2 * μ * (∑ i, f i) + ∑ _i : ι, μ ^ 2 := by
    calc
      (∑ i, (f i - μ) ^ 2) = ∑ i, ((f i) ^ 2 - (2 * μ) * f i + μ ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hid, hid, hc]
  linarith

end Chvatal.PacketAlignment
