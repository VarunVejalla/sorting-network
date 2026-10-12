import RaggedBootstrapFlow
import AddressDebt
import Mathlib.Tactic

namespace Tapered945

def bootstrapPrefixWires (d x j : Nat) : Nat :=
  ∑ i ∈ Finset.range j, bootstrapSlotRows x i * bootstrapColumns d

def bootstrapSuffixWires (d x j : Nat) : Nat :=
  ∑ i ∈ Finset.Ioc j 63, bootstrapSlotRows x i * bootstrapColumns d

def bootstrapHalfUpWires (d x : Nat) : Nat :=
  (bootstrapUpRows x / 2) * bootstrapColumns d

theorem bootstrap_down_coeff_prefix (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63) :
    (∑ i ∈ Finset.range j, bootstrapDownCoeff i) =
      (j : Rat) / 64 - 1 / 2 ^ 17 := by
  have hsame : ∀ i, bootstrapDownCoeff i = addressDownCoeff i := by
    intro i
    simp [bootstrapDownCoeff, addressDownCoeff, isEndAddress]
  simp_rw [hsame]
  exact addressDownCoeff_prefix_sum j hj1 hj63

theorem bootstrap_down_coeff_suffix (j : Nat) (hj : j ≤ 62) :
    (∑ i ∈ Finset.Ioc j 63, bootstrapDownCoeff i) =
      (63 - j : Nat) / 64 - 1 / 2 ^ 17 := by
  have hsame : ∀ i, bootstrapDownCoeff i = addressDownCoeff i := by
    intro i
    simp [bootstrapDownCoeff, addressDownCoeff, isEndAddress]
  simp_rw [hsame]
  exact addressDownCoeff_suffix_sum j hj

theorem bootstrap_prefix_wires_exact (d : Nat) (hd : 14 ≤ d) (x j : Nat)
    (hj1 : 1 ≤ j) (hj63 : j ≤ 63) :
    (bootstrapPrefixWires d x j : Rat) =
      ((j : Rat) / 64 - 1 / 2 ^ 17 +
        (j : Rat) * firstAddressDebt x / 64) * seedRootDown d := by
  have hfactor := bootstrap_input_factorization d hd
  have hterm : ∀ i,
      ((bootstrapSlotRows x i * bootstrapColumns d : Nat) : Rat) =
        (bootstrapDownCoeff i + firstAddressDebt x / 64) * seedRootDown d := by
    intro i
    rw [Nat.cast_mul, bootstrap_slot_rows_exact, hfactor]
    push_cast
    ring
  have hterm' : ∀ i,
      (bootstrapSlotRows x i : Rat) * (bootstrapColumns d : Rat) =
        (bootstrapDownCoeff i + firstAddressDebt x / 64) * seedRootDown d := by
    intro i
    simpa only [Nat.cast_mul] using hterm i
  unfold bootstrapPrefixWires
  push_cast
  simp_rw [hterm']
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [bootstrap_down_coeff_prefix j hj1 hj63]
  push_cast
  ring

theorem bootstrap_suffix_wires_exact (d : Nat) (hd : 14 ≤ d) (x j : Nat)
    (hj : j ≤ 62) :
    (bootstrapSuffixWires d x j : Rat) =
      ((63 - j : Nat) / 64 - 1 / 2 ^ 17 +
        (63 - j : Nat) * firstAddressDebt x / 64) * seedRootDown d := by
  have hfactor := bootstrap_input_factorization d hd
  have hterm : ∀ i,
      ((bootstrapSlotRows x i * bootstrapColumns d : Nat) : Rat) =
        (bootstrapDownCoeff i + firstAddressDebt x / 64) * seedRootDown d := by
    intro i
    rw [Nat.cast_mul, bootstrap_slot_rows_exact, hfactor]
    push_cast
    ring
  have hterm' : ∀ i,
      (bootstrapSlotRows x i : Rat) * (bootstrapColumns d : Rat) =
        (bootstrapDownCoeff i + firstAddressDebt x / 64) * seedRootDown d := by
    intro i
    simpa only [Nat.cast_mul] using hterm i
  unfold bootstrapSuffixWires
  push_cast
  simp_rw [hterm']
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  have hcard : (Finset.Ioc j 63).card = 63 - j := by simp
  rw [Finset.sum_const, hcard]
  rw [bootstrap_down_coeff_suffix j hj]
  push_cast
  ring

theorem bootstrap_half_up_wires_exact (d : Nat) (hd : 14 ≤ d) (x : Nat) :
    (bootstrapHalfUpWires d x : Rat) =
      (upFlow - firstAddressDebt x + 1 / cap) * seedRootDown d / 2 := by
  have hfactor := bootstrap_input_factorization d hd
  obtain ⟨k, hk⟩ := bootstrap_up_rows_even x
  have hdiv : bootstrapUpRows x / 2 = k := by omega
  have hsplit : 2 * bootstrapHalfUpWires d x =
      bootstrapUpRows x * bootstrapColumns d := by
    unfold bootstrapHalfUpWires
    rw [hdiv, hk]
    ring
  have hsplitR : 2 * (bootstrapHalfUpWires d x : Rat) =
      (bootstrapUpRows x : Rat) * bootstrapColumns d := by
    exact_mod_cast hsplit
  have hfactorR : (seedRootDown d : Rat) =
      (bootstrapRows : Rat) * bootstrapColumns d := by exact_mod_cast hfactor
  rw [bootstrap_up_rows_exact] at hsplitR
  have hmain : (bootstrapHalfUpWires d x : Rat) =
      (upFlow - firstAddressDebt x + 1 / cap) *
        ((bootstrapRows : Rat) * bootstrapColumns d) / 2 := by
    linarith
  calc
    (bootstrapHalfUpWires d x : Rat) =
        (upFlow - firstAddressDebt x + 1 / cap) *
          ((bootstrapRows : Rat) * bootstrapColumns d) / 2 := hmain
    _ = (upFlow - firstAddressDebt x + 1 / cap) *
          (seedRootDown d : Rat) / 2 := by rw [← hfactorR]

/-- The signed reserve is exactly the small excess in the prefix count when
the physical prefix widths are compared with the equal native child intervals.
This is the arithmetic identity needed to derive the first-stage hL bound
from the root's external-tail bound. -/
theorem bootstrap_prefix_tail_slack (d : Nat) (hd : 14 ≤ d) (x j : Nat)
    (hj1 : 1 ≤ j) (hj63 : j ≤ 63) :
    (bootstrapPrefixWires d x j : Rat) + bootstrapHalfUpWires d x +
        (seedRootDown d : Rat) / (2 * cap) +
          ((32 : Rat) - j) * firstAddressDebt x * seedRootDown d / 64 =
      (j : Rat) * ((seedRootDown d : Rat) / 64) +
        (seedRootDown d : Rat) / (2 * cap) := by
  rw [bootstrap_prefix_wires_exact d hd x j hj1 hj63,
    bootstrap_half_up_wires_exact d hd x]
  unfold upFlow cap
  push_cast
  ring_nf

/-- The dual suffix reserve identity for the right-tail estimate. -/
theorem bootstrap_suffix_tail_slack (d : Nat) (hd : 14 ≤ d) (x j : Nat)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62) :
    (bootstrapSuffixWires d x j : Rat) + bootstrapHalfUpWires d x +
        (seedRootDown d : Rat) / (2 * cap) +
          ((j : Rat) - 31) * firstAddressDebt x * seedRootDown d / 64 =
      ((63 - j : Nat) : Rat) * ((seedRootDown d : Rat) / 64) +
        (seedRootDown d : Rat) / (2 * cap) := by
  rw [bootstrap_suffix_wires_exact d hd x j hj62,
    bootstrap_half_up_wires_exact d hd x]
  have hjcast : ((63 - j : Nat) : Rat) = 63 - j := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hjcast]
  unfold upFlow cap
  push_cast
  ring_nf

end Tapered945
