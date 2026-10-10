module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # A modular interface for an amortized lower bound

These are conditional accounting theorems. They do not supply the missing
structural bank inequality for sorting networks.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

theorem bank_telescope (bank : ℕ → ℝ) (d : ℕ) :
    ∑ t ∈ Finset.range d, (bank t - bank (t + 1)) = bank 0 - bank d := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih]; ring

/-- Local entropy-budget and endpoint obligations imply the global budget. -/
theorem amortized_information_budget (gain bank error : ℕ → ℝ)
    (d : ℕ) (capacity rho endpoint totalError : ℝ)
    (localBudget : ∀ t < d,
      gain t ≤ (1 - rho) * capacity + bank t - bank (t + 1) + error t)
    (endpointBudget : bank 0 - bank d ≤ endpoint)
    (errorBudget : ∑ t ∈ Finset.range d, error t ≤ totalError) :
    ∑ t ∈ Finset.range d, gain t ≤
      (d : ℝ) * ((1 - rho) * capacity) + endpoint + totalError := by
  have h := Finset.sum_le_sum (s := Finset.range d)
    (fun t ht ↦ localBudget t (Finset.mem_range.mp ht))
  have hs : (∑ t ∈ Finset.range d,
      ((1 - rho) * capacity + bank t - bank (t + 1) + error t)) =
      (d : ℝ) * ((1 - rho) * capacity) + (bank 0 - bank d) +
        ∑ t ∈ Finset.range d, error t := by
    simp_rw [show ∀ t, (1 - rho) * capacity + bank t - bank (t + 1) + error t =
      (1 - rho) * capacity + (bank t - bank (t + 1)) + error t by intro t; ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, bank_telescope]
    simp
  rw [hs] at h
  linarith

/-- Deficit decomposition keeps orientation dependence distinct from bias. -/
theorem orientation_deficit_identity (slots gain marginalSum : ℝ) :
    slots - gain = (slots - marginalSum) + (marginalSum - gain) := by ring

end Kahale
