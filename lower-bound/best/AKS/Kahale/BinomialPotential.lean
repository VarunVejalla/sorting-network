module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-! # The discrete deficit potential behind Yao's counting inequality

A min-output inherits the smaller certificate height; a max-output has height
at most one plus the larger height. The convex potential below controls this
pair update. This module proves scalar facts, not a sorting-network bound.
-/

@[expose] public section

namespace Kahale

def deficitPotential : ℕ → ℕ → ℕ → ℕ
  | 0, L, x => L - x
  | h + 1, L, x => deficitPotential h L x + deficitPotential h L (x + 1)

theorem deficitPotential_decreasing (h L x : ℕ) :
    deficitPotential h L (x + 1) ≤ deficitPotential h L x := by
  induction h generalizing x with
  | zero => simp only [deficitPotential]; omega
  | succ h ih =>
    have h₁ := ih x
    have h₂ := ih (x + 1)
    simp only [deficitPotential]
    omega

theorem deficitPotential_convex (h L a b : ℕ) (hab : a ≤ b) :
    deficitPotential h L (a + 1) + deficitPotential h L b ≤
      deficitPotential h L a + deficitPotential h L (b + 1) := by
  induction h generalizing a b with
  | zero => simp only [deficitPotential]; omega
  | succ h ih =>
    have h₁ := ih a b hab
    have h₂ := ih (a + 1) (b + 1) (by omega)
    simp only [deficitPotential]
    omega

theorem deficitPotential_pair (h L a b : ℕ) :
    deficitPotential (h + 1) L a + deficitPotential (h + 1) L b ≤
      2 * (deficitPotential h L (min a b) + deficitPotential h L (max a b + 1)) := by
  rcases le_total a b with hab | hba
  · have hh := deficitPotential_convex h L a b hab
    simp only [min_eq_left hab, max_eq_right hab, deficitPotential]
    omega
  · have hh := deficitPotential_convex h L b a hba
    simp only [min_eq_right hba, max_eq_left hba, deficitPotential]
    omega

theorem deficitPotential_idle (h L x : ℕ) :
    deficitPotential (h + 1) L x ≤ 2 * deficitPotential h L x := by
  have hh := deficitPotential_decreasing h L x
  simp only [deficitPotential]
  omega

theorem deficitPotential_eq_zero (h L x : ℕ) (hx : L ≤ x) :
    deficitPotential h L x = 0 := by
  induction h generalizing x with
  | zero => exact Nat.sub_eq_zero_of_le hx
  | succ h ih => simp only [deficitPotential, ih x hx, ih (x + 1) (by omega), zero_add]

theorem deficitPotential_choose_lower (h L x i : ℕ) :
    (L - (x + i)) * Nat.choose h i ≤ deficitPotential h L x := by
  induction h generalizing x i with
  | zero =>
    cases i <;> simp [deficitPotential]
  | succ h ih =>
    cases i with
    | zero =>
      have hh := ih x 0
      simp only [Nat.add_zero, Nat.choose_zero_right, mul_one] at hh ⊢
      simp only [deficitPotential]
      omega
    | succ i =>
      have h₁ := ih x (i + 1)
      have h₂ := ih (x + 1) i
      have he : x + 1 + i = x + (i + 1) := by omega
      rw [he] at h₂
      rw [Nat.choose_succ_succ, mul_add]
      simp only [Nat.succ_eq_add_one]
      change _ ≤ deficitPotential h L x + deficitPotential h L (x + 1)
      omega

end Kahale
