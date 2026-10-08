module
/-
  # Displaced Count Monotonicity for Comparator Networks

  A comparator network can only decrease the "displaced count" — the number
  of small values at high positions (or large values at low positions).
  This is a key structural property used in the separator correctness proof.

  Main results:
  • `exec_displaced_le`: small values at high positions can only decrease
  • `exec_displaced_final_le`: large values at low positions can only decrease
-/

public import AKS.Sort.Defs

@[expose] public section


open Finset BigOperators

/-! **Comparator helpers** -/

/-- When `w(c.i) ≤ w(c.j)`, the comparator is identity. -/
lemma Comparator.apply_eq_of_le {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.i ≤ w c.j) :
    c.apply w = w := by
  ext pos; unfold Comparator.apply
  by_cases hpi : pos = c.i
  · rw [if_pos hpi, hpi, min_eq_left h]
  · rw [if_neg hpi]; by_cases hpj : pos = c.j
    · rw [if_pos hpj, hpj, max_eq_right h]
    · rw [if_neg hpj]

/-- When `w(c.j) < w(c.i)`, the comparator swaps positions `i` and `j`. -/
lemma Comparator.apply_eq_swap {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.j < w c.i) (pos : Fin n) :
    c.apply w pos = w (Equiv.swap c.i c.j pos) := by
  unfold Comparator.apply
  by_cases hpi : pos = c.i
  · rw [if_pos hpi, hpi, min_eq_right h.le, Equiv.swap_apply_left]
  · rw [if_neg hpi]; by_cases hpj : pos = c.j
    · rw [if_pos hpj, hpj, max_eq_left h.le, Equiv.swap_apply_right]
    · rw [if_neg hpj, Equiv.swap_apply_of_ne_of_ne hpi hpj]


/-! **SepInitial direction: small values at high positions** -/




/-! **SepFinal direction: large values at low positions** -/



end
