module
/-
  # ε-Halver Theory

  Defines ε-halvers and supporting infrastructure.

  Key definitions:
  • `countOnes`, `sortedVersion`: Boolean sequence sorting infrastructure
  • `EpsilonInitialHalved`, `EpsilonHalved`, `IsEpsilonHalver`: permutation-based
    halver definitions (AKS Section 3). Uses `rank` from `Fin.lean`.
  • `epsHalverMerge`: iterated halver composition
  • `IsEpsilonSorted`, `Monotone.bool_pattern`: sortedness infrastructure

  The proof that expanders yield ε-halvers is in `FromExpander.lean`.
-/

public import AKS.Sort.Defs
public import AKS.Sort.Depth
public import AKS.Misc.Fin

@[expose] public section


open Finset BigOperators


/-! **Sorted Version and Counting** -/









/-! **ε-Halvers (Permutation-Based Definition)** -/











/-! **Top/Bottom Half Partitioning** -/







/-! **Halver Composition** -/


/-! **Basic Properties of IsEpsilonSorted** -/


/-- The false-set cardinality is a `0*1*` witness for a monotone Boolean sequence. -/
lemma Monotone.bool_pattern_at_card {n : ℕ} (w : Fin n → Bool) (hw : Monotone w) :
    let k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
    (∀ i : Fin n, (i : ℕ) < k → w i = false) ∧
      (∀ i : Fin n, k ≤ (i : ℕ) → w i = true) := by
  dsimp only
  set k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  constructor
  · -- For i.val < k: w i = false
    intro ⟨i, hi⟩ h_lt
    by_contra h_not
    have h_true : w ⟨i, hi⟩ = true := by
      match h : w ⟨i, hi⟩ with
      | true => rfl
      | false => exact absurd h h_not
    -- Every j ≥ i has w j = true (by monotonicity)
    have h_above : ∀ j : Fin n, i ≤ j.val → w j = true := by
      intro ⟨j, hj⟩ h_ij
      have := hw (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from h_ij)
      rw [h_true] at this
      match h : w ⟨j, hj⟩ with
      | true => rfl
      | false => rw [h] at this; exact absurd this (by decide)
    -- So false set ⊆ {j | j.val < i}
    have h_sub : Finset.univ.filter (fun j : Fin n ↦ w j = false) ⊆
        Finset.Iio ⟨i, hi⟩ := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio, Fin.lt_def]
      by_contra h_ge; push_neg at h_ge
      exact absurd (h_above ⟨j, hj⟩ h_ge) (by simp [hm])
    -- Card of false set ≤ card of Iio = i
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iio] at this; omega
  · -- For k ≤ i.val: w i = true
    intro ⟨i, hi⟩ h_ge
    by_contra h_not
    have h_false : w ⟨i, hi⟩ = false := by
      match h : w ⟨i, hi⟩ with
      | false => rfl
      | true => exact absurd h h_not
    -- Every j ≤ i has w j = false (by monotonicity)
    have h_below : ∀ j : Fin n, j.val ≤ i → w j = false := by
      intro ⟨j, hj⟩ h_ji
      have := hw (show (⟨j, hj⟩ : Fin n) ≤ ⟨i, hi⟩ from h_ji)
      rw [h_false] at this
      match h : w ⟨j, hj⟩ with
      | false => rfl
      | true => rw [h] at this; exact absurd this (by decide)
    -- So Iic ⟨i, hi⟩ ⊆ false set
    have h_sub : Finset.Iic ⟨i, hi⟩ ⊆
        Finset.univ.filter (fun j : Fin n ↦ w j = false) := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_below ⟨j, hj⟩ hm
    -- Card of Iic = i + 1 ≤ card of false set = k
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iic] at this; omega





/-! **Halver Family** -/




/-! **Network Cast** -/




end
