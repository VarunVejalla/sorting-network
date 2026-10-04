module

public import AKS.Paterson.DeepErrors

/-! # Fixed positional bins in a sorted rank sequence -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem sorted_threshold_prefix {m n : ℕ} (u : Fin m → Fin n) (hu : Monotone u)
    (threshold : ℕ) (i : Fin m) :
    (u i).val < threshold ↔ i.val < (univ.filter (fun j ↦ (u j).val < threshold)).card := by
  constructor
  · intro hi
    have hsub : univ.filter (fun j : Fin m ↦ j.val < i.val + 1) ⊆
        univ.filter (fun j ↦ (u j).val < threshold) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      have hij : j ≤ i := by change j.val ≤ i.val; omega
      have hmono := hu hij
      change (u j).val ≤ (u i).val at hmono
      omega
    have hc := card_le_card hsub
    rw [card_filter_val_lt _ _ (by have := i.isLt; omega)] at hc
    omega
  · intro hi
    by_contra hvalue
    have hsub : univ.filter (fun j ↦ (u j).val < threshold) ⊆
        univ.filter (fun j : Fin m ↦ j.val < i.val) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      by_contra hji
      have hij : i ≤ j := by change i.val ≤ j.val; omega
      have hmono := hu hij
      change (u i).val ≤ (u j).val at hmono
      omega
    have hc := card_le_card hsub
    rw [card_filter_val_lt _ _ i.isLt.le] at hc
    omega

theorem positional_interval_card (n a b : ℕ) (hb : b ≤ n) :
    (univ.filter (fun i : Fin n ↦ a ≤ i.val ∧ i.val < b)).card = b - a := by
  by_cases hab : a ≤ b
  · have hpart : univ.filter (fun i : Fin n ↦ i.val < b) =
        univ.filter (fun i : Fin n ↦ i.val < a) ∪
          univ.filter (fun i : Fin n ↦ a ≤ i.val ∧ i.val < b) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    have hd : Disjoint (univ.filter (fun i : Fin n ↦ i.val < a))
        (univ.filter (fun i : Fin n ↦ a ≤ i.val ∧ i.val < b)) := by
      rw [disjoint_filter]
      intro i _ hi hj
      omega
    have hc := card_filter_val_lt n b hb
    rw [hpart, card_union_of_disjoint hd, card_filter_val_lt _ _ (hab.trans hb)] at hc
    omega
  · have hz : univ.filter (fun i : Fin n ↦ a ≤ i.val ∧ i.val < b) = ∅ := by
      rw [filter_eq_empty_iff]
      intro i _ hi
      omega
    rw [hz, card_empty]
    omega

theorem sorted_bin_wrong_bound {m n : ℕ} (u : Fin m → Fin n) (hu : Monotone u)
    (a b lo hi : ℕ) (hb : b ≤ m) {E : ℚ} (hE : 0 ≤ E)
    (hlow : ((univ.filter (fun i ↦ (u i).val < lo)).card : ℚ) - a ≤ E)
    (hhigh : (b : ℚ) - (univ.filter (fun i ↦ (u i).val < hi)).card ≤ E) :
    ((univ.filter (fun i ↦ a ≤ i.val ∧ i.val < b ∧
      ((u i).val < lo ∨ hi ≤ (u i).val))).card : ℚ) ≤ 2 * E := by
  let A := (univ.filter (fun i ↦ (u i).val < lo)).card
  let B := (univ.filter (fun i ↦ (u i).val < hi)).card
  have hA : A ≤ m := (card_le_card (filter_subset _ _)).trans (by simp)
  have hB : B ≤ m := (card_le_card (filter_subset _ _)).trans (by simp)
  have hsub : univ.filter (fun i ↦ a ≤ i.val ∧ i.val < b ∧
      ((u i).val < lo ∨ hi ≤ (u i).val)) ⊆
      univ.filter (fun i : Fin m ↦ a ≤ i.val ∧ i.val < A) ∪
        univ.filter (fun i : Fin m ↦ B ≤ i.val ∧ i.val < b) := by
    intro i hmem
    simp only [mem_filter, mem_univ, true_and, mem_union] at hmem ⊢
    rcases hmem.2.2 with h | h
    · exact Or.inl ⟨hmem.1, (sorted_threshold_prefix u hu lo i).mp h⟩
    · right
      have hnot : ¬ (u i).val < hi := by omega
      have hn := mt (sorted_threshold_prefix u hu hi i).mpr hnot
      exact ⟨by omega, hmem.2.1⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  rw [positional_interval_card _ _ _ hA, positional_interval_card _ _ _ hb] at hc
  have hlow' : ((A - a : ℕ) : ℚ) ≤ E := by
    by_cases ha : a ≤ A
    · rw [Nat.cast_sub ha]
      exact hlow
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
      exact hE
  have hhigh' : ((b - B : ℕ) : ℚ) ≤ E := by
    by_cases hbb : B ≤ b
    · rw [Nat.cast_sub hbb]
      exact hhigh
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
      exact hE
  have hcQ : ((univ.filter (fun i ↦ a ≤ i.val ∧ i.val < b ∧
      ((u i).val < lo ∨ hi ≤ (u i).val))).card : ℚ) ≤ (A - a : ℕ) + (b - B : ℕ) := by
    exact_mod_cast hc
  linarith

end Paterson.Bags
