module

public import AKS.Separator.PatersonPartial
public import AKS.Bags.Filter

/-! # Counting the two real halves of a padded partial bag -/

@[expose] public section

namespace Paterson

open Finset

theorem half_filter_card (m offset : ℕ) (ho : offset + m ≤ 2 * m)
    (P : Fin (2 * m) → Prop) [DecidablePred P] :
    (univ.filter (fun i : Fin m ↦
      P ⟨offset + i.val, by have := i.isLt; omega⟩)).card =
      (univ.filter (fun i : Fin (2 * m) ↦
        offset ≤ i.val ∧ i.val < offset + m ∧ P i)).card := by
  apply card_nbij (fun i : Fin m ↦
    (⟨offset + i.val, by have := i.isLt; omega⟩ : Fin (2 * m)))
  · intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hi ⊢
    exact ⟨by omega, by have := i.isLt; omega, hi⟩
  · intro i _ j _ hij
    have h := congrArg (fun x : Fin (2 * m) ↦ x.val) hij
    change offset + i.val = offset + j.val at h
    exact Fin.ext (by omega)
  · intro j hj
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hj
    let i : Fin m := ⟨j.val - offset, by omega⟩
    have heq : (⟨offset + i.val, by have := i.isLt; omega⟩ : Fin (2 * m)) = j := by
      apply Fin.ext
      dsimp [i]
      omega
    refine ⟨i, ?_, heq⟩
    simp only [mem_coe, mem_filter, mem_univ, true_and, heq]
    exact hj.2.2

theorem left_half_filter_card (m : ℕ) (P : Fin (2 * m) → Prop) [DecidablePred P] :
    (univ.filter (fun i : Fin m ↦ P ⟨i.val, by have := i.isLt; omega⟩)).card =
      (univ.filter (fun i : Fin (2 * m) ↦ i.val < m ∧ P i)).card := by
  simpa only [Nat.zero_add, Nat.zero_le, true_and] using
    half_filter_card m 0 (by omega) P

theorem right_half_filter_card (m : ℕ) (P : Fin (2 * m) → Prop) [DecidablePred P] :
    (univ.filter (fun i : Fin m ↦ P ⟨m + i.val, by have := i.isLt; omega⟩)).card =
      (univ.filter (fun i : Fin (2 * m) ↦ m ≤ i.val ∧ P i)).card := by
  have h : ∀ i : Fin (2 * m), m ≤ i.val ∧ i.val < m + m ∧ P i ↔
      m ≤ i.val ∧ P i := by
    intro i
    have hlt : i.val < m + m := by have := i.isLt; omega
    simp only [hlt, true_and]
  simpa only [h] using half_filter_card m m (by omega) P

/-- Both half refinements preserve each half's complete value multiset. -/
theorem partialRefinement_half_count {full real ambient : ℕ} (hs : real ≤ full)
    (w : Fin (2 * real) → Fin ambient) (P : Fin ambient → Prop) [DecidablePred P]
    (side : Bool) :
    ((univ.filter (fun i : Fin (2 * real) ↦
      if side then real ≤ i.val else i.val < real)).filter
        (fun i ↦ P ((partialRefinement full real hs).exec w i))).card =
    ((univ.filter (fun i : Fin (2 * real) ↦
      if side then real ≤ i.val else i.val < real)).filter (fun i ↦ P (w i))).card := by
  apply network_card_filter
  intro c hc
  change c ∈ _ ++ _ at hc
  rcases List.mem_append.mp hc with hl | hr
  · have h := shiftEmbed_wires_range
      ((refinementNetwork full).restrictWires real hs) (2 * real) 0 (by omega) c hl
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      mem_filter, mem_univ, true_and]
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · have h := shiftEmbed_wires_range
      (paddedFinalNetwork (refinementNetwork full) real hs)
      (2 * real) real (by omega) c hr
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      mem_filter, mem_univ, true_and]
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩

end Paterson
