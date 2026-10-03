module

public import AKS.Separator.PatersonHalfCounting

/-! # Whole partial-bag filtering from the concrete padded gadget

Paterson (1990), Section 5. The first split consumes the actual large-cohort
support; half refinements consume the virtual ideal support. Keeping these
two distinct support conditions is necessary for a small partial bag.
-/

@[expose] public section

namespace Paterson

open Finset

theorem exec_filter_card {n ambient : ℕ} (net : ComparatorNetwork n)
    (u : Fin n → Fin ambient) (P : Fin ambient → Prop) [DecidablePred P] :
    (univ.filter (fun i ↦ P (net.exec u i))).card =
      (univ.filter (fun i ↦ P (u i))).card :=
  network_card_filter net u univ P (by intro c _; exact Or.inl ⟨mem_univ _, mem_univ _⟩)

theorem partialNetwork_initial {full real ambient : ℕ} (hs : real ≤ full)
    (h16 : 16 ∣ full) (u : Fin (2 * real) → Fin ambient) (hu : Function.Injective u)
    (threshold : ℕ) (ht : threshold ≤ ambient)
    (hfirst : ((univ.filter (fun i ↦ (u i).val < threshold)).card : ℝ) ≤
      (patersonAlpha0 : ℝ) * real)
    (hvirtual : ((univ.filter (fun i ↦ (u i).val < threshold)).card : ℝ) ≤
      (2 * patersonMu : ℝ) * full) :
    ((univ.filter (fun i : Fin (2 * real) ↦ full / 16 ≤ i.val ∧
      ((partialNetwork full real hs).exec u i).val < threshold)).card : ℝ) ≤
      (patersonDelta0 + refinementTailError : ℝ) *
        (univ.filter (fun i ↦ (u i).val < threshold)).card := by
  let w := (firstLevelNetwork real).exec u
  let out := (partialNetwork full real hs).exec u
  let P := fun x : Fin ambient ↦ x.val < threshold
  have hwcount : (univ.filter (fun i ↦ P (w i))).card =
      (univ.filter (fun i ↦ P (u i))).card := exec_filter_card _ _ P
  have hleftCount : (univ.filter (fun i : Fin real ↦
      P (w ⟨i.val, by have := i.isLt; omega⟩))).card ≤
        (univ.filter (fun i ↦ P (u i))).card := by
    rw [left_half_filter_card real (fun i ↦ P (w i))]
    apply le_trans _ hwcount.le
    apply card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2
  have hleft := partialNetwork_left_refinement hs h16 u hu threshold ht
    ((Nat.cast_le.mpr hleftCount).trans hvirtual)
  have hleftEq := left_half_filter_card real
    (fun i ↦ full / 16 ≤ i.val ∧ P (out i))
  have hleft' : ((univ.filter (fun i : Fin (2 * real) ↦
      i.val < real ∧ full / 16 ≤ i.val ∧ P (out i))).card : ℝ) ≤
        (refinementTailError : ℝ) * (univ.filter (fun i ↦ P (u i))).card := by
    rw [← hleftEq]
    apply hleft.trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hleftCount)
      (by norm_num [refinementTailError, patersonDelta2, patersonDelta3,
        patersonDelta4, patersonDelta5])
  have hrightEq : (univ.filter (fun i : Fin (2 * real) ↦ real ≤ i.val ∧ P (out i))).card =
      (univ.filter (fun i : Fin (2 * real) ↦ real ≤ i.val ∧ P (w i))).card := by
    have h := partialRefinement_half_count hs w P true
    simpa only [ite_true, filter_filter, out, partialNetwork,
      ComparatorNetwork.exec_append, w] using h
  have hgood := supported_injective_initial
    (restricted_halver_is_supported_separator (firstLevelNetwork_good real)) u hu threshold
    (show ((univ.filter (fun i ↦ (u i).val < threshold)).card : ℝ) ≤
      ((patersonAlpha0 : ℝ) / 2) * (2 * real : ℕ) by
        push_cast; nlinarith [hfirst])
  have hright : ((univ.filter (fun i : Fin (2 * real) ↦
      real ≤ i.val ∧ P (out i))).card : ℝ) ≤
        (patersonDelta0 : ℝ) * (univ.filter (fun i ↦ P (u i))).card := by
    rw [hrightEq]
    exact hgood
  have hsum : (univ.filter (fun i : Fin (2 * real) ↦
      full / 16 ≤ i.val ∧ P (out i))).card ≤
      (univ.filter (fun i : Fin (2 * real) ↦ i.val < real ∧ full / 16 ≤ i.val ∧ P (out i))).card +
        (univ.filter (fun i : Fin (2 * real) ↦ real ≤ i.val ∧ P (out i))).card := by
    apply (card_le_card (show _ ⊆ _ ∪ _ from ?_)).trans (card_union_le _ _)
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    by_cases h : i.val < real
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h, hi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega, hi.2⟩)
  have hsumR : ((univ.filter (fun i : Fin (2 * real) ↦
      full / 16 ≤ i.val ∧ P (out i))).card : ℝ) ≤
      (univ.filter (fun i : Fin (2 * real) ↦ i.val < real ∧ full / 16 ≤ i.val ∧ P (out i))).card +
        (univ.filter (fun i : Fin (2 * real) ↦ real ≤ i.val ∧ P (out i))).card := by
    exact_mod_cast hsum
  push_cast
  dsimp [P, out] at hleft' hright hsumR
  linarith

theorem partialNetwork_final {full real ambient : ℕ} (hs : real ≤ full)
    (h16 : 16 ∣ full) (u : Fin (2 * real) → Fin ambient) (hu : Function.Injective u)
    (threshold : ℕ) (ht : threshold ≤ ambient)
    (hfirst : ((univ.filter (fun i ↦ threshold ≤ (u i).val)).card : ℝ) ≤
      (patersonAlpha0 : ℝ) * real)
    (hvirtual : ((univ.filter (fun i ↦ threshold ≤ (u i).val)).card : ℝ) ≤
      (2 * patersonMu : ℝ) * full) :
    ((univ.filter (fun i : Fin (2 * real) ↦ i.val < 2 * real - full / 16 ∧
      threshold ≤ ((partialNetwork full real hs).exec u i).val)).card : ℝ) ≤
      (patersonDelta0 + refinementTailError : ℝ) *
        (univ.filter (fun i ↦ threshold ≤ (u i).val)).card := by
  let w := (firstLevelNetwork real).exec u
  let out := (partialNetwork full real hs).exec u
  let P := fun x : Fin ambient ↦ threshold ≤ x.val
  have hwcount : (univ.filter (fun i ↦ P (w i))).card =
      (univ.filter (fun i ↦ P (u i))).card := exec_filter_card _ _ P
  have hrightCount : (univ.filter (fun i : Fin real ↦
      P (w ⟨real + i.val, by have := i.isLt; omega⟩))).card ≤
        (univ.filter (fun i ↦ P (u i))).card := by
    rw [right_half_filter_card real (fun i ↦ P (w i))]
    apply le_trans _ hwcount.le
    apply card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2
  have hright := partialNetwork_right_refinement hs h16 u hu threshold ht
    ((Nat.cast_le.mpr hrightCount).trans hvirtual)
  have hrightEq := right_half_filter_card real
    (fun i ↦ i.val < 2 * real - full / 16 ∧ P (out i))
  have hright' : ((univ.filter (fun i : Fin (2 * real) ↦
      real ≤ i.val ∧ i.val < 2 * real - full / 16 ∧ P (out i))).card : ℝ) ≤
        (refinementTailError : ℝ) * (univ.filter (fun i ↦ P (u i))).card := by
    have hpos (i : Fin real) : real + i.val < 2 * real - full / 16 ↔ i.val < real - full / 16 := by
      have := i.isLt
      omega
    rw [← hrightEq]
    simp only [Fin.val_mk, hpos]
    apply hright.trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hrightCount)
      (by norm_num [refinementTailError, patersonDelta2, patersonDelta3,
        patersonDelta4, patersonDelta5])
  have hleftEq : (univ.filter (fun i : Fin (2 * real) ↦ i.val < real ∧ P (out i))).card =
      (univ.filter (fun i : Fin (2 * real) ↦ i.val < real ∧ P (w i))).card := by
    have h := partialRefinement_half_count hs w P false
    simpa only [Bool.false_eq_true, ite_false, filter_filter, out, partialNetwork,
      ComparatorNetwork.exec_append, w] using h
  have hgood := supported_injective_final
    (restricted_halver_is_supported_separator (firstLevelNetwork_good real)) u hu threshold
    (show ((univ.filter (fun i ↦ threshold ≤ (u i).val)).card : ℝ) ≤
      ((patersonAlpha0 : ℝ) / 2) * (2 * real : ℕ) by
        push_cast; nlinarith [hfirst])
  have hleft : ((univ.filter (fun i : Fin (2 * real) ↦
      i.val < real ∧ P (out i))).card : ℝ) ≤
        (patersonDelta0 : ℝ) * (univ.filter (fun i ↦ P (u i))).card := by
    rw [hleftEq]
    simpa only [show 2 * real - real = real by omega] using hgood
  have hsum : (univ.filter (fun i : Fin (2 * real) ↦
      i.val < 2 * real - full / 16 ∧ P (out i))).card ≤
      (univ.filter (fun i : Fin (2 * real) ↦ real ≤ i.val ∧ i.val < 2 * real - full / 16 ∧ P (out i))).card +
        (univ.filter (fun i : Fin (2 * real) ↦ i.val < real ∧ P (out i))).card := by
    apply (card_le_card (show _ ⊆ _ ∪ _ from ?_)).trans (card_union_le _ _)
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    by_cases h : real ≤ i.val
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h, hi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega, hi.2⟩)
  have hsumR : ((univ.filter (fun i : Fin (2 * real) ↦
      i.val < 2 * real - full / 16 ∧ P (out i))).card : ℝ) ≤
      (univ.filter (fun i : Fin (2 * real) ↦ real ≤ i.val ∧ i.val < 2 * real - full / 16 ∧ P (out i))).card +
        (univ.filter (fun i : Fin (2 * real) ↦ i.val < real ∧ P (out i))).card := by
    exact_mod_cast hsum
  push_cast
  dsimp [P, out] at hright' hleft hsumR
  linarith

/-- A whole supported-separator interface with explicit actual and virtual
support budgets. It can be consumed by the existing middle-stranger lemmas. -/
theorem partialNetwork_supported {full real : ℕ} (hs : real ≤ full)
    (h16 : 16 ∣ full) (support : ℝ)
    (hfirst : support * (2 * real : ℕ) ≤ (patersonAlpha0 : ℝ) * real)
    (hvirtual : support * (2 * real : ℕ) ≤ (2 * patersonMu : ℝ) * full) :
    IsSupportedSeparator (partialNetwork full real hs) (full / 16) support
      (patersonDelta0 + refinementTailError : ℝ) := by
  intro v
  have hsize (a : ℕ) (ha : (a : ℝ) ≤ support * (2 * real : ℕ)) : a ≤ 2 * real := by
    have h := ha.trans hfirst
    have hn : (a : ℝ) ≤ (2 * real : ℕ) := by
      norm_num [patersonAlpha0_eq] at h
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) real]
    exact_mod_cast hn
  constructor
  · intro a ha
    have hcount : (univ.filter (fun i ↦ (v i).val < a)).card = a := by
      rw [bijection_count_val_lt v v.injective, card_filter_val_lt _ _ (hsize a ha)]
    have h := partialNetwork_initial hs h16 v v.injective a (hsize a ha)
      (by rw [hcount]; exact ha.trans hfirst)
      (by rw [hcount]; exact ha.trans hvirtual)
    simpa only [hcount] using h
  · intro a ha
    have hbound := hsize a ha
    have hcount : (univ.filter (fun i ↦ 2 * real - a ≤ (v i).val)).card = a := by
      rw [bijection_count_val_ge v v.injective,
        card_filter_val_ge _ _ (Nat.sub_le _ _)]
      omega
    have h := partialNetwork_final hs h16 v v.injective (2 * real - a) (Nat.sub_le _ _)
      (by rw [hcount]; exact ha.trans hfirst)
      (by rw [hcount]; exact ha.trans hvirtual)
    simpa only [hcount] using h

end Paterson
