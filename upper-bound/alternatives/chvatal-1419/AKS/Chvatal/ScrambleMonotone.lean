module

/-
  # Column sorting never increases marks in a top region (deterministic monotonicity)

  For a `Bool` matrix `w` (marks = `true`), sorting every column ascending moves marks down, so the
  count of marks in the top rows (`matrixOnesCountInRegion`, rows `< m - i`) never increases; a row
  scramble preserves each row's content, hence also those counts.  Consequently the second round
  of a two-round separator can only improve a top-region mark count (and, symmetrically, a
  bottom-region count of zeros).
-/

public import AKS.Chvatal.SortedColumnDecode
public import AKS.Chvatal.PhysicalPack2

@[expose] public section

namespace Chvatal

open Finset

/-- Zero (`false`) marks in the bottom row-suffix `rows ≥ i` (the low-side counterpart of
`matrixOnesCountInRegion`). -/
def matrixZerosCountInSuffix {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) (i : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin (m * n) =>
      i ≤ (matrixRow m n hn w).val ∧ v w = false).card

/-! ### Row-preserving permutations preserve region counts -/

theorem matrixOnesCountInRegion_comp_perm {m n : Nat} (hn : 0 < n)
    (ρ : Equiv.Perm (Fin (m * n))) (hρ : ∀ w, matrixRow m n hn (ρ w) = matrixRow m n hn w)
    (u : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn (u ∘ ρ) i = matrixOnesCountInRegion hn u i := by
  unfold matrixOnesCountInRegion
  refine Finset.card_bij (fun w _ => ρ w) ?_ (fun a _ b _ h => ρ.injective h) ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hw ⊢
    rw [hρ]; exact hw
  · intro w hw
    refine ⟨ρ.symm w, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hw ⊢
    have := hρ (ρ.symm w)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]; simpa using hw

theorem matrixZerosCountInSuffix_comp_perm {m n : Nat} (hn : 0 < n)
    (ρ : Equiv.Perm (Fin (m * n))) (hρ : ∀ w, matrixRow m n hn (ρ w) = matrixRow m n hn w)
    (u : Fin (m * n) → Bool) (i : Nat) :
    matrixZerosCountInSuffix hn (u ∘ ρ) i = matrixZerosCountInSuffix hn u i := by
  unfold matrixZerosCountInSuffix
  refine Finset.card_bij (fun w _ => ρ w) ?_ (fun a _ b _ h => ρ.injective h) ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hw ⊢
    rw [hρ]; exact hw
  · intro w hw
    refine ⟨ρ.symm w, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hw ⊢
    have := hρ (ρ.symm w)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]; simpa using hw

theorem matrixOnesCountInRegion_comp_rowScramble_symm {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (u : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn (u ∘ (rowScrambleWirePerm m n hn σ).symm) i =
      matrixOnesCountInRegion hn u i :=
  matrixOnesCountInRegion_comp_perm hn _ (matrixRow_rowScrambleWirePerm_symm hn σ) u i

theorem matrixZerosCountInSuffix_comp_rowScramble_symm {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (u : Fin (m * n) → Bool) (i : Nat) :
    matrixZerosCountInSuffix hn (u ∘ (rowScrambleWirePerm m n hn σ).symm) i =
      matrixZerosCountInSuffix hn u i :=
  matrixZerosCountInSuffix_comp_perm hn _ (matrixRow_rowScrambleWirePerm_symm hn σ) u i

/-! ### Column sorting never increases the top-region marks -/

private theorem card_rows_ge_le {m : Nat} (i : Nat) :
    (univ.filter fun r : Fin m => m - i ≤ r.val).card ≤ i := by
  rw [card_filter_val_ge m (m - i) (Nat.sub_le _ _)]; omega

private theorem card_rows_lt_le {m : Nat} (i : Nat) :
    (univ.filter fun r : Fin m => r.val < i).card ≤ i := by
  calc (univ.filter fun r : Fin m => r.val < i).card
      ≤ (Finset.range i).card := by
        refine card_le_card_of_injOn (fun r => r.val) ?_ (fun a _ b _ h => Fin.ext h)
        intro r hr
        simpa using (mem_filter.mp hr).2
    _ = i := card_range i

/-- Per-column: marks in the top region are at least `colSum - i`. -/
private theorem matrixColumnTrueCount_sub_le {m n : Nat} (j : Fin n) (w : Fin (m * n) → Bool)
    (i : Nat) :
    matrixColumnTrueCount j w - i ≤
      (univ.filter fun r : Fin m => r.val < m - i ∧ w (matrixWire m n r j) = true).card := by
  have hT : (univ.filter fun r : Fin m => w (matrixWire m n r j) = true) ⊆
      (univ.filter fun r : Fin m => r.val < m - i ∧ w (matrixWire m n r j) = true) ∪
        univ.filter fun r : Fin m => m - i ≤ r.val := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and, mem_union] at hr ⊢
    rcases lt_or_ge r.val (m - i) with h | h
    exacts [Or.inl ⟨h, hr⟩, Or.inr h]
  have h := (card_le_card hT).trans (card_union_le _ _)
  have h2 := card_rows_ge_le (m := m) i
  unfold matrixColumnTrueCount
  omega

theorem matrixOnesCountInRegion_eq_sum_columns {m n : Nat} (hn : 0 < n) (w : Fin (m * n) → Bool)
    (i : Nat) :
    matrixOnesCountInRegion hn w i =
      ∑ j : Fin n,
        (univ.filter fun r : Fin m => r.val < m - i ∧ w (matrixWire m n r j) = true).card := by
  rw [matrixOnesCountInRegion, card_filter, sum_matrixWire hn]
  refine sum_congr rfl fun j _ => ?_
  rw [← card_filter]
  simp only [(matrixWire_row_col hn _ _).1]

/-- **Column sorting never increases the marks in a top region.** -/
theorem matrixOnesCountInRegion_colSort_le {m n : Nat} (hn : 0 < n) (w : Fin (m * n) → Bool)
    (i : Nat) :
    matrixOnesCountInRegion hn ((columnSortNetwork m n hn).exec w) i ≤
      matrixOnesCountInRegion hn w i := by
  rw [matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i, matrixOnesCountInRegion_eq_sum_columns]
  exact sum_le_sum fun j _ => matrixColumnTrueCount_sub_le j w i

/-- Scramble, then column sort: never increases the marks in a top region
(no hypothesis on the matrix or on the scramble). -/
theorem matrixOnesCountInRegion_scramble_colSort_le {m n : Nat} (hn : 0 < n) (σ : Scramble m n)
    (u : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn
        ((columnSortNetwork m n hn).exec (u ∘ (rowScrambleWirePerm m n hn σ).symm)) i ≤
      matrixOnesCountInRegion hn u i :=
  (matrixOnesCountInRegion_colSort_le hn _ i).trans
    (matrixOnesCountInRegion_comp_rowScramble_symm hn σ u i).le

/-- The second round never increases the top-region marks of the first-round semantic output. -/
theorem matrixOnesCountInRegion_semanticExec2_le {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (v : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn (semanticExec2 hn σ1 σ2 v) i ≤
      matrixOnesCountInRegion hn (semanticExec hn σ1 v) i :=
  matrixOnesCountInRegion_scramble_colSort_le hn σ2 _ i

/-! ### Symmetric statement: zeros in a bottom suffix -/

private theorem matrixColumnFalseCount_le {m n : Nat} (j : Fin n) (w : Fin (m * n) → Bool)
    (i : Nat) :
    (m - matrixColumnTrueCount j w) - i ≤
      (univ.filter fun r : Fin m => i ≤ r.val ∧ w (matrixWire m n r j) = false).card := by
  have hF : (univ.filter fun r : Fin m => w (matrixWire m n r j) = false) ⊆
      (univ.filter fun r : Fin m => i ≤ r.val ∧ w (matrixWire m n r j) = false) ∪
        univ.filter fun r : Fin m => r.val < i := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and, mem_union] at hr ⊢
    rcases lt_or_ge r.val i with h | h
    exacts [Or.inr h, Or.inl ⟨h, hr⟩]
  have h := (card_le_card hF).trans (card_union_le _ _)
  have h2 := card_rows_lt_le (m := m) i
  have h3 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun r => w (matrixWire m n r j) = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at h3
  unfold matrixColumnTrueCount
  omega

private theorem card_filter_Ico' (m a b : Nat) :
    (univ.filter fun r : Fin m => a ≤ r.val ∧ r.val < b).card = min b m - a := by
  rw [← Nat.card_Ico, ← card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
  constructor
  · rintro ⟨r, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, lt_min h2 r.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2.trans_le (min_le_right _ _)⟩, ⟨h1, h2.trans_le (min_le_left _ _)⟩, rfl⟩

theorem matrixZerosCountInSuffix_colSort_eq_sum {m n : Nat} (hn : 0 < n) (i : Nat)
    (v : Fin (m * n) → Bool) :
    matrixZerosCountInSuffix hn ((columnSortNetwork m n hn).exec v) i =
      ∑ j : Fin n, ((m - matrixColumnTrueCount j v) - i) := by
  set u := (columnSortNetwork m n hn).exec v
  have hcm : ColumnMonotoneInput m n hn u := columnSortNetwork_columnMonotone hn v
  rw [matrixZerosCountInSuffix, card_filter, sum_matrixWire hn]
  refine sum_congr rfl fun j _ => ?_
  have hcnt : matrixColumnTrueCount j u = matrixColumnTrueCount j v :=
    matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn) v
  rw [← card_filter]
  simp only [(matrixWire_row_col hn _ _).1]
  rw [show (univ.filter fun r : Fin m => i ≤ r.val ∧ u (matrixWire m n r j) = false) =
      univ.filter fun r : Fin m => i ≤ r.val ∧ r.val < m - matrixColumnTrueCount j u by
    ext r
    have := r.isLt
    have := matrixColumnTrueCount_le j u
    simp only [mem_filter, mem_univ, true_and, Bool.eq_false_iff, ne_eq,
      colMono_true_iff hn hcm]
    omega, card_filter_Ico', hcnt]
  have := matrixColumnTrueCount_le j v
  omega

/-- **Column sorting never increases the zeros in a bottom suffix.** -/
theorem matrixZerosCountInSuffix_colSort_le {m n : Nat} (hn : 0 < n) (w : Fin (m * n) → Bool)
    (i : Nat) :
    matrixZerosCountInSuffix hn ((columnSortNetwork m n hn).exec w) i ≤
      matrixZerosCountInSuffix hn w i := by
  rw [matrixZerosCountInSuffix_colSort_eq_sum hn i]
  unfold matrixZerosCountInSuffix
  rw [card_filter, sum_matrixWire hn]
  refine sum_le_sum fun j _ => ?_
  rw [← card_filter]
  simp only [(matrixWire_row_col hn _ _).1]
  exact matrixColumnFalseCount_le j w i

theorem matrixZerosCountInSuffix_semanticExec2_le {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (v : Fin (m * n) → Bool) (i : Nat) :
    matrixZerosCountInSuffix hn (semanticExec2 hn σ1 σ2 v) i ≤
      matrixZerosCountInSuffix hn (semanticExec hn σ1 v) i :=
  (matrixZerosCountInSuffix_colSort_le hn _ i).trans
    (matrixZerosCountInSuffix_comp_rowScramble_symm hn σ2 _ i).le

end Chvatal
