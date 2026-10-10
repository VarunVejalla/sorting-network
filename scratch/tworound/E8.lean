import AKS.Chvatal.Bulk2Count
import AKS.Chvatal.PackSpec2
open Finset

namespace Chvatal

/-- Number of `true` wires is unchanged by a wire permutation. -/
theorem card_true_comp_equiv {N : ℕ} (f : Fin N → Bool) (e : Equiv.Perm (Fin N)) :
    (univ.filter fun w => (f ∘ e) w = true).card = (univ.filter fun w => f w = true).card := by
  refine Finset.card_bij (fun w _ => e w) ?_ (fun a _ b _ h => e.injective h) ?_
  · intro w hw; simpa using hw
  · intro w hw
    exact ⟨e.symm w, by simpa using hw, by simp⟩

theorem card_true_colSort {m n : Nat} (hn : 0 < n) (v : Fin (m * n) → Bool) :
    (univ.filter fun w => (columnSortNetwork m n hn).exec v w = true).card =
      (univ.filter fun w => v w = true).card := by
  rw [card_filter, card_filter, sum_matrixWire hn, sum_matrixWire hn]
  refine sum_congr rfl fun j _ => ?_
  have := matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn) v
  rw [← card_filter, ← card_filter]
  exact this

/-- Decode of the second round: the region count of the two-round semantic output is the
combinatorial `onesAboveBottom` of the intermediate (post first round) column sums under `σ2`. -/
theorem matrixOnesCountInRegion_semanticExec2_eq {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (x : Fin (m * n) → Bool) (i : Nat) :
    matrixOnesCountInRegion hn (semanticExec2 hn σ1 σ2 x) i =
      onesAboveBottom (monotoneColumnSumsOfBool (semanticExec hn σ1 x)) σ2 i := by
  set u := semanticExec hn σ1 x with hu
  set c' := monotoneColumnSumsOfBool u
  have hcm : ColumnMonotoneInput m n hn u := columnSortNetwork_columnMonotone hn _
  have hu1 : u = monotoneMatrixBool hn c' := monotoneMatrixBool_eq_of_columnMonotone hn u hcm
  show matrixOnesCountInRegion hn ((columnSortNetwork m n hn).exec
    (u ∘ (rowScrambleWirePerm m n hn σ2).symm)) i = _
  rw [matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i]
  refine sum_congr rfl fun j _ => ?_
  rw [scrambledColSum_eq_matrixColumnTrueCount hn σ2 c' j, ← hu1]

/-- Round-1 data of the intermediate state: exact mass `i·n` and excess equal to the round-1
`onesAboveBottom`. -/
theorem semanticExec_intermediate {m n : Nat} (hn : 0 < n) (σ1 : Scramble m n)
    (x : Fin (m * n) → Bool) (i : Nat) :
    totalColumnOnes (monotoneColumnSumsOfBool (semanticExec hn σ1 x)) =
      totalColumnOnes (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec x)) ∧
    excessAbove (monotoneColumnSumsOfBool (semanticExec hn σ1 x)) i =
      onesAboveBottom (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec x)) σ1 i := by
  set pre := (columnSortNetwork m n hn).exec x ∘ (rowScrambleWirePerm m n hn σ1).symm with hpre
  have hu : semanticExec hn σ1 x = (columnSortNetwork m n hn).exec pre := rfl
  constructor
  · rw [hu, totalColumnOnes_colSort_exec_eq, totalColumnOnes_colSort_exec_eq, hpre]
    rw [card_true_comp_equiv, card_true_colSort]
  · rw [← matrixOnesCountInRegion_semanticExec, hu,
      matrixOnesCountInRegion_colSort_eq_sum_columnSub hn i]
    unfold excessAbove monotoneColumnSumsOfBool
    refine sum_congr rfl fun j _ => ?_
    simp only
    rw [matrixColumnTrueCount_exec_eq hn j _ (columnSortNetwork_columnLocal m n hn)]

/-- **T2.** Round-1 pipeline Property B (at `E1`) and round-2 combinatorial Property B2 give
two-round semantic Property B (at `d`). -/
theorem HasPackSemanticPropertyB2.of_combinatorial {m n : Nat} {E1 d : ℝ} (hn : 0 < n)
    {σ1 σ2 : Scramble m n} (h1 : HasCombinatorialPropertyBOnPipeline σ1 E1)
    (h2 : HasCombinatorialPropertyB2 σ2 E1 d) : HasPackSemanticPropertyB2 hn σ1 σ2 d := by
  intro v i hi1 him
  set x : Fin (m * n) → Bool := fun w => largestKeyThresholdJ01 (m := m) (n := n) (i * n) (v w)
  have hmass : totalColumnOnes (monotoneColumnSumsOfBool ((columnSortNetwork m n hn).exec x)) = i * n :=
    sum_topJ_colSums_eq_j hn v (i * n) (Nat.mul_le_mul_right n him)
  obtain ⟨ht, he⟩ := semanticExec_intermediate hn σ1 x i
  have hB1 := h1 _ i (by rw [hmass]; exact le_of_eq (by ring)) hi1 him
  rw [matrixOnesCountInRegion_semanticExec2_eq]
  refine h2 _ i (by rw [ht, hmass]; ring) hi1 him ?_
  rw [he]; exact hB1

end Chvatal
