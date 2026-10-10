module

public import AKS.Chvatal.Lemma62Tail
public import AKS.Chvatal.SortedColumnDecode

/-! # Property-F bridge (Chvátal Lemma 6.2): the paper Property F (events with `totalColumnOnes c = j`)
implies the semantic matrix Property F of a pack, for any `n`. -/

@[expose] public section

namespace Chvatal

theorem onesAboveHalfFringe_eq_sum_aboveBottomRows {m n : Nat} (f : Nat)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe f c σ S =
      ∑ col ∈ S, scrambledColSumInAboveBottomRows c σ (f / 2) col := by
  classical
  have h1 : ∀ r : Fin m, rowHit c S r (σ r) =
      ∑ col ∈ S, if col ∈ scrambledRowOnes c σ r then 1 else 0 := by
    intro r
    unfold rowHit
    have : ((monotoneRowOnes c r).image (σ r) ∩ S) = S.filter (· ∈ scrambledRowOnes c σ r) := by
      ext x; simp [scrambledRowOnes, and_comm]
    rw [this, Finset.sum_boole]
    simp
  unfold onesAboveHalfFringe
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun col _ => ?_
  unfold scrambledColSumInAboveBottomRows topRows
  rw [Finset.card_filter, Finset.sum_filter, ← Finset.sum_filter, ← Finset.card_filter,
    Finset.sum_boole]
  congr 1
  ext r
  simp

/-- Semantic Property F is monotone in `δ_F` (down) and `ε_F` (up). -/
theorem HasPackSemanticPropertyF.mono {m n f : ℕ} (hn : 0 < n) {σ : Scramble m n}
    (hfm : f ≤ m) {δ δ' ε ε' : ℝ}
    (hδ : δ' ≤ δ) (hε : ε ≤ ε') (h : HasPackSemanticPropertyF hn σ f hfm δ ε) :
    HasPackSemanticPropertyF hn σ f hfm δ' ε' := by
  intro v j hj hjδ
  have h1 := h v j hj (hjδ.trans (mul_le_mul_of_nonneg_right hδ (by positivity)))
  exact h1.trans_le (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg j))

theorem HasPackSemanticPropertyF.of_paperF {m n f : ℕ} (hf : Even f) (hn : 0 < n)
    (hfm : f ≤ m) {σ : Scramble m n} (hP : HasPaperPropertyF f σ) :
    HasPackSemanticPropertyF hn σ f hfm (128 / 4095) eps := by
  classical
  intro v j hj hjδ
  have hjmn : j ≤ m * n := by
    have : (f : ℝ) * n ≤ m * n := by gcongr
    exact_mod_cast (by push_cast; linarith [show (0 : ℝ) ≤ f * n by positivity] :
      (j : ℝ) ≤ (m * n : ℕ))
  rw [matrixOnesCountInRegion_semanticExec hn σ _ f]
  set cMark := monotoneColumnSumsOfBool
      ((columnSortNetwork m n hn).exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have htot : totalColumnOnes cMark = j := sum_topJ_colSums_eq_j hn v j hjmn
  by_contra hcon
  rw [not_lt] at hcon
  set S := excessColumnSet cMark σ (f + 1) with hS
  have hfe : f = 2 * (f / 2) := by obtain ⟨k, hk⟩ := hf; omega
  have hsum2 : ∑ col ∈ S, (scrambledColSum cMark σ col - f / 2) =
      onesAboveBottom cMark σ f + (f / 2) * S.card := by
    have hsumS : onesAboveBottom cMark σ f = ∑ col ∈ S, (scrambledColSum cMark σ col - f) := by
      unfold onesAboveBottom
      rw [hS, excessColumnSet, Finset.sum_filter]
      exact Finset.sum_congr rfl fun col _ => by split_ifs <;> omega
    rw [hsumS, mul_comm, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun col hcol => by
      have := (mem_excessColumnSet _ _ _ _).mp hcol
      omega
  have hkey : ∑ col ∈ S, (scrambledColSum cMark σ col - f / 2) ≤ onesAboveHalfFringe f cMark σ S := by
    rw [onesAboveHalfFringe_eq_sum_aboveBottomRows]
    exact Finset.sum_le_sum fun col _ =>
      onesAboveBottom_le_scrambledColSumInAboveBottomRows cMark σ (f / 2) col (by omega)
  refine hP cMark j htot hj hjδ S ?_
  unfold fringeColumnEventBad
  rw [cast_half_of_even hf |>.symm]
  have h1 : ((onesAboveBottom cMark σ f + f / 2 * S.card : ℕ) : ℝ) ≤
      (onesAboveHalfFringe f cMark σ S : ℝ) := by exact_mod_cast hsum2 ▸ hkey
  push_cast at h1
  linarith

end Chvatal
