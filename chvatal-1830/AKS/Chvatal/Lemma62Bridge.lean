module

public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.SortedColumnDecode

/-! # Property-F bridge (Chvátal Lemma 6.2): the paper Property F (events with `totalColumnOnes c = j`)
implies the semantic matrix Property F of a pack, for any `n`. -/

@[expose] public section

namespace Chvatal

theorem onesAboveHalfFringe_eq_sum_aboveBottomRows {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe hf c σ S =
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

theorem onesAboveHalfFringe_ge_sum_excess {m n f : Nat} (hf : Even f) (hfm : f ≤ m)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) :
    ∑ col ∈ S, (scrambledColSum c σ col - f / 2) ≤ onesAboveHalfFringe hf c σ S := by
  rw [onesAboveHalfFringe_eq_sum_aboveBottomRows]
  exact Finset.sum_le_sum fun col _ =>
    onesAboveBottom_le_scrambledColSumInAboveBottomRows c σ (f / 2) col (by omega)

theorem HasPackSemanticPropertyF.of_paperF {m n f : ℕ} {hf : Even f} (hn : 0 < n)
    (hfm : f ≤ m) {deltaF epsF : ℝ} (hdelta1 : deltaF ≤ 1)
    (hcol : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      IdealColumnSort m n hn pack.colSort)
    (hrow : ∀ (σ : Scramble m n) (pack : SortScrambleSortPack m n hn σ),
      RowScrambleCorrect m n hn σ pack.colSort pack.rowScramble)
    {σ : Scramble m n} (pack : SortScrambleSortPack m n hn σ)
    (hP : ∀ (c : MonotoneColumnSums m n) (j : ℕ), totalColumnOnes c = j → 0 < j →
      (j : ℝ) ≤ deltaF * (f * n) → ∀ S : Finset (Fin n), ¬ fringeColumnEventBad hf deltaF epsF c σ j S) :
    HasPackSemanticPropertyF hn pack f hfm deltaF epsF := by
  classical
  intro v j hj hjδ
  have hjmn : j ≤ m * n := by
    have hfm' : (f : ℝ) ≤ m := by exact_mod_cast hfm
    have h1 : deltaF * (f * n) ≤ 1 * (f * n) := mul_le_mul_of_nonneg_right hdelta1 (by positivity)
    have h2 : (f : ℝ) * n ≤ m * n := by gcongr
    exact_mod_cast (by push_cast; linarith : (j : ℝ) ≤ (m * n : ℕ))
  rw [packSemanticIntrusionCountF_eq_onesAboveBottom (m := m) (n := n) (f := f) hn hfm
    (hf := hf) (σ := σ) (pack := pack) (hcol σ pack) (hrow σ pack) v j]
  set cMark := monotoneColumnSumsOfBool hn
      (pack.colSort.net.exec fun w => largestKeyThresholdJ01 (m := m) (n := n) j (v w))
  have htot : totalColumnOnes cMark = j :=
    sum_topJ_colSums_eq_j hn pack.colSort (hcol σ pack) v j hj hjmn
  by_contra hcon
  rw [not_lt] at hcon
  set S := excessColumnSet cMark σ (f + 1) with hS
  have hsumS : onesAboveBottom cMark σ f = ∑ col ∈ S, (scrambledColSum cMark σ col - f) := by
    unfold onesAboveBottom
    rw [hS, excessColumnSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun col _ => ?_
    split_ifs with h
    · rfl
    · omega
  have hkey := onesAboveHalfFringe_ge_sum_excess hf hfm cMark σ S
  have hf2 := cast_half_of_even hf
  have hfe : f = 2 * (f / 2) := by obtain ⟨k, hk⟩ := hf; omega
  have hsum2 : ∑ col ∈ S, (scrambledColSum cMark σ col - f / 2) =
      onesAboveBottom cMark σ f + (f / 2) * S.card := by
    rw [hsumS, Finset.sum_congr rfl (g := fun col => (scrambledColSum cMark σ col - f) + f / 2)
      fun col hcol' => by
        have : f + 1 ≤ scrambledColSum cMark σ col := (mem_excessColumnSet _ _ _ _).mp hcol'
        simp only
        omega, Finset.sum_add_distrib]
    simp [Nat.mul_comm]
  refine hP cMark j htot hj hjδ S ?_
  unfold fringeColumnEventBad
  rw [← hf2]
  have h1 : ((onesAboveBottom cMark σ f + f / 2 * S.card : ℕ) : ℝ) ≤
      (onesAboveHalfFringe hf cMark σ S : ℝ) := by exact_mod_cast hsum2 ▸ hkey
  push_cast at h1
  linarith

end Chvatal
